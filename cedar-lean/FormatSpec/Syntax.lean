/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Lean
import FormatSpec.Grammar
import FormatSpec.Classify
import FormatSpec.Value
import FormatSpec.Constraint

/-!
# `format_spec` embedded DSL

Surface syntax for flat non-recursive attribute grammars, transcribing the `::=`
grammars written in `doc/CedarDoc/*.lean`. Lean's own `syntax`/`declare_syntax_cat`
framework does all the *parsing* of the notation; this module declares the notation
and elaborates the resulting `Syntax` tree into the generated declarations.

The command has three sections (see design note §16.3), in order:

```
format_spec Decimal where
  grammar
    Decimal  ::= Integer "." Fraction
    Integer  ::= ["-"] digit+
    Fraction ::= digit{1,4}
  constraints
    -- value/string constraints (raw Lean predicates for now; see below)
  value
    -- the value function (a raw Lean term for now; see below)
```

* **`grammar`** (required) — the EBNF productions. Elaborated fully into the core
  `FormatSpec.Grammar` value bound to `<Name>.grammar`. `grammar` is used rather than
  `syntax` because `syntax` is a reserved Lean keyword.
* **`constraints`** (optional) — currently captured as raw Lean predicate terms
  (`String → Prop`) and bound to `<Name>.constraints`. Per §16.3 these will later be
  written in a small predicate DSL and auto-classified into `IsWf` (string-only) vs
  `SatisfiesConstraints` (value-dependent).
* **`value`** (optional) — currently captured as a raw Lean term and bound to
  `<Name>.valueFn` (the §16.4 "opaque" tier). Per §16.4 this will later be written in
  a flat first-order value-DSL that is analyzed for affinity to auto-generate proofs.

Grammar notation:
* a production is `Name ::= item item …`
* an item is a string literal, a nonterminal reference (`ident`), a terminal
  (`digit`/`hexDigit` with a length suffix), or an optional `[item]`
* length suffix: `+` (one-or-more), `{n}` (exactly), `{lo,hi}` (between)

Not yet: production-level alternation (`A ::= x | y`), the predicate/value DSLs, and
generation of `IsWf` / `SatisfiesConstraints` / `IsAccepted` / `computeValue`. Those
are the next increments; this module currently generates the grammar value (+ captures
the raw value/constraint terms) so the three-section shape is in place.
-/

namespace FormatSpec

open Lean Elab Command

/-- Length suffix on a terminal: `+`, `{n}`, `{lo,hi}`. -/
declare_syntax_cat fmtLen
syntax "+"                : fmtLen
syntax "{" num "}"        : fmtLen
syntax "{" num "," num "}" : fmtLen

/-- A right-hand-side item: literal, nonterminal ref, terminal, or optional. -/
declare_syntax_cat fmtItem
syntax str                : fmtItem  -- literal
syntax "digit" fmtLen     : fmtItem  -- decimal terminal
syntax "hexDigit" fmtLen  : fmtItem  -- hex terminal
syntax ident              : fmtItem  -- nonterminal reference
syntax "[" fmtItem "]"    : fmtItem  -- optional

/-- A production: `Name ::= item⁺` (single-sequence; alternation added later).
    `withPosition`/`colGt` pins all items strictly right of the LHS column, so the
    greedy `+` stops at the next production's LHS (same column) instead of consuming
    it. -/
declare_syntax_cat fmtProd
syntax withPosition(ident " ::= " (colGt fmtItem)+) : fmtProd

/-- The optional `constraints` section: predicates written in the constraint-DSL
    (`constraintExpr` category from `FormatSpec.Constraint`), one per line (`colGt`, like
    the `grammar` productions — no commas). Each is auto-classified (string → `IsWf`,
    value → `SatisfiesConstraints`) downstream. -/
syntax fmtConstraints := "constraints" (colGt constraintExpr)+

/-- The optional `value` section. Two tiers (design note §16.4/§16.7):
    * `value <formula>` — the value-DSL (`valExpr`); analyzable, matches `value(X)=…`.
    * `value opaque := <term>` — the ESCAPE HATCH: an arbitrary Lean term of type
      `Env → Int`, for values outside the DSL vocabulary (CoStar++-level expressiveness,
      definitional — no auto-analysis). Ensures no grammar is ever blocked. -/
syntax fmtValue := "value" (("opaque" " := " term) <|> valExpr)

/-- The `format_spec` command, sections in order: `grammar` (required), `value`
    (optional), `constraints` (optional). `value` precedes `constraints` so a constraint
    can refer to `value` (the elaborated value expression), matching the doc's
    `Constraint: value(X) ∈ [Int64.MIN, Int64.MAX]`. -/
syntax (name := formatSpecCmd)
  "format_spec " ident " where "
    "grammar" (colGt fmtProd)+
    (fmtValue)?
    (fmtConstraints)? : command

/-- Elaborate a `fmtLen` into a `LenSpec` term. -/
def elabLen : TSyntax `fmtLen → CommandElabM (TSyntax `term)
  | `(fmtLen| +)                      => `(FormatSpec.LenSpec.atLeastOne)
  | `(fmtLen| { $n:num })             => `(FormatSpec.LenSpec.exactly $n)
  | `(fmtLen| { $lo:num , $hi:num })  => `(FormatSpec.LenSpec.between $lo $hi)
  | s                                 => throwErrorAt s "unrecognized length suffix"

/-- Elaborate a non-optional item into a `Sym` term. Errors on a bare `[…]`
    (optionality is handled one level up, in `elabItem`). -/
def elabSym : TSyntax `fmtItem → CommandElabM (TSyntax `term)
  | `(fmtItem| $s:str)            => `(FormatSpec.Sym.lit $s)
  | `(fmtItem| digit $l:fmtLen)   => do `(FormatSpec.Sym.term FormatSpec.TokClass.digit $(← elabLen l))
  | `(fmtItem| hexDigit $l:fmtLen) => do `(FormatSpec.Sym.term FormatSpec.TokClass.hexDigit $(← elabLen l))
  | `(fmtItem| $i:ident)          => `(FormatSpec.Sym.ref $(Syntax.mkStrLit i.getId.toString))
  | s                             => throwErrorAt s "unrecognized grammar item"

/-- Elaborate an item into a `SymItem` term, setting `optional` for `[…]`. -/
def elabItem : TSyntax `fmtItem → CommandElabM (TSyntax `term)
  | `(fmtItem| [ $inner:fmtItem ]) => do
      `(FormatSpec.SymItem.mk $(← elabSym inner) true)
  | other => do
      `(FormatSpec.SymItem.mk $(← elabSym other) false)

/-- Elaborate a single production into a `Production` term. -/
def elabProd : TSyntax `fmtProd → CommandElabM (TSyntax `term)
  | `(fmtProd| $lhs:ident ::= $items:fmtItem*) => do
      let itemTerms ← items.mapM elabItem
      let sep : Syntax.TSepArray `term "," := .ofElems itemTerms
      `(FormatSpec.Production.mk
          $(Syntax.mkStrLit lhs.getId.toString)
          [[$sep,*]])
  | s => throwErrorAt s "unrecognized production"

/-- Elaborate the `format_spec` command. Currently emits:
    * `<Name>.grammar : Grammar`            — from the `grammar` section (always)
    * `<Name>.constraints : List (String → Prop)` — from `constraints` (if present)
    * `<Name>.valueExpr : ValExpr`          — from `value` (if present), the deep AST
      built from the in-place value-DSL formula (no `val%` wrapper)

    Generation of `IsWf` / `SatisfiesConstraints` / `IsAccepted` / `computeValue` from
    these is the next increment. -/
@[command_elab formatSpecCmd]
def elabFormatSpec : CommandElab := fun stx => do
  match stx with
  | `(format_spec $name:ident where grammar $prods:fmtProd* $[$v:fmtValue]? $[$cs:fmtConstraints]?) => do
      -- Grammar (always).
      let prodTerms ← prods.mapM elabProd
      let sep : Syntax.TSepArray `term "," := .ofElems prodTerms
      let grammarIdent := mkIdentFrom name (name.getId ++ `grammar)
      elabCommand (← `(def $grammarIdent : FormatSpec.Grammar :=
                    FormatSpec.Grammar.mk $(Syntax.mkStrLit name.getId.toString) [$sep,*]))
      -- Value (optional), processed BEFORE constraints so a constraint may refer to
      -- `value`. Two tiers: `value opaque := <term>` binds the raw `Env → Int`;
      -- `value <formula>` elaborates the value-DSL to a `ValExpr` (bound as `valueExpr`)
      -- whose `eval` is the value fn. `valueSub` is the `ValExpr` term substituted for a
      -- `value` reference in constraints (only in the DSL tier).
      let mut valueSub : Option (TSyntax `term) := none
      if let some vStx := v then
        let inner := vStx.raw[1]
        let vfnIdent := mkIdentFrom name (name.getId ++ `valueFn)
        if inner[0].isToken "opaque" then
          let t : TSyntax `term := ⟨inner[2]⟩
          elabCommand (← `(def $vfnIdent : FormatSpec.Env → Int := $t))
        else
          let ve : TSyntax `valExpr := ⟨inner⟩
          let valTerm ← liftMacroM (elabValExpr ve)
          let veIdent := mkIdentFrom name (name.getId ++ `valueExpr)
          elabCommand (← `(def $veIdent : FormatSpec.ValExpr := $valTerm))
          elabCommand (← `(def $vfnIdent : FormatSpec.Env → Int := ($veIdent).eval))
          -- Refer to the value expression by its generated name in constraints.
          valueSub := some (← `($veIdent))
      -- Constraints (optional): constraint-DSL predicates, one per line, with `value`
      -- substituted by the value expression. The `fmtConstraints` node is
      -- `"constraints" (colGt constraintExpr)+`; arg 1 is the plain array of exprs.
      if let some csStx := cs then
        let exprs : Array (TSyntax `constraintExpr) := csStx.raw[1].getArgs.map (⟨·⟩)
        let cTerms ← exprs.mapM (fun e => liftMacroM (elabEntryWith valueSub e))
        let csep : Syntax.TSepArray `term "," := .ofElems cTerms
        let cIdent := mkIdentFrom name (name.getId ++ `constraints)
        elabCommand (← `(def $cIdent : List FormatSpec.ConstraintEntry := [$csep,*]))
  | _ => throwUnsupportedSyntax

end FormatSpec
