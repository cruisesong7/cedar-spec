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
import FormatSpec.Assemble
import FormatSpec.Emit

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

/-- The optional `parser` clause: names the external hand-written parser and the
    projection reading its value's `Int` denotation back out. When present, the command
    emits the contract theorem *obligations* (`<Name>.sound`/`.complete`/`.reject`) as
    `sorry`d theorems relating that parser to the generated spec. -/
syntax fmtParser := "parser" term " projection " term

/-- Optional trailing clause: `to "path.lean"` writes the generated declarations to a
    `.lean` file on disk (de-hygiened, clean source), in addition to elaborating them. -/
syntax fmtTo := "to " str

/-- The `format_spec` command, sections in order: `grammar` (required), `value`
    (optional), `constraints` (optional), `parser` (optional), `to` (optional). `value`
    precedes `constraints` so a constraint can refer to `value`. The `parser` clause
    triggers emission of the sorried contract theorems; `to` writes output to a file. -/
syntax (name := formatSpecCmd)
  ("#show ")? "format_spec " ident " where "
    "grammar" (colGt fmtProd)+
    (fmtValue)?
    (fmtConstraints)?
    (fmtParser)?
    (fmtTo)? : command

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

/-! Parse the grammar syntax into `Grammar`/`Production`/`Sym` *values* (not terms), so
    the inlined-predicate synthesizer (`FormatSpec.prodPred`, `topoOrder`) can run at
    elaboration time. -/

def parseLen : TSyntax `fmtLen → CommandElabM LenSpec
  | `(fmtLen| +)                     => pure .atLeastOne
  | `(fmtLen| { $n:num })            => pure (.exactly n.getNat)
  | `(fmtLen| { $lo:num , $hi:num }) => pure (.between lo.getNat hi.getNat)
  | s                                => throwErrorAt s "unrecognized length suffix"

def parseSym : TSyntax `fmtItem → CommandElabM Sym
  | `(fmtItem| $s:str)             => pure (.lit s.getString)
  | `(fmtItem| digit $l:fmtLen)    => do pure (.term .digit (← parseLen l))
  | `(fmtItem| hexDigit $l:fmtLen) => do pure (.term .hexDigit (← parseLen l))
  | `(fmtItem| $i:ident)           => pure (.ref i.getId.toString)
  | s                              => throwErrorAt s "unrecognized grammar item"

def parseItem : TSyntax `fmtItem → CommandElabM SymItem
  | `(fmtItem| [ $inner:fmtItem ]) => do pure { sym := ← parseSym inner, optional := true }
  | other                          => do pure { sym := ← parseSym other, optional := false }

def parseProd : TSyntax `fmtProd → CommandElabM Production
  | `(fmtProd| $lhs:ident ::= $items:fmtItem*) => do
      pure { name := lhs.getId.toString, alts := [(← items.toList.mapM parseItem)] }
  | s => throwErrorAt s "unrecognized production"

/-- Strip macro scopes from every identifier in a syntax tree, so pretty-printing yields
    clean source without hygiene daggers (`✝`). Used when writing generated declarations
    to a file. -/
partial def deHygiene (stx : Syntax) : Syntax :=
  match stx with
  | .ident info rawVal val pre => .ident info rawVal val.eraseMacroScopes pre
  | .node info kind args       => .node info kind (args.map deHygiene)
  | s                          => s

/-- Elaborate the `format_spec` command: generates the spec declarations (grammar,
    per-production `isWf`, value, constraints, bundled predicates, `computeValue`) and —
    with a `parser` clause — the sorried contract theorems. `#show` logs the generated
    source; `to "path"` writes it (de-hygiened) to a file. -/
@[command_elab formatSpecCmd]
def elabFormatSpec : CommandElab := fun stx => do
  match stx with
  | `($[#show%$sh]? format_spec $name:ident where grammar $prods:fmtProd* $[$v:fmtValue]? $[$cs:fmtConstraints]? $[$pr:fmtParser]? $[$to?:fmtTo]?) => do
      -- `#show` logs every generated declaration; a `to "path"` clause additionally
      -- collects them (de-hygiened) and writes clean source to that file. `emit` both
      -- elaborates the command AND records/logs its source form as configured.
      let showing := sh.isSome
      let buf ← IO.mkRef (#[] : Array String)
      let writing := to?.isSome
      let emit (cmd : TSyntax `command) : CommandElabM Unit := do
        if showing || writing then
          let clean : TSyntax `command := ⟨deHygiene cmd.raw⟩
          let src := (← liftCoreM (Lean.PrettyPrinter.ppCommand clean)).pretty
          if showing then logInfo src
          if writing then buf.modify (·.push src)
        elabCommand cmd
      -- Grammar (always).
      let prodTerms ← prods.mapM elabProd
      let sep : Syntax.TSepArray `term "," := .ofElems prodTerms
      let grammarIdent := mkIdentFrom name (name.getId ++ `grammar)
      emit (← `(def $grammarIdent : FormatSpec.Grammar :=
                    FormatSpec.Grammar.mk $(Syntax.mkStrLit name.getId.toString) [$sep,*]))
      -- Per-production well-formedness: emit `<Name>.isWf.<Prod>` for each production as
      -- an INLINED structural predicate (∃ pieces, s = p0 ++ … ∧ …), reading like the
      -- hand specs (`DateComponents.syntaxWf` / `IsWfV4`) rather than an interpreter call.
      -- Emitted in topological (leaf-first) order so each references only already-defined
      -- sibling predicates.
      let gval : FormatSpec.Grammar :=
        { start := name.getId.toString, prods := ← prods.toList.mapM parseProd }
      for prod in FormatSpec.topoOrder gval do
        let pIdent := mkIdentFrom name (name.getId ++ `isWf ++ prod.name.toName)
        let sVar ← `(s)
        let body ← FormatSpec.prodPred name.getId prod sVar
        emit (← `(def $pIdent (s : String) : Prop := $body))
      -- Value (optional), processed BEFORE constraints so a constraint may refer to
      -- `value`. Two tiers: `value opaque := <term>` binds the raw `Env → Int`;
      -- `value <formula>` elaborates the value-DSL to a `ValExpr` (bound as `valueExpr`)
      -- whose `eval` is the value fn. `valueSub` is the `ValExpr` term substituted for a
      -- `value` reference in constraints (only in the DSL tier).
      let mut valueSub : Option (TSyntax `term) := none
      let mut veIdent? : Option (TSyntax `ident) := none
      if let some vStx := v then
        let inner := vStx.raw[1]
        let vfnIdent := mkIdentFrom name (name.getId ++ `valueFn)
        if inner[0].isToken "opaque" then
          let t : TSyntax `term := ⟨inner[2]⟩
          emit (← `(def $vfnIdent : FormatSpec.Env → Int := $t))
        else
          let ve : TSyntax `valExpr := ⟨inner⟩
          let valTerm ← liftMacroM (elabValExpr ve)
          let veIdent := mkIdentFrom name (name.getId ++ `valueExpr)
          emit (← `(def $veIdent : FormatSpec.ValExpr := $valTerm))
          emit (← `(def $vfnIdent : FormatSpec.Env → Int := ($veIdent).eval))
          -- Refer to the value expression by its generated name in constraints.
          valueSub := some (← `($veIdent))
          veIdent? := some veIdent
      -- Constraints (optional): constraint-DSL predicates, one per line, with `value`
      -- substituted by the value expression. The `fmtConstraints` node is
      -- `"constraints" (colGt constraintExpr)+`; arg 1 is the plain array of exprs.
      -- Always bind `<Name>.constraints` (empty list if the section is absent) so the
      -- bundled predicates below can reference it uniformly.
      let cIdent := mkIdentFrom name (name.getId ++ `constraints)
      match cs with
      | some csStx =>
        let exprs : Array (TSyntax `constraintExpr) := csStx.raw[1].getArgs.map (⟨·⟩)
        let cTerms ← exprs.mapM (fun e => liftMacroM (elabEntryWith valueSub e))
        let csep : Syntax.TSepArray `term "," := .ofElems cTerms
        emit (← `(def $cIdent : List FormatSpec.ConstraintEntry := [$csep,*]))
      | none =>
        emit (← `(def $cIdent : List FormatSpec.ConstraintEntry := []))
      -- Bundle the spec: `isWf` / `satisfiesConstraints` / `isAccepted` (design §16.1),
      -- referring to the generated grammar + constraints.
      -- RECONCILIATION GAP (TODO): the bundled `<Name>.isWf` below still uses the
      -- `decode`-based interpreter (`FormatSpec.isWf grammar constraints`), whereas the
      -- per-production `<Name>.isWf.<start>` is now the readable INLINED predicate. These
      -- two well-formedness notions should be provably equal (inlined ≡ IsWfProd start ≡
      -- interpreter), but that equivalence is not yet proved — so the bundle and the
      -- inlined predicates coexist. Unifying them (bundle references the inlined start
      -- predicate) + the equivalence proof is the next milestone.
      let wfIdent  := mkIdentFrom name (name.getId ++ `isWf)
      let scIdent  := mkIdentFrom name (name.getId ++ `satisfiesConstraints)
      let accIdent := mkIdentFrom name (name.getId ++ `isAccepted)
      -- `abbrev` (reducible) so the `Decidable` instances on `isWf`/… fire through.
      -- `isAccepted` is emitted as the explicit conjunction of the generated `isWf` and
      -- `satisfiesConstraints` (self-evident, and reads better than an opaque helper call).
      emit (← `(abbrev $wfIdent  (s : String) : Prop := FormatSpec.isWf $grammarIdent $cIdent s))
      emit (← `(abbrev $scIdent  (s : String) : Prop := FormatSpec.satisfiesConstraints $grammarIdent $cIdent s))
      emit (← `(abbrev $accIdent (s : String) : Prop := $wfIdent s ∧ $scIdent s))
      -- Bundle `computeValue` when a value expression was given.
      if let some veIdent := veIdent? then
        let cvIdent := mkIdentFrom name (name.getId ++ `computeValue)
        emit (← `(def $cvIdent (s : String) : Option Int :=
                      FormatSpec.computeValue $grammarIdent $veIdent s))
      -- Contract obligations: when a `parser <p> projection <π>` clause is present, emit
      -- `<Name>.sound` / `.complete` / `.reject` as `sorry`d theorems relating the
      -- external parser to the generated spec (design §16.1). Requires a value expression
      -- (for `sound`/`complete`); `reject` needs only the spec.
      if let some prStx := pr then
        if let `(fmtParser| parser $parseT:term projection $projT:term) := prStx then
          let rejIdent := mkIdentFrom name (name.getId ++ `reject)
          emit (← `(theorem $rejIdent :
              FormatSpec.RejectStmt $grammarIdent $cIdent $parseT := by sorry))
          if let some veIdent := veIdent? then
            let soundIdent := mkIdentFrom name (name.getId ++ `sound)
            let compIdent  := mkIdentFrom name (name.getId ++ `complete)
            emit (← `(theorem $soundIdent :
                FormatSpec.SoundStmt $grammarIdent $cIdent $veIdent $parseT $projT := by sorry))
            emit (← `(theorem $compIdent :
                FormatSpec.CompleteStmt $grammarIdent $cIdent $veIdent $parseT $projT := by sorry))
      -- If a `to "path"` clause was given, write the collected declarations to that file.
      if let some toStx := to? then
        if let `(fmtTo| to $pathStx:str) := toStx then
          let path := pathStx.getString
          -- Drop-in header: imports + `open` so the file compiles on its own.
          let header :=
            s!"-- Generated by FormatSpec from `format_spec {name.getId}`. Do not edit by hand.\n\
               \nimport FormatSpec.Denote\n\
               import FormatSpec.Value\n\
               import FormatSpec.Constraint\n\
               import FormatSpec.Assemble\n\
               \nopen FormatSpec\n\n"
          let body := String.intercalate "\n\n" (← buf.get).toList
          IO.FS.writeFile path (header ++ body ++ "\n")
          logInfo m!"FormatSpec: wrote {(← buf.get).size} declarations to {path}"
  | _ => throwUnsupportedSyntax

end FormatSpec
