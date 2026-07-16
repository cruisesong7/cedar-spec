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

/-!
# Core grammar type: flat, non-recursive (DAG) attribute grammars — *syntax only*

This is the first-order data the `format_spec` DSL elaborates into, and the
classifier / spec-generator consume. It records **only the syntactic skeleton** — a
DAG of named productions in an EBNF subset, matching the `::=` grammars written in
`doc/CedarDoc/*.lean`.

Deliberately *not* here: the value function. Per the design (see
`FormatSpec/DESIGN.md`), the value function is an *arbitrary Lean
term* supplied alongside the grammar; it is never stored as first-order data.
`computeValue = valueFn ∘ decode` is always available (the author writes `valueFn`,
`decode` is synthesized from this syntax). The tool's job is to *analyze* that term's
`Expr` at elaboration time to decide whether the contract proofs auto-discharge
(affine) or need manual `sorry` holes (e.g. calendar arithmetic) — that analysis is
NOT part of this data type.

The class encoded here:
* **DAG, non-recursive** — productions may reference other productions by name, but
  the reference graph must be acyclic (a classifier check). No cycles ⟹ the
  denotation unfolds to a flat `Prop`, never an inductive relation.
* **regular leaves** — the only terminals are literals and character-class token runs
  (`Terminal`), the sole site of Kleene iteration (`LenSpec`).
-/

namespace FormatSpec

/-- Leaf character classes: the terminal token kinds. Each corresponds to a decidable
    per-character predicate and a base-b reader (base-10 `digit`, base-16 `hexDigit`). -/
inductive TokClass where
  /-- ASCII decimal digits `0-9`. -/
  | digit
  /-- ASCII hex digits `0-9a-fA-F`. -/
  | hexDigit
  deriving Repr, DecidableEq, Inhabited

/-- Length constraint on a terminal token run (the `Digit⁺` / `Digit{4}` / `Digit{1,4}`
    of the doc grammars). Determines finiteness/arity. -/
inductive LenSpec where
  /-- Exactly `n` characters (`Digit{4}`). -/
  | exactly (n : Nat)
  /-- Between `lo` and `hi` characters inclusive (`Digit{1,4}`). -/
  | between (lo hi : Nat)
  /-- One or more characters (`Digit⁺`, unbounded ⟹ infinite language). -/
  | atLeastOne
  deriving Repr, DecidableEq, Inhabited

/-- A symbol appearing in a production's right-hand side. -/
inductive Sym where
  /-- A fixed literal string (separators `"."`, `":"`, `"-"`; unit tags `"ms"`). -/
  | lit (s : String)
  /-- A reference to another named production (nonterminal). The DAG edge. -/
  | ref (name : String)
  /-- An inline terminal: a token run of class `tok`, length-constrained by `len`. -/
  | term (tok : TokClass) (len : LenSpec)
  deriving Repr, DecidableEq, Inhabited

/-- One right-hand-side symbol together with whether it is optional (the `[X]` of
    the doc grammars, e.g. `['-']`). -/
structure SymItem where
  sym : Sym
  optional : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- One alternative of a production: a finite sequence of (possibly optional) symbols. -/
abbrev Seq := List SymItem

/-- A named production: `name ::= alt₁ | alt₂ | …`. A single-sequence production has a
    one-element `alts`; alternation lists several sequences. -/
structure Production where
  name : String
  alts : List Seq
  deriving Repr, DecidableEq, Inhabited

/-- A flat non-recursive attribute grammar (syntax only): a start symbol plus a DAG of
    named productions. `start` must name one of `prods`. -/
structure Grammar where
  start : String
  prods : List Production
  deriving Repr, DecidableEq, Inhabited

namespace Grammar

/-- Look up a production by name. -/
def prod? (g : Grammar) (name : String) : Option Production :=
  g.prods.find? (·.name == name)

/-- The start production, if present. -/
def startProd? (g : Grammar) : Option Production :=
  g.prod? g.start

end Grammar

namespace Sym

/-- The referenced nonterminal name, if this symbol is a `ref`. -/
def refName? : Sym → Option String
  | .ref n => some n
  | _      => none

end Sym

end FormatSpec
