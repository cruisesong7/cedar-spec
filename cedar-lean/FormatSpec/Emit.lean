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
import FormatSpec.Denote

/-!
# Inlined per-production predicate synthesis

Generates *readable, inlined* well-formedness predicates per production — the `∃ …, s =
p0 ++ p1 ++ … ∧ …` structural form that reads like the hand-written specs
(`doc/CedarDoc/*.lean`), instead of an opaque `IsWfProd grammar "Name"` interpreter call.

The synthesized predicate mirrors the `Denote` denotation exactly (`matchesSeq` /
`matchesProd`), with nonterminal references resolved to sibling predicate *names*
(`<Name>.isWf.<Prod>`). This eliminates the fuel/interpreter indirection: the DAG is
unrolled into named defs emitted in topological (leaf-first) order.
-/

namespace FormatSpec

open Lean Elab Command

/-- Render a natural number as Unicode subscript digits (`1 ↦ "₁"`, `12 ↦ "₁₂"`), for
    readable disambiguating suffixes on generated binder names (`rest₁`, `rest₂`, …). -/
def subscript (n : Nat) : String :=
  let subs := "₀₁₂₃₄₅₆₇₈₉".toList
  String.ofList ((toString n).toList.map (fun c => subs[(c.toNat - '0'.toNat)]!))

/-- The readable leaf predicate for a `term tok len`, matching the hand specs'
    vocabulary (`IsDigits`, `IsFixedDigits`, …). Names are emitted UNQUALIFIED (the
    generated file `open`s `FormatSpec`), so they read like the doc. -/
def termPred (tok : TokClass) (ls : LenSpec) (v : TSyntax `term) : CommandElabM (TSyntax `term) :=
  match tok, ls with
  | .digit,    .atLeastOne    => `(IsDigits $v)
  | .hexDigit, .atLeastOne    => `(IsHexDigits $v)
  | .digit,    .exactly n     => `(IsFixedDigits $(quote n) $v)
  | .hexDigit, .exactly n     => `(IsFixedHexDigits $(quote n) $v)
  | .digit,    .between lo hi => `(IsDigitsBetween $(quote lo) $(quote hi) $v)
  | .hexDigit, .between lo hi => `(IsHexDigitsBetween $(quote lo) $(quote hi) $v)

/-- Predicate that string `v` matches symbol `sym`. Refs resolve to the sibling
    per-production predicate `<specName>.IsWf.<Nt>`. -/
def symPred (specName : Name) : Sym → (v : TSyntax `term) → CommandElabM (TSyntax `term)
  | .lit l,       v => `($v = $(Syntax.mkStrLit l))
  | .term tok ls, v => termPred tok ls v
  | .ref nm,      v => do
      -- resolve to the sibling per-production predicate `<specName>.IsWf.<Nt>` (the
      -- capital-`I` Prop = the readable surface spec; cf. the bundle's lowercase `isWf`)
      let refId := mkIdent (specName ++ `IsWf ++ nm.toName)
      `($refId $v)

/-- Lowercase the first character (nonterminal `Integer` → binder `integer`). -/
private def deCap (s : String) : String :=
  match s.toList with
  | []      => s
  | c :: cs => String.ofList (c.toLower :: cs)

/-- Base binder name for a capturing symbol; `none` for a literal (no binder). -/
private def binderBase : Sym → Option String
  | .lit _      => none
  | .ref nm     => some (deCap nm)
  | .term _ _   => some "digits"

/-- Assign a readable, unique binder name to each capturing item (literals → `none`).
    Names come from the nonterminal (`Integer` → `integer`); duplicates within one
    sequence are disambiguated with a numeric suffix (`group0`, `group1`, …). -/
private def assignBinders (items : List SymItem) : List (Option String) := Id.run do
  let bases := items.map (binderBase ·.sym)
  -- how many times each base occurs
  let mut counts : Std.HashMap String Nat := {}
  for b in bases do
    if let some nm := b then counts := counts.insert nm ((counts.getD nm 0) + 1)
  -- assign, suffixing only when a base is duplicated
  let mut seen : Std.HashMap String Nat := {}
  let mut out : List (Option String) := []
  for b in bases do
    match b with
    | none    => out := out ++ [none]
    | some nm =>
      if (counts.getD nm 1) == 1 then
        out := out ++ [some nm]
      else
        let idx := seen.getD nm 0
        seen := seen.insert nm (idx + 1)
        out := out ++ [some s!"{nm}{idx}"]
  return out

/-- Predicate that string `whole` matches a NON-optional sequence, in the flat form that
    reads like the hand spec: bind one variable per capture (named from the grammar),
    literals inline in the concatenation.
      `∃ integer fraction, whole = integer ++ "." ++ fraction ∧ P integer ∧ Q fraction`
    A single lone capture needs no `∃` (`P whole` directly). -/
def seqPredFlat (specName : Name) (whole : TSyntax `term) (items : List SymItem) :
    CommandElabM (TSyntax `term) := do
  let names := assignBinders items
  -- single lone capture: apply its predicate directly to `whole`, no existential.
  match items, names with
  | [it], [some _] => symPred specName it.sym whole
  | _, _ => do
    -- concatenation pieces: literal string for lits, binder var for captures
    let mut concatPieces : List (TSyntax `term) := []
    let mut binders : List (TSyntax `ident) := []
    let mut preds : List (TSyntax `term) := []
    for (it, nm?) in items.zip names do
      match nm? with
      | none =>
        if let .lit l := it.sym then concatPieces := concatPieces ++ [← `($(Syntax.mkStrLit l))]
      | some nm =>
        let id := mkIdent (Name.mkSimple nm)
        let idTm : TSyntax `term := ⟨id.raw⟩
        binders := binders ++ [id]
        concatPieces := concatPieces ++ [idTm]
        preds := preds ++ [← symPred specName it.sym idTm]
    let concat ← match concatPieces with
      | []      => `("")
      | x :: xs => xs.foldlM (fun acc y => `($acc ++ $y)) x
    let eqp ← `($whole = $concat)
    let body ← preds.foldlM (fun acc p => `($acc ∧ $p)) eqp
    binders.foldrM (fun id acc => `(∃ $id:ident, $acc)) body

/-- Peel a single item off the front of `whole`, then recurse on `rest`.
    * a LITERAL is inlined into the equation with no binder (`whole = "-" ++ tl ∧ …`),
      matching the hand spec's `∃ t, s = "-" ++ t ∧ …`;
    * a CAPTURE binds a variable named after the nonterminal.
    The trailing `rest` binder is named `rest` (or `rest2`, … at deeper peels).
    A trailing empty sequence closes with the tail predicate directly (no `= ""`). -/
partial def seqPeel (specName : Name) (whole : TSyntax `term)
    (items : List SymItem) (depth : Nat) : CommandElabM (TSyntax `term) := do
  match items with
  | []           => `($whole = "")
  | [item] =>
    -- last item: it must consume all of `whole` (no fresh rest binder needed)
    if item.optional then
      let hd ← symPred specName item.sym whole
      `($hd ∨ $whole = "")
    else
      symPred specName item.sym whole
  | item :: rest =>
    -- first remainder is `rest`, then `rest₁`, `rest₂`, … (Unicode subscripts)
    let restName := if depth == 0 then "rest" else s!"rest{subscript depth}"
    let rst   := mkIdent (Name.mkSimple restName)
    let rstTm : TSyntax `term := ⟨rst.raw⟩
    let tl ← seqPeel specName rstTm rest (depth + 1)
    let mkPresent : CommandElabM (TSyntax `term) := do
      match item.sym, binderBase item.sym with
      | .lit l, _ =>              -- literal: inline, bind only the rest
        `(∃ $rst:ident, $whole = $(Syntax.mkStrLit l) ++ $rstTm ∧ $tl)
      | sym, some base =>          -- capture: bind a named var + the rest
        let p   := mkIdent (Name.mkSimple base)
        let pTm : TSyntax `term := ⟨p.raw⟩
        let hd ← symPred specName sym pTm
        `(∃ $p:ident $rst:ident, $whole = $pTm ++ $rstTm ∧ $hd ∧ $tl)
      | sym, none =>               -- (unreachable: only lits have no base)
        let p   := mkIdent (Name.mkSimple "piece")
        let pTm : TSyntax `term := ⟨p.raw⟩
        let hd ← symPred specName sym pTm
        `(∃ $p:ident $rst:ident, $whole = $pTm ++ $rstTm ∧ $hd ∧ $tl)
    if item.optional then
      let present ← mkPresent
      let absent ← seqPeel specName whole rest (depth + 1)
      `($present ∨ $absent)
    else
      mkPresent

/-- A sequence of ALL-optional captures (e.g. `[Days][Hours][Minutes][Seconds][Millis]`).
    The peel form would produce a combinatorial `present ∨ absent` tree; instead emit the
    flat, linear form — bind one piece per component, concatenated in order, each piece
    "empty or well-formed":
      `∃ days hours …, whole = days ++ hours ++ … ∧ (days = "" ∨ IsWf.Days days) ∧ …`
    This reads like the doc's one-line `[Days][Hours]…` and is O(n), not O(2ⁿ). -/
def seqAllOptional (specName : Name) (whole : TSyntax `term) (items : List SymItem) :
    CommandElabM (TSyntax `term) := do
  let names := assignBinders items          -- every item is a capture ⟹ all `some`
  let binders : List (TSyntax `ident) := names.filterMap (·.map (mkIdent ∘ Name.mkSimple))
  let binderTms : List (TSyntax `term) := binders.map (fun i => ⟨i.raw⟩)
  let concat ← match binderTms with
    | []      => `("")
    | x :: xs => xs.foldlM (fun acc y => `($acc ++ $y)) x
  -- per-piece: `(piece = "" ∨ IsWf.<Nt> piece)`
  let pieceProps ← (items.zip binderTms).mapM (fun (it, pTm) => do
    let hd ← symPred specName it.sym pTm
    `($pTm = "" ∨ $hd))
  let eqp ← `($whole = $concat)
  let body ← pieceProps.foldlM (fun acc p => `($acc ∧ $p)) eqp
  binders.foldrM (fun id acc => `(∃ $id:ident, $acc)) body

/-- Predicate that string `whole` matches sequence `items`:
    * no optionals            → flat named form (`seqPredFlat`);
    * ALL items optional captures → flat "empty-or-wf" form (`seqAllOptional`), avoiding
      the combinatorial peel tree (the doc's `[Days][Hours]…` shape);
    * otherwise (mixed)       → peel form (`seqPeel`). -/
partial def seqPred (specName : Name) (whole : TSyntax `term)
    (items : List SymItem) (_depth : Nat := 0) : CommandElabM (TSyntax `term) := do
  if items.all (! ·.optional) then
    seqPredFlat specName whole items
  else if items.all (fun it => it.optional && (binderBase it.sym).isSome) then
    seqAllOptional specName whole items
  else
    seqPeel specName whole items 0

/-- Predicate that string `v` matches production `p` (disjunction over alternatives). -/
def prodPred (specName : Name) (p : Production) (v : TSyntax `term) :
    CommandElabM (TSyntax `term) := do
  match p.alts with
  | []        => `(False)
  | a :: rest =>
      let first ← seqPred specName v a 0
      rest.foldlM (fun acc alt => do `($acc ∨ $(← seqPred specName v alt 0))) first

/-- Topologically order productions leaf-first (dependencies before dependents), so each
    emitted `def` references only already-defined sibling predicates. Assumes the grammar
    is acyclic (checked elsewhere); on a cycle, remaining nodes are appended in input
    order (the generated defs would then fail to compile, surfacing the cycle). -/
partial def topoOrder (g : Grammar) : List Production :=
  let step := fun (visited : List String) (acc : List Production) (name : String) =>
    goName g name visited acc
  (g.prods.map (·.name)).foldl (fun (st : List String × List Production) nm =>
    let (v, a) := step st.1 st.2 nm
    (v, a)) ([], []) |>.2 |>.reverse
where
  /-- DFS: visit `name`'s dependencies, then `name`; accumulate in reverse post-order. -/
  goName (g : Grammar) (name : String) (visited : List String) (acc : List Production) :
      List String × List Production :=
    if visited.contains name then (visited, acc)
    else match g.prod? name with
      | none   => (name :: visited, acc)
      | some p =>
          let visited := name :: visited
          let (visited, acc) := p.directRefs.foldl (fun (st : List String × List Production) r =>
            goName g r st.1 st.2) (visited, acc)
          (visited, p :: acc)

end FormatSpec
