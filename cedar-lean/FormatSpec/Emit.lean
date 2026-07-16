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

/-- `TokClass` as a term. -/
def tokTerm : TokClass → CommandElabM (TSyntax `term)
  | .digit    => `(FormatSpec.TokClass.digit)
  | .hexDigit => `(FormatSpec.TokClass.hexDigit)

/-- `LenSpec` as a term. -/
def lenTerm : LenSpec → CommandElabM (TSyntax `term)
  | .exactly n     => `(FormatSpec.LenSpec.exactly $(quote n))
  | .between lo hi => `(FormatSpec.LenSpec.between $(quote lo) $(quote hi))
  | .atLeastOne    => `(FormatSpec.LenSpec.atLeastOne)

/-- Predicate that string `v` matches symbol `sym`. Refs resolve to
    `<specName>.isWf.<Prod>`. -/
def symPred (specName : Name) : Sym → (v : TSyntax `term) → CommandElabM (TSyntax `term)
  | .lit l,       v => `($v = $(Syntax.mkStrLit l))
  | .term tok ls, v => do `(($(← tokTerm tok)).all $v ∧ ($(← lenTerm ls)).sat ($v).length)
  | .ref nm,      v => do
      let refId := mkIdent (specName ++ `isWf ++ nm.toName)
      `($refId $v)

/-- Predicate that string `whole` matches sequence `items`. Mirrors `matchesSeq`:
    each item splits off a prefix (`∃ p rest, whole = p ++ rest ∧ symPred p ∧ seqPred rest`);
    an optional item may instead be absent (`∨ seqPred rest whole`). Uses `depth` to name
    fresh piece binders `p<depth>`. -/
partial def seqPred (specName : Name) (whole : TSyntax `term) :
    List SymItem → Nat → CommandElabM (TSyntax `term)
  | [],           _     => `($whole = "")
  | item :: rest, depth => do
      let p    := mkIdent (Name.mkSimple s!"p{depth}")
      let rst  := mkIdent (Name.mkSimple s!"r{depth}")
      let pTm  : TSyntax `term := ⟨p.raw⟩
      let rstTm : TSyntax `term := ⟨rst.raw⟩
      let hd   ← symPred specName item.sym pTm
      let tl   ← seqPred specName rstTm rest (depth + 1)
      let present ← `(∃ $p:ident $rst:ident, $whole = $pTm ++ $rstTm ∧ $hd ∧ $tl)
      if item.optional then
        let absent ← seqPred specName whole rest (depth + 1)
        `($present ∨ $absent)
      else
        pure present

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
