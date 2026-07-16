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

import FormatSpec.Denote

/-!
# Decidability of `IsWf`

`IsWf` (from `Denote`) is a flat `Prop` built from `∃`/`∧`/`∨` over string splits. This
module gives `DecidablePred (IsWf g)` — the concrete unlock that turns `IsWf` into an
executable, provably-correct validator (design note §16.2).

Approach: a **total, fuel-based boolean recognizer** `recognizeProd`/`recognizeSeq`/
`recognizeSym` that mirrors the `Denote` `Prop`s exactly, plus a correspondence proof
`recognize… = true ↔ matches…`. Decidability then follows by `decidable_of_iff`.

Note on `decode` (in `FormatSpec.Decode`): that one is `partial` and executable — good
for `#eval`/demos but opaque to the kernel, so NOT usable for this proof. This module
deliberately uses a separate *total* recognizer instead. (The two agree; relating them
is a separate optional lemma.)

The correspondence's key step is that a sequence's split existential
`∃ s1 s2, s = s1 ++ s2 ∧ …` ranges over finitely many split points (the `String`
prefixes), hence is a bounded search. The boolean recognizer makes that search explicit.

STATUS: the recognizer and the `Decidable` wiring are in place; the correspondence
lemma `recognizeProd_iff` — the string-split induction — is the remaining proof
obligation (`sorry`), flagged honestly. Once discharged, `DecidablePred IsWf` is
complete and `decide (IsWf g s)` becomes the validator used in demos/tests.
-/

namespace FormatSpec

/-- Boolean check that a string is a valid terminal token run. -/
def recognizeTerm (tok : TokClass) (ls : LenSpec) (s : String) : Bool :=
  decide (ls.sat s.length) && s.toList.all (fun c => decide (tok.mem c))

mutual

/-- Total boolean recognizer for a symbol, mirroring `matchesSym`. -/
def recognizeSym (g : Grammar) : Nat → Sym → String → Bool
  | _,      .lit l,        s => s == l
  | _,      .term tok ls,  s => recognizeTerm tok ls s
  | 0,      .ref _,        _ => false
  | fuel+1, .ref name,     s =>
      match g.prod? name with
      | none   => false
      | some p => recognizeProd g fuel p s

/-- Total boolean recognizer for a sequence, mirroring `matchesSeq`. The split
    existential becomes an explicit search over all `s.length + 1` split points. -/
def recognizeSeq (g : Grammar) : Nat → Seq → String → Bool
  | _,    [],           s => s == ""
  | fuel, item :: rest, s =>
      let splitOk : Bool :=
        (List.range (s.toList.length + 1)).any (fun i =>
          let s1 := String.ofList (s.toList.take i)
          let s2 := String.ofList (s.toList.drop i)
          recognizeSym g fuel item.sym s1 && recognizeSeq g fuel rest s2)
      if item.optional then splitOk || recognizeSeq g fuel rest s else splitOk

/-- Total boolean recognizer for a production, mirroring `matchesProd`. -/
def recognizeProd (g : Grammar) (fuel : Nat) (p : Production) (s : String) : Bool :=
  p.alts.any (fun alt => recognizeSeq g fuel alt s)

end

/-- Boolean well-formedness: mirror of `IsWf`. -/
def recognize (g : Grammar) (s : String) : Bool :=
  match g.startProd? with
  | none   => false
  | some p => recognizeProd g g.prods.length p s

/-- A string is the append of its `take i`/`drop i` split (at the character level). -/
theorem str_split (s : String) (i : Nat) :
    s = String.ofList (s.toList.take i) ++ String.ofList (s.toList.drop i) := by
  rw [← String.ofList_append, List.take_append_drop, String.ofList_toList]

/-- Split-point lemma (the reusable crux of the sequence case): an append-existential
    over strings is equivalent to a bounded search over the `s.length + 1` split points.
    Standalone `String`/`List.append` fact, independent of the grammar. PROVED. -/
theorem exists_append_iff_any_split (s : String) (P : String → String → Bool) :
    (∃ s1 s2, s = s1 ++ s2 ∧ P s1 s2 = true) ↔
    (List.range (s.toList.length + 1)).any (fun i =>
      P (String.ofList (s.toList.take i)) (String.ofList (s.toList.drop i))) = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨s1, s2, hs, hP⟩
    have happ : s.toList = s1.toList ++ s2.toList := by
      rw [hs, ← String.toList_ofList (l := s1.toList ++ s2.toList),
        String.ofList_append, String.ofList_toList, String.ofList_toList]
    refine ⟨s1.toList.length, ?_, ?_⟩
    · rw [List.mem_range, happ]; simp; omega
    · rw [happ, List.take_left, List.drop_left, String.ofList_toList, String.ofList_toList]
      exact hP
  · rintro ⟨i, _, hP⟩
    exact ⟨_, _, str_split s i, hP⟩

/-- Correspondence: the boolean recognizer agrees with the `Prop` denotation.

    Proof shape (REMAINING): mutual well-founded induction on `fuel` then structural on
    the sequence, with base cases `.lit`/`.term` discharged by `simp` (verified) and the
    sequence case reduced to `exists_append_iff_any_split`. The leaf correspondences
    hold; what remains is assembling the mutual induction. -/
theorem recognizeProd_iff (g : Grammar) (fuel : Nat) (p : Production) (s : String) :
    recognizeProd g fuel p s = true ↔ matchesProd g fuel p s := by
  sorry

/-- `recognize` decides `IsWf`. -/
theorem recognize_iff (g : Grammar) (s : String) :
    recognize g s = true ↔ IsWf g s := by
  unfold recognize IsWf
  cases g.startProd? with
  | none   => simp
  | some p => exact recognizeProd_iff g g.prods.length p s

/-- `IsWf` is decidable — the executable, provably-correct validator. -/
instance (g : Grammar) : DecidablePred (IsWf g) := fun s =>
  decidable_of_iff (recognize g s = true) (recognize_iff g s)

end FormatSpec
