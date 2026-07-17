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

/-- Boolean check that a string is a valid terminal token run — just `decide` on the single
    `matchesTerm` predicate (which owns the digit/length logic), rather than a re-implemented
    char loop. This shares the leaf check across the recognizer and (via `matchesTerm`) the
    decoder, so the token semantics lives in exactly one place. -/
def recognizeTerm (tok : TokClass) (ls : LenSpec) (s : String) : Bool :=
  decide (matchesTerm tok ls s)

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

/-- Terminal correspondence: `recognizeTerm` agrees with `matchesTerm` — now immediate,
    since `recognizeTerm = decide (matchesTerm …)`. -/
theorem term_corr (tok : TokClass) (ls : LenSpec) (s : String) :
    recognizeTerm tok ls s = true ↔ matchesTerm tok ls s := by
  simp only [recognizeTerm, decide_eq_true_eq]

/-- Sequence correspondence, GIVEN the symbol correspondence at the same fuel. By
    structural induction on the sequence; the split-point search collapses to the
    `∃ s1 s2` existential via `exists_append_iff_any_split`. -/
theorem seq_corr_of_sym (g : Grammar) (fuel : Nat)
    (hsym : ∀ sym s, recognizeSym g fuel sym s = true ↔ matchesSym g fuel sym s) :
    ∀ seq s, recognizeSeq g fuel seq s = true ↔ matchesSeq g fuel seq s := by
  intro seq
  induction seq with
  | nil => intro s; simp [recognizeSeq, matchesSeq]
  | cons item rest ih =>
    intro s
    have hsplit : ((List.range (s.toList.length + 1)).any (fun i =>
        recognizeSym g fuel item.sym (String.ofList (s.toList.take i))
          && recognizeSeq g fuel rest (String.ofList (s.toList.drop i))) = true)
        ↔ (∃ s1 s2, s = s1 ++ s2 ∧ matchesSym g fuel item.sym s1 ∧ matchesSeq g fuel rest s2) := by
      rw [← exists_append_iff_any_split s
            (fun a b => recognizeSym g fuel item.sym a && recognizeSeq g fuel rest b)]
      constructor
      · rintro ⟨s1, s2, hs, hP⟩
        rw [Bool.and_eq_true] at hP
        exact ⟨s1, s2, hs, (hsym _ _).mp hP.1, (ih s2).mp hP.2⟩
      · rintro ⟨s1, s2, hs, h1, h2⟩
        exact ⟨s1, s2, hs, by rw [Bool.and_eq_true]; exact ⟨(hsym _ _).mpr h1, (ih s2).mpr h2⟩⟩
    unfold recognizeSeq matchesSeq
    by_cases hopt : item.optional = true
    · simp only [hopt, if_true, Bool.or_eq_true]
      rw [hsplit, ih s]
    · simp only [Bool.not_eq_true] at hopt
      simp only [hopt, Bool.false_eq_true, if_false]
      rw [hsplit]

/-- Production correspondence, GIVEN the sequence correspondence at the same fuel. -/
theorem prod_corr_of_seq (g : Grammar) (fuel : Nat)
    (hseq : ∀ seq s, recognizeSeq g fuel seq s = true ↔ matchesSeq g fuel seq s) :
    ∀ p s, recognizeProd g fuel p s = true ↔ matchesProd g fuel p s := by
  intro p s
  simp only [recognizeProd, matchesProd, List.any_eq_true]
  constructor
  · rintro ⟨alt, hmem, hrec⟩; exact ⟨alt, hmem, (hseq alt s).mp hrec⟩
  · rintro ⟨alt, hmem, hm⟩; exact ⟨alt, hmem, (hseq alt s).mpr hm⟩

/-- Symbol correspondence, by induction on `fuel` (the `ref` case drops to a production
    at `fuel-1`, closed with the sequence/production correspondences at that fuel). -/
theorem sym_corr (g : Grammar) : ∀ fuel sym s,
    recognizeSym g fuel sym s = true ↔ matchesSym g fuel sym s := by
  intro fuel
  induction fuel with
  | zero =>
    intro sym s
    cases sym with
    | lit l => simp [recognizeSym, matchesSym]
    | term tok ls => simp only [recognizeSym, matchesSym]; exact term_corr tok ls s
    | ref name => simp [recognizeSym, matchesSym]
  | succ fuel ih =>
    have hprod := prod_corr_of_seq g fuel (seq_corr_of_sym g fuel ih)
    intro sym s
    cases sym with
    | lit l => simp [recognizeSym, matchesSym]
    | term tok ls => simp only [recognizeSym, matchesSym]; exact term_corr tok ls s
    | ref name =>
      simp only [recognizeSym, matchesSym]
      cases hp : g.prod? name with
      | none => simp
      | some p => simp only []; exact hprod p s

/-- Correspondence: the boolean recognizer agrees with the `Prop` denotation. PROVED. -/
theorem recognizeProd_iff (g : Grammar) (fuel : Nat) (p : Production) (s : String) :
    recognizeProd g fuel p s = true ↔ matchesProd g fuel p s :=
  prod_corr_of_seq g fuel (seq_corr_of_sym g fuel (sym_corr g fuel)) p s

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
