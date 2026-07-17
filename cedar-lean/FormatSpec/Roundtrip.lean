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

import FormatSpec.Decode

/-!
# `decode` ↔ `IsWf` roundtrip

The executable capture extractor `decode` (from `FormatSpec.Decode`) and the denotational
well-formedness predicate `IsWf` (from `FormatSpec.Denote`) agree on acceptance:

    theorem decodeSome_iff_IsWf (g : Grammar) (s : String) :
        (decode g s).isSome = true ↔ IsWf g s

The proof goes through three mutually-recursive **bridge lemmas** relating each `match*`
combinator's *reachable remainders* to the corresponding `matches*` denotation, with the
capture map `m` and the qualifier `q` (both irrelevant to which remainders are reachable)
quantified away:

    (∃ m, (m, r₂) ∈ matchSym  g q fuel sym cs) ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSym  g fuel sym (String.ofList r₁)
    (∃ m, (m, r₂) ∈ matchSeq  g q fuel seq cs) ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSeq  g fuel seq (String.ofList r₁)
    (∃ m, (m, r₂) ∈ matchProd g q fuel p  cs) ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesProd g fuel p  (String.ofList r₁)

The structure is the standard mutual fuel induction (`sym`/`seq`/`prod`, each given the next
level down):
`matchSym_iter` is proved by induction on `fuel` (the `ref` case at `fuel+1` drops to
`matchProd` at `fuel`); `matchSeq_iter` by induction on the sequence list; `matchProd_iter`
over the alternatives. `decodeSome_iff_IsWf` then instantiates the prod bridge with `r₂ = []`.
-/

namespace FormatSpec

open List


-- lit leaf
theorem lit_leaf (g : Grammar) (q : String) (fuel : Nat) (l : String) (cs r₂ : List Char) :
    (∃ m, (m, r₂) ∈ matchSym g q fuel (Sym.lit l) cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSym g fuel (Sym.lit l) (String.ofList r₁) := by
  have hden : ∀ r₁ : List Char, matchesSym g fuel (Sym.lit l) (String.ofList r₁) ↔ r₁ = l.toList := by
    intro r₁; cases fuel <;> (
      simp only [matchesSym]; rw [← String.toList_inj, String.toList_ofList])
  cases fuel <;> (
    simp only [matchSym]
    constructor
    · rintro ⟨m, hmem⟩
      by_cases h : l.toList.isPrefixOf cs = true
      · simp only [h, if_true, List.mem_singleton] at hmem
        obtain ⟨t, ht⟩ := isPrefixOf_iff_prefix.mp h
        refine ⟨l.toList, ?_, (hden l.toList).mpr rfl⟩
        have hr₂ : r₂ = cs.drop l.toList.length := congrArg Prod.snd hmem
        subst ht; rw [hr₂, List.drop_left]
      · rw [Bool.not_eq_true] at h; rw [h] at hmem; simp at hmem
    · rintro ⟨r₁, hcs, hden'⟩
      rw [(hden r₁).mp hden'] at hcs
      have h : l.toList.isPrefixOf cs = true := by
        rw [hcs]; exact isPrefixOf_iff_prefix.mpr ⟨r₂, rfl⟩
      simp only [h, if_true]; exact ⟨[], by rw [hcs]; simp⟩)

-- term leaf
theorem term_leaf (g : Grammar) (q : String) (fuel : Nat) (tok : TokClass) (ls : LenSpec)
    (cs r₂ : List Char) :
    (∃ m, (m, r₂) ∈ matchSym g q fuel (Sym.term tok ls) cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSym g fuel (Sym.term tok ls) (String.ofList r₁) := by
  cases fuel <;> (
    simp only [matchSym, matchesSym]
    constructor
    · rintro ⟨m, hmem⟩
      rw [List.mem_filterMap] at hmem
      obtain ⟨k, hk, hval⟩ := hmem
      by_cases hok : termPrefixOk tok ls cs k = true
      · rw [hok] at hval; simp only [if_true, Option.some.injEq, Prod.mk.injEq] at hval
        refine ⟨cs.take k, ?_, ?_⟩
        · rw [← hval.2, List.take_append_drop]
        · unfold termPrefixOk at hok
          rw [Bool.and_eq_true] at hok
          exact of_decide_eq_true hok.2
      · rw [Bool.not_eq_true] at hok; rw [hok] at hval; simp at hval
    · rintro ⟨r₁, hcs, hden⟩
      refine ⟨[], ?_⟩
      rw [List.mem_filterMap]
      refine ⟨r₁.length, ?_, ?_⟩
      · rw [List.mem_range, hcs]; simp only [List.length_append]; omega
      · have hok : termPrefixOk tok ls cs r₁.length = true := by
          unfold termPrefixOk
          rw [Bool.and_eq_true]
          refine ⟨?_, ?_⟩
          · rw [decide_eq_true_eq, hcs]; simp
          · rw [decide_eq_true_eq, hcs, List.take_left]; exact hden
        rw [hok]; simp
        rw [hcs, List.drop_left])

-- present block characterization
theorem present_mem (g : Grammar) (q : String) (fuel : Nat) (item : SymItem)
    (rest : Seq) (cs r₂ : List Char) :
    (∃ m, (m, r₂) ∈ (matchSym g q fuel item.sym cs).flatMap (fun x =>
        (matchSeq g q fuel rest x.2).map (fun y => (x.1 ++ y.1, y.2))))
      ↔ ∃ r1, (∃ m1, (m1, r1) ∈ matchSym g q fuel item.sym cs)
              ∧ (∃ m2, (m2, r₂) ∈ matchSeq g q fuel rest r1) := by
  constructor
  · rintro ⟨m, hmem⟩
    rw [List.mem_flatMap] at hmem
    obtain ⟨⟨m1, r1⟩, hmem1, hmem2⟩ := hmem
    rw [List.mem_map] at hmem2
    obtain ⟨⟨m2, r₂'⟩, hmem2', heq⟩ := hmem2
    simp only [Prod.mk.injEq] at heq
    exact ⟨r1, ⟨m1, hmem1⟩, ⟨m2, by rw [← heq.2]; exact hmem2'⟩⟩
  · rintro ⟨r1, ⟨m1, hmem1⟩, ⟨m2, hmem2⟩⟩
    exact ⟨m1 ++ m2, List.mem_flatMap.mpr ⟨(m1, r1), hmem1,
      List.mem_map.mpr ⟨(m2, r₂), hmem2, rfl⟩⟩⟩

-- seq given sym at same fuel
theorem seq_iter (g : Grammar) (q : String) (fuel : Nat)
    (hsym : ∀ sym cs r₂, (∃ m, (m, r₂) ∈ matchSym g q fuel sym cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSym g fuel sym (String.ofList r₁)) :
    ∀ seq cs r₂, (∃ m, (m, r₂) ∈ matchSeq g q fuel seq cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSeq g fuel seq (String.ofList r₁) := by
  intro seq
  induction seq with
  | nil =>
    intro cs r₂
    simp only [matchSeq, matchesSeq, List.mem_singleton]
    constructor
    · rintro ⟨m, heq⟩
      simp only [Prod.mk.injEq] at heq
      exact ⟨[], by rw [heq.2]; simp, rfl⟩
    · rintro ⟨r₁, hcs, hnil⟩
      have : r₁ = [] := by
        have := congrArg String.toList hnil
        rw [String.toList_ofList] at this; simpa using this
      subst this; simp at hcs
      exact ⟨[], by rw [hcs]⟩
  | cons item rest ih =>
    intro cs r₂
    have hpresent : (∃ m, (m, r₂) ∈ (matchSym g q fuel item.sym cs).flatMap (fun x =>
          (matchSeq g q fuel rest x.2).map (fun y => (x.1 ++ y.1, y.2))))
        ↔ (∃ r1 r1', cs = r1 ++ r1' ++ r₂ ∧ matchesSym g fuel item.sym (String.ofList r1)
              ∧ matchesSeq g fuel rest (String.ofList r1')) := by
      rw [present_mem]
      constructor
      · rintro ⟨rMid, hsymm, hseqm⟩
        rw [hsym] at hsymm
        obtain ⟨r1, hcs1, hden1⟩ := hsymm
        rw [ih] at hseqm
        obtain ⟨r1', hmid, hden2⟩ := hseqm
        exact ⟨r1, r1', by rw [hcs1, hmid, List.append_assoc], hden1, hden2⟩
      · rintro ⟨r1, r1', hcs, hden1, hden2⟩
        refine ⟨r1' ++ r₂, ?_, ?_⟩
        · rw [hsym]; exact ⟨r1, by rw [hcs, List.append_assoc], hden1⟩
        · rw [ih]; exact ⟨r1', rfl, hden2⟩
    unfold matchSeq matchesSeq
    by_cases hopt : item.optional = true
    · simp only [hopt, if_true]
      constructor
      · rintro ⟨m, hmem⟩
        rw [List.mem_append] at hmem
        cases hmem with
        | inl h =>
          obtain ⟨r1, r1', hcs, hd1, hd2⟩ := hpresent.mp ⟨m, h⟩
          exact ⟨r1 ++ r1', hcs, Or.inl ⟨String.ofList r1, String.ofList r1',
            by rw [String.ofList_append], hd1, hd2⟩⟩
        | inr h =>
          obtain ⟨r₁, hcs, hd⟩ := (ih cs r₂).mp ⟨m, h⟩
          exact ⟨r₁, hcs, Or.inr hd⟩
      · rintro ⟨r₁, hcs, hd⟩
        cases hd with
        | inl h =>
          obtain ⟨s1, s2, hsplit, hd1, hd2⟩ := h
          have hlist : r₁ = s1.toList ++ s2.toList := by
            have := congrArg String.toList hsplit
            rw [String.toList_ofList, String.toList_append] at this; exact this
          obtain ⟨m, hm⟩ := hpresent.mpr ⟨s1.toList, s2.toList,
            by rw [hcs, hlist, List.append_assoc],
            by rw [String.ofList_toList]; exact hd1,
            by rw [String.ofList_toList]; exact hd2⟩
          exact ⟨m, by rw [List.mem_append]; exact Or.inl hm⟩
        | inr h =>
          obtain ⟨m, hm⟩ := (ih cs r₂).mpr ⟨r₁, hcs, h⟩
          exact ⟨m, by rw [List.mem_append]; exact Or.inr hm⟩
    · simp only [Bool.not_eq_true] at hopt
      simp only [hopt, Bool.false_eq_true, if_false]
      rw [hpresent]
      constructor
      · rintro ⟨r1, r1', hcs, hd1, hd2⟩
        exact ⟨r1 ++ r1', hcs, String.ofList r1, String.ofList r1',
          by rw [String.ofList_append], hd1, hd2⟩
      · rintro ⟨r₁, hcs, s1, s2, hsplit, hd1, hd2⟩
        have hlist : r₁ = s1.toList ++ s2.toList := by
          have := congrArg String.toList hsplit
          rw [String.toList_ofList, String.toList_append] at this; exact this
        exact ⟨s1.toList, s2.toList, by rw [hcs, hlist, List.append_assoc],
          by rw [String.ofList_toList]; exact hd1,
          by rw [String.ofList_toList]; exact hd2⟩

-- prod given seq at same fuel
theorem prod_iter (g : Grammar) (q : String) (fuel : Nat) (p : Production) (cs r₂ : List Char)
    (hseq : ∀ seq cs r₂, (∃ m, (m, r₂) ∈ matchSeq g q fuel seq cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSeq g fuel seq (String.ofList r₁)) :
    (∃ m, (m, r₂) ∈ matchProd g q fuel p cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesProd g fuel p (String.ofList r₁) := by
  simp only [matchProd, matchesProd]
  constructor
  · rintro ⟨m, hmem⟩
    rw [List.mem_flatMap] at hmem
    obtain ⟨alt, halt, hm⟩ := hmem
    obtain ⟨r₁, hcs, hd⟩ := (hseq alt cs r₂).mp ⟨m, hm⟩
    exact ⟨r₁, hcs, alt, halt, hd⟩
  · rintro ⟨r₁, hcs, alt, halt, hd⟩
    obtain ⟨m, hm⟩ := (hseq alt cs r₂).mpr ⟨r₁, hcs, hd⟩
    exact ⟨m, List.mem_flatMap.mpr ⟨alt, halt, hm⟩⟩

-- sym by fuel induction (q universally quantified so the ref case can re-instantiate it)
theorem sym_iter (g : Grammar) : ∀ fuel (q : String) sym cs r₂,
    (∃ m, (m, r₂) ∈ matchSym g q fuel sym cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSym g fuel sym (String.ofList r₁) := by
  intro fuel
  induction fuel with
  | zero =>
    intro q sym cs r₂
    cases sym with
    | lit l => exact lit_leaf g q 0 l cs r₂
    | term tok ls => exact term_leaf g q 0 tok ls cs r₂
    | ref name =>
      simp only [matchSym, matchesSym, List.not_mem_nil, exists_false]
      simp
  | succ fuel ih =>
    intro q sym cs r₂
    cases sym with
    | lit l => exact lit_leaf g q (fuel+1) l cs r₂
    | term tok ls => exact term_leaf g q (fuel+1) tok ls cs r₂
    | ref name =>
      have hprod : ∀ (q' : String) p cs r₂,
          (∃ m, (m, r₂) ∈ matchProd g q' fuel p cs)
            ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesProd g fuel p (String.ofList r₁) := by
        intro q' p cs r₂
        exact prod_iter g q' fuel p cs r₂
          (seq_iter g q' fuel (fun sym cs r₂ => ih q' sym cs r₂))
      simp only [matchSym, matchesSym]
      cases hp : g.prod? name with
      | none => simp
      | some p =>
        simp only []
        rw [← hprod name p cs r₂]
        constructor
        · rintro ⟨m, hmem⟩
          rw [List.mem_map] at hmem
          obtain ⟨⟨m0, r0⟩, hmem0, heq⟩ := hmem
          simp only [Prod.mk.injEq] at heq
          exact ⟨m0, by rw [← heq.2]; exact hmem0⟩
        · rintro ⟨m, hmem⟩
          exact ⟨_, List.mem_map.mpr ⟨(m, r₂), hmem, rfl⟩⟩

-- top-level bridges
theorem matchSeq_iter (g : Grammar) (q : String) (fuel : Nat) :
    ∀ seq cs r₂, (∃ m, (m, r₂) ∈ matchSeq g q fuel seq cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesSeq g fuel seq (String.ofList r₁) :=
  seq_iter g q fuel (fun sym cs r₂ => sym_iter g fuel q sym cs r₂)

theorem matchProd_iter (g : Grammar) (q : String) (fuel : Nat) (p : Production) (cs r₂ : List Char) :
    (∃ m, (m, r₂) ∈ matchProd g q fuel p cs)
      ↔ ∃ r₁, cs = r₁ ++ r₂ ∧ matchesProd g fuel p (String.ofList r₁) :=
  prod_iter g q fuel p cs r₂ (matchSeq_iter g q fuel)

theorem decodeSome_iff_IsWf (g : Grammar) (s : String) :
    (decode g s).isSome = true ↔ IsWf g s := by
  unfold decode IsWf
  cases hstart : g.startProd? with
  | none => simp
  | some p =>
    simp only [Option.isSome_map]
    -- head?.isSome of the filtered list ↔ ∃ elem with empty remainder
    have hhead : (((matchProd g "" g.prods.length p s.toList).filter
        (fun x => x.2.isEmpty)).head?).isSome = true
        ↔ ∃ m, (m, ([] : List Char)) ∈ matchProd g "" g.prods.length p s.toList := by
      have hne : ∀ L : List (CaptureMap × List Char), L.head?.isSome = true ↔ ∃ x, x ∈ L := by
        intro L; cases L with
        | nil => simp
        | cons a t => simp
      rw [hne]
      constructor
      · rintro ⟨x, hx⟩
        rw [List.mem_filter] at hx
        refine ⟨x.1, ?_⟩
        have hx2 : x.2 = [] := by
          have := hx.2; simp only [List.isEmpty_iff] at this; exact this
        rw [← hx2]; exact hx.1
      · rintro ⟨m, hmem⟩
        exact ⟨(m, []), by rw [List.mem_filter]; exact ⟨hmem, by simp⟩⟩
    rw [hhead, matchProd_iter g "" g.prods.length p s.toList []]
    constructor
    · rintro ⟨r₁, hcs, hd⟩
      have : r₁ = s.toList := by simpa using hcs.symm
      rw [this, String.ofList_toList] at hd; exact hd
    · intro hd
      exact ⟨s.toList, by simp, by rw [String.ofList_toList]; exact hd⟩

/-- `IsWf` is decidable — the executable, provably-correct validator, obtained DIRECTLY from
    the total `decode` (`(decode g s).isSome` is a decidable `Bool` test) via the roundtrip.
    This is the sole consumer of well-formedness decidability; because `decode` already exists
    (it drives `computeValue`/`envOf`), no separate boolean recognizer walk is needed. -/
instance (g : Grammar) : DecidablePred (IsWf g) := fun s =>
  decidable_of_iff ((decode g s).isSome = true) (decodeSome_iff_IsWf g s)

end FormatSpec

