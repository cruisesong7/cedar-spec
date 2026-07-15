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
# Grammar denotation tests

Validate that the generated `IsWf` predicate means what it should, by proving
acceptance (with explicit substring witnesses) on small grammars exercising each
denotation case: literal, terminal, and reference+sequence.

The leaf predicates (`matchesTerm`, token class, length) are `Decidable` (see
`Denote.lean`), so leaf goals close by `decide`. The structural existentials (the
substring split) are still supplied by hand — full `by decide` acceptance for the real
grammars is the next milestone (deciding the string-split ∃).
-/

namespace FormatSpec.DenoteTest

open FormatSpec

/-! ## A single literal: `S ::= "hi"` -/

def litGrammar : Grammar where
  start := "S"
  prods := [{ name := "S", alts := [[{ sym := .lit "hi" }]] }]

example : IsWf litGrammar "hi" := by
  have h : litGrammar.startProd? = some { name := "S", alts := [[{ sym := .lit "hi" }]] } := by decide
  unfold IsWf; rw [h]; unfold matchesProd
  refine ⟨[{ sym := .lit "hi" }], by decide, ?_⟩
  unfold matchesSeq
  exact ⟨"hi", "", by decide, by simp [matchesSym], by simp [matchesSeq]⟩

/-! ## A single terminal: `S ::= digit{1,3}` -/

def digitGrammar : Grammar where
  start := "S"
  prods := [{ name := "S", alts := [[{ sym := .term .digit (.between 1 3) }]] }]

example : IsWf digitGrammar "42" := by
  have h : digitGrammar.startProd? = some { name := "S", alts := [[{ sym := .term .digit (.between 1 3) }]] } := by decide
  unfold IsWf; rw [h]; unfold matchesProd
  refine ⟨[{ sym := .term .digit (.between 1 3) }], by decide, ?_⟩
  unfold matchesSeq
  refine ⟨"42", "", by decide, ?_, by simp [matchesSeq]⟩
  show matchesSym _ _ _ _
  simp only [matchesSym]
  decide

/-! ## Reference + sequence + literal: `S ::= A "!"`, `A ::= digit{1}` -/

def refGrammar : Grammar where
  start := "S"
  prods := [
    { name := "S", alts := [[{ sym := .ref "A" }, { sym := .lit "!" }]] },
    { name := "A", alts := [[{ sym := .term .digit (.exactly 1) }]] }
  ]

example : IsWf refGrammar "7!" := by
  have h : refGrammar.startProd? = some { name := "S", alts := [[{ sym := .ref "A" }, { sym := .lit "!" }]] } := by decide
  unfold IsWf; rw [h]; unfold matchesProd
  refine ⟨[{ sym := .ref "A" }, { sym := .lit "!" }], by decide, ?_⟩
  unfold matchesSeq
  refine ⟨"7", "!", by decide, ?_, ?_⟩
  · -- "7" matches ref A: step fuel into production A, digit{1}
    show matchesSym _ refGrammar.prods.length _ _
    have hlen : refGrammar.prods.length = 1 + 1 := by decide
    rw [hlen]
    simp only [matchesSym]
    have hA : refGrammar.prod? "A" = some { name := "A", alts := [[{ sym := .term .digit (.exactly 1) }]] } := by decide
    rw [hA]; unfold matchesProd
    refine ⟨[{ sym := .term .digit (.exactly 1) }], by decide, ?_⟩
    unfold matchesSeq
    refine ⟨"7", "", by decide, ?_, by simp [matchesSeq]⟩
    show matchesSym _ _ _ _
    simp only [matchesSym]
    decide
  · -- tail "!" = "!" ++ ""
    unfold matchesSeq
    exact ⟨"!", "", by decide, by simp [matchesSym], by simp [matchesSeq]⟩

end FormatSpec.DenoteTest
