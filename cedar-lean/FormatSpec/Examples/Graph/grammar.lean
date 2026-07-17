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

import FormatSpec.Syntax
import FormatSpec.Decode
import FormatSpec.Roundtrip

/-!
# Graph example — a STRUCTURED (non-`Int`) value via the `value'` escape

The SAT-community encoding of a graph on `n` vertices as the upper-triangle of its adjacency
matrix, written as a bit string. For `n = 3` the upper triangle has `T(3) = 3·2/2 = 3` cells,
one per unordered pair, in the order `(0,1) (0,2) (1,2)`:

```
G   ::= E01 " " E02 " " E12   -- 3 upper-triangle cells
Exy ::= "0" | "1"             -- edge present?
```

This exercises the **arbitrary-typed value** feature: the `value'` escape parses the bit
string into a structured `Graph3` (an edge list over vertices `{0,1,2}`), NOT an `Int`. The
generated `Graph.computeValue : String → Option Graph3` is a real string→graph parser whose
correctness is tied to the readable spec by the same machinery as the scalar examples
(`IsWf_equiv`, the `decode` roundtrip); the value type simply flows through — it never enters
those proofs, so structured values are proof-neutral (the whole point: acceptance is
`IsWf ∧ SatisfiesConstraints`, both value-type-free; the value is a separate function).

Design notes:
* **Fixed `n = 3`.** The grammar is fixed-arity: the vertex count is a compile-time constant,
  so the length is exactly `T(3)`, and each cell is a DISTINCT named capture (`E01`/`E02`/`E12`)
  read independently by the value function — no `rep` needed. A single format spanning ALL `n`
  would need a data-dependent count ("read `n`, then read `T(n)` cells"), which is the
  hand-written-`decode` / non-regular case the design flags; out of scope by construction.
* **Why not larger `n` here?** `n = 3` (3 cells) keeps the flat `G` sequence within the
  reconciliation closer's nested-∃ normalization budget. Larger `n` (a deeper flat sequence)
  hits the SAME closer scaling limit noted for wide sequences generally — orthogonal to the
  value-type feature this example demonstrates. Expressing the cells with `rep … sepBy " "`
  would collapse the sequence to one node (lifting that limit), but reading the individual
  repeated cells back for the value function needs rep-element capture exposure (a separate,
  planned increment); with distinct named captures the value reads each cell directly today.
* The value is written with the `value'` ESCAPE (`toGraph3`), because a graph is outside the
  scalar-arithmetic `value` DSL — exactly what the escape hatch is for.

Writes `spec.lean` beside this file.
-/

namespace FormatSpec.Examples.Graph
open FormatSpec

/-- A simple graph on 3 vertices `{0,1,2}`, as the set of present edges. The STRUCTURED
    value the parser produces (a custom type — not an `Int`). -/
structure Graph3 where
  edges : List (Nat × Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Author-supplied structured decoder: the three upper-triangle edge bits → the graph. Each
    `"1"` cell contributes its pair; `"0"` contributes nothing. This is the `value'` escape:
    an ordinary Lean function over the decoded component strings, returning a `Graph3`. -/
def toGraph3 (e01 e02 e12 : String) : Graph3 :=
  let cell (b : String) (p : Nat × Nat) : List (Nat × Nat) := if b == "1" then [p] else []
  { edges := cell e01 (0,1) ++ cell e02 (0,2) ++ cell e12 (1,2) }

format_spec Graph where
  grammar
    G   ::= E01 " " E02 " " E12
    E01 ::= "0" | "1"
    E02 ::= "0" | "1"
    E12 ::= "0" | "1"
  value'
    toGraph3 E01 E02 E12
  to "FormatSpec/Examples/Graph"

#check (Graph.IsWf.G       : String → Prop)
#check (Graph.computeValue : String → Option Graph3)   -- STRUCTURED value, not Int

#eval Graph.computeValue "1 0 1"   -- some { edges := [(0,1),(1,2)] }      (a path 0-1-2)
#eval Graph.computeValue "1 1 1"   -- some { edges := [(0,1),(0,2),(1,2)] } (triangle K₃)
#eval Graph.computeValue "0 0 0"   -- some { edges := [] }                  (empty graph)
#eval decide (Graph.IsValid "1 0 1")  -- true
#eval decide (Graph.IsValid "1 0")    -- false (only 2 cells — grammar)
#eval decide (Graph.IsValid "2 0 1")  -- false ("2" not a bit — grammar)

#check (Graph.IsWf_equiv : ∀ s, IsWf Graph.grammar s ↔ Graph.IsWf.G s)
example : DecidablePred Graph.IsValid := inferInstance

end FormatSpec.Examples.Graph
