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

import FormatSpec.Grammar
import FormatSpec.Denote
import FormatSpec.Constraint
import FormatSpec.Decode

/-!
# Assembling the bundled spec

The `format_spec` command emits the *ingredients* — the grammar, the constraint list,
and the value expression. This module bundles them into the named predicates of the
design-note contract (§16.1):

* `isWf`                — grammar well-formedness ∧ the string-only (`wfPart`) constraints
* `satisfiesConstraints` — the value-dependent (`valPart`) constraints
* `isAccepted`         — `isWf ∧ satisfiesConstraints` (⟺ the parser accepts the string)

All three are phrased against the capture environment produced by `decode`. Constraints
of a not-well-formed string are vacuously satisfied (`decode` fails ⟹ no env ⟹ the
constraint list is checked against the empty environment, matching "constraints only
constrain well-formed strings").

Note: these use `decode` (executable, `partial`) for the environment, so they are
definitions for *running*/bundling, not yet the proof-facing forms. The proof-facing
`IsWf` lives in `Denote`; relating the two is part of the contract-theorem milestone.
-/

namespace FormatSpec

/-- The capture environment `decode` assigns to `s` (empty if not well-formed). -/
def envOf (g : Grammar) (s : String) : Env :=
  match decode g s with
  | some m => m.toEnv
  | none   => fun _ => none

/-- Well-formedness: the grammar recognizes `s` AND every string-only constraint
    (`wfPart`) holds on its capture environment. -/
def isWf (g : Grammar) (cs : List ConstraintEntry) (s : String) : Prop :=
  (decode g s).isSome = true ∧ ∀ c ∈ cs, c.wfPart (envOf g s)

/-- The value-dependent constraints hold on `s`'s capture environment. -/
def satisfiesConstraints (g : Grammar) (cs : List ConstraintEntry) (s : String) : Prop :=
  ∀ c ∈ cs, c.valPart (envOf g s)

/-- The parser accepts `s`: well-formed and all constraints satisfied. -/
def isAccepted (g : Grammar) (cs : List ConstraintEntry) (s : String) : Prop :=
  isWf g cs s ∧ satisfiesConstraints g cs s

instance (g : Grammar) (cs : List ConstraintEntry) (s : String) :
    Decidable (isWf g cs s) := by unfold isWf; infer_instance
instance (g : Grammar) (cs : List ConstraintEntry) (s : String) :
    Decidable (satisfiesConstraints g cs s) := by unfold satisfiesConstraints; infer_instance
instance (g : Grammar) (cs : List ConstraintEntry) (s : String) :
    Decidable (isAccepted g cs s) := by unfold isAccepted; infer_instance

end FormatSpec
