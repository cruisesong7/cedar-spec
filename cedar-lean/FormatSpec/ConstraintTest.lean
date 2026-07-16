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

import FormatSpec.Constraint

/-!
# Constraint-DSL tests

Check that constraints parse via `cstr%`, classify correctly (string → `IsWf`, value →
`SatisfiesConstraints`), and evaluate as intended.
-/

namespace FormatSpec.ConstraintTest

open FormatSpec

def env (pairs : List (String × String)) : Env := fun k =>
  (pairs.find? (·.1 == k)).map (·.2)

/-! ## Classification: value-dependence routes to the right layer -/

-- Classification is pure structural recursion (no String externs), so `decide` PROVES
-- it — these are real theorems, axiom-free.
-- `nat NumV4 ≤ 255` — the IPv4 octet bound — is VALUE-dependent (→ SatisfiesConstraints).
example : (cstr% nat NumV4 ≤ 255).isValueDependent = true := by decide
-- `noLeadingZero NumV4` is STRING-only (→ IsWf).
example : (cstr% noLeadingZero NumV4).isValueDependent = false := by decide
-- The Int64 range bound (Decimal): value-dependent.
example : (cstr% int Integer ≤ 9223372036854775807).isValueDependent = true := by decide

/-! ## Evaluation (`#guard`: build-time checks — `.eval` touches String externs, so
     kernel `decide` can't reduce it and we avoid `native_decide`'s axiom). -/

-- `nat NumV4 ≤ 255` holds for "200", fails for "300".
#guard decide ((cstr% nat NumV4 ≤ 255).eval (env [("NumV4", "200")]))
#guard ! decide ((cstr% nat NumV4 ≤ 255).eval (env [("NumV4", "300")]))
-- `noLeadingZero` : "0" ok, "007" bad, "42" ok.
#guard decide ((cstr% noLeadingZero X).eval (env [("X", "0")]))
#guard ! decide ((cstr% noLeadingZero X).eval (env [("X", "007")]))
#guard decide ((cstr% noLeadingZero X).eval (env [("X", "42")]))

/-! ## wfPart / valPart split a conjunction into the two layers -/

-- A mixed constraint: `noLeadingZero X ∧ nat X ≤ 255`.
def mixed : Constraint := .and (cstr% noLeadingZero X) (cstr% nat X ≤ 255)

-- wfPart keeps only the string side; on "007" it fails (leading zero)...
#guard ! decide (mixed.wfPart (env [("X", "007")]))
-- ...even though the value side would pass (7 ≤ 255): valPart is about the bound only.
#guard decide (mixed.valPart (env [("X", "007")]))
-- valPart catches the bound violation on "300" (value side)...
#guard ! decide (mixed.valPart (env [("X", "300")]))
-- ...while wfPart passes on "300" (no leading zero).
#guard decide (mixed.wfPart (env [("X", "300")]))

/-! ## Escape hatch: `ConstraintEntry.opaque` for out-of-DSL constraints -/

-- An arbitrary `Env → Bool` check (here: capture "Z" has even length) that the DSL
-- cannot express, declared value-dependent.
def evenLen : ConstraintEntry :=
  .opaque true (fun e => match e "Z" with | some s => s.length % 2 == 0 | none => true)

-- Classifies per its declared flag (value → SatisfiesConstraints)...
example : evenLen.isValueDependent = true := by decide
-- ...folds into valPart, not wfPart...
#guard decide (evenLen.valPart (env [("Z", "abcd")]))
#guard ! decide (evenLen.valPart (env [("Z", "abc")]))
#guard decide (evenLen.wfPart (env [("Z", "abc")]))  -- vacuous on the wf side

-- A string-classified escape (`opaqueWf`) folds into wfPart instead.
def opaqueString : ConstraintEntry := .opaque false (fun _ => true)
example : opaqueString.isValueDependent = false := by decide

end FormatSpec.ConstraintTest
