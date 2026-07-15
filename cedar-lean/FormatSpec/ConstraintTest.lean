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

-- `nat NumV4 ≤ 255` — the IPv4 octet bound — is VALUE-dependent (→ SatisfiesConstraints).
example : (cstr% nat NumV4 ≤ 255).isValueDependent = true := by native_decide

-- `noLeadingZero NumV4` is STRING-only (→ IsWf).
example : (cstr% noLeadingZero NumV4).isValueDependent = false := by native_decide

-- The Int64 range bound (Decimal): value-dependent.
example : (cstr% int Integer ≤ 9223372036854775807).isValueDependent = true := by native_decide

/-! ## Evaluation -/

-- `nat NumV4 ≤ 255` holds for "200", fails for "300".
example : (cstr% nat NumV4 ≤ 255).eval (env [("NumV4", "200")]) := by native_decide
example : ¬ (cstr% nat NumV4 ≤ 255).eval (env [("NumV4", "300")]) := by native_decide

-- `noLeadingZero` : "0" ok, "007" bad, "42" ok.
example : (cstr% noLeadingZero X).eval (env [("X", "0")]) := by native_decide
example : ¬ (cstr% noLeadingZero X).eval (env [("X", "007")]) := by native_decide
example : (cstr% noLeadingZero X).eval (env [("X", "42")]) := by native_decide

/-! ## wfPart / valPart split a conjunction into the two layers -/

-- A mixed constraint: `noLeadingZero X ∧ nat X ≤ 255`.
def mixed : Constraint := .and (cstr% noLeadingZero X) (cstr% nat X ≤ 255)

-- wfPart keeps only the string side; on "007" it fails (leading zero)...
example : ¬ mixed.wfPart (env [("X", "007")]) := by native_decide
-- ...even though the value side would pass (7 ≤ 255): valPart is about the bound only.
example : mixed.valPart (env [("X", "007")]) := by native_decide
-- valPart catches the bound violation on "300" (value side)...
example : ¬ mixed.valPart (env [("X", "300")]) := by native_decide
-- ...while wfPart passes on "300" (no leading zero).
example : mixed.wfPart (env [("X", "300")]) := by native_decide

/-! ## Escape hatch: `ConstraintEntry.opaque` for out-of-DSL constraints -/

-- An arbitrary `Env → Bool` check (here: capture "Z" has even length) that the DSL
-- cannot express, declared value-dependent.
def evenLen : ConstraintEntry :=
  .opaque true (fun e => match e "Z" with | some s => s.length % 2 == 0 | none => true)

-- Classifies per its declared flag (value → SatisfiesConstraints)...
example : evenLen.isValueDependent = true := by native_decide
-- ...folds into valPart, not wfPart...
example : evenLen.valPart (env [("Z", "abcd")]) := by native_decide
example : ¬ evenLen.valPart (env [("Z", "abc")]) := by native_decide
example : evenLen.wfPart (env [("Z", "abc")]) := by native_decide  -- vacuous on the wf side

-- A string-classified escape (`opaqueWf`) folds into wfPart instead.
def opaqueString : ConstraintEntry := .opaque false (fun _ => true)
example : opaqueString.isValueDependent = false := by native_decide

end FormatSpec.ConstraintTest
