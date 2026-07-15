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

import FormatSpec.Value

/-!
# Value-DSL tests

Transcribe the doc `value(X) = …` formulas via `val%`, then check the denotation
(`eval`) computes the intended values on sample capture environments.
-/

namespace FormatSpec.ValueTest

open FormatSpec

/-- Test environment builder from an association list. -/
def env (pairs : List (String × String)) : Env := fun k =>
  (pairs.find? (·.1 == k)).map (·.2)

/-!
## Decimal

Doc: `value(Decimal) = int(Integer) × 10⁴ + sign × nat(Fraction) × 10^(4 − |Fraction|)`
-/

def decimalValue : ValExpr :=
  val% int Integer * 10 ^ 4 + sign Integer * nat Fraction * 10 ^ (4 - len Fraction)

-- `1.2345`  →  Integer="1", Fraction="2345"  →  1·10⁴ + 2345·10⁰ = 12345
example : decimalValue.eval (env [("Integer", "1"), ("Fraction", "2345")]) = 12345 := by
  native_decide

-- `1.5`  →  Integer="1", Fraction="5"  →  1·10⁴ + 5·10³ = 15000
example : decimalValue.eval (env [("Integer", "1"), ("Fraction", "5")]) = 15000 := by
  native_decide

-- `-1.5` →  Integer="-1", Fraction="5" →  -1·10⁴ + (-1)·5·10³ = -15000
example : decimalValue.eval (env [("Integer", "-1"), ("Fraction", "5")]) = -15000 := by
  native_decide

/-!
## Duration

Doc: `value(Duration) = sign × (d × 86400000 + h × 3600000 + m × 60000 + s × 1000 + ms)`
(components 0 if omitted — handled by `eval`'s absent-field default).
-/

def durationValue : ValExpr :=
  val% nat Days * 86400000 + nat Hours * 3600000 + nat Minutes * 60000
       + nat Seconds * 1000 + nat Millis

-- `1d2h30m`  →  1·86400000 + 2·3600000 + 30·60000 = 95400000
example : durationValue.eval (env [("Days", "1"), ("Hours", "2"), ("Minutes", "30")]) = 95400000 := by
  native_decide

-- omitted components read as 0: `500ms` → 500
example : durationValue.eval (env [("Millis", "500")]) = 500 := by
  native_decide

-- Operator precedence: `^` binds tighter than `*`, `*` tighter than `+`.
example : (val% 2 + 3 * 4 ^ 2).eval (env []) = 50 := by native_decide

end FormatSpec.ValueTest
