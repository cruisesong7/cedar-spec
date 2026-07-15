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

/-!
# Decimal demo: input the grammar, get the spec

Transcribes `doc/CedarDoc/Decimal.lean` into one `format_spec` block and exercises the
generated spec (`grammar`, `constraints`, `valueExpr`) end-to-end via `decode`,
`computeValue`, and the decidable recognizer `IsWf`.
-/

namespace FormatSpec.DecimalDemo
open FormatSpec

-- ════════════════════════════════════════════════════════════════════════════
--  INPUT — the doc's Decimal grammar + constraint + value, transcribed
-- ════════════════════════════════════════════════════════════════════════════
--   Decimal  ::= Integer '.' Fraction
--   Integer  ::= ['-'] Digit⁺
--   Fraction ::= Digit{1,4}
--   value(Decimal) = int(Integer)·10⁴ + sign·nat(Fraction)·10^(4 − |Fraction|)
--   Constraint: value ∈ [Int64.MIN, Int64.MAX]   (Int64 range; -2^63 .. 2^63-1)
format_spec Decimal where
  grammar
    Decimal  ::= Integer "." Fraction
    Integer  ::= ["-"] digit+
    Fraction ::= digit{1,4}
  value
    int Integer * 10 ^ 4 + sign Integer * nat Fraction * 10 ^ (4 - len Fraction)
  constraints
    value ∈ [Int64.MIN, Int64.MAX]

-- ════════════════════════════════════════════════════════════════════════════
--  OUTPUT — the generated spec, run on sample strings
-- ════════════════════════════════════════════════════════════════════════════

-- The generated declarations:
#check (Decimal.grammar     : Grammar)
#check (Decimal.constraints : List ConstraintEntry)
#check (Decimal.valueExpr   : ValExpr)

-- `decode` extracts the captures:  "1.5" ↦ Integer="1", Fraction="5"
#eval decode Decimal.grammar "1.5"       -- some [("Integer","1"), ("Fraction","5")]
#eval decode Decimal.grammar "-12.34"    -- some [("Integer","-12"), ("Fraction","34")]
#eval decode Decimal.grammar "1.x"       -- none (fraction not digits)
#eval decode Decimal.grammar "1"         -- none (no '.')

-- `computeValue` = eval the value formula on the decoded captures (fixed-point ×10⁴):
#eval computeValue Decimal.grammar Decimal.valueExpr "1.2345"   -- some 12345
#eval computeValue Decimal.grammar Decimal.valueExpr "1.5"      -- some 15000
#eval computeValue Decimal.grammar Decimal.valueExpr "-1.5"     -- some (-15000)
#eval computeValue Decimal.grammar Decimal.valueExpr "1.x"      -- none

-- Executable validator: `decode …` succeeds iff the string is well-formed. (`decode`
-- is the reference recognizer-with-captures; the theorem `IsWf ↔ (decode).isSome`, which
-- would make `IsWf` itself `Decidable`, is the next proof milestone.)
#eval (decode Decimal.grammar "1.5").isSome     -- true
#eval (decode Decimal.grammar "1.x").isSome     -- false
#eval (decode Decimal.grammar "12.3456").isSome -- true

-- Machine-checked acceptance/rejection via the executable recognizer:
example : (decode Decimal.grammar "1.5").isSome    = true  := by native_decide
example : (decode Decimal.grammar "-12.34").isSome = true  := by native_decide
example : (decode Decimal.grammar "1.x").isSome    = false := by native_decide
example : (decode Decimal.grammar "1").isSome      = false := by native_decide

-- Machine-checked value computations:
example : computeValue Decimal.grammar Decimal.valueExpr "1.2345" = some 12345 := by native_decide
example : computeValue Decimal.grammar Decimal.valueExpr "-1.5"   = some (-15000) := by native_decide

end FormatSpec.DecimalDemo
