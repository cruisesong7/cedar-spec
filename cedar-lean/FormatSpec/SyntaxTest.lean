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
import FormatSpec.Classify
import FormatSpec.Examples

/-!
# DSL end-to-end test

Uses the `format_spec` command with the doc-style `::=` notation and checks the
elaborated `Grammar` matches the hand-written `Examples` transcription, confirming the
surface syntax → core pipeline.
-/

namespace FormatSpec.SyntaxTest

open FormatSpec

-- Decimal via the DSL (cf. `doc/CedarDoc/Decimal.lean` grammar). Grammar-only.
format_spec Decimal where
  grammar
    Decimal  ::= Integer "." Fraction
    Integer  ::= ["-"] digit+
    Fraction ::= digit{1,4}

-- IPv4 via the DSL, exercising all three sections (grammar/constraints/value).
format_spec IPv4 where
  grammar
    IPv4  ::= Group "." Group "." Group "." Group
    Group ::= digit{1,3}
  constraints
    fun s => s.length ≤ 15,
    fun s => ¬ s.startsWith "."
  value
    fun (s : String) => s.length

-- The DSL output matches the hand-written grammar values.
example : Decimal.grammar = Examples.decimal := by decide
example : IPv4.grammar = Examples.ipv4 := by decide

-- And the DSL-produced grammars are in-class (references resolve, acyclic).
example : Decimal.grammar.ok = true := by native_decide
example : IPv4.grammar.ok = true := by native_decide

-- The optional sections generate their auxiliary defs.
example : IPv4.constraints.length = 2 := by native_decide
example : IPv4.valueFn "abc" = 3 := by native_decide

end FormatSpec.SyntaxTest
