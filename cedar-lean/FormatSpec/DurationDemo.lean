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
import FormatSpec.Decidable

/-!
# Duration demo — stresses the naming with five optional unit components

Transcribes `doc/CedarDoc/Duration.lean`:
```
Duration   ::= ['-'] Components
Components ::= [Days] [Hours] [Minutes] [Seconds] [Millis]
Days       ::= Digit⁺ 'd'   (etc.)
```
This exercises the peel-form binder naming (optional refs → `days`/`hours`/…) far more
than Decimal did. Grammar + IsWf only for now; see the note on `value` at the end.
-/

namespace FormatSpec.DurationDemo
open FormatSpec

-- SUB-CAPTURE PATTERN: each unit's digit-run is its own nonterminal (`DDays ::= digit+`),
-- so `value` can read the number via `nat DDays` — `Days ::= DDays "d"` captures both the
-- full `"1d"` (as `Days`) AND the digits `"1"` (as `DDays`), since `decode` records nested
-- refs. This resolves the "`nat Days` on `"1d"` is garbage" problem with no new machinery.
-- Full spec: grammar + value + Int64 constraint.
format_spec Duration where
  grammar
    Duration   ::= ["-"] Components
    Components ::= [Days] [Hours] [Minutes] [Seconds] [Millis]
    Days       ::= DDays "d"
    Hours      ::= DHours "h"
    Minutes    ::= DMinutes "m"
    Seconds    ::= DSeconds "s"
    Millis     ::= DMillis "ms"
    DDays      ::= digit+
    DHours     ::= digit+
    DMinutes   ::= digit+
    DSeconds   ::= digit+
    DMillis    ::= digit+
  value
    nat DDays * 86400000 + nat DHours * 3600000 + nat DMinutes * 60000
      + nat DSeconds * 1000 + nat DMillis
  constraints
    value ∈ [Int64.MIN, Int64.MAX]
  to "FormatSpec/Generated/Duration.lean"

-- Inspect the generated per-production predicates + their binder names.
#check (Duration.IsWf.Duration   : String → Prop)
#check (Duration.IsWf.Components : String → Prop)
#check (Duration.IsWf.Days       : String → Prop)

-- The value function reads the sub-captured digit runs (not the "1d" strings):
--   "1d2h30m" = 1·86400000 + 2·3600000 + 30·60000 = 95400000
#eval Duration.computeValue "1d2h30m"   -- some 95400000
#eval Duration.computeValue "500ms"     -- some 500
#eval Duration.computeValue "2h"        -- some 7200000 (other units absent → 0)

end FormatSpec.DurationDemo
