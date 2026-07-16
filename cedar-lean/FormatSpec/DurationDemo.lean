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

-- Grammar only (no `value`/`constraints` yet — see the note below on the `nat` subtlety).
format_spec Duration where
  grammar
    Duration   ::= ["-"] Components
    Components ::= [Days] [Hours] [Minutes] [Seconds] [Millis]
    Days       ::= digit+ "d"
    Hours      ::= digit+ "h"
    Minutes    ::= digit+ "m"
    Seconds    ::= digit+ "s"
    Millis     ::= digit+ "ms"
  to "FormatSpec/Generated/Duration.lean"

-- Inspect the generated per-production predicates + their binder names.
#check (Duration.IsWf.Duration   : String → Prop)
#check (Duration.IsWf.Components : String → Prop)
#check (Duration.IsWf.Days       : String → Prop)

/-!
NOTE on `value` (a real design finding, deferred): the doc's `value` uses
`d = nat value of Days component`, i.e. the *digits* of `Days`. But `Days ::= Digit⁺ 'd'`
captures the whole `"1d"`, and our `nat Days` reads the entire captured substring — so
`nat Days` on `"1d"` is garbage. To compute the duration value we'd need either to
capture the digit-run as its own nonterminal (`Days ::= DayNum "d"`, `DayNum ::= digit+`,
then `nat DayNum`), or a value-DSL "numeric prefix" reader. Surfaced by trying Duration;
addressed separately.
-/

end FormatSpec.DurationDemo
