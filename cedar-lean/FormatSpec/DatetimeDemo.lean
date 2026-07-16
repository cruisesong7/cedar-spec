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
# Datetime demo — the hard case: 5-way alternation + calendar constraints

Transcribes `doc/CedarDoc/Datetime.lean`. This is the generality stress test:
* top-level **alternation** (`Datetime ::= Date | Date "T" Time "Z" | …`) — needs the
  DSL's `|` support;
* inline `('+' | '-')` in `Offset` — desugared here into two `Offset` alternatives;
* fixed-width terminals (`Digit{4}`, `Digit{2}`, `Digit{3}`);
* value = epoch-millis via calendar arithmetic — NON-affine, NON-flat-in-DSL, so it goes
  to the `value opaque` escape (honest boundary); constraints likewise reference calendar
  helpers, shown here as the doc's bounds on the numeric components.
-/

namespace FormatSpec.DatetimeDemo
open FormatSpec

format_spec Datetime where
  grammar
    Datetime ::= Date
               | Date "T" Time "Z"
               | Date "T" Time "." SSS "Z"
               | Date "T" Time Offset
               | Date "T" Time "." SSS Offset
    Date     ::= YYYY "-" MM "-" DD
    Time     ::= hh ":" mm ":" ss
    Offset   ::= "+" hh mm
               | "-" hh mm
    SSS      ::= digit{3}
    YYYY     ::= digit{4}
    MM       ::= digit{2}
    DD       ::= digit{2}
    hh       ::= digit{2}
    mm       ::= digit{2}
    ss       ::= digit{2}
  to "FormatSpec/Generated/Datetime.lean"

-- The 5 top-level forms + the 2-alt Offset exercise alternation end to end.
#check (Datetime.IsWf.Datetime : String → Prop)
#check (Datetime.IsWf.Offset   : String → Prop)
#check (Datetime.IsWf.Date     : String → Prop)

end FormatSpec.DatetimeDemo
