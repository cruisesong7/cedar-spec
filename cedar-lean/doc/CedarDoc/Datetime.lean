import VersoManual
import Cedar.Spec.Ext.Datetime

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Cedar.Spec.Ext

set_option verso.code.warnLineLength 80

#doc (Manual) "Datetime and Duration Parsing" =>

Cedar datetime values are measured in milliseconds since the Unix epoch (`1970-01-01T00:00:00Z`), stored as `Int64`. Duration values are also measured in milliseconds, stored as `Int64`.

# Datetime Grammar

The accepted syntax for datetime literals is:

```
Datetime ::= Date
           | Date 'T' Time 'Z'
           | Date 'T' Time '.' SSS 'Z'
           | Date 'T' Time Offset
           | Date 'T' Time '.' SSS Offset

Date     ::= YYYY '-' MM '-' DD
Time     ::= hh ':' mm ':' ss
SSS      ::= Digit{3}
Offset   ::= ('+' | '-') hh mm
YYYY     ::= Digit{4}
MM       ::= Digit{2}
DD       ::= Digit{2}
hh       ::= Digit{2}
mm       ::= Digit{2}
ss       ::= Digit{2}
Digit    ::= '0' | '1' | … | '9'

Constraints:
  - 01 ≤ MM ≤ 12
  - 01 ≤ DD ≤ daysInMonth(YYYY, MM)
  - 00 ≤ hh ≤ 23
  - 00 ≤ mm ≤ 59
  - 00 ≤ ss ≤ 59

daysInMonth(y, m) =
  30  if m ∈ {4, 6, 9, 11}
  28  if m = 2 ∧ ¬isLeapYear(y)
  29  if m = 2 ∧ isLeapYear(y)
  31  otherwise

isLeapYear(y) =
  (4 | y) ∧ (¬(100 | y) ∨ (400 | y))
```

A datetime string is _valid_ if and only if it satisfies the grammar and constraints above. Internally, a datetime is stored as milliseconds since the Unix epoch in an `Int64`. Since the grammar restricts years to at most 4 digits and offsets to at most ±23:59, the representable range is a strict subset of `Int64` — no valid string can overflow. This is a provable property:


# Duration Grammar

The accepted syntax for duration literals is:

```
Duration   ::= ['-'] Components
Components ::= [Days] [Hours] [Minutes] [Seconds] [Millis]

Days       ::= Digit⁺ 'd'
Hours      ::= Digit⁺ 'h'
Minutes    ::= Digit⁺ 'm'
Seconds    ::= Digit⁺ 's'
Millis     ::= Digit⁺ 'ms'
Digit      ::= '0' | '1' | … | '9'

Constraints:
  - At least one component must be present
  - Components must appear in order (largest to smallest)
  - value(Duration) ∈ [Int64.min, Int64.max]

value(Duration) in milliseconds =
  sign × (d × 86400000 + h × 3600000 + m × 60000
          + s × 1000 + ms)
  where sign    = -1 if '-' is present, else 1
        d, h, m, s, ms = nat value of each component
                         (0 if omitted)
```

A duration string is _valid_ if and only if it satisfies the grammar and constraints above.
