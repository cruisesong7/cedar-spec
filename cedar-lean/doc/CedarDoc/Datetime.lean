import VersoManual
import Cedar.Thm.Ext.Datetime.Grammar

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Cedar.Spec.Ext
open Cedar.Thm.Datetime

set_option verso.code.warnLineLength 80

-- Source project for `anchor` code blocks: the sibling `cedar-lean` package.
set_option verso.exampleProject ".."

#doc (Manual) "Datetime Parsing" =>

Cedar datetime values are measured in milliseconds since the Unix epoch (`1970-01-01T00:00:00Z`), stored as `Int64`.

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

A datetime string is _valid_ if and only if it satisfies the grammar and constraints above. Internally, a datetime is stored as milliseconds since the Unix epoch in an `Int64`. Since the grammar restricts years to at most 4 digits and offsets to at most ±23:59, the representable range is a strict subset of `Int64` — no valid string can overflow. This is a provable property.

Duration literals — the signed unit-tagged offsets used with datetimes — have their own grammar and correctness proofs, covered in the _Duration Parsing_ chapter.

# Formal Specification

We formalize the validity of an input string by the predicate `IsWfDatetime` (well-formed syntax of the grammar). Unlike the decimal grammar, which splits a string into fixed positional fields, the datetime grammar describes a date optionally followed by a time, a fractional-seconds field, and a zone designator, so the specification is phrased over an explicit record of those components (as in the duration grammar).

The building block for numeric fields is `IsFixedDigits`, the fixed-width `Digit{n}` refinement of the shared `Digit⁺` predicate `IsDigits`:

```anchor IsFixedDigits (module := Cedar.Thm.Ext.Datetime.Grammar)
public def IsFixedDigits (n : Nat) (s : String) : Prop :=
  IsDigits s ∧ s.length = n
```

Each nonterminal of the grammar becomes a record of its digit fields, with a `syntaxWf` predicate pinning field widths and a `constraintsWf` predicate imposing the numeric bounds. For the `Date ::= YYYY '-' MM '-' DD` production:

```anchor DateComponents (module := Cedar.Thm.Ext.Datetime.Grammar)
public structure DateComponents where
  year : String
  month : String
  day : String
```

```anchor DateComponents.syntaxWf (module := Cedar.Thm.Ext.Datetime.Grammar)
public def DateComponents.syntaxWf (d : DateComponents) : Prop :=
  IsFixedDigits 4 d.year ∧
  IsFixedDigits 2 d.month ∧
  IsFixedDigits 2 d.day
```

```anchor DateComponents.constraintsWf (module := Cedar.Thm.Ext.Datetime.Grammar)
public def DateComponents.constraintsWf (d : DateComponents) : Prop :=
  let mm := fieldValue d.month
  1 ≤ mm ∧ mm ≤ 12 ∧
  1 ≤ fieldValue d.day ∧ fieldValue d.day ≤ daysInMonth (fieldValue d.year) mm
```

The month/day bounds refer to `daysInMonth` and `isLeapYear`, the two auxiliary grammar functions:

```anchor daysInMonth (module := Cedar.Thm.Ext.Datetime.Grammar)
public def daysInMonth (y m : Nat) : Nat :=
  if m == 4 || m == 6 || m == 9 || m == 11 then 30
  else if m == 2 then (if isLeapYear y then 29 else 28)
  else 31
```

```anchor isLeapYear (module := Cedar.Thm.Ext.Datetime.Grammar)
public def isLeapYear (y : Nat) : Bool :=
  y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
```

The `Time`, `Offset`, and `Zone` nonterminals are modelled the same way; the time-bearing tail (`Time ['.' SSS] Zone`) is a `TimePart` combining a `TimeComponents`, an optional millisecond field, and a `Zone`:

```anchor TimePart (module := Cedar.Thm.Ext.Datetime.Grammar)
public structure TimePart where
  time : TimeComponents
  millis : Option String
  zone : Zone
```

A datetime is then a `Date` optionally followed by such a tail, and well-formedness reads straight off the grammar — the string is the rendering of some record that is both syntactically well-formed and satisfies the numeric constraints. Phrasing this existentially over `asString` bakes in the separators, the field order, and the choice among the five top-level forms:

```anchor DatetimeComponents (module := Cedar.Thm.Ext.Datetime.Grammar)
public structure DatetimeComponents where
  date : DateComponents
  time : Option TimePart
```

```anchor IsWfDatetime (module := Cedar.Thm.Ext.Datetime.Grammar)
public def IsWfDatetime (str : String) : Prop :=
  ∃ components : DatetimeComponents,
    components.syntaxWf ∧
    components.constraintsWf ∧
    str = components.asString
```

The parser `Datetime.parse` delegates to `Std.Time.GenericFormat.parse`. Its soundness and completeness against `IsWfDatetime` — that parsing succeeds exactly on well-formed strings, computing the correct millisecond value — are stated as theorems in `Cedar.Thm.Ext.Datetime`; their machine-checked proofs are in progress and are omitted here until complete.
