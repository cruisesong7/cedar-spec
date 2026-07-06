module

public import Cedar.Spec.Ext.Datetime
public import Cedar.Thm.Data.String

import all Cedar.Spec.Ext.Util
import all Cedar.Spec.Ext.Datetime
import all Cedar.Thm.Data.String

namespace Cedar.Thm.Datetime
open Cedar.Spec.Ext

/-! # Datetime grammar: definitions

This file contains only the grammar-level definitions — the well-formedness predicates — as a
direct, parser-independent transcription of the datetime grammar. Unlike the decimal grammar,
which splits a string into fixed positional fields, the datetime grammar describes a date
optionally followed by a time, a fractional-seconds field, and a zone designator, so the
specification is phrased over an explicit record of those components (as in the duration grammar).
The `Digit⁺` predicate `IsDigits` is shared with the decimal and duration grammars and lives in
`Cedar.Thm.Data.String`; here it is refined to the fixed-width `Digit{n}` fields the datetime
grammar uses. -/

/-- The grammar's `Digit{n}`: a digit string of exactly `n` characters. `IsDigits` supplies the
    digit constraint (and non-emptiness), the length equation pins the width. This generalizes the
    decimal grammar's `IsWfFrac`, which bounds the width from above rather than fixing it. -/
-- ANCHOR: IsFixedDigits
public def IsFixedDigits (n : Nat) (s : String) : Prop :=
  IsDigits s ∧ s.length = n
-- ANCHOR_END: IsFixedDigits

/-- Numeric value of a digit field, defaulting to `0` when the string does not parse. On a field
    satisfying `IsFixedDigits` the default is never taken, so this is exactly the field's value. -/
-- ANCHOR: fieldValue
public def fieldValue (s : String) : Nat := (toNat?' s).getD 0
-- ANCHOR_END: fieldValue

/-! ## Numeric constraints

The grammar's `Constraints` block bounds each numeric field. These are pure arithmetic predicates
over the field values; `daysInMonth` and `isLeapYear` transcribe the two auxiliary functions the
day constraint depends on. -/

/-- The grammar's `isLeapYear(y) = (4 | y) ∧ (¬(100 | y) ∨ (400 | y))`, as a decidable `Bool`. -/
-- ANCHOR: isLeapYear
public def isLeapYear (y : Nat) : Bool :=
  y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
-- ANCHOR_END: isLeapYear

/-- The grammar's `daysInMonth(y, m)`: 30 for April/June/September/November, 28 or 29 for
    February depending on the leap year, and 31 otherwise. -/
-- ANCHOR: daysInMonth
public def daysInMonth (y m : Nat) : Nat :=
  if m == 4 || m == 6 || m == 9 || m == 11 then 30
  else if m == 2 then (if isLeapYear y then 29 else 28)
  else 31
-- ANCHOR_END: daysInMonth

/-! ## Components

Each nonterminal of the grammar becomes a record of its fixed-width digit fields. A `syntaxWf`
predicate pins the field widths (`Digit{n}`) and a `constraintsWf` predicate imposes the numeric
bounds from the grammar's `Constraints` block. -/

/-- The grammar's `Date ::= YYYY '-' MM '-' DD`. -/
-- ANCHOR: DateComponents
public structure DateComponents where
  year : String
  month : String
  day : String
-- ANCHOR_END: DateComponents

/-- `YYYY` is `Digit{4}`; `MM` and `DD` are `Digit{2}`. -/
-- ANCHOR: DateComponents.syntaxWf
public def DateComponents.syntaxWf (d : DateComponents) : Prop :=
  IsFixedDigits 4 d.year ∧
  IsFixedDigits 2 d.month ∧
  IsFixedDigits 2 d.day
-- ANCHOR_END: DateComponents.syntaxWf

/-- The month/day bounds: `01 ≤ MM ≤ 12` and `01 ≤ DD ≤ daysInMonth(YYYY, MM)`. -/
-- ANCHOR: DateComponents.constraintsWf
public def DateComponents.constraintsWf (d : DateComponents) : Prop :=
  let mm := fieldValue d.month
  1 ≤ mm ∧ mm ≤ 12 ∧
  1 ≤ fieldValue d.day ∧ fieldValue d.day ≤ daysInMonth (fieldValue d.year) mm
-- ANCHOR_END: DateComponents.constraintsWf

/-- Render a date as `YYYY '-' MM '-' DD`. -/
-- ANCHOR: DateComponents.asString
public def DateComponents.asString (d : DateComponents) : String :=
  d.year ++ "-" ++ d.month ++ "-" ++ d.day
-- ANCHOR_END: DateComponents.asString

/-- The grammar's `Time ::= hh ':' mm ':' ss`. -/
-- ANCHOR: TimeComponents
public structure TimeComponents where
  hours : String
  minutes : String
  seconds : String
-- ANCHOR_END: TimeComponents

/-- `hh`, `mm`, and `ss` are each `Digit{2}`. -/
-- ANCHOR: TimeComponents.syntaxWf
public def TimeComponents.syntaxWf (t : TimeComponents) : Prop :=
  IsFixedDigits 2 t.hours ∧
  IsFixedDigits 2 t.minutes ∧
  IsFixedDigits 2 t.seconds
-- ANCHOR_END: TimeComponents.syntaxWf

/-- The time bounds: `00 ≤ hh ≤ 23`, `00 ≤ mm ≤ 59`, `00 ≤ ss ≤ 59`. -/
-- ANCHOR: TimeComponents.constraintsWf
public def TimeComponents.constraintsWf (t : TimeComponents) : Prop :=
  fieldValue t.hours ≤ 23 ∧
  fieldValue t.minutes ≤ 59 ∧
  fieldValue t.seconds ≤ 59
-- ANCHOR_END: TimeComponents.constraintsWf

/-- Render a time as `hh ':' mm ':' ss`. -/
-- ANCHOR: TimeComponents.asString
public def TimeComponents.asString (t : TimeComponents) : String :=
  t.hours ++ ":" ++ t.minutes ++ ":" ++ t.seconds
-- ANCHOR_END: TimeComponents.asString

/-- The grammar's `Offset ::= ('+' | '-') hh mm`. `negative` records the sign character;
    `hours` and `mm` reuse the `hh`/`mm` nonterminals of `Time`. -/
-- ANCHOR: OffsetComponents
public structure OffsetComponents where
  negative : Bool
  hours : String
  minutes : String
-- ANCHOR_END: OffsetComponents

/-- The offset's `hh` and `mm` are each `Digit{2}`, matching the `Time` nonterminals. -/
-- ANCHOR: OffsetComponents.syntaxWf
public def OffsetComponents.syntaxWf (o : OffsetComponents) : Prop :=
  IsFixedDigits 2 o.hours ∧
  IsFixedDigits 2 o.minutes
-- ANCHOR_END: OffsetComponents.syntaxWf

/-- Because the offset reuses the `hh`/`mm` nonterminals, it inherits their bounds:
    `00 ≤ hh ≤ 23` and `00 ≤ mm ≤ 59`. -/
-- ANCHOR: OffsetComponents.constraintsWf
public def OffsetComponents.constraintsWf (o : OffsetComponents) : Prop :=
  fieldValue o.hours ≤ 23 ∧
  fieldValue o.minutes ≤ 59
-- ANCHOR_END: OffsetComponents.constraintsWf

/-- Render an offset as `('+' | '-') hh mm`. -/
-- ANCHOR: OffsetComponents.asString
public def OffsetComponents.asString (o : OffsetComponents) : String :=
  (if o.negative then "-" else "+") ++ o.hours ++ o.minutes
-- ANCHOR_END: OffsetComponents.asString

/-- The zone designator that terminates a datetime with a time: either the UTC marker `'Z'`
    (`Date 'T' Time 'Z'` / `Date 'T' Time '.' SSS 'Z'`) or an explicit `Offset`. -/
-- ANCHOR: Zone
public inductive Zone where
  | utc
  | offset (o : OffsetComponents)
-- ANCHOR_END: Zone

/-- A UTC marker imposes nothing; an offset must have well-formed digit fields. -/
-- ANCHOR: Zone.syntaxWf
public def Zone.syntaxWf : Zone → Prop
  | .utc => True
  | .offset o => o.syntaxWf
-- ANCHOR_END: Zone.syntaxWf

/-- A UTC marker imposes nothing; an offset must satisfy the `hh`/`mm` bounds. -/
-- ANCHOR: Zone.constraintsWf
public def Zone.constraintsWf : Zone → Prop
  | .utc => True
  | .offset o => o.constraintsWf
-- ANCHOR_END: Zone.constraintsWf

/-- Render the zone: `'Z'` for UTC, otherwise the offset's `('+' | '-') hh mm`. -/
-- ANCHOR: Zone.asString
public def Zone.asString : Zone → String
  | .utc => "Z"
  | .offset o => o.asString
-- ANCHOR_END: Zone.asString

/-- The time-bearing tail of a datetime: a `Time`, an optional fractional-seconds field `SSS`
    (`'.' SSS`), and a `Zone`. Absent `SSS` (`none`) corresponds to the forms without a
    `'.' SSS`; `some` corresponds to the `'.' SSS` forms. -/
-- ANCHOR: TimePart
public structure TimePart where
  time : TimeComponents
  millis : Option String
  zone : Zone
-- ANCHOR_END: TimePart

/-- Lift `IsFixedDigits 3` (the grammar's `SSS ::= Digit{3}`) to the optional field:
    an absent `SSS` is trivially valid. -/
-- ANCHOR: IsWfOptionalMillis
public def IsWfOptionalMillis : Option String → Prop
  | none => True
  | some millis => IsFixedDigits 3 millis
-- ANCHOR_END: IsWfOptionalMillis

/-- The time, the optional `SSS`, and the zone are each well-formed. -/
-- ANCHOR: TimePart.syntaxWf
public def TimePart.syntaxWf (tp : TimePart) : Prop :=
  tp.time.syntaxWf ∧
  IsWfOptionalMillis tp.millis ∧
  tp.zone.syntaxWf
-- ANCHOR_END: TimePart.syntaxWf

/-- The time and zone satisfy their numeric bounds. `SSS` is unconstrained (`000`–`999` are all
    valid), so it contributes no numeric constraint. -/
-- ANCHOR: TimePart.constraintsWf
public def TimePart.constraintsWf (tp : TimePart) : Prop :=
  tp.time.constraintsWf ∧ tp.zone.constraintsWf
-- ANCHOR_END: TimePart.constraintsWf

/-- Render the tail: `'T' Time ['.' SSS] Zone`, so `some sss` inserts `'.' sss`. -/
-- ANCHOR: TimePart.asString
public def TimePart.asString (tp : TimePart) : String :=
  "T" ++ tp.time.asString ++
    (match tp.millis with | none => "" | some sss => "." ++ sss) ++
    tp.zone.asString
-- ANCHOR_END: TimePart.asString

/-- A datetime is a `Date` optionally followed by a time-bearing tail. `none` is the date-only
    form `Date`; `some tp` covers the four `Date 'T' Time …` forms, with the presence of `SSS`
    and the choice of `Zone` selecting among them. -/
-- ANCHOR: DatetimeComponents
public structure DatetimeComponents where
  date : DateComponents
  time : Option TimePart
-- ANCHOR_END: DatetimeComponents

/-- Every present component has well-formed digit fields. -/
-- ANCHOR: DatetimeComponents.syntaxWf
public def DatetimeComponents.syntaxWf (c : DatetimeComponents) : Prop :=
  c.date.syntaxWf ∧ (match c.time with | none => True | some tp => tp.syntaxWf)
-- ANCHOR_END: DatetimeComponents.syntaxWf

/-- Every present component satisfies its numeric bounds. -/
-- ANCHOR: DatetimeComponents.constraintsWf
public def DatetimeComponents.constraintsWf (c : DatetimeComponents) : Prop :=
  c.date.constraintsWf ∧ (match c.time with | none => True | some tp => tp.constraintsWf)
-- ANCHOR_END: DatetimeComponents.constraintsWf

/-- Canonical string representation: the date, followed by the time-bearing tail when present.
    Phrasing well-formedness existentially over `asString` (below) bakes the grammar's structure
    in for free — the separators, the fixed field order, and the choice among the five top-level
    forms all follow from the shape of the witnessing record. -/
-- ANCHOR: DatetimeComponents.asString
public def DatetimeComponents.asString (c : DatetimeComponents) : String :=
  c.date.asString ++ (match c.time with | none => "" | some tp => tp.asString)
-- ANCHOR_END: DatetimeComponents.asString

/-- A datetime string is well-formed exactly when it is the rendering of some `DatetimeComponents`
    that is both syntactically well-formed and satisfies the grammar's numeric constraints. -/
-- ANCHOR: IsWfDatetime
public def IsWfDatetime (str : String) : Prop :=
  ∃ components : DatetimeComponents,
    components.syntaxWf ∧
    components.constraintsWf ∧
    str = components.asString
-- ANCHOR_END: IsWfDatetime

end Cedar.Thm.Datetime
