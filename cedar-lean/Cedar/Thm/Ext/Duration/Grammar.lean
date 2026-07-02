module

public import Cedar.Spec.Ext.Datetime
public import Cedar.Thm.Data.String

import all Cedar.Data.Int64
import all Cedar.Spec.Ext.Util
import all Cedar.Spec.Ext.Datetime
import all Cedar.Thm.Data.String
import all Init.Data.String.Search
import Std.Data.String.ToNat

namespace Cedar.Thm.Duration
open Cedar.Spec.Ext
open Datetime

/-- Apply the duration sign to a natural number: negates if `isNegative`, otherwise coerces. -/
public def signedQuantity (isNegative : Bool) (n : Nat) : Int :=
  if isNegative then Int.negOfNat n else Int.ofNat n

/-- Render an optional duration component as its string representation.
    `none` produces `""`, `some digits` produces `digits ++ suffix`. -/
public def durationChunk (digits? : Option String) (suffix : String) : String :=
  match digits? with
  | none => ""
  | some digits => digits ++ suffix

/-- Render a required duration component as `toString n ++ suffix`. -/
public def durationComponent (n : Nat) (suffix : String) : String :=
  toString n ++ suffix

/-- Lift the `Digit⁺` quantity-token predicate (`IsDigits`) to optional components:
    `none` is trivially valid. -/
-- ANCHOR: IsOptionalDurationQuantity
public def IsOptionalDurationQuantity : Option String → Prop
  | none => True
  | some digits => IsDigits digits
-- ANCHOR_END: IsOptionalDurationQuantity

/-- The five optional digit-string components of a duration body, one per time unit.
    Each field holds `none` (unit absent) or `some digits` (unit present with that value). -/
-- ANCHOR: DurationComponents
public structure DurationComponents where
  days : Option String
  hours : Option String
  minutes : Option String
  seconds : Option String
  milliseconds : Option String
-- ANCHOR_END: DurationComponents

/-- At least one component must be present (the body cannot be empty). -/
-- ANCHOR: nonempty
public def DurationComponents.nonempty (components : DurationComponents) : Prop :=
  components.days ≠ none ∨
  components.hours ≠ none ∨
  components.minutes ≠ none ∨
  components.seconds ≠ none ∨
  components.milliseconds ≠ none
-- ANCHOR_END: nonempty

/-- Every present component must be a valid duration quantity (nonempty, parseable digits). -/
-- ANCHOR: quantitiesWf
public def DurationComponents.quantitiesWf
    (components : DurationComponents) : Prop :=
  IsOptionalDurationQuantity components.days ∧
  IsOptionalDurationQuantity components.hours ∧
  IsOptionalDurationQuantity components.minutes ∧
  IsOptionalDurationQuantity components.seconds ∧
  IsOptionalDurationQuantity components.milliseconds
-- ANCHOR_END: quantitiesWf

/-- Canonical string representation: concatenate present components in order `d h m s ms`.
    Absent components contribute `""`. -/
-- ANCHOR: asString
public def DurationComponents.asString (components : DurationComponents) : String :=
  durationChunk components.days "d" ++
  durationChunk components.hours "h" ++
  durationChunk components.minutes "m" ++
  durationChunk components.seconds "s" ++
  durationChunk components.milliseconds "ms"
-- ANCHOR_END: asString

/-- Canonical maximized components for a duration value split into days, hours, minutes,
    seconds, and milliseconds. All five fields are present, including zero-valued fields. -/
public def canonicalDurationComponents (days hours minutes seconds ms : Nat) :
    DurationComponents :=
  { days := some (toString days)
    hours := some (toString hours)
    minutes := some (toString minutes)
    seconds := some (toString seconds)
    milliseconds := some (toString ms) }

/-- Canonical maximized duration body: `days d`, `hours h`, `minutes m`, `seconds s`,
    and `milliseconds ms`, printed largest-to-smallest. -/
public def canonicalDurationBody (days hours minutes seconds ms : Nat) : String :=
  durationComponent days "d" ++ durationComponent hours "h" ++
    durationComponent minutes "m" ++ durationComponent seconds "s" ++
    durationComponent ms "ms"

/-- A duration body string is well-formed iff it equals `components.asString` for some
    `DurationComponents` that is nonempty and has valid quantities. -/
-- ANCHOR: IsWfDurationBody
public def IsWfDurationBody (body : String) : Prop :=
  ∃ components : DurationComponents,
    components.nonempty ∧
    components.quantitiesWf ∧
    body = components.asString
-- ANCHOR_END: IsWfDurationBody

/-- A duration string is well-formed iff it is either a well-formed body directly,
    or `"-"` followed by a well-formed body. -/
-- ANCHOR: IsWfDurationStr
public def IsWfDurationStr (str : String) : Prop :=
  IsWfDurationBody str ∨
  ∃ body, str = "-" ++ body ∧ IsWfDurationBody body
-- ANCHOR_END: IsWfDurationStr

/-- Extract the trailing natural-number token immediately before a duration suffix.
    Returns `(0, s)` as a junk value when the suffix is absent or digits fail to parse. -/
-- ANCHOR: extractTrailingDurationQuantity
public def extractTrailingDurationQuantity (s : String) (suffix : String) : Nat × String :=
  if s.endsWith suffix then
    let rest := (s.dropEnd suffix.length).toString
    let digits := rest.toList.reverse.takeWhile Char.isDigit |>.reverse
    match toNat?' (String.ofList digits) with
    | some n => (n, (rest.dropEnd digits.length).toString)
    | none => (0, s)
  else
    (0, s)
-- ANCHOR_END: extractTrailingDurationQuantity

/-- Compute the unsigned millisecond total of a duration body by extracting each component
    right-to-left (ms, s, m, h, d). Only meaningful on well-formed input. -/
-- ANCHOR: computeDurationBodyValue
public def computeDurationBodyValue (body : String) : Int :=
  let (ms, body) := extractTrailingDurationQuantity body "ms"
  let (sec, body) := extractTrailingDurationQuantity body "s"
  let (min, body) := extractTrailingDurationQuantity body "m"
  let (hr, body) := extractTrailingDurationQuantity body "h"
  let (day, _) := extractTrailingDurationQuantity body "d"
  ↑day * MILLISECONDS_PER_DAY +
  ↑hr * MILLISECONDS_PER_HOUR +
  ↑min * MILLISECONDS_PER_MINUTE +
  ↑sec * MILLISECONDS_PER_SECOND +
  ↑ms
-- ANCHOR_END: computeDurationBodyValue

/-- Compute the signed millisecond value: negates the unsigned total when `isNegative`. -/
-- ANCHOR: computeSignedDurationBodyValue
public def computeSignedDurationBodyValue (isNegative : Bool) (body : String) : Int :=
  let value := computeDurationBodyValue body
  if isNegative then -value else value
-- ANCHOR_END: computeSignedDurationBodyValue

/-- Compute the total signed millisecond value of a full duration string,
    first splitting off the sign via `isNegativeDuration`. -/
-- ANCHOR: computeDurationValue
public def computeDurationValue (str : String) : Int :=
  let (isNegative, body) := isNegativeDuration str
  computeSignedDurationBodyValue isNegative body
-- ANCHOR_END: computeDurationValue

/-- Canonical-form normalizer: parse the string and re-serialize.
    Returns `none` for malformed or out-of-range inputs. -/
public def normalize (str : String) : Option String := (Duration.parse str).map Duration.toString

end Cedar.Thm.Duration
