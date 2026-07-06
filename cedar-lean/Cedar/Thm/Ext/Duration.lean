module

public import Cedar.Data.Int64
public import Cedar.Spec.Ext.Datetime
public import Cedar.Thm.Ext.Duration.Grammar

import all Cedar.Thm.Ext.Duration.Grammar
import all Cedar.Thm.Ext.Duration.Lemmas

/-!
Duration parser theorem surface.

`parse_eq_none_iff` characterizes exactly when parsing rejects a string.
`parse_sound` and `parse_complete` state the parser soundness and completeness
properties against `IsWfDuration` and `computeDurationValue`.
-/

namespace Cedar.Thm.Duration
open Cedar.Spec.Ext
open Datetime

/-- Failure characterization for `Duration.parse`: parsing rejects exactly strings that are
    not well-formed or whose computed value overflows the `Int64` range. -/
public theorem parse_eq_none_iff (str : String) :
    Duration.parse str = none ↔
    ¬ IsWfDuration str ∨
      (computeDurationValue str < Int64.MIN ∨ computeDurationValue str > Int64.MAX) := by
  unfold Duration.parse
  cases hsign : isNegativeDuration str with
  | mk isNegative body =>
    rw [parseDuration?_eq_none_iff]
    have hwf := wf_str_iff_signed_body str
    simp only [hsign] at hwf
    constructor
    · intro h
      rcases h with hbody | hoverflow
      · left
        intro hstr
        exact hbody (hwf.mp hstr)
      · right
        have hvalue := compute_value_eq_signed_body_value str
        simp only [hsign] at hvalue
        rw [show computeDurationValue str = computeSignedDurationBodyValue isNegative body from by
          unfold computeDurationValue; simp [hsign]]
        exact hoverflow
    · intro h
      rcases h with hstr | hoverflow
      · left
        intro hbody
        exact hstr (hwf.mpr hbody)
      · right
        rw [show computeDurationValue str = computeSignedDurationBodyValue isNegative body from by
          unfold computeDurationValue; simp [hsign]] at hoverflow
        exact hoverflow

/-- Core completeness of `Duration.parse`: if a string is well-formed, then parsing agrees
    with `duration?` applied to the computed millisecond value. -/
public theorem parse_eq_duration?_of_wf (str : String) (hwf : IsWfDuration str) :
    Duration.parse str = duration? (computeDurationValue str) := by
  unfold Duration.parse computeDurationValue
  cases hsign : isNegativeDuration str with
  | mk isNegative body =>
    have hbody : IsWfBody body := by
      have h := (wf_str_iff_signed_body str).mp hwf
      simp [hsign] at h
      exact h
    exact parseDuration?_eq_duration?_of_wf isNegative body hbody

/-- Soundness of `Duration.parse`: if parsing succeeds, then the input is well-formed,
    its computed value does not overflow the `Int64` range, and the returned duration has
    exactly that computed value. -/
public theorem parse_sound (str : String) (d : Duration)
    (h : Duration.parse str = some d) :
    IsWfDuration str ∧
      ¬ (computeDurationValue str < Int64.MIN ∨ computeDurationValue str > Int64.MAX) ∧
      computeDurationValue str = d.val.toInt := by
  have hwf : IsWfDuration str := by
    by_contra hnot
    have hnone : Duration.parse str = none := (parse_eq_none_iff str).mpr (Or.inl hnot)
    rw [h] at hnone
    contradiction
  have hnoOverflow :
      ¬ (computeDurationValue str < Int64.MIN ∨ computeDurationValue str > Int64.MAX) := by
    intro hoverflow
    have hnone : Duration.parse str = none := (parse_eq_none_iff str).mpr (Or.inr hoverflow)
    rw [h] at hnone
    contradiction
  have hsome : duration? (computeDurationValue str) = some d := by
    rw [← parse_eq_duration?_of_wf str hwf]
    exact h
  exact ⟨hwf, hnoOverflow, (duration?_some_toInt (computeDurationValue str) d hsome).symm⟩

/-- Completeness of `Duration.parse`: if a string is well-formed and its computed value
    does not overflow the `Int64` range, then parsing accepts the string as a duration
    with exactly that computed value. -/
public theorem parse_complete (str : String)
    (hwf : IsWfDuration str)
    (hnoOverflow :
      ¬ (computeDurationValue str < Int64.MIN ∨ computeDurationValue str > Int64.MAX)) :
    ∃ d, Duration.parse str = some d ∧ computeDurationValue str = d.val.toInt := by
  cases hparse : Duration.parse str with
  | none =>
    have hfail := (parse_eq_none_iff str).mp hparse
    rcases hfail with hnot_wf | hoverflow
    · exact False.elim (hnot_wf hwf)
    · exact False.elim (hnoOverflow hoverflow)
  | some d =>
    exact ⟨d, rfl, (parse_sound str d hparse).2.2⟩

/-- Parsing a negated duration string negates the underlying value. -/
public theorem parse_neg (s : String) (d : Duration)
    (hpos : ¬ s.startsWith "-")
    (h : Duration.parse s = some d) :
    Duration.parse ("-" ++ s) = duration? (-d.val.toInt) := by
  have hfront : s.front ≠ '-' := by
    intro hf
    have hs : s = "-" ++ (s.drop 1).copy :=
      string_eq_dash_append_drop_one_of_front_eq_dash s hf
    have hstarts : s.startsWith "-" = true := by
      rw [hs]
      simp
    exact hpos hstarts
  have hs_pos : isNegativeDuration s = (false, s) := by
    unfold isNegativeDuration
    split
    · contradiction
    · rfl
  have hs_neg : isNegativeDuration ("-" ++ s) = (true, s) := by
    unfold isNegativeDuration
    rw [dash_append_front_eq_dash]
    simp [dash_append_drop_one_copy]
  unfold Duration.parse at h ⊢
  simp [hs_pos] at h
  simp [hs_neg]
  have hwf : IsWfBody s := wf_of_parseDuration?_eq_some false s d h
  rw [parseDuration?_eq_duration?_of_wf true s hwf]
  rw [parseDuration?_eq_duration?_of_wf false s hwf] at h
  unfold computeSignedDurationBodyValue at h ⊢
  simp at h ⊢
  have hvalue : d.val.toInt = computeDurationBodyValue s :=
    duration?_some_toInt (computeDurationBodyValue s) d h
  rw [← hvalue]

/-- `offset` and `durationSince` are inverses: adding a duration then computing
    the difference gives back the same duration. -/
public theorem offset_durationSince_inverse (dt : Datetime) (dur : Duration) (dt' : Datetime)
    (h : offset dt dur = some dt') :
    durationSince dt' dt = some dur := by
  unfold offset at h
  unfold durationSince
  cases h_add : Int64.add? dt.val dur.val with
  | none =>
    simp [h_add] at h
  | some i =>
    simp [h_add] at h
    subst h
    rw [Int64.sub?_add?_inverse dt.val dur.val i h_add]
    rfl

/-- `parse ∘ toString` roundtrip: parsing the string representation recovers the original. -/
public theorem parse_toString_roundtrip (d : Duration) :
    Duration.parse (Duration.toString d) = some d := by
  let totalMs := d.val.toInt.natAbs
  let days := totalMs / MILLISECONDS_PER_DAY.toNat
  let rem₁ := totalMs % MILLISECONDS_PER_DAY.toNat
  let hours := rem₁ / MILLISECONDS_PER_HOUR.toNat
  let rem₂ := rem₁ % MILLISECONDS_PER_HOUR.toNat
  let minutes := rem₂ / MILLISECONDS_PER_MINUTE.toNat
  let rem₃ := rem₂ % MILLISECONDS_PER_MINUTE.toNat
  let seconds := rem₃ / MILLISECONDS_PER_SECOND.toNat
  let ms := rem₃ % MILLISECONDS_PER_SECOND.toNat
  let body := canonicalDurationBody days hours minutes seconds ms
  have hbody_wf : IsWfBody body := canonicalDurationBody_wf days hours minutes seconds ms
  have hbody_value :
      computeDurationBodyValue body =
        (days : Int) * MILLISECONDS_PER_DAY +
        (hours : Int) * MILLISECONDS_PER_HOUR +
        (minutes : Int) * MILLISECONDS_PER_MINUTE +
        (seconds : Int) * MILLISECONDS_PER_SECOND +
        (ms : Int) := by
    exact canonicalDurationBody_value days hours minutes seconds ms
  have hparts :
      (days : Int) * MILLISECONDS_PER_DAY +
        (hours : Int) * MILLISECONDS_PER_HOUR +
        (minutes : Int) * MILLISECONDS_PER_MINUTE +
        (seconds : Int) * MILLISECONDS_PER_SECOND +
        (ms : Int) = (totalMs : Int) := by
    dsimp [days, hours, minutes, seconds, ms, rem₁, rem₂, rem₃]
    exact durationParts_value_int totalMs
  have htoString :
      Duration.toString d = if d.val < 0 then "-" ++ body else body := by
    simp [Duration.toString, body, canonicalDurationBody, durationComponent,
      Datetime.durationComponent, days, hours, minutes, seconds, ms, rem₁, rem₂,
      rem₃, totalMs]
  rw [htoString]
  unfold Duration.parse
  by_cases hneg : d.val < 0
  · simp [hneg, isNegativeDuration_neg_body]
    rw [parseDuration?_eq_duration?_of_wf true body hbody_wf]
    unfold computeSignedDurationBodyValue
    rw [hbody_value, hparts]
    have htoInt_neg : -((totalMs : Nat) : Int) = d.val.toInt := by
      have hlt : d.val.toInt < 0 := by simpa [Int64.lt_def_toInt] using hneg
      dsimp [totalMs]
      omega
    simp [htoInt_neg]
    exact duration?_of_val_toInt d
  · have hfront : body.front ≠ '-' := duration_body_front_ne_dash body hbody_wf
    simp [hneg, isNegativeDuration_canonical_body body hfront]
    rw [parseDuration?_eq_duration?_of_wf false body hbody_wf]
    unfold computeSignedDurationBodyValue
    rw [hbody_value, hparts]
    have htoInt_nonneg : ((totalMs : Nat) : Int) = d.val.toInt := by
      have hle : ¬ d.val.toInt < 0 := by
        intro hlt
        exact hneg (by simpa [Int64.lt_def_toInt] using hlt)
      dsimp [totalMs]
      omega
    simp [htoInt_nonneg]
    exact duration?_of_val_toInt d

/-- `toString` is injective: distinct durations produce distinct strings. -/
public theorem toString_injective (d d' : Duration)
    (h : Duration.toString d = Duration.toString d') :
    d = d' := by
  have h1 := parse_toString_roundtrip d
  have h2 := parse_toString_roundtrip d'
  rw [h] at h1
  rw [h1] at h2
  injection h2

/-- Equal normal form iff equal value: normalization decides duration equality. -/
public theorem normalize_eq_iff_parse_eq (s s' : String) :
    normalize s = normalize s' ↔ Duration.parse s = Duration.parse s' := by
  constructor
  · intro h
    unfold normalize at h
    match hps : Duration.parse s, hps' : Duration.parse s' with
    | .some d, .some d' =>
      simp [hps, hps', Option.map] at h
      exact congrArg _ (toString_injective d d' h)
    | .some d, .none => simp [hps, hps', Option.map] at h
    | .none, .some d' => simp [hps, hps', Option.map] at h
    | .none, .none => rfl
  · intro h
    simp [normalize, h]

end Cedar.Thm.Duration
