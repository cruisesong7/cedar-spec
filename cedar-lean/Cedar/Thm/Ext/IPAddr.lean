module

public import Cedar.Thm.Ext.IPAddr.Lemmas

import all Cedar.Spec.Ext.Util
import all Cedar.Spec.Ext.IPAddr
import all Cedar.Thm.Ext.IPAddr.Grammar
import all Cedar.Thm.Ext.IPAddr.Lemmas

namespace Cedar.Thm.IPAddr
open Cedar.Spec.Ext
open IPAddr

/-! # IPAddr parser correctness

`parse_sound`, `parse_complete`, and `parse_eq_none_iff` characterize exactly when
`Cedar.Spec.Ext.IPAddr.ip` (a.k.a. `ip`) succeeds, in terms of the grammar-level `IsWfIPNet`
predicate and the `v4Value`/`v6Value` value functions (both in `Cedar.Thm.Ext.IPAddr.Grammar`). The
parser-independent bridge lemmas they build on live in `Cedar.Thm.Ext.IPAddr.Lemmas`.

Unlike decimal/duration, the value of an IP-net is not a single `Int` but an `IPNet`, so soundness
is phrased as "the returned net equals the components' value". Unlike datetime, the parser is
hand-written (no `Std.Time` delegation), so the bridges are direct string-manipulation reasoning.

`IsWfIPNet` is `IsWfV4 ∨ IsWfV6`. On the value side there is no separate `computeValue : Option`
(as in decimal): a well-formed string determines its `IPNet` via `v4Value`/`v6Value`, so soundness
and completeness are stated per witnessing components. -/

/-! ## Soundness -/

/-- Soundness of `IPAddr.ip`: if parsing succeeds, the input is a well-formed IP-net string, and
    the returned net is the value of its witnessing components. -/
public theorem parse_sound (str : String) (net : IPNet) (h : IPAddr.ip str = some net) :
    IsWfIPNet str ∧
    ((∃ v pre, net = v4Value v pre) ∨ (∃ v pre, net = v6Value v pre)) := by
  sorry -- TODO: case on parse's V4-first `if`; parseIPv4Net_isSome_wf / parseIPv6Net_isSome_wf

/-! ## Completeness -/

/-- Completeness for the V4 form: a well-formed V4 string parses to its `v4Value`. -/
public theorem parse_complete_v4 {v : V4Components} {pre : Option String}
    (hsyn : v.syntaxWf) (hcon : v.constraintsWf)
    (hpre : IsWfOptionalPrefix 2 (ADDR_SIZE V4_WIDTH) pre) :
    IPAddr.ip (v.asString ++ (match pre with | none => "" | some p => "/" ++ p))
      = some (v4Value v pre) := by
  sorry -- TODO: parseIPv4Net_eq_some makes the V4-first branch fire

/-- Completeness for the V6 form: a well-formed V6 string parses to its `v6Value`. -/
public theorem parse_complete_v6 {v : V6Components} {pre : Option String}
    (hsyn : v.syntaxWf)
    (hpre : IsWfOptionalPrefix 3 (ADDR_SIZE V6_WIDTH) pre) :
    IPAddr.ip (v.asString ++ (match pre with | none => "" | some p => "/" ++ p))
      = some (v6Value v pre) := by
  sorry -- TODO: parseIPv4Net_none_of_isWfV6 forces fall-through, then parseIPv6Net_eq_some

/-- Completeness of `IPAddr.ip`: every well-formed IP-net string is accepted (with the value of
    its witnessing components). -/
public theorem parse_complete (str : String) (h : IsWfIPNet str) :
    (IPAddr.ip str).isSome := by
  sorry -- TODO: case on IsWfV4/IsWfV6; parse_complete_v4 / parse_complete_v6

/-! ## Failure characterization -/

/-- Failure characterization: `IPAddr.ip` rejects exactly the strings that are not well-formed
    IP-nets. (There is no overflow condition — the grammar's field bounds already exclude
    out-of-range values.) -/
public theorem parse_eq_none_iff (str : String) :
    IPAddr.ip str = none ↔ ¬ IsWfIPNet str := by
  sorry -- TODO: contrapositive of parse_sound / parse_complete (pure Option reasoning)

/-! ## Roundtrip -/

/-- Parsing the canonical string representation of any `IPNet` recovers it: `parse` and `toString`
    are mutually inverse on parseable nets. This is the headline user-facing property. (Kept
    non-`public` since the spec's `ToString IPNet` instance is not `public`; it is an internal
    corollary of completeness.) -/
theorem parse_toString_roundtrip (net net' : IPNet) (h : IPAddr.ip (toString net) = some net') :
    net' = net := by
  sorry -- TODO: toString produces a canonical well-formed string; parse_complete recovers net

end Cedar.Thm.IPAddr
