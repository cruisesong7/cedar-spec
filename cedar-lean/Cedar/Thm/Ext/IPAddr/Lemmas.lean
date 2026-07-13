module

public import Cedar.Thm.Ext.IPAddr.Grammar

import all Cedar.Spec.Ext.Util
import all Cedar.Spec.Ext.IPAddr
import all Cedar.Thm.Data.String
import all Cedar.Thm.Ext.IPAddr.Grammar

namespace Cedar.Thm.IPAddr
open Cedar.Spec.Ext
open IPAddr

/-! # IPAddr grammar bridge lemmas

These lemmas connect the parser-independent grammar definitions in
`Cedar.Thm.Ext.IPAddr.Grammar` (`IsWfIPNet`, `computeValue`-style `v4Value`/`v6Value`) to the actual
`Cedar.Spec.Ext.IPAddr.parse`. They culminate in the per-form parse characterizations the aggregator
`parse_sound`/`parse_complete` build on.

The parser structure (from `Cedar.Spec.Ext.IPAddr`) is:
- `parse str = if (parseIPv4Net str).isSome then parseIPv4Net str else parseIPv6Net str`;
- `parseIPv4Net` splits on `'/'`, parses four `parseNumV4` groups (split on `'.'`) and an optional
  `parsePrefixNat` prefix;
- `parseIPv6Net` splits on `'/'`, parses the address via `parseSegsV6` (which handles `::` via
  `splitOn "::"` and pads to eight hextets) and an optional `parsePrefixNat` prefix.

Each numeric primitive (`parseNumV4`, `parseNumV6`, `parsePrefixNat`) enforces the length /
leading-zero / range side conditions that the grammar predicates transcribe. -/

/-! ## Numeric-token bridges -/

/-- `parseNumV4` accepts exactly the canonical ≤ 3-digit groups with value ≤ 255, returning
    `numValue`. -/
theorem parseNumV4_eq_some {s : String} (hwf : IsCanonicalNat s ∧ s.length ≤ 3)
    (hcon : numValue s ≤ 255) :
    parseNumV4 s = some (BitVec.ofNat 8 (numValue s)) :=
  sorry -- TODO: unfold parseNumV4; discharge length/leading-zero guard, toNat?' bridge, range check

/-- Conversely, if `parseNumV4` accepts `s` it is a canonical ≤ 3-digit group with value ≤ 255. -/
theorem parseNumV4_isSome_wf {s : String} (h : (parseNumV4 s).isSome) :
    (IsCanonicalNat s ∧ s.length ≤ 3) ∧ numValue s ≤ 255 :=
  sorry -- TODO: invert parseNumV4's guard

/-- `parseNumV6` accepts exactly the 1–4 digit hex groups, returning `hexValue`. -/
theorem parseNumV6_eq_some {s : String} (hwf : IsHexGroup s) :
    parseNumV6 s = some (BitVec.ofNat 16 (hexValue s)) :=
  sorry -- TODO: unfold parseNumV6; the ≤ 4 hex digits give value ≤ 0xffff automatically

/-- Conversely, if `parseNumV6` accepts `s` it is a well-formed hex group. -/
theorem parseNumV6_isSome_wf {s : String} (h : (parseNumV6 s).isSome) : IsHexGroup s :=
  sorry -- TODO: invert parseNumV6's guard

/-- `parsePrefixNat` accepts exactly the canonical ≤ `digits`-digit numbers with value ≤ `size`. -/
theorem parsePrefixNat_eq_some {s : String} {digits size : Nat}
    (hwf : IsCanonicalNat s ∧ s.length ≤ digits ∧ numValue s ≤ size) :
    (parsePrefixNat s digits size).isSome :=
  sorry -- TODO: unfold parsePrefixNat; discharge the guard

/-! ## IPv4 form -/

/-- `parseSegsV4` inverts `V4Components.asString` on well-formed, in-range V4 groups. -/
theorem parseSegsV4_asString {v : V4Components} (hsyn : v.syntaxWf) (hcon : v.constraintsWf) :
    parseSegsV4 v.asString = some v.toAddr :=
  sorry -- TODO: split on '.'; apply parseNumV4_eq_some to each group

/-- `parseIPv4Net` succeeds on a well-formed V4 string, yielding `v4Value`. -/
theorem parseIPv4Net_eq_some {v : V4Components} {pre : Option String}
    (hsyn : v.syntaxWf) (hcon : v.constraintsWf)
    (hpre : IsWfOptionalPrefix 2 (ADDR_SIZE V4_WIDTH) pre) :
    parseIPv4Net (v.asString ++ (match pre with | none => "" | some p => "/" ++ p))
      = some (v4Value v pre) :=
  sorry -- TODO: split on '/'; parseSegsV4_asString + parsePrefixNat_eq_some

/-- Soundness for V4: a successful `parseIPv4Net` means the string is a well-formed V4 rendering
    whose value is the returned net. -/
theorem parseIPv4Net_isSome_wf {str : String} {net : IPNet} (h : parseIPv4Net str = some net) :
    IsWfV4 str ∧ ∃ v pre, net = v4Value v pre :=
  sorry -- TODO: invert parseIPv4Net through parseSegsV4/parseNumV4/parsePrefixNat

/-! ## IPv6 form -/

/-- `parseSegsV6` inverts a `V6Renders` rendering on well-formed hextets. -/
theorem parseSegsV6_renders {v : V6Components} {addr : String}
    (hsyn : v.syntaxWf) (hren : V6Renders v addr) :
    parseSegsV6 addr = some v.toAddr :=
  sorry -- TODO: characterize splitOn "::" / splitToList ':' on a valid rendering; pad to 8

/-- `parseIPv6Net` succeeds on a well-formed V6 string, yielding `v6Value`. -/
theorem parseIPv6Net_eq_some {v : V6Components} {addr : String} {pre : Option String}
    (hsyn : v.syntaxWf) (hren : V6Renders v addr)
    (hpre : IsWfOptionalPrefix 3 (ADDR_SIZE V6_WIDTH) pre) :
    parseIPv6Net (addr ++ (match pre with | none => "" | some p => "/" ++ p))
      = some (v6Value v pre) :=
  sorry -- TODO: split on '/'; parseSegsV6_renders + parsePrefixNat_eq_some

/-- Soundness for V6: a successful `parseIPv6Net` means the string is a well-formed V6 rendering. -/
theorem parseIPv6Net_isSome_wf {str : String} {net : IPNet} (h : parseIPv6Net str = some net) :
    IsWfV6 str ∧ ∃ v pre, net = v6Value v pre :=
  sorry -- TODO: invert parseIPv6Net through parseSegsV6

/-- The V4 and V6 accepted-string sets are disjoint: no string parses as both. In particular a
    well-formed V6 string is not accepted by `parseIPv4Net` (needed for the `parse`'s V4-first
    fall-through to reach V6). -/
theorem parseIPv4Net_none_of_isWfV6 {str : String} (h : IsWfV6 str) :
    parseIPv4Net str = none :=
  sorry -- TODO: a `::`/hex V6 rendering never matches the four-decimal-group V4 grammar

end Cedar.Thm.IPAddr
