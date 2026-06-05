import VersoManual
import Cedar.Thm.Ext.Decimal

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Cedar.Thm.Decimal

set_option verso.code.warnLineLength 80

#doc (Manual) "Decimal Parsing" =>

Cedar decimals use a fixed-point representation over `Int64`, with a scale factor of 10⁴ (4 digits after the decimal point). For example, the value `1.2345` is stored as the integer `12345`.

# Grammar

The accepted syntax for decimal literals is:

```
Decimal  ::= Integer '.' Fraction
Integer  ::= ['-'] Digit⁺
Fraction ::= Digit{1,4}
Digit    ::= '0' | '1' | … | '9'

value(Integer '.' Fraction) =
  int(Integer) × 10⁴ + sign × nat(Fraction) × 10^(4 - |Fraction|)
  where sign = -1 if Integer starts with '-', else 1

Constraint: value(Decimal) ∈ [Int64.min, Int64.max]
```

A string is _valid_ if and only if it satisfies both the grammar and the constraint above.

# Parser

`Decimal.parse` returns `some d` when the input string is valid, and `none` otherwise:

```lean -show
open Cedar.Spec.Ext Cedar.Spec.Ext.Decimal
```

```lean
def parse (str : String) : Option Decimal :=
  match str.splitToList (· = '.') with
  | ["-", _] => .none
  | [left, right] =>
    let rlen := right.length
    if 0 < rlen ∧ rlen ≤ DECIMAL_DIGITS then
      match toInt?' left, toNat?' right with
      | .some l, .some r =>
        let l' := l * (Int.pow 10 DECIMAL_DIGITS)
        let r' := r * (Int.pow 10 (DECIMAL_DIGITS - rlen))
        let i := if !left.startsWith "-" then l' + r' else l' - r'
        decimal? i
      | _, _ => .none
    else .none
  | _ => .none
```

For example:

```lean (name := ex1)
#eval Decimal.parse "1.23"        -- valid
```
```leanOutput ex1
some 12300
```

```lean (name := ex2)
#eval Decimal.parse "123"         -- malformed
```
```leanOutput ex2
none
```

```lean (name := ex3)
#eval Decimal.parse "922337203685477.5808" -- overflow
```
```leanOutput ex3
none
```

# Formal Specification

We formalize the validity of input string by the predicate `IsWfStr` (well-formed syntax of the grammar) and the function `computeValue` (value function).

{docstring IsWfStr}

```lean
def IsWfStr (s : String) : Prop :=
  ∃ left right,
    s.splitToList (· = '.') = [left, right] ∧
    left ≠ "-" ∧
    0 < right.length ∧
    right.length ≤ DECIMAL_DIGITS ∧
    (toInt?' left).isSome ∧
    (toNat?' right).isSome
```

{docstring computeValue}

```lean
def computeValue (s : String) : Int :=
  match s.splitToList (· = '.') with
  | [left, right] =>
    let rlen := right.length
    match toInt?' left, toNat?' right with
      | .some l, .some r =>
        let l' := l * (Int.pow 10 DECIMAL_DIGITS)
        let r' := r * (Int.pow 10 (DECIMAL_DIGITS - rlen))
        if !left.startsWith "-" then l' + r' else l' - r'
      | _, _ => 0
  | _ => 0
```

Together they give a complete characterization of parsing failure:

{docstring parse_eq_none_iff}

# Canonical String Representation

`toString` converts a decimal back to its canonical string form, always producing exactly 4 fractional digits:

```lean
instance : ToString Decimal where
  toString (d : Decimal) : String :=
    let neg   := if d < 0 then "-" else ""
    let d     := d.natAbs
    let left  := d / (Nat.pow 10 DECIMAL_DIGITS)
    let right := d % (Nat.pow 10 DECIMAL_DIGITS)
    let right :=
      if right < 10 then s!".000{right}"
      else if right < 100 then s!".00{right}"
      else if right < 1000 then s!".0{right}"
      else s!".{right}"
    s!"{neg}{left}{right}"
```

For example, the canonical string representation of a decimal with internal value `12000` is `1.2000`:

```lean (name := ex4)
#eval toString (⟨12000⟩ : Decimal)
```
```leanOutput ex4
"1.2000"
```

`normalize` composes parsing and serialization — it accepts any valid string and returns its canonical form:

{docstring normalize}

{docstring toString_injective}

{docstring normalize_eq_iff_parse_eq}

# Roundtrip Theorem

The central correctness guarantee: parsing the canonical string representation of any decimal recovers the original value.

{docstring parse_toString_roundtrip}

This is proved via two intermediate results:

{docstring toString_isWfStr}

{docstring computeValue_toString}
