import VersoManual
import Cedar.Thm.Ext.Decimal

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Cedar.Thm.Decimal

set_option verso.code.warnLineLength 80

-- Source project for `module`/`anchor` code blocks: the sibling `cedar-lean`
-- package, relative to this doc's Lake workspace. These blocks render the real
-- imported definitions (true namespaces and bodies) straight from source.
set_option verso.exampleProject ".."

#doc (Manual) "Decimal Parsing" =>

Cedar decimals use a fixed-point representation over `Int64`, with a scale factor of 10⁴ (4 digits after the decimal point). For example, the value `1.2345` is stored as the integer `12345`.

# Grammar

The accepted syntax for decimal literals is:

```
Decimal  ::= Integer '.' Fraction
Integer  ::= ['-'] Digit⁺
Fraction ::= Digit{1,4}
Digit    ::= '0' | '1' | … | '9'

value(Decimal) =
  int(Integer) × 10⁴ + sign × nat(Fraction) × 10^(4 - |Fraction|)
  where sign   = -1 if Integer starts with '-', else 1
        int(s) = integer value of s (e.g., int("-12") = -12)
        nat(s) = natural number value of s (e.g., nat("03") = 3)
        |s|    = length of s

Constraint: value(Decimal) ∈ [Int64.min, Int64.max]
```

A string is _valid_ if and only if it satisfies both the grammar and the constraint above.

# Parser

```lean -show
-- Bring the spec's `Decimal` type and `Decimal.parse`/`toString` into scope for
-- the executable `#eval` examples below. The definitions themselves are shown
-- from source via `anchor` blocks, so nothing is redeclared here.
open Cedar.Spec.Ext Cedar.Spec.Ext.Decimal
```

`Decimal.parse` returns `some d` when the input string is valid, and `none` otherwise (shown here directly from its source in `Cedar.Spec.Ext.Decimal`):

```anchor parse (module := Cedar.Spec.Ext.Decimal)
public def parse (str : String) : Option Decimal :=
  match str.splitToList (· = '.') with
  | ["-", _] => .none -- guard against bare "-"; redundant on current stdlib (`String.toInt? "-" = none`) but robust to stdlib changes
  | [left, right] =>
    let rlen := right.length
    if 0 < rlen ∧ rlen ≤ DECIMAL_DIGITS
    then
      match toInt?' left, toNat?' right with
      | .some l, .some r =>
        let l' := l * (Int.pow 10 DECIMAL_DIGITS)
        let r' := r * (Int.pow 10 (DECIMAL_DIGITS - rlen))
        let i  := if !left.startsWith "-" then l' + r' else l' - r'
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

We formalize the validity of input string by the predicate `IsWfDecimal` (well-formed syntax of the grammar) and the function `computeValue` (value function).

`IsWfDecimal` is a direct transcription of the grammar's character-level productions. The building block is `IsDigits`, which captures `Digit⁺` — a non-empty string all of whose characters satisfy `Char.isDigit`. It lives at the root namespace in `Cedar.Thm.Data.String`, shared with the duration grammar:

```anchor IsDigits (module := Cedar.Thm.Data.String)
public def IsDigits (s : String) : Prop :=
  0 < s.length ∧ ∀ c ∈ s.toList, c.isDigit = true
```

The integer part follows the grammar's `Integer ::= ['-'] Digit⁺` — either a bare digit string, or a `'-'` followed by one. Because the second branch still demands `IsDigits t`, a bare `"-"` is rejected structurally, without a separate side condition:

```anchor IsWfInt (module := Cedar.Thm.Ext.Decimal.Grammar)
public def IsWfInt (s : String) : Prop :=
  IsDigits s ∨ ∃ t, s = "-" ++ t ∧ IsDigits t
```

The fraction part follows `Fraction ::= Digit{1,4}` — `IsDigits` supplies the lower bound (at least one digit) and the length constraint supplies the upper bound:

```anchor IsWfFrac (module := Cedar.Thm.Ext.Decimal.Grammar)
public def IsWfFrac (s : String) : Prop :=
  IsDigits s ∧ s.length ≤ DECIMAL_DIGITS
```

Well-formedness of the whole string then reads straight off the grammar — split on `.`, an `Integer` on the left and a `Fraction` on the right:

```anchor IsWfDecimal (module := Cedar.Thm.Ext.Decimal.Grammar)
public def IsWfDecimal (s : String) : Prop :=
 ∃ left right,
    s.splitToList (· = '.') = [left, right] ∧
    IsWfInt left ∧
    IsWfFrac right
```

Note that this definition talks only about digit characters — it does not mention the string-to-number parsers `toInt?'`/`toNat?'`. That keeps the specification faithful to the grammar and independent of any parsing implementation. The `computeValue` function below and `Decimal.parse` do use those parsers to extract the numeric value; a family of _bridge lemmas_ (e.g. `toInt?'_isSome_of_isWfInt` and its converse `isWfInt_of_toInt?'_isSome`) connect the two views, proving that a digit string is exactly one the parser accepts.

```anchor computeValue (module := Cedar.Thm.Ext.Decimal.Grammar)
public def computeValue (s : String) : Option Int :=
  match s.splitToList (· = '.') with
  | [left, right] =>
    match toInt?' left, toNat?' right with
      | .some l, .some r =>
        let sign : Int := if left.startsWith "-" then -1 else 1
        some (l * Int.pow 10 DECIMAL_DIGITS
          + sign * r * Int.pow 10 (DECIMAL_DIGITS - right.length))
      | _, _ => none
  | _ => none
```

This is a literal transcription of the grammar's value function: `int(Integer) × 10⁴` for the integer part, plus `sign × nat(Fraction) × 10^(4 − |Fraction|)` for the fraction, where `sign = −1` when the integer starts with `'-'`. It returns `none` when the string does not split into an integer part and a fraction that the primitives accept.

# Soundness and Completeness

The parser is characterized by two complementary guarantees stated in terms of the previous formal definitions.

_Soundness_ says that whenever parsing succeeds, the input was genuinely valid: it is well-formed and `computeValue` yields exactly the returned decimal's value. (The range constraint is implicit — `d.toInt` is always in `Int64` range, since `d` is an `Int64`.)

{docstring parse_sound}

_Completeness_ is the converse: every well-formed string whose computed value is `some d.toInt` is accepted as that decimal. (Again the range constraint is implicit — `d.toInt` is always in range.)

{docstring parse_complete}

Together they also give a complete characterization of parsing failure — the parser rejects exactly those strings that are malformed or whose computed value overflows the `Int64` range:

{docstring parse_eq_none_iff}

# Canonical String Representation

`toString` converts a decimal back to its canonical string form, always producing exactly 4 fractional digits:

```anchor ToString (module := Cedar.Spec.Ext.Decimal)
public instance : ToString Decimal where
  toString (d : Decimal) : String :=
    let neg   := if d < 0 then "-" else ""
    let d     := d.natAbs
    let left  := d / (Nat.pow 10 4)
    let right := d % (Nat.pow 10 4)
    let right :=
      -- this is not generalized for arbitrary DECIMAL_DIGITS
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

Parsing the canonical string representation of any decimal recovers the original value.

{docstring parse_toString_roundtrip}

It is a direct corollary of completeness: canonical strings are just a special case of well-formed inputs, so we only need to check that `toString d` _is_ well-formed and that its computed value is `d.toInt`, then hand both to `parse_complete`.

{docstring toString_isWfDecimal}

{docstring computeValue_toString}

Though only a corollary, roundtrip guards against parser bugs on _valid_ inputs — cases soundness and the failure characterization, aimed at rejecting _invalid_ inputs, never exercise. For example, every decimal in `(-1, 0)` serializes to a `-0.xxxx` string (value `-5000` becomes `"-0.5000"`), so roundtrip must parse these back exactly. An earlier parser derived the sign from the integer part's value, where `int("-0") = 0` dropped the negative and turned `-0.5000` into `+0.5000`. The existence of such a bug would have violated the roundtrip property; in other words, the proof we now have rules it out.
