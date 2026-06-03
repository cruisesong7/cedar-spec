import VersoManual
import Cedar.Thm.Ext.Decimal

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Decimal Parsing" =>

Cedar decimals use a fixed-point representation over `Int64`, with a scale factor of 10⁴ (4 digits after the decimal point). For example, the value `1.2345` is stored as the integer `12345`.

# Well-Formedness

A string is _well-formed_ for decimal parsing when it splits on `'.'` into exactly
two parts: the left part must be a valid integer string (not bare `"-"`), and the
right part must be a non-empty natural number string of at most 4 characters.

{docstring Cedar.Thm.Decimal.IsWfStr}

# Roundtrip Theorem for Parsing

The most crucial correctness guarantee: parsing the canonical string representation of any
decimal recovers the original decimal.

{docstring Cedar.Thm.Decimal.parse_toString_roundtrip}

This is proved via two intermediate results:

{docstring Cedar.Thm.Decimal.toString_isWfStr}

{docstring Cedar.Thm.Decimal.computeValue_toString}

# Parse Failure Characterization

Parsing fails if and only if the input string is malformed or its value overflows `Int64`:

{docstring Cedar.Thm.Decimal.parse_eq_none_iff}

This gives a _complete_ characterization — there are no "mysterious" failure modes.
