/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Lean

/-!
# The value-DSL: a deep-embedded value expression language

The `value` section of `format_spec` is written in a small, readable, math-style
formula language transcribing the doc's `value(X) = …` notation. Crucially this is a
**deep embedding**: the DSL elaborates into an inspectable `ValExpr` AST, NOT directly
into an opaque Lean term.

Why deep (design note §16.4, and the CoStar++ contrast): CoStar++ consumes the value
function as a black box (`f vs`), which is why its value is stuck at *definitional*.
Owning the AST lets us (a) *translate* it to a Lean computation via the `eval`
denotation, and later (b) *analyze* it for affinity to auto-generate roundtrip /
soundness proofs. `eval e` IS the value function (a total Lean function), so the
"translation into Lean" is just the denotation.

Scope of this first increment: scalar `Int`-valued formulas (covers decimal, duration).
Deferred: structured / non-`Int` output (IPAddr's `IPNet`), non-recursive `where`
helpers (datetime's `isLeapYear`/`daysInMonth`), and the affinity analysis pass.
-/

namespace FormatSpec

/-- Deep-embedded value-expression AST. Field references (`nat`/`int`/`len`/`sign`)
    read a named capture from the environment; the rest is closed-form arithmetic. -/
inductive ValExpr where
  /-- Integer literal. -/
  | lit    (n : Int)
  /-- `nat X` — unsigned decimal value of capture `X` (0 if absent). -/
  | nat    (field : String)
  /-- `int X` — signed decimal value of capture `X` (leading `-` ⟹ negative; 0 if absent). -/
  | int    (field : String)
  /-- `len X` — character length of capture `X` (0 if absent). -/
  | len    (field : String)
  /-- `sign X` — `-1` if capture `X` starts with `-`, else `+1` (used for the doc's
      `sign` helper; `+1` if absent). -/
  | signOf (field : String)
  | add    (a b : ValExpr)
  | sub    (a b : ValExpr)
  | mul    (a b : ValExpr)
  /-- `base ^ exp` — exponent is evaluated then truncated to `Nat` (always ≥ 0 here). -/
  | pow    (base exp : ValExpr)
  | neg    (a : ValExpr)
  deriving Repr, Inhabited, DecidableEq

/-- Reader: unsigned decimal value of a digit string (`"345" ↦ 345`). -/
def readNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

/-- Reader: signed decimal value (leading `-` ⟹ negative; `"-12" ↦ -12`). -/
def readInt (s : String) : Int :=
  if s.startsWith "-" then -(readNat (s.drop 1).toString : Int) else (readNat s : Int)

/-- Evaluation environment: capture name ↦ its matched substring (absent ⟹ `none`).
    In the full pipeline this comes from `decode`; here it is supplied directly. -/
abbrev Env := String → Option String

/-- Denotation of a value expression against a capture environment — this IS the
    translation to a Lean computation. Absent field references read as `0`
    (`nat`/`int`/`len`) or `+1` (`sign`), matching the doc's "0 if omitted". -/
def ValExpr.eval (env : Env) : ValExpr → Int
  | .lit n    => n
  | .nat f    => match env f with | some s => (readNat s : Int) | none => 0
  | .int f    => match env f with | some s => readInt s        | none => 0
  | .len f    => match env f with | some s => (s.length : Int) | none => 0
  | .signOf f => match env f with | some s => if s.startsWith "-" then -1 else 1 | none => 1
  | .add a b  => a.eval env + b.eval env
  | .sub a b  => a.eval env - b.eval env
  | .mul a b  => a.eval env * b.eval env
  | .pow b e  => (b.eval env) ^ (e.eval env).toNat
  | .neg a    => -(a.eval env)

/-! ## Surface syntax: math-style formulas → `ValExpr`

A dedicated syntax category `valExpr` with its own operator precedences
(`^` > `*` > `+`/`-`), so the DSL owns the parse and builds a `ValExpr` term. The
`val%` wrapper turns a formula into a `ValExpr` value. -/

open Lean

declare_syntax_cat valExpr

syntax:max num             : valExpr
syntax:max "nat " ident    : valExpr
syntax:max "int " ident    : valExpr
syntax:max "len " ident    : valExpr
syntax:max "sign " ident   : valExpr
-- Named integer constants (desugar to `ValExpr.lit`, staying fully analyzable).
syntax:max "Int64.MAX"     : valExpr
syntax:max "Int64.MIN"     : valExpr
-- `value` — inside a `constraints` entry, refers to the elaborated value expression
-- (so constraints read like the doc's `value(X) ∈ [MIN, MAX]`). Only meaningful when a
-- value substitution is supplied (see `elabValExprWith`); bare use elsewhere errors.
syntax:max "value"         : valExpr
syntax:max "(" valExpr ")" : valExpr
syntax:65 valExpr:65 " + " valExpr:66 : valExpr
syntax:65 valExpr:65 " - " valExpr:66 : valExpr
syntax:70 valExpr:70 " * " valExpr:71 : valExpr
syntax:75 valExpr:76 " ^ " valExpr:75 : valExpr

/-- Translate a `valExpr` formula into a `ValExpr` term. `valueSub`, if provided, is the
    term substituted for a `value` reference (the format's value expression); `none`
    makes a `value` reference an error. -/
partial def elabValExprWith (valueSub : Option (TSyntax `term)) :
    TSyntax `valExpr → MacroM (TSyntax `term)
  | `(valExpr| $n:num)      => `(FormatSpec.ValExpr.lit $n)
  | `(valExpr| Int64.MAX)   => `(FormatSpec.ValExpr.lit 9223372036854775807)
  | `(valExpr| Int64.MIN)   => `(FormatSpec.ValExpr.lit (-9223372036854775808))
  | `(valExpr| value)       =>
      match valueSub with
      | some t => pure t
      | none   => Macro.throwUnsupported
  | `(valExpr| nat $i:ident)  => `(FormatSpec.ValExpr.nat $(quote i.getId.toString))
  | `(valExpr| int $i:ident)  => `(FormatSpec.ValExpr.int $(quote i.getId.toString))
  | `(valExpr| len $i:ident)  => `(FormatSpec.ValExpr.len $(quote i.getId.toString))
  | `(valExpr| sign $i:ident) => `(FormatSpec.ValExpr.signOf $(quote i.getId.toString))
  | `(valExpr| ( $e:valExpr )) => elabValExprWith valueSub e
  | `(valExpr| $a:valExpr + $b:valExpr) => do `(FormatSpec.ValExpr.add $(← elabValExprWith valueSub a) $(← elabValExprWith valueSub b))
  | `(valExpr| $a:valExpr - $b:valExpr) => do `(FormatSpec.ValExpr.sub $(← elabValExprWith valueSub a) $(← elabValExprWith valueSub b))
  | `(valExpr| $a:valExpr * $b:valExpr) => do `(FormatSpec.ValExpr.mul $(← elabValExprWith valueSub a) $(← elabValExprWith valueSub b))
  | `(valExpr| $a:valExpr ^ $b:valExpr) => do `(FormatSpec.ValExpr.pow $(← elabValExprWith valueSub a) $(← elabValExprWith valueSub b))
  | _ => Macro.throwUnsupported

/-- Translate a `valExpr` with no `value` substitution (the common case). -/
partial def elabValExpr (e : TSyntax `valExpr) : MacroM (TSyntax `term) :=
  elabValExprWith none e

/-- `val% <formula>` : a `ValExpr` value from math-style syntax. -/
macro "val% " e:valExpr : term => elabValExpr e

end FormatSpec
