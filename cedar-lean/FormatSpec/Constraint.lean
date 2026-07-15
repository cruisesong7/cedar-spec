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

import FormatSpec.Value

/-!
# The constraint-DSL: deep-embedded predicates, auto-classified

The `constraints` section of `format_spec` lists predicates. Like the value-DSL this is
a **deep embedding**: each constraint elaborates to an inspectable `Constraint` AST, so
the tool can (design note §16.1/§16.3):

* **auto-classify** each constraint by value-dependence:
  - references only capture strings (e.g. `noLeadingZero X`) → folds into `IsWf`;
  - references a value expression (e.g. `nat X ≤ 255`, the `Int64` bound) → folds into
    `SatisfiesConstraints`.
* keep the two layers separate so `IsWf` stays value-free (decidable unconditionally).

This is the "dynamic input validation" layer (CoStar++'s semantic predicates), made
first-class and possibly non-context-free (bounds on computed values, cross-field).

Scope of this increment: the `Constraint` AST + its denotation + the classifier
(`isValueDependent`). Wiring into the `format_spec` command's `constraints` section
(replacing the raw-term capture) is the following step.
-/

namespace FormatSpec

/-- A constraint predicate over the capture environment. Two syntactic flavors:
    *string* predicates (over one capture's matched substring) and *value* predicates
    (comparisons of `ValExpr` value expressions). -/
inductive Constraint where
  /-- `noLeadingZero X` — capture `X` has no leading zero unless it is exactly `"0"`
      (`startsWith "0" → s = "0"`). The pervasive IPAddr canonical-nat rule. STRING. -/
  | noLeadingZero (field : String)
  /-- `X = <lit>` — capture `X`'s matched string equals a literal. STRING. -/
  | strEq (field : String) (lit : String)
  /-- `a ≤ b` — value comparison of two value expressions (e.g. `nat X ≤ 255`). VALUE. -/
  | le (a b : ValExpr)
  /-- `a < b`. VALUE. -/
  | lt (a b : ValExpr)
  /-- `a = b` — value equality. VALUE. -/
  | eq (a b : ValExpr)
  /-- Conjunction. -/
  | and (a b : Constraint)
  deriving Repr, Inhabited, DecidableEq

/-- Whether a constraint depends on a computed *value* (vs. only capture strings).
    Value-dependent ⟹ folds into `SatisfiesConstraints`; otherwise into `IsWf`. -/
def Constraint.isValueDependent : Constraint → Bool
  | .noLeadingZero _ => false
  | .strEq _ _       => false
  | .le _ _          => true
  | .lt _ _          => true
  | .eq _ _          => true
  | .and a b         => a.isValueDependent || b.isValueDependent

/-- Denotation of a constraint against a capture environment. Absent captures: a
    string predicate on an absent capture is vacuously true (the symbol wasn't present,
    so its rule does not apply); value predicates read absent captures as `0` via
    `ValExpr.eval`. -/
def Constraint.eval (env : Env) : Constraint → Prop
  | .noLeadingZero f =>
      match env f with
      | some s => s.startsWith "0" → s = "0"
      | none   => True
  | .strEq f l =>
      match env f with
      | some s => s = l
      | none   => True
  | .le a b => a.eval env ≤ b.eval env
  | .lt a b => a.eval env < b.eval env
  | .eq a b => a.eval env = b.eval env
  | .and a b => a.eval env ∧ b.eval env

instance instDecidableEval (env : Env) : (c : Constraint) → Decidable (c.eval env)
  | .noLeadingZero f => by unfold Constraint.eval; split <;> infer_instance
  | .strEq f l       => by unfold Constraint.eval; split <;> infer_instance
  | .le a b          => by unfold Constraint.eval; infer_instance
  | .lt a b          => by unfold Constraint.eval; infer_instance
  | .eq a b          => by unfold Constraint.eval; infer_instance
  | .and a b         =>
      have := instDecidableEval env a
      have := instDecidableEval env b
      by unfold Constraint.eval; infer_instance

/-- The `IsWf`-side conjunction: only the string (non-value-dependent) constraints. -/
def Constraint.wfPart (env : Env) : Constraint → Prop
  | .and a b => a.wfPart env ∧ b.wfPart env
  | c        => if c.isValueDependent then True else c.eval env

/-- The `SatisfiesConstraints`-side conjunction: only the value-dependent constraints. -/
def Constraint.valPart (env : Env) : Constraint → Prop
  | .and a b => a.valPart env ∧ b.valPart env
  | c        => if c.isValueDependent then c.eval env else True

instance instDecidableWfPart (env : Env) : (c : Constraint) → Decidable (c.wfPart env)
  | .and a b =>
      have := instDecidableWfPart env a
      have := instDecidableWfPart env b
      by unfold Constraint.wfPart; infer_instance
  | .noLeadingZero f => by unfold Constraint.wfPart; split <;> infer_instance
  | .strEq f l       => by unfold Constraint.wfPart; split <;> infer_instance
  | .le a b          => by unfold Constraint.wfPart; split <;> infer_instance
  | .lt a b          => by unfold Constraint.wfPart; split <;> infer_instance
  | .eq a b          => by unfold Constraint.wfPart; split <;> infer_instance

instance instDecidableValPart (env : Env) : (c : Constraint) → Decidable (c.valPart env)
  | .and a b =>
      have := instDecidableValPart env a
      have := instDecidableValPart env b
      by unfold Constraint.valPart; infer_instance
  | .noLeadingZero f => by unfold Constraint.valPart; split <;> infer_instance
  | .strEq f l       => by unfold Constraint.valPart; split <;> infer_instance
  | .le a b          => by unfold Constraint.valPart; split <;> infer_instance
  | .lt a b          => by unfold Constraint.valPart; split <;> infer_instance
  | .eq a b          => by unfold Constraint.valPart; split <;> infer_instance

/-! ## Surface syntax → `Constraint`

A `constraintExpr` category reusing the `valExpr` category (from `FormatSpec.Value`) for
the arithmetic sides of comparisons. -/

open Lean

declare_syntax_cat constraintExpr
syntax "noLeadingZero " ident            : constraintExpr
syntax ident " = " str                   : constraintExpr   -- string equality
syntax valExpr " ≤ " valExpr             : constraintExpr
syntax valExpr " < " valExpr             : constraintExpr
syntax valExpr " == " valExpr            : constraintExpr   -- value equality (`==` to avoid clash)

/-- Translate a `constraintExpr` into a `Constraint` term. -/
def elabConstraint : TSyntax `constraintExpr → MacroM (TSyntax `term)
  | `(constraintExpr| noLeadingZero $i:ident) =>
      `(FormatSpec.Constraint.noLeadingZero $(quote i.getId.toString))
  | `(constraintExpr| $i:ident = $l:str) =>
      `(FormatSpec.Constraint.strEq $(quote i.getId.toString) $l)
  | `(constraintExpr| $a:valExpr ≤ $b:valExpr) => do
      `(FormatSpec.Constraint.le $(← elabValExpr a) $(← elabValExpr b))
  | `(constraintExpr| $a:valExpr < $b:valExpr) => do
      `(FormatSpec.Constraint.lt $(← elabValExpr a) $(← elabValExpr b))
  | `(constraintExpr| $a:valExpr == $b:valExpr) => do
      `(FormatSpec.Constraint.eq $(← elabValExpr a) $(← elabValExpr b))
  | _ => Macro.throwUnsupported

/-- `cstr% <predicate>` : a `Constraint` value from the constraint-DSL. -/
macro "cstr% " c:constraintExpr : term => elabConstraint c

end FormatSpec
