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

/-- A constraint *entry* in the `constraints` section: either a structured, analyzable
    `Constraint` (the DSL), or the ESCAPE HATCH — an arbitrary decidable predicate on the
    environment with a declared classification (design note §16.7). The escape keeps the
    analyzable `Constraint` AST pure (deriving `Repr`/`DecidableEq`) while never blocking
    a constraint outside the DSL vocabulary. -/
inductive ConstraintEntry where
  /-- A DSL constraint (analyzable). -/
  | dsl (c : Constraint)
  /-- Opaque escape: an arbitrary boolean check on the environment (carrying its own
      decision procedure, so no `DecidablePred` plumbing). `isVal` declares whether it
      folds into `SatisfiesConstraints` (true) or `IsWf` (false), since it cannot be
      inferred from an opaque term. -/
  | opaque (isVal : Bool) (check : Env → Bool)

/-- Value-dependence of an entry (opaque uses its declared `isVal`). -/
def ConstraintEntry.isValueDependent : ConstraintEntry → Bool
  | .dsl c        => c.isValueDependent
  | .opaque b _   => b

/-- `IsWf`-side contribution of an entry. -/
def ConstraintEntry.wfPart (env : Env) : ConstraintEntry → Prop
  | .dsl c              => c.wfPart env
  | .opaque isVal check => if isVal then True else check env = true

/-- `SatisfiesConstraints`-side contribution of an entry. -/
def ConstraintEntry.valPart (env : Env) : ConstraintEntry → Prop
  | .dsl c              => c.valPart env
  | .opaque isVal check => if isVal then check env = true else True

instance (env : Env) : (e : ConstraintEntry) → Decidable (e.wfPart env)
  | .dsl c        => by unfold ConstraintEntry.wfPart; infer_instance
  | .opaque _ _   => by unfold ConstraintEntry.wfPart; split <;> infer_instance

instance (env : Env) : (e : ConstraintEntry) → Decidable (e.valPart env)
  | .dsl c        => by unfold ConstraintEntry.valPart; infer_instance
  | .opaque _ _   => by unfold ConstraintEntry.valPart; split <;> infer_instance

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
-- Closed-interval sugar: `e ∈ [lo, hi]` desugars to `lo ≤ e ∧ e ≤ hi` (no new AST node).
-- Matches the doc's `value ∈ [Int64.MIN, Int64.MAX]`. (Sets/half-open intervals are out
-- of scope — use the `opaque` escape for those.)
syntax valExpr " ∈ " "[" valExpr ", " valExpr "]" : constraintExpr
-- ESCAPE HATCH (design note §16.7): an arbitrary `Env → Bool` check outside the DSL
-- vocabulary. `opaqueWf`   → folds into `IsWf` (string-only classification);
--                `opaqueVal` → folds into `SatisfiesConstraints` (value classification).
syntax "opaqueWf "  term:max : constraintExpr
syntax "opaqueVal " term:max : constraintExpr

/-- Translate a `constraintExpr` into a `Constraint` term (DSL forms only). `valueSub`,
    if provided, is substituted for a `value` reference in the arithmetic sides. -/
def elabConstraintWith (valueSub : Option (TSyntax `term)) :
    TSyntax `constraintExpr → MacroM (TSyntax `term)
  | `(constraintExpr| noLeadingZero $i:ident) =>
      `(Constraint.noLeadingZero $(quote i.getId.toString))
  | `(constraintExpr| $i:ident = $l:str) =>
      `(Constraint.strEq $(quote i.getId.toString) $l)
  | `(constraintExpr| $a:valExpr ≤ $b:valExpr) => do
      `(Constraint.le $(← elabValExprWith valueSub a) $(← elabValExprWith valueSub b))
  | `(constraintExpr| $a:valExpr < $b:valExpr) => do
      `(Constraint.lt $(← elabValExprWith valueSub a) $(← elabValExprWith valueSub b))
  | `(constraintExpr| $a:valExpr == $b:valExpr) => do
      `(Constraint.eq $(← elabValExprWith valueSub a) $(← elabValExprWith valueSub b))
  | `(constraintExpr| $e:valExpr ∈ [ $lo:valExpr , $hi:valExpr ]) => do
      -- desugar to `lo ≤ e ∧ e ≤ hi`
      let et ← elabValExprWith valueSub e
      let lot ← elabValExprWith valueSub lo
      let hit ← elabValExprWith valueSub hi
      `(Constraint.and (Constraint.le $lot $et)
                                  (Constraint.le $et $hit))
  | _ => Macro.throwUnsupported

/-- Translate a `constraintExpr` into a `Constraint` term with no `value` substitution. -/
def elabConstraint (c : TSyntax `constraintExpr) : MacroM (TSyntax `term) :=
  elabConstraintWith none c

/-- Translate a `constraintExpr` into a `ConstraintEntry` term: DSL forms wrap in
    `.dsl`, `opaqueWf`/`opaqueVal` produce the escape-hatch `.opaque` entry. `valueSub`
    threads the value expression for `value` references. -/
def elabEntryWith (valueSub : Option (TSyntax `term)) :
    TSyntax `constraintExpr → MacroM (TSyntax `term)
  | `(constraintExpr| opaqueWf $t:term)  => `(ConstraintEntry.opaque false $t)
  | `(constraintExpr| opaqueVal $t:term) => `(ConstraintEntry.opaque true $t)
  | c => do `(ConstraintEntry.dsl $(← elabConstraintWith valueSub c))

/-- `elabEntry` with no `value` substitution. -/
def elabEntry (c : TSyntax `constraintExpr) : MacroM (TSyntax `term) :=
  elabEntryWith none c

/-- `cstr% <predicate>` : a `Constraint` value from the constraint-DSL. -/
macro "cstr% " c:constraintExpr : term => elabConstraint c

end FormatSpec
