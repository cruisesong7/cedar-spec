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

import FormatSpec.Grammar
import FormatSpec.Classify
import FormatSpec.Denote
import FormatSpec.Value
import FormatSpec.Constraint
import FormatSpec.Decode
import FormatSpec.Decidable
import FormatSpec.Assemble
import FormatSpec.Syntax
import FormatSpec.Examples
import FormatSpec.SyntaxTest
import FormatSpec.ValueTest
import FormatSpec.DenoteTest
import FormatSpec.ConstraintTest
import FormatSpec.DecimalDemo

/-!
# FormatSpec

A (work-in-progress) reusable Lean library for **specifying and verifying flat
non-recursive string-format parsers** — the "verified textual scalar parsing" niche.

Given a grammar for a flat regular attribute-grammar format (dates, decimals,
durations, IP addresses, UUIDs, semver, ...), generate the Lean *specification*
(`IsWf`, `computeValue`) and the parser *contract theorem* surface, auto-discharging
the grammar-generic obligations and delegating the non-affine parts via typed holes.

See `Cedar/Thm/Ext/GRAMMAR_TO_SPEC_DESIGN.md` for the full design.

Module layout:
* `FormatSpec.Grammar`  — core grammar data type (what the DSL elaborates into)
* `FormatSpec.Classify` — decidable syntactic classifier (acyclicity, ref resolution)
* `FormatSpec.Denote`     — grammar denotation → `IsWf` (well-formedness predicate)
* `FormatSpec.Value`      — the value-DSL: deep `ValExpr` AST + `eval` denotation
* `FormatSpec.Constraint` — the constraint-DSL: deep `Constraint` AST, auto-classified
                            into `IsWf` (string) / `SatisfiesConstraints` (value) parts
* `FormatSpec.Decode`     — executable capture extractor `decode` + `computeValue`
* `FormatSpec.Decidable`  — `DecidablePred (IsWf g)` via a total boolean recognizer
                            (one remaining `sorry`: the recognizer↔denotation lemma)
* `FormatSpec.Assemble`   — bundles ingredients into `isWf`/`satisfiesConstraints`/
                            `isAccepted` (the generated command's top-level predicates)
* `FormatSpec.Syntax`     — the `format_spec` embedded DSL (surface → core `Grammar`)
* `FormatSpec.Examples`   — hand-written `Grammar` values (Decimal, IPv4) for validation
* `FormatSpec.DecimalDemo`— end-to-end demo: Decimal grammar → runnable spec
* `FormatSpec.*Test`      — Syntax / Value / Denote / Constraint test fixtures
-/
