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

import FormatSpec.Syntax
import FormatSpec.Decode
import FormatSpec.Decidable

/-!
# IPv6 example — `hexDigit`, and the fixed-arity BOUNDARY of the tool

Transcribes the IPv6 fragment of `doc/CedarDoc/IPAddr.lean`. The full grammar is
```
V6Addr ::= H16 (':' H16){7}                        -- 8 groups, no '::'
         | [H16 (':' H16)*] '::' [H16 (':' H16)*]  -- one '::', sides total < 8
H16    ::= HexDigit{1,4}     -- value ≤ 0xffff (automatic from ≤ 4 hex digits)
```

This example exercises the `hexDigit` terminal (unused by the others); the `H16 ≤ 0xffff`
bound is automatic from `hexDigit{1,4}` (≤ 4 hex digits), so the grammar alone captures it.

TWO honest truncations vs the full grammar:

1. **The `::` (gap) form is OMITTED** — a VARIABLE-ARITY production (a variable *number* of
   `:`-separated `H16` groups on each side of `::`). The grammar DSL is fixed-arity by design
   (its only repetition is a leaf token run — `hexDigit{1,4}` — never a repeated *group*), so
   `::` is out of scope by construction. This is exactly the case the design (§5–§6) flags for
   a hand-written `decode`: the tool cannot synthesize it and would prompt the author for the
   decoder, rather than mis-specifying it.

2. **The group count is 4, not the real 8.** The auto-emitted `IsWf_equiv` reconciliation proof
   uses a uniform `simp`-normalization closer that does not yet scale past ~5 flat group-refs
   in one sequence (the nested-existential normalization blows up in `whnf`). At 8 groups it
   exceeds any reasonable heartbeat budget. So this example uses a 4-group `V6Addr` — fully
   representative of the `hexDigit`/fixed-arity behavior — and this limit is a KNOWN, recorded
   scaling boundary of the current closer (not a soundness issue; the proof that DOES emit is
   axiom-clean). Scaling the closer to 8+ groups is a separate improvement.

Writes `spec.lean` beside this file.
-/

namespace FormatSpec.Examples.IPv6
open FormatSpec

format_spec IPv6 where
  grammar
    V6Addr ::= H16 ":" H16 ":" H16 ":" H16
    H16    ::= hexDigit{1,4}
  to "FormatSpec/Examples/IPv6"

#check (IPv6.IsWf.V6Addr : String → Prop)

#eval decide (IPv6.IsWf.V6Addr "1:2:3:4")        -- true
#eval decide (IPv6.IsWf.V6Addr "2001:db8:0:1")   -- true (case-insensitive hex)
#eval decide (IPv6.IsWf.V6Addr "1:2:3")          -- false (3 groups — grammar)
#eval decide (IPv6.IsWf.V6Addr "1:2:3:12345")    -- false (5 hex digits > 4)
#eval decide (IPv6.IsWf.V6Addr "1::4")           -- false (`::` out of scope)

#check (IPv6.IsWf_equiv : ∀ s, IsWf IPv6.grammar s ↔ IPv6.IsWf.V6Addr s)
example : DecidablePred IPv6.IsWf.V6Addr := inferInstance

end FormatSpec.Examples.IPv6
