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
import FormatSpec.Denote
import FormatSpec.Value

/-!
# `decode` — the executable capture extractor, and `computeValue`

`IsWf` (from `Denote`) *recognizes* a string existentially. `computeValue` needs the
*witnessing* capture assignment: which substring each nonterminal matched. `decode`
computes that assignment — the executable inverse of the grammar denotation.

`decode` is a small backtracking recognizer-with-captures over the flat grammar: it
tries every way to split the string across a sequence's items, records each matched
nonterminal's substring, and keeps assignments that consume the whole string. It is the
*reference* decoder (simple, obviously-correct-by-inspection), NOT a production parser.

Status: `partial` and executable (drives `#eval`/demos and, later, differential testing
against the hand-written parser). Its roundtrip lemma vs `IsWf` — `decode (asString env)
= some env` on well-formed inputs — is the next proof milestone; not yet proved.
-/

namespace FormatSpec

/-- A capture assignment: nonterminal name ↦ matched substring. -/
abbrev CaptureMap := List (String × String)

/-- View a `CaptureMap` as the `Env` the value/constraint DSLs evaluate against. -/
def CaptureMap.toEnv (m : CaptureMap) : Env := fun k => (m.find? (·.1 == k)).map (·.2)

/-- Does a char run of length `k` satisfy the terminal `tok`/`ls` at the front of `cs`? -/
private def termPrefixOk (tok : TokClass) (ls : LenSpec) (cs : List Char) (k : Nat) : Bool :=
  ls.sat k && k ≤ cs.length && (cs.take k).all (fun c => decide (tok.mem c))

mutual

/-- All ways symbol `sym` matches a prefix of `cs`: each result is (captures, remaining).
    `fuel` bounds ref-recursion (= #productions, the DAG depth), mirroring `Denote`; this
    makes the function TOTAL and kernel-reducible (so `decide`, not `native_decide`). -/
def matchSym (g : Grammar) : Nat → Sym → List Char → List (CaptureMap × List Char)
  | _,      .lit l,        cs =>
      let ls := l.toList
      if ls.isPrefixOf cs then [([], cs.drop ls.length)] else []
  | _,      .term tok ls,  cs =>
      -- try every valid prefix length (backtracking over the token run)
      (List.range (cs.length + 1)).filterMap (fun k =>
        if termPrefixOk tok ls cs k then some ([], cs.drop k) else none)
  | 0,      .ref _,        _  => []        -- out of fuel (cannot happen in a DAG)
  | fuel+1, .ref name,     cs =>
      match g.prod? name with
      | none   => []
      | some p =>
          (matchProd g fuel p cs).map (fun (m, rem) =>
            let consumed := String.ofList (cs.take (cs.length - rem.length))
            ((name, consumed) :: m, rem))

/-- All ways a sequence matches a prefix of `cs`. -/
def matchSeq (g : Grammar) : Nat → Seq → List Char → List (CaptureMap × List Char)
  | _,    [],           cs => [([], cs)]
  | fuel, item :: rest, cs =>
      let present := (matchSym g fuel item.sym cs).flatMap (fun (m1, r1) =>
        (matchSeq g fuel rest r1).map (fun (m2, r2) => (m1 ++ m2, r2)))
      if item.optional then present ++ matchSeq g fuel rest cs else present

/-- All ways a production matches a prefix of `cs` (union over alternatives). -/
def matchProd (g : Grammar) (fuel : Nat) (p : Production) (cs : List Char) :
    List (CaptureMap × List Char) :=
  p.alts.flatMap (fun alt => matchSeq g fuel alt cs)

end

/-- Decode a string into a capture assignment: a full-consumption match of the start
    production. Fuel = #productions (DAG-depth backstop). Returns the first such
    assignment, or `none` if the string is not well-formed. -/
def decode (g : Grammar) (s : String) : Option CaptureMap :=
  match g.startProd? with
  | none   => none
  | some p =>
      let full := (matchProd g g.prods.length p s.toList).filter (fun (_, rem) => rem.isEmpty)
      full.head?.map (·.1)

/-- The value function: decode the string, then evaluate the value expression against
    the resulting capture environment. `none` when the string is not well-formed. -/
def computeValue (g : Grammar) (ve : ValExpr) (s : String) : Option Int :=
  (decode g s).map (fun m => ve.eval m.toEnv)

end FormatSpec
