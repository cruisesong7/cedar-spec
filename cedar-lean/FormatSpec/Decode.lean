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

/-- Does the length-`k` prefix of `cs` satisfy the terminal `tok`/`ls`? Routes through the
    single `matchesTerm` predicate (shared with the recognizer/spec), so the token semantics
    is defined once; the `k ≤ cs.length` guard keeps the prefix a genuine prefix. -/
def termPrefixOk (tok : TokClass) (ls : LenSpec) (cs : List Char) (k : Nat) : Bool :=
  k ≤ cs.length && decide (matchesTerm tok ls (String.ofList (cs.take k)))

mutual

/-- All ways symbol `sym` matches a prefix of `cs`: each result is (captures, remaining).
    `fuel` bounds ref-recursion (= #productions, the DAG depth), mirroring `Denote`; this
    makes the function TOTAL and kernel-reducible (so `decide`, not `native_decide`).

    `qual` is the IMMEDIATE-PARENT production name (`""` at the start production). A matched
    nonterminal `name` is recorded under BOTH its bare key `name` AND — when `qual` is
    nonempty — the qualified key `qual ++ "." ++ name`. So a nonterminal reused in several
    parents (e.g. `hh` in both `Time` and `Offset`) is still reachable *unambiguously* as
    `Time.hh` / `Offset.hh`, while the bare `name` keeps working for uniquely-used captures
    (backward compatible: unique captures resolve by bare name exactly as before). -/
def matchSym (g : Grammar) (qual : String) : Nat → Sym → List Char → List (CaptureMap × List Char)
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
          -- children of `name` are qualified by `name`
          (matchProd g name fuel p cs).map (fun (m, rem) =>
            let consumed := String.ofList (cs.take (cs.length - rem.length))
            let keys := if qual.isEmpty then [(name, consumed)]
                        else [(name, consumed), (qual ++ "." ++ name, consumed)]
            (keys ++ m, rem))

/-- All ways a sequence matches a prefix of `cs`. `qual` = the enclosing production name. -/
def matchSeq (g : Grammar) (qual : String) : Nat → Seq → List Char → List (CaptureMap × List Char)
  | _,    [],           cs => [([], cs)]
  | fuel, item :: rest, cs =>
      let present := (matchSym g qual fuel item.sym cs).flatMap (fun (m1, r1) =>
        (matchSeq g qual fuel rest r1).map (fun (m2, r2) => (m1 ++ m2, r2)))
      if item.optional then present ++ matchSeq g qual fuel rest cs else present

/-- All ways a production matches a prefix of `cs` (union over alternatives). `qual` is the
    production's OWN name, used to qualify the captures its alternatives produce. -/
def matchProd (g : Grammar) (qual : String) (fuel : Nat) (p : Production) (cs : List Char) :
    List (CaptureMap × List Char) :=
  p.alts.flatMap (fun alt => matchSeq g qual fuel alt cs)

end

/-- Decode a string into a capture assignment: a full-consumption match of the start
    production. Fuel = #productions (DAG-depth backstop). Returns the first such
    assignment, or `none` if the string is not well-formed. Start-production children are
    unqualified (`qual := ""`), so top-level captures keep their bare names. -/
def decode (g : Grammar) (s : String) : Option CaptureMap :=
  match g.startProd? with
  | none   => none
  | some p =>
      let full := (matchProd g "" g.prods.length p s.toList).filter (fun (_, rem) => rem.isEmpty)
      full.head?.map (·.1)

/-- The value function: decode the string, then evaluate the value expression against
    the resulting capture environment. `none` when the string is not well-formed. -/
def computeValue (g : Grammar) (ve : ValExpr) (s : String) : Option Int :=
  (decode g s).map (fun m => ve.eval m.toEnv)

end FormatSpec
