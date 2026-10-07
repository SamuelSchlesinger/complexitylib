/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeRouting

/-!
# Unrestricted depth-three lower bound: tape branch

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeBranch.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3 uDepth4 uDepth5 uDepth6 uDepth7 uDepth8 uDepth9 uDepth10 uDepth11
universe uDepth12 uDepth13 uDepth14 uDepth15 uDepth16 uDepth17 uDepth18 uDepth19 uDepth20

namespace DepthThreeLowerBound
namespace TapeBranch

open TapeMultiProgram

/-- Control states of the branch routine. -/
abbrev State (Q : Type uDepth1) (R : Type uDepth2) := Q ⊕ (R ⊕ Unit)

/-- Embed a test-stage state in the conditional routine. -/
def test {Q : Type uDepth3} {R : Type uDepth4} (q : Q) : State Q R := .inl q
/-- Embed a body-stage state in the conditional routine. -/
def body {Q : Type uDepth5} {R : Type uDepth6} (r : R) : State Q R := .inr (.inl r)
/-- The conditional routine's rejecting terminal state. -/
def rejected {Q : Type uDepth7} {R : Type uDepth8} : State Q R := .inr (.inr ())

/-- Transition function of the branch routine. -/
def program {Q : Type uDepth9} {R : Type uDepth10} (P : TapeMultiProgram Q) (B : TapeMultiProgram R)
    (entry : R) (accept : Q → Bool) : TapeMultiProgram (State Q R)
  | .inl q, h =>
      match P q h with
      | none => jump (if accept q then body entry else rejected) h
      | some (q', writes, moves) => some (test q', writes, moves)
  | .inr (.inl r), h => (B r h).map fun out => (body out.1, out.2)
  | .inr (.inr _), _ => none

@[simp] theorem rejected_halts {Q : Type uDepth11} {R : Type uDepth12} (P : TapeMultiProgram Q)
    (B : TapeMultiProgram R) (entry : R) (accept : Q → Bool) (h : TapeHeads) :
    program P B entry accept rejected h = none := rfl

theorem body_halts {Q : Type uDepth13} {R : Type uDepth14} (P : TapeMultiProgram Q)
    (B : TapeMultiProgram R) (entry : R) (accept : Q → Bool)
    (r : R) (h : TapeHeads) (hr : B r h = none) :
    program P B entry accept (body r) h = none := by
  simp only [program, body, hr, Option.map_none]

theorem runs_test {Q : Type uDepth15} {R : Type uDepth16} (P : TapeMultiProgram Q) (B :
  TapeMultiProgram R)
    (entry : R) (accept : Q → Bool) {q q' : Q} {T U : TapeTapes} {m : ℕ}
    (h : RunsIn P.step (cfg q T) (cfg q' U) m) :
    RunsIn (program P B entry accept).step (cfg (test q) T) (cfg (test q') U) m :=
  runs_map P _ test (by
    intro a heads a' writes moves he
    simp only [program, test, he]) h

theorem runs_reject {Q : Type uDepth17} {R : Type uDepth18} (P : TapeMultiProgram Q) (B :
  TapeMultiProgram R)
    (entry : R) (accept : Q → Bool) {q q' : Q} {T U : TapeTapes} {m : ℕ}
    (h : RunsIn P.step (cfg q T) (cfg q' U) m)
    (hhalt : P q' (heads U) = none) (hno : accept q' = false) :
    RunsIn (program P B entry accept).step (cfg (test q) T) (cfg rejected U) (m + 1) := by
  have ht := runs_test P B entry accept h
  have he := RunsIn.single (step_jump (program P B entry accept) (test q') rejected U
    (by simp [program, test, hhalt, hno]))
  exact ht.trans he

theorem runs_accept {Q : Type uDepth19} {R : Type uDepth20} (P : TapeMultiProgram Q) (B :
  TapeMultiProgram R)
    (entry : R) (accept : Q → Bool) {q q' : Q} {r : R} {T U V : TapeTapes} {m n : ℕ}
    (hP : RunsIn P.step (cfg q T) (cfg q' U) m)
    (hhalt : P q' (heads U) = none) (hyes : accept q' = true)
    (hB : RunsIn B.step (cfg entry U) (cfg r V) n) :
    RunsIn (program P B entry accept).step (cfg (test q) T) (cfg (body r) V)
      (m + 1 + n) := by
  have ht := runs_test P B entry accept hP
  have he := RunsIn.single (step_jump (program P B entry accept) (test q') (body entry) U
    (by simp [program, test, hhalt, hyes]))
  have hb := runs_map B (program P B entry accept) body (by
    intro a heads a' writes moves hcode
    simp only [program, body, hcode, Option.map_some]) hB
  exact (ht.trans he).trans hb

end TapeBranch
end DepthThreeLowerBound

end Complexity
