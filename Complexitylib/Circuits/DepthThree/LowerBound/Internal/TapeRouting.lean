/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeMultiRoutines

/-!
# Unrestricted depth-three lower bound: tape routing

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeRouting.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3 uDepth4 uDepth5 uDepth6 uDepth7 uDepth8 uDepth9 uDepth10 uDepth11
universe uDepth12 uDepth13 uDepth14 uDepth15 uDepth16 uDepth17 uDepth18 uDepth19 uDepth20 uDepth21
universe uDepth22 uDepth23 uDepth24 uDepth25 uDepth26

namespace DepthThreeLowerBound
namespace TapeRouting

open TapeMultiProgram

/-- Transition function for the join stage of the routing routine. -/
def joinCode {Q : Type uDepth1} {R : Type uDepth2} (P : TapeMultiProgram Q) (B : TapeMultiProgram R)
    (entry : Q → R) : TapeMultiProgram (Q ⊕ R)
  | .inl q, h =>
      match P q h with
      | none => jump (.inr (entry q)) h
      | some (q', writes, moves) => some (.inl q', writes, moves)
  | .inr r, h => (B r h).map fun out => (.inr out.1, out.2)

theorem join_runs {Q : Type uDepth3} {R : Type uDepth4} (P : TapeMultiProgram Q) (B :
  TapeMultiProgram R)
    (entry : Q → R) {q q' : Q} {r : R} {T U V : TapeTapes} {m n : ℕ}
    (hP : RunsIn P.step (cfg q T) (cfg q' U) m)
    (hhalt : P q' (heads U) = none)
    (hB : RunsIn B.step (cfg (entry q') U) (cfg r V) n) :
    RunsIn (joinCode P B entry).step (cfg (.inl q) T) (cfg (.inr r) V) (m + 1 + n) := by
  have hp := runs_map P (joinCode P B entry) Sum.inl (by
    intro a h a' writes moves he
    simp only [joinCode, he]) hP
  have hlink := RunsIn.single (step_jump (joinCode P B entry)
    (.inl q') (.inr (entry q')) U (by simp only [joinCode, hhalt]))
  have hb := runs_map B (joinCode P B entry) Sum.inr (by
    intro a h a' writes moves he
    simp only [joinCode, he, Option.map_some]) hB
  exact (hp.trans hlink).trans hb

theorem join_done {Q : Type uDepth5} {R : Type uDepth6} (P : TapeMultiProgram Q) (B :
  TapeMultiProgram R)
    (entry : Q → R) (r : R) (h : TapeHeads) (hh : B r h = none) :
    joinCode P B entry (.inr r) h = none := by
  simp only [joinCode, hh, Option.map_none]

/-- Control states for the loop stage of the routing routine. -/
abbrev LoopState (Q : Type uDepth7) (R : Type uDepth8) := (Q ⊕ R) ⊕ Unit

/-- Embed a test-stage state in the loop control. -/
def loopTest {Q : Type uDepth9} {R : Type uDepth10} (q : Q) : LoopState Q R := .inl (.inl q)
/-- Embed a body-stage state in the loop control. -/
def loopBody {Q : Type uDepth11} {R : Type uDepth12} (r : R) : LoopState Q R := .inl (.inr r)
/-- Terminal control state of the loop stage of the routing routine. -/
def loopDone {Q : Type uDepth13} {R : Type uDepth14} : LoopState Q R := .inr ()

/-- Transition function for the loop stage of the routing routine. -/
def loopCode {Q : Type uDepth15} {R : Type uDepth16} (P : TapeMultiProgram Q) (B :
  TapeMultiProgram R)
    (testEntry : Q) (bodyEntry : R) (again : Q → Bool) : TapeMultiProgram (LoopState Q R)
  | .inl (.inl q), h =>
      match P q h with
      | none => jump (if again q then loopBody bodyEntry else loopDone) h
      | some (q', writes, moves) => some (loopTest q', writes, moves)
  | .inl (.inr r), h =>
      match B r h with
      | none => jump (loopTest testEntry) h
      | some (r', writes, moves) => some (loopBody r', writes, moves)
  | .inr _, _ => none

theorem loop_test_runs {Q : Type uDepth17} {R : Type uDepth18} (P : TapeMultiProgram Q) (B :
  TapeMultiProgram R)
    (testEntry : Q) (bodyEntry : R) (again : Q → Bool)
    {q q' : Q} {T U : TapeTapes} {m : ℕ}
    (h : RunsIn P.step (cfg q T) (cfg q' U) m) :
    RunsIn (loopCode P B testEntry bodyEntry again).step
      (cfg (loopTest q) T) (cfg (loopTest q') U) m :=
  runs_map P _ loopTest (by
    intro a h a' writes moves he
    simp only [loopCode, loopTest, he]) h

theorem loop_body_runs {Q : Type uDepth19} {R : Type uDepth20} (P : TapeMultiProgram Q) (B :
  TapeMultiProgram R)
    (testEntry : Q) (bodyEntry : R) (again : Q → Bool)
    {r r' : R} {T U : TapeTapes} {m : ℕ}
    (h : RunsIn B.step (cfg r T) (cfg r' U) m) :
    RunsIn (loopCode P B testEntry bodyEntry again).step
      (cfg (loopBody r) T) (cfg (loopBody r') U) m :=
  runs_map B _ loopBody (by
    intro a h a' writes moves he
    simp only [loopCode, loopBody, he]) h

theorem loop_exit {Q : Type uDepth21} {R : Type uDepth22} (P : TapeMultiProgram Q) (B :
  TapeMultiProgram R)
    (testEntry : Q) (bodyEntry : R) (again : Q → Bool)
    {q : Q} {T U : TapeTapes} {m : ℕ}
    (h : RunsIn P.step (cfg testEntry T) (cfg q U) m)
    (hhalt : P q (heads U) = none) (hstop : again q = false) :
    RunsIn (loopCode P B testEntry bodyEntry again).step
      (cfg (loopTest testEntry) T) (cfg loopDone U) (m + 1) := by
  have ht := loop_test_runs P B testEntry bodyEntry again h
  have he := RunsIn.single (step_jump (loopCode P B testEntry bodyEntry again)
    (loopTest q) loopDone U (by simp [loopCode, loopTest, hhalt, hstop]))
  exact ht.trans he

theorem loop_iter {Q : Type uDepth23} {R : Type uDepth24} (P : TapeMultiProgram Q) (B :
  TapeMultiProgram R)
    (testEntry : Q) (bodyEntry : R) (again : Q → Bool)
    {q : Q} {r : R} {T U V : TapeTapes} {m n : ℕ}
    (hP : RunsIn P.step (cfg testEntry T) (cfg q U) m)
    (hPhalt : P q (heads U) = none) (hgo : again q = true)
    (hB : RunsIn B.step (cfg bodyEntry U) (cfg r V) n)
    (hBhalt : B r (heads V) = none) :
    RunsIn (loopCode P B testEntry bodyEntry again).step
      (cfg (loopTest testEntry) T) (cfg (loopTest testEntry) V) (m + 1 + n + 1) := by
  have hp := loop_test_runs P B testEntry bodyEntry again hP
  have hcall := RunsIn.single (step_jump (loopCode P B testEntry bodyEntry again)
    (loopTest q) (loopBody bodyEntry) U (by simp [loopCode, loopTest, hPhalt, hgo]))
  have hb := loop_body_runs P B testEntry bodyEntry again hB
  have hreturn := RunsIn.single (step_jump (loopCode P B testEntry bodyEntry again)
    (loopBody r) (loopTest testEntry) V (by simp [loopCode, loopBody, hBhalt]))
  exact ((hp.trans hcall).trans hb).trans hreturn

@[simp] theorem loop_done {Q : Type uDepth25} {R : Type uDepth26} (P : TapeMultiProgram Q) (B :
  TapeMultiProgram R)
    (testEntry : Q) (bodyEntry : R) (again : Q → Bool) (h : TapeHeads) :
    loopCode P B testEntry bodyEntry again loopDone h = none := rfl

end TapeRouting
end DepthThreeLowerBound

end Complexity
