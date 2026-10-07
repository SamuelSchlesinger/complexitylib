/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeArithmetic

/-!
# Unrestricted depth-three lower bound: tape multiply

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeMultiply.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeMultiply

open TapeMultiProgram TapeRouting TapeUnary TapeCopy TapeArithmetic

/-- The four counter tapes used in the multiplication invariant. -/
def tapes (outer source scratch destination : TapeRegister) (T : TapeTapes)
    (n m k z : ℕ) : TapeTapes :=
  onPair outer source (onPair scratch destination T (counterTape k) (counterTape z))
    (counterTape n) (counterTape m)

@[simp] theorem tapes_outer (outer source scratch destination : TapeRegister)
    (T : TapeTapes) (n m k z : ℕ) :
    tapes outer source scratch destination T n m k z outer = counterTape n := by
  simp [tapes]

@[simp] theorem tapes_source {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (T : TapeTapes) (n m k z : ℕ) :
    tapes outer source scratch destination T n m k z source = counterTape m := by
  simp [tapes, hos]

@[simp] theorem tapes_scratch {outer source scratch destination : TapeRegister}
    (hoc : outer ≠ scratch) (hsc : source ≠ scratch) (T : TapeTapes) (n m k z : ℕ) :
    tapes outer source scratch destination T n m k z scratch = counterTape k := by
  simp [tapes, onPair, Ne.symm hoc, Ne.symm hsc]

@[simp] theorem tapes_destination {outer source scratch destination : TapeRegister}
    (hod : outer ≠ destination) (hsd : source ≠ destination) (hcd : scratch ≠ destination)
    (T : TapeTapes) (n m k z : ℕ) :
    tapes outer source scratch destination T n m k z destination = counterTape z := by
  simp [tapes, onPair, Ne.symm hod, Ne.symm hsd, Ne.symm hcd]

theorem tapes_other (outer source scratch destination : TapeRegister)
    (T : TapeTapes) (n m k z : ℕ) (r : TapeRegister)
    (ho : r ≠ outer) (hs : r ≠ source) (hc : r ≠ scratch) (hd : r ≠ destination) :
    tapes outer source scratch destination T n m k z r = T r := by
  simp [tapes, onPair, ho, hs, hc, hd]

private theorem update_outer (outer source scratch destination : TapeRegister)
    (T : TapeTapes) (n m k z n' : ℕ) :
    Function.update (tapes outer source scratch destination T n m k z) outer
      (counterTape n') = tapes outer source scratch destination T n' m k z := by
  exact update_onPair_src outer source
    (onPair scratch destination T (counterTape k) (counterTape z))
    (counterTape n) (counterTape m) (counterTape n')

private theorem overlay_source_scratch {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (hoc : outer ≠ scratch) (hsc : source ≠ scratch)
    (T : TapeTapes) (n m k z m' k' : ℕ) :
    onPair source scratch (tapes outer source scratch destination T n m k z)
      (counterTape m') (counterTape k') =
      tapes outer source scratch destination T n m' k' z := by
  funext r
  by_cases ho : r = outer
  · subst r
    simp [tapes, onPair, hos, hoc]
  · by_cases hs : r = source
    · subst r
      simp [tapes, onPair, Ne.symm hos]
    · by_cases hc : r = scratch
      · subst r
        simp [tapes, onPair, Ne.symm hoc, Ne.symm hsc]
      · simp [tapes, onPair, ho, hs, hc]

private theorem overlay_scratch_destination {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (hoc : outer ≠ scratch) (hod : outer ≠ destination)
    (hsc : source ≠ scratch) (hsd : source ≠ destination)
    (T : TapeTapes) (n m k z k' z' : ℕ) :
    onPair scratch destination (tapes outer source scratch destination T n m k z)
      (counterTape k') (counterTape z') =
      tapes outer source scratch destination T n m k' z' := by
  funext r
  by_cases ho : r = outer
  · subst r
    simp [tapes, onPair, hoc, hod]
  · by_cases hs : r = source
    · subst r
      simp [tapes, onPair, Ne.symm hos, hsc, hsd]
    · by_cases hc : r = scratch
      · subst r
        simp [tapes, onPair, Ne.symm hoc, Ne.symm hsc]
      · by_cases hd : r = destination <;>
          simp [tapes, onPair, ho, hs, hc, hd, Ne.symm hod, Ne.symm hsd]

/-- Control states for the body stage of the multiply routine. -/
abbrev BodyState := TapeCopy.State ⊕ AddState

/-- Transition function for the body stage of the multiply routine. -/
def bodyProgram (source scratch destination : TapeRegister) : TapeMultiProgram BodyState :=
  joinCode (TapeCopy.code source scratch) (addProgram scratch destination)
    (fun _ => addStart)

/-- Initial control state of the body stage of the multiply routine. -/
def bodyStart : BodyState := .inl .start
/-- Terminal control state of the body stage of the multiply routine. -/
def bodyDone : BodyState := .inr addDone

theorem runs_body {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (hoc : outer ≠ scratch) (hod : outer ≠ destination)
    (hsc : source ≠ scratch) (hsd : source ≠ destination) (hcd : scratch ≠ destination)
    (T : TapeTapes) (n m z : ℕ) :
    RunsIn (bodyProgram source scratch destination).step
      (cfg bodyStart (tapes outer source scratch destination T n m 0 z))
      (cfg bodyDone (tapes outer source scratch destination T n m 0 (z + m)))
      (10 * m + 8) := by
  have hcopy := runs_copy hsc (tapes outer source scratch destination T n m 0 z)
    (List.replicate m true)
  simp only [List.length_replicate] at hcopy
  change RunsIn (TapeCopy.code source scratch).step
    (cfg TapeCopy.State.start (onPair source scratch
      (tapes outer source scratch destination T n m 0 z) (counterTape m) (counterTape 0)))
    (cfg TapeCopy.State.done (onPair source scratch
      (tapes outer source scratch destination T n m 0 z) (counterTape m) (counterTape m)))
    (2 * m + 4) at hcopy
  simp only [overlay_source_scratch hos hoc hsc] at hcopy
  have hadd := runs_add hcd (tapes outer source scratch destination T n m m z) m z
  simp only [overlay_scratch_destination hos hoc hod hsc hsd] at hadd
  have h := join_runs (TapeCopy.code source scratch) (addProgram scratch destination)
    (fun _ => addStart) hcopy rfl hadd
  have htime : 2 * m + 4 + 1 + (8 * m + 3) = 10 * m + 8 := by omega
  simpa only [bodyProgram, bodyStart, bodyDone, htime] using h

@[simp] theorem body_done (source scratch destination : TapeRegister) (h : TapeHeads) :
    bodyProgram source scratch destination bodyDone h = none := rfl

/-- Control states of the multiply routine. -/
abbrev State := LoopState DecState BodyState

/-- Transition function of the multiply routine. -/
def program (outer source scratch destination : TapeRegister) : TapeMultiProgram State :=
  loopCode (decProgram outer) (bodyProgram source scratch destination)
    DecState.start bodyStart decPositive

/-- Initial control state of the multiply routine. -/
def start : State := loopTest DecState.start
/-- Terminal control state of the multiply routine. -/
def done : State := loopDone

theorem runs_mul {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (hoc : outer ≠ scratch) (hod : outer ≠ destination)
    (hsc : source ≠ scratch) (hsd : source ≠ destination) (hcd : scratch ≠ destination)
    (T : TapeTapes) (n m z : ℕ) :
    RunsIn (program outer source scratch destination).step
      (cfg start (tapes outer source scratch destination T n m 0 z))
      (cfg done (tapes outer source scratch destination T 0 m 0 (z + n * m)))
      (n * (10 * m + 14) + 3) := by
  induction n generalizing z with
  | zero =>
      have hdec := decrement_empty outer
        (tapes outer source scratch destination T 0 m 0 z) (by simp [counterTape])
      have h := loop_exit (decProgram outer) (bodyProgram source scratch destination)
        DecState.start bodyStart decPositive hdec rfl rfl
      simpa only [program, start, done, Nat.zero_mul, Nat.add_zero, Nat.zero_add] using h
  | succ n ih =>
      have hdec := decrement_cons outer
        (tapes outer source scratch destination T (n + 1) m 0 z)
        (List.replicate n true) true (by simp [counterTape, List.replicate_succ])
      change RunsIn (decProgram outer).step
        (cfg DecState.start (tapes outer source scratch destination T (n + 1) m 0 z))
        (cfg (DecState.done true) (Function.update
          (tapes outer source scratch destination T (n + 1) m 0 z) outer (counterTape n)))
        4 at hdec
      simp only [update_outer] at hdec
      have hbody := runs_body hos hoc hod hsc hsd hcd T n m z
      have hit := loop_iter (decProgram outer) (bodyProgram source scratch destination)
        DecState.start bodyStart decPositive hdec rfl rfl hbody rfl
      have hall := hit.trans (ih (z + m))
      have hacc : z + m + n * m = z + (n + 1) * m := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have htime : 4 + 1 + (10 * m + 8) + 1 + (n * (10 * m + 14) + 3) =
          (n + 1) * (10 * m + 14) + 3 := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [program, start, done, hacc, htime] using hall

@[simp] theorem program_done (outer source scratch destination : TapeRegister) (h : TapeHeads) :
    program outer source scratch destination done h = none := rfl

end TapeMultiply
end DepthThreeLowerBound

end Complexity
