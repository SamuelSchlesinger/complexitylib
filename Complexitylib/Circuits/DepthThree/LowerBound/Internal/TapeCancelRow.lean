/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeCancelStep
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageBitReductionLoop

/-!
# Unrestricted depth-three lower bound: tape cancel row

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeCancelRow.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeCancelRow

open TapeMultiProgram TapeRouting TapeUnary TapeArithmetic TapeRegister

/-- Control states of the cancel row routine. -/
abbrev State := LoopState DecState TapeCancelStep.State

/-- Transition function of the cancel row routine. -/
def program (v : Bool) : TapeMultiProgram State :=
  loopCode (decProgram loop1) (TapeCancelStep.program v)
    DecState.start TapeCancelStep.start decPositive

/-- Initial control state of the cancel row routine. -/
def start : State := loopTest DecState.start
/-- Terminal control state of the cancel row routine. -/
def done : State := loopDone

/-- Tape-store invariant recording the loop counters and current output. -/
def frame (σ : TapeStore) (n j shift : ℕ) (out : List Bool) : TapeStore :=
  fun r => if r = loop1 then List.replicate n true
    else if r = indexA then List.replicate j true
    else if r = indexC then List.replicate (shift + j) true
    else if r = productBits then out else σ r

@[simp] theorem frame_counter (σ : TapeStore) (n j s : ℕ) (out : List Bool) :
    frame σ n j s out loop1 = List.replicate n true := by simp [frame]
@[simp] theorem frame_indexA (σ : TapeStore) (n j s : ℕ) (out : List Bool) :
    frame σ n j s out indexA = List.replicate j true := by simp [frame, loop1, indexA]
@[simp] theorem frame_indexC (σ : TapeStore) (n j s : ℕ) (out : List Bool) :
    frame σ n j s out indexC = List.replicate (s + j) true := by
  simp [frame, loop1, indexA, indexC]
@[simp] theorem frame_output (σ : TapeStore) (n j s : ℕ) (out : List Bool) :
    frame σ n j s out productBits = out := by
  simp [frame, loop1, indexA, indexC, productBits]

theorem update_counter (σ : TapeStore) (n n' j s : ℕ) (out : List Bool) :
    Function.update (frame σ n j s out) loop1 (List.replicate n' true) =
      frame σ n' j s out := by
  funext r
  by_cases hr : r = loop1
  · subst r
    simp
  · simp [frame, Function.update, hr]

theorem resultStore_frame (σ : TapeStore) (n j s : ℕ) (out out' : List Bool) :
    TapeCancelStep.resultStore (frame σ n j s out) j (s + j) out' =
      frame σ n (j + 1) s out' := by
  funext r
  by_cases hc : r = indexC
  · subst r
    simp [TapeCancelStep.resultStore, Nat.add_assoc]
  · by_cases ha : r = indexA
    · subst r
      simp [TapeCancelStep.resultStore, indexA, indexC]
    · by_cases hp : r = productBits
      · subst r
        simp [TapeCancelStep.resultStore, indexA, indexC, productBits]
      · simp [TapeCancelStep.resultStore, Function.update, frame, hc, ha, hp]

theorem runs_row (v : Bool) (σ : TapeStore) (p c : List Bool) (s j n : ℕ)
    (hP : σ polyBits = p) (hj : j + n ≤ p.length) (hsize : s + p.length ≤ c.length) :
    RunsIn (program v).step
      (cfg start (storeTapes (frame σ n j s (modulusUpdateLoop p v s j c))))
      (cfg done (storeTapes (frame σ 0 (j + n) s (modulusUpdateLoop p v s (j + n) c))))
      (n * (2 * s + 4 * p.length + 21) + 3) := by
  induction n generalizing j with
  | zero =>
      have hd := decrement_empty loop1
        (storeTapes (frame σ 0 j s (modulusUpdateLoop p v s j c))) (by simp [])
      have he := loop_exit (decProgram loop1) (TapeCancelStep.program v)
        DecState.start TapeCancelStep.start decPositive hd rfl rfl
      simpa only [program, start, done, Nat.add_zero, Nat.zero_mul, Nat.zero_add] using he
  | succ n ih =>
      let out := modulusUpdateLoop p v s j c
      let out' := modulusUpdateLoop p v s (j + 1) c
      have hd := decrement_cons loop1 (storeTapes (frame σ (n + 1) j s out))
        (List.replicate n true) true (by simp [List.replicate_succ])
      have hd' : RunsIn (decProgram loop1).step
          (cfg DecState.start (storeTapes (frame σ (n + 1) j s out)))
          (cfg (DecState.done true) (storeTapes (frame σ n j s out))) 4 := by
        simpa only [← storeTapes_update, update_counter] using hd
      have hPf : frame σ n j s out polyBits = p := by
        simp [frame, hP, polyBits, loop1, indexA, indexC, productBits]
      have ht := TapeCancelStep.runs_step v (frame σ n j s out) j (s + j)
        (by simp) (by simp) (by rw [hPf]; omega)
        (by simp only [frame_output, out, modulusUpdateLoop_length]; omega)
      have ht' : RunsIn (TapeCancelStep.program v).step
          (cfg TapeCancelStep.start (storeTapes (frame σ n j s out)))
          (cfg TapeCancelStep.done (storeTapes (frame σ n (j + 1) s out')))
          (2 * j + 2 * (s + j) + 15) := by
        simpa only [frame_output, hPf, resultStore_frame, out', modulusUpdateLoop_step, out] using
          ht
      have hit := loop_iter (decProgram loop1) (TapeCancelStep.program v)
        DecState.start TapeCancelStep.start decPositive hd' rfl rfl ht' rfl
      have hit' := hit.mono (show 4 + 1 + (2 * j + 2 * (s + j) + 15) + 1 ≤
          2 * s + 4 * p.length + 21 by omega)
      have hrest := ih (j + 1) (by omega)
      have hall := hit'.trans hrest
      have htime : (2 * s + 4 * p.length + 21) +
          (n * (2 * s + 4 * p.length + 21) + 3) =
          (n + 1) * (2 * s + 4 * p.length + 21) + 3 := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have hindex : j + 1 + n = j + (n + 1) := by omega
      simpa only [program, start, done, htime, hindex, out, out'] using hall

@[simp] theorem program_done (v : Bool) (h : TapeHeads) : program v done h = none := rfl

end TapeCancelRow
end DepthThreeLowerBound

end Complexity
