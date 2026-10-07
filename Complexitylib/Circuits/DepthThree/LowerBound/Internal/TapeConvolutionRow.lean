/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeConvolutionStep
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeNaturalAccess

/-!
# Unrestricted depth-three lower bound: tape convolution row

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeConvolutionRow.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeConvolutionRow

open TapeMultiProgram TapeRouting TapeUnary TapeArithmetic TapeRegister

/-- Control states of the convolution row routine. -/
abbrev State := LoopState DecState TapeConvolutionStep.State

/-- Transition function of the convolution row routine. -/
def program : TapeMultiProgram State :=
  loopCode (decProgram loop1) TapeConvolutionStep.program
    DecState.start TapeConvolutionStep.start decPositive

/-- Initial control state of the convolution row routine. -/
def start : State := loopTest DecState.start
/-- Terminal control state of the convolution row routine. -/
def done : State := loopDone

/-- Tape-store invariant recording the loop counters and current output. -/
def frame (σ : TapeStore) (remaining column : ℕ) (out : List Bool) : TapeStore :=
  fun r => if r = loop1 then List.replicate remaining true
    else if r = indexB then List.replicate column true
    else if r = productBits then out else σ r

@[simp] theorem frame_counter (σ : TapeStore) (n j : ℕ) (out : List Bool) :
    frame σ n j out loop1 = List.replicate n true := by simp [frame]

@[simp] theorem frame_index (σ : TapeStore) (n j : ℕ) (out : List Bool) :
    frame σ n j out indexB = List.replicate j true := by simp [frame, loop1, indexB]

@[simp] theorem frame_output (σ : TapeStore) (n j : ℕ) (out : List Bool) :
    frame σ n j out productBits = out := by simp [frame, loop1, indexB, productBits]

theorem update_counter (σ : TapeStore) (n n' j : ℕ) (out : List Bool) :
    Function.update (frame σ n j out) loop1 (List.replicate n' true) = frame σ n' j out := by
  funext r
  by_cases hr : r = loop1
  · subst r
    simp
  · simp [frame, Function.update, hr]

theorem resultStore_frame (σ : TapeStore) (n j : ℕ) (out out' : List Bool) :
    TapeConvolutionStep.resultStore (frame σ n j out) j out' = frame σ n (j + 1) out' := by
  funext r
  by_cases hr : r = indexB
  · subst r
    simp [TapeConvolutionStep.resultStore]
  · by_cases hp : r = productBits
    · subst r
      simp [TapeConvolutionStep.resultStore, indexB, productBits]
    · simp [TapeConvolutionStep.resultStore, Function.update, frame, hr, hp]

theorem runs_step (σ : TapeStore) (i j : ℕ)
    (hi : σ indexA = List.replicate i true) (hj : σ indexB = List.replicate j true)
    (hk : σ indexC = []) (hs : σ scratchA = [])
    (ha : i < (σ hashBits).length) (hb : j < (σ accumBits).length)
    (hc : i + j < (σ productBits).length) :
    RunsIn TapeConvolutionStep.program.step
      (cfg TapeConvolutionStep.start (storeTapes σ))
      (cfg TapeConvolutionStep.done (storeTapes
        (TapeConvolutionStep.resultStore σ j
          (xorListAt (σ productBits) (i + j)
            ((σ hashBits).getD i false && (σ accumBits).getD j false)))))
      (8 * i + 16 * j + 37) := by
  have h := TapeConvolutionStep.runs_step σ
    ((σ hashBits).take i) ((σ hashBits).drop (i + 1))
    ((σ accumBits).take j) ((σ accumBits).drop (j + 1))
    ((σ productBits).take (i + j)) ((σ productBits).drop (i + j + 1))
    ((σ hashBits).getD i false) ((σ accumBits).getD j false)
    ((σ productBits).getD (i + j) false)
    (by simpa only [TapeNaturalAccess.take_length _ _ ha] using hi)
    (by simpa only [TapeNaturalAccess.take_length _ _ hb] using hj) hk hs
    (TapeNaturalAccess.split _ _ ha) (TapeNaturalAccess.split _ _ hb)
    (TapeNaturalAccess.split _ _ hc)
    (by simp only [TapeNaturalAccess.take_length _ _ ha,
      TapeNaturalAccess.take_length _ _ hb, TapeNaturalAccess.take_length _ _ hc])
  simpa only [TapeNaturalAccess.take_length _ _ ha, TapeNaturalAccess.take_length _ _ hb,
    TapeNaturalAccess.xorListAt_eq_split _ _ hc] using h

theorem runs_row (σ : TapeStore) (a b : List Bool) (i j n : ℕ) (out : List Bool)
    (hA : σ hashBits = a) (hB : σ accumBits = b)
    (hI : σ indexA = List.replicate i true)
    (hK : σ indexC = []) (hS : σ scratchA = [])
    (hi : i < a.length) (hj : j + n ≤ b.length)
    (hsize : a.length + b.length ≤ out.length) :
    RunsIn program.step (cfg start (storeTapes (frame σ n j out)))
      (cfg done (storeTapes (frame σ 0 (j + n)
        (convolutionUpdateRow a b i (List.range' j n) out))))
      (n * (8 * a.length + 16 * b.length + 43) + 3) := by
  induction n generalizing j out with
  | zero =>
      have hd := decrement_empty loop1 (storeTapes (frame σ 0 j out)) (by
        simp [])
      have he := loop_exit (decProgram loop1) TapeConvolutionStep.program
        DecState.start TapeConvolutionStep.start decPositive hd rfl rfl
      simpa only [program, start, done, List.range'_zero, convolutionUpdateRow_nil,
        Nat.add_zero, Nat.zero_mul, Nat.zero_add] using he
  | succ n ih =>
      have hj' : j < b.length := by omega
      have hij : i + j < out.length := by omega
      let out' := xorListAt out (i + j) (a.getD i false && b.getD j false)
      have hd := decrement_cons loop1 (storeTapes (frame σ (n + 1) j out))
        (List.replicate n true) true (by simp [List.replicate_succ])
      have hd' : RunsIn (decProgram loop1).step
          (cfg DecState.start (storeTapes (frame σ (n + 1) j out)))
          (cfg (DecState.done true) (storeTapes (frame σ n j out))) 4 := by
        simpa only [← storeTapes_update, update_counter] using hd
      have hAf : frame σ n j out hashBits = a := by
        simp [frame, hA, hashBits, loop1, indexB, productBits]
      have hBf : frame σ n j out accumBits = b := by
        simp [frame, hB, accumBits, loop1, indexB, productBits]
      have ht := runs_step (frame σ n j out) i j
        (by simp [frame, hI, indexA, loop1, indexB, productBits])
        (by simp) (by simp [frame, hK, indexC, loop1, indexB, productBits])
        (by simp [frame, hS, scratchA, loop1, indexB, productBits])
        (by simpa [frame, hA, hashBits, loop1, indexB, productBits] using hi)
        (by simpa [frame, hB, accumBits, loop1, indexB, productBits] using hj')
        (by simpa using hij)
      have ht' : RunsIn TapeConvolutionStep.program.step
          (cfg TapeConvolutionStep.start (storeTapes (frame σ n j out)))
          (cfg TapeConvolutionStep.done (storeTapes (frame σ n (j + 1) out')))
          (8 * i + 16 * j + 37) := by
        simpa only [frame_output, hAf, hBf, resultStore_frame, out'] using ht
      have hit := loop_iter (decProgram loop1) TapeConvolutionStep.program
        DecState.start TapeConvolutionStep.start decPositive hd' rfl rfl ht' rfl
      have hit' := hit.mono (show 4 + 1 + (8 * i + 16 * j + 37) + 1 ≤
          8 * a.length + 16 * b.length + 43 by omega)
      have hrest := ih (j + 1) out' (by omega) (by simpa [out'] using hsize)
      have hall := hit'.trans hrest
      have htime : (8 * a.length + 16 * b.length + 43) +
          (n * (8 * a.length + 16 * b.length + 43) + 3) =
          (n + 1) * (8 * a.length + 16 * b.length + 43) + 3 := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have hindex : j + 1 + n = j + (n + 1) := by omega
      simpa only [program, start, done, List.range'_succ, convolutionUpdateRow_step,
        htime, hindex, out'] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeConvolutionRow
end DepthThreeLowerBound

end Complexity
