/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeHashStep
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeForLoop
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageBitHashUpdates

/-!
# Unrestricted depth-three lower bound: tape hash inner

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeHashInner.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeHashInner

open TapeMultiProgram TapeUnary TapeRegister

/-- Control states of the hash inner routine. -/
abbrev State := TapeForLoop.State TapeHashStep.State

/-- Transition function of the hash inner routine. -/
def program : TapeMultiProgram State :=
  TapeForLoop.program indexB dataLength TapeHashStep.program TapeHashStep.start

/-- Initial control state of the hash inner routine. -/
def start : State := TapeForLoop.start
/-- Terminal control state of the hash inner routine. -/
def done : State := TapeForLoop.done

/-- Tape-store contents at the progress stage of the hash inner routine. -/
def progressStore (σ : TapeStore) (i j : ℕ) : TapeStore :=
  Function.update (Function.update (Function.update σ hashBits
    (hashUpdateRow (σ keyBits) (σ dataBits) i (List.range j) (σ hashBits)))
    indexA (List.replicate (i + j) true)) indexB (List.replicate j true)

theorem progress_zero (σ : TapeStore) (i : ℕ)
    (ha : σ indexA = List.replicate i true) (hb : σ indexB = []) :
    progressStore σ i 0 = σ := by
  simp only [progressStore, List.range_zero, hashUpdateRow_nil,
    Function.update_eq_self, Nat.add_zero, List.replicate_zero, ← ha, ← hb]

theorem progress_step (σ : TapeStore) (i j : ℕ) :
    TapeHashStep.resultStore (progressStore σ i j) i j =
      Function.update (progressStore σ i (j + 1)) indexB (List.replicate j true) := by
  funext r
  by_cases hb : r = indexB
  · subst r
    simp [TapeHashStep.resultStore, progressStore, indexA, indexB, hashBits]
  · by_cases ha : r = indexA
    · subst r
      simp [TapeHashStep.resultStore, progressStore, indexA, indexB, Nat.add_assoc]
    · by_cases hh : r = hashBits
      · subst r
        simp [TapeHashStep.resultStore, progressStore, hashUpdateRow_range_succ,
          indexA, indexB, hashBits, keyBits, dataBits]
      · simp [TapeHashStep.resultStore, progressStore, hb, ha, hh]

theorem runs_inner (σ : TapeStore) (i d r : ℕ)
    (hi : i < r) (hd : σ dataLength = List.replicate d true)
    (ha : σ indexA = List.replicate i true) (hb : σ indexB = [])
    (hc : σ indexC = List.replicate i true)
    (hkey : (σ keyBits).length = d + r - 1)
    (hdata : (σ dataBits).length = d) (hout : (σ hashBits).length = r) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (progressStore σ i d)))
      (d * (4 * i + 8 * d + 29) + 4 * d + 8) := by
  let τ : ℕ → TapeTapes := fun j => storeTapes (progressStore σ i j)
  have hindex : ∀ j ≤ d, τ j indexB = counterTape j := by
    intro j hj
    simp [τ, progressStore, counterTape]
  have hbound : ∀ j ≤ d, τ j dataLength = counterTape d := by
    intro j hj
    simp [τ, progressStore, counterTape, hd, dataLength, indexA, indexB, hashBits]
  have hbody : ∀ j < d, RunsIn TapeHashStep.program.step
      (cfg TapeHashStep.start (τ j))
      (cfg TapeHashStep.done (Function.update (τ (j + 1)) indexB (counterTape j)))
      (4 * i + 4 * d + 17) := by
    intro j hj
    have hkey' : i + j < (progressStore σ i j keyBits).length := by
      simpa [progressStore, keyBits, indexA, indexB, hashBits, hkey] using
        (hashReadIndex_lt hi hj)
    have hdata' : j < (progressStore σ i j dataBits).length := by
      simpa [progressStore, dataBits, indexA, indexB, hashBits, hdata] using hj
    have hout' : i < (progressStore σ i j hashBits).length := by
      simpa [progressStore, indexA, indexB, hashBits, hout] using hi
    have hs := TapeHashStep.runs_step (progressStore σ i j) i j
      (by simp [progressStore, indexA, indexB])
      (by simp [progressStore])
      (by simp [progressStore, hc, indexA, indexB, indexC, hashBits])
      hkey' hdata' hout'
    have hs' := hs.mono (show 4 * i + 4 * j + 17 ≤ 4 * i + 4 * d + 17 by omega)
    simpa only [τ, progress_step, storeTapes_update, counterTape] using hs'
  have hall := TapeForLoop.runs_zero (by decide : indexB ≠ dataLength)
    TapeHashStep.program TapeHashStep.start TapeHashStep.done τ d (4 * i + 4 * d + 17)
    hindex hbound hbody TapeHashStep.program_done
  have htime : d * (4 * i + 4 * d + 17 + 4 * d + 12) + (4 * d + 8) =
      d * (4 * i + 8 * d + 29) + 4 * d + 8 := by ring
  simpa only [program, start, done, τ, progress_zero σ i ha hb, htime] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeHashInner
end DepthThreeLowerBound

end Complexity
