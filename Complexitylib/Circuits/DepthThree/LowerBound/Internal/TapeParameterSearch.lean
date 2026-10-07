/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapePowerSearch

/-!
# Unrestricted depth-three lower bound: tape parameter search

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeParameterSearch.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeParameterSearch

open TapeMultiProgram TapeRouting TapeUnary TapePowerSearch

private theorem erase_output (k : ℕ) (R : Registers) (σ : TapeStore) (c : ℕ)
    (ho : σ (R 0) = []) (hd : σ (R 3) = []) :
    RunsIn (TapeErase.code (TapePower.resultRegister k (R 0) (R 3))).step
      (cfg TapeErase.State.start (storeTapes (TapePowerCompare.outputStore k (R 0) (R 3)
        (candidateStore R σ c) c)))
      (cfg TapeErase.State.done (storeTapes (candidateStore R σ c))) (2 * c ^ k + 5) := by
  have h := TapeStoreRuns.erase (TapePower.resultRegister k (R 0) (R 3))
    (TapePowerCompare.outputStore k (R 0) (R 3) (candidateStore R σ c) c)
  have ho' : candidateStore R σ c (R 0) = [] := by
    simpa [candidateStore, R.injective.ne (by decide : (0 : Fin 5) ≠ 1)] using ho
  have hd' : candidateStore R σ c (R 3) = [] := by
    simpa [candidateStore, R.injective.ne (by decide : (3 : Fin 5) ≠ 1)] using hd
  simpa only [TapePowerCompare.outputStore_result, List.length_replicate,
    TapePowerCompare.outputStore_clear k (R 0) (R 3) (candidateStore R σ c) c ho' hd'] using h

private theorem decrement_candidate (R : Registers) (σ : TapeStore) (c : ℕ) :
    RunsIn (decProgram (R 1)).step
      (cfg DecState.start (storeTapes (candidateStore R σ (c + 1))))
      (cfg (DecState.done true) (storeTapes (candidateStore R σ c))) 4 := by
  have h := decrement_cons (R 1) (storeTapes (candidateStore R σ (c + 1)))
    (List.replicate c true) true (by
      simp [storeTapes, candidateStore, List.replicate_succ])
  have he : Function.update (storeTapes (candidateStore R σ (c + 1))) (R 1)
      (wordTape (List.replicate c true)) = storeTapes (candidateStore R σ c) := by
    rw [← storeTapes_update]
    simp [candidateStore]
  simpa only [he] using h

/-- Control states for the cube stage of the parameter search routine. -/
abbrev CubeState := TapePowerSearch.State 3 ⊕ TapeErase.State

/-- Transition function for the cube stage of the parameter search routine. -/
def cubeProgram (R : Registers) : TapeMultiProgram CubeState :=
  joinCode (TapePowerSearch.program 3 false continueLt R)
    (TapeErase.code (TapePower.resultRegister 3 (R 0) (R 3)))
    (fun _ => TapeErase.State.start)

/-- Initial control state of the cube stage of the parameter search routine. -/
def cubeStart : CubeState := .inl (TapePowerSearch.start 3)
/-- Terminal control state of the cube stage of the parameter search routine. -/
def cubeDone : CubeState := .inr .done

/-- Transition budget for the parameter search routine at its cube stage. -/
def cubeCost (d : ℕ) : ℕ :=
  TapePowerSearch.cost 3 false (d ^ 2) (hashDimension d) 0 + 1 +
    (2 * (hashDimension d) ^ 3 + 5)

theorem runs_cube (R : Registers) (σ : TapeStore) (d : ℕ)
    (ho : σ (R 0) = []) (hs : σ (R 2) = []) (hd : σ (R 3) = [])
    (ht : σ (R 4) = List.replicate (d ^ 2) true) :
    RunsIn (cubeProgram R).step
      (cfg cubeStart (storeTapes (candidateStore R σ 0)))
      (cfg cubeDone (storeTapes (candidateStore R σ (hashDimension d))))
      (cubeCost d) := by
  have hc := TapePowerSearch.runs_cube R σ d ho hs hd ht
  have he := erase_output 3 R σ (hashDimension d) ho hd
  exact join_runs _ _ _ hc rfl he

@[simp] theorem cube_done (R : Registers) (h : TapeHeads) :
    cubeProgram R cubeDone h = none := rfl

/-- Control states for the decrease stage of the parameter search routine. -/
abbrev DecreaseState := DecState ⊕ DecState

/-- Transition function for the decrease stage of the parameter search routine. -/
def decreaseProgram (R : Registers) : TapeMultiProgram DecreaseState :=
  joinCode (decProgram (R 1)) (decProgram (R 1)) (fun _ => DecState.start)

/-- Initial control state of the decrease stage of the parameter search routine. -/
def decreaseStart : DecreaseState := .inl .start
/-- Terminal control state of the decrease stage of the parameter search routine. -/
def decreaseDone : DecreaseState := .inr (.done true)

theorem runs_decrease (R : Registers) (σ : TapeStore) (c : ℕ) :
    RunsIn (decreaseProgram R).step
      (cfg decreaseStart (storeTapes (candidateStore R σ (c + 2))))
      (cfg decreaseDone (storeTapes (candidateStore R σ c))) 9 := by
  have h₁ := decrement_candidate R σ (c + 1)
  have h₂ := decrement_candidate R σ c
  have h := join_runs (decProgram (R 1)) (decProgram (R 1))
    (fun _ => DecState.start) h₁ rfl h₂
  have he : c + 1 + 1 = c + 2 := by omega
  simpa only [decreaseProgram, decreaseStart, decreaseDone, he] using h

/-- Control states for the cleanup stage of the parameter search routine. -/
abbrev CleanupState := TapeErase.State ⊕ DecreaseState

/-- Transition function for the cleanup stage of the parameter search routine. -/
def cleanupProgram (R : Registers) : TapeMultiProgram CleanupState :=
  joinCode (TapeErase.code (TapePower.resultRegister 6 (R 0) (R 3)))
    (decreaseProgram R) (fun _ => decreaseStart)

/-- Initial control state of the cleanup stage of the parameter search routine. -/
def cleanupStart : CleanupState := .inl .start
/-- Terminal control state of the cleanup stage of the parameter search routine. -/
def cleanupDone : CleanupState := .inr decreaseDone

theorem runs_cleanup (R : Registers) (σ : TapeStore) (c : ℕ)
    (ho : σ (R 0) = []) (hd : σ (R 3) = []) :
    RunsIn (cleanupProgram R).step
      (cfg cleanupStart (storeTapes (TapePowerCompare.outputStore 6 (R 0) (R 3)
        (candidateStore R σ (c + 2)) (c + 2))))
      (cfg cleanupDone (storeTapes (candidateStore R σ c)))
      (2 * (c + 2) ^ 6 + 5 + 1 + 9) := by
  have he := erase_output 6 R σ (c + 2) ho hd
  have hd := runs_decrease R σ c
  exact join_runs _ _ _ he rfl hd

/-- Control states for the sixth stage of the parameter search routine. -/
abbrev SixthState := TapePowerSearch.State 6 ⊕ CleanupState

/-- Transition function for the sixth stage of the parameter search routine. -/
def sixthProgram (R : Registers) : TapeMultiProgram SixthState :=
  joinCode (TapePowerSearch.program 6 true continueLe R) (cleanupProgram R)
    (fun _ => cleanupStart)

/-- Initial control state of the sixth stage of the parameter search routine. -/
def sixthStart : SixthState := .inl (TapePowerSearch.start 6)
/-- Terminal control state of the sixth stage of the parameter search routine. -/
def sixthDone : SixthState := .inr cleanupDone

/-- Transition budget for the parameter search routine at its sixth stage. -/
def sixthCost (d : ℕ) : ℕ :=
  TapePowerSearch.cost 6 true d (independenceOrder d / 2 + 1) 0 + 1 +
    (2 * (independenceOrder d + 2) ^ 6 + 5 + 1 + 9)

theorem runs_sixth (R : Registers) (σ : TapeStore) (d : ℕ)
    (ho : σ (R 0) = []) (hs : σ (R 2) = []) (hd : σ (R 3) = [])
    (ht : σ (R 4) = List.replicate d true) :
    RunsIn (sixthProgram R).step
      (cfg sixthStart (storeTapes (candidateStore R σ 0)))
      (cfg sixthDone (storeTapes (candidateStore R σ (independenceOrder d))))
      (sixthCost d) := by
  have hs := TapePowerSearch.runs_sixth_boundary R σ d ho hs hd ht
  have hc := runs_cleanup R σ (independenceOrder d) ho hd
  exact join_runs _ _ _ hs rfl hc

@[simp] theorem sixth_done (R : Registers) (h : TapeHeads) :
    sixthProgram R sixthDone h = none := rfl

end TapeParameterSearch
end DepthThreeLowerBound

end Complexity
