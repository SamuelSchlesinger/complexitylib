/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeHashInner

/-!
# Unrestricted depth-three lower bound: tape hash row

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeHashRow.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeHashRow

open TapeMultiProgram TapeRouting TapeRegister

/-- Control states for the run stage of the hash row routine. -/
abbrev RunState := TapeCopy.State ⊕ TapeHashInner.State
/-- Control states for the clear stage of the hash row routine. -/
abbrev ClearState := RunState ⊕ TapeErase.State
/-- Control states of the hash row routine. -/
abbrev State := ClearState ⊕ TapeErase.State

/-- Transition function for the run stage of the hash row routine. -/
def runProgram : TapeMultiProgram RunState :=
  joinCode (TapeCopy.code indexC indexA) TapeHashInner.program
    (fun _ => TapeHashInner.start)

/-- Transition function for the clear stage of the hash row routine. -/
def clearProgram : TapeMultiProgram ClearState :=
  joinCode runProgram (TapeErase.code indexA) (fun _ => TapeErase.State.start)

/-- Transition function of the hash row routine. -/
def program : TapeMultiProgram State :=
  joinCode clearProgram (TapeErase.code indexB) (fun _ => TapeErase.State.start)

/-- Initial control state of the hash row routine. -/
def start : State := .inl (.inl (.inl TapeCopy.State.start))
/-- Terminal control state of the hash row routine. -/
def done : State := .inr TapeErase.State.done

/-- Tape-store contents at the result stage of the hash row routine. -/
def resultStore (σ : TapeStore) (i d : ℕ) : TapeStore :=
  Function.update σ hashBits
    (hashUpdateRow (σ keyBits) (σ dataBits) i (List.range d) (σ hashBits))

theorem runs_row (σ : TapeStore) (i d r : ℕ)
    (hi : i < r) (hd : σ dataLength = List.replicate d true)
    (ha : σ indexA = []) (hb : σ indexB = [])
    (hc : σ indexC = List.replicate i true)
    (hkey : (σ keyBits).length = d + r - 1)
    (hdata : (σ dataBits).length = d) (hout : (σ hashBits).length = r) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (resultStore σ i d)))
      (d * (4 * i + 8 * d + 29) + 4 * i + 8 * d + 25) := by
  let τ := Function.update σ indexA (σ indexC)
  let τ₁ := TapeHashInner.progressStore τ i d
  let τ₂ := Function.update τ₁ indexA []
  let τ₃ := Function.update τ₂ indexB []
  have hcopy := TapeStoreRuns.copy (by decide : indexC ≠ indexA) σ ha
  have hinner := TapeHashInner.runs_inner τ i d r hi
    (by simp [τ, hd, dataLength, indexA])
    (by simp [τ, hc])
    (by simp [τ, hb, indexA, indexB])
    (by simp [τ, hc, indexA, indexC])
    (by simpa [τ, indexA, keyBits] using hkey)
    (by simpa [τ, indexA, dataBits] using hdata)
    (by simpa [τ, indexA, hashBits] using hout)
  have hrun := join_runs (TapeCopy.code indexC indexA) TapeHashInner.program
    (fun _ => TapeHashInner.start) hcopy rfl hinner
  have heraseA := TapeStoreRuns.erase indexA τ₁
  have hclear := join_runs runProgram (TapeErase.code indexA)
    (fun _ => TapeErase.State.start) hrun rfl heraseA
  have heraseB := TapeStoreRuns.erase indexB τ₂
  have hall := join_runs clearProgram (TapeErase.code indexB)
    (fun _ => TapeErase.State.start) hclear rfl heraseB
  have hstore : τ₃ = resultStore σ i d := by
    funext q
    by_cases hB : q = indexB
    · subst q
      simp [τ₃, resultStore, hb, indexB, hashBits]
    · by_cases hA : q = indexA
      · subst q
        simp [τ₃, τ₂, resultStore, ha, indexA, indexB, hashBits]
      · by_cases hH : q = hashBits
        · subst q
          simp [τ₃, τ₂, τ₁, TapeHashInner.progressStore, τ, resultStore,
            indexA, indexB, hashBits, keyBits, dataBits]
        · simp [τ₃, τ₂, τ₁, TapeHashInner.progressStore, τ, resultStore, hB, hA, hH]
  have hlenC : (σ indexC).length = i := by simp [hc]
  have hlenA : (τ₁ indexA).length = i + d := by
    simp [τ₁, TapeHashInner.progressStore, indexA, indexB]
  have hlenB : (τ₂ indexB).length = d := by
    simp [τ₂, τ₁, TapeHashInner.progressStore, indexA, indexB]
  have htime : ((2 * i + 4 + 1 + (d * (4 * i + 8 * d + 29) + 4 * d + 8)) +
      1 + (2 * (i + d) + 5)) + 1 + (2 * d + 5) =
      d * (4 * i + 8 * d + 29) + 4 * i + 8 * d + 25 := by ring
  have hall' : RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes τ₃))
      (d * (4 * i + 8 * d + 29) + 4 * i + 8 * d + 25) := by
    simpa only [program, start, done, hlenC, hlenA, hlenB, htime] using hall
  simpa only [hstore] using hall'

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeHashRow
end DepthThreeLowerBound

end Complexity
