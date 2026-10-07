/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeConvolutionRows

/-!
# Unrestricted depth-three lower bound: tape convolution prepare

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeConvolutionPrepare.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeConvolutionPrepare

open TapeMultiProgram TapeRouting TapeUnary TapeArithmetic TapeRegister

/-- Control states for the copy stage of the convolution prepare routine. -/
abbrev CopyState := TapeCopy.State ⊕ TapeCopy.State
/-- Control states for the add stage of the convolution prepare routine. -/
abbrev AddState := CopyState ⊕ TapeArithmetic.AddState
/-- Control states for the fill stage of the convolution prepare routine. -/
abbrev FillState := AddState ⊕ TapeFill.FillState
/-- Control states of the convolution prepare routine. -/
abbrev State := FillState ⊕ TapeCopy.State

/-- Copy the ring degree into the two convolution loop counters. -/
def copies : TapeMultiProgram CopyState :=
  joinCode (TapeCopy.code ringDegree loop0) (TapeCopy.code ringDegree loop1)
    (fun _ => TapeCopy.State.start)

/-- Add the copied counters to determine the convolution workspace length. -/
def addition : TapeMultiProgram AddState :=
  joinCode copies (addProgram loop1 loop0) (fun _ => addStart)

/-- Fill the convolution output workspace with false bits. -/
def filling : TapeMultiProgram FillState :=
  joinCode addition (TapeFill.fillProgram loop0 productBits false) (fun _ => TapeFill.fillStart)

/-- Transition function of the convolution prepare routine. -/
def program : TapeMultiProgram State :=
  joinCode filling (TapeCopy.code ringDegree loop0) (fun _ => TapeCopy.State.start)

/-- Initial control state of the convolution prepare routine. -/
def start : State := .inl (.inl (.inl (.inl TapeCopy.State.start)))
/-- Terminal control state of the convolution prepare routine. -/
def done : State := .inr TapeCopy.State.done

theorem runs_prepare (σ : TapeStore) (r : ℕ)
    (hr : σ ringDegree = List.replicate r true)
    (hL0 : σ loop0 = []) (hL1 : σ loop1 = [])
    (hI : σ indexA = []) (hOut : σ productBits = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (TapeConvolutionRows.frame σ r 0 (List.replicate (r + r) false))))
      (30 * r + 22) := by
  let σ₁ := Function.update σ loop0 (σ ringDegree)
  let σ₂ := Function.update σ₁ loop1 (σ₁ ringDegree)
  let σ₃ := Function.update (Function.update σ₂ loop1 []) loop0 (List.replicate (r + r) true)
  let σ₄ := Function.update (Function.update σ₃ loop0 []) productBits (List.replicate (r + r) false)
  let σ₅ := Function.update σ₄ loop0 (σ₄ ringDegree)
  have hcopy0 := TapeStoreRuns.copy (by decide : ringDegree ≠ loop0) σ hL0
  have hcopy1 := TapeStoreRuns.copy (by decide : ringDegree ≠ loop1) σ₁ (by
    simp [σ₁, hL1, loop0, loop1])
  have hc := join_runs (TapeCopy.code ringDegree loop0) (TapeCopy.code ringDegree loop1)
    (fun _ => TapeCopy.State.start) hcopy0 rfl hcopy1
  have hadd := TapeStoreRuns.add (by decide : loop1 ≠ loop0) σ₂ r r
    (by simp [σ₂, σ₁, hr, ringDegree, loop0])
    (by simp [σ₂, σ₁, hr, loop0, loop1])
  have ha := join_runs copies (addProgram loop1 loop0) (fun _ => addStart) hc rfl hadd
  have hfill := TapeStoreRuns.fill (by decide : loop0 ≠ productBits) false σ₃ (r + r) (by
    simp [σ₃])
  have hfill' : RunsIn (TapeFill.fillProgram loop0 productBits false).step
      (cfg TapeFill.fillStart (storeTapes σ₃)) (cfg TapeFill.fillDone (storeTapes σ₄))
      (8 * (r + r) + 3) := by
    simpa only [σ₄, show σ₃ productBits = [] by
      simp [σ₃, σ₂, σ₁, hOut, loop0, loop1, productBits], List.append_nil] using hfill
  have hf := join_runs addition (TapeFill.fillProgram loop0 productBits false)
    (fun _ => TapeFill.fillStart) ha rfl hfill'
  have hlast := TapeStoreRuns.copy (by decide : ringDegree ≠ loop0) σ₄ (by
    simp [σ₄, loop0, productBits])
  have hall := join_runs filling (TapeCopy.code ringDegree loop0)
    (fun _ => TapeCopy.State.start) hf rfl hlast
  have hstore : σ₅ = TapeConvolutionRows.frame σ r 0 (List.replicate (r + r) false) := by
    funext k
    by_cases h0 : k = loop0
    · subst k
      simp [σ₅, σ₄, σ₃, σ₂, σ₁, hr, ringDegree, loop0, loop1, productBits]
    · by_cases hp : k = productBits
      · subst k
        simp [σ₅, σ₄, TapeConvolutionRows.frame, loop0, indexA, productBits]
      · by_cases h1 : k = loop1
        · subst k
          simp [σ₅, σ₄, σ₃, TapeConvolutionRows.frame, hL1, loop0, loop1, indexA, productBits]
        · by_cases hi : k = indexA
          · subst k
            simp [σ₅, σ₄, σ₃, σ₂, σ₁, TapeConvolutionRows.frame, hI,
              loop0, loop1, indexA, productBits]
          · simp [σ₅, σ₄, σ₃, σ₂, σ₁, TapeConvolutionRows.frame, h0, hp, h1, hi]
  have hl0 : (σ ringDegree).length = r := by simp [hr]
  have hl1 : (σ₁ ringDegree).length = r := by simp [σ₁, hr, ringDegree, loop0]
  have hlf : (σ₄ ringDegree).length = r := by
    simp [σ₄, σ₃, σ₂, σ₁, hr, ringDegree, loop0, loop1, productBits]
  have htime : ((2 * r + 4 + 1 + (2 * r + 4)) + 1 + (8 * r + 3)) +
      1 + (8 * (r + r) + 3) + 1 + (2 * r + 4) = 30 * r + 22 := by omega
  dsimp only [σ₅] at hstore
  simpa only [program, start, done, hstore, hl0, hl1, hlf, htime] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeConvolutionPrepare
end DepthThreeLowerBound

end Complexity
