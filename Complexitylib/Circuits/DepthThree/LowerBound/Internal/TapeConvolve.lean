/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeConvolutionPrepare

/-!
# Unrestricted depth-three lower bound: tape convolve

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeConvolve.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeConvolve

open TapeMultiProgram TapeRouting TapeUnary TapeArithmetic TapeRegister

/-- Control states for the work stage of the convolve routine. -/
abbrev WorkState := TapeConvolutionPrepare.State ⊕ TapeConvolutionRows.State
/-- Control states of the convolve routine. -/
abbrev State := WorkState ⊕ TapeErase.State

/-- Compose the main computational stages of the routine. -/
def work : TapeMultiProgram WorkState :=
  joinCode TapeConvolutionPrepare.program TapeConvolutionRows.program
    (fun _ => TapeConvolutionRows.start)

/-- Transition function of the convolve routine. -/
def program : TapeMultiProgram State :=
  joinCode work (TapeErase.code indexA) (fun _ => TapeErase.State.start)

/-- Initial control state of the convolve routine. -/
def start : State := .inl (.inl TapeConvolutionPrepare.start)
/-- Terminal control state of the convolve routine. -/
def done : State := .inr TapeErase.State.done

/-- Transition budget for the convolve routine. -/
def cost (r : ℕ) : ℕ := r * (r * (24 * r + 43) + 4 * r + 23) + 32 * r + 32

theorem runs_convolve (σ : TapeStore) (a b : List Bool) (r : ℕ)
    (hA : σ hashBits = a) (hB : σ accumBits = b)
    (hlenA : a.length = r) (hlenB : b.length = r)
    (hCount : σ ringDegree = List.replicate r true)
    (hL0 : σ loop0 = []) (hL1 : σ loop1 = [])
    (hI : σ indexA = []) (hJ : σ indexB = [])
    (hK : σ indexC = []) (hS : σ scratchA = []) (hOut : σ productBits = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update σ productBits (convolveBitLists a b))))
      (cost r) := by
  have hp := TapeConvolutionPrepare.runs_prepare σ r hCount hL0 hL1 hI hOut
  have hr := TapeConvolutionRows.runs_rows σ a b 0 r (List.replicate (r + r) false)
    hA hB hJ (by simpa only [hlenB] using hCount) hL1 hK hS (by omega) (by simp [hlenA, hlenB])
  have hout : convolutionUpdateRows a b (List.range' 0 r) (List.replicate (r + r) false) =
      convolveBitLists a b := by
    rw [← convolveByUpdates_eq]
    simp only [convolveByUpdates, hlenA, hlenB, List.range_eq_range']
  have hr' : RunsIn TapeConvolutionRows.program.step
      (cfg TapeConvolutionRows.start
        (storeTapes (TapeConvolutionRows.frame σ r 0 (List.replicate (r + r) false))))
      (cfg TapeConvolutionRows.done
        (storeTapes (TapeConvolutionRows.frame σ 0 r (convolveBitLists a b))))
      (r * (r * (8 * r + 16 * r + 43) + 4 * r + 23) + 3) := by
    simpa only [Nat.zero_add, hout, hlenA, hlenB] using hr
  have hw := join_runs TapeConvolutionPrepare.program TapeConvolutionRows.program
    (fun _ => TapeConvolutionRows.start) hp rfl hr'
  let ρ := TapeConvolutionRows.frame σ 0 r (convolveBitLists a b)
  have he := TapeStoreRuns.erase indexA ρ
  have hall := join_runs work (TapeErase.code indexA) (fun _ => TapeErase.State.start) hw rfl he
  have hframe : Function.update ρ indexA [] = Function.update σ productBits (convolveBitLists a b)
    := by
    funext k
    by_cases hi : k = indexA
    · subst k
      simp [hI, indexA, productBits]
    · by_cases hl : k = loop0
      · subst k
        simp [ρ, Function.update, hL0, indexA, loop0, productBits]
      · by_cases hp : k = productBits
        · subst k
          simp [ρ, Function.update, indexA, productBits]
        · simp [ρ, TapeConvolutionRows.frame, Function.update, hi, hl, hp]
  have hlen : (ρ indexA).length = r := by simp [ρ]
  have hlinear : 8 * r + 16 * r + 43 = 24 * r + 43 := by omega
  have htime : (30 * r + 22 + 1 +
      (r * (r * (8 * r + 16 * r + 43) + 4 * r + 23) + 3)) + 1 + (2 * r + 5) = cost r := by
    rw [hlinear]
    unfold cost
    omega
  simpa only [program, start, done, hframe, hlen, htime] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeConvolve
end DepthThreeLowerBound

end Complexity
