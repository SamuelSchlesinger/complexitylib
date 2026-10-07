/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeStoreRepresentation
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeMultiply
public import Lean.Elab.Tactic.Omega

/-!
# Unrestricted depth-three lower bound: tape product length

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeProductLength.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeProductLength

open TapeMultiProgram TapeRouting TapeUnary TapeCopy

/-- Control states of the product length routine. -/
abbrev State := TapeCopy.State ⊕ TapeMultiply.State

/-- Transition function of the product length routine. -/
def program : TapeMultiProgram State :=
  joinCode (TapeCopy.code 4 5) (TapeMultiply.program 5 3 6 30)
    (fun _ => TapeMultiply.start)

/-- Initial control state of the product length routine. -/
def start : State := .inl TapeCopy.State.start
/-- Terminal control state of the product length routine. -/
def done : State := .inr TapeMultiply.done

/-- Tape-store contents at the output stage of the product length routine. -/
def outputStore (σ : TapeStore) (n m : ℕ) : TapeStore :=
  Function.update σ 30 (List.replicate (n * m) true)

@[simp] theorem outputStore_destination (σ : TapeStore) (n m : ℕ) :
    outputStore σ n m 30 = List.replicate (n * m) true := by
  simp [outputStore]

theorem outputStore_other (σ : TapeStore) (n m : ℕ) (r : TapeRegister)
    (hr : r ≠ 30) : outputStore σ n m r = σ r := by
  simp [outputStore, Function.update, hr]

/-- Transition budget for the product length routine. -/
def cost (n m : ℕ) : ℕ := n * (10 * m + 16) + 8

private theorem frame_store (σ : TapeStore) (n m z : ℕ)
    (h3 : σ 3 = List.replicate m true) (h6 : σ 6 = []) :
    TapeMultiply.tapes 5 3 6 30 (storeTapes σ) n m 0 z =
      storeTapes (Function.update (Function.update σ 5 (List.replicate n true))
        30 (List.replicate z true)) := by
  funext r
  by_cases h5 : r = 5
  · subst r
    simp [TapeMultiply.tapes, onPair, storeTapes, counterTape]
  · by_cases hs : r = 3
    · subst r
      simp [TapeMultiply.tapes, onPair, storeTapes, counterTape, h3]
    · by_cases hc : r = 6
      · subst r
        simp [TapeMultiply.tapes, onPair, storeTapes, counterTape, h6]
      · by_cases hd : r = 30
        · subst r
          simp [TapeMultiply.tapes, onPair, storeTapes, counterTape]
        · simp [TapeMultiply.tapes, onPair, storeTapes, Function.update,
            h5, hs, hc, hd]

theorem runs_product (σ : TapeStore) (n m : ℕ)
    (h4 : σ 4 = List.replicate n true) (h3 : σ 3 = List.replicate m true)
    (h5 : σ 5 = []) (h6 : σ 6 = []) (h30 : σ 30 = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (outputStore σ n m))) (cost n m) := by
  let copied := Function.update σ 5 (List.replicate n true)
  have hcopy := TapeStoreRuns.copy (src := 4) (dst := 5) (by decide) σ h5
  simp only [h4, List.length_replicate] at hcopy
  have hi : TapeMultiply.tapes 5 3 6 30 (storeTapes σ) n m 0 0 =
      storeTapes copied := by
    calc
      TapeMultiply.tapes 5 3 6 30 (storeTapes σ) n m 0 0 =
          storeTapes (Function.update copied 30 []) := by
        simpa only [copied, List.replicate_zero] using frame_store σ n m 0 h3 h6
      _ = storeTapes copied := by
        apply congrArg storeTapes
        apply Function.update_eq_self_iff.mpr
        simp [copied, h30]
  have hrestore : Function.update σ 5 [] = σ :=
    Function.update_eq_self_iff.mpr h5.symm
  have ho : TapeMultiply.tapes 5 3 6 30 (storeTapes σ) 0 m 0 (n * m) =
      storeTapes (outputStore σ n m) := by
    simpa only [List.replicate_zero, hrestore, outputStore] using
      frame_store σ 0 m (n * m) h3 h6
  have hmul := TapeMultiply.runs_mul (outer := 5) (source := 3) (scratch := 6)
    (destination := 30) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (storeTapes σ) n m 0
  simp only [Nat.zero_add, hi, ho] at hmul
  have h := join_runs (TapeCopy.code 4 5) (TapeMultiply.program 5 3 6 30)
    (fun _ => TapeMultiply.start) hcopy rfl hmul
  have htime : 2 * n + 4 + 1 + (n * (10 * m + 14) + 3) =
      n * (10 * m + 16) + 8 := by
    have hcoeff : 10 * m + 16 = (10 * m + 14) + 2 := by omega
    rw [hcoeff, Nat.mul_add n (10 * m + 14) 2]
    omega
  simpa only [program, start, done, cost, htime] using h

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeProductLength
end DepthThreeLowerBound

end Complexity
