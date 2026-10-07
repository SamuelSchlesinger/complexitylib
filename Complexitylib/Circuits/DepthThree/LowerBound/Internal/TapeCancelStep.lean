/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeNaturalAccess

/-!
# Unrestricted depth-three lower bound: tape cancel step

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeCancelStep.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeCancelStep

open TapeMultiProgram TapeRouting TapeUnary TapeProductTerm TapeRegister

/-- Control states for the read stage of the cancel step routine. -/
abbrev ReadState := TapeArray.State ⊕ (Bool × TapeArray.State)
/-- Control states for the first stage of the cancel step routine. -/
abbrev FirstState := ReadState ⊕ IncState
/-- Control states of the cancel step routine. -/
abbrev State := FirstState ⊕ IncState

/-- Transition function for the read stage of the cancel step routine. -/
def readProgram (v : Bool) : TapeMultiProgram ReadState :=
  joinCode (TapeArray.code indexA polyBits id)
    (carryCode fun b : Bool => TapeArray.code indexC productBits
      (fun old => Bool.xor old (v && b)))
    (fun q => (readFlag q, TapeArray.State.start))

/-- Transition function for the first stage of the cancel step routine. -/
def firstProgram (v : Bool) : TapeMultiProgram FirstState :=
  joinCode (readProgram v) (incProgram indexA) (fun _ => IncState.start)

/-- Transition function of the cancel step routine. -/
def program (v : Bool) : TapeMultiProgram State :=
  joinCode (firstProgram v) (incProgram indexC) (fun _ => IncState.start)

/-- Initial control state of the cancel step routine. -/
def start : State := .inl (.inl (.inl TapeArray.State.start))
/-- Terminal control state of the cancel step routine. -/
def done : State := .inr IncState.done

/-- Tape-store contents at the result stage of the cancel step routine. -/
def resultStore (σ : TapeStore) (j k : ℕ) (out : List Bool) : TapeStore :=
  Function.update (Function.update (Function.update σ productBits out)
    indexA (List.replicate (j + 1) true)) indexC (List.replicate (k + 1) true)

theorem runs_step (v : Bool) (σ : TapeStore) (j k : ℕ)
    (hA : σ indexA = List.replicate j true)
    (hC : σ indexC = List.replicate k true)
    (hj : j < (σ polyBits).length) (hk : k < (σ productBits).length) :
    RunsIn (program v).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (resultStore σ j k
        (xorListAt (σ productBits) k (v && (σ polyBits).getD j false)))))
      (2 * j + 2 * k + 15) := by
  let b := (σ polyBits).getD j false
  let out := xorListAt (σ productBits) k (v && b)
  let σ₁ := Function.update σ productBits out
  let σ₂ := Function.update σ₁ indexA (List.replicate (j + 1) true)
  have hr := TapeNaturalAccess.read indexA polyBits (by decide) σ j hA hj
  have hx := TapeNaturalAccess.xorAt indexC productBits (by decide) σ k (v && b) hC hk
  have hxc := carry_runs
    (fun b : Bool => TapeArray.code indexC productBits (fun old => Bool.xor old (v && b))) b hx
  have hread := join_runs (TapeArray.code indexA polyBits id)
    (carryCode fun b : Bool => TapeArray.code indexC productBits
      (fun old => Bool.xor old (v && b)))
    (fun q => (readFlag q, TapeArray.State.start)) hr rfl hxc
  have ha := increment indexA (storeTapes σ₁) j (by
    simp [σ₁, counterTape, hA, indexA, productBits])
  have ha' : RunsIn (incProgram indexA).step
      (cfg IncState.start (storeTapes σ₁)) (cfg IncState.done (storeTapes σ₂)) 2 := by
    simpa only [σ₂, storeTapes_update, counterTape] using ha
  have hfirst := join_runs (readProgram v) (incProgram indexA)
    (fun _ => IncState.start) hread rfl ha'
  have hc := increment indexC (storeTapes σ₂) k (by
    simp [σ₂, σ₁, counterTape, hC, indexC, indexA, productBits])
  have hc' : RunsIn (incProgram indexC).step
      (cfg IncState.start (storeTapes σ₂))
      (cfg IncState.done (storeTapes (resultStore σ j k out))) 2 := by
    simpa only [resultStore, σ₂, σ₁, storeTapes_update, counterTape] using hc
  have hall := join_runs (firstProgram v) (incProgram indexC)
    (fun _ => IncState.start) hfirst rfl hc'
  have ht : (2 * j + 4 + 1 + (2 * k + 4)) + 1 + 2 + 1 + 2 =
      2 * j + 2 * k + 15 := by omega
  simpa only [program, start, done, out, b, ht] using hall

@[simp] theorem program_done (v : Bool) (h : TapeHeads) : program v done h = none := rfl

end TapeCancelStep
end DepthThreeLowerBound

end Complexity
