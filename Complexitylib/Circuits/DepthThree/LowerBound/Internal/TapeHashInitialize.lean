/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeStoreRepresentation

/-!
# Unrestricted depth-three lower bound: tape hash initialize

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeHashInitialize.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeHashInitialize

open TapeMultiProgram TapeRouting TapeRegister

/-- Control states of the hash initialize routine. -/
abbrev State := TapeCopy.State ⊕ TapeFill.FillState

/-- Transition function of the hash initialize routine. -/
def program : TapeMultiProgram State :=
  joinCode (TapeCopy.code ringDegree scratchA) (TapeFill.fillProgram scratchA hashBits false)
    (fun _ => TapeFill.fillStart)

/-- Initial control state of the hash initialize routine. -/
def start : State := .inl TapeCopy.State.start
/-- Terminal control state of the hash initialize routine. -/
def done : State := .inr TapeFill.fillDone

theorem runs_initialize (σ : TapeStore) (r : ℕ)
    (hr : σ ringDegree = List.replicate r true)
    (hs : σ scratchA = []) (hh : σ hashBits = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update σ hashBits (List.replicate r false))))
      (10 * r + 8) := by
  let τ := Function.update σ scratchA (σ ringDegree)
  have hcopy := TapeStoreRuns.copy (by decide : ringDegree ≠ scratchA) σ hs
  have hfill := TapeStoreRuns.fill (by decide : scratchA ≠ hashBits) false τ r
    (by simp [τ, hr])
  have hall := join_runs (TapeCopy.code ringDegree scratchA)
    (TapeFill.fillProgram scratchA hashBits false) (fun _ => TapeFill.fillStart)
    hcopy rfl hfill
  have hstore : Function.update (Function.update τ scratchA []) hashBits
      (List.replicate r false ++ τ hashBits) =
        Function.update σ hashBits (List.replicate r false) := by
    have hreset : Function.update τ scratchA [] = σ := by
      simp only [τ, Function.update_idem, ← hs, Function.update_eq_self]
    rw [hreset]
    simp [τ, hh, hashBits, scratchA]
  have htime : 2 * r + 4 + 1 + (8 * r + 3) = 10 * r + 8 := by omega
  simpa only [program, start, done, hstore, hr, List.length_replicate, htime] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeHashInitialize
end DepthThreeLowerBound

end Complexity
