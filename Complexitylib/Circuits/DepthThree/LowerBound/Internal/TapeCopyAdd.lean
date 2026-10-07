/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeStoreRepresentation

/-!
# Unrestricted depth-three lower bound: tape copy add

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeCopyAdd.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeCopyAdd

open TapeMultiProgram TapeRouting TapeArithmetic

/-- Control states of the copy add routine. -/
abbrev State := TapeCopy.State ⊕ AddState

/-- Transition function of the copy add routine. -/
def program (src scratch dst : TapeRegister) : TapeMultiProgram State :=
  joinCode (TapeCopy.code src scratch) (addProgram scratch dst) (fun _ => addStart)

/-- Initial control state of the copy add routine. -/
def start : State := .inl .start
/-- Terminal control state of the copy add routine. -/
def done : State := .inr addDone

@[simp] theorem program_done (src scratch dst : TapeRegister) (h : TapeHeads) :
    program src scratch dst done h = none := rfl

theorem runs_add {src scratch dst : TapeRegister}
    (hsc : src ≠ scratch) (hcd : scratch ≠ dst) (σ : TapeStore) (n m : ℕ)
    (hn : σ src = List.replicate n true) (hm : σ dst = List.replicate m true)
    (hc : σ scratch = []) :
    RunsIn (program src scratch dst).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update σ dst (List.replicate (m + n) true))))
      (10 * n + 8) := by
  let τ := Function.update σ scratch (List.replicate n true)
  have hcopy := TapeStoreRuns.copy hsc σ hc
  have hcopy' : RunsIn (TapeCopy.code src scratch).step
      (cfg TapeCopy.State.start (storeTapes σ))
      (cfg TapeCopy.State.done (storeTapes τ)) (2 * n + 4) := by
    simpa only [hn, List.length_replicate] using hcopy
  have hadd := TapeStoreRuns.add hcd τ n m
    (by simp [τ]) (by simp [τ, hm, Ne.symm hcd])
  have hclear : Function.update τ scratch [] = σ := by
    dsimp [τ]
    rw [Function.update_idem, ← hc, Function.update_eq_self]
  rw [hclear] at hadd
  have hall := join_runs (TapeCopy.code src scratch) (addProgram scratch dst)
    (fun _ => addStart) hcopy' rfl hadd
  have hcost : (2 * n + 4) + 1 + (8 * n + 3) = 10 * n + 8 := by omega
  simpa only [program, start, done, hcost] using hall

end TapeCopyAdd
end DepthThreeLowerBound

end Complexity
