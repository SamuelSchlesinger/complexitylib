/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeStoreRepresentation

/-!
# Unrestricted depth-three lower bound: tape output

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeOutput.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeOutput

open TapeMultiProgram TapeRouting

/-- Control states of the output routine. -/
abbrev State := TapeArray.State ⊕ Bool

/-- Transition function for the halt stage of the output routine. -/
def haltProgram : TapeMultiProgram Bool := fun _ _ => none

/-- Read the Boolean verdict from the terminal control state of the output routine. -/
def acceptFlag : TapeArray.State → Bool
  | .done b => !b
  | _ => false

/-- Transition function of the output routine. -/
def program : TapeMultiProgram State :=
  joinCode (TapeArray.code TapeRegister.indexA TapeRegister.accumBits id)
    haltProgram acceptFlag

/-- Initial control state of the output routine. -/
def start : State := .inl .start
/-- Terminal control state of the output routine. -/
def done (answer : Bool) : State := .inr answer

@[simp] theorem program_done (answer : Bool) (h : TapeHeads) :
    program (done answer) h = none := rfl

theorem runs_output (σ : TapeStore) (b : Bool) (tail : List Bool)
    (hi : σ TapeRegister.indexA = [])
    (ha : σ TapeRegister.accumBits = b :: tail) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg (done (!b)) (storeTapes σ)) 5 := by
  have hr := TapeProductTerm.read_at
    (index := TapeRegister.indexA) (array := TapeRegister.accumBits)
    (by decide) (storeTapes σ) [] tail b
    (by simp [storeTapes, TapeUnary.counterTape, hi])
    (by simp [storeTapes, ha])
  have hh := join_runs (TapeArray.code TapeRegister.indexA TapeRegister.accumBits id)
    haltProgram acceptFlag hr rfl
    (RunsIn.refl haltProgram.step (cfg (!b) (storeTapes σ)))
  simpa only [State, program, start, done, acceptFlag, List.length_nil, Nat.mul_zero,
    Nat.zero_add, Nat.add_zero] using hh

end TapeOutput
end DepthThreeLowerBound

end Complexity
