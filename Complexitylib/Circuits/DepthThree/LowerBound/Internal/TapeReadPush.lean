/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeStoreRepresentation

/-!
# Unrestricted depth-three lower bound: tape read push

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeReadPush.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeReadPush

open TapeMultiProgram TapeRouting TapeUnary TapeCopy TapeArithmetic

/-- Control states of the read push routine. -/
abbrev State := TapeArray.State ⊕ (Bool × TapeUnary.IncState)

/-- Transition function of the read push routine. -/
def program (index source destination : TapeRegister) : TapeMultiProgram State :=
  joinCode (TapeArray.code index source id)
    (TapeProductTerm.carryCode (fun b : Bool => TapeFill.pushProgram destination b))
    (fun q => (TapeProductTerm.readFlag q, TapeUnary.IncState.start))

/-- Initial control state of the read push routine. -/
def start : State := .inl TapeArray.State.start

/-- Terminal control state of the read push routine. -/
def done (b : Bool) : State := .inr (b, TapeUnary.IncState.done)

theorem runs_read_push {index source : TapeRegister} (hne : index ≠ source)
    (destination : TapeRegister) (T : TapeTapes)
    («prefix» suffix acc : List Bool) (b : Bool)
    (hi : T index = counterTape «prefix».length)
    (hs : T source = wordTape («prefix» ++ b :: suffix))
    (hd : T destination = wordTape acc) :
    RunsIn (program index source destination).step (cfg start T)
      (cfg (done b) (Function.update T destination (wordTape (b :: acc))))
      (2 * «prefix».length + 7) := by
  have hread := TapeProductTerm.read_at hne T «prefix» suffix b hi hs
  have hpush := TapeFill.runs_push destination b T acc hd
  have hcarry := TapeProductTerm.carry_runs
    (fun b : Bool => TapeFill.pushProgram destination b) b hpush
  have hall := join_runs (TapeArray.code index source id)
    (TapeProductTerm.carryCode (fun b : Bool => TapeFill.pushProgram destination b))
    (fun q => (TapeProductTerm.readFlag q, TapeUnary.IncState.start)) hread rfl hcarry
  have htime : (2 * «prefix».length + 4) + 1 + 2 = 2 * «prefix».length + 7 := by omega
  simpa only [program, start, done, htime] using hall

@[simp] theorem program_done (index source destination : TapeRegister)
    (b : Bool) (h : TapeHeads) :
    program index source destination (done b) h = none := rfl

theorem runs_store {index source : TapeRegister} (hne : index ≠ source)
    (destination : TapeRegister) (σ : TapeStore) («prefix» suffix : List Bool) (b : Bool)
    (hi : σ index = List.replicate «prefix».length true)
    (hs : σ source = «prefix» ++ b :: suffix) :
    RunsIn (program index source destination).step (cfg start (storeTapes σ))
      (cfg (done b) (storeTapes (Function.update σ destination (b :: σ destination))))
      (2 * «prefix».length + 7) := by
  have h := runs_read_push hne destination (storeTapes σ) «prefix» suffix (σ destination) b
    (by simp only [storeTapes_apply, hi, counterTape])
    (by simp only [storeTapes_apply, hs]) rfl
  simpa only [storeTapes_update] using h

end TapeReadPush
end DepthThreeLowerBound

end Complexity
