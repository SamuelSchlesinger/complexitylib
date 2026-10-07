/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeInputPrepare
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeInputBlocks
public import Mathlib.Tactic.Linarith

/-!
# Unrestricted depth-three lower bound: tape decode block

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeDecodeBlock.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeDecodeBlock

open TapeMultiProgram TapeRouting

/-- Control states for the finish stage of the decode block routine. -/
abbrev FinishState := TapeInputBlocks.State ⊕ TapeErase.State

/-- Transition function for the finish stage of the decode block routine. -/
def finishProgram (kind : InputBlockKind) : TapeMultiProgram FinishState :=
  joinCode (TapeInputBlocks.canonicalProgram kind) (TapeErase.code TapeRegister.temp0)
    (fun _ => TapeErase.State.start)

/-- Initial control state of the finish stage of the decode block routine. -/
def finishStart : FinishState := .inl TapeInputBlocks.start
/-- Terminal control state of the finish stage of the decode block routine. -/
def finishDone : FinishState := .inr TapeErase.State.done

/-- Control states of the decode block routine. -/
abbrev State (kind : InputBlockKind) := TapeInputPrepare.State kind ⊕ FinishState

/-- Transition function of the decode block routine. -/
def program (kind : InputBlockKind) : TapeMultiProgram (State kind) :=
  joinCode (TapeInputPrepare.program kind) (finishProgram kind) (fun _ => finishStart)

/-- Initial control state of the decode block routine. -/
def start (kind : InputBlockKind) : State kind := .inl (TapeInputPrepare.start kind)
/-- Terminal control state of the decode block routine. -/
def done (kind : InputBlockKind) : State kind := .inr finishDone

@[simp] theorem program_done (kind : InputBlockKind) (h : TapeHeads) :
    program kind (done kind) h = none := rfl

/-- Tape-store contents at the output stage of the decode block routine. -/
def outputStore (σ : TapeStore) (w : List Bool) (kind : InputBlockKind) : TapeStore :=
  Function.update σ (TapeInputBlocks.outputRegister kind) (inputBlockData w kind)

theorem runs_block (σ : TapeStore) (w : List Bool) (kind : InputBlockKind)
    (hfit : InputFits w) (hw : σ TapeRegister.input = w)
    (hd : σ 2 = List.replicate (dataDimension w.length) true)
    (hr : σ 3 = List.replicate (hashDimension (dataDimension w.length)) true)
    (ht : σ 4 = List.replicate (independenceOrder (dataDimension w.length)) true)
    (h29 : σ 29 = []) (h30 : σ 30 = []) (h31 : σ 31 = [])
    (h5 : σ 5 = []) (h6 : σ 6 = []) (h7 : σ 7 = [])
    (hout : σ (TapeInputBlocks.outputRegister kind) = []) :
    RunsIn (program kind).step (cfg (start kind) (storeTapes σ))
      (cfg (done kind) (storeTapes (outputStore σ w kind)))
      (200 * (w.length + 1) ^ 2) := by
  let τ := TapeInputPrepare.outputStore σ w.length kind
  let υ := Function.update (Function.update τ TapeRegister.temp1 [])
    (TapeInputBlocks.outputRegister kind) (inputBlockData w kind)
  have hp := TapeInputPrepare.runs_prepare σ w.length kind hd hr ht h29 h30 h31 h5 h6 h7
  have hi : τ TapeRegister.temp0 = List.replicate (inputBlockOffset w.length kind) true := by
    simp [τ, TapeInputPrepare.outputStore, TapeRegister.temp0]
  have hc : τ TapeRegister.temp1 = List.replicate (inputBlockLength w.length kind) true := by
    simp [τ, TapeInputPrepare.outputStore, TapeRegister.temp1]
  have hx := TapeInputBlocks.runs_canonical_block kind τ w hfit
    (by simpa [τ, TapeInputPrepare.outputStore, TapeRegister.input] using hw) hi hc
    (by simpa [τ, TapeInputPrepare.outputStore, TapeRegister.temp2] using h31)
    (by cases kind <;> simpa [τ, TapeInputPrepare.outputStore,
      TapeInputBlocks.outputRegister, TapeRegister.dataBits, TapeRegister.keyBits,
      TapeRegister.polyBits, TapeRegister.coeffBits] using hout)
  have he := TapeStoreRuns.erase TapeRegister.temp0 υ
  have hindex : υ TapeRegister.temp0 =
      List.replicate (inputBlockOffset w.length kind) true := by
    cases kind <;> simp [υ, τ, TapeInputPrepare.outputStore,
      TapeInputBlocks.outputRegister, TapeRegister.temp0, TapeRegister.temp1,
      TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits]
  have hrestore : Function.update υ TapeRegister.temp0 [] = outputStore σ w kind := by
    funext q
    cases kind <;> by_cases hq29 : q = 29 <;> by_cases hq30 : q = 30 <;>
      simp_all [υ, τ, TapeInputPrepare.outputStore, outputStore,
        TapeInputBlocks.outputRegister, TapeRegister.temp0, TapeRegister.temp1,
        TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits,
        Function.update_apply]
  rw [hrestore, hindex, List.length_replicate] at he
  have hf := join_runs (TapeInputBlocks.canonicalProgram kind)
    (TapeErase.code TapeRegister.temp0) (fun _ => TapeErase.State.start) hx rfl he
  have hall := join_runs (TapeInputPrepare.program kind) (finishProgram kind)
    (fun _ => finishStart) hp (by simp) hf
  apply hall.mono
  have hpbound := TapeInputPrepare.cost_le w.length kind
  have hxbound := TapeInputBlocks.canonical_cost_le hfit kind
  have hobound := inputBlock_offset_le hfit kind
  nlinarith [Nat.zero_le (w.length ^ 2)]

end TapeDecodeBlock
end DepthThreeLowerBound

end Complexity
