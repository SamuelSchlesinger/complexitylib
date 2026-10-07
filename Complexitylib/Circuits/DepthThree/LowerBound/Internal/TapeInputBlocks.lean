/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeInputBlockLoop
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageInputBlockLists

/-!
# Unrestricted depth-three lower bound: tape input blocks

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeInputBlocks.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeInputBlocks

open TapeMultiProgram TapeCopy TapeRouting TapeUnary TapeArithmetic
open TapeInputBlockLoop

/-- Control states for the prepare stage of the input blocks routine. -/
abbrev PrepareState := TapeCopy.State ⊕ AddState

/-- Transition function for the prepare stage of the input blocks routine. -/
def prepareProgram (R : Registers) : TapeMultiProgram PrepareState :=
  joinCode (TapeCopy.code (count R) (scratch R))
    (addProgram (scratch R) (index R)) (fun _ => addStart)

/-- Initial control state of the prepare stage of the input blocks routine. -/
def prepareStart : PrepareState := .inl TapeCopy.State.start
/-- Terminal control state of the prepare stage of the input blocks routine. -/
def prepareDone : PrepareState := .inr addDone

/-- Control states of the input blocks routine. -/
abbrev State := PrepareState ⊕ TapeInputBlockLoop.State

/-- Transition function of the input blocks routine. -/
def program (R : Registers) : TapeMultiProgram State :=
  joinCode (prepareProgram R) (TapeInputBlockLoop.program R)
    (fun _ => TapeInputBlockLoop.start)

/-- Initial control state of the input blocks routine. -/
def start : State := .inl prepareStart
/-- Terminal control state of the input blocks routine. -/
def done : State := .inr TapeInputBlockLoop.done

@[simp] theorem prepare_done (R : Registers) (h : TapeHeads) :
    prepareProgram R prepareDone h = none := rfl

@[simp] theorem program_done (R : Registers) (h : TapeHeads) :
    program R done h = none := rfl

theorem runs_prepare (R : Registers) (σ : TapeStore) (offset len : ℕ)
    (hi : σ (index R) = List.replicate offset true)
    (hc : σ (count R) = List.replicate len true)
    (hs : σ (scratch R) = []) :
    RunsIn (prepareProgram R).step (cfg prepareStart (storeTapes σ))
      (cfg prepareDone (storeTapes
        (Function.update σ (index R) (List.replicate (offset + len) true))))
      (10 * len + 8) := by
  have hcs : count R ≠ scratch R := by simp [count, scratch]
  have hsi : scratch R ≠ index R := by simp [scratch, index]
  let U := Function.update σ (scratch R) (List.replicate len true)
  have hcopy := TapeStoreRuns.copy hcs σ hs
  have hcopy' : RunsIn (TapeCopy.code (count R) (scratch R)).step
      (cfg TapeCopy.State.start (storeTapes σ))
      (cfg TapeCopy.State.done (storeTapes U)) (2 * len + 4) := by
    simpa only [hc, List.length_replicate] using hcopy
  have hadd := TapeStoreRuns.add hsi U len offset
    (by simp [U]) (by simp [U, hi, Ne.symm hsi])
  have hclear : Function.update U (scratch R) [] = σ := by
    dsimp [U]
    rw [Function.update_idem, ← hs, Function.update_eq_self]
  have hadd' : RunsIn (addProgram (scratch R) (index R)).step
      (cfg addStart (storeTapes U))
      (cfg addDone (storeTapes
        (Function.update σ (index R) (List.replicate (offset + len) true))))
      (8 * len + 3) := by
    simpa only [hclear] using hadd
  have hall := join_runs (TapeCopy.code (count R) (scratch R))
    (addProgram (scratch R) (index R)) (fun _ => addStart) hcopy' rfl hadd'
  have ht : (2 * len + 4) + 1 + (8 * len + 3) = 10 * len + 8 := by omega
  simpa only [prepareProgram, prepareStart, prepareDone, ht] using hall

theorem blockStore_prepared (R : Registers) (σ : TapeStore) (offset len : ℕ)
    (acc : List Bool) (hc : σ (count R) = List.replicate len true)
    (hd : σ (destination R) = acc) :
    blockStore R σ (offset + len) len acc =
      Function.update σ (index R) (List.replicate (offset + len) true) := by
  funext q
  by_cases hq : q = destination R <;> by_cases hi : q = index R <;>
    by_cases hk : q = count R <;>
    simp_all [blockStore, Function.update, count, index, destination]

theorem blockStore_finished (R : Registers) (σ : TapeStore) (offset : ℕ)
    (bits : List Bool) (hi : σ (index R) = List.replicate offset true) :
    blockStore R σ offset 0 bits =
      Function.update (Function.update σ (count R) []) (destination R) bits := by
  funext q
  by_cases hq : q = destination R <;> by_cases hk : q = count R <;>
    by_cases hj : q = index R <;>
    simp_all [blockStore, Function.update, count, index, destination]

theorem runs_extract (R : Registers) (σ : TapeStore)
    («prefix» block suffix acc : List Bool)
    (hinput : σ (source R) = «prefix» ++ block ++ suffix)
    (hi : σ (index R) = List.replicate «prefix».length true)
    (hc : σ (count R) = List.replicate block.length true)
    (hs : σ (scratch R) = [])
    (hd : σ (destination R) = acc) :
    RunsIn (program R).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update (Function.update σ (count R) [])
        (destination R) (block ++ acc))))
      (block.length * (2 * «prefix».length + block.length + 27) + 12) := by
  have hp := runs_prepare R σ «prefix».length block.length hi hc hs
  have hb := TapeInputBlockLoop.runs_block R σ «prefix» block suffix acc hinput
  rw [blockStore_prepared R σ «prefix».length block.length acc hc hd,
    blockStore_finished R σ «prefix».length (block ++ acc) hi] at hb
  have hall := join_runs (prepareProgram R) (TapeInputBlockLoop.program R)
    (fun _ => TapeInputBlockLoop.start) hp (by simp) hb
  have ht : (10 * block.length + 8) + 1 +
      (block.length * (2 * «prefix».length + block.length + 17) + 3) =
      block.length * (2 * «prefix».length + block.length + 27) + 12 := by ring
  simpa only [program, start, done, ht] using hall

/-- The destination register for the selected kind of input block. -/
def outputRegister : InputBlockKind → TapeRegister
  | .data => TapeRegister.dataBits
  | .hash => TapeRegister.keyBits
  | .polynomial => TapeRegister.polyBits
  | .coefficients => TapeRegister.coeffBits

/-- Allocate input and temporary registers for decoding the selected block. -/
def canonicalRegisters (kind : InputBlockKind) : Registers where
  toFun i := match i.val with
    | 0 => TapeRegister.input
    | 1 => TapeRegister.temp0
    | 2 => TapeRegister.temp1
    | 3 => TapeRegister.temp2
    | _ => outputRegister kind
  inj' := by cases kind <;> decide

@[simp] theorem canonical_source (kind : InputBlockKind) :
    source (canonicalRegisters kind) = TapeRegister.input := rfl

@[simp] theorem canonical_index (kind : InputBlockKind) :
    index (canonicalRegisters kind) = TapeRegister.temp0 := rfl

@[simp] theorem canonical_count (kind : InputBlockKind) :
    count (canonicalRegisters kind) = TapeRegister.temp1 := rfl

@[simp] theorem canonical_scratch (kind : InputBlockKind) :
    scratch (canonicalRegisters kind) = TapeRegister.temp2 := rfl

@[simp] theorem canonical_destination (kind : InputBlockKind) :
    destination (canonicalRegisters kind) = outputRegister kind := rfl

/-- Transition function for the canonical stage of the input blocks routine. -/
def canonicalProgram (kind : InputBlockKind) : TapeMultiProgram State :=
  program (canonicalRegisters kind)

@[simp] theorem canonical_done (kind : InputBlockKind) (h : TapeHeads) :
    canonicalProgram kind done h = none := rfl

theorem canonical_cost_le {w : List Bool} (hfit : InputFits w) (kind : InputBlockKind) :
    inputBlockLength w.length kind *
        (2 * inputBlockOffset w.length kind + inputBlockLength w.length kind + 27) + 12 ≤
      w.length * (3 * w.length + 27) + 12 := by
  have hend := inputBlock_end_le hfit kind
  have hlen : inputBlockLength w.length kind ≤ w.length := by omega
  apply Nat.add_le_add_right _ 12
  exact Nat.mul_le_mul hlen (by omega)

theorem runs_canonical_block (kind : InputBlockKind) (σ : TapeStore) (w : List Bool)
    (hfit : InputFits w) (hw : σ TapeRegister.input = w)
    (hi : σ TapeRegister.temp0 = List.replicate (inputBlockOffset w.length kind) true)
    (hc : σ TapeRegister.temp1 = List.replicate (inputBlockLength w.length kind) true)
    (hs : σ TapeRegister.temp2 = []) (hd : σ (outputRegister kind) = []) :
    RunsIn (canonicalProgram kind).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update (Function.update σ TapeRegister.temp1 [])
        (outputRegister kind) (inputBlockData w kind))))
      (inputBlockLength w.length kind *
        (2 * inputBlockOffset w.length kind + inputBlockLength w.length kind + 27) + 12) := by
  have hall := runs_extract (canonicalRegisters kind) σ
    (w.take (inputBlockOffset w.length kind)) (inputBlockData w kind)
    (w.drop (inputBlockOffset w.length kind + inputBlockLength w.length kind)) []
    (by simpa only [canonical_source, hw] using inputBlock_reconstruct w kind)
    (by simpa only [canonical_index, inputBlock_prefix_length hfit kind] using hi)
    (by simpa only [canonical_count, inputBlockData_length hfit kind] using hc)
    (by simpa only [canonical_scratch] using hs)
    (by simpa only [canonical_destination] using hd)
  simpa only [canonicalProgram, canonical_count, canonical_destination,
    List.append_nil, inputBlock_prefix_length hfit kind,
    inputBlockData_length hfit kind] using hall

theorem runs_data (σ : TapeStore) (w : List Bool) (hfit : InputFits w)
    (hw : σ TapeRegister.input = w) (hi : σ TapeRegister.temp0 = [])
    (hc : σ TapeRegister.temp1 = List.replicate (dataDimension w.length) true)
    (hs : σ TapeRegister.temp2 = []) (hd : σ TapeRegister.dataBits = []) :
    RunsIn (canonicalProgram .data).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update (Function.update σ TapeRegister.temp1 [])
        TapeRegister.dataBits (inputBlockData w .data))))
      (dataDimension w.length * (dataDimension w.length + 27) + 12) := by
  simpa only [inputBlockOffset, inputBlockLength, outputRegister, Nat.mul_zero,
    Nat.zero_add] using runs_canonical_block .data σ w hfit hw hi hc hs hd

theorem runs_hash (σ : TapeStore) (w : List Bool) (hfit : InputFits w)
    (hw : σ TapeRegister.input = w)
    (hi : σ TapeRegister.temp0 =
      List.replicate (hashOffset (dataDimension w.length)) true)
    (hc : σ TapeRegister.temp1 =
      List.replicate (hashBlockLength (dataDimension w.length)) true)
    (hs : σ TapeRegister.temp2 = []) (hd : σ TapeRegister.keyBits = []) :
    RunsIn (canonicalProgram .hash).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update (Function.update σ TapeRegister.temp1 [])
        TapeRegister.keyBits (inputBlockData w .hash))))
      (hashBlockLength (dataDimension w.length) *
        (2 * hashOffset (dataDimension w.length) +
          hashBlockLength (dataDimension w.length) + 27) + 12) :=
  runs_canonical_block .hash σ w hfit hw hi hc hs hd

theorem runs_polynomial (σ : TapeStore) (w : List Bool) (hfit : InputFits w)
    (hw : σ TapeRegister.input = w)
    (hi : σ TapeRegister.temp0 =
      List.replicate (polynomialOffset (dataDimension w.length)) true)
    (hc : σ TapeRegister.temp1 =
      List.replicate (hashDimension (dataDimension w.length)) true)
    (hs : σ TapeRegister.temp2 = []) (hd : σ TapeRegister.polyBits = []) :
    RunsIn (canonicalProgram .polynomial).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update (Function.update σ TapeRegister.temp1 [])
        TapeRegister.polyBits (inputBlockData w .polynomial))))
      (hashDimension (dataDimension w.length) *
        (2 * polynomialOffset (dataDimension w.length) +
          hashDimension (dataDimension w.length) + 27) + 12) :=
  runs_canonical_block .polynomial σ w hfit hw hi hc hs hd

theorem runs_coefficients (σ : TapeStore) (w : List Bool) (hfit : InputFits w)
    (hw : σ TapeRegister.input = w)
    (hi : σ TapeRegister.temp0 =
      List.replicate (coefficientsOffset (dataDimension w.length)) true)
    (hc : σ TapeRegister.temp1 = List.replicate
      (independenceOrder (dataDimension w.length) * hashDimension (dataDimension w.length)) true)
    (hs : σ TapeRegister.temp2 = []) (hd : σ TapeRegister.coeffBits = []) :
    RunsIn (canonicalProgram .coefficients).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update (Function.update σ TapeRegister.temp1 [])
        TapeRegister.coeffBits (inputBlockData w .coefficients))))
      ((independenceOrder (dataDimension w.length) * hashDimension (dataDimension w.length)) *
        (2 * coefficientsOffset (dataDimension w.length) +
          independenceOrder (dataDimension w.length) * hashDimension (dataDimension w.length) +
          27) + 12) :=
  runs_canonical_block .coefficients σ w hfit hw hi hc hs hd

end TapeInputBlocks
end DepthThreeLowerBound

end Complexity
