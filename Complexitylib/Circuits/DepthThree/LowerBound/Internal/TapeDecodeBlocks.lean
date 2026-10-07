/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeDecodeBlock

/-!
# Unrestricted depth-three lower bound: tape decode blocks

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeDecodeBlocks.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeDecodeBlocks

open TapeMultiProgram TapeRouting

/-- Control states for the tail stage of the decode blocks routine. -/
abbrev TailState := TapeDecodeBlock.State .polynomial ⊕ TapeDecodeBlock.State .coefficients

/-- Transition function for the tail stage of the decode blocks routine. -/
def tailProgram : TapeMultiProgram TailState :=
  joinCode (TapeDecodeBlock.program .polynomial) (TapeDecodeBlock.program .coefficients)
    (fun _ => TapeDecodeBlock.start .coefficients)

/-- Initial control state of the tail stage of the decode blocks routine. -/
def tailStart : TailState := .inl (TapeDecodeBlock.start .polynomial)
/-- Terminal control state of the tail stage of the decode blocks routine. -/
def tailDone : TailState := .inr (TapeDecodeBlock.done .coefficients)

/-- Control states for the rest stage of the decode blocks routine. -/
abbrev RestState := TapeDecodeBlock.State .hash ⊕ TailState

/-- Transition function for the rest stage of the decode blocks routine. -/
def restProgram : TapeMultiProgram RestState :=
  joinCode (TapeDecodeBlock.program .hash) tailProgram (fun _ => tailStart)

/-- Initial control state of the rest stage of the decode blocks routine. -/
def restStart : RestState := .inl (TapeDecodeBlock.start .hash)
/-- Terminal control state of the rest stage of the decode blocks routine. -/
def restDone : RestState := .inr tailDone

/-- Control states of the decode blocks routine. -/
abbrev State := TapeDecodeBlock.State .data ⊕ RestState

/-- Transition function of the decode blocks routine. -/
def program : TapeMultiProgram State :=
  joinCode (TapeDecodeBlock.program .data) restProgram (fun _ => restStart)

/-- Initial control state of the decode blocks routine. -/
def start : State := .inl (TapeDecodeBlock.start .data)
/-- Terminal control state of the decode blocks routine. -/
def done : State := .inr restDone

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

/-- Tape-store contents at the output stage of the decode blocks routine. -/
def outputStore (σ : TapeStore) (w : List Bool) : TapeStore :=
  TapeDecodeBlock.outputStore
    (TapeDecodeBlock.outputStore
      (TapeDecodeBlock.outputStore (TapeDecodeBlock.outputStore σ w .data) w .hash)
      w .polynomial) w .coefficients

@[simp] theorem outputStore_block (σ : TapeStore) (w : List Bool) (kind : InputBlockKind) :
    outputStore σ w (TapeInputBlocks.outputRegister kind) = inputBlockData w kind := by
  cases kind <;> simp [outputStore, TapeDecodeBlock.outputStore,
    TapeInputBlocks.outputRegister, TapeRegister.dataBits, TapeRegister.keyBits,
    TapeRegister.polyBits, TapeRegister.coeffBits]

theorem outputStore_other (σ : TapeStore) (w : List Bool) (q : TapeRegister)
    (h15 : q ≠ 15) (h16 : q ≠ 16) (h17 : q ≠ 17) (h18 : q ≠ 18) :
    outputStore σ w q = σ q := by
  simp [outputStore, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
    TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
    TapeRegister.coeffBits, Function.update, h15, h16, h17, h18]

theorem runs_decode (σ : TapeStore) (w : List Bool)
    (hfit : InputFits w) (hw : σ TapeRegister.input = w)
    (hd : σ 2 = List.replicate (dataDimension w.length) true)
    (hr : σ 3 = List.replicate (hashDimension (dataDimension w.length)) true)
    (ht : σ 4 = List.replicate (independenceOrder (dataDimension w.length)) true)
    (h29 : σ 29 = []) (h30 : σ 30 = []) (h31 : σ 31 = [])
    (h5 : σ 5 = []) (h6 : σ 6 = []) (h7 : σ 7 = [])
    (h15 : σ 15 = []) (h16 : σ 16 = []) (h17 : σ 17 = []) (h18 : σ 18 = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (outputStore σ w))) (804 * (w.length + 1) ^ 2) := by
  let σ1 := TapeDecodeBlock.outputStore σ w .data
  let σ2 := TapeDecodeBlock.outputStore σ1 w .hash
  let σ3 := TapeDecodeBlock.outputStore σ2 w .polynomial
  have h0 := TapeDecodeBlock.runs_block σ w .data hfit hw hd hr ht
    h29 h30 h31 h5 h6 h7 h15
  have h1 := TapeDecodeBlock.runs_block σ1 w .hash hfit
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using hw)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using hd)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using hr)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using ht)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h29)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h30)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h31)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h5)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h6)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h7)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h16)
  have h2 := TapeDecodeBlock.runs_block σ2 w .polynomial hfit
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using hw)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using hd)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using hr)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using ht)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h29)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h30)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h31)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h5)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h6)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h7)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h17)
  have h3 := TapeDecodeBlock.runs_block σ3 w .coefficients hfit
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using hw)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using hd)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using hr)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using ht)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h29)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h30)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h31)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h5)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h6)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h7)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
      TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
      TapeRegister.coeffBits] using h18)
  have htail := join_runs (TapeDecodeBlock.program .polynomial)
    (TapeDecodeBlock.program .coefficients) (fun _ => TapeDecodeBlock.start .coefficients)
    h2 (by simp) h3
  have hrest := join_runs (TapeDecodeBlock.program .hash) tailProgram
    (fun _ => tailStart) h1 (by simp) htail
  have hall := join_runs (TapeDecodeBlock.program .data) restProgram
    (fun _ => restStart) h0 (by simp) hrest
  apply hall.mono
  have hpos : 1 ≤ (w.length + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos _)
  omega

end TapeDecodeBlocks
end DepthThreeLowerBound

end Complexity
