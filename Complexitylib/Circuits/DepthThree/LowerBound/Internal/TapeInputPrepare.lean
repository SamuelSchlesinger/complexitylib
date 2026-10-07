/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageInputBlockLists
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeCopyAdd
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeProductLength
public import Mathlib.Tactic.Linarith

/-!
# Unrestricted depth-three lower bound: tape input prepare

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeInputPrepare.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeInputPrepare

open TapeMultiProgram TapeRouting TapeUnary

/-- Control states for the sum minus stage of the input prepare routine. -/
abbrev SumMinusState := TapeCopy.State ⊕ (TapeCopyAdd.State ⊕ DecState)

/-- Transition function for the sum minus stage of the input prepare routine. -/
def sumMinusProgram (dst : TapeRegister) : TapeMultiProgram SumMinusState :=
  joinCode (TapeCopy.code 2 dst)
    (joinCode (TapeCopyAdd.program 3 31 dst) (decProgram dst) (fun _ => .start))
    (fun _ => .inl TapeCopyAdd.start)

/-- Initial control state of the sum minus stage of the input prepare routine. -/
def sumMinusStart : SumMinusState := .inl .start

/-- Terminal control state of the sum minus stage of the input prepare routine. -/
def sumMinusDone (d r : ℕ) : SumMinusState :=
  .inr (.inr (.done (decide (0 < d + r))))

@[simp] theorem sumMinusProgram_done (dst : TapeRegister) (d r : ℕ) (h : TapeHeads) :
    sumMinusProgram dst (sumMinusDone d r) h = none := rfl

private theorem runs_decrement (dst : TapeRegister) (σ : TapeStore) (n : ℕ)
    (hn : σ dst = List.replicate n true) :
    RunsIn (decProgram dst).step (cfg DecState.start (storeTapes σ))
      (cfg (.done (decide (0 < n)))
        (storeTapes (Function.update σ dst (List.replicate (n - 1) true)))) 4 := by
  have h := TapeUnary.decrement dst (storeTapes σ) n (by simp [storeTapes, hn, counterTape])
  simpa only [storeTapes_update, counterTape] using h

theorem runs_sumMinus {dst : TapeRegister}
    (h2 : (2 : TapeRegister) ≠ dst) (h3 : (3 : TapeRegister) ≠ dst)
    (h31 : (31 : TapeRegister) ≠ dst) (σ : TapeStore) (d r : ℕ)
    (hd : σ 2 = List.replicate d true) (hr : σ 3 = List.replicate r true)
    (he : σ dst = []) (hc : σ 31 = []) :
    RunsIn (sumMinusProgram dst).step (cfg sumMinusStart (storeTapes σ))
      (cfg (sumMinusDone d r)
        (storeTapes (Function.update σ dst (List.replicate (d + r - 1) true))))
      (2 * d + 10 * r + 18) := by
  let copied := Function.update σ dst (List.replicate d true)
  let added := Function.update σ dst (List.replicate (d + r) true)
  have hcopy := TapeStoreRuns.copy h2 σ he
  simp only [hd, List.length_replicate] at hcopy
  have hadd := TapeCopyAdd.runs_add (src := 3) (scratch := 31) (dst := dst)
    (by decide) h31 copied r d (by simp [copied, h3, hr])
    (by simp [copied]) (by simp [copied, h31, hc])
  have hadd' : RunsIn (TapeCopyAdd.program 3 31 dst).step
      (cfg TapeCopyAdd.start (storeTapes copied))
      (cfg TapeCopyAdd.done (storeTapes added)) (10 * r + 8) := by
    simpa only [copied, added, Function.update_idem] using hadd
  have hdec := runs_decrement dst added (d + r) (by simp [added])
  have hdec' : RunsIn (decProgram dst).step
      (cfg DecState.start (storeTapes added))
      (cfg (.done (decide (0 < d + r)))
        (storeTapes (Function.update σ dst (List.replicate (d + r - 1) true)))) 4 := by
    simpa only [added, Function.update_idem] using hdec
  have htail := join_runs (TapeCopyAdd.program 3 31 dst) (decProgram dst)
    (fun _ => DecState.start) hadd' rfl hdec'
  have h := join_runs (TapeCopy.code 2 dst)
    (joinCode (TapeCopyAdd.program 3 31 dst) (decProgram dst) (fun _ => DecState.start))
    (fun _ => .inl TapeCopyAdd.start) hcopy rfl htail
  have hcost : 2 * d + 4 + 1 + (10 * r + 8 + 1 + 4) =
      2 * d + 10 * r + 18 := by omega
  simpa only [sumMinusProgram, sumMinusStart, sumMinusDone, hcost] using h

/-- Control states for the offset stage of the input prepare routine. -/
abbrev OffsetState := SumMinusState ⊕ TapeCopyAdd.State

/-- Transition function for the offset stage of the input prepare routine. -/
def offsetProgram : TapeMultiProgram OffsetState :=
  joinCode (sumMinusProgram 29) (TapeCopyAdd.program 2 31 29)
    (fun _ => TapeCopyAdd.start)

/-- Initial control state of the offset stage of the input prepare routine. -/
def offsetStart : OffsetState := .inl sumMinusStart
/-- Terminal control state of the offset stage of the input prepare routine. -/
def offsetDone : OffsetState := .inr TapeCopyAdd.done

@[simp] theorem offsetProgram_done (h : TapeHeads) : offsetProgram offsetDone h = none := rfl

theorem runs_offset (σ : TapeStore) (d r : ℕ)
    (hd : σ 2 = List.replicate d true) (hr : σ 3 = List.replicate r true)
    (he : σ 29 = []) (hc : σ 31 = []) :
    RunsIn offsetProgram.step (cfg offsetStart (storeTapes σ))
      (cfg offsetDone
        (storeTapes (Function.update σ 29 (List.replicate (d + (d + r - 1)) true))))
      (12 * d + 10 * r + 27) := by
  let τ := Function.update σ 29 (List.replicate (d + r - 1) true)
  have hs := runs_sumMinus (dst := 29) (by decide) (by decide) (by decide)
    σ d r hd hr he hc
  have ha := TapeCopyAdd.runs_add (src := 2) (scratch := 31) (dst := 29)
    (by decide) (by decide) τ d (d + r - 1)
    (by simp [τ, hd]) (by simp [τ]) (by simp [τ, hc])
  have ha' : RunsIn (TapeCopyAdd.program 2 31 29).step
      (cfg TapeCopyAdd.start (storeTapes τ))
      (cfg TapeCopyAdd.done
        (storeTapes (Function.update σ 29 (List.replicate (d + (d + r - 1)) true))))
      (10 * d + 8) := by
    simpa only [τ, Function.update_idem, Nat.add_comm (d + r - 1) d] using ha
  have h := join_runs (sumMinusProgram 29) (TapeCopyAdd.program 2 31 29)
    (fun _ => TapeCopyAdd.start) hs rfl ha'
  have hcost : 2 * d + 10 * r + 18 + 1 + (10 * d + 8) =
      12 * d + 10 * r + 27 := by omega
  simpa only [offsetProgram, offsetStart, offsetDone, hcost] using h

/-- Transition function for the terminal stage of the input prepare routine. -/
def terminalProgram : TapeMultiProgram Unit := fun _ _ => none

/-- Control states for the hash stage of the input prepare routine. -/
abbrev HashState := TapeCopy.State ⊕ (SumMinusState ⊕ Unit)

/-- Transition function for the hash stage of the input prepare routine. -/
def hashProgram : TapeMultiProgram HashState :=
  joinCode (TapeCopy.code 2 29)
    (joinCode (sumMinusProgram 30) terminalProgram (fun _ => ()))
    (fun _ => .inl sumMinusStart)

/-- Initial control state of the hash stage of the input prepare routine. -/
def hashStart : HashState := .inl .start
/-- Terminal control state of the hash stage of the input prepare routine. -/
def hashDone : HashState := .inr (.inr ())

/-- Control states for the polynomial stage of the input prepare routine. -/
abbrev PolynomialState := OffsetState ⊕ TapeCopy.State

/-- Transition function for the polynomial stage of the input prepare routine. -/
def polynomialProgram : TapeMultiProgram PolynomialState :=
  joinCode offsetProgram (TapeCopy.code 3 30) (fun _ => TapeCopy.State.start)

/-- Initial control state of the polynomial stage of the input prepare routine. -/
def polynomialStart : PolynomialState := .inl offsetStart
/-- Terminal control state of the polynomial stage of the input prepare routine. -/
def polynomialDone : PolynomialState := .inr .done

/-- Control states for the coefficients stage of the input prepare routine. -/
abbrev CoefficientsState := OffsetState ⊕ (TapeCopyAdd.State ⊕ TapeProductLength.State)

/-- Transition function for the coefficients stage of the input prepare routine. -/
def coefficientsProgram : TapeMultiProgram CoefficientsState :=
  joinCode offsetProgram
    (joinCode (TapeCopyAdd.program 3 31 29) TapeProductLength.program
      (fun _ => TapeProductLength.start))
    (fun _ => .inl TapeCopyAdd.start)

/-- Initial control state of the coefficients stage of the input prepare routine. -/
def coefficientsStart : CoefficientsState := .inl offsetStart
/-- Terminal control state of the coefficients stage of the input prepare routine. -/
def coefficientsDone : CoefficientsState := .inr (.inr TapeProductLength.done)

/-- Control states of the input prepare routine. -/
def State : InputBlockKind → Type
  | .data => TapeCopy.State
  | .hash => HashState
  | .polynomial => PolynomialState
  | .coefficients => CoefficientsState

instance (kind : InputBlockKind) : Fintype (State kind) := by
  cases kind <;> dsimp [State] <;> infer_instance

/-- Transition function of the input prepare routine. -/
def program : (kind : InputBlockKind) → TapeMultiProgram (State kind)
  | .data => TapeCopy.code 2 30
  | .hash => hashProgram
  | .polynomial => polynomialProgram
  | .coefficients => coefficientsProgram

/-- Initial control state of the input prepare routine. -/
def start : (kind : InputBlockKind) → State kind
  | .data => .start
  | .hash => hashStart
  | .polynomial => polynomialStart
  | .coefficients => coefficientsStart

/-- Terminal control state of the input prepare routine. -/
def done : (kind : InputBlockKind) → State kind
  | .data => .done
  | .hash => hashDone
  | .polynomial => polynomialDone
  | .coefficients => coefficientsDone

/-- Tape-store contents at the output stage of the input prepare routine. -/
def outputStore (σ : TapeStore) (n : ℕ) (kind : InputBlockKind) : TapeStore :=
  Function.update
    (Function.update σ 29 (List.replicate (inputBlockOffset n kind) true))
    30 (List.replicate (inputBlockLength n kind) true)

@[simp] theorem outputStore_offset (σ : TapeStore) (n : ℕ) (kind : InputBlockKind) :
    outputStore σ n kind 29 = List.replicate (inputBlockOffset n kind) true := by
  simp [outputStore]

@[simp] theorem outputStore_length (σ : TapeStore) (n : ℕ) (kind : InputBlockKind) :
    outputStore σ n kind 30 = List.replicate (inputBlockLength n kind) true := by
  simp [outputStore]

theorem outputStore_other (σ : TapeStore) (n : ℕ) (kind : InputBlockKind)
    (s : TapeRegister) (h29 : s ≠ 29) (h30 : s ≠ 30) :
    outputStore σ n kind s = σ s := by
  simp [outputStore, Function.update, h29, h30]

/-- Transition budget for the input prepare routine. -/
def cost (n : ℕ) : InputBlockKind → ℕ :=
  let d := dataDimension n
  let r := hashDimension d
  let t := independenceOrder d
  fun kind => match kind with
    | .data => 2 * d + 4
    | .hash => 4 * d + 10 * r + 24
    | .polynomial => 12 * d + 12 * r + 32
    | .coefficients => 12 * d + 20 * r + 45 + t * (10 * r + 16)

private theorem runs_hash (σ : TapeStore) (d r : ℕ)
    (hd : σ 2 = List.replicate d true) (hr : σ 3 = List.replicate r true)
    (h29 : σ 29 = []) (h30 : σ 30 = []) (h31 : σ 31 = []) :
    RunsIn hashProgram.step (cfg hashStart (storeTapes σ))
      (cfg hashDone (storeTapes (Function.update
        (Function.update σ 29 (List.replicate d true))
        30 (List.replicate (d + r - 1) true)))) (4 * d + 10 * r + 24) := by
  let τ := Function.update σ 29 (List.replicate d true)
  have hc := TapeStoreRuns.copy (src := 2) (dst := 29) (by decide) σ h29
  simp only [hd, List.length_replicate] at hc
  have hs := runs_sumMinus (dst := 30) (by decide) (by decide) (by decide) τ d r
    (by simp [τ, hd]) (by simp [τ, hr]) (by simp [τ, h30]) (by simp [τ, h31])
  have hz := RunsIn.refl terminalProgram.step
    (cfg () (storeTapes (Function.update τ 30 (List.replicate (d + r - 1) true))))
  have htail := join_runs (sumMinusProgram 30) terminalProgram (fun _ => ()) hs rfl hz
  have h := join_runs (TapeCopy.code 2 29)
    (joinCode (sumMinusProgram 30) terminalProgram (fun _ => ()))
    (fun _ => .inl sumMinusStart) hc rfl htail
  have hcost : 2 * d + 4 + 1 + (2 * d + 10 * r + 18 + 1 + 0) =
      4 * d + 10 * r + 24 := by omega
  simpa only [hashProgram, hashStart, hashDone, τ, hcost] using h

private theorem runs_polynomial (σ : TapeStore) (d r : ℕ)
    (hd : σ 2 = List.replicate d true) (hr : σ 3 = List.replicate r true)
    (h29 : σ 29 = []) (h30 : σ 30 = []) (h31 : σ 31 = []) :
    RunsIn polynomialProgram.step (cfg polynomialStart (storeTapes σ))
      (cfg polynomialDone (storeTapes (Function.update
        (Function.update σ 29 (List.replicate (d + (d + r - 1)) true))
        30 (List.replicate r true)))) (12 * d + 12 * r + 32) := by
  let τ := Function.update σ 29 (List.replicate (d + (d + r - 1)) true)
  have ho := runs_offset σ d r hd hr h29 h31
  have hc := TapeStoreRuns.copy (src := 3) (dst := 30) (by decide) τ (by simp [τ, h30])
  have hs : τ 3 = List.replicate r true := by simp [τ, hr]
  simp only [hs, List.length_replicate] at hc
  have h := join_runs offsetProgram (TapeCopy.code 3 30)
    (fun _ => TapeCopy.State.start) ho rfl hc
  have hcost : 12 * d + 10 * r + 27 + 1 + (2 * r + 4) =
      12 * d + 12 * r + 32 := by omega
  simpa only [polynomialProgram, polynomialStart, polynomialDone, τ, hcost] using h

private theorem runs_coefficients (σ : TapeStore) (d r t : ℕ)
    (hd : σ 2 = List.replicate d true) (hr : σ 3 = List.replicate r true)
    (ht : σ 4 = List.replicate t true) (h29 : σ 29 = []) (h30 : σ 30 = [])
    (h31 : σ 31 = []) (h5 : σ 5 = []) (h6 : σ 6 = []) :
    RunsIn coefficientsProgram.step (cfg coefficientsStart (storeTapes σ))
      (cfg coefficientsDone (storeTapes (Function.update
        (Function.update σ 29 (List.replicate (d + (d + r - 1) + r) true))
        30 (List.replicate (t * r) true))))
      (12 * d + 20 * r + 45 + t * (10 * r + 16)) := by
  let τ := Function.update σ 29 (List.replicate (d + (d + r - 1)) true)
  let υ := Function.update σ 29 (List.replicate (d + (d + r - 1) + r) true)
  have ho := runs_offset σ d r hd hr h29 h31
  have ha := TapeCopyAdd.runs_add (src := 3) (scratch := 31) (dst := 29)
    (by decide) (by decide) τ r (d + (d + r - 1))
    (by simp [τ, hr]) (by simp [τ]) (by simp [τ, h31])
  have ha' : RunsIn (TapeCopyAdd.program 3 31 29).step
      (cfg TapeCopyAdd.start (storeTapes τ))
      (cfg TapeCopyAdd.done (storeTapes υ)) (10 * r + 8) := by
    simpa only [τ, υ, Function.update_idem] using ha
  have hp := TapeProductLength.runs_product υ t r (by simp [υ, ht])
    (by simp [υ, hr]) (by simp [υ, h5]) (by simp [υ, h6]) (by simp [υ, h30])
  have htail := join_runs (TapeCopyAdd.program 3 31 29) TapeProductLength.program
    (fun _ => TapeProductLength.start) ha' rfl hp
  have h := join_runs offsetProgram
    (joinCode (TapeCopyAdd.program 3 31 29) TapeProductLength.program
      (fun _ => TapeProductLength.start))
    (fun _ => .inl TapeCopyAdd.start) ho rfl htail
  have hcost : 12 * d + 10 * r + 27 + 1 + (10 * r + 8 + 1 +
      (t * (10 * r + 16) + 8)) = 12 * d + 20 * r + 45 + t * (10 * r + 16) := by omega
  simpa only [coefficientsProgram, coefficientsStart, coefficientsDone,
    TapeProductLength.outputStore, TapeProductLength.cost, υ, hcost] using h

theorem runs_prepare (σ : TapeStore) (n : ℕ) (kind : InputBlockKind)
    (hd : σ 2 = List.replicate (dataDimension n) true)
    (hr : σ 3 = List.replicate (hashDimension (dataDimension n)) true)
    (ht : σ 4 = List.replicate (independenceOrder (dataDimension n)) true)
    (h29 : σ 29 = []) (h30 : σ 30 = []) (h31 : σ 31 = [])
    (h5 : σ 5 = []) (h6 : σ 6 = []) (_h7 : σ 7 = []) :
    RunsIn (program kind).step (cfg (start kind) (storeTapes σ))
      (cfg (done kind) (storeTapes (outputStore σ n kind))) (cost n kind) := by
  cases kind with
  | data =>
      have h := TapeStoreRuns.copy (src := 2) (dst := 30) (by decide) σ h30
      have he : Function.update σ 29 [] = σ := Function.update_eq_self_iff.mpr h29.symm
      simpa only [State, program, start, done, outputStore, inputBlockOffset, inputBlockLength,
        cost, List.replicate_zero, he, hd, List.length_replicate] using h
  | hash =>
      simpa only [State, program, start, done, outputStore, inputBlockOffset, inputBlockLength,
        hashOffset, hashBlockLength, cost] using
        runs_hash σ (dataDimension n) (hashDimension (dataDimension n)) hd hr h29 h30 h31
  | polynomial =>
      simpa only [State, program, start, done, outputStore, inputBlockOffset, inputBlockLength,
        polynomialOffset, hashOffset, hashBlockLength, cost] using
        runs_polynomial σ (dataDimension n) (hashDimension (dataDimension n)) hd hr h29 h30 h31
  | coefficients =>
      simpa only [State, program, start, done, outputStore, inputBlockOffset, inputBlockLength,
        coefficientsOffset, polynomialOffset, hashOffset, hashBlockLength, cost] using
        runs_coefficients σ (dataDimension n) (hashDimension (dataDimension n))
          (independenceOrder (dataDimension n)) hd hr ht h29 h30 h31 h5 h6

theorem cost_le (n : ℕ) (kind : InputBlockKind) : cost n kind ≤ 128 * (n + 1) ^ 2 := by
  have hd : dataDimension n ≤ n := Nat.div_le_self n 5
  have hr : hashDimension (dataDimension n) ≤ n :=
    Nat.le_trans (hashDimension_le (dataDimension n)) hd
  have ht : independenceOrder (dataDimension n) ≤ n :=
    Nat.le_trans (independenceOrder_le (dataDimension n)) hd
  have hp : independenceOrder (dataDimension n) *
      (10 * hashDimension (dataDimension n) + 16) ≤ n * (10 * n + 16) :=
    Nat.mul_le_mul ht (by omega)
  cases kind <;> dsimp [cost] <;> nlinarith

@[simp] theorem program_done (kind : InputBlockKind) (h : TapeHeads) :
    program kind (done kind) h = none := by
  cases kind <;> rfl

end TapeInputPrepare
end DepthThreeLowerBound

end Complexity
