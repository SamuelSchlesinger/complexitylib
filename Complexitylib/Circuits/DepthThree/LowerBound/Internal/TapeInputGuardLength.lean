/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeCopyAdd
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeMultiply
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageParameters
public import Mathlib.Tactic.Ring

/-!
# Unrestricted depth-three lower bound: tape input guard length

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeInputGuardLength.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeInputGuard

open TapeMultiProgram TapeRouting TapeUnary TapeCopy

/-- Total input length needed for the chosen data, hash, modulus, and coefficient blocks. -/
def requiredLength (d r t : ℕ) : ℕ := d + (d + r - 1) + r + t * r

theorem requiredLength_parameters (d : ℕ) :
    requiredLength d (hashDimension d) (independenceOrder d) = blockLen d := rfl

/-- Tape-store contents at the output stage of the input guard length routine. -/
def outputStore (σ : TapeStore) (d r t : ℕ) : TapeStore :=
  Function.update σ 8 (List.replicate (requiredLength d r t) true)

@[simp] theorem outputStore_length (σ : TapeStore) (d r t : ℕ) :
    outputStore σ d r t 8 = List.replicate (requiredLength d r t) true := by
  simp [outputStore]

theorem outputStore_other (σ : TapeStore) (d r t : ℕ) (q : TapeRegister)
    (hq : q ≠ 8) : outputStore σ d r t q = σ q := by
  simp [outputStore, Function.update, hq]

/-- Control states for the product stage of the input guard length routine. -/
abbrev ProductState := TapeCopy.State ⊕ TapeMultiply.State

/-- Transition function for the product stage of the input guard length routine. -/
def productProgram : TapeMultiProgram ProductState :=
  joinCode (TapeCopy.code 4 5) (TapeMultiply.program 5 3 6 8)
    (fun _ => TapeMultiply.start)

/-- Initial control state of the product stage of the input guard length routine. -/
def productStart : ProductState := .inl .start
/-- Terminal control state of the product stage of the input guard length routine. -/
def productDone : ProductState := .inr TapeMultiply.done

theorem runs_product (σ : TapeStore) (t r z : ℕ)
    (h3 : σ 3 = List.replicate r true) (h4 : σ 4 = List.replicate t true)
    (h5 : σ 5 = []) (h6 : σ 6 = []) (h8 : σ 8 = List.replicate z true) :
    RunsIn productProgram.step (cfg productStart (storeTapes σ))
      (cfg productDone (storeTapes (Function.update σ 8 (List.replicate (z + t*r) true))))
      (t * (10*r + 14) + 2*t + 8) := by
  let τ := Function.update σ 5 (List.replicate t true)
  have hc := TapeStoreRuns.copy (src := 4) (dst := 5) (by decide) σ h5
  have hc' : RunsIn (TapeCopy.code 4 5).step (cfg TapeCopy.State.start (storeTapes σ))
      (cfg TapeCopy.State.done (storeTapes τ)) (2*t+4) := by
    simpa only [τ, h4, List.length_replicate] using hc
  have hin : TapeMultiply.tapes 5 3 6 8 (storeTapes σ) t r 0 z = storeTapes τ := by
    funext q
    by_cases hq5 : q = 5
    · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, τ, counterTape]
    · by_cases hq3 : q = 3
      · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, τ, counterTape, h3]
      · by_cases hq6 : q = 6
        · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, τ, counterTape, h6]
        · by_cases hq8 : q = 8
          · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, τ, counterTape, h8]
          · simp [TapeMultiply.tapes, onPair, storeTapes, τ, hq5, hq3, hq6, hq8]
  have hout : TapeMultiply.tapes 5 3 6 8 (storeTapes σ) 0 r 0 (z+t*r) =
      storeTapes (Function.update σ 8 (List.replicate (z+t*r) true)) := by
    funext q
    by_cases hq5 : q = 5
    · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, counterTape, h5]
    · by_cases hq3 : q = 3
      · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, counterTape, h3]
      · by_cases hq6 : q = 6
        · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, counterTape, h6]
        · by_cases hq8 : q = 8
          · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, counterTape]
          · simp [TapeMultiply.tapes, onPair, storeTapes, Function.update,
              hq5, hq3, hq6, hq8]
  have hm := TapeMultiply.runs_mul (outer := 5) (source := 3) (scratch := 6)
    (destination := 8) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (storeTapes σ) t r z
  rw [hin, hout] at hm
  have h := join_runs (TapeCopy.code 4 5) (TapeMultiply.program 5 3 6 8)
    (fun _ => TapeMultiply.start) hc' rfl hm
  have ht : (2*t+4)+1+(t*(10*r+14)+3) = t*(10*r+14)+2*t+8 := by omega
  simpa only [productProgram, productStart, productDone, ht] using h

/-- Control states for the ring sum stage of the input guard length routine. -/
abbrev RingSumState := TapeCopyAdd.State ⊕ TapeCopyAdd.State
/-- Transition function for the ring sum stage of the input guard length routine. -/
def ringSumProgram : TapeMultiProgram RingSumState :=
  joinCode (TapeCopyAdd.program 3 5 8) (TapeCopyAdd.program 3 5 8)
    (fun _ => TapeCopyAdd.start)
/-- Initial control state of the ring sum stage of the input guard length routine. -/
def ringSumStart : RingSumState := .inl TapeCopyAdd.start
/-- Terminal control state of the ring sum stage of the input guard length routine. -/
def ringSumDone : RingSumState := .inr TapeCopyAdd.done

/-- Control states for the add sum stage of the input guard length routine. -/
abbrev AddSumState := TapeCopyAdd.State ⊕ RingSumState
/-- Transition function for the add sum stage of the input guard length routine. -/
def addSumProgram : TapeMultiProgram AddSumState :=
  joinCode (TapeCopyAdd.program 2 5 8) ringSumProgram (fun _ => ringSumStart)
/-- Initial control state of the add sum stage of the input guard length routine. -/
def addSumStart : AddSumState := .inl TapeCopyAdd.start
/-- Terminal control state of the add sum stage of the input guard length routine. -/
def addSumDone : AddSumState := .inr ringSumDone

/-- Control states for the sum stage of the input guard length routine. -/
abbrev SumState := TapeCopy.State ⊕ AddSumState
/-- Transition function for the sum stage of the input guard length routine. -/
def sumProgram : TapeMultiProgram SumState :=
  joinCode (TapeCopy.code 2 8) addSumProgram (fun _ => addSumStart)
/-- Initial control state of the sum stage of the input guard length routine. -/
def sumStart : SumState := .inl .start
/-- Terminal control state of the sum stage of the input guard length routine. -/
def sumDone : SumState := .inr addSumDone

theorem runs_sum (σ : TapeStore) (d r : ℕ)
    (h2 : σ 2 = List.replicate d true) (h3 : σ 3 = List.replicate r true)
    (h5 : σ 5 = []) (h8 : σ 8 = []) :
    RunsIn sumProgram.step (cfg sumStart (storeTapes σ))
      (cfg sumDone (storeTapes (Function.update σ 8 (List.replicate (d+d+r+r) true))))
      (12*d+20*r+31) := by
  let σ1 := Function.update σ 8 (List.replicate d true)
  let σ2 := Function.update σ 8 (List.replicate (d+d) true)
  let σ3 := Function.update σ 8 (List.replicate (d+d+r) true)
  have hc := TapeStoreRuns.copy (src := 2) (dst := 8) (by decide) σ h8
  have hc' : RunsIn (TapeCopy.code 2 8).step (cfg TapeCopy.State.start (storeTapes σ))
      (cfg TapeCopy.State.done (storeTapes σ1)) (2*d+4) := by
    simpa only [σ1, h2, List.length_replicate] using hc
  have ha := TapeCopyAdd.runs_add (src := 2) (scratch := 5) (dst := 8)
    (by decide) (by decide) σ1 d d (by simp [σ1, h2]) (by simp [σ1]) (by simp [σ1, h5])
  have ha' : RunsIn (TapeCopyAdd.program 2 5 8).step
      (cfg TapeCopyAdd.start (storeTapes σ1)) (cfg TapeCopyAdd.done (storeTapes σ2))
      (10*d+8) := by simpa only [σ1, σ2, Function.update_idem] using ha
  have hb := TapeCopyAdd.runs_add (src := 3) (scratch := 5) (dst := 8)
    (by decide) (by decide) σ2 r (d+d) (by simp [σ2, h3]) (by simp [σ2])
    (by simp [σ2, h5])
  have hb' : RunsIn (TapeCopyAdd.program 3 5 8).step
      (cfg TapeCopyAdd.start (storeTapes σ2)) (cfg TapeCopyAdd.done (storeTapes σ3))
      (10*r+8) := by simpa only [σ2, σ3, Function.update_idem] using hb
  have he := TapeCopyAdd.runs_add (src := 3) (scratch := 5) (dst := 8)
    (by decide) (by decide) σ3 r (d+d+r) (by simp [σ3, h3]) (by simp [σ3])
    (by simp [σ3, h5])
  simp only [σ3, Function.update_idem] at he
  have hr := join_runs (TapeCopyAdd.program 3 5 8) (TapeCopyAdd.program 3 5 8)
    (fun _ => TapeCopyAdd.start) hb' rfl he
  have hd := join_runs (TapeCopyAdd.program 2 5 8) ringSumProgram
    (fun _ => ringSumStart) ha' rfl hr
  have h := join_runs (TapeCopy.code 2 8) addSumProgram
    (fun _ => addSumStart) hc' rfl hd
  have ht : (2*d+4)+1+((10*d+8)+1+((10*r+8)+1+(10*r+8))) =
      12*d+20*r+31 := by omega
  simpa only [sumProgram, sumStart, sumDone, addSumProgram, addSumStart, addSumDone,
    ringSumProgram, ringSumStart, ringSumDone, ht] using h

/-- Control states for the tail stage of the input guard length routine. -/
abbrev TailState := DecState ⊕ ProductState
/-- Transition function for the tail stage of the input guard length routine. -/
def tailProgram : TapeMultiProgram TailState :=
  joinCode (decProgram 8) productProgram (fun _ => productStart)
/-- Initial control state of the tail stage of the input guard length routine. -/
def tailStart : TailState := .inl .start
/-- Terminal control state of the tail stage of the input guard length routine. -/
def tailDone : TailState := .inr productDone

/-- Control states for the length stage of the input guard length routine. -/
abbrev LengthState := SumState ⊕ TailState
/-- Transition function for the length stage of the input guard length routine. -/
def lengthProgram : TapeMultiProgram LengthState :=
  joinCode sumProgram tailProgram (fun _ => tailStart)
/-- Initial control state of the length stage of the input guard length routine. -/
def lengthStart : LengthState := .inl sumStart
/-- Terminal control state of the length stage of the input guard length routine. -/
def lengthDone : LengthState := .inr tailDone

/-- Transition budget for the input guard length routine at its length stage. -/
def lengthCost (d r t : ℕ) : ℕ := 12*d+20*r+16*t+10*(t*r)+45

theorem runs_length (σ : TapeStore) (d r t : ℕ)
    (h2 : σ 2 = List.replicate d true) (h3 : σ 3 = List.replicate r true)
    (h4 : σ 4 = List.replicate t true) (h5 : σ 5 = []) (h6 : σ 6 = [])
    (h8 : σ 8 = []) :
    RunsIn lengthProgram.step (cfg lengthStart (storeTapes σ))
      (cfg lengthDone (storeTapes (outputStore σ d r t))) (lengthCost d r t) := by
  let z := d+d+r+r
  let σS := Function.update σ 8 (List.replicate z true)
  let σD := Function.update σ 8 (List.replicate (z-1) true)
  have hs := runs_sum σ d r h2 h3 h5 h8
  have hd := decrement 8 (storeTapes σS) z (by simp [σS, storeTapes, counterTape])
  have hd' : RunsIn (decProgram 8).step (cfg DecState.start (storeTapes σS))
      (cfg (DecState.done (decide (0 < z))) (storeTapes σD)) 4 := by
    simpa only [σS, σD, ← storeTapes_update, counterTape, Function.update_idem] using hd
  have hp := runs_product σD t r (z-1) (by simp [σD, h3]) (by simp [σD, h4])
    (by simp [σD, h5]) (by simp [σD, h6]) (by simp [σD])
  have hz : z-1 = d+(d+r-1)+r := by dsimp [z]; omega
  have ho : Function.update σD 8 (List.replicate (z-1+t*r) true) =
      outputStore σ d r t := by
    simp only [σD, Function.update_idem, outputStore, requiredLength, hz]
  rw [ho] at hp
  have htail := join_runs (decProgram 8) productProgram (fun _ => productStart) hd' rfl hp
  have h := join_runs sumProgram tailProgram (fun _ => tailStart) hs rfl htail
  have ht : (12*d+20*r+31)+1+(4+1+(t*(10*r+14)+2*t+8)) =
      lengthCost d r t := by unfold lengthCost; ring
  simpa only [lengthProgram, lengthStart, lengthDone, tailProgram, tailStart, tailDone,
    σS, z, ht] using h

@[simp] theorem lengthProgram_done (h : TapeHeads) : lengthProgram lengthDone h = none := rfl

end TapeInputGuard
end DepthThreeLowerBound

end Complexity
