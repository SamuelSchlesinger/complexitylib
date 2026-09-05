/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Defs

/-!
# Minimum Circuit Size Problem -- proof internals

This module proves codec exactness and connects the direct existential MCSP
semantics to `Circuit.sizeComplexity` at every positive arity.
-/


public section

namespace Complexity

namespace MCSP

namespace Instance

theorem length_tableBits_internal (inst : Instance) :
    inst.tableBits.length = 2 ^ inst.arity := by
  simp [tableBits]

theorem inputIndex_inputOfIndex_internal {arity : ℕ} (index : Fin (2 ^ arity)) :
    inputIndex (inputOfIndex index) = index := by
  apply Fin.ext
  simp [inputIndex, inputOfIndex, Nat.fromBitsLE_toBitsLE index.isLt]

theorem inputOfIndex_inputIndex_internal {arity : ℕ} (input : BitString arity) :
    inputOfIndex (inputIndex input) = input := by
  rw [← BitString.toList_inj]
  simp only [inputOfIndex, inputIndex]
  erw [BitString.toList_ofList]
  calc
    Nat.toBitsLE arity (Nat.fromBitsLE input.toList) =
        Nat.toBitsLE input.toList.length (Nat.fromBitsLE input.toList) :=
      congrArg (fun width => Nat.toBitsLE width (Nat.fromBitsLE input.toList))
        (BitString.length_toList input).symm
    _ = input.toList := Nat.toBitsLE_fromBitsLE input.toList

theorem function_inputOfIndex_internal (inst : Instance)
    (index : Fin (2 ^ inst.arity)) :
    inst.function (inputOfIndex index) = inst.table index := by
  simp [function, inputIndex_inputOfIndex_internal]

theorem function_ofFunction_internal (arity threshold : ℕ)
    (f : BitString arity → Bool) :
    (ofFunction arity threshold f).function = f := by
  funext input
  simp only [function, ofFunction]
  exact congrArg f (inputOfIndex_inputIndex_internal input)

theorem function_withThreshold_internal (inst : Instance) (threshold : ℕ) :
    (inst.withThreshold threshold).function = inst.function := by
  rfl

theorem decode?_encode_internal (inst : Instance) :
    decode? inst.encode = some inst := by
  rcases inst with ⟨arity, table, threshold⟩
  simp [decode?, encode, tableBits]

theorem decode?_eq_some_iff_internal (bits : List Bool) (inst : Instance) :
    decode? bits = some inst ↔ bits = inst.encode := by
  constructor
  · intro hdecode
    cases houter : unpair? bits with
    | none => simp [decode?, houter] at hdecode
    | some outer =>
        rcases outer with ⟨arityBits, rest⟩
        cases hinner : unpair? rest with
        | none => simp [decode?, houter, hinner] at hdecode
        | some inner =>
            rcases inner with ⟨thresholdBits, tableBits⟩
            cases harity : BinaryNatCode.decode? arityBits with
            | none => simp [decode?, houter, hinner, harity] at hdecode
            | some arity =>
                cases hthreshold : BinaryNatCode.decode? thresholdBits with
                | none =>
                    simp [decode?, houter, hinner, harity, hthreshold] at hdecode
                | some threshold =>
                    by_cases htable : tableBits.length = 2 ^ arity
                    · have hbits := eq_pair_of_unpair?_eq_some houter
                      have hrest := eq_pair_of_unpair?_eq_some hinner
                      have harityCode :=
                        (BinaryNatCode.decode?_eq_some_iff arityBits arity).mp harity
                      have hthresholdCode :=
                        (BinaryNatCode.decode?_eq_some_iff thresholdBits threshold).mp
                          hthreshold
                      simp [decode?, houter, hinner, harity, hthreshold, htable] at hdecode
                      cases hdecode
                      calc
                        bits = pair arityBits rest := hbits
                        _ = pair arityBits (pair thresholdBits tableBits) := by rw [hrest]
                        _ = pair (BinaryNatCode.encode arity)
                            (pair (BinaryNatCode.encode threshold) tableBits) := by
                              rw [harityCode, hthresholdCode]
                        _ = encode
                            { arity
                              table := BitString.ofList tableBits htable
                              threshold } := by
                                simp [encode, MCSP.Instance.tableBits]
                    · simp [decode?, houter, hinner, harity, hthreshold, htable] at hdecode
  · rintro rfl
    exact decode?_encode_internal inst

/-- Internal characterization of every rejected MCSP code. -/
theorem decode?_eq_none_iff_internal (bits : List Bool) :
    decode? bits = none ↔ ¬ ∃ inst : Instance, bits = inst.encode := by
  constructor
  · intro hnone ⟨inst, hbits⟩
    rw [hbits, decode?_encode_internal] at hnone
    contradiction
  · intro hnoncanonical
    cases hdecode : decode? bits with
    | none => rfl
    | some inst =>
        exact (hnoncanonical
          ⟨inst, (decode?_eq_some_iff_internal bits inst).mp hdecode⟩).elim

theorem encode_injective_internal : Function.Injective encode := by
  intro first second hencode
  have hfirst := decode?_encode_internal first
  rw [hencode, decode?_encode_internal second] at hfirst
  exact Option.some.inj hfirst.symm

theorem length_encode_internal (inst : Instance) :
    inst.encode.length =
      2 ^ inst.arity + 2 * inst.arity.size +
        2 * inst.threshold.size + 4 := by
  simp [encode, BinaryNatCode.length_encode, length_tableBits_internal]
  omega

theorem minimumSize_of_arity_eq_zero_internal (inst : Instance)
    (harity : inst.arity = 0) :
    inst.minimumSize = 0 := by
  simp [minimumSize, harity]

theorem minimumSize_eq_sizeComplexity_internal (inst : Instance)
    [NeZero inst.arity] :
    inst.minimumSize =
      Circuit.sizeComplexity Basis.andOr2 inst.function := by
  simp [minimumSize, NeZero.ne inst.arity]

theorem hasCircuitAtMost_of_arity_eq_zero_internal (inst : Instance)
    (harity : inst.arity = 0) : inst.HasCircuitAtMost := by
  simp [HasCircuitAtMost, harity]

theorem hasCircuitAtMost_iff_sizeComplexity_le_internal (inst : Instance)
    [NeZero inst.arity] :
    inst.HasCircuitAtMost ↔
      Circuit.sizeComplexity Basis.andOr2 inst.function ≤ inst.threshold := by
  simp only [HasCircuitAtMost, NeZero.ne inst.arity, dite_false]
  constructor
  · rintro ⟨internalGates, circuit, hsize, hcomputes⟩
    exact (Circuit.sizeComplexity_le circuit inst.function hcomputes).trans hsize
  · intro hsize
    obtain ⟨internalGates, circuit, hminimum, hcomputes⟩ :=
      Circuit.sizeComplexity_witness (B := Basis.andOr2) inst.function
    refine ⟨internalGates, circuit, ?_, hcomputes⟩
    rw [hminimum]
    exact hsize

theorem hasCircuitAtMost_iff_minimumSize_le_internal (inst : Instance) :
    inst.HasCircuitAtMost ↔ inst.minimumSize ≤ inst.threshold := by
  by_cases harity : inst.arity = 0
  · simp [HasCircuitAtMost, minimumSize, harity]
  · let _ : NeZero inst.arity := ⟨harity⟩
    rw [hasCircuitAtMost_iff_sizeComplexity_le_internal,
      minimumSize_eq_sizeComplexity_internal]

theorem hasCircuitAtMost_withThreshold_mono_internal (inst : Instance)
    {first second : ℕ} (hthreshold : first ≤ second)
    (hsmall : (inst.withThreshold first).HasCircuitAtMost) :
    (inst.withThreshold second).HasCircuitAtMost := by
  by_cases harity : inst.arity = 0
  · simp [withThreshold, HasCircuitAtMost, harity]
  · unfold HasCircuitAtMost withThreshold at hsmall ⊢
    rw [dite_eq_right harity] at hsmall ⊢
    obtain ⟨internalGates, circuit, hsize, hcomputes⟩ := hsmall
    exact ⟨internalGates, circuit, hsize.trans hthreshold, hcomputes⟩

end Instance

end MCSP

end Complexity
