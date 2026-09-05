/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Normalization.Defs
import Complexitylib.Circuits.AndOrNot
import Complexitylib.Circuits.Dependency.Defs
import Complexitylib.Asymptotics.PolyBound
import Complexitylib.Classes.Pairing
import Complexitylib.Metacomplexity.MCSP.Internal
import Complexitylib.Metacomplexity.MCSP.Witness.Internal
import Mathlib.Tactic.Ring

/-!
# Threshold normalization for MCSP -- proof internals

The proof uses the library's explicit DNF circuit over unbounded AND/OR and its
verified gate-chain compilation to `Basis.andOr2`. The resulting coarse square
bound is sufficient to make canonical raw witnesses polynomial in truth-table
input length.
-/


public section

namespace Complexity

namespace MCSP

namespace Instance

theorem arity_le_tableLength_internal (arity : ℕ) : arity ≤ 2 ^ arity := by
  induction arity with
  | zero => simp
  | succ arity ih =>
      rw [pow_succ]
      have hpositive : 1 ≤ 2 ^ arity := Nat.one_le_two_pow
      omega

theorem exists_circuit_size_le_trivialCircuitSizeBound_internal (inst : Instance)
    [NeZero inst.arity] :
    ∃ (internalGates : ℕ)
        (circuit : Circuit Basis.andOr2 inst.arity 1 internalGates),
      circuit.size ≤ inst.trivialCircuitSizeBound ∧
        circuit.Computes inst.function := by
  let source := andOrNotFor inst.function
  let circuit := CompileAndOr.compileFn source
  refine ⟨_, circuit, ?_, ?_⟩
  · rw [trivialCircuitSizeBound, ite_eq_right (NeZero.ne inst.arity)]
    have hcompile := CompileAndOr.compileFn_size_le source
    have hfanIn := andOrNotFor_totalFanIn_le inst.function
    have hsourceSize : source.size = 2 ^ inst.arity + 1 := rfl
    have harity := arity_le_tableLength_internal inst.arity
    calc
      circuit.size ≤ source.totalFanIn + source.size + 1 := hcompile
      _ ≤ (inst.arity + 1) * 2 ^ inst.arity + (2 ^ inst.arity + 1) + 1 := by
        rw [hsourceSize]
        exact Nat.add_le_add_right
          (Nat.add_le_add_right hfanIn (2 ^ inst.arity + 1)) 1
      _ = (inst.arity + 2) * 2 ^ inst.arity + 2 := by ring
      _ ≤ (2 ^ inst.arity + 2) * 2 ^ inst.arity + 2 := by
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_right (2 ^ inst.arity) (Nat.add_le_add_right harity 2)) 2
      _ ≤ (2 ^ inst.arity + 2) * 2 ^ inst.arity +
          (2 ^ inst.arity + 2) * 2 := by omega
      _ = (2 ^ inst.arity + 2) ^ 2 := by ring
  · unfold Circuit.Computes
    funext input
    change (circuit.eval input) 0 = inst.function input
    rw [show circuit.eval = source.eval from CompileAndOr.compileFn_eval source]
    exact congrFun (andOrNotFor_eval inst.function) input

theorem hasCircuitAtMost_trivialCircuitSizeBound_internal (inst : Instance) :
    (inst.withThreshold inst.trivialCircuitSizeBound).HasCircuitAtMost := by
  by_cases harity : inst.arity = 0
  · simp [withThreshold, HasCircuitAtMost, harity]
  · let : NeZero inst.arity := ⟨harity⟩
    unfold HasCircuitAtMost withThreshold
    rw [dite_eq_right harity]
    exact exists_circuit_size_le_trivialCircuitSizeBound_internal inst

theorem effectiveThreshold_le_threshold_internal (inst : Instance) :
    inst.effectiveThreshold ≤ inst.threshold := by
  exact min_le_left _ _

theorem effectiveThreshold_le_trivialCircuitSizeBound_internal (inst : Instance) :
    inst.effectiveThreshold ≤ inst.trivialCircuitSizeBound := by
  exact min_le_right _ _

theorem hasCircuitAtMost_normalizeThreshold_iff_internal (inst : Instance) :
    inst.normalizeThreshold.HasCircuitAtMost ↔ inst.HasCircuitAtMost := by
  constructor
  · intro hnormalized
    apply hasCircuitAtMost_withThreshold_mono_internal inst
      (effectiveThreshold_le_threshold_internal inst)
    simpa [normalizeThreshold] using hnormalized
  · intro hsmall
    by_cases hthreshold : inst.threshold ≤ inst.trivialCircuitSizeBound
    · simp [normalizeThreshold, effectiveThreshold, min_eq_left hthreshold]
      exact hsmall
    · have hbound : inst.trivialCircuitSizeBound ≤ inst.threshold := by omega
      have htrivial := hasCircuitAtMost_trivialCircuitSizeBound_internal inst
      simpa [normalizeThreshold, effectiveThreshold, min_eq_right hbound] using htrivial

theorem trivialCircuitSizeBound_le_encodeLength_internal (inst : Instance) :
    inst.trivialCircuitSizeBound ≤ (inst.encode.length + 2) ^ 2 := by
  by_cases harity : inst.arity = 0
  · simp [trivialCircuitSizeBound, harity]
  · rw [trivialCircuitSizeBound, ite_eq_right harity]
    have htable : 2 ^ inst.arity ≤ inst.encode.length := by
      rw [length_encode_internal]
      omega
    have hadd := Nat.add_le_add_right htable 2
    simpa [pow_two] using Nat.mul_le_mul hadd hadd

theorem isRawCircuitWitness_normalizeThreshold_length_le_encode_internal
    (inst : Instance) {code : List Bool}
    (hwitness : inst.normalizeThreshold.IsRawCircuitWitness code) :
    code.length ≤ rawWitnessLengthPolynomial inst.encode.length := by
  apply (isRawCircuitWitness_length_le_internal inst.normalizeThreshold hwitness).trans
  have heffective :
      inst.effectiveThreshold ≤ (inst.encode.length + 2) ^ 2 :=
    (effectiveThreshold_le_trivialCircuitSizeBound_internal inst).trans
      (trivialCircuitSizeBound_le_encodeLength_internal inst)
  have harity : inst.arity ≤ inst.encode.length :=
    (arity_le_tableLength_internal inst.arity).trans (by
      rw [length_encode_internal]
      omega)
  have hfactor :
      2 * (inst.arity + inst.effectiveThreshold) + 6 ≤
        2 * (inst.encode.length + (inst.encode.length + 2) ^ 2) + 6 := by
    omega
  have hproduct := Nat.mul_le_mul heffective hfactor
  simpa [rawWitnessCodeLengthBound, rawWitnessLengthPolynomial,
    normalizeThreshold, withThreshold] using Nat.add_le_add_left hproduct 1

theorem rawWitnessLengthPolynomial_polyBound_internal :
    PolyBound rawWitnessLengthPolynomial := by
  let sizeBound : ℕ → ℕ := fun inputLength => (inputLength + 2) ^ 2
  have hsizeBound : PolyBound sizeBound :=
    (PolyBound.id.add (PolyBound.const 2)).pow 2
  have hfactor :
      PolyBound (fun inputLength =>
        2 * (inputLength + sizeBound inputLength) + 6) :=
    ((PolyBound.const 2).mul (PolyBound.id.add hsizeBound)).add
      (PolyBound.const 6)
  have htotal := (PolyBound.const 1).add (hsizeBound.mul hfactor)
  exact htotal

end Instance

theorem rawWitnessRelation_polyBalanced_internal :
    PolyBalanced RawWitnessRelation := by
  obtain ⟨polynomial, hpolynomial⟩ :=
    Instance.rawWitnessLengthPolynomial_polyBound_internal
  refine ⟨polynomial, ?_⟩
  intro bits witness hrelation
  cases hdecode : Instance.decode? bits with
  | none => simp [RawWitnessRelation, hdecode] at hrelation
  | some inst =>
      simp only [RawWitnessRelation, hdecode] at hrelation
      have hcanonical := (Instance.decode?_eq_some_iff_internal bits inst).mp hdecode
      rw [hcanonical]
      exact
        (Instance.isRawCircuitWitness_normalizeThreshold_length_le_encode_internal
          inst hrelation).trans (hpolynomial inst.encode.length)

theorem mem_MCSP_iff_exists_rawWitnessRelation_internal (bits : List Bool) :
    bits ∈ MCSP ↔ ∃ witness, RawWitnessRelation bits witness := by
  cases hdecode : Instance.decode? bits with
  | none => simp [MCSP, RawWitnessRelation, hdecode]
  | some inst =>
      simp only [MCSP, RawWitnessRelation, hdecode, Set.mem_ofPred_eq]
      rw [Instance.exists_isRawCircuitWitness_iff_internal,
        Instance.hasCircuitAtMost_normalizeThreshold_iff_internal]

namespace Instance

theorem exists_isRawCircuitWitness_length_le_encode_internal (inst : Instance)
    (hsmall : inst.HasCircuitAtMost) :
    ∃ code,
      inst.IsRawCircuitWitness code ∧
        code.length ≤ rawWitnessLengthPolynomial inst.encode.length := by
  have hnormalized : inst.normalizeThreshold.HasCircuitAtMost :=
    (hasCircuitAtMost_normalizeThreshold_iff_internal inst).mpr hsmall
  obtain ⟨code, hwitness⟩ :=
    (exists_isRawCircuitWitness_iff_internal inst.normalizeThreshold).mpr hnormalized
  have hwitnessCapped :
      (inst.withThreshold inst.effectiveThreshold).IsRawCircuitWitness code := by
    simpa [normalizeThreshold] using hwitness
  have hwitnessOriginal : inst.IsRawCircuitWitness code := by
    have hmono := isRawCircuitWitness_withThreshold_mono_internal inst
      (effectiveThreshold_le_threshold_internal inst) hwitnessCapped
    simpa [withThreshold] using hmono
  exact ⟨code, hwitnessOriginal,
    isRawCircuitWitness_normalizeThreshold_length_le_encode_internal inst hwitness⟩

end Instance

end MCSP

end Complexity
