/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Raw.Defs
public import Complexitylib.Metacomplexity.MCSP.Gap.Slice.Internal
import Complexitylib.Metacomplexity.MCSP.Internal
import Complexitylib.Metacomplexity.MCSP.Threshold.Internal

/-!
# Raw truth-table MCSP -- proof internals
-/


public section

namespace Complexity

namespace MCSP

theorem rawArity_eq_of_length_eq_pow_internal (bits : List Bool) {arity : ℕ}
    (hlength : bits.length = 2 ^ arity) :
    rawArity bits = arity := by
  rw [rawArity, hlength]
  exact Nat.log_pow (by omega) arity

theorem isRawTruthTable_iff_length_eq_pow_rawArity_internal (bits : List Bool) :
    IsRawTruthTable bits ↔ bits.length = 2 ^ rawArity bits := by
  constructor
  · rintro ⟨arity, hlength⟩
    rw [rawArity_eq_of_length_eq_pow_internal bits hlength]
    exact hlength
  · intro hlength
    exact ⟨rawArity bits, hlength⟩

theorem rawArity_tableBits_internal (inst : Instance) :
    rawArity inst.tableBits = inst.arity := by
  exact rawArity_eq_of_length_eq_pow_internal inst.tableBits
    (Instance.length_tableBits_internal inst)

theorem rawDecode?_tableBits_internal (threshold : ℕ → ℕ) (inst : Instance) :
    rawDecode? threshold inst.tableBits =
      some (inst.withThreshold (threshold inst.arity)) := by
  have harity := rawArity_tableBits_internal inst
  unfold rawDecode?
  rw [harity]
  simp only [Instance.length_tableBits_internal, dite_true]
  congr 1
  cases inst
  simp [Instance.withThreshold, Instance.tableBits]

theorem rawDecode?_eq_some_iff_internal
    (threshold : ℕ → ℕ) (bits : List Bool) (inst : Instance) :
    rawDecode? threshold bits = some inst ↔
      bits = inst.tableBits ∧ inst.threshold = threshold inst.arity := by
  constructor
  · intro hdecode
    unfold rawDecode? at hdecode
    dsimp only at hdecode
    split at hdecode
    · cases hdecode
      constructor
      · simp [Instance.tableBits]
      · rfl
    · simp at hdecode
  · rintro ⟨rfl, hthreshold⟩
    rw [rawDecode?_tableBits_internal]
    congr 1
    cases inst
    simp_all [Instance.withThreshold]

theorem rawDecode?_eq_none_iff_internal
    (threshold : ℕ → ℕ) (bits : List Bool) :
    rawDecode? threshold bits = none ↔ ¬ IsRawTruthTable bits := by
  rw [isRawTruthTable_iff_length_eq_pow_rawArity_internal]
  unfold rawDecode?
  dsimp only
  by_cases hlength : bits.length = 2 ^ rawArity bits <;> simp [hlength]

theorem rawToCanonical_tableBits_internal
    (threshold : ℕ → ℕ) (inst : Instance) :
    rawToCanonical threshold inst.tableBits =
      (inst.withThreshold (threshold inst.arity)).encode := by
  simp [rawToCanonical, rawDecode?_tableBits_internal]

theorem canonicalToRaw_encode_internal (inst : Instance) :
    canonicalToRaw inst.encode = inst.tableBits := by
  simp [canonicalToRaw, Instance.decode?_encode_internal]

theorem canonicalToRaw_rawToCanonical_internal
    (threshold : ℕ → ℕ) {bits : List Bool}
    (hraw : IsRawTruthTable bits) :
    canonicalToRaw (rawToCanonical threshold bits) = bits := by
  cases hdecode : rawDecode? threshold bits with
  | none =>
      have hnraw := (rawDecode?_eq_none_iff_internal threshold bits).mp hdecode
      exact (hnraw hraw).elim
  | some inst =>
      rw [show rawToCanonical threshold bits = inst.encode by
        simp [rawToCanonical, hdecode]]
      rw [canonicalToRaw_encode_internal]
      exact ((rawDecode?_eq_some_iff_internal threshold bits inst).mp hdecode).1.symm

theorem rawToCanonical_canonicalToRaw_encode_internal
    (threshold : ℕ → ℕ) (inst : Instance) :
    rawToCanonical threshold (canonicalToRaw inst.encode) =
      (inst.withThreshold (threshold inst.arity)).encode := by
  rw [canonicalToRaw_encode_internal, rawToCanonical_tableBits_internal]

theorem mem_rawAtThreshold_tableBits_iff_internal
    (threshold : ℕ → ℕ) (inst : Instance) :
    inst.tableBits ∈ rawAtThreshold threshold ↔
      inst.minimumSize ≤ threshold inst.arity := by
  simp only [rawAtThreshold, Set.mem_ofPred_eq,
    rawDecode?_tableBits_internal]
  rw [Instance.hasCircuitAtMost_iff_minimumSize_le_internal,
    Instance.minimumSize_withThreshold_internal]
  rfl

theorem mem_rawAtThreshold_iff_exists_internal
    (threshold : ℕ → ℕ) (bits : List Bool) :
    bits ∈ rawAtThreshold threshold ↔
      ∃ inst : Instance,
        bits = inst.tableBits ∧ inst.minimumSize ≤ threshold inst.arity := by
  constructor
  · intro hmem
    cases hdecode : rawDecode? threshold bits with
    | none => simp [rawAtThreshold, hdecode] at hmem
    | some inst =>
        have hsmall : inst.HasCircuitAtMost := by
          simpa [rawAtThreshold, hdecode] using hmem
        have hdescription :=
          (rawDecode?_eq_some_iff_internal threshold bits inst).mp hdecode
        refine ⟨inst, hdescription.1, ?_⟩
        have hminimum :=
          (Instance.hasCircuitAtMost_iff_minimumSize_le_internal inst).mp hsmall
        exact hminimum.trans_eq hdescription.2
  · rintro ⟨inst, rfl, hminimum⟩
    exact (mem_rawAtThreshold_tableBits_iff_internal threshold inst).mpr hminimum

end MCSP

namespace GapMCSP

theorem mem_rawSliceYesLanguage_tableBits_iff_internal
    (parameters : SliceParameters) (inst : MCSP.Instance) :
    inst.tableBits ∈ rawSliceYesLanguage parameters ↔
      inst.minimumSize ≤ parameters.yesThreshold inst.arity := by
  simpa [rawSliceYesLanguage] using
    MCSP.mem_rawAtThreshold_tableBits_iff_internal
      parameters.yesThreshold inst

theorem mem_rawSliceNoLanguage_tableBits_iff_internal
    (parameters : SliceParameters) (inst : MCSP.Instance) :
    inst.tableBits ∈ rawSliceNoLanguage parameters ↔
      parameters.noThreshold inst.arity < inst.minimumSize := by
  simp only [rawSliceNoLanguage, Set.mem_ofPred_eq,
    MCSP.rawDecode?_tableBits_internal]
  rw [MCSP.Instance.minimumSize_withThreshold_internal]
  rfl

theorem disjoint_rawSliceLanguages_internal
    (parameters : SliceParameters) (hgap : parameters.IsGap) :
    Disjoint (rawSliceYesLanguage parameters)
      (rawSliceNoLanguage parameters) := by
  apply Set.disjoint_left.mpr
  intro bits hyes hno
  cases hdecode : MCSP.rawDecode? parameters.yesThreshold bits with
  | none =>
      simp [rawSliceYesLanguage, MCSP.rawAtThreshold, hdecode] at hyes
  | some inst =>
      have hsmall : inst.HasCircuitAtMost := by
        simpa [rawSliceYesLanguage, MCSP.rawAtThreshold, hdecode] using hyes
      have hlarge : parameters.noThreshold inst.arity < inst.minimumSize := by
        simpa [rawSliceNoLanguage, hdecode] using hno
      have hminimum :=
        (MCSP.Instance.hasCircuitAtMost_iff_minimumSize_le_internal inst).mp hsmall
      have hthreshold :=
        ((MCSP.rawDecode?_eq_some_iff_internal
          parameters.yesThreshold bits inst).mp hdecode).2
      have hminimum' : inst.minimumSize ≤ parameters.yesThreshold inst.arity :=
        hminimum.trans_eq hthreshold
      exact (Nat.not_lt_of_ge (hminimum'.trans (hgap inst.arity))) hlarge

theorem mem_rawSliceYesLanguage_imp_isRawTruthTable_internal
    (parameters : SliceParameters) {bits : List Bool}
    (hmem : bits ∈ rawSliceYesLanguage parameters) :
    MCSP.IsRawTruthTable bits := by
  cases hdecode : MCSP.rawDecode? parameters.yesThreshold bits with
  | none =>
      simp [rawSliceYesLanguage, MCSP.rawAtThreshold, hdecode] at hmem
  | some inst =>
      have hbits :=
        ((MCSP.rawDecode?_eq_some_iff_internal
          parameters.yesThreshold bits inst).mp hdecode).1
      refine ⟨inst.arity, ?_⟩
      rw [hbits]
      exact MCSP.Instance.length_tableBits_internal inst

theorem mem_rawSliceNoLanguage_imp_isRawTruthTable_internal
    (parameters : SliceParameters) {bits : List Bool}
    (hmem : bits ∈ rawSliceNoLanguage parameters) :
    MCSP.IsRawTruthTable bits := by
  cases hdecode : MCSP.rawDecode? parameters.yesThreshold bits with
  | none => simp [rawSliceNoLanguage, hdecode] at hmem
  | some inst =>
      have hbits :=
        ((MCSP.rawDecode?_eq_some_iff_internal
          parameters.yesThreshold bits inst).mp hdecode).1
      refine ⟨inst.arity, ?_⟩
      rw [hbits]
      exact MCSP.Instance.length_tableBits_internal inst

theorem rawSliceProblem_mapReducesVia_rawToCanonical_internal
    (parameters : SliceParameters) (hgap : parameters.IsGap) :
    (PromiseProblem.mk
      (rawSliceYesLanguage parameters)
      (rawSliceNoLanguage parameters)
      (disjoint_rawSliceLanguages_internal parameters hgap)).MapReducesVia
    (PromiseProblem.mk
      (sliceYesLanguage parameters)
      (sliceNoLanguage parameters)
      (disjoint_sliceLanguages_internal parameters hgap))
    (MCSP.rawToCanonical parameters.yesThreshold) := by
  constructor
  · intro bits hyes
    cases hdecode : MCSP.rawDecode? parameters.yesThreshold bits with
    | none =>
        simp [rawSliceYesLanguage, MCSP.rawAtThreshold, hdecode] at hyes
    | some inst =>
        have hsmall : inst.HasCircuitAtMost := by
          simpa [rawSliceYesLanguage, MCSP.rawAtThreshold, hdecode] using hyes
        have hdescription :=
          (MCSP.rawDecode?_eq_some_iff_internal
            parameters.yesThreshold bits inst).mp hdecode
        rw [show MCSP.rawToCanonical parameters.yesThreshold bits = inst.encode by
          simp [MCSP.rawToCanonical, hdecode]]
        exact (mem_sliceYesLanguage_encode_iff_internal parameters inst).mpr
          ⟨hdescription.2, hsmall⟩
  · intro bits hno
    cases hdecode : MCSP.rawDecode? parameters.yesThreshold bits with
    | none => simp [rawSliceNoLanguage, hdecode] at hno
    | some inst =>
        have hlarge : parameters.noThreshold inst.arity < inst.minimumSize := by
          simpa [rawSliceNoLanguage, hdecode] using hno
        have hdescription :=
          (MCSP.rawDecode?_eq_some_iff_internal
            parameters.yesThreshold bits inst).mp hdecode
        rw [show MCSP.rawToCanonical parameters.yesThreshold bits = inst.encode by
          simp [MCSP.rawToCanonical, hdecode]]
        exact (mem_sliceNoLanguage_encode_iff_internal parameters inst).mpr
          ⟨hdescription.2, hlarge⟩

theorem sliceProblem_mapReducesVia_canonicalToRaw_internal
    (parameters : SliceParameters) (hgap : parameters.IsGap) :
    (PromiseProblem.mk
      (sliceYesLanguage parameters)
      (sliceNoLanguage parameters)
      (disjoint_sliceLanguages_internal parameters hgap)).MapReducesVia
    (PromiseProblem.mk
      (rawSliceYesLanguage parameters)
      (rawSliceNoLanguage parameters)
      (disjoint_rawSliceLanguages_internal parameters hgap))
    MCSP.canonicalToRaw := by
  constructor
  · intro bits hyes
    cases hdecode : MCSP.Instance.decode? bits with
    | none => simp [sliceYesLanguage, MCSP.atThreshold, hdecode] at hyes
    | some inst =>
        have hyes' :
            inst.threshold = parameters.yesThreshold inst.arity ∧
              inst.HasCircuitAtMost := by
          simpa [sliceYesLanguage, MCSP.atThreshold, hdecode] using hyes
        rw [show MCSP.canonicalToRaw bits = inst.tableBits by
          simp [MCSP.canonicalToRaw, hdecode]]
        apply (mem_rawSliceYesLanguage_tableBits_iff_internal parameters inst).mpr
        have hminimum :=
          (MCSP.Instance.hasCircuitAtMost_iff_minimumSize_le_internal inst).mp
            hyes'.2
        exact hminimum.trans_eq hyes'.1
  · intro bits hno
    cases hdecode : MCSP.Instance.decode? bits with
    | none => simp [sliceNoLanguage, hdecode] at hno
    | some inst =>
        have hno' :
            inst.threshold = parameters.yesThreshold inst.arity ∧
              parameters.noThreshold inst.arity < inst.minimumSize := by
          simpa [sliceNoLanguage, hdecode] using hno
        rw [show MCSP.canonicalToRaw bits = inst.tableBits by
          simp [MCSP.canonicalToRaw, hdecode]]
        exact (mem_rawSliceNoLanguage_tableBits_iff_internal parameters inst).mpr
          hno'.2

end GapMCSP

end Complexity
