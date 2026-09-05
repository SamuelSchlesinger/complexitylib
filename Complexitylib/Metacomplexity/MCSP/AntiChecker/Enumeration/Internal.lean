/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Enumeration.Defs
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Extraction.Internal
import Complexitylib.Metacomplexity.MCSP.Internal

/-!
# Finite circuit-code enumeration -- proof internals
-/


public section

namespace Complexity

namespace AntiChecker

theorem mem_codesOfLength_iff_internal {length : ℕ} {code : List Bool} :
    code ∈ codesOfLength length ↔ code.length = length := by
  rw [codesOfLength, Finset.mem_image]
  constructor
  · rintro ⟨bits, _, rfl⟩
    exact BitString.length_toList bits
  · intro hlength
    exact ⟨BitString.ofList code hlength, Finset.mem_univ _,
      BitString.toList_ofList code hlength⟩

theorem card_codesOfLength_internal (length : ℕ) :
    (codesOfLength length).card = 2 ^ length := by
  rw [codesOfLength,
    Finset.card_image_of_injective Finset.univ]
  · simp
  · intro first second heq
    exact BitString.toList_inj.mp heq

theorem mem_codesUpTo_iff_internal {bound : ℕ} {code : List Bool} :
    code ∈ codesUpTo bound ↔ code.length ≤ bound := by
  rw [codesUpTo, Finset.mem_biUnion]
  constructor
  · rintro ⟨length, hlength, hcode⟩
    rw [mem_codesOfLength_iff_internal] at hcode
    rw [hcode]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hlength)
  · intro hlength
    exact ⟨code.length, Finset.mem_range.mpr (by omega),
      mem_codesOfLength_iff_internal.mpr rfl⟩

theorem card_codesUpTo_le_internal (bound : ℕ) :
    (codesUpTo bound).card ≤ 2 ^ (bound + 1) := by
  have hsum : ∀ count : ℕ,
      (Finset.range count).sum (fun length => 2 ^ length) ≤
        2 ^ count := by
    intro count
    induction count with
    | zero => simp
    | succ count ih =>
        rw [Finset.sum_range_succ, pow_succ]
        omega
  calc
    (codesUpTo bound).card ≤
        ∑ length ∈ Finset.range (bound + 1),
          (codesOfLength length).card :=
      Finset.card_biUnion_le
    _ = (Finset.range (bound + 1)).sum
        (fun length => 2 ^ length) := by
      apply Finset.sum_congr rfl
      intro length _
      exact card_codesOfLength_internal length
    _ ≤ 2 ^ (bound + 1) := hsum (bound + 1)

theorem mem_candidateCodes_iff_internal {arity threshold : ℕ}
    {code : List Bool} :
    code ∈ candidateCodes arity threshold ↔
      code.length ≤ codeLengthBound arity threshold ∧
        IsSmallCircuitCode arity threshold code := by
  simp [candidateCodes, mem_codesUpTo_iff_internal]

theorem card_candidateCodes_le_internal (arity threshold : ℕ) :
    (candidateCodes arity threshold).card ≤
      2 ^ (codeLengthBound arity threshold + 1) := by
  exact (Finset.card_filter_le _ _).trans
    (card_codesUpTo_le_internal (codeLengthBound arity threshold))

theorem candidateCodes_coversThreshold_internal
    (arity threshold : ℕ) [NeZero arity] :
    CoversThreshold (arity := arity) threshold
      (candidateCodes arity threshold) := by
  intro internalGates circuit hsize
  rw [mem_candidateCodes_iff_internal]
  constructor
  · apply (CircuitCode.encodeCircuit_length_le_size circuit).trans
    unfold codeLengthBound
    gcongr
  · unfold IsSmallCircuitCode
    simp only [CircuitCode.encodeCircuit,
      CircuitCode.RawCircuit.decode?_encode]
    exact ⟨CircuitCode.RawCircuit.ofCircuit_wellFormed circuit,
      by simpa [Circuit.size] using hsize⟩

theorem candidateCodes_allFailSomewhere_internal {arity threshold : ℕ}
    [NeZero arity] (target : BitString arity → Bool)
    (hhard :
      ¬ (MCSP.Instance.ofFunction arity threshold target).HasCircuitAtMost) :
    AllFailSomewhere target (candidateCodes arity threshold) := by
  intro code hcode
  have hsmall := (mem_candidateCodes_iff_internal.mp hcode).2
  unfold IsSmallCircuitCode at hsmall
  cases hdecode : CircuitCode.RawCircuit.decode? code with
  | none => simp [hdecode] at hsmall
  | some circuit =>
      simp only [hdecode] at hsmall
      obtain ⟨hwell, hsize⟩ := hsmall
      by_contra hmissing
      apply hhard
      let : NeZero
          (MCSP.Instance.ofFunction arity threshold target).arity :=
        ⟨by exact NeZero.ne arity⟩
      apply (MCSP.Instance.hasCircuitAtMost_iff_sizeComplexity_le_internal
        (MCSP.Instance.ofFunction arity threshold target)).mpr
      have hcomputes :
          (circuit.toCircuit arity hwell).Computes target := by
        rw [Circuit.Computes]
        funext input
        have hagrees : CodeAgreesAt target code input := by
          by_contra hdisagrees
          exact hmissing ⟨input, hdisagrees⟩
        unfold CodeAgreesAt at hagrees
        simp [CircuitCode.evalCode, BitString.length_toList,
          hdecode] at hagrees
        have heval := CircuitCode.RawCircuit.eval?_toCircuit
          arity circuit hwell input
        rw [heval] at hagrees
        exact Option.some.inj hagrees
      have hminimum := Circuit.sizeComplexity_le
        (circuit.toCircuit arity hwell) target hcomputes
      have hcircuitSize :
          (circuit.toCircuit arity hwell).size ≤ threshold := by
        rw [CircuitCode.RawCircuit.size_toCircuit]
        exact hsize
      rw [MCSP.Instance.function_ofFunction_internal]
      exact hminimum.trans hcircuitSize

theorem exists_isFor_length_le_candidateCard_internal
    {arity threshold : ℕ} [NeZero arity]
    (target : BitString arity → Bool)
    (hhard :
      ¬ (MCSP.Instance.ofFunction arity threshold target).HasCircuitAtMost) :
    ∃ inputs : List (BitString arity),
      inputs.length ≤ (candidateCodes arity threshold).card ∧
        IsFor target threshold inputs := by
  exact exists_isFor_length_le_card_internal target
    (candidateCodes arity threshold)
    (candidateCodes_coversThreshold_internal arity threshold)
    (candidateCodes_allFailSomewhere_internal target hhard)

theorem exists_isFor_length_le_codeBound_internal
    {arity threshold : ℕ} [NeZero arity]
    (target : BitString arity → Bool)
    (hhard :
      ¬ (MCSP.Instance.ofFunction arity threshold target).HasCircuitAtMost) :
    ∃ inputs : List (BitString arity),
      inputs.length ≤ 2 ^ (codeLengthBound arity threshold + 1) ∧
        IsFor target threshold inputs := by
  obtain ⟨inputs, hlength, hanti⟩ :=
    exists_isFor_length_le_candidateCard_internal target hhard
  exact ⟨inputs,
    hlength.trans (card_candidateCodes_le_internal arity threshold), hanti⟩

end AntiChecker

end Complexity
