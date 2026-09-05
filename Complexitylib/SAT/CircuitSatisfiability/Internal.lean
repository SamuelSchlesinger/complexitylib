/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.SAT.CircuitSatisfiability.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.NP
import Complexitylib.Classes.P.Cobham
import Complexitylib.Classes.P.Cobham.Internal.StringOps
import Complexitylib.Classes.P.DecisionFn
import Complexitylib.Classes.P.Pairing
import Complexitylib.Classes.PPoly.Uniform.Containment
import Complexitylib.Models.TuringMachine.Subroutines.PairValidate
import Complexitylib.SAT.Internal.LinearGuessVerify

/-!
# Padded circuit satisfiability -- proof internals
-/


public section

namespace Complexity

namespace CircuitSAT

theorem witness_pair_iff_internal (code ruler witness : List Bool) :
    Witness (pair code ruler) witness ↔
      witness.length = ruler.length ∧
        CircuitCode.evalFamilyCode code witness = some true := by
  simp [Witness, CircuitCode.circuitEvalLanguage]

theorem pair_mem_language_iff_internal (code ruler : List Bool) :
    pair code ruler ∈ language ↔
      ∃ witness, witness.length = ruler.length ∧
        CircuitCode.evalFamilyCode code witness = some true := by
  simp [language, witness_pair_iff_internal]

theorem witness_length_le_internal (query witness : List Bool)
    (h : Witness query witness) :
    witness.length ≤ query.length + 1 := by
  rw [h.2.1]
  exact (pairSnd_length_le query).trans (Nat.le_add_right _ _)

private def verifierRepack (input : List Bool) : List Bool :=
  pair (pairFst (pairFst input)) (pairSnd input)

private def verifierLengthFlag (input : List Bool) : List Bool :=
  Cobham.lenEqFlag (pairSnd (pairFst input)) (pairSnd input)

private def verifierLengthLanguage : Language :=
  {input | verifierLengthFlag input = [true]}

private theorem validPairEncoding_mem_P : validPairEncoding ∈ P := by
  refine Set.mem_iUnion.mpr ⟨1, 0, TM.pairValidateTM, (fun n => n + 2),
    TM.pairValidateTM_decidesInTime, ?_⟩
  refine BigO.add ?_ (BigO.const_le_pow 2 1)
  simpa using BigO.refl (fun n : ℕ => n)

private theorem verifierRepack_mem_FP : verifierRepack ∈ FP := by
  have hcode : (fun input => pairFst (pairFst input)) ∈ FP := by
    exact mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  exact mem_FP_pair hcode pairSnd_mem_FP

private theorem verifierLengthFlag_mem_FP : verifierLengthFlag ∈ FP := by
  have hleft : (fun input => pairSnd (pairFst input)) ∈ FP := by
    exact mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hright : (fun input => pairSnd input) ∈ FP := pairSnd_mem_FP
  have hleftCobham :
      Cobham (fun v : Fin 1 → List Bool => pairSnd (pairFst (v 0))) := by
    exact FP_subset_CobhamFP hleft
  have hrightCobham :
      Cobham (fun v : Fin 1 → List Bool => pairSnd (v 0)) := by
    exact FP_subset_CobhamFP hright
  apply CobhamFP_subset_FP
  exact Cobham.lenEqFlag_mem hleftCobham hrightCobham

private theorem verifierLengthLanguage_mem_P : verifierLengthLanguage ∈ P := by
  apply mem_P_of_decisionFn verifierLengthFlag_mem_FP
  intro input
  simp only [verifierLengthLanguage, Set.mem_ofPred_eq, verifierLengthFlag]
  constructor
  · intro h
    refine ⟨true, ?_, rfl⟩
    rw [h]
    simp
  · rintro ⟨bit, hbit, htrue⟩
    subst bit
    rcases Cobham.lenEqFlag_flag (pairSnd (pairFst input)) (pairSnd input) with
      hflag | hflag
    · exact hflag
    · rw [hflag] at hbit
      simp at hbit

private theorem pairLang_witness_eq :
    pairLang Witness =
      validPairEncoding ∩
        (pairFst ⁻¹' validPairEncoding ∩
          (verifierRepack ⁻¹' CircuitCode.circuitEvalLanguage ∩
            verifierLengthLanguage)) := by
  ext input
  constructor
  · rintro ⟨query, witness, rfl, hquery, hlength, heval⟩
    refine ⟨pair_mem_validPairEncoding query witness, ?_, ?_, ?_⟩
    · simpa using hquery
    · simpa [verifierRepack] using heval
    · change verifierLengthFlag (pair query witness) = [true]
      simpa [verifierLengthFlag] using
        (Cobham.lenEqFlag_eq_true_iff (pairSnd query) witness).2 hlength.symm
  · rintro ⟨houter, hquery, heval, hlength⟩
    obtain ⟨query, witness, rfl⟩ :=
      (mem_validPairEncoding_iff_exists_pair _).1 houter
    refine ⟨query, witness, rfl, ?_, ?_, ?_⟩
    · simpa using hquery
    · change verifierLengthFlag (pair query witness) = [true] at hlength
      have hlength' : (pairSnd query).length = witness.length := by
        exact (Cobham.lenEqFlag_eq_true_iff _ _).1 <| by
          simpa [verifierLengthFlag] using hlength
      exact hlength'.symm
    · simpa [verifierRepack] using heval

theorem pairLang_witness_mem_P_internal : pairLang Witness ∈ P := by
  rw [pairLang_witness_eq]
  exact P_inter validPairEncoding_mem_P <|
    P_inter (mem_P_preimage pairFst_mem_FP validPairEncoding_mem_P) <|
      P_inter
        (mem_P_preimage verifierRepack_mem_FP circuitEvalLanguage_mem_P)
        verifierLengthLanguage_mem_P

theorem language_mem_NP_internal : language ∈ NP :=
  SAT.language_mem_NP_of_linear_witness_verifierP_direct
    witness_length_le_internal (fun _ => Iff.rfl)
    pairLang_witness_mem_P_internal

theorem extensionWitness_pair_iff_internal
    (code fixedPrefix ruler witness : List Bool) :
    ExtensionWitness (pair code (pair fixedPrefix ruler)) witness ↔
      witness.length = ruler.length ∧
        CircuitCode.evalFamilyCode code (fixedPrefix ++ witness) = some true := by
  simp [ExtensionWitness, CircuitCode.circuitEvalLanguage]

theorem pair_mem_extensionLanguage_iff_internal
    (code fixedPrefix ruler : List Bool) :
    pair code (pair fixedPrefix ruler) ∈ extensionLanguage ↔
      ∃ witness, witness.length = ruler.length ∧
        CircuitCode.evalFamilyCode code (fixedPrefix ++ witness) = some true := by
  simp [extensionLanguage, extensionWitness_pair_iff_internal]

theorem extensionWitness_length_le_internal (query witness : List Bool)
    (h : ExtensionWitness query witness) :
    witness.length ≤ query.length + 1 := by
  rw [h.2.2.1]
  exact (pairSnd_length_le (pairSnd query)).trans <|
    (pairSnd_length_le query).trans (Nat.le_add_right _ _)

private def extensionVerifierRepack (input : List Bool) : List Bool :=
  pair (pairFst (pairFst input))
    (pairFst (pairSnd (pairFst input)) ++ pairSnd input)

private def extensionVerifierLengthFlag (input : List Bool) : List Bool :=
  Cobham.lenEqFlag (pairSnd (pairSnd (pairFst input))) (pairSnd input)

private def extensionVerifierLengthLanguage : Language :=
  {input | extensionVerifierLengthFlag input = [true]}

private theorem extensionVerifierRepack_mem_FP : extensionVerifierRepack ∈ FP := by
  have hquery : (fun input => pairFst input) ∈ FP := pairFst_mem_FP
  have hcode : (fun input => pairFst (pairFst input)) ∈ FP := by
    exact mem_FP_comp hquery pairFst_mem_FP
  have hpayload : (fun input => pairSnd (pairFst input)) ∈ FP := by
    exact mem_FP_comp hquery pairSnd_mem_FP
  have hprefix :
      (fun input => pairFst (pairSnd (pairFst input))) ∈ FP := by
    exact mem_FP_comp hpayload pairFst_mem_FP
  have hwitness : (fun input => pairSnd input) ∈ FP := pairSnd_mem_FP
  have hprefixCobham :
      Cobham (fun v : Fin 1 → List Bool =>
        pairFst (pairSnd (pairFst (v 0)))) := by
    exact FP_subset_CobhamFP hprefix
  have hwitnessCobham :
      Cobham (fun v : Fin 1 → List Bool => pairSnd (v 0)) := by
    exact FP_subset_CobhamFP hwitness
  have happend :
      (fun input => pairFst (pairSnd (pairFst input)) ++ pairSnd input) ∈ FP := by
    apply CobhamFP_subset_FP
    exact Cobham.appendFn hprefixCobham hwitnessCobham
  exact mem_FP_pair hcode happend

private theorem extensionVerifierLengthFlag_mem_FP :
    extensionVerifierLengthFlag ∈ FP := by
  have hquery : (fun input => pairFst input) ∈ FP := pairFst_mem_FP
  have hpayload : (fun input => pairSnd (pairFst input)) ∈ FP := by
    exact mem_FP_comp hquery pairSnd_mem_FP
  have hruler :
      (fun input => pairSnd (pairSnd (pairFst input))) ∈ FP := by
    exact mem_FP_comp hpayload pairSnd_mem_FP
  have hwitness : (fun input => pairSnd input) ∈ FP := pairSnd_mem_FP
  have hrulerCobham :
      Cobham (fun v : Fin 1 → List Bool =>
        pairSnd (pairSnd (pairFst (v 0)))) := by
    exact FP_subset_CobhamFP hruler
  have hwitnessCobham :
      Cobham (fun v : Fin 1 → List Bool => pairSnd (v 0)) := by
    exact FP_subset_CobhamFP hwitness
  apply CobhamFP_subset_FP
  exact Cobham.lenEqFlag_mem hrulerCobham hwitnessCobham

private theorem extensionVerifierLengthLanguage_mem_P :
    extensionVerifierLengthLanguage ∈ P := by
  apply mem_P_of_decisionFn extensionVerifierLengthFlag_mem_FP
  intro input
  simp only [extensionVerifierLengthLanguage, Set.mem_ofPred_eq,
    extensionVerifierLengthFlag]
  constructor
  · intro h
    refine ⟨true, ?_, rfl⟩
    rw [h]
    simp
  · rintro ⟨bit, hbit, htrue⟩
    subst bit
    rcases Cobham.lenEqFlag_flag
        (pairSnd (pairSnd (pairFst input))) (pairSnd input) with
      hflag | hflag
    · exact hflag
    · rw [hflag] at hbit
      simp at hbit

private theorem pairLang_extensionWitness_eq :
    pairLang ExtensionWitness =
      validPairEncoding ∩
        (pairFst ⁻¹' validPairEncoding ∩
          ((pairSnd ∘ pairFst) ⁻¹' validPairEncoding ∩
            (extensionVerifierRepack ⁻¹'
                CircuitCode.circuitEvalLanguage ∩
              extensionVerifierLengthLanguage))) := by
  ext input
  constructor
  · rintro ⟨query, witness, rfl, hquery, hpayload, hlength, heval⟩
    refine ⟨pair_mem_validPairEncoding query witness, ?_, ?_, ?_, ?_⟩
    · simpa using hquery
    · simpa using hpayload
    · simpa [extensionVerifierRepack] using heval
    · change extensionVerifierLengthFlag (pair query witness) = [true]
      simpa [extensionVerifierLengthFlag] using
        (Cobham.lenEqFlag_eq_true_iff (pairSnd (pairSnd query)) witness).2
          hlength.symm
  · rintro ⟨houter, hquery, hpayload, heval, hlength⟩
    obtain ⟨query, witness, rfl⟩ :=
      (mem_validPairEncoding_iff_exists_pair _).1 houter
    refine ⟨query, witness, rfl, ?_, ?_, ?_, ?_⟩
    · simpa using hquery
    · simpa using hpayload
    · change extensionVerifierLengthFlag (pair query witness) = [true] at hlength
      have hlength' : (pairSnd (pairSnd query)).length = witness.length := by
        exact (Cobham.lenEqFlag_eq_true_iff _ _).1 <| by
          simpa [extensionVerifierLengthFlag] using hlength
      exact hlength'.symm
    · simpa [extensionVerifierRepack] using heval

theorem pairLang_extensionWitness_mem_P_internal :
    pairLang ExtensionWitness ∈ P := by
  rw [pairLang_extensionWitness_eq]
  exact P_inter validPairEncoding_mem_P <|
    P_inter (mem_P_preimage pairFst_mem_FP validPairEncoding_mem_P) <|
      P_inter
        (mem_P_preimage
          (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
          validPairEncoding_mem_P) <|
        P_inter
          (mem_P_preimage extensionVerifierRepack_mem_FP
            circuitEvalLanguage_mem_P)
          extensionVerifierLengthLanguage_mem_P

theorem extensionLanguage_mem_NP_internal : extensionLanguage ∈ NP :=
  SAT.language_mem_NP_of_linear_witness_verifierP_direct
    extensionWitness_length_le_internal (fun _ => Iff.rfl)
    pairLang_extensionWitness_mem_P_internal

end CircuitSAT

end Complexity
