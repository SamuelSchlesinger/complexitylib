/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.ListDecoding.Defs
public import Complexitylib.Models.TuringMachine.Oracle.Universality.Defs
import Complexitylib.Metacomplexity.ListDecoding.Internal
import Complexitylib.Metacomplexity.Kolmogorov.Internal
import Complexitylib.Metacomplexity.Kolmogorov.Oracle.Internal
import Complexitylib.Models.TuringMachine.OutputSemantics.Internal
import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.CertificateSearch.Internal
import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.Encoding.Internal

/-!
# List decoding explicit NW reconstruction programs -- proof internals
-/


public section

namespace Complexity

namespace NWDesign

theorem IndexedReconstructionProgram.length_encodeBooleanPayload_internal
    {listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : IndexedReconstructionProgram design listSize) :
    program.encodeBooleanPayload.length =
      design.reconstructionDataBitsAt program.reconstruction.current +
        BooleanListCode.decoderIndexBitWidth listSize := by
  simp [IndexedReconstructionProgram.encodeBooleanPayload,
    Complexity.NWDesign.length_encodeBooleanPayload_internal,
    BooleanListCode.length_encodeDecoderIndex_internal]

theorem IndexedReconstructionProgram.length_encode_internal
    {listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : IndexedReconstructionProgram design listSize) :
    program.encode.length =
      1 + Fin.bitWidth outputLength +
        design.reconstructionDataBitsAt program.reconstruction.current +
          BooleanListCode.decoderIndexBitWidth listSize := by
  simp [IndexedReconstructionProgram.encode,
    IndexedReconstructionProgram.length_encodeBooleanPayload_internal]
  omega

theorem decodeIndexedReconstructionBooleanPayload?_encode_internal
    {listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : IndexedReconstructionProgram design listSize) :
    decodeIndexedReconstructionBooleanPayload? design listSize
      program.reconstruction.complement program.reconstruction.current
        program.encodeBooleanPayload = some program := by
  simp [decodeIndexedReconstructionBooleanPayload?,
    IndexedReconstructionProgram.encodeBooleanPayload,
    Complexity.NWDesign.length_encodeBooleanPayload_internal,
    decodeReconstructionBooleanPayload?_encode_internal,
    BooleanListCode.decodeDecoderIndex?_encodeDecoderIndex_internal]

theorem decodeIndexedReconstructionProgram?_encode_internal
    {listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : IndexedReconstructionProgram design listSize) :
    decodeIndexedReconstructionProgram? design listSize program.encode =
      some program := by
  simp [decodeIndexedReconstructionProgram?,
    IndexedReconstructionProgram.encode,
    decodeIndexedReconstructionBooleanPayload?_encode_internal]

theorem decodeIndexedMessage?_encode_internal
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : IndexedReconstructionProgram design listSize)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (test : Finset (Fin outputLength → Bool)) :
    decodeIndexedMessage? design code test program.encode =
      some (program.decodedMessage code test) := by
  simp [decodeIndexedMessage?,
    decodeIndexedReconstructionProgram?_encode_internal]

theorem HasEncodedMessageCertificateWithin.timeBoundedKolmogorovComplexity_le_internal
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    {test : Finset (Fin outputLength → Bool)}
    {message : Fin messageLength → Bool} {bound : ℕ}
    (realization : EncodedMessageDecoderRealization design code test)
    (hcertificate : HasEncodedMessageCertificateWithin
      design code test message bound) :
    realization.machine.timeBoundedKolmogorovComplexity
        (List.ofFn message) (realization.time bound) ≤
      (bound : WithTop ℕ) := by
  obtain ⟨description, hdecode, hlength⟩ := hcertificate
  have hproduce := realization.correct description message hdecode
  have hproduceBound := TM.producesInTime_mono_internal
    (realization.time_mono hlength) hproduce
  exact le_trans
    (TM.timeBoundedKolmogorovComplexity_le_internal hproduceBound)
    (by exact_mod_cast hlength)

namespace HasEncodedMessageCertificateWithin

theorem oracleTimeBoundedKolmogorovComplexity_le_internal
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    {test : Finset (Fin outputLength → Bool)}
    {message : Fin messageLength → Bool} {bound : ℕ}
    (realization : OracleEncodedMessageDecoderRealization design code)
    (hcertificate : HasEncodedMessageCertificateWithin
      design code test message bound) :
    realization.machine.timeBoundedKolmogorovComplexity
        (finiteTestOracle test) (List.ofFn message) (realization.time bound) ≤
      (bound : WithTop ℕ) := by
  obtain ⟨description, hdecode, hlength⟩ := hcertificate
  have hproduce := realization.correct test description message hdecode
  have hproduceBound := hproduce.mono (realization.time_mono hlength)
  exact le_trans
    (OracleTM.timeBoundedKolmogorovComplexity_le_internal hproduceBound)
    (by exact_mod_cast hlength)

end HasEncodedMessageCertificateWithin

namespace OracleEncodedMessageDecoderRealization

theorem efficientlyUniversal_transfer_internal
    {messageLength listSize outputLength inputLength seedLength
      universalTapes : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    (realization : OracleEncodedMessageDecoderRealization design code)
    (universal : OracleTM universalTapes)
    (huniversal : OracleTM.IsEfficientlyUniversal universal) :
    ∃ constant coefficient exponent,
      ∀ (test : Finset (Fin outputLength → Bool))
        (message : Fin messageLength → Bool) (bound : ℕ),
        HasEncodedMessageCertificateWithin design code test message bound →
          universal.timeBoundedKolmogorovComplexity
              (finiteTestOracle test) (List.ofFn message)
              (coefficient *
                (bound + realization.time bound + 1) ^ exponent) ≤
            (bound + constant : ℕ) := by
  obtain ⟨compile, constant, clock, -, _hsim, hlength, htimed, hclock⟩ :=
    huniversal realization.tapes realization.machine
  obtain ⟨coefficient, exponent, htransfer⟩ :=
    OracleTM.polynomialTimeOverhead_kolmogorov_transfer_internal
      htimed hlength hclock
  refine ⟨constant, coefficient, exponent, ?_⟩
  intro test message bound hcertificate
  exact htransfer (finiteTestOracle test) (List.ofFn message)
    (realization.time bound) bound
    (hcertificate.oracleTimeBoundedKolmogorovComplexity_le_internal
      realization)

end OracleEncodedMessageDecoderRealization

theorem EncodedMessageDecoderRealization.efficientlyUniversal_transfer_internal
    {messageLength listSize outputLength inputLength seedLength
      universalTapes : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    {test : Finset (Fin outputLength → Bool)}
    (realization : EncodedMessageDecoderRealization design code test)
    (universal : TM universalTapes)
    (huniversal : universal.IsEfficientlyUniversal) :
    ∃ constant coefficient exponent,
      ∀ (message : Fin messageLength → Bool) (bound : ℕ),
        HasEncodedMessageCertificateWithin design code test message bound →
          universal.timeBoundedKolmogorovComplexity (List.ofFn message)
              (coefficient *
                (bound + realization.time bound + 1) ^ exponent) ≤
            (bound + constant : ℕ) := by
  obtain ⟨compile, constant, clock, -, _hsim, hlength, htimed, hclock⟩ :=
    huniversal realization.tapes realization.machine
  obtain ⟨coefficient, exponent, htransfer⟩ :=
    TM.polynomialTimeOverhead_kolmogorov_transfer_internal
      htimed hlength hclock
  refine ⟨constant, coefficient, exponent, ?_⟩
  intro message bound hcertificate
  exact htransfer (List.ofFn message) (realization.time bound) bound
    (HasEncodedMessageCertificateWithin.timeBoundedKolmogorovComplexity_le_internal
      realization hcertificate)

theorem ReconstructionProgram.agreementProbability_eq_listCode_internal
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (message : Fin messageLength → Bool)
    (test : Finset (Fin outputLength → Bool)) :
    program.agreementProbability (code.encode message) test =
      BooleanListCode.agreementProbability (code.encode message)
        (program.predictor test) := by
  unfold ReconstructionProgram.agreementProbability
  unfold BooleanListCode.agreementProbability
  congr 1
  ext challenge
  simp [eq_comm]

theorem ReconstructionProgram.mem_listDecoderCandidates_and_card_le_internal
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (message : Fin messageLength → Bool)
    (test : Finset (Fin outputLength → Bool)) (margin : ℚ)
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (hagreement : 1 / 2 + margin ≤
      program.agreementProbability (code.encode message) test) :
    message ∈ program.listDecoderCandidates code test ∧
      (program.listDecoderCandidates code test).card ≤ listSize := by
  have hresult :=
    BooleanListCode.mem_candidates_and_card_le_of_half_add_margin_internal
      hcode message (program.predictor test) (by
        rwa [← program.agreementProbability_eq_listCode_internal])
  simpa [ReconstructionProgram.listDecoderCandidates] using hresult

theorem ReconstructionProgram.exists_indexedProgram_of_half_add_margin_internal
    {messageLength listSize outputLength inputLength seedLength : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    (program : design.ReconstructionProgram)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (message : Fin messageLength → Bool)
    (test : Finset (Fin outputLength → Bool)) (margin : ℚ)
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (hagreement : 1 / 2 + margin ≤
      program.agreementProbability (code.encode message) test) :
    ∃ indexed : IndexedReconstructionProgram design listSize,
      indexed.reconstruction = program ∧
        indexed.decodedMessage code test = message ∧
          indexed.encodeBooleanPayload.length =
            program.encodeBooleanPayload.length +
              BooleanListCode.decoderIndexBitWidth listSize := by
  have hcodeAgreement : 1 / 2 + margin ≤
      BooleanListCode.agreementProbability (code.encode message)
        (program.predictor test) := by
    rwa [← program.agreementProbability_eq_listCode_internal]
  have hradius : 1 - (1 / 2 - margin) ≤
      BooleanListCode.agreementProbability (code.encode message)
        (program.predictor test) := by
    convert hcodeAgreement using 1
    ring
  obtain ⟨index, hdecode⟩ :=
    BooleanListCode.exists_decoder_index_of_agreementProbability_ge_internal
      hcode message (program.predictor test) hradius
  refine ⟨{ reconstruction := program, decoderIndex := index }, rfl,
    hdecode, ?_⟩
  simp [IndexedReconstructionProgram.encodeBooleanPayload,
    BooleanListCode.length_encodeDecoderIndex_internal]

theorem findGoodReconstructionCertificate_indexedProgram_sound_internal
    {messageLength listSize outputLength inputLength seedLength trials budget : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (message : Fin messageLength → Bool)
    (test : Finset (Fin outputLength → Bool)) (margin : ℚ)
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (hbudget : design.HasOverlapBudget budget)
    (batch : Fin trials → ReconstructionTrial outputLength seedLength)
    (certificate : ReconstructionCertificate outputLength seedLength)
    (hfind : design.findGoodReconstructionCertificate? (code.encode message)
      test (1 / 2 + margin) batch = some certificate) :
    ∃ indexed : IndexedReconstructionProgram design listSize,
      indexed.reconstruction =
          certificate.toProgram design (code.encode message) ∧
        indexed.decodedMessage code test = message ∧
          indexed.encodeBooleanPayload.length ≤
            budget + (seedLength - inputLength) + 1 +
              BooleanListCode.decoderIndexBitWidth listSize := by
  obtain ⟨hagreement, hpayload⟩ :=
    findGoodReconstructionCertificate_encodedProgram_sound_internal design
      (code.encode message) test (1 / 2 + margin) hbudget batch
      certificate hfind
  obtain ⟨indexed, hreconstruction, hdecode, hlength⟩ :=
    (certificate.toProgram design
      (code.encode message)).exists_indexedProgram_of_half_add_margin_internal
        code message test margin hcode hagreement
  refine ⟨indexed, hreconstruction, hdecode, ?_⟩
  rw [hlength]
  exact Nat.add_le_add_right hpayload _

theorem findGoodReconstructionCertificate_fullyEncodedIndexedProgram_sound_internal
    {messageLength listSize outputLength inputLength seedLength trials budget : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (message : Fin messageLength → Bool)
    (test : Finset (Fin outputLength → Bool)) (margin : ℚ)
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (hbudget : design.HasOverlapBudget budget)
    (batch : Fin trials → ReconstructionTrial outputLength seedLength)
    (certificate : ReconstructionCertificate outputLength seedLength)
    (hfind : design.findGoodReconstructionCertificate? (code.encode message)
      test (1 / 2 + margin) batch = some certificate) :
    ∃ indexed : IndexedReconstructionProgram design listSize,
      indexed.reconstruction =
          certificate.toProgram design (code.encode message) ∧
        indexed.decodedMessage code test = message ∧
          indexed.encode.length ≤
            1 + Fin.bitWidth outputLength +
              (budget + (seedLength - inputLength) + 1) +
                BooleanListCode.decoderIndexBitWidth listSize := by
  obtain ⟨indexed, hreconstruction, hdecode, hpayload⟩ :=
    findGoodReconstructionCertificate_indexedProgram_sound_internal
      design code message test margin hcode hbudget batch certificate hfind
  refine ⟨indexed, hreconstruction, hdecode, ?_⟩
  simp only [IndexedReconstructionProgram.encode, List.length_cons,
    List.length_append, Fin.length_toBits]
  omega

theorem findGoodReconstructionCertificate_encodedMessage_sound_internal
    {messageLength listSize outputLength inputLength seedLength trials budget : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (message : Fin messageLength → Bool)
    (test : Finset (Fin outputLength → Bool)) (margin : ℚ)
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (hbudget : design.HasOverlapBudget budget)
    (batch : Fin trials → ReconstructionTrial outputLength seedLength)
    (certificate : ReconstructionCertificate outputLength seedLength)
    (hfind : design.findGoodReconstructionCertificate? (code.encode message)
      test (1 / 2 + margin) batch = some certificate) :
    ∃ description : List Bool,
      decodeIndexedMessage? design code test description = some message ∧
        description.length ≤
          1 + Fin.bitWidth outputLength +
            (budget + (seedLength - inputLength) + 1) +
              BooleanListCode.decoderIndexBitWidth listSize := by
  obtain ⟨indexed, _hreconstruction, hdecode, hlength⟩ :=
    findGoodReconstructionCertificate_fullyEncodedIndexedProgram_sound_internal
      design code message test margin hcode hbudget batch certificate hfind
  refine ⟨indexed.encode, ?_, hlength⟩
  rw [decodeIndexedMessage?_encode_internal, hdecode]

theorem findGoodReconstructionCertificate_listDecoding_sound_internal
    {messageLength listSize outputLength inputLength seedLength trials budget : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (code : BooleanListCode messageLength listSize (Fin inputLength → Bool))
    (message : Fin messageLength → Bool)
    (test : Finset (Fin outputLength → Bool)) (margin : ℚ)
    (hcode : code.IsListDecodableAt (1 / 2 - margin))
    (hbudget : design.HasOverlapBudget budget)
    (batch : Fin trials → ReconstructionTrial outputLength seedLength)
    (certificate : ReconstructionCertificate outputLength seedLength)
    (hfind : design.findGoodReconstructionCertificate? (code.encode message)
      test (1 / 2 + margin) batch = some certificate) :
    message ∈ (certificate.toProgram design
        (code.encode message)).listDecoderCandidates code test ∧
      ((certificate.toProgram design
        (code.encode message)).listDecoderCandidates code test).card ≤ listSize ∧
      (certificate.toProgram design
        (code.encode message)).encodeBooleanPayload.length ≤
          budget + (seedLength - inputLength) + 1 := by
  obtain ⟨hagreement, hpayload⟩ :=
    findGoodReconstructionCertificate_encodedProgram_sound_internal design
      (code.encode message) test (1 / 2 + margin) hbudget batch
      certificate hfind
  obtain ⟨hmessage, hcard⟩ :=
    (certificate.toProgram design
      (code.encode message)).mem_listDecoderCandidates_and_card_le_internal
        code message test margin hcode hagreement
  exact ⟨hmessage, hcard, hpayload⟩

theorem half_le_listDecodedReconstructionProgram_of_randomTest_internal
    {messageLength listSize outputLength inputLength seedLength tapes time
      threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hcode : code.IsListDecodableAt
      (1 / 2 - (density / (outputLength : ℚ)) / 2))
    (hlow : (design.generator (code.encode message)).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          (code.encode message) test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? (code.encode message) test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        message ∈ (certificate.toProgram design
            (code.encode message)).listDecoderCandidates code test ∧
          ((certificate.toProgram design
            (code.encode message)).listDecoderCandidates code test).card ≤ listSize ∧
          (certificate.toProgram design
            (code.encode message)).encodeBooleanPayload.length ≤
              budget + (seedLength - inputLength) + 1 := by
  obtain ⟨hhalf, _hselected⟩ :=
    half_le_encodedReconstructionProgram_of_randomTest_internal
      houtputLength hdensity hlow hrandom hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact findGoodReconstructionCertificate_listDecoding_sound_internal
    design code message test ((density / (outputLength : ℚ)) / 2)
      hcode hbudget batch certificate hfind

theorem half_le_indexedReconstructionProgram_of_randomTest_internal
    {messageLength listSize outputLength inputLength seedLength tapes time
      threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hcode : code.IsListDecodableAt
      (1 / 2 - (density / (outputLength : ℚ)) / 2))
    (hlow : (design.generator (code.encode message)).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          (code.encode message) test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? (code.encode message) test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        ∃ indexed : IndexedReconstructionProgram design listSize,
          indexed.reconstruction =
              certificate.toProgram design (code.encode message) ∧
            indexed.decodedMessage code test = message ∧
              indexed.encodeBooleanPayload.length ≤
                budget + (seedLength - inputLength) + 1 +
                  BooleanListCode.decoderIndexBitWidth listSize := by
  obtain ⟨hhalf, _hselected⟩ :=
    half_le_encodedReconstructionProgram_of_randomTest_internal
      houtputLength hdensity hlow hrandom hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact findGoodReconstructionCertificate_indexedProgram_sound_internal
    design code message test ((density / (outputLength : ℚ)) / 2)
      hcode hbudget batch certificate hfind

theorem half_le_fullyEncodedIndexedReconstructionProgram_of_randomTest_internal
    {messageLength listSize outputLength inputLength seedLength tapes time
      threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hcode : code.IsListDecodableAt
      (1 / 2 - (density / (outputLength : ℚ)) / 2))
    (hlow : (design.generator (code.encode message)).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          (code.encode message) test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? (code.encode message) test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        ∃ indexed : IndexedReconstructionProgram design listSize,
          indexed.reconstruction =
              certificate.toProgram design (code.encode message) ∧
            indexed.decodedMessage code test = message ∧
              indexed.encode.length ≤
                1 + Fin.bitWidth outputLength +
                  (budget + (seedLength - inputLength) + 1) +
                    BooleanListCode.decoderIndexBitWidth listSize := by
  obtain ⟨hhalf, _hselected⟩ :=
    half_le_indexedReconstructionProgram_of_randomTest_internal
      houtputLength hdensity hcode hlow hrandom hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact
    findGoodReconstructionCertificate_fullyEncodedIndexedProgram_sound_internal
      design code message test ((density / (outputLength : ℚ)) / 2)
        hcode hbudget batch certificate hfind

theorem half_le_listDecodedReconstructionProgram_of_seedDescriptions_internal
    {messageLength listSize outputLength inputLength seedLength tapes time
      threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hcode : code.IsListDecodableAt
      (1 / 2 - (density / (outputLength : ℚ)) / 2))
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (design.generator (code.encode message) seed)) time)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          (code.encode message) test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? (code.encode message) test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        message ∈ (certificate.toProgram design
            (code.encode message)).listDecoderCandidates code test ∧
          ((certificate.toProgram design
            (code.encode message)).listDecoderCandidates code test).card ≤ listSize ∧
          (certificate.toProgram design
            (code.encode message)).encodeBooleanPayload.length ≤
              budget + (seedLength - inputLength) + 1 := by
  obtain ⟨hhalf, _hselected⟩ :=
    half_le_encodedReconstructionProgram_of_seedDescriptions_internal
      houtputLength hdensity hseedLength hproduces hrandom hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact findGoodReconstructionCertificate_listDecoding_sound_internal
    design code message test ((density / (outputLength : ℚ)) / 2)
      hcode hbudget batch certificate hfind

theorem half_le_indexedReconstructionProgram_of_seedDescriptions_internal
    {messageLength listSize outputLength inputLength seedLength tapes time
      threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hcode : code.IsListDecodableAt
      (1 / 2 - (density / (outputLength : ℚ)) / 2))
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (design.generator (code.encode message) seed)) time)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          (code.encode message) test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? (code.encode message) test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        ∃ indexed : IndexedReconstructionProgram design listSize,
          indexed.reconstruction =
              certificate.toProgram design (code.encode message) ∧
            indexed.decodedMessage code test = message ∧
              indexed.encodeBooleanPayload.length ≤
                budget + (seedLength - inputLength) + 1 +
                  BooleanListCode.decoderIndexBitWidth listSize := by
  obtain ⟨hhalf, _hselected⟩ :=
    half_le_encodedReconstructionProgram_of_seedDescriptions_internal
      houtputLength hdensity hseedLength hproduces hrandom hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact findGoodReconstructionCertificate_indexedProgram_sound_internal
    design code message test ((density / (outputLength : ℚ)) / 2)
      hcode hbudget batch certificate hfind

theorem
    half_le_fullyEncodedIndexedReconstructionProgram_of_seedDescriptions_internal
    {messageLength listSize outputLength inputLength seedLength tapes time
      threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {code : BooleanListCode messageLength listSize (Fin inputLength → Bool)}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hcode : code.IsListDecodableAt
      (1 / 2 - (density / (outputLength : ℚ)) / 2))
    (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (design.generator (code.encode message) seed)) time)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          (code.encode message) test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate? (code.encode message) test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        ∃ indexed : IndexedReconstructionProgram design listSize,
          indexed.reconstruction =
              certificate.toProgram design (code.encode message) ∧
            indexed.decodedMessage code test = message ∧
              indexed.encode.length ≤
                1 + Fin.bitWidth outputLength +
                  (budget + (seedLength - inputLength) + 1) +
                    BooleanListCode.decoderIndexBitWidth listSize := by
  obtain ⟨hhalf, _hselected⟩ :=
    half_le_indexedReconstructionProgram_of_seedDescriptions_internal
      houtputLength hdensity hcode hseedLength hproduces hrandom hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact
    findGoodReconstructionCertificate_fullyEncodedIndexedProgram_sound_internal
      design code message test ((density / (outputLength : ℚ)) / 2)
        hcode hbudget batch certificate hfind

end NWDesign

end Complexity
