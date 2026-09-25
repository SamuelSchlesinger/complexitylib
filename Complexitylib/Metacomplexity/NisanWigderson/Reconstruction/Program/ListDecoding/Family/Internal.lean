/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public
import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.ListDecoding.Family.Defs
import Complexitylib.Metacomplexity.ListDecoding.Family.Internal
public
import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Program.ListDecoding.Internal
import Complexitylib.Metacomplexity.Kolmogorov.Internal
import Complexitylib.Metacomplexity.Kolmogorov.Oracle.Internal
import Complexitylib.Metacomplexity.NisanWigderson.Encoding.Internal
import Complexitylib.Models.TuringMachine.OutputSemantics.Internal

/-!
# Uniform list-code families in NW reconstruction -- proof internals
-/


public section

namespace Complexity

namespace NWDesign

namespace HasEncodedMessageCertificateWithin

theorem uniformTimeBoundedKolmogorovComplexity_le_internal
    {family : BooleanListCodeFamily}
    {messageLength inverseAccuracy outputLength seedLength : ℕ}
    {design : NWDesign outputLength
      (family.coordinateLength messageLength inverseAccuracy) seedLength}
    {test : Finset (Fin outputLength → Bool)}
    {message : Fin messageLength → Bool} {bound : ℕ}
    (realization : UniformEncodedMessageDecoderRealization family)
    (hcertificate : HasEncodedMessageCertificateWithin design
      (family.code messageLength inverseAccuracy) test message bound) :
    realization.machine.timeBoundedKolmogorovComplexity
        (List.ofFn message)
        (realization.time
          (realization.framedDescriptionBound design test bound)) ≤
      (realization.framedDescriptionBound design test bound : WithTop ℕ) := by
  obtain ⟨description, hdecode, hlength⟩ := hcertificate
  have hproduce := realization.correct design test description message hdecode
  have hframedLength :
      (pair (realization.ambientEncoding design test) description).length ≤
        realization.framedDescriptionBound design test bound := by
    simp [UniformEncodedMessageDecoderRealization.framedDescriptionBound]
    omega
  have hproduceBound := TM.producesInTime_mono_internal
    (realization.time_mono hframedLength) hproduce
  exact le_trans
    (TM.timeBoundedKolmogorovComplexity_le_internal hproduceBound)
    (WithTop.coe_le_coe.mpr hframedLength)

theorem uniformOracleTimeBoundedKolmogorovComplexity_le_internal
    {family : BooleanListCodeFamily}
    {messageLength inverseAccuracy outputLength seedLength : ℕ}
    {design : NWDesign outputLength
      (family.coordinateLength messageLength inverseAccuracy) seedLength}
    {test : Finset (Fin outputLength → Bool)}
    {message : Fin messageLength → Bool} {bound : ℕ}
    (realization : UniformOracleEncodedMessageDecoderRealization family)
    (hcertificate : HasEncodedMessageCertificateWithin design
      (family.code messageLength inverseAccuracy) test message bound) :
    realization.machine.timeBoundedKolmogorovComplexity
        (finiteTestOracle test) (List.ofFn message)
        (realization.time
          (UniformOracleEncodedMessageDecoderRealization.framedDescriptionBound
            design bound)) ≤
      (UniformOracleEncodedMessageDecoderRealization.framedDescriptionBound
        design bound : WithTop ℕ) := by
  obtain ⟨description, hdecode, hlength⟩ := hcertificate
  have hproduce := realization.correct design test description message hdecode
  have hframedLength :
      (pair (decoderInstance messageLength inverseAccuracy design).encode
        description).length ≤
        UniformOracleEncodedMessageDecoderRealization.framedDescriptionBound
          design bound := by
    simp [UniformOracleEncodedMessageDecoderRealization.framedDescriptionBound]
    omega
  have hproduceBound := hproduce.mono
    (realization.time_mono hframedLength)
  exact le_trans
    (OracleTM.timeBoundedKolmogorovComplexity_le_internal hproduceBound)
    (WithTop.coe_le_coe.mpr hframedLength)

end HasEncodedMessageCertificateWithin

namespace UniformOracleEncodedMessageDecoderRealization

theorem framedDescriptionBound_eq_internal
    {family : BooleanListCodeFamily}
    {messageLength inverseAccuracy outputLength seedLength : ℕ}
    (design : NWDesign outputLength
      (family.coordinateLength messageLength inverseAccuracy) seedLength)
    (descriptionBound : ℕ) :
    framedDescriptionBound design descriptionBound =
      4 * (messageLength.size + inverseAccuracy.size + outputLength.size +
          (family.coordinateLength messageLength inverseAccuracy).size +
          seedLength.size) + 22 +
        2 * (outputLength *
          family.coordinateLength messageLength inverseAccuracy *
          Fin.bitWidth seedLength) + descriptionBound := by
  simp [UniformOracleEncodedMessageDecoderRealization.framedDescriptionBound,
    DecoderInstance.length_encode_internal, decoderInstance]
  omega

theorem inverseDensityFramedDescriptionBound_eq_internal
    {family : BooleanListCodeFamily}
    (bounds : family.PolynomialParameterBounds)
    {messageLength outputLength inverseDensity seedLength : ℕ}
    (design : NWDesign outputLength
      (family.coordinateLength messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)) seedLength)
    (budget : ℕ) :
    inverseDensityFramedDescriptionBound bounds design budget =
      4 * (messageLength.size +
          (reconstructionInverseAccuracy outputLength inverseDensity).size +
          outputLength.size +
          (family.coordinateLength messageLength
            (reconstructionInverseAccuracy outputLength inverseDensity)).size +
          seedLength.size) + 22 +
        2 * (outputLength *
          family.coordinateLength messageLength
            (reconstructionInverseAccuracy outputLength inverseDensity) *
          Fin.bitWidth seedLength) +
        inverseDensityDescriptionBound family bounds messageLength outputLength
          inverseDensity seedLength budget := by
  simp [inverseDensityFramedDescriptionBound,
    framedDescriptionBound_eq_internal]

end UniformOracleEncodedMessageDecoderRealization

namespace UniformEncodedMessageDecoderRealization

theorem efficientlyUniversal_transfer_internal
    {family : BooleanListCodeFamily} {universalTapes : ℕ}
    (realization : UniformEncodedMessageDecoderRealization family)
    (universal : TM universalTapes)
    (huniversal : universal.IsEfficientlyUniversal) :
    ∃ constant coefficient exponent,
      ∀ {messageLength inverseAccuracy outputLength seedLength : ℕ}
        (design : NWDesign outputLength
          (family.coordinateLength messageLength inverseAccuracy) seedLength)
        (test : Finset (Fin outputLength → Bool))
        (message : Fin messageLength → Bool) (bound : ℕ),
        HasEncodedMessageCertificateWithin design
            (family.code messageLength inverseAccuracy) test message bound →
          universal.timeBoundedKolmogorovComplexity (List.ofFn message)
              (coefficient *
                (realization.framedDescriptionBound design test bound +
                  realization.time
                    (realization.framedDescriptionBound design test bound) + 1) ^
                    exponent) ≤
            (realization.framedDescriptionBound design test bound +
              constant : ℕ) := by
  obtain ⟨compile, constant, clock, -, _hsim, hlength, htimed, hclock⟩ :=
    huniversal realization.tapes realization.machine
  obtain ⟨coefficient, exponent, htransfer⟩ :=
    TM.polynomialTimeOverhead_kolmogorov_transfer_internal
      htimed hlength hclock
  refine ⟨constant, coefficient, exponent, ?_⟩
  intro messageLength inverseAccuracy outputLength seedLength design test
    message bound hcertificate
  exact htransfer (List.ofFn message)
    (realization.time
      (realization.framedDescriptionBound design test bound))
    (realization.framedDescriptionBound design test bound)
    (hcertificate.uniformTimeBoundedKolmogorovComplexity_le_internal
      realization)

end UniformEncodedMessageDecoderRealization

namespace UniformOracleEncodedMessageDecoderRealization

theorem efficientlyUniversal_transfer_internal
    {family : BooleanListCodeFamily} {universalTapes : ℕ}
    (realization : UniformOracleEncodedMessageDecoderRealization family)
    (universal : OracleTM universalTapes)
    (huniversal : OracleTM.IsEfficientlyUniversal universal) :
    ∃ constant coefficient exponent,
      ∀ {messageLength inverseAccuracy outputLength seedLength : ℕ}
        (design : NWDesign outputLength
          (family.coordinateLength messageLength inverseAccuracy) seedLength)
        (test : Finset (Fin outputLength → Bool))
        (message : Fin messageLength → Bool) (bound : ℕ),
        HasEncodedMessageCertificateWithin design
            (family.code messageLength inverseAccuracy) test message bound →
          universal.timeBoundedKolmogorovComplexity
              (finiteTestOracle test) (List.ofFn message)
              (coefficient *
                (framedDescriptionBound design bound +
                  realization.time
                    (framedDescriptionBound design bound) + 1) ^
                    exponent) ≤
            (framedDescriptionBound design bound + constant : ℕ) := by
  obtain ⟨compile, constant, clock, -, _hsim, hlength, htimed, hclock⟩ :=
    huniversal realization.tapes realization.machine
  obtain ⟨coefficient, exponent, htransfer⟩ :=
    OracleTM.polynomialTimeOverhead_kolmogorov_transfer_internal
      htimed hlength hclock
  refine ⟨constant, coefficient, exponent, ?_⟩
  intro messageLength inverseAccuracy outputLength seedLength design test
    message bound hcertificate
  exact htransfer (finiteTestOracle test) (List.ofFn message)
    (realization.time (framedDescriptionBound design bound))
    (framedDescriptionBound design bound)
    (hcertificate.uniformOracleTimeBoundedKolmogorovComplexity_le_internal
      realization)

end UniformOracleEncodedMessageDecoderRealization

theorem two_le_reconstructionInverseAccuracy_internal
    {outputLength inverseDensity : ℕ}
    (houtputLength : 0 < outputLength)
    (hinverseDensity : 0 < inverseDensity) :
    2 ≤ reconstructionInverseAccuracy outputLength inverseDensity := by
  rw [reconstructionInverseAccuracy]
  exact le_trans (Nat.le_mul_of_pos_right 2 houtputLength)
    (Nat.le_mul_of_pos_right (2 * outputLength) hinverseDensity)

theorem reconstructionInverseAccuracy_margin_eq_internal
    {outputLength inverseDensity : ℕ}
    (houtputLength : 0 < outputLength)
    (hinverseDensity : 0 < inverseDensity) :
    1 / (reconstructionInverseAccuracy outputLength inverseDensity : ℚ) =
      ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2 := by
  simp only [reconstructionInverseAccuracy, Nat.cast_mul, Nat.cast_ofNat]
  norm_num [div_eq_mul_inv]
  field_simp

theorem half_le_fullyEncodedIndexedReconstructionProgram_of_codeFamily_internal
    {messageLength inverseAccuracy outputLength seedLength tapes time
      threshold budget : ℕ}
    (family : BooleanListCodeFamily)
    (hfamily : family.IsListDecodableAtInverseAccuracy)
    (haccuracy : 2 ≤ inverseAccuracy)
    {design : NWDesign outputLength
      (family.coordinateLength messageLength inverseAccuracy) seedLength}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ}
    (hmargin : 1 / (inverseAccuracy : ℚ) =
      (density / (outputLength : ℚ)) / 2)
    (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hlow : BitGenerator.HasLowTimeBoundedComplexity
      (design.generator
        ((family.code messageLength inverseAccuracy).encode message))
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          ((family.code messageLength inverseAccuracy).encode message) test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate?
            ((family.code messageLength inverseAccuracy).encode message) test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        ∃ indexed : IndexedReconstructionProgram design
            (family.listSize messageLength inverseAccuracy),
          indexed.reconstruction = certificate.toProgram design
              ((family.code messageLength inverseAccuracy).encode message) ∧
            indexed.decodedMessage
                (family.code messageLength inverseAccuracy) test = message ∧
              indexed.encode.length ≤
                1 + Fin.bitWidth outputLength +
                  (budget + (seedLength -
                    family.coordinateLength messageLength inverseAccuracy) + 1) +
                    BooleanListCode.decoderIndexBitWidth
                      (family.listSize messageLength inverseAccuracy) := by
  have hcode := hfamily messageLength inverseAccuracy haccuracy
  rw [hmargin] at hcode
  exact
    half_le_fullyEncodedIndexedReconstructionProgram_of_randomTest_internal
      houtputLength hdensity hcode hlow hrandom hdense hbudget

theorem
    half_le_fullyEncodedIndexedReconstructionProgram_of_polynomialCodeFamily_internal
    {messageLength inverseAccuracy outputLength seedLength tapes time
      threshold budget : ℕ}
    (family : BooleanListCodeFamily)
    (hfamily : family.IsListDecodableAtInverseAccuracy)
    (bounds : family.PolynomialParameterBounds)
    (haccuracy : 2 ≤ inverseAccuracy)
    {design : NWDesign outputLength
      (family.coordinateLength messageLength inverseAccuracy) seedLength}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ}
    (hmargin : 1 / (inverseAccuracy : ℚ) =
      (density / (outputLength : ℚ)) / 2)
    (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hlow : BitGenerator.HasLowTimeBoundedComplexity
      (design.generator
        ((family.code messageLength inverseAccuracy).encode message))
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          ((family.code messageLength inverseAccuracy).encode message) test
          (1 / 2 + (density / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength density) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength density) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate?
            ((family.code messageLength inverseAccuracy).encode message) test
            (1 / 2 + (density / (outputLength : ℚ)) / 2) batch =
          some certificate →
        ∃ indexed : IndexedReconstructionProgram design
            (family.listSize messageLength inverseAccuracy),
          indexed.reconstruction = certificate.toProgram design
              ((family.code messageLength inverseAccuracy).encode message) ∧
            indexed.decodedMessage
                (family.code messageLength inverseAccuracy) test = message ∧
              indexed.encode.length ≤
                1 + Fin.bitWidth outputLength +
                  (budget + (seedLength -
                    family.coordinateLength messageLength inverseAccuracy) + 1) +
                    Nat.clog 2
                      (bounds.listConstant *
                        (inverseAccuracy + 1) ^ bounds.listDegree) := by
  obtain ⟨hhalf, hselected⟩ :=
    half_le_fullyEncodedIndexedReconstructionProgram_of_codeFamily_internal
      family hfamily haccuracy hmargin houtputLength hdensity hlow hrandom
        hdense hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  obtain ⟨indexed, hreconstruction, hdecode, hlength⟩ :=
    hselected batch certificate hfind
  refine ⟨indexed, hreconstruction, hdecode, hlength.trans ?_⟩
  exact Nat.add_le_add_left
    (BooleanListCodeFamily.decoderIndexBitWidth_le_polynomialBound_internal
      bounds messageLength inverseAccuracy) _

theorem
    half_le_fullyEncodedIndexedReconstructionProgram_of_inverseDensity_internal
    {messageLength outputLength inverseDensity seedLength tapes time
      threshold budget : ℕ}
    (family : BooleanListCodeFamily)
    (hfamily : family.IsListDecodableAtInverseAccuracy)
    (bounds : family.PolynomialParameterBounds)
    (houtputLength : 0 < outputLength)
    (hinverseDensity : 0 < inverseDensity)
    {design : NWDesign outputLength
      (family.coordinateLength messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)) seedLength}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    (hlow : BitGenerator.HasLowTimeBoundedComplexity
      (design.generator ((family.code messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)).encode
          message)) machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test
      (1 / (inverseDensity : ℚ)))
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          ((family.code messageLength
            (reconstructionInverseAccuracy outputLength inverseDensity)).encode
              message) test
          (1 / 2 +
            ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength
            (1 / (inverseDensity : ℚ))) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength
          (1 / (inverseDensity : ℚ))) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate?
            ((family.code messageLength
              (reconstructionInverseAccuracy outputLength inverseDensity)).encode
                message) test
            (1 / 2 +
              ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2) batch =
          some certificate →
        ∃ indexed : IndexedReconstructionProgram design
            (family.listSize messageLength
              (reconstructionInverseAccuracy outputLength inverseDensity)),
          indexed.reconstruction = certificate.toProgram design
              ((family.code messageLength
                (reconstructionInverseAccuracy outputLength inverseDensity)).encode
                  message) ∧
            indexed.decodedMessage
                (family.code messageLength
                  (reconstructionInverseAccuracy outputLength inverseDensity))
                test = message ∧
              indexed.encode.length ≤
                1 + Fin.bitWidth outputLength +
                  (budget + (seedLength - family.coordinateLength messageLength
                    (reconstructionInverseAccuracy outputLength inverseDensity)) +
                      1) +
                    Nat.clog 2
                      (bounds.listConstant *
                        (reconstructionInverseAccuracy outputLength
                          inverseDensity + 1) ^ bounds.listDegree) := by
  exact
    half_le_fullyEncodedIndexedReconstructionProgram_of_polynomialCodeFamily_internal
      family hfamily bounds
        (two_le_reconstructionInverseAccuracy_internal
          houtputLength hinverseDensity)
        (density := 1 / (inverseDensity : ℚ))
        (reconstructionInverseAccuracy_margin_eq_internal
          houtputLength hinverseDensity)
        houtputLength (by positivity) hlow hrandom hdense hbudget

theorem half_le_encodedMessageCertificate_of_inverseDensity_internal
    {messageLength outputLength inverseDensity seedLength tapes time
      threshold budget : ℕ}
    (family : BooleanListCodeFamily)
    (hfamily : family.IsListDecodableAtInverseAccuracy)
    (bounds : family.PolynomialParameterBounds)
    (houtputLength : 0 < outputLength)
    (hinverseDensity : 0 < inverseDensity)
    {design : NWDesign outputLength
      (family.coordinateLength messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)) seedLength}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    (hlow : BitGenerator.HasLowTimeBoundedComplexity
      (design.generator ((family.code messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)).encode
          message)) machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test
      (1 / (inverseDensity : ℚ)))
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          ((family.code messageLength
            (reconstructionInverseAccuracy outputLength inverseDensity)).encode
              message) test
          (1 / 2 +
            ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength
            (1 / (inverseDensity : ℚ))) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength
          (1 / (inverseDensity : ℚ))) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate?
            ((family.code messageLength
              (reconstructionInverseAccuracy outputLength inverseDensity)).encode
                message) test
            (1 / 2 +
              ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2) batch =
          some certificate →
        HasEncodedMessageCertificateWithin design
          (family.code messageLength
            (reconstructionInverseAccuracy outputLength inverseDensity))
          test message
          (inverseDensityDescriptionBound family bounds messageLength
            outputLength inverseDensity seedLength budget) := by
  obtain ⟨hhalf, hselected⟩ :=
    half_le_fullyEncodedIndexedReconstructionProgram_of_inverseDensity_internal
      family hfamily bounds houtputLength hinverseDensity hlow hrandom hdense
        hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  obtain ⟨indexed, _hreconstruction, hdecode, hlength⟩ :=
    hselected batch certificate hfind
  refine ⟨indexed.encode, ?_, hlength⟩
  rw [decodeIndexedMessage?_encode_internal, hdecode]

theorem half_le_timeBoundedKolmogorovComplexity_of_inverseDensity_internal
    {messageLength outputLength inverseDensity seedLength tapes time
      threshold budget : ℕ}
    (family : BooleanListCodeFamily)
    (hfamily : family.IsListDecodableAtInverseAccuracy)
    (bounds : family.PolynomialParameterBounds)
    (houtputLength : 0 < outputLength)
    (hinverseDensity : 0 < inverseDensity)
    {design : NWDesign outputLength
      (family.coordinateLength messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)) seedLength}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    (realization : EncodedMessageDecoderRealization design
      (family.code messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)) test)
    (hlow : BitGenerator.HasLowTimeBoundedComplexity
      (design.generator ((family.code messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)).encode
          message)) machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test
      (1 / (inverseDensity : ℚ)))
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          ((family.code messageLength
            (reconstructionInverseAccuracy outputLength inverseDensity)).encode
              message) test
          (1 / 2 +
            ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength
            (1 / (inverseDensity : ℚ))) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength
          (1 / (inverseDensity : ℚ))) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate?
            ((family.code messageLength
              (reconstructionInverseAccuracy outputLength inverseDensity)).encode
                message) test
            (1 / 2 +
              ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2) batch =
          some certificate →
        realization.machine.timeBoundedKolmogorovComplexity
            (List.ofFn message)
            (realization.time (inverseDensityDescriptionBound family bounds
              messageLength outputLength inverseDensity seedLength budget)) ≤
          (inverseDensityDescriptionBound family bounds messageLength
            outputLength inverseDensity seedLength budget : WithTop ℕ) := by
  obtain ⟨hhalf, hcertificates⟩ :=
    half_le_encodedMessageCertificate_of_inverseDensity_internal
      family hfamily bounds houtputLength hinverseDensity hlow hrandom hdense
        hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact
    HasEncodedMessageCertificateWithin.timeBoundedKolmogorovComplexity_le_internal
      realization (hcertificates batch certificate hfind)

theorem half_le_oracleTimeBoundedKolmogorovComplexity_of_inverseDensity_internal
    {messageLength outputLength inverseDensity seedLength tapes time
      threshold budget : ℕ}
    (family : BooleanListCodeFamily)
    (hfamily : family.IsListDecodableAtInverseAccuracy)
    (bounds : family.PolynomialParameterBounds)
    (houtputLength : 0 < outputLength)
    (hinverseDensity : 0 < inverseDensity)
    {design : NWDesign outputLength
      (family.coordinateLength messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)) seedLength}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    (realization : OracleEncodedMessageDecoderRealization design
      (family.code messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)))
    (hlow : BitGenerator.HasLowTimeBoundedComplexity
      (design.generator ((family.code messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)).encode
          message)) machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test
      (1 / (inverseDensity : ℚ)))
    (hbudget : design.HasOverlapBudget budget) :
    1 / 2 ≤
        design.checkedReconstructionBatchSuccessProbability
          ((family.code messageLength
            (reconstructionInverseAccuracy outputLength inverseDensity)).encode
              message) test
          (1 / 2 +
            ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2)
          (reconstructionAdviceTrialCount outputLength
            (1 / (inverseDensity : ℚ))) ∧
      ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength
          (1 / (inverseDensity : ℚ))) →
          ReconstructionTrial outputLength seedLength) certificate,
        design.findGoodReconstructionCertificate?
            ((family.code messageLength
              (reconstructionInverseAccuracy outputLength inverseDensity)).encode
                message) test
            (1 / 2 +
              ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2) batch =
          some certificate →
        realization.machine.timeBoundedKolmogorovComplexity
            (finiteTestOracle test) (List.ofFn message)
            (realization.time (inverseDensityDescriptionBound family bounds
              messageLength outputLength inverseDensity seedLength budget)) ≤
          (inverseDensityDescriptionBound family bounds messageLength
            outputLength inverseDensity seedLength budget : WithTop ℕ) := by
  obtain ⟨hhalf, hcertificates⟩ :=
    half_le_encodedMessageCertificate_of_inverseDensity_internal
      family hfamily bounds houtputLength hinverseDensity hlow hrandom hdense
        hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  have hcertificate := hcertificates batch certificate hfind
  exact hcertificate.oracleTimeBoundedKolmogorovComplexity_le_internal
    realization

theorem half_le_efficientlyUniversalOracleKolmogorovComplexity_of_inverseDensity_internal
    {messageLength outputLength inverseDensity seedLength tapes time
      threshold budget universalTapes : ℕ}
    (family : BooleanListCodeFamily)
    (hfamily : family.IsListDecodableAtInverseAccuracy)
    (bounds : family.PolynomialParameterBounds)
    (houtputLength : 0 < outputLength)
    (hinverseDensity : 0 < inverseDensity)
    {design : NWDesign outputLength
      (family.coordinateLength messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)) seedLength}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    (realization : OracleEncodedMessageDecoderRealization design
      (family.code messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)))
    (universal : OracleTM universalTapes)
    (huniversal : OracleTM.IsEfficientlyUniversal universal)
    (hlow : BitGenerator.HasLowTimeBoundedComplexity
      (design.generator ((family.code messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)).encode
          message)) machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test
      (1 / (inverseDensity : ℚ)))
    (hbudget : design.HasOverlapBudget budget) :
    ∃ constant coefficient exponent,
      (∀ (otherTest : Finset (Fin outputLength → Bool))
        (otherMessage : Fin messageLength → Bool) (bound : ℕ),
        HasEncodedMessageCertificateWithin design
            (family.code messageLength
              (reconstructionInverseAccuracy outputLength inverseDensity))
            otherTest otherMessage bound →
          universal.timeBoundedKolmogorovComplexity
              (finiteTestOracle otherTest) (List.ofFn otherMessage)
              (coefficient *
                (bound + realization.time bound + 1) ^ exponent) ≤
            (bound + constant : ℕ)) ∧
        1 / 2 ≤
          design.checkedReconstructionBatchSuccessProbability
            ((family.code messageLength
              (reconstructionInverseAccuracy outputLength inverseDensity)).encode
                message) test
            (1 / 2 +
              ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2)
            (reconstructionAdviceTrialCount outputLength
              (1 / (inverseDensity : ℚ))) ∧
        ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength
            (1 / (inverseDensity : ℚ))) →
            ReconstructionTrial outputLength seedLength) certificate,
          design.findGoodReconstructionCertificate?
              ((family.code messageLength
                (reconstructionInverseAccuracy outputLength inverseDensity)).encode
                  message) test
              (1 / 2 +
                ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2) batch =
            some certificate →
          universal.timeBoundedKolmogorovComplexity
              (finiteTestOracle test) (List.ofFn message)
              (coefficient *
                (inverseDensityDescriptionBound family bounds messageLength
                    outputLength inverseDensity seedLength budget +
                  realization.time
                    (inverseDensityDescriptionBound family bounds messageLength
                      outputLength inverseDensity seedLength budget) + 1) ^
                    exponent) ≤
            (inverseDensityDescriptionBound family bounds messageLength
              outputLength inverseDensity seedLength budget + constant : ℕ) := by
  obtain ⟨constant, coefficient, exponent, htransfer⟩ :=
    realization.efficientlyUniversal_transfer_internal universal huniversal
  obtain ⟨hhalf, hcertificates⟩ :=
    half_le_encodedMessageCertificate_of_inverseDensity_internal
      family hfamily bounds houtputLength hinverseDensity hlow hrandom hdense
        hbudget
  refine ⟨constant, coefficient, exponent, htransfer, hhalf, ?_⟩
  intro batch certificate hfind
  exact htransfer test message
    (inverseDensityDescriptionBound family bounds messageLength outputLength
      inverseDensity seedLength budget)
    (hcertificates batch certificate hfind)

theorem half_le_efficientlyUniversalKolmogorovComplexity_of_inverseDensity_internal
    {messageLength outputLength inverseDensity seedLength tapes time
      threshold budget universalTapes : ℕ}
    (family : BooleanListCodeFamily)
    (hfamily : family.IsListDecodableAtInverseAccuracy)
    (bounds : family.PolynomialParameterBounds)
    (houtputLength : 0 < outputLength)
    (hinverseDensity : 0 < inverseDensity)
    {design : NWDesign outputLength
      (family.coordinateLength messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)) seedLength}
    {message : Fin messageLength → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    (realization : EncodedMessageDecoderRealization design
      (family.code messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)) test)
    (universal : TM universalTapes)
    (huniversal : universal.IsEfficientlyUniversal)
    (hlow : BitGenerator.HasLowTimeBoundedComplexity
      (design.generator ((family.code messageLength
        (reconstructionInverseAccuracy outputLength inverseDensity)).encode
          message)) machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test
      (1 / (inverseDensity : ℚ)))
    (hbudget : design.HasOverlapBudget budget) :
    ∃ constant coefficient exponent,
      1 / 2 ≤
          design.checkedReconstructionBatchSuccessProbability
            ((family.code messageLength
              (reconstructionInverseAccuracy outputLength inverseDensity)).encode
                message) test
            (1 / 2 +
              ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2)
            (reconstructionAdviceTrialCount outputLength
              (1 / (inverseDensity : ℚ))) ∧
        ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength
            (1 / (inverseDensity : ℚ))) →
            ReconstructionTrial outputLength seedLength) certificate,
          design.findGoodReconstructionCertificate?
              ((family.code messageLength
                (reconstructionInverseAccuracy outputLength inverseDensity)).encode
                  message) test
              (1 / 2 +
                ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2) batch =
            some certificate →
          universal.timeBoundedKolmogorovComplexity (List.ofFn message)
              (coefficient *
                (inverseDensityDescriptionBound family bounds messageLength
                    outputLength inverseDensity seedLength budget +
                  realization.time
                    (inverseDensityDescriptionBound family bounds messageLength
                      outputLength inverseDensity seedLength budget) + 1) ^
                    exponent) ≤
            (inverseDensityDescriptionBound family bounds messageLength
              outputLength inverseDensity seedLength budget + constant : ℕ) := by
  obtain ⟨constant, coefficient, exponent, htransfer⟩ :=
    realization.efficientlyUniversal_transfer_internal universal huniversal
  obtain ⟨hhalf, hcertificates⟩ :=
    half_le_encodedMessageCertificate_of_inverseDensity_internal
      family hfamily bounds houtputLength hinverseDensity hlow hrandom hdense
        hbudget
  refine ⟨constant, coefficient, exponent, hhalf, ?_⟩
  intro batch certificate hfind
  exact htransfer message
    (inverseDensityDescriptionBound family bounds messageLength outputLength
      inverseDensity seedLength budget)
    (hcertificates batch certificate hfind)

namespace UniformEncodedMessageDecoderRealization

theorem half_le_efficientlyUniversalKolmogorovComplexity_of_inverseDensity_internal
    {family : BooleanListCodeFamily} {universalTapes : ℕ}
    (realization : UniformEncodedMessageDecoderRealization family)
    (universal : TM universalTapes)
    (huniversal : universal.IsEfficientlyUniversal) :
    ∃ constant coefficient exponent,
      ∀ (bounds : family.PolynomialParameterBounds)
        {messageLength outputLength inverseDensity seedLength tapes time
          threshold budget : ℕ}
        {design : NWDesign outputLength
          (family.coordinateLength messageLength
            (reconstructionInverseAccuracy outputLength inverseDensity)) seedLength}
        {message : Fin messageLength → Bool}
        {machine : TM tapes} {test : Finset (Fin outputLength → Bool)},
        family.IsListDecodableAtInverseAccuracy →
        0 < outputLength →
        0 < inverseDensity →
        BitGenerator.HasLowTimeBoundedComplexity
          (design.generator ((family.code messageLength
            (reconstructionInverseAccuracy outputLength inverseDensity)).encode
              message)) machine time threshold →
        BitGenerator.IsTimeBoundedRandomTest test machine time threshold →
        BitGenerator.IsDenseTest test (1 / (inverseDensity : ℚ)) →
        design.HasOverlapBudget budget →
        1 / 2 ≤
            design.checkedReconstructionBatchSuccessProbability
              ((family.code messageLength
                (reconstructionInverseAccuracy outputLength inverseDensity)).encode
                  message) test
              (1 / 2 +
                ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2)
              (reconstructionAdviceTrialCount outputLength
                (1 / (inverseDensity : ℚ))) ∧
          ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength
              (1 / (inverseDensity : ℚ))) →
              ReconstructionTrial outputLength seedLength) certificate,
            design.findGoodReconstructionCertificate?
                ((family.code messageLength
                  (reconstructionInverseAccuracy outputLength inverseDensity)).encode
                    message) test
                (1 / 2 +
                  ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2) batch =
              some certificate →
            universal.timeBoundedKolmogorovComplexity (List.ofFn message)
                (coefficient *
                  (realization.inverseDensityFramedDescriptionBound bounds
                      design test budget +
                    realization.time
                      (realization.inverseDensityFramedDescriptionBound bounds
                        design test budget) + 1) ^ exponent) ≤
              (realization.inverseDensityFramedDescriptionBound bounds
                design test budget + constant : ℕ) := by
  obtain ⟨constant, coefficient, exponent, htransfer⟩ :=
    realization.efficientlyUniversal_transfer_internal universal huniversal
  refine ⟨constant, coefficient, exponent, ?_⟩
  intro bounds messageLength outputLength inverseDensity seedLength tapes time
    threshold budget design message machine test hfamily houtputLength
    hinverseDensity hlow hrandom hdense hbudget
  obtain ⟨hhalf, hcertificates⟩ :=
    half_le_encodedMessageCertificate_of_inverseDensity_internal
      family hfamily bounds houtputLength hinverseDensity hlow hrandom hdense
        hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact htransfer design test message
    (inverseDensityDescriptionBound family bounds messageLength outputLength
      inverseDensity seedLength budget)
    (hcertificates batch certificate hfind)

end UniformEncodedMessageDecoderRealization

namespace UniformOracleEncodedMessageDecoderRealization

theorem half_le_efficientlyUniversalKolmogorovComplexity_of_inverseDensity_internal
    {family : BooleanListCodeFamily} {universalTapes : ℕ}
    (realization : UniformOracleEncodedMessageDecoderRealization family)
    (universal : OracleTM universalTapes)
    (huniversal : OracleTM.IsEfficientlyUniversal universal) :
    ∃ constant coefficient exponent,
      ∀ (bounds : family.PolynomialParameterBounds)
        {messageLength outputLength inverseDensity seedLength tapes time
          threshold budget : ℕ}
        {design : NWDesign outputLength
          (family.coordinateLength messageLength
            (reconstructionInverseAccuracy outputLength inverseDensity)) seedLength}
        {message : Fin messageLength → Bool}
        {machine : TM tapes} {test : Finset (Fin outputLength → Bool)},
        family.IsListDecodableAtInverseAccuracy →
        0 < outputLength →
        0 < inverseDensity →
        BitGenerator.HasLowTimeBoundedComplexity
          (design.generator ((family.code messageLength
            (reconstructionInverseAccuracy outputLength inverseDensity)).encode
              message)) machine time threshold →
        BitGenerator.IsTimeBoundedRandomTest test machine time threshold →
        BitGenerator.IsDenseTest test (1 / (inverseDensity : ℚ)) →
        design.HasOverlapBudget budget →
        1 / 2 ≤
            design.checkedReconstructionBatchSuccessProbability
              ((family.code messageLength
                (reconstructionInverseAccuracy outputLength inverseDensity)).encode
                  message) test
              (1 / 2 +
                ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2)
              (reconstructionAdviceTrialCount outputLength
                (1 / (inverseDensity : ℚ))) ∧
          ∀ (batch : Fin (reconstructionAdviceTrialCount outputLength
              (1 / (inverseDensity : ℚ))) →
              ReconstructionTrial outputLength seedLength) certificate,
            design.findGoodReconstructionCertificate?
                ((family.code messageLength
                  (reconstructionInverseAccuracy outputLength inverseDensity)).encode
                    message) test
                (1 / 2 +
                  ((1 / (inverseDensity : ℚ)) / (outputLength : ℚ)) / 2) batch =
              some certificate →
            universal.timeBoundedKolmogorovComplexity
                (finiteTestOracle test) (List.ofFn message)
                (coefficient *
                  (inverseDensityFramedDescriptionBound bounds design budget +
                    realization.time
                      (inverseDensityFramedDescriptionBound bounds design
                        budget) + 1) ^ exponent) ≤
              (inverseDensityFramedDescriptionBound bounds design budget +
                constant : ℕ) := by
  obtain ⟨constant, coefficient, exponent, htransfer⟩ :=
    realization.efficientlyUniversal_transfer_internal universal huniversal
  refine ⟨constant, coefficient, exponent, ?_⟩
  intro bounds messageLength outputLength inverseDensity seedLength tapes time
    threshold budget design message machine test hfamily houtputLength
    hinverseDensity hlow hrandom hdense hbudget
  obtain ⟨hhalf, hcertificates⟩ :=
    half_le_encodedMessageCertificate_of_inverseDensity_internal
      family hfamily bounds houtputLength hinverseDensity hlow hrandom hdense
        hbudget
  refine ⟨hhalf, ?_⟩
  intro batch certificate hfind
  exact htransfer design test message
    (inverseDensityDescriptionBound family bounds messageLength outputLength
      inverseDensity seedLength budget)
    (hcertificates batch certificate hfind)

end UniformOracleEncodedMessageDecoderRealization

end NWDesign

end Complexity
