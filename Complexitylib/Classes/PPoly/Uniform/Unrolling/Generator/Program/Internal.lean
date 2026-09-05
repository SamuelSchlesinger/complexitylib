/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Program.Defs
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Control
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.SpaceBounds
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.InputLength.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinaryLength
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

/-!
# Direct-unrolling generator program -- proof internals
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

private noncomputable def preambleSpaceWidthPolynomial
    (tm : TM k) (q : Polynomial ℕ) : Polynomial ℕ :=
  TM.binaryPolynomialSpaceWidthPolynomial
      (TM.directSerializerHorizonPolynomial q) +
    TM.binaryPolynomialSpaceWidthPolynomial
      (TM.directSerializerFrontierPolynomial tm q) +
    TM.binaryPolynomialSpaceWidthPolynomial
      (TM.directSerializerGateCountPolynomial tm q) +
    Polynomial.X + TM.directSerializerGateCountPolynomial tm q +
    Polynomial.C 1

theorem positivePreamble_spaceBoundByWidth_internal
    (tm : TM k) (q : Polynomial ℕ) :
    ∃ p : Polynomial ℕ,
      BinaryRoutine.SpaceBoundByWidthAt (positivePreamble tm q)
        TM.binaryLengthSpace
        (BinaryRoutine.inputLengthValues Work.inputLength) p.eval := by
  refine ⟨preambleSpaceWidthPolynomial tm q, ?_⟩
  unfold positivePreamble
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList_internal
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.evalPolynomial_internal
    intro inputLength
    simp [preambleSpaceWidthPolynomial, BinaryRoutine.inputLengthValues,
      Work.inputLength]
    omega
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.evalPolynomial_internal
    intro inputLength
    simp [preambleSpaceWidthPolynomial, BinaryRoutine.evalPolynomial,
      BinaryRoutine.inputLengthValues, Work.inputLength, Work.horizon]
    omega
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.evalPolynomial_internal
    intro inputLength
    simp [preambleSpaceWidthPolynomial, BinaryRoutine.evalPolynomial,
      BinaryRoutine.inputLengthValues, Work.inputLength, Work.horizon,
      Work.frontier]
    omega
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.binaryCopy_internal
    · intro inputLength
      simp [preambleSpaceWidthPolynomial, BinaryRoutine.evalPolynomial,
        BinaryRoutine.inputLengthValues, Work.inputLength, Work.horizon,
        Work.frontier, Work.gateCount]
      omega
    · intro inputLength
      simp [preambleSpaceWidthPolynomial, BinaryRoutine.evalPolynomial,
        BinaryRoutine.inputLengthValues, Work.inputLength, Work.horizon,
        Work.frontier, Work.gateCount, Work.available]
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.binaryCopy_internal
    · intro inputLength
      simp [preambleSpaceWidthPolynomial, BinaryRoutine.binaryCopy,
        BinaryRoutine.evalPolynomial, BinaryRoutine.inputLengthValues,
        Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
        Work.available]
      omega
    · intro inputLength
      simp [preambleSpaceWidthPolynomial, BinaryRoutine.binaryCopy,
        BinaryRoutine.evalPolynomial, BinaryRoutine.inputLengthValues,
        Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
        Work.available, Work.configBase]
  constructor
  · exact BinaryRoutine.SpaceBoundByWidthAt.emitBits_internal [true]
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.emitNatCode_internal
    intro inputLength
    simp [preambleSpaceWidthPolynomial, BinaryRoutine.emitBits,
      BinaryRoutine.binaryCopy, BinaryRoutine.evalPolynomial,
      BinaryRoutine.inputLengthValues, Work.inputLength, Work.horizon,
      Work.frontier, Work.gateCount, Work.available, Work.configBase]
    omega
  · trivial

theorem positivePreamble_space_bigO_log_internal
    (tm : TM k) (q : Polynomial ℕ) :
    BinaryRoutine.SpaceBoundInLogAt (positivePreamble tm q)
      TM.binaryLengthSpace
      (BinaryRoutine.inputLengthValues Work.inputLength) := by
  obtain ⟨p, hspace⟩ :=
    positivePreamble_spaceBoundByWidth_internal tm q
  exact hspace.to_log TM.binaryLengthSpace_bigO_log p (fun _ => le_rfl)

theorem positivePreamble_sound_internal (tm : TM k) (q : Polynomial ℕ) :
    (positivePreamble tm q).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h | h
  · subst routine
    exact BinaryRoutine.evalPolynomial_sound Work.inputLength Work.horizon
      Work.polynomialScratch Work.multiplyCounter Work.addCounter
      (TM.directSerializerHorizonPolynomial q)
  · subst routine
    exact BinaryRoutine.evalPolynomial_sound Work.inputLength Work.frontier
      Work.polynomialScratch Work.multiplyCounter Work.addCounter
      (TM.directSerializerFrontierPolynomial tm q)
  · subst routine
    exact BinaryRoutine.evalPolynomial_sound Work.inputLength Work.gateCount
      Work.polynomialScratch Work.multiplyCounter Work.addCounter
      (TM.directSerializerGateCountPolynomial tm q)
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.inputLength Work.available
      Work.copyCounter
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.inputLength Work.configBase
      Work.copyCounter
  · subst routine
    exact BinaryRoutine.emitBits_sound [true]
  · subst routine
    exact BinaryRoutine.emitNatCode_sound Work.emitCounter Work.gateCount

theorem positiveMember_sound_internal (tm : TM k) (q : Polynomial ℕ)
    {body : BinaryRoutine WorkCount} (hbody : body.Sound) :
    (positiveMember tm q body).Sound :=
  (positivePreamble_sound_internal tm q).seq hbody

theorem zeroMember_sound_internal (tm : TM k) (q : Polynomial ℕ) :
    (zeroMember tm q).Sound :=
  BinaryRoutine.emitBits_sound _

theorem zeroMember_space_bigO_log_internal (tm : TM k)
    (q : Polynomial ℕ) :
    BinaryRoutine.SpaceBoundInLogAt (zeroMember tm q)
      TM.binaryLengthSpace
      (BinaryRoutine.inputLengthValues Work.inputLength) := by
  exact BinaryRoutine.SpaceBoundInLogAt.emitBits_internal _
    TM.binaryLengthSpace_bigO_log

theorem program_sound_internal (tm : TM k) (q : Polynomial ℕ)
    {positiveBody : BinaryRoutine WorkCount} (hbody : positiveBody.Sound) :
    (program tm q positiveBody).Sound :=
  (zeroMember_sound_internal tm q).branchZero
    (positiveMember_sound_internal tm q hbody) Work.inputLength

theorem positivePreamble_effect_internal (tm : TM k) (q : Polynomial ℕ)
    (values : BinaryValues WorkCount) :
    (positivePreamble tm q).effect values = preambleValues tm q values := by
  simp [positivePreamble, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits,
    BinaryRoutine.evalPolynomial, BinaryRoutine.binaryCopy,
    BinaryRoutine.emitNatCode, preambleValues, Work.inputLength, Work.horizon,
    Work.frontier, Work.gateCount, Work.available, Work.configBase]

theorem positiveMember_space_bigO_log_internal
    (tm : TM k) (q : Polynomial ℕ) (body : BinaryRoutine WorkCount)
    (hbody : BinaryRoutine.SpaceBoundInLogAt body TM.binaryLengthSpace
      (fun inputLength => preambleValues tm q
        (BinaryRoutine.inputLengthValues Work.inputLength inputLength))) :
    BinaryRoutine.SpaceBoundInLogAt (positiveMember tm q body)
      TM.binaryLengthSpace
      (BinaryRoutine.inputLengthValues Work.inputLength) := by
  apply BinaryRoutine.SpaceBoundInLogAt.seq_internal
    (positivePreamble_space_bigO_log_internal tm q)
  simpa only [positivePreamble_effect_internal] using hbody

theorem program_space_bigO_log_internal
    (tm : TM k) (q : Polynomial ℕ)
    (positiveBody : BinaryRoutine WorkCount)
    (hbody : BinaryRoutine.SpaceBoundInLogAt positiveBody
      TM.binaryLengthSpace
      (fun inputLength => preambleValues tm q
        (BinaryRoutine.inputLengthValues Work.inputLength inputLength))) :
    BinaryRoutine.SpaceBoundInLogAt (program tm q positiveBody)
      TM.binaryLengthSpace
      (BinaryRoutine.inputLengthValues Work.inputLength) := by
  exact BinaryRoutine.SpaceBoundInLogAt.branchZero_internal Work.inputLength
    (zeroMember_space_bigO_log_internal tm q)
    (positiveMember_space_bigO_log_internal tm q positiveBody hbody)

theorem positivePreamble_requires_inputLengthValues_internal
    (tm : TM k) (q : Polynomial ℕ) (length : ℕ) :
    (positivePreamble tm q).requires
      (BinaryRoutine.inputLengthValues Work.inputLength length) := by
  simp [positivePreamble, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits,
    BinaryRoutine.evalPolynomial, BinaryRoutine.binaryCopy,
    BinaryRoutine.emitNatCode, BinaryRoutine.inputLengthValues,
    Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
    Work.available, Work.configBase,
    Work.polynomialScratch, Work.multiplyCounter, Work.addCounter,
    Work.copyCounter, Work.emitCounter]
  constructor
  · constructor <;> decide
  · constructor
    · constructor <;> decide
    · constructor <;> decide

theorem program_requires_inputLengthValues_internal
    (tm : TM k) (q : Polynomial ℕ)
    (positiveBody : BinaryRoutine WorkCount)
    (hbody : ∀ length, 0 < length →
      positiveBody.requires (preambleValues tm q
        (BinaryRoutine.inputLengthValues Work.inputLength length))) :
    ∀ length, (program tm q positiveBody).requires
      (BinaryRoutine.inputLengthValues Work.inputLength length) := by
  intro length
  by_cases hzero : length = 0
  · subst length
    simp [program, BinaryRoutine.branchZero, zeroMember,
      BinaryRoutine.emitBits, BinaryRoutine.inputLengthValues,
      Work.inputLength]
  · simp only [program, BinaryRoutine.branchZero]
    rw [ite_eq_right (by
      simpa [BinaryRoutine.inputLengthValues, Work.inputLength] using hzero)]
    change
      (positivePreamble tm q).requires
          (BinaryRoutine.inputLengthValues Work.inputLength length) ∧
        positiveBody.requires
          ((positivePreamble tm q).effect
            (BinaryRoutine.inputLengthValues Work.inputLength length))
    constructor
    · exact positivePreamble_requires_inputLengthValues_internal tm q length
    · rw [positivePreamble_effect_internal]
      exact hbody length (Nat.pos_of_ne_zero hzero)

theorem positivePreamble_emitted_internal (tm : TM k) (q : Polynomial ℕ)
    (values : BinaryValues WorkCount) :
    (positivePreamble tm q).emitted values =
      true :: CircuitCode.NatCode.encode
        ((TM.directSerializerGateCountPolynomial tm q).eval
          (values Work.inputLength)) := by
  simp [positivePreamble, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits,
    BinaryRoutine.evalPolynomial, BinaryRoutine.binaryCopy,
    BinaryRoutine.emitNatCode, Work.inputLength, Work.horizon, Work.frontier,
    Work.gateCount, Work.available, Work.configBase]

theorem zeroMember_emitted_internal (tm : TM k) (q : Polynomial ℕ)
    (values : BinaryValues WorkCount) :
    (zeroMember tm q).emitted values =
      [false,
        boundedAcceptanceBit tm.toNTM
          ((TM.directSerializerHorizonPolynomial q).eval 0)
          (fun index => Fin.elim0 index) (fun _ => false)] := by
  rfl

theorem program_emitted_internal (tm : TM k) (q : Polynomial ℕ)
    (positiveBody : BinaryRoutine WorkCount)
    (values : BinaryValues WorkCount) :
    (program tm q positiveBody).emitted values =
      if values Work.inputLength = 0 then
        [false,
          boundedAcceptanceBit tm.toNTM
            ((TM.directSerializerHorizonPolynomial q).eval 0)
            (fun index => Fin.elim0 index) (fun _ => false)]
      else
        true :: (CircuitCode.NatCode.encode
          ((TM.directSerializerGateCountPolynomial tm q).eval
            (values Work.inputLength)) ++
          positiveBody.emitted (preambleValues tm q values)) := by
  by_cases hzero : values Work.inputLength = 0
  · simp [program, BinaryRoutine.branchZero, hzero,
      zeroMember_emitted_internal]
  · simp [program, BinaryRoutine.branchZero, positiveMember,
      BinaryRoutine.seq, hzero, positivePreamble_effect_internal,
      positivePreamble_emitted_internal]

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
