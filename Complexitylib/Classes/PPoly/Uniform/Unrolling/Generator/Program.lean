/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Program.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Program.Internal

/-!
# Direct-unrolling generator program

This module exposes the fixed work-vector layout and verified tagged/header
prefix of the direct-unrolling generator. A later module supplies the positive
tableau body and discharges its value-level entry condition.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- The positive polynomial-counter and tagged-header prefix is sound. -/
theorem positivePreamble_sound (tm : TM k) (q : Polynomial ℕ) :
    (positivePreamble tm q).Sound :=
  positivePreamble_sound_internal tm q

/-- The positive polynomial/header prefix uses logarithmic all-prefix space
after the unary input length has been loaded in binary. -/
theorem positivePreamble_space_bigO_log (tm : TM k) (q : Polynomial ℕ) :
    BinaryRoutine.SpaceBoundInLogAt (positivePreamble tm q)
      TM.binaryLengthSpace
      (BinaryRoutine.inputLengthValues Work.inputLength) :=
  positivePreamble_space_bigO_log_internal tm q

/-- A sound positive tableau body composes with the verified header prefix. -/
theorem positiveMember_sound (tm : TM k) (q : Polynomial ℕ)
    {body : BinaryRoutine WorkCount} (hbody : body.Sound) :
    (positiveMember tm q body).Sound :=
  positiveMember_sound_internal tm q hbody

/-- A logarithmic-space positive body remains logarithmic after the verified
polynomial/header prefix. -/
theorem positiveMember_space_bigO_log
    (tm : TM k) (q : Polynomial ℕ) (body : BinaryRoutine WorkCount)
    (hbody : BinaryRoutine.SpaceBoundInLogAt body TM.binaryLengthSpace
      (fun inputLength => preambleValues tm q
        (BinaryRoutine.inputLengthValues Work.inputLength inputLength))) :
    BinaryRoutine.SpaceBoundInLogAt (positiveMember tm q body)
      TM.binaryLengthSpace
      (BinaryRoutine.inputLengthValues Work.inputLength) :=
  positiveMember_space_bigO_log_internal tm q body hbody

/-- The hardwired zero-length family member is sound. -/
theorem zeroMember_sound (tm : TM k) (q : Polynomial ℕ) :
    (zeroMember tm q).Sound :=
  zeroMember_sound_internal tm q

/-- A sound positive tableau body yields a sound complete zero/positive
generator skeleton. -/
theorem program_sound (tm : TM k) (q : Polynomial ℕ)
    {positiveBody : BinaryRoutine WorkCount} (hbody : positiveBody.Sound) :
    (program tm q positiveBody).Sound :=
  program_sound_internal tm q hbody

/-- A logarithmic-space positive body yields a logarithmic-space complete
zero/positive generator skeleton. -/
theorem program_space_bigO_log
    (tm : TM k) (q : Polynomial ℕ)
    (positiveBody : BinaryRoutine WorkCount)
    (hbody : BinaryRoutine.SpaceBoundInLogAt positiveBody
      TM.binaryLengthSpace
      (fun inputLength => preambleValues tm q
        (BinaryRoutine.inputLengthValues Work.inputLength inputLength))) :
    BinaryRoutine.SpaceBoundInLogAt (program tm q positiveBody)
      TM.binaryLengthSpace
      (BinaryRoutine.inputLengthValues Work.inputLength) :=
  program_space_bigO_log_internal tm q positiveBody hbody

/-- The positive prefix's arithmetic/scratch obligations hold from the
canonical input-length work vector. -/
theorem positivePreamble_requires_inputLengthValues
    (tm : TM k) (q : Polynomial ℕ) (length : ℕ) :
    (positivePreamble tm q).requires
      (BinaryRoutine.inputLengthValues Work.inputLength length) :=
  positivePreamble_requires_inputLengthValues_internal tm q length

/-- A positive body's entry obligation for every nonzero length is exactly
what the complete zero/positive generator needs at fresh-input entry. -/
theorem program_requires_inputLengthValues
    (tm : TM k) (q : Polynomial ℕ)
    (positiveBody : BinaryRoutine WorkCount)
    (hbody : ∀ length, 0 < length →
      positiveBody.requires (preambleValues tm q
        (BinaryRoutine.inputLengthValues Work.inputLength length))) :
    ∀ length, (program tm q positiveBody).requires
      (BinaryRoutine.inputLengthValues Work.inputLength length) :=
  program_requires_inputLengthValues_internal tm q positiveBody hbody

/-- Exact pure work-vector endpoint of the positive prefix. -/
@[simp] theorem positivePreamble_effect (tm : TM k) (q : Polynomial ℕ)
    (values : BinaryValues WorkCount) :
    (positivePreamble tm q).effect values = preambleValues tm q values :=
  positivePreamble_effect_internal tm q values

/-- Exact tag and gate-count header emitted by the positive prefix. -/
@[simp] theorem positivePreamble_emitted (tm : TM k) (q : Polynomial ℕ)
    (values : BinaryValues WorkCount) :
    (positivePreamble tm q).emitted values =
      true :: CircuitCode.NatCode.encode
        ((TM.directSerializerGateCountPolynomial tm q).eval
          (values Work.inputLength)) :=
  positivePreamble_emitted_internal tm q values

/-- Exact tagged code emitted on length zero. -/
@[simp] theorem zeroMember_emitted (tm : TM k) (q : Polynomial ℕ)
    (values : BinaryValues WorkCount) :
    (zeroMember tm q).emitted values =
      [false,
        boundedAcceptanceBit tm.toNTM
          ((TM.directSerializerHorizonPolynomial q).eval 0)
          (fun index => Fin.elim0 index) (fun _ => false)] :=
  zeroMember_emitted_internal tm q values

/-- Exact zero/positive word emitted by the generator skeleton. -/
@[simp] theorem program_emitted (tm : TM k) (q : Polynomial ℕ)
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
          positiveBody.emitted (preambleValues tm q values)) :=
  program_emitted_internal tm q positiveBody values

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
