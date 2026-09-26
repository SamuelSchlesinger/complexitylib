/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Encoding.Validity.Defs
public import Complexitylib.DescriptiveComplexity.Encoding.PolynomialTime
public import Complexitylib.DescriptiveComplexity.Encoding.Decoding
import Complexitylib.DescriptiveComplexity.Encoding.Validity.Internal
import Complexitylib.Classes.P.DecisionFn
import Complexitylib.Classes.P

/-!
# Structure-encoding validation belongs to P

The explicit header, length, and one-hot conditions characterize exactly the
encoder's image. They are polynomial-time predicates by bounded quantification
over the arithmetic bit-access primitives. Thus recognizing valid encodings and
testing successful decoding belong to the existing machine class `P`.

This proves the validation part of the descriptive-complexity machine bridge.
`ModelChecking.PolynomialTime` combines it with fixed-formula evaluation to prove
first-order query languages belong to `P`. `SecondOrder.PolynomialTime` uses the
same validation predicate for its existential-SO certificate verifier.
-/

public section

namespace Complexity.DescriptiveComplexity

/-- Every encoded structure satisfies the explicit wire-format conditions. -/
theorem isValidEncoding_encodeStruct {V : Vocabulary} (A : DecFinStruct V) :
    IsValidEncoding V A.card (encodeStruct A) := isValidEncoding_encodeStruct_internal A

/-- Wire-format validation is equivalent to encoding a structure of the specified size. -/
theorem isValidEncoding_iff (V : Vocabulary) (card : Nat) (bits : List Bool) :
    IsValidEncoding V card bits ↔
      ∃ A : DecFinStruct V, A.card = card ∧ encodeStruct A = bits :=
  isValidEncoding_iff_internal V card bits

/-- Validation at the parsed universe size recognizes exactly all structure encodings. -/
theorem isValidEncoding_parsed_iff (V : Vocabulary) (bits : List Bool) :
    IsValidEncoding V (bits.takeWhile id).length bits ↔
      ∃ A : DecFinStruct V, encodeStruct A = bits := by
  constructor
  · intro h
    obtain ⟨A, _, hA⟩ := (isValidEncoding_iff V _ bits).mp h
    exact ⟨A, hA⟩
  · rintro ⟨A, rfl⟩
    rw [encodeStruct_card]
    exact isValidEncoding_encodeStruct A

/-- Wire-format validation is polynomial-time when the string and universe size are. -/
theorem isValidEncoding_fpPred (V : Vocabulary)
    {bits : List Bool → List Bool} {card : List Bool → Nat}
    (hbits : bits ∈ FP) (hcard : UnaryFn card) :
    FPPred fun z => IsValidEncoding V (card z) (bits z) :=
  isValidEncoding_fpPred_internal V hbits hcard

/-- Membership in the encoder's image is a polynomial-time predicate on every bit string. -/
theorem encodable_fpPred (V : Vocabulary) :
    FPPred fun bits => ∃ A : DecFinStruct V, encodeStruct A = bits :=
  (isValidEncoding_fpPred V id_mem_FP encodedCard_unary).of_iff
    (isValidEncoding_parsed_iff V)

/-- Whether the existing exact decoder succeeds can be tested in polynomial time. -/
theorem decodable_fpPred (V : Vocabulary) :
    FPPred fun bits => ∃ A : DecFinStruct V, decodeStruct V bits = some A :=
  (encodable_fpPred V).of_iff fun bits => by simp only [decodeStruct_eq_some_iff]

/-- The binary language of valid encodings belongs to the actual deterministic machine class P. -/
theorem validEncodings_mem_P (V : Vocabulary) :
    {bits | ∃ A : DecFinStruct V, encodeStruct A = bits} ∈ P :=
  (encodable_fpPred V).mem_P

end Complexity.DescriptiveComplexity
