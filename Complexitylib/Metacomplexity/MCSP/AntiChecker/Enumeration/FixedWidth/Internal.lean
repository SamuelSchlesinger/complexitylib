/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Enumeration.FixedWidth.Defs
import Complexitylib.Circuits.Encoding.FixedWidth.Codec
import Complexitylib.Circuits.Encoding.FixedWidth.Conversion
import Complexitylib.Circuits.Encoding.FixedWidth.Conversion.Internal
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Enumeration

/-!
# Fixed-width circuit-candidate enumeration -- proof internals
-/


public section

namespace Complexity

namespace AntiChecker

private theorem rawCircuit_encode_length_le_codeLengthBound
    {arity threshold : Nat} {circuit : CircuitCode.RawCircuit}
    (htopological : circuit.TopologicallyWellFormed arity)
    (hbound : circuit.length ≤ threshold) :
    circuit.encode.length ≤ codeLengthBound arity threshold := by
  have hencode := CircuitCode.RawCircuit.encode_length_le arity
    circuit.length circuit rfl htopological
  calc
    circuit.encode.length ≤
        circuit.length + 1 +
          circuit.length * (2 * (arity + circuit.length) + 5) :=
      hencode
    _ = 1 + circuit.length *
        (2 * (arity + circuit.length) + 6) := by
      ring
    _ ≤ codeLengthBound arity threshold := by
      unfold codeLengthBound
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul hbound
      omega

private theorem candidateCode_exists_boundedRawCircuit
    {arity threshold : Nat} (code : CandidateCode arity threshold) :
    ∃ circuit : CircuitCode.RawCircuit,
      CircuitCode.RawCircuit.decode? code.val = some circuit ∧
        circuit.WellFormed arity ∧ circuit.length ≤ threshold := by
  have hsmall := (mem_candidateCodes_iff.mp code.property).2
  unfold IsSmallCircuitCode at hsmall
  cases hdecode : CircuitCode.RawCircuit.decode? code.val with
  | none => simp [hdecode] at hsmall
  | some circuit =>
      exact ⟨circuit, rfl, by simpa [hdecode] using hsmall⟩

private noncomputable def candidateCodeToBoundedRawCircuit
    {arity threshold : Nat} (code : CandidateCode arity threshold) :
    CircuitCode.FixedWidth.BoundedRawCircuit arity threshold :=
  let circuit := Classical.choose (candidateCode_exists_boundedRawCircuit code)
  ⟨circuit,
    (Classical.choose_spec
      (candidateCode_exists_boundedRawCircuit code)).2⟩

private theorem decode_candidateCodeToBoundedRawCircuit
    {arity threshold : Nat} (code : CandidateCode arity threshold) :
    CircuitCode.RawCircuit.decode? code.val =
      some (candidateCodeToBoundedRawCircuit code).val := by
  unfold candidateCodeToBoundedRawCircuit
  exact (Classical.choose_spec
    (candidateCode_exists_boundedRawCircuit code)).1

private def boundedRawCircuitToCandidateCode
    {arity threshold : Nat}
    (circuit : CircuitCode.FixedWidth.BoundedRawCircuit arity threshold) :
    CandidateCode arity threshold :=
  ⟨circuit.val.encode, by
    apply mem_candidateCodes_iff.mpr
    constructor
    · exact rawCircuit_encode_length_le_codeLengthBound
        circuit.property.1.2 circuit.property.2
    · unfold IsSmallCircuitCode
      rw [CircuitCode.RawCircuit.decode?_encode]
      exact circuit.property⟩

/-- Internal exact equivalence between canonical candidate codes and bounded
well-formed raw circuits. -/
noncomputable def candidateCodeBoundedRawCircuitEquivInternal
    (arity threshold : Nat) :
    CandidateCode arity threshold ≃
      CircuitCode.FixedWidth.BoundedRawCircuit arity threshold where
  toFun := candidateCodeToBoundedRawCircuit
  invFun := boundedRawCircuitToCandidateCode
  left_inv code := by
    apply Subtype.ext
    exact (CircuitCode.RawCircuit.decode?_eq_some_iff code.val
      (candidateCodeToBoundedRawCircuit code).val).mp
        (decode_candidateCodeToBoundedRawCircuit code) |>.symm
  right_inv circuit := by
    apply Subtype.ext
    have hdecode := decode_candidateCodeToBoundedRawCircuit
      (boundedRawCircuitToCandidateCode circuit)
    change CircuitCode.RawCircuit.decode? circuit.val.encode =
      some (candidateCodeToBoundedRawCircuit
        (boundedRawCircuitToCandidateCode circuit)).val at hdecode
    rw [CircuitCode.RawCircuit.decode?_encode] at hdecode
    exact Option.some.inj hdecode |>.symm

/-- Internal exact equivalence between the old canonical candidate-code type
and valid fixed-width descriptions. -/
noncomputable def candidateCodeFixedWidthEquivInternal
    (arity threshold : Nat) :
    CandidateCode arity threshold ≃
      CircuitCode.FixedWidth.ValidDescription arity threshold :=
  (candidateCodeBoundedRawCircuitEquivInternal arity threshold).trans
    (CircuitCode.FixedWidth.wellFormedEquivInternal arity threshold).symm

theorem decode_candidateCodeFixedWidthEquiv_internal
    {arity threshold : Nat} (code : CandidateCode arity threshold) :
    CircuitCode.RawCircuit.decode? code.val =
      some
        (CircuitCode.FixedWidth.Description.toRawCircuit
          (candidateCodeFixedWidthEquivInternal arity threshold code).val) := by
  have hdecode := decode_candidateCodeToBoundedRawCircuit code
  have hroundTrip :=
    (CircuitCode.FixedWidth.wellFormedEquivInternal arity threshold).apply_symm_apply
      (candidateCodeToBoundedRawCircuit code)
  have hraw := congrArg Subtype.val hroundTrip
  rw [CircuitCode.FixedWidth.wellFormedEquiv_apply_val_internal] at hraw
  change CircuitCode.RawCircuit.decode? code.val =
    some
      ((CircuitCode.FixedWidth.wellFormedEquivInternal arity threshold).symm
        (candidateCodeToBoundedRawCircuit code)).val.toRawCircuit
  exact hdecode.trans (congrArg some hraw.symm)

theorem candidateCodeFixedWidthEquiv_symm_val_internal
    {arity threshold : Nat}
    (description : CircuitCode.FixedWidth.ValidDescription arity threshold) :
    ((candidateCodeFixedWidthEquivInternal arity threshold).symm
        description).val = description.val.toRawCircuit.encode := by
  change
    (boundedRawCircuitToCandidateCode
      (CircuitCode.FixedWidth.wellFormedEquivInternal arity threshold
        description)).val = description.val.toRawCircuit.encode
  unfold boundedRawCircuitToCandidateCode
  change
    ((CircuitCode.FixedWidth.wellFormedEquivInternal arity threshold
      description).val).encode = description.val.toRawCircuit.encode
  rw [CircuitCode.FixedWidth.wellFormedEquiv_apply_val_internal]

theorem card_validDescription_eq_candidateCodes_internal
    (arity threshold : Nat) :
    Fintype.card
        (CircuitCode.FixedWidth.ValidDescription arity threshold) =
      (candidateCodes arity threshold).card := by
  calc
    Fintype.card
        (CircuitCode.FixedWidth.ValidDescription arity threshold) =
        Fintype.card (CandidateCode arity threshold) :=
      Fintype.card_congr
        (candidateCodeFixedWidthEquivInternal arity threshold).symm
    _ = (candidateCodes arity threshold).card := by
      simp only [CandidateCode]
      exact Fintype.card_coe _

theorem fixedWidth_codeWidth_le_codeLengthBound_internal
    (arity threshold : Nat) :
    CircuitCode.FixedWidth.codeWidth arity threshold ≤
      codeLengthBound arity threshold := by
  have hbitWidth (value : Nat) : Fin.bitWidth value ≤ value := by
    unfold Fin.bitWidth
    exact Nat.clog_le_of_le_pow (le_of_lt (Nat.lt_two_pow_self))
  have hreference :
      CircuitCode.FixedWidth.referenceWidth arity threshold ≤
        arity + threshold + 1 := by
    unfold CircuitCode.FixedWidth.referenceWidth
    apply max_le
    · omega
    · exact (hbitWidth (arity + threshold)).trans (by omega)
  have hcount :
      CircuitCode.FixedWidth.gateCountWidth threshold ≤ threshold + 1 := by
    unfold CircuitCode.FixedWidth.gateCountWidth
    apply max_le
    · omega
    · exact hbitWidth (threshold + 1)
  unfold CircuitCode.FixedWidth.codeWidth
    CircuitCode.FixedWidth.gateSlotWidth codeLengthBound
  calc
    CircuitCode.FixedWidth.gateCountWidth threshold +
        threshold *
          (3 +
            (CircuitCode.FixedWidth.referenceWidth arity threshold +
              CircuitCode.FixedWidth.referenceWidth arity threshold)) ≤
        threshold + 1 +
          threshold *
            (3 + ((arity + threshold + 1) +
              (arity + threshold + 1))) := by
      gcongr
    _ = 1 + threshold * (2 * (arity + threshold) + 6) := by
      ring

end AntiChecker

end Complexity
