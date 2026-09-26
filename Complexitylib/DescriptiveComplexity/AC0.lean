/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.AC0.Defs
public import Complexitylib.DescriptiveComplexity.AC0.Internal

/-!
# First-order definable queries belong to nonuniform AC0

The characteristic family of the existing binary query language has polynomial
size and constant depth. The circuits reject malformed encodings and cover every
input length, including zero. At positive length `N`, sentence `φ` has a circuit
of size at most `φ.validatedPolynomial.eval N` and depth at most `φ.size + 5`.

This implements the finite quantifier construction in Immerman's *Descriptive
Complexity*, Section 5.4, Theorem 5.22, for this library's unordered FO syntax and
encoding. The ordered FO[BIT] characterization of uniform AC0 is a further result.
-/

public section

namespace Complexity.DescriptiveComplexity

/-- The query family is the characteristic function of the induced binary language. -/
theorem queryFamily_eq_true {V : Vocabulary} (Q : BooleanQuery V) {N : Nat}
    (input : BitString N) :
    queryFamily Q N input = true ↔ List.ofFn input ∈ queryLanguage Q := by
  simp [queryFamily]

/-- Every induced query language rejects the empty input. -/
@[simp] theorem queryFamily_zero {V : Vocabulary} (Q : BooleanQuery V)
    (input : BitString 0) : queryFamily Q 0 input = false := by
  simp [queryFamily, not_mem_queryLanguage_of_decodeStruct_eq_none Q [] (decodeStruct_nil V)]

/-- A fixed FO sentence has polynomial-size, constant-depth circuits at all positive lengths. -/
theorem Sentence.exists_circuit_on_length {V : Vocabulary} (φ : Sentence V) (N : Nat)
    [NeZero N] :
    ∃ gates, ∃ c : Circuit Basis.unboundedAndOr N 1 gates,
      c.size ≤ φ.validatedPolynomial.eval N ∧ c.depth ≤ φ.size + 5 ∧
        ∀ input, c.eval input 0 = queryFamily (fun A => Sentence.Models A φ) N input :=
  sentence_circuits_internal φ N

/-- The binary language defined by a first-order sentence has a nonuniform AC0 family. -/
theorem Sentence.queryFamily_mem_AC0 {V : Vocabulary} (φ : Sentence V) :
    queryFamily (fun A => Sentence.Models A φ) ∈ Complexity.AC0 :=
  sentence_mem_AC0_internal φ

/-- Every FO-definable query induces a binary language in nonuniform AC0. -/
theorem FODefinable.queryFamily_mem_AC0 {V : Vocabulary} {Q : BooleanQuery V}
    (hQ : FODefinable Q) : queryFamily Q ∈ Complexity.AC0 :=
  foDefinable_mem_AC0_internal hQ

end Complexity.DescriptiveComplexity
