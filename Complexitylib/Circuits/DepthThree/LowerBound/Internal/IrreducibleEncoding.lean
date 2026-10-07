/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.AlgebraPolynomial
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.IrreduciblePolynomial

/-!
# Unrestricted depth-three lower bound: irreducible encoding

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/IrreducibleEncoding.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace BinaryAlgebra

/-- Encode the coefficients of a monic binary polynomial as bits. -/
def polynomialBits (P : Polynomial F2) (r : ℕ) : Fin r → Bool :=
  fun i => fieldBit (P.coeff i.val)

theorem inputPolynomialBits_polynomialBits (P : Polynomial F2) (hP : P.Monic)
    {r : ℕ} (hdegree : P.natDegree = r) :
    inputPolynomialBits (polynomialBits P r) = P := by
  ext j
  rcases lt_trichotomy j r with hj | rfl | hj
  · simpa only [polynomialBits, bitValue_fieldBit] using
      inputPolynomialBits_coeff_lt (polynomialBits P r) ⟨j, hj⟩
  · rw [inputPolynomialBits_coeff_leading]
    simpa only [hdegree] using hP.coeff_natDegree.symm
  · have hleft : (inputPolynomialBits (polynomialBits P r)).coeff j = 0 :=
      inputPolynomial_coeff_of_gt _ hj
    rw [hleft]
    symm
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    simpa only [hdegree] using hj

end BinaryAlgebra

theorem exists_irreducible_inputPolynomialBits (r : ℕ) (hr : 0 < r) :
    ∃ p : Fin r → Bool, Irreducible (BinaryAlgebra.inputPolynomialBits p) := by
  obtain ⟨P, hP, hI, hdegree⟩ := exists_monic_irreducible_natDegree_two r hr
  refine ⟨BinaryAlgebra.polynomialBits P r, ?_⟩
  rw [BinaryAlgebra.inputPolynomialBits_polynomialBits P hP hdegree]
  exact hI

end DepthThreeLowerBound

end Complexity
