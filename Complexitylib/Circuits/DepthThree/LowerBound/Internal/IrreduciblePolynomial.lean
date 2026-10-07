/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Unrestricted depth-three lower bound: irreducible polynomial

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/IrreduciblePolynomial.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

theorem exists_monic_irreducible_natDegree_two (r : ℕ) (hr : 0 < r) :
    ∃ P : Polynomial (ZMod 2),
      P.Monic ∧ Irreducible P ∧ P.natDegree = r := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_top
    (ZMod 2) (GaloisField 2 r)
  have hαint : IsIntegral (ZMod 2) α := IsIntegral.of_finite (ZMod 2) α
  refine ⟨minpoly (ZMod 2) α, minpoly.monic hαint,
    minpoly.irreducible hαint, ?_⟩
  exact ((Field.primitive_element_iff_minpoly_natDegree_eq
    (ZMod 2) α).mp hα).trans
      (GaloisField.finrank 2 (Nat.ne_of_gt hr))

theorem exists_monic_irreducible_degree_two (r : ℕ) (hr : 0 < r) :
    ∃ P : Polynomial (ZMod 2),
      P.Monic ∧ Irreducible P ∧ P.degree = (r : WithBot ℕ) := by
  obtain ⟨P, hP, hI, hdegree⟩ := exists_monic_irreducible_natDegree_two r hr
  refine ⟨P, hP, hI, ?_⟩
  rw [Polynomial.degree_eq_natDegree hP.ne_zero, hdegree]

end DepthThreeLowerBound

end Complexity
