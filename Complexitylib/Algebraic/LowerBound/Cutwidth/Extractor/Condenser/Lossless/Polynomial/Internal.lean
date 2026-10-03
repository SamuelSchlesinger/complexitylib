/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Polynomial.Defs
public import Mathlib.Data.Fintype.Pi
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Expansion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# From polynomial expansion to seed-preserving flat condensation

The power-of-two map has the same neighbors as the GUV graph.
Its expansion loss divided by the field cardinality bounds every seeded
test discrepancy from a distribution uniform on one equally sized set in
each seed fiber. The witness may depend on the source support.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem polynomialCondenser_flat_lossless {F : Type*} [Field F] [Fintype F]
    {r m : Nat} (E : Polynomial F) (monic : E.Monic)
    (irreducible : Irreducible E) (degree : 1 < E.natDegree)
    (fieldSize : 2 ^ r ≤ Fintype.card F)
    (P : Finset (Polynomial F)) (nonempty : P.Nonempty)
    (source : ∀ f ∈ P, f.degree < E.degree) (size : P.card ≤ (2 ^ r) ^ m) :
    ∃ g : F → (P ↪ (Fin m → F)), ∀ T : Finset (F × (Fin m → F)),
      |seededTestProb (fun f : P => polynomialCondenser E r m f.val) T -
        seededTestProb (fun f y => g y f) T| ≤
          (((E.natDegree - 1) * (2 ^ r - 1) * m : Nat) : ℝ) / Fintype.card F := by
  have capacity : P.card ≤ Fintype.card (Fin m → F) := by
    simpa only [Fintype.card_fun, Fintype.card_fin] using
      size.trans (Nat.pow_le_pow_left fieldSize m)
  have neighbors : seededNeighborSet (polynomialCondenser E r m) P =
      polynomialNeighborSet E (2 ^ r) m P := by
    ext z
    simp only [seededNeighborSet, polynomialNeighborSet, Finset.mem_biUnion,
      Finset.mem_image, polynomialNeighbor_pow_two]
  apply exists_seedwise_injection_of_expansion (polynomialCondenser E r m)
    P nonempty capacity
  rw [neighbors]
  let loss := (E.natDegree - 1) * (2 ^ r - 1) * m
  have expansion := polynomialNeighborSet_expansion E monic irreducible degree
    (Nat.two_pow_pos r) P source size
  have cover : (Fintype.card F : ℝ) ≤
      ((Fintype.card F - loss : Nat) : ℝ) + loss := by
    exact_mod_cast (le_tsub_add : Fintype.card F ≤ Fintype.card F - loss + loss)
  have nonzero : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have factor : (1 - (loss : ℝ) / Fintype.card F) * Fintype.card F =
      (Fintype.card F : ℝ) - loss := by
    field_simp [nonzero]
  calc
    (1 - (loss : ℝ) / Fintype.card F) * P.card * Fintype.card F =
        ((Fintype.card F : ℝ) - loss) * P.card := by
      rw [mul_right_comm, factor]
    _ ≤ ((Fintype.card F - loss : Nat) : ℝ) * P.card :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ ≤ ((polynomialNeighborSet E (2 ^ r) m P).card : ℝ) := by
      exact_mod_cast expansion

theorem polynomialCondenser_flat_mixture {F : Type*} [Field F] [Fintype F]
    {r m K : Nat} (E : Polynomial F) (monic : E.Monic)
    (irreducible : Irreducible E) (degree : 1 < E.natDegree)
    (fieldSize : 2 ^ r ≤ Fintype.card F)
    (P : Finset (Polynomial F)) (source : ∀ f ∈ P, f.degree < E.degree)
    (positive : 0 < K) (threshold : K ≤ P.card) (capacity : K ≤ (2 ^ r) ^ m) :
    ∃ g : ∀ S : P.powersetCard K, F → (S.val ↪ (Fin m → F)),
      ∀ T : Finset (F × (Fin m → F)),
        |seededTestProb (fun f : P => polynomialCondenser E r m f.val) T -
          seededMixtureTestProb (fun _ : P.powersetCard K =>
            ((P.powersetCard K).card : ℝ)⁻¹)
            (fun S f y => g S y f) T| ≤
              (((E.natDegree - 1) * (2 ^ r - 1) * m : Nat) : ℝ) / Fintype.card F := by
  apply exists_flat_mixture_of_exact_size (polynomialCondenser E r m) P positive threshold
  intro S subset card
  exact polynomialCondenser_flat_lossless E monic irreducible degree fieldSize S
    (Finset.card_pos.mp (card ▸ positive))
    (fun f hf => source f (subset hf)) (card ▸ capacity)

end Algebraic.Cutwidth.Extractor.Internal
