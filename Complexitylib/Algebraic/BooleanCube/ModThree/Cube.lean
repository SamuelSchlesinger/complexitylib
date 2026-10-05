/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.BooleanCube.ModThree.Cube.Internal
public import Mathlib.Data.Fin.Embedding

/-!
# A signed MOD3 cube inside a binary affine solution set

Choose disjoint coordinate blocks, each containing more than twice as many
coordinates as the system has equations. Every affine solution coset then contains
an injective cube with one direction in each block. On that cube the full Hamming
residue is a sum of independent zero/one parameters with nonzero coefficients in
`ZMod 3`; each coefficient is therefore `1` or `-1`.
-/

@[expose] public section

namespace Algebraic.BooleanCube.ModThree

variable {ι κ J : Type*} [Fintype ι] [Fintype κ] [Fintype J]

/-- Hamming residue on a disjoint cube is the affine sum of the single-direction
 residue changes, with each cube parameter interpreted as zero or one. -/
theorem residue_affineCube (a : ι → ZMod 2) (v : J → ι → ZMod 2)
    (disjoint : DisjointDirections v) (z : J → ZMod 2) :
    residue (affineCube a v z) =
      residue a + ∑ j, bit (z j) * (residue (a + v j) - residue a) :=
  Internal.residue_affineCube a v disjoint z

/-- Each sufficiently large disjoint coordinate block supplies one independent
 MOD3 direction inside the original affine solution coset. -/
theorem exists_affineCube_of_disjoint_blocks
    (R : (ι → ZMod 2) →ₗ[ZMod 2] (κ → ZMod 2)) (a : ι → ZMod 2)
    (B : J → Finset ι) (disjoint : Pairwise fun j k => Disjoint (B j) (B k))
    (large : ∀ j, 2 * Fintype.card κ < (B j).card) :
    ∃ v : J → ι → ZMod 2,
      DisjointDirections v ∧ Function.Injective (affineCube a v) ∧
      (∀ z, R (affineCube a v z) = R a) ∧
      (∀ j, residue (a + v j) - residue a ≠ 0) ∧
      ∀ z, residue (affineCube a v z) =
        residue a + ∑ j, bit (z j) * (residue (a + v j) - residue a) := by
  classical
  choose v kernel supported different using
    fun j => exists_supported_kernel_residue_ne R a (B j) (large j)
  have directions : DisjointDirections v := by
    intro j k unequal i
    by_cases mem : i ∈ B j
    · right
      apply supported k i
      exact Finset.disjoint_left.mp (disjoint unequal) mem
    · exact Or.inl (supported j i mem)
  have nonzero (j : J) : v j ≠ 0 := by
    intro zero
    apply different j
    simp [zero]
  refine ⟨v, directions, Internal.affineCube_injective a v directions nonzero, ?_, ?_, ?_⟩
  · intro z
    simp [affineCube, cubeLinearMap, map_sum, kernel]
  · intro j
    exact sub_ne_zero.mpr (different j)
  · exact residue_affineCube a v directions


/-- Any `q` binary linear equations on `n` coordinates retain a signed MOD3 cube
 of dimension `n / (2*q+1)` in every affine solution coset. -/
theorem exists_signed_cube {n q : ℕ}
    (R : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin q → ZMod 2)) (a : Fin n → ZMod 2) :
    ∃ (L : (Fin (n / (2 * q + 1)) → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
      (δ : Fin (n / (2 * q + 1)) → ZMod 3),
      Function.Injective L ∧ (∀ z, R (L z) = 0) ∧
      (∀ j, δ j = 1 ∨ δ j = -1) ∧
      ∀ z, residue (a + L z) = residue a + ∑ j, bit (z j) * δ j := by
  classical
  let e : Fin (n / (2 * q + 1)) × Fin (2 * q + 1) ↪ Fin n :=
    finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb (Nat.div_mul_le_self n (2 * q + 1)))
  let B (j : Fin (n / (2 * q + 1))) := Finset.univ.image fun t => e (j, t)
  have disjoint : Pairwise fun j k => Disjoint (B j) (B k) := by
    intro j k unequal
    apply Finset.disjoint_left.mpr
    intro i left right
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp left
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp right
    have equal := e.injective (hs.trans ht.symm)
    exact unequal (congrArg Prod.fst equal)
  have large (j : Fin (n / (2 * q + 1))) : 2 * Fintype.card (Fin q) < (B j).card := by
    have injective : Function.Injective fun t => e (j, t) := by
      intro s t equal
      exact congrArg Prod.snd (e.injective equal)
    simp [B, Finset.card_image_of_injective _ injective]
  obtain ⟨v, _, injective, kernel, nonzero, identity⟩ :=
    exists_affineCube_of_disjoint_blocks R a B disjoint large
  refine ⟨cubeLinearMap v, fun j => residue (a + v j) - residue a, ?_, ?_, ?_, identity⟩
  · intro z w equal
    apply injective
    exact congrArg (a + ·) equal
  · intro z
    have h := kernel z
    simp only [affineCube, map_add] at h
    exact add_left_cancel (h.trans (add_zero (R a)).symm)
  · intro j
    exact (by decide : ∀ t : ZMod 3, t ≠ 0 → t = 1 ∨ t = -1) _ (nonzero j)

end Algebraic.BooleanCube.ModThree
