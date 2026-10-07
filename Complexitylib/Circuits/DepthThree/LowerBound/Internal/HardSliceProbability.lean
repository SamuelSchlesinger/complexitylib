/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.HardSliceMoment
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.SparseCorrelation
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.HashProbability
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.AlgebraQuotient
public import Mathlib.Tactic.Positivity

/-!
# Unrestricted depth-three lower bound: hard slice probability

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/HardSliceProbability.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

/-- The sparse-family constant used in the hard-slice existence argument. -/
def hardSliceSparseConstant (b : ℕ) (hb : 1 ≤ b) : ℕ :=
  Classical.choose (exists_sparse_correlation_constant.{0} b hb)

theorem hardSliceSparseConstant_pos (b : ℕ) (hb : 1 ≤ b) :
    0 < hardSliceSparseConstant b hb :=
  (Classical.choose_spec (exists_sparse_correlation_constant.{0} b hb)).1

theorem hardSliceSparseConstant_spec (b : ℕ) (hb : 1 ≤ b)
    (V : Type) [Fintype V] [DecidableEq V] (G : Cube V → ℝ)
    (htests : ∀ H : CNF V, H.Normalized → H.WidthAtMost b →
      H.length ≤ hardSliceSparseConstant b hb * Fintype.card V →
      |finiteAvg (fun x => G x * indicator (H.eval x))| ≤
        (2 : ℝ) ^ (-(Fintype.card V : ℝ) / 4)) :
    corr b G ≤ (2 : ℝ) ^ (-(Fintype.card V : ℝ) / 8) :=
  (Classical.choose_spec (exists_sparse_correlation_constant.{0} b hb)).2 V G htests

theorem sparseMomentBound_nonneg (m b L h : ℕ) (δ : ℝ) :
    0 ≤ sparseMomentBound m b L h δ := by
  unfold sparseMomentBound
  apply mul_nonneg (Nat.cast_nonneg _)
  apply div_nonneg
  · positivity
  · rw [pow_mul]
    exact pow_nonneg (sq_nonneg (δ * ((2 ^ m : ℕ) : ℝ))) h

theorem coefficient_corr_failure_le {F V : Type} [Field F]
    [Module BinaryAlgebra.F2 F] [Fintype F] [Fintype V]
    (ell : F →ₗ[BinaryAlgebra.F2] BinaryAlgebra.F2) (hOne : ell 1 = 1)
    (a : Cube V → F) (ha : Function.Injective a)
    (b : ℕ) (hb : 1 ≤ b) (h : ℕ) (hh : 0 < h) :
    finiteProb (fun β : Fin (2 * h) → F =>
      ¬ corr b (fun x => sign (Interpolation.acceptEval ell (2 * h) a β x)) ≤
        (2 : ℝ) ^ (-(Fintype.card V : ℝ) / 8)) ≤
      sparseMomentBound (Fintype.card V) b
        (hardSliceSparseConstant b hb * Fintype.card V) h
        ((2 : ℝ) ^ (-(Fintype.card V : ℝ) / 4)) := by
  apply le_trans _ (coefficient_sparse_cnfs_gt_le ell hOne a ha b
    (hardSliceSparseConstant b hb * Fintype.card V) h hh
    ((2 : ℝ) ^ (-(Fintype.card V : ℝ) / 4)) (Real.rpow_pos_of_pos (by norm_num) _))
  apply finiteProb_mono
  intro β hβ
  by_contra hnone
  apply hβ
  apply hardSliceSparseConstant_spec b hb V
  intro H _ hw hlen
  by_contra hfail
  exact hnone ⟨H, hw, hlen, lt_of_not_ge hfail⟩

theorem hash_coefficient_corr_failure_le {F V U : Type} [Field F]
    [Module BinaryAlgebra.F2 F] [Fintype F] [Fintype V]
    [Fintype U] [Nonempty U]
    (ell : F →ₗ[BinaryAlgebra.F2] BinaryAlgebra.F2) (hOne : ell 1 = 1)
    (a : U → Cube V → F) (b : ℕ) (hb : 1 ≤ b) (h : ℕ) (hh : 0 < h) :
    finiteProb (fun ω : U × (Fin (2 * h) → F) =>
      ¬ corr b (fun x => sign (Interpolation.acceptEval ell (2 * h) (a ω.1) ω.2 x)) ≤
        (2 : ℝ) ^ (-(Fintype.card V : ℝ) / 8)) ≤
      finiteProb (fun u => ¬ Function.Injective (a u)) +
        sparseMomentBound (Fintype.card V) b
          (hardSliceSparseConstant b hb * Fintype.card V) h
          ((2 : ℝ) ^ (-(Fintype.card V : ℝ) / 4)) := by
  let B := sparseMomentBound (Fintype.card V) b
    (hardSliceSparseConstant b hb * Fintype.card V) h
    ((2 : ℝ) ^ (-(Fintype.card V : ℝ) / 4))
  have hB : 0 ≤ B := sparseMomentBound_nonneg _ _ _ _ _
  change finiteAvg _ ≤ finiteProb _ + B
  rw [finiteAvg_product]
  calc
    _ ≤ finiteAvg (fun u : U => (if ¬ Function.Injective (a u) then 1 else 0) + B) := by
      apply finiteAvg_mono
      intro u
      by_cases hu : Function.Injective (a u)
      · simpa only [finiteProb, B, hu, not_true_eq_false, ite_false, zero_add] using
          coefficient_corr_failure_le ell hOne (a u) hu b hb h hh
      · have hone := finiteProb_le_one (fun β : Fin (2 * h) → F =>
          ¬ corr b (fun x => sign (Interpolation.acceptEval ell (2 * h) (a u) β x)) ≤
            (2 : ℝ) ^ (-(Fintype.card V : ℝ) / 8))
        simpa only [finiteProb, hu, not_false_eq_true, ite_true] using
          hone.trans (le_add_of_nonneg_right hB)
    _ = finiteProb (fun u => ¬ Function.Injective (a u)) + B := by
      rw [finiteAvg_add, finiteAvg_const]
      apply congrArg (fun z : ℝ => z + B)
      apply finiteAvg_congr
      intro u
      exact (ite_eq_ite _ _ _).mpr trivial

/-- Hash the data and encode the result in the polynomial quotient. -/
def encodedHash {d r : ℕ} (p : Fin r → Bool)
    (u : Fin (d + r - 1) → Bool) (x : Cube (Fin d)) : BinaryAlgebra.BitQuotient p :=
  BinaryAlgebra.encode (fun i => BinaryAlgebra.bitValue (p i))
    (fun i => BinaryAlgebra.bitValue (BinaryHash.hashBool u x i))

theorem encodedHash_fill_injective {d r : ℕ} (p : Fin r → Bool)
    (u : Fin (d + r - 1) → Bool) (σ : Restriction (Fin d))
    (hu : Function.Injective (fun z : Cube (Live σ) => BinaryHash.hashBool u (fill σ z))) :
    Function.Injective (fun z : Cube (Live σ) => encodedHash p u (fill σ z)) := by
  intro x y hxy
  apply hu
  apply (BinaryAlgebra.bitsEquivF2 (Fin r)).injective
  exact BinaryAlgebra.encode_injective _ hxy

/-- Evaluate the acceptance bit determined by a hash output. -/
def hashAcceptance {d r : ℕ} (p : Fin r → Bool)
    [Fact (Irreducible (BinaryAlgebra.inputPolynomialBits p))]
    (t : ℕ) (u : Fin (d + r - 1) → Bool)
    (β : Fin t → BinaryAlgebra.BitQuotient p) : Cube (Fin d) → Bool :=
  Interpolation.acceptEval
    (BinaryAlgebra.degreeZero (BinaryAlgebra.inputPolynomialBits_monic p)) t
    (encodedHash p u) β

theorem actual_hash_coefficient_failure_le {d r : ℕ} (p : Fin r → Bool)
    [Fact (Irreducible (BinaryAlgebra.inputPolynomialBits p))]
    (hr : 0 < r) (σ : Restriction (Fin d))
    (b : ℕ) (hb : 1 ≤ b) (h : ℕ) (hh : 0 < h) :
    finiteProb (fun ω : (Fin (d + r - 1) → Bool) ×
        (Fin (2 * h) → BinaryAlgebra.BitQuotient p) =>
      ¬ corr b (fun z => sign (hashAcceptance p (2 * h) ω.1 ω.2 (fill σ z))) ≤
        (2 : ℝ) ^ (-(Fintype.card (Live σ) : ℝ) / 8)) ≤
      (2 : ℝ) ^ Fintype.card (Live σ) / (2 : ℝ) ^ r +
        sparseMomentBound (Fintype.card (Live σ)) b
          (hardSliceSparseConstant b hb * Fintype.card (Live σ)) h
          ((2 : ℝ) ^ (-(Fintype.card (Live σ) : ℝ) / 4)) := by
  let : Field (BinaryAlgebra.BitQuotient p) :=
    AdjoinRoot.instField (f := BinaryAlgebra.inputPolynomialBits p)
  let : Module BinaryAlgebra.F2 (BinaryAlgebra.BitQuotient p) :=
    inferInstanceAs (Module BinaryAlgebra.F2
      (AdjoinRoot (BinaryAlgebra.inputPolynomialBits p)))
  have hOne : BinaryAlgebra.degreeZero (BinaryAlgebra.inputPolynomialBits_monic p)
      (1 : BinaryAlgebra.BitQuotient p) = 1 :=
    BinaryAlgebra.degreeZero_one _ (by simpa using hr)
  have hhash : finiteProb (fun u : Fin (d + r - 1) → Bool =>
      ¬ Function.Injective (fun z : Cube (Live σ) => encodedHash p u (fill σ z))) ≤
      (2 : ℝ) ^ Fintype.card (Live σ) / (2 : ℝ) ^ r := by
    apply le_trans _ (BinaryHash.hashBool_restriction_failure_le_pow (r := r) σ)
    apply finiteProb_mono
    intro u hu hinj
    exact hu (encodedHash_fill_injective p u σ hinj)
  exact (hash_coefficient_corr_failure_le (F := BinaryAlgebra.BitQuotient p)
    (V := Live σ) (U := Fin (d + r - 1) → Bool)
    (BinaryAlgebra.degreeZero (BinaryAlgebra.inputPolynomialBits_monic p)) hOne
    (fun u z => encodedHash p u (fill σ z)) b hb h hh).trans
      (add_le_add_left hhash _)

end DepthThreeLowerBound

end

end Complexity
