/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.MomentBounds
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.FiniteProbabilityBounds
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.SparseTestCodes
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.InterpolationSigns

/-!
# Unrestricted depth-three lower bound: hard slice moment

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/HardSliceMoment.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3 uDepth4 uDepth5 uDepth6 uDepth7 uDepth8 uDepth9 uDepth10

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

theorem finiteProb_abs_avg_gt_le {Ω : Type uDepth1} {Z : Type uDepth2} [Fintype Ω] [Nonempty Ω]
    [Fintype Z] [Nonempty Z] [DecidableEq Z]
    (h : ℕ) (hh : 0 < h) (bits : Ω → Z → Bool)
    (hdist : UniformBitsUpTo (2 * h) bits) (J : Z → Bool)
    (δ : ℝ) (hδ : 0 < δ) :
    finiteProb (fun ω => δ < |finiteAvg (fun z => sign (bits ω z) * indicator (J z))|) ≤
      (((2 * h : ℕ) : ℝ) ^ (2 * h) * (Fintype.card Z : ℝ) ^ h) /
        (δ * (Fintype.card Z : ℝ)) ^ (2 * h) := by
  have hN : 0 < (Fintype.card Z : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnorm (ω : Ω) :
      |finiteAvg (fun z => sign (bits ω z) * indicator (J z))| =
        |∑ z, sign (bits ω z) * indicator (J z)| / (Fintype.card Z : ℝ) := by
    rw [finiteAvg, abs_mul, abs_inv, abs_of_nonneg hN.le, div_eq_inv_mul]
  have hevent :
      finiteProb (fun ω => δ < |finiteAvg (fun z => sign (bits ω z) * indicator (J z))|) ≤
      finiteProb (fun ω => δ * (Fintype.card Z : ℝ) <
        |∑ z, sign (bits ω z) * indicator (J z)|) := by
    apply finiteProb_mono
    intro ω hω
    rw [hnorm ω] at hω
    exact (lt_div_iff₀ hN).mp hω
  exact hevent.trans (finiteProb_abs_gt_le_moment
    (fun ω => ∑ z, sign (bits ω z) * indicator (J z))
    (2 * h) (Nat.mul_pos (by decide) hh)
    (δ * (Fintype.card Z : ℝ))
    (((2 * h : ℕ) : ℝ) ^ (2 * h) * (Fintype.card Z : ℝ) ^ h)
    (mul_pos hδ hN) (even_moment_le_manuscript h bits hdist J))

/-- The moment estimate used to control sparse-CNF correlations. -/
def sparseMomentBound (m b L h : ℕ) (δ : ℝ) : ℝ :=
  ((((2 * m + 1) ^ b + 1) ^ L : ℕ) : ℝ) *
    ((((2 * h : ℕ) : ℝ) ^ (2 * h) * ((2 ^ m : ℕ) : ℝ) ^ h) /
      (δ * ((2 ^ m : ℕ) : ℝ)) ^ (2 * h))

theorem finiteProb_sparse_codes_gt_le {Ω : Type uDepth3} {V : Type uDepth4} [Fintype Ω] [Nonempty Ω]
    [Fintype V] (b L h : ℕ) (hh : 0 < h)
    (bits : Ω → Cube V → Bool) (hdist : UniformBitsUpTo (2 * h) bits)
    (δ : ℝ) (hδ : 0 < δ) :
    finiteProb (fun ω => ∃ c : SparseTestCode V b L,
      δ < |finiteAvg (fun x => sign (bits ω x) * indicator (c.eval x))|) ≤
      sparseMomentBound (Fintype.card V) b L h δ := by
  let P : SparseTestCode V b L → Ω → Prop := fun c ω =>
    δ < |finiteAvg (fun x => sign (bits ω x) * indicator (c.eval x))|
  let B : ℝ :=
    (((2 * h : ℕ) : ℝ) ^ (2 * h) * (Fintype.card (Cube V) : ℝ) ^ h) /
      (δ * (Fintype.card (Cube V) : ℝ)) ^ (2 * h)
  have hsingle (c : SparseTestCode V b L) : finiteProb (P c) ≤ B :=
    finiteProb_abs_avg_gt_le h hh bits hdist c.eval δ hδ
  calc
    _ ≤ ∑ c : SparseTestCode V b L, finiteProb (P c) := by
      simpa only [P, Finset.mem_univ, true_and] using
        (finiteProb_exists_le_sum (Finset.univ : Finset (SparseTestCode V b L)) P)
    _ ≤ ∑ _c : SparseTestCode V b L, B :=
      Finset.sum_le_sum (fun c _ => hsingle c)
    _ = (Fintype.card (SparseTestCode V b L) : ℝ) * B := by
      simp [nsmul_eq_mul]
    _ = sparseMomentBound (Fintype.card V) b L h δ := by
      simp [B, sparseMomentBound, Cube,
        Fintype.card_bool, mul_comm]

theorem finiteProb_sparse_cnfs_gt_le {Ω : Type uDepth5} {V : Type uDepth6} [Fintype Ω] [Nonempty Ω]
    [Fintype V] (b L h : ℕ) (hh : 0 < h)
    (bits : Ω → Cube V → Bool) (hdist : UniformBitsUpTo (2 * h) bits)
    (δ : ℝ) (hδ : 0 < δ) :
    finiteProb (fun ω => ∃ H : CNF V, H.WidthAtMost b ∧ H.length ≤ L ∧
      δ < |finiteAvg (fun x => sign (bits ω x) * indicator (H.eval x))|) ≤
      sparseMomentBound (Fintype.card V) b L h δ := by
  apply le_trans _ (finiteProb_sparse_codes_gt_le b L h hh bits hdist δ hδ)
  apply finiteProb_mono
  rintro ω ⟨H, hw, hlen, hbad⟩
  obtain ⟨c, hc⟩ := SparseTestCode.exists_eval_eq H hw hlen
  refine ⟨c, ?_⟩
  simpa only [hc] using hbad

theorem acceptEval_uniformBitsUpTo {F : Type uDepth7} {Z : Type uDepth8} [Field F]
    [Module BinaryAlgebra.F2 F] [Fintype F] [DecidableEq Z]
    (ell : F →ₗ[BinaryAlgebra.F2] BinaryAlgebra.F2) (hOne : ell 1 = 1)
    (t : ℕ) (a : Z → F) (ha : Function.Injective a) :
    UniformBitsUpTo t (Interpolation.acceptEval ell t a) := by
  intro s hs Φ
  exact Interpolation.finiteAvg_acceptEval_finset ell hOne a s hs
    (fun _ _ _ _ hxy => ha hxy) Φ

theorem coefficient_sparse_cnfs_gt_le {F : Type uDepth9} {V : Type uDepth10} [Field F]
    [Module BinaryAlgebra.F2 F] [Fintype F] [Fintype V]
    (ell : F →ₗ[BinaryAlgebra.F2] BinaryAlgebra.F2) (hOne : ell 1 = 1)
    (a : Cube V → F) (ha : Function.Injective a)
    (b L h : ℕ) (hh : 0 < h) (δ : ℝ) (hδ : 0 < δ) :
    finiteProb (fun β : Fin (2 * h) → F =>
      ∃ H : CNF V, H.WidthAtMost b ∧ H.length ≤ L ∧
        δ < |finiteAvg (fun x =>
          sign (Interpolation.acceptEval ell (2 * h) a β x) * indicator (H.eval x))|) ≤
      sparseMomentBound (Fintype.card V) b L h δ := by
  exact finiteProb_sparse_cnfs_gt_le b L h hh _
    (acceptEval_uniformBitsUpTo ell hOne (2 * h) a ha) δ hδ

end DepthThreeLowerBound

end

end Complexity
