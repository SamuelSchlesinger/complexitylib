/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Internal

/-!
# Pathwidth from a cubic bisection bound

This completes the reduction in Fomin and Høie's *Pathwidth of cubic graphs
and exact algorithms* (2006), Theorem 5. For any cut of a subcubic graph,
the decompositions of its sides and their boundary graph concatenate with
the explicit finite bound below. For balanced cuts, every positive linear
slack absorbs the logarithmic remainder.

`Bisection.Helpful` proves the Monien–Preis theorem asserting
`BisectionBound ξ N₀` for every positive `ξ` and some `N₀`, then applies
this reduction to obtain the sharp pathwidth bound.
-/

@[expose] public section

namespace Algebraic.Cutwidth

open scoped Classical

/-- Decompose both sides of any cut and join them through their boundaries.
This bound requires only maximum degree three, with no bisection hypothesis. -/
theorem PathDecomposition.exists_of_cut {W : Type} [Fintype W] (H : SimpleGraph W)
    (degree : ∀ v, H.degree v ≤ 3) (S : Finset W) :
    ∃ D : PathDecomposition H, ∀ i,
      (D.bag i).card ≤ max (H.cutFinset S).card (max S.card Sᶜ.card / 3 + 1) +
        Nat.clog 2 (Fintype.card W) + 1 :=
  Internal.exists_of_cut H degree S

/-- For a balanced cut, each side contributes at most one sixth of the
total vertex count, rounded as indicated, plus the logarithmic remainder. -/
theorem PathDecomposition.exists_of_balanced_cut {W : Type} [Fintype W] (H : SimpleGraph W)
    (degree : ∀ v, H.degree v ≤ 3) (S : Finset W)
    (leftSmall : S.card ≤ Sᶜ.card + 1) (rightSmall : Sᶜ.card ≤ S.card + 1) :
    ∃ D : PathDecomposition H, ∀ i,
      (D.bag i).card ≤ max (H.cutFinset S).card ((Fintype.card W + 1) / 6 + 1) +
        Nat.clog 2 (Fintype.card W) + 1 :=
  Internal.exists_of_balanced_cut H degree S leftSmall rightSmall

/-- Every cubic graph admits a balanced cut of size at most `3n/2`, simply
because this counts all its edges. This coarse instance is unconditional. -/
theorem bisectionBound_coarse : BisectionBound (4 / 3) 0 :=
  PathDecomposition.Internal.bisectionBound_coarse

/-- Increasing the slack and the size threshold weakens the bisection bound. -/
theorem BisectionBound.mono {ξ ξ' : ℝ} {N₀ N₁ : Nat} (h : BisectionBound ξ N₀)
    (hξ : ξ ≤ ξ') (hN : N₀ ≤ N₁) : BisectionBound ξ' N₁ := by
  intro W _ _ H _ regular large
  obtain ⟨S, hleft, hright, hcut⟩ := h W H regular (hN.trans_lt large)
  refine ⟨S, hleft, hright, hcut.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

/-- Every positive additional slack absorbs the finite decomposition's
logarithmic remainder. The bisection theorem is the only graph hypothesis. -/
theorem BisectionBound.exists_pathwidthBound {ξ δ : ℝ} {N₀ : Nat}
    (bisection : BisectionBound ξ N₀) (hξ : 0 ≤ ξ) (hδ : 0 < δ) :
    ∃ N₁ : Nat, PathwidthBound (ξ + δ) N₁ :=
  PathDecomposition.Internal.exists_pathwidthBound bisection hξ hδ

/-- The sharp asymptotic bisection theorem implies the sharp asymptotic
cubic pathwidth theorem. Half the slack pays for the logarithmic remainder. -/
theorem pathwidthBound_of_bisectionBound
    (bisection : ∀ ξ : ℝ, 0 < ξ → ∃ N₀ : Nat, BisectionBound ξ N₀) :
    ∀ ξ : ℝ, 0 < ξ → ∃ N₁ : Nat, PathwidthBound ξ N₁ := by
  intro ξ hξ
  obtain ⟨N₀, cut⟩ := bisection (ξ / 2) (by positivity)
  obtain ⟨N₁, bound⟩ := cut.exists_pathwidthBound (by positivity) (δ := ξ / 2) (by positivity)
  refine ⟨N₁, ?_⟩
  rwa [show ξ / 2 + ξ / 2 = ξ by ring] at bound

end Algebraic.Cutwidth
