/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.CutBoundary

/-!
# Prefix cuts of a score order through a threshold grid

Every prefix of the score order lies between two consecutive threshold sets
`{X < a + i δ}`, or inside one of the two tails. With maximum degree three, its cut is
therefore at most the cut of the lower threshold set plus three times the number of
scores in the window, or three times the size of a tail.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

variable {W : Type} [Fintype W]

theorem scoreRank_injective (X : W → ℝ) : Function.Injective (scoreRank X) := by
  intro u v h
  have h' := congrArg (fun p => (ofLex p).2) h
  simp only [scoreRank, ofLex_toLex] at h'
  exact (Fintype.equivFin W).injective (Fin.ext h')

theorem scoreKey_lt_of_scoreRank_lt {X : W → ℝ} {u v : W}
    (h : scoreRank X u < scoreRank X v) : scoreKey X u < scoreKey X v := by
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨u, ?_, ?_⟩
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact hw.trans h
  · simpa using h
  · simp

theorem scoreKey_injective (X : W → ℝ) : Function.Injective (scoreKey X) := by
  intro u v h
  rcases lt_trichotomy (scoreRank X u) (scoreRank X v) with hlt | heq | hgt
  · exact absurd h (scoreKey_lt_of_scoreRank_lt hlt).ne
  · exact scoreRank_injective X heq
  · exact absurd h (scoreKey_lt_of_scoreRank_lt hgt).ne'

theorem scoreKey_lt_of_lt {X : W → ℝ} {u v : W} (h : X u < X v) :
    scoreKey X u < scoreKey X v :=
  scoreKey_lt_of_scoreRank_lt (Prod.Lex.lt_iff.mpr (Or.inl h))

variable [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- A cut has at most three edges per vertex of the side. -/
theorem card_cutFinset_le_three_mul (degree : ∀ v, H.degree v ≤ 3) (S : Finset W) :
    (H.cutFinset S).card ≤ 3 * S.card := by
  have hsub : H.cutFinset S ⊆ S.biUnion fun v => H.incidenceFinset v := by
    intro e he
    obtain ⟨hedge, a, b, rfl, ha, -⟩ := (H.mem_cutFinset).mp he
    exact Finset.mem_biUnion.mpr ⟨a, ha, by
      simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet] using hedge⟩
  calc (H.cutFinset S).card ≤ (S.biUnion fun v => H.incidenceFinset v).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ v ∈ S, (H.incidenceFinset v).card := Finset.card_biUnion_le
    _ = ∑ v ∈ S, H.degree v := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [SimpleGraph.card_incidenceFinset_eq_degree]
    _ ≤ ∑ _v ∈ S, 3 := Finset.sum_le_sum fun v _ => degree v
    _ = 3 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- Enlarging a side changes its cut by at most three edges per added vertex. -/
theorem card_cutFinset_le_of_subset (degree : ∀ v, H.degree v ≤ 3) {S T : Finset W}
    (hST : S ⊆ T) : (H.cutFinset T).card ≤ (H.cutFinset S).card + 3 * (T \ S).card := by
  have hsub : H.cutFinset T ⊆ H.cutFinset S ∪ H.cutFinset (T \ S) := by
    intro e he
    obtain ⟨hedge, a, b, rfl, ha, hb⟩ := (H.mem_cutFinset).mp he
    rw [Finset.mem_union]
    by_cases haS : a ∈ S
    · exact Or.inl ((H.mem_cutFinset).mpr ⟨hedge, a, b, rfl, haS, fun hbS => hb (hST hbS)⟩)
    · exact Or.inr ((H.mem_cutFinset).mpr ⟨hedge, a, b, rfl, Finset.mem_sdiff.mpr ⟨ha, haS⟩,
        fun hbTS => hb (Finset.mem_sdiff.mp hbTS).1⟩)
  calc (H.cutFinset T).card ≤ (H.cutFinset S ∪ H.cutFinset (T \ S)).card :=
        Finset.card_le_card hsub
    _ ≤ (H.cutFinset S).card + (H.cutFinset (T \ S)).card := Finset.card_union_le _ _
    _ ≤ (H.cutFinset S).card + 3 * (T \ S).card := by
        have := card_cutFinset_le_three_mul H degree (T \ S)
        omega

/-- **Grid bound for score prefixes.** Fix thresholds `a + i δ` for `i ≤ M`. If both
tails are small and each threshold cut plus three times its window is at most `B`, then
every prefix of the score order has at most `B` crossing edges. -/
theorem card_cutFinset_scoreKey_le (degree : ∀ v, H.degree v ≤ 3) (X : W → ℝ)
    {a δ : ℝ} (hδ : 0 < δ) (M : ℕ) {B : ℝ}
    (low : 3 * ((Finset.univ.filter fun v => X v < a).card : ℝ) ≤ B)
    (high : 3 * ((Finset.univ.filter fun v => a + M * δ ≤ X v).card : ℝ) ≤ B)
    (mid : ∀ i < M,
      ((H.cutFinset (Finset.univ.filter fun v => X v < a + i * δ)).card : ℝ) +
        3 * ((Finset.univ.filter fun v => a + i * δ ≤ X v ∧ X v < a + (i + 1) * δ).card : ℝ)
        ≤ B)
    (t : ℕ) :
    ((H.cutFinset (Finset.univ.filter fun w => scoreKey X w < t)).card : ℝ) ≤ B := by
  set P := Finset.univ.filter fun w => scoreKey X w < t with hP
  have memP : ∀ w, w ∈ P ↔ scoreKey X w < t := fun w => by simp [hP]
  have hB : 0 ≤ B := le_trans (by positivity) low
  -- Prefixes are lower sets for the score.
  have lower : ∀ {u v}, v ∈ P → X u < X v → u ∈ P := fun hv huv =>
    (memP _).mpr ((scoreKey_lt_of_lt huv).trans ((memP _).mp hv))
  rcases P.eq_empty_or_nonempty with hempty | hne
  · rw [hempty]
    have : H.cutFinset (∅ : Finset W) = ∅ := by
      ext e
      simp [SimpleGraph.mem_cutFinset]
    rw [this, Finset.card_empty, Nat.cast_zero]
    exact hB
  obtain ⟨v₀, hv₀, hmax⟩ := Finset.exists_max_image P X hne
  set τ := X v₀
  by_cases hlow : τ < a
  · -- The prefix lies in the lower tail.
    have hsub : P ⊆ Finset.univ.filter fun v => X v < a := by
      intro w hw
      simpa using (hmax w hw).trans_lt hlow
    have := card_cutFinset_le_three_mul H degree P
    have hcard := Finset.card_le_card hsub
    calc ((H.cutFinset P).card : ℝ) ≤ 3 * (P.card : ℝ) := by exact_mod_cast this
      _ ≤ 3 * ((Finset.univ.filter fun v => X v < a).card : ℝ) := by
          gcongr
      _ ≤ B := low
  by_cases hhigh : a + M * δ ≤ τ
  · -- The complement lies in the upper tail.
    have hsub : Pᶜ ⊆ Finset.univ.filter fun v => a + M * δ ≤ X v := by
      intro w hw
      simp only [Finset.mem_compl] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hlt
      exact hw (lower hv₀ (lt_of_lt_of_le (not_le.mp hlt) hhigh))
    have := card_cutFinset_le_three_mul H degree Pᶜ
    have hcompl : H.cutFinset Pᶜ = H.cutFinset P := by convert cutFinset_compl H P
    rw [hcompl] at this
    have hcard := Finset.card_le_card hsub
    calc ((H.cutFinset P).card : ℝ) ≤ 3 * (Pᶜ.card : ℝ) := by exact_mod_cast this
      _ ≤ 3 * ((Finset.univ.filter fun v => a + M * δ ≤ X v).card : ℝ) := by
          gcongr
      _ ≤ B := high
  -- The prefix lies between two consecutive thresholds.
  push Not at hlow hhigh
  set i := ⌊(τ - a) / δ⌋₊ with hi
  have hq : 0 ≤ (τ - a) / δ := div_nonneg (by linarith) hδ.le
  have hi_le : (i : ℝ) * δ ≤ τ - a := by
    have := Nat.floor_le hq
    rwa [le_div_iff₀ hδ] at this
  have hi_lt : τ - a < ((i : ℝ) + 1) * δ := by
    have := Nat.lt_floor_add_one ((τ - a) / δ)
    rwa [div_lt_iff₀ hδ] at this
  have hiM : i < M := by
    by_contra hge
    push Not at hge
    have : (M : ℝ) * δ ≤ i * δ := by gcongr
    linarith
  set L := Finset.univ.filter fun v => X v < a + i * δ
  have hLP : L ⊆ P := by
    intro w hw
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact lower hv₀ (by linarith)
  have hwindow : P \ L ⊆
      Finset.univ.filter fun v => a + i * δ ≤ X v ∧ X v < a + (i + 1) * δ := by
    intro w hw
    obtain ⟨hwP, hwL⟩ := Finset.mem_sdiff.mp hw
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hwL
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hwL, by linarith [hmax w hwP]⟩
  have key := card_cutFinset_le_of_subset H degree hLP
  have hcard := Finset.card_le_card hwindow
  calc ((H.cutFinset P).card : ℝ) ≤ (H.cutFinset L).card + 3 * ((P \ L).card : ℝ) := by
        exact_mod_cast key
    _ ≤ (H.cutFinset L).card + 3 *
          ((Finset.univ.filter fun v => a + i * δ ≤ X v ∧ X v < a + (i + 1) * δ).card : ℝ) := by
        gcongr
    _ ≤ B := mid i hiM

end Algebraic.Cutwidth.Gaussian.Internal
