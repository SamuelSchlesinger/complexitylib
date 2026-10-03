/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Asymptotics
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Internal.Assembly
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Endpoint

/-!
# Bag bounds from a graph cut

The prescribed-endpoint theorem on each side and the transition between
their boundaries give the finite form of Fomin and Høie's Theorem 5.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition.Internal

open scoped Classical

private theorem degree_le_of_embedding {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ↪g H) (v : V) :
    G.degree v ≤ H.degree (e v) := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_le_of_embedding (e.mapNeighborSet v)

private theorem side_bound {a x b m n : Nat}
    (hx : x ≤ b) (ha : a ≤ m) (han : a ≤ n) :
    max x (a / 3 + 1) + Nat.clog 2 a + 1 ≤
      max b (m / 3 + 1) + Nat.clog 2 n + 1 := by
  have hdiv := Nat.div_le_div_right (c := 3) ha
  have hlog := Nat.clog_mono_right 2 han
  have hmax := max_le_max hx (Nat.add_le_add_right hdiv 1)
  lia

theorem exists_of_cut {W : Type} [Fintype W] (H : SimpleGraph W)
    (degree : ∀ v, H.degree v ≤ 3) (S : Finset W) :
    ∃ D : PathDecomposition H, ∀ i,
      (D.bag i).card ≤ max (H.cutFinset S).card (max S.card Sᶜ.card / 3 + 1) +
        Nat.clog 2 (Fintype.card W) + 1 := by
  have leftDegree (v : {w | w ∈ S}) : (H.induce {w | w ∈ S}).degree v ≤ 3 :=
    (degree_le_of_embedding (SimpleGraph.Embedding.induce _) v).trans (degree v)
  have rightDegree (v : {w | w ∉ S}) : (H.induce {w | w ∉ S}).degree v ≤ 3 :=
    (degree_le_of_embedding (SimpleGraph.Embedding.induce _) v).trans (degree v)
  obtain ⟨DL, leftEnd, leftBound⟩ := exists_subcubic_endsAt
    (H.induce {w | w ∈ S}) leftDegree ((cutBoundary H S).subtype (· ∈ S))
  obtain ⟨DR, rightEnd, rightBound⟩ := exists_subcubic_endsAt
    (H.induce {w | w ∉ S}) rightDegree ((cutBoundary H Sᶜ).subtype (· ∉ S))
  obtain ⟨DM, middleStart, middleEnd, middleBound⟩ := exists_between_cutBoundaries H S
  have leftCard : Fintype.card {w | w ∈ S} = S.card :=
    Fintype.card_of_finset' S (fun _ => Iff.rfl)
  have rightCard : Fintype.card {w | w ∉ S} = Sᶜ.card :=
    Fintype.card_of_finset' (p := {w | w ∉ S}) Sᶜ (fun _ => Finset.mem_compl)
  have leftSize : ((cutBoundary H S).subtype (· ∈ S)).card ≤ (H.cutFinset S).card := by
    rw [Finset.card_subtype]
    exact (Finset.card_filter_le _ _).trans (card_cutBoundary_le H S)
  have rightSize : ((cutBoundary H Sᶜ).subtype (· ∉ S)).card ≤ (H.cutFinset S).card := by
    rw [Finset.card_subtype]
    exact (Finset.card_filter_le _ _).trans
      ((card_cutBoundary_le H Sᶜ).trans_eq (congrArg Finset.card (cutFinset_compl H S)))
  apply exists_assemble_cut H S DL DM DR.reverse leftEnd middleStart middleEnd rightEnd.reverse
  · intro i
    apply (leftBound i).trans (side_bound leftSize ?_ (Fintype.card_subtype_le _))
    rw [leftCard]
    exact le_max_left _ _
  · intro i
    exact (middleBound i).trans (by lia)
  · intro i
    change (DR.bag i.rev).card ≤ _
    apply (rightBound i.rev).trans (side_bound rightSize ?_ (Fintype.card_subtype_le _))
    rw [rightCard]
    exact le_max_right _ _

theorem exists_of_balanced_cut {W : Type} [Fintype W] (H : SimpleGraph W)
    (degree : ∀ v, H.degree v ≤ 3) (S : Finset W)
    (leftSmall : S.card ≤ Sᶜ.card + 1) (rightSmall : Sᶜ.card ≤ S.card + 1) :
    ∃ D : PathDecomposition H, ∀ i,
      (D.bag i).card ≤ max (H.cutFinset S).card ((Fintype.card W + 1) / 6 + 1) +
        Nat.clog 2 (Fintype.card W) + 1 := by
  obtain ⟨D, bound⟩ := exists_of_cut H degree S
  refine ⟨D, fun i => (bound i).trans ?_⟩
  have hsum := Finset.card_compl_add_card S
  have hdiv : max S.card Sᶜ.card / 3 ≤ (Fintype.card W + 1) / 6 := by lia
  have hmax := max_le_max (le_refl (H.cutFinset S).card) (Nat.add_le_add_right hdiv 1)
  lia

theorem bisectionBound_coarse : BisectionBound (4 / 3) 0 := by
  intro W _ _ H _ regular _
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset W)) (n := Fintype.card W / 2)
    (by simpa only [Finset.card_univ] using Nat.div_le_self (Fintype.card W) 2)
  have hsum := Finset.card_compl_add_card S
  refine ⟨S, by lia, by lia, ?_⟩
  have hcut : (H.cutFinset S).card ≤ H.edgeFinset.card :=
    Finset.card_le_card (fun _ he => H.mem_edgeFinset.mpr ((H.mem_cutFinset).mp he).1)
  have hedges : Fintype.card W * 3 = 2 * H.edgeFinset.card := by
    simpa only [regular.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul] using
      H.sum_degrees_eq_twice_card_edges
  have hcutR : ((H.cutFinset S).card : ℝ) ≤ H.edgeFinset.card := by exact_mod_cast hcut
  have hedgesR : (Fintype.card W : ℝ) * 3 = 2 * H.edgeFinset.card := by
    exact_mod_cast hedges
  linarith

theorem exists_pathwidthBound {ξ δ : ℝ} {N₀ : Nat}
    (bisection : BisectionBound ξ N₀) (hξ : 0 ≤ ξ) (hδ : 0 < δ) :
    ∃ N₁ : Nat, PathwidthBound (ξ + δ) N₁ := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (eventually_clog_add_lt 2 hδ)
  refine ⟨max N₀ N, ?_⟩
  intro W _ _ H _ regular large
  obtain ⟨S, leftSmall, rightSmall, cutBound⟩ :=
    bisection W H regular (lt_of_le_of_lt (le_max_left _ _) large)
  obtain ⟨D, bound⟩ := @exists_of_balanced_cut W ‹Fintype W› H
    (fun v => by convert (regular.degree_eq v).le) S
    (by simpa only [Finset.card_compl] using leftSmall)
    (by simpa only [Finset.card_compl] using rightSmall)
  have smallLog := hN (Fintype.card W) (by lia)
  have hn : (0 : ℝ) ≤ Fintype.card W := Nat.cast_nonneg _
  have hξn := mul_nonneg hξ hn
  have divNat : 6 * ((Fintype.card W + 1) / 6) ≤ Fintype.card W + 1 := by lia
  have divReal : 6 * (((Fintype.card W + 1) / 6 : Nat) : ℝ) ≤ Fintype.card W + 1 := by
    exact_mod_cast divNat
  have hmax : ((max (H.cutFinset S).card ((Fintype.card W + 1) / 6 + 1) : Nat) : ℝ) ≤
      (1 / 6 + ξ) * Fintype.card W + 2 := by
    rw [Nat.cast_max]
    apply max_le (by linarith)
    push_cast
    nlinarith
  refine ⟨D, fun i => ?_⟩
  have bagBound : ((D.bag i).card : ℝ) ≤
      ((max (H.cutFinset S).card ((Fintype.card W + 1) / 6 + 1) : Nat) : ℝ) +
        (Nat.clog 2 (Fintype.card W) : ℝ) + 1 := by exact_mod_cast bound i
  nlinarith

end Algebraic.Cutwidth.PathDecomposition.Internal
