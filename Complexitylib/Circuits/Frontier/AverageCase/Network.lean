/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.AverageCase.Sweep
public import Complexitylib.Circuits.Frontier.Compiler

/-!
# Coherent frontier traces of unambiguous networks

Uniqueness of satisfying edge assignments makes the separator lemma splice the entire
frontier trace. This supplies the stronger interface needed by weighted peeling.
-/

@[expose] public section

namespace Complexity.Frontier.Network

open Set

variable {U ι V E : Type*} (N : Network U ι V E) (π : Layout V) [Nonempty U]

/-- The sweep of a network with unique satisfying assignments preserves entire traces. -/
theorem sweep_coherent
    (hunique : ∀ x α β, N.Satisfies x α → N.Satisfies x β → α = β) :
    (N.sweep π).Coherent := by
  intro t x hx y hy hxy z hzx hzy
  change EqOn z x (N.revealedBy π t) at hzx
  change EqOn z y (N.revealedBy π t)ᶜ at hzy
  have hcut : EqOn (N.witness x) (N.witness y) (N.frontier π t) := by
    simpa only [sweep, frontierSweep, Prod.mk.injEq, true_and, frontierValues_eq_iff] using hxy
  by_cases ht : t ≤ Nat.card V
  · simp only [revealedBy, ht, ite_true] at hzx hzy
    obtain ⟨γ, hz, hnear, hfar⟩ :=
      (N.satisfies_witness hx).splice (N.satisfies_witness hy) hcut hzx hzy
    have hwz := hunique z (N.witness z) γ (N.satisfies_witness ⟨γ, hz⟩) hz
    constructor
    · intro u hu
      change ((), N.frontierValues π u (N.witness z)) = ((), N.frontierValues π u (N.witness x))
      refine Prod.ext rfl ?_
      apply (N.frontierValues_eq_iff π).2
      rw [hwz]
      intro e he
      apply hnear
      change (π (N.src e) : ℕ) < t ∨ (π (N.tgt e) : ℕ) < t
      change ¬((π (N.src e) : ℕ) < u ↔ (π (N.tgt e) : ℕ) < u) at he
      lia
    · intro u hu
      change ((), N.frontierValues π u (N.witness z)) = ((), N.frontierValues π u (N.witness y))
      refine Prod.ext rfl ?_
      apply (N.frontierValues_eq_iff π).2
      rw [hwz]
      intro e he
      by_cases hn : e ∈ N.touching (π.initial t)
      · apply (hnear hn).trans
        apply hcut
        change ¬((π (N.src e) : ℕ) < t ↔ (π (N.tgt e) : ℕ) < t)
        change (π (N.src e) : ℕ) < t ∨ (π (N.tgt e) : ℕ) < t at hn
        change ¬((π (N.src e) : ℕ) < u ↔ (π (N.tgt e) : ℕ) < u) at he
        lia
      · exact hfar hn
  · simp only [revealedBy, ht, ite_false] at hzx
    have hzx : z = x := funext fun i => hzx (mem_univ i)
    subst z
    refine ⟨fun _ _ => rfl, ?_⟩
    intro u hu
    have hu' : Nat.card V ≤ u := by lia
    change ((), N.frontierValues π u (N.witness x)) = ((), N.frontierValues π u (N.witness y))
    refine Prod.ext rfl ?_
    apply (N.frontierValues_eq_iff π).2
    rw [frontier, π.initial_of_card_le hu', Multigraph.cut_univ]
    exact eqOn_empty _ _

/-- The transition bound is independent of any rectangle or weight hypothesis. -/
theorem transitionCount_sweep_le [Finite ι] [Finite U] [Finite E]
    {w d m : ℕ} (hw : ∀ t, (N.frontier π t).ncard ≤ w) (hd : N.MaxDegreeLE d)
    (hm : ∀ v, (N.readAt v).ncard ≤ m) :
    (N.sweep π).transitionCount ≤
      Nat.card V * Nat.card U ^ (w + d + m) + Nat.card U ^ N.readᶜ.ncard := by
  have hq : 1 ≤ Nat.card U := Nat.card_pos
  -- The extra messages carry no information.
  have hunit : ∀ t, ((fun x => (((fun _ _ => ()) : ℕ → (ι → U) → Unit) t x,
      ((fun _ _ => ()) : ℕ → (ι → U) → Unit) (t + 1) x)) '' N.accepted).ncard ≤ 1 :=
    fun t => (ncard_le_one (toFinite _)).mpr fun a _ b _ => Subsingleton.elim a b
  unfold Sweep.transitionCount
  rw [show (N.sweep π).length = Nat.card V + 1 from rfl, Finset.sum_range_succ]
  refine add_le_add ?_ ((N.ncard_transition_last_le).trans ?_)
  · calc ∑ t ∈ Finset.range (Nat.card V), ((N.sweep π).transition t '' N.accepted).ncard
        ≤ ∑ _t ∈ Finset.range (Nat.card V), Nat.card U ^ (w + d + m) := by
          refine Finset.sum_le_sum fun t ht => ?_
          have ht : t < Nat.card V := Finset.mem_range.mp ht
          refine (N.ncard_transition_le ht).trans ?_
          refine (Nat.mul_le_mul_right _ (hunit t)).trans ?_
          rw [one_mul]
          refine Nat.pow_le_pow_right hq ?_
          -- The next frontier differs from this one only at the edges of the vertex processed.
          have hnext : N.frontier π (t + 1) ⊆ N.frontier π t ∪ N.edgesAt (π.symm ⟨t, ht⟩) := by
            rw [frontier, π.initial_succ ht]
            exact N.cut_insert_subset _ _
          have hC : (N.frontier π t ∪ N.frontier π (t + 1)).ncard ≤ w + d :=
            calc (N.frontier π t ∪ N.frontier π (t + 1)).ncard
                ≤ (N.frontier π t ∪ N.edgesAt (π.symm ⟨t, ht⟩)).ncard :=
                  ncard_le_ncard (union_subset subset_union_left hnext) (toFinite _)
              _ ≤ (N.frontier π t).ncard + (N.edgesAt (π.symm ⟨t, ht⟩)).ncard :=
                  ncard_union_le _ _
              _ ≤ w + d := add_le_add (hw t) (hd _)
          have := hm (π.symm ⟨t, ht⟩)
          lia
      _ = Nat.card V * Nat.card U ^ (w + d + m) := by simp
  · exact (Nat.mul_le_mul_right _ (hunit (Nat.card V))).trans (by rw [one_mul])

/-- Weighted peeling applied to the uniquely determined runs of a network. -/
theorem abs_sumOn_accepted_le [Finite ι] [Finite U] [Finite E]
    (hunique : ∀ x α β, N.Satisfies x α → N.Satisfies x β → α = β)
    {KL KR : ℕ} (hKL : 1 < KL) (hKR : 1 < KR)
    {weight cost : (ι → U) → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hweight : ∀ x, |weight x| ≤ a) (hc : ∀ x, 0 ≤ cost x)
    (hrect : RectangleBudget weight cost KL KR)
    {w d m : ℕ} (hw : ∀ t, (N.frontier π t).ncard ≤ w) (hd : N.MaxDegreeLE d)
    (hm : ∀ v, (N.readAt v).ncard ≤ m) :
    |sumOn weight N.accepted| ≤ sumOn cost N.accepted + a * ((KL - 1) * (KR - 1) *
      (Nat.card V * Nat.card U ^ (w + d + m) + Nat.card U ^ N.readᶜ.ncard) : ℕ) := by
  have H := (N.sweep π).abs_sumOn_le_of_budget (N.sweep_coherent π hunique)
    (Nat.succ_pos _) hKL hKR ha hweight hc hrect
  refine H.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ ha))
  exact_mod_cast Nat.mul_le_mul_left _ (N.transitionCount_sweep_le π hw hd hm)

end Complexity.Frontier.Network
