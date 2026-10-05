/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Tree
public import Complexitylib.Circuits.Frontier.Network
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.GCongr

/-!
# Constraint networks on trees of regions

Unique satisfying assignments make a laminar family of vertex separators coherent.
The capacity of a merge is the union of its three boundaries, together with the inputs
read at the merge. This construction assumes every input is read; unused inputs can be
handled separately by the existing unused-input bias bound.
-/

@[expose] public section

namespace Complexity.Frontier.Network

open Set

variable {U ι V E B : Type*} (G : Network U ι V E)

/-- Values on the boundary of an arbitrary vertex region. -/
noncomputable def boundaryValues (X : Set V) (α : E → U) : E → Option U := by
  classical
  exact fun e => if e ∈ G.cut X then some (α e) else none

theorem boundaryValues_eq_iff (X : Set V) (α β : E → U) :
    G.boundaryValues X α = G.boundaryValues X β ↔ EqOn α β (G.cut X) := by
  classical
  constructor
  · intro h e he
    have H := congrFun h e
    simpa [boundaryValues, he] using H
  · intro h
    funext e
    by_cases he : e ∈ G.cut X
    · simp [boundaryValues, he, h he]
    · simp [boundaryValues, he]

/-- Transfer a decomposition of vertices to the inputs read in its regions. -/
def readTree (T : RegionTree V B) (hread : G.read = univ) : RegionTree ι B where
  region v := G.readIn (T.region v)
  root := T.root
  region_root := by rw [T.region_root]; exact hread
  left := T.left
  right := T.right
  rank := T.rank
  left_subset v := by rintro i ⟨u, hu, hi⟩; exact ⟨u, T.left_subset v hu, hi⟩
  right_subset v := by rintro i ⟨u, hu, hi⟩; exact ⟨u, T.right_subset v hu, hi⟩
  disjoint v := by
    apply disjoint_left.mpr
    rintro i ⟨u, hu, hiu⟩ ⟨w, hw, hiw⟩
    have he := Option.some_injective _ (hiu.symm.trans hiw)
    subst w
    exact disjoint_left.mp (T.disjoint v) hu hw
  left_lt v := (T.left_lt v).imp (fun h => by rw [h, G.readIn_empty]) id
  right_lt v := (T.right_lt v).imp (fun h => by rw [h, G.readIn_empty]) id

variable [Nonempty U] (T : RegionTree V B) (hread : G.read = univ)

/-- A region tree gives network messages by restricting the canonical satisfying trace. -/
noncomputable def treeFrontier : TreeFrontier G.accepted (E → Option U) B where
  toRegionTree := G.readTree T hread
  message v x := G.boundaryValues (T.region v) (G.witness x)
  message_root x _ y _ := by
    apply (G.boundaryValues_eq_iff (T.region T.root) _ _).mpr
    rw [T.region_root, Multigraph.cut_univ]
    exact eqOn_empty _ _
  splice v x hx y hy hxy z hzx hzy := by
    have hcut := (G.boundaryValues_eq_iff _ _ _).mp hxy
    obtain ⟨γ, hz, _, _⟩ := (G.satisfies_witness hx).splice (G.satisfies_witness hy) hcut hzx hzy
    exact ⟨γ, hz⟩

/-- Laminarity is what makes arbitrary region-state deletion preserve the network trace. -/
theorem treeFrontier_coherent
    (hlam : ∀ u v, T.region u ⊆ T.region v ∨ T.region v ⊆ T.region u ∨
      Disjoint (T.region u) (T.region v))
    (hunique : ∀ x α β, G.Satisfies x α → G.Satisfies x β → α = β) :
    (G.treeFrontier T hread).Coherent := by
  intro v x hx y hy hxy z hzx hzy
  have hcut := (G.boundaryValues_eq_iff _ _ _).mp hxy
  obtain ⟨γ, hz, hnear, hfar⟩ :=
    (G.satisfies_witness hx).splice (G.satisfies_witness hy) hcut hzx hzy
  have he := hunique z (G.witness z) γ (G.satisfies_witness ⟨γ, hz⟩) hz
  have hleft (u : B) (hu : T.region u ⊆ T.region v) :
      (G.treeFrontier T hread).message u z = (G.treeFrontier T hread).message u x := by
    apply (G.boundaryValues_eq_iff _ _ _).mpr
    rw [he]
    intro e he
    apply hnear
    have h := he
    change ¬(G.src e ∈ T.region u ↔ G.tgt e ∈ T.region u) at h
    change G.src e ∈ T.region v ∨ G.tgt e ∈ T.region v
    by_cases hs : G.src e ∈ T.region u
    · exact Or.inl (hu hs)
    · exact Or.inr (hu (by tauto))
  refine ⟨hleft v Subset.rfl, fun u => ?_⟩
  rcases hlam u v with huv | hvu | hdis
  · exact Or.inl (hleft u huv)
  all_goals
    right
    apply (G.boundaryValues_eq_iff _ _ _).mpr
    rw [he]
    intro e he
    by_cases hn : e ∈ G.touching (T.region v)
    · apply (hnear hn).trans
      apply hcut
      change ¬(G.src e ∈ T.region v ↔ G.tgt e ∈ T.region v)
      change G.src e ∈ T.region v ∨ G.tgt e ∈ T.region v at hn
      change ¬(G.src e ∈ T.region u ↔ G.tgt e ∈ T.region u) at he
      first
      | have hs := @hvu (G.src e); have ht := @hvu (G.tgt e); tauto
      | have hs : ¬(G.src e ∈ T.region u ∧ G.src e ∈ T.region v) :=
          fun h => disjoint_left.mp hdis h.1 h.2
        have ht : ¬(G.tgt e ∈ T.region u ∧ G.tgt e ∈ T.region v) :=
          fun h => disjoint_left.mp hdis h.1 h.2
        tauto
    · exact hfar hn

/-- The number of joint merge states, with each edge in the boundary union paid once. -/
theorem ncard_tree_transition_le [Finite ι] [Finite U] [Finite E] (v : B) :
    ((G.treeFrontier T hread).transition v '' G.accepted).ncard ≤
      Nat.card U ^ ((G.cut (T.region v) ∪ G.cut (T.region (T.left v)) ∪
        G.cut (T.region (T.right v))).ncard + ((G.treeFrontier T hread).localInputs v).ncard) := by
  let P := G.treeFrontier T hread
  let C := G.cut (T.region v) ∪ G.cut (T.region (T.left v)) ∪ G.cut (T.region (T.right v))
  let Q := P.localInputs v
  let code (x : ι → U) := (C.domRestrict (G.witness x), Q.domRestrict x)
  calc (P.transition v '' G.accepted).ncard ≤ (code '' G.accepted).ncard := by
        refine ncard_image_le_ncard_image_of_determines (toFinite _) _ _ fun x _ y _ h => ?_
        simp only [code, Prod.mk.injEq, domRestrict_eq_domRestrict_iff] at h
        simp only [TreeFrontier.transition, Prod.mk.injEq, domRestrict_eq_domRestrict_iff]
        exact ⟨(G.boundaryValues_eq_iff _ _ _).mpr (h.1.mono (fun _ he => Or.inl (Or.inl he))),
          (G.boundaryValues_eq_iff _ _ _).mpr (h.1.mono (fun _ he => Or.inl (Or.inr he))),
          (G.boundaryValues_eq_iff _ _ _).mpr (h.1.mono (fun _ he => Or.inr he)), h.2⟩
    _ ≤ (univ : Set ((C → U) × (Q → U))).ncard := ncard_le_ncard (subset_univ _)
    _ = _ := by rw [ncard_univ, Nat.card_prod, Nat.card_fun, Nat.card_fun,
                  Nat.card_coe_set_eq, Nat.card_coe_set_eq, ← pow_add]

/-- **Weighted tree bound for networks.** The exponent is the joint merge boundary, not
the maximum of the three separate separator sizes. -/
theorem abs_sumOn_accepted_le_tree [Finite ι] [Finite U] [Finite E] [Fintype B]
    (hlam : ∀ u v, T.region u ⊆ T.region v ∨ T.region v ⊆ T.region u ∨
      Disjoint (T.region u) (T.region v))
    (hunique : ∀ x α β, G.Satisfies x α → G.Satisfies x β → α = β)
    {K : ℕ} (hK : 1 < K) {w cost : (ι → U) → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hw : ∀ x, |w x| ≤ a) (hc : ∀ x, 0 ≤ cost x)
    (hrect : RectangleBudget w cost K K) :
    |sumOn w G.accepted| ≤ sumOn cost G.accepted + a * ((K - 1) ^ 3 *
      ∑ v, Nat.card U ^ ((G.cut (T.region v) ∪ G.cut (T.region (T.left v)) ∪
        G.cut (T.region (T.right v))).ncard +
          ((G.treeFrontier T hread).localInputs v).ncard) : ℕ) := by
  refine ((G.treeFrontier T hread).abs_sumOn_le_of_budget
    (G.treeFrontier_coherent T hread hlam hunique) hK ha hw hc hrect).trans ?_
  gcongr
  exact Finset.sum_le_sum fun v _ => G.ncard_tree_transition_le T hread v

end Complexity.Frontier.Network
