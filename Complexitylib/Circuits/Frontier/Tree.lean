/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.AverageCase.Sweep
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Frontiers on a tree of regions

A binary decomposition pays for the joint boundary states at each merge, rather than for
the largest individual separator. Threshold charging now uses the two child interiors and
the parent exterior. This costs `(K - 1)^3` per merge, still subexponential when `K` is.
The weighted version uses the same disjoint peeling idea as the linear sweep.
-/

@[expose] public section

namespace Complexity.Frontier

open Set

variable {ι U M N : Type*}

/-- A finite binary region decomposition. Empty children serve as leaves; every nonempty
child has smaller rank. Inputs not in either child are read at the current node. -/
structure RegionTree (ι N : Type*) where
  /-- The inputs of each node's region. -/
  region : N → Set ι
  /-- The root node, whose region is everything. -/
  root : N
  region_root : region root = univ
  /-- The left child of a node. -/
  left : N → N
  /-- The right child of a node. -/
  right : N → N
  /-- A rank that decreases at every nonempty child. -/
  rank : N → ℕ
  left_subset : ∀ v, region (left v) ⊆ region v
  right_subset : ∀ v, region (right v) ⊆ region v
  disjoint : ∀ v, Disjoint (region (left v)) (region (right v))
  left_lt : ∀ v, region (left v) = ∅ ∨ rank (left v) < rank v
  right_lt : ∀ v, region (right v) = ∅ ∨ rank (right v) < rank v

/-- Splicing messages on a binary tree of input regions. -/
structure TreeFrontier (S : Set (ι → U)) (M N : Type*) extends RegionTree ι N where
  /-- The message of each node, a function of the whole input. -/
  message : N → (ι → U) → M
  message_root : ∀ x ∈ S, ∀ y ∈ S, message root x = message root y
  splice : ∀ v, ∀ x ∈ S, ∀ y ∈ S, message v x = message v y →
    ∀ z, EqOn z x (region v) → EqOn z y (region v)ᶜ → z ∈ S

namespace TreeFrontier

variable {S : Set (ι → U)} (P : TreeFrontier S M N)

/-- The inputs of `S` sending the same message at `v` as `x`. -/
def peers (v : N) (x : ι → U) : Set (ι → U) := {y ∈ S | P.message v y = P.message v x}

/-- The restrictions of the peers of `x` at `v` to the region of `v`. -/
def inside (v : N) (x : ι → U) : Set (P.region v → U) :=
  (P.region v).domRestrict '' P.peers v x

/-- The restrictions of the peers of `x` at `v` to the complement of the region of `v`. -/
def outside (v : N) (x : ι → U) : Set (↥(P.region v)ᶜ → U) :=
  (P.region v)ᶜ.domRestrict '' P.peers v x

/-- The inputs of the region of `v` in neither child region: those read at `v` itself. -/
def localInputs (v : N) : Set ι := P.region v \ (P.region (P.left v) ∪ P.region (P.right v))

/-- A merge includes all three messages, together with inputs read locally. -/
def transition (v : N) (x : ι → U) : M × M × M × (P.localInputs v → U) :=
  (P.message v x, P.message (P.left v) x, P.message (P.right v) x,
    (P.localInputs v).domRestrict x)

/-- The number of distinct merge transitions realized by `S`, summed over all nodes. -/
noncomputable def transitionCount [Fintype N] : ℕ := ∑ v, (P.transition v '' S).ncard

/-- A splice stays in the shared class and inherits each other message from a parent.
Laminar network separators with unique satisfying assignments have this property. -/
def Coherent : Prop :=
  ∀ v, ∀ x ∈ S, ∀ y ∈ S, P.message v x = P.message v y →
    ∀ z, EqOn z x (P.region v) → EqOn z y (P.region v)ᶜ →
      P.message v z = P.message v x ∧
      ∀ u, P.message u z = P.message u x ∨ P.message u z = P.message u y

theorem Coherent.peers_eq_rectangle (hP : P.Coherent) (v : N) (x : ι → U) :
    P.peers v x = rectangle (P.region v) (P.inside v x) (P.outside v x) := by
  apply subset_antisymm
  · intro y hy
    exact ⟨⟨y, hy, rfl⟩, ⟨y, hy, rfl⟩⟩
  · rintro z ⟨⟨a, ha, haz⟩, ⟨b, hb, hbz⟩⟩
    have hab := ha.2.trans hb.2.symm
    have hza := (domRestrict_eq_domRestrict_iff.mp haz).symm
    have hzb := (domRestrict_eq_domRestrict_iff.mp hbz).symm
    exact ⟨P.splice v a ha.1 b hb.1 hab z hza hzb,
      ((hP v a ha.1 b hb.1 hab z hza hzb).1).trans ha.2⟩

/-- Delete the peers of `x` at `v` from a coherent tree frontier. -/
def erase (hP : P.Coherent) (v : N) (x : ι → U) :
    TreeFrontier (S \ P.peers v x) M N where
  toRegionTree := P.toRegionTree
  message := P.message
  message_root a ha b hb := P.message_root a ha.1 b hb.1
  splice u a ha b hb hab z hza hzb := by
    refine ⟨P.splice u a ha.1 b hb.1 hab z hza hzb, fun hz => ?_⟩
    rcases (hP u a ha.1 b hb.1 hab z hza hzb).2 v with h | h
    · exact ha.2 ⟨ha.1, h.symm.trans hz.2⟩
    · exact hb.2 ⟨hb.1, h.symm.trans hz.2⟩

theorem Coherent.erase (hP : P.Coherent) (v : N) (x : ι → U) :
    (P.erase hP v x).Coherent := by
  intro u a ha b hb hab z hza hzb
  exact hP u a ha.1 b hb.1 hab z hza hzb

theorem transitionCount_erase_le [Finite ι] [Finite U] [Fintype N]
    (hP : P.Coherent) (v : N) (x : ι → U) :
    (P.erase hP v x).transitionCount ≤ P.transitionCount := by
  refine Finset.sum_le_sum fun u _ => ?_
  exact ncard_le_ncard (image_mono sdiff_subset) ((toFinite S).image _)

theorem ncard_inside_empty_le {v : N} (hv : P.region v = ∅) (x : ι → U) :
    (P.inside v x).ncard ≤ 1 := by
  have : Subsingleton (P.region v → U) :=
    ⟨fun a b => funext fun i => absurd i.2 (by simp [hv])⟩
  exact (ncard_le_one (toFinite _)).mpr fun a _ b _ => Subsingleton.elim a b

theorem ncard_inside_root {x : ι → U} (hx : x ∈ S) :
    (P.inside P.root x).ncard = S.ncard := by
  have he : P.peers P.root x = S :=
    subset_antisymm (fun _ hy => hy.1) fun y hy => ⟨hy, P.message_root y hy x hx⟩
  rw [inside, he]
  refine ncard_image_of_injective _ fun a b h => funext fun i => ?_
  exact domRestrict_eq_domRestrict_iff.mp h (by simp [P.region_root])

/-- A minimal-rank region with a large interior has two small child interiors. -/
theorem exists_critical {K : ℕ} (hK : 1 < K) (hS : K ≤ S.ncard)
    {x : ι → U} (hx : x ∈ S) :
    ∃ v, K ≤ (P.inside v x).ncard ∧ (P.inside (P.left v) x).ncard < K ∧
      (P.inside (P.right v) x).ncard < K := by
  classical
  have hex : ∃ r, ∃ v, P.rank v = r ∧ K ≤ (P.inside v x).ncard :=
    ⟨_, P.root, rfl, (P.ncard_inside_root hx).symm ▸ hS⟩
  obtain ⟨v, hv, hlarge⟩ := Nat.find_spec hex
  have hsmall (u : N) (h : P.region u = ∅ ∨ P.rank u < P.rank v) :
      (P.inside u x).ncard < K := by
    rcases h with h | h
    · exact (P.ncard_inside_empty_le h x).trans_lt hK
    · by_contra! hu
      exact Nat.find_min hex (hv ▸ h) ⟨u, rfl, hu⟩
  exact ⟨v, hlarge, hsmall _ (P.left_lt v), hsmall _ (P.right_lt v)⟩

/-- **Tree threshold charging.** Only the actual number of joint merge states is charged. -/
theorem ncard_le_of_small_sides [Finite ι] [Finite U] [Fintype N] {K : ℕ}
    (hK : 1 < K) (hS : K ≤ S.ncard)
    (hsmall : ∀ v, ∀ x ∈ S, (P.inside v x).ncard < K ∨ (P.outside v x).ncard < K) :
    S.ncard ≤ (K - 1) ^ 3 * P.transitionCount := by
  classical
  choose node hnode using fun x : S => P.exists_critical hK hS x.property
  let charge (x : ι → U) : N := if hx : x ∈ S then node ⟨x, hx⟩ else P.root
  have hcharge (x : ι → U) (hx : x ∈ S) :
      K ≤ (P.inside (charge x) x).ncard ∧
        (P.inside (P.left (charge x)) x).ncard < K ∧
        (P.inside (P.right (charge x)) x).ncard < K := by
    have he : charge x = node ⟨x, hx⟩ := dite_eq_left hx
    rw [he]
    exact hnode ⟨x, hx⟩
  have hsplit : S.ncard = ∑ v, (S ∩ charge ⁻¹' {v}).ncard := by
    let s := (toFinite S).toFinset
    have h := Finset.card_eq_sum_card_fiberwise (f := charge) (s := s)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    rw [← ncard_eq_toFinset_card] at h
    refine h.trans (Finset.sum_congr rfl fun v _ => ?_)
    rw [← ncard_coe_finset]
    congr 1
    ext x
    simp [s]
  rw [hsplit, transitionCount, Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  refine (ncard_le_mul_ncard_image (toFinite _) (P.transition v) _ fun τ => ?_).trans
    (Nat.mul_le_mul_left _ (ncard_le_ncard (image_mono inter_subset_left)))
  rcases (S ∩ charge ⁻¹' {v} ∩ P.transition v ⁻¹' {τ}).eq_empty_or_nonempty with he | ⟨x, hx⟩
  · simp [he]
  obtain ⟨⟨hxS, hxv⟩, hxτ⟩ := hx
  have hc := hcharge x hxS
  change charge x = v at hxv
  rw [hxv] at hc
  have hout : (P.outside v x).ncard ≤ K - 1 := by
    rcases hsmall v x hxS with h | h <;> lia
  calc (S ∩ charge ⁻¹' {v} ∩ P.transition v ⁻¹' {τ}).ncard
      ≤ (P.inside (P.left v) x ×ˢ P.inside (P.right v) x ×ˢ P.outside v x).ncard := by
        refine ncard_le_ncard_of_injOn
          (fun y => ((P.region (P.left v)).domRestrict y,
            (P.region (P.right v)).domRestrict y, (P.region v)ᶜ.domRestrict y)) ?_ ?_ (toFinite _)
        · rintro y ⟨⟨hyS, _⟩, hyτ⟩
          have H := hyτ.trans hxτ.symm
          simp only [transition, Prod.mk.injEq] at H
          exact ⟨⟨y, ⟨hyS, H.2.1⟩, rfl⟩, ⟨y, ⟨hyS, H.2.2.1⟩, rfl⟩,
            ⟨y, ⟨hyS, H.1⟩, rfl⟩⟩
        · rintro y ⟨⟨_, _⟩, hyτ⟩ z ⟨⟨_, _⟩, hzτ⟩ hyz
          simp only [Prod.mk.injEq, domRestrict_eq_domRestrict_iff] at hyz
          have H := hyτ.trans hzτ.symm
          simp only [transition, Prod.mk.injEq, domRestrict_eq_domRestrict_iff] at H
          funext i
          by_cases hl : i ∈ P.region (P.left v)
          · exact hyz.1 hl
          by_cases hr : i ∈ P.region (P.right v)
          · exact hyz.2.1 hr
          by_cases hv : i ∈ P.region v
          · exact H.2.2.2 ⟨hv, fun h => h.elim hl hr⟩
          · exact hyz.2.2 hv
    _ = (P.inside (P.left v) x).ncard *
        ((P.inside (P.right v) x).ncard * (P.outside v x).ncard) := by rw [ncard_prod, ncard_prod]
    _ ≤ (K - 1) * ((K - 1) * (K - 1)) :=
      Nat.mul_le_mul (by lia) (Nat.mul_le_mul (by lia) hout)
    _ = (K - 1) ^ 3 := by ring

theorem transitionCount_pos [Finite ι] [Finite U] [Fintype N] (hS : S.Nonempty) :
    0 < P.transitionCount := by
  exact ((ncard_pos (toFinite _)).mpr (hS.image (P.transition P.root))).trans_le
    (Finset.single_le_sum (f := fun v => (P.transition v '' S).ncard)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))

/-- **Weighted tree peeling.** A rectangle budget is paid once; the thin remainder pays
at most `(K - 1)^3` maximum atoms per joint merge state. -/
theorem abs_sumOn_le_of_budget [Finite ι] [Finite U] [Fintype N]
    (hP : P.Coherent) {K : ℕ} (hK : 1 < K)
    {w cost : (ι → U) → ℝ} {a : ℝ} (ha : 0 ≤ a) (hw : ∀ x, |w x| ≤ a)
    (hc : ∀ x, 0 ≤ cost x) (hrect : RectangleBudget w cost K K) :
    |sumOn w S| ≤ sumOn cost S + a * ((K - 1) ^ 3 * P.transitionCount : ℕ) := by
  classical
  induction hn : S.ncard using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases hthick : ∃ v x, x ∈ S ∧ K ≤ (P.inside v x).ncard ∧ K ≤ (P.outside v x).ncard
    · obtain ⟨v, x, hx, hA, hB⟩ := hthick
      let R := P.peers v x
      have hR : R ⊆ S := fun _ hy => hy.1
      have hxR : x ∈ R := ⟨hx, rfl⟩
      have hlt : (S \ R).ncard < n := by
        rw [← hn]
        exact ncard_lt_ncard (ssubset_iff_subset_ne.mpr ⟨sdiff_subset,
          fun he => (show x ∈ S \ R from by rw [he]; exact hx).2 hxR⟩)
      have hbudget : |sumOn w R| ≤ sumOn cost R := by
        rw [show R = rectangle (P.region v) (P.inside v x) (P.outside v x) from
          Coherent.peers_eq_rectangle P hP v x]
        exact hrect _ _ _ hA hB
      have hrest := ih _ hlt (P.erase hP v x) (Coherent.erase P hP v x) rfl
      have hcount : a * ((K - 1) ^ 3 * (P.erase hP v x).transitionCount : ℕ) ≤
          a * ((K - 1) ^ 3 * P.transitionCount : ℕ) := by
        apply mul_le_mul_of_nonneg_left _ ha
        exact_mod_cast Nat.mul_le_mul_left _ (P.transitionCount_erase_le hP v x)
      rw [sumOn_sdiff w hR, sumOn_sdiff cost hR]
      exact (abs_add_le _ _).trans (by linarith)
    · have hsmall : ∀ v, ∀ x ∈ S,
          (P.inside v x).ncard < K ∨ (P.outside v x).ncard < K := by
        push Not at hthick
        intro v x hx
        by_cases hA : K ≤ (P.inside v x).ncard
        · exact Or.inr (hthick v x hx hA)
        · exact Or.inl (not_le.mp hA)
      have hcard : S.ncard ≤ (K - 1) ^ 3 * P.transitionCount := by
        by_cases hS : K ≤ S.ncard
        · exact P.ncard_le_of_small_sides hK hS hsmall
        · rcases S.eq_empty_or_nonempty with he | hne
          · simp [he]
          · have hD := P.transitionCount_pos hne
            have hpow : K - 1 ≤ (K - 1) ^ 3 := Nat.le_self_pow (by decide) _
            have hm := Nat.mul_le_mul_left ((K - 1) ^ 3) hD
            lia
      have hcardR : a * S.ncard ≤ a * ((K - 1) ^ 3 * P.transitionCount : ℕ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) ha
      exact (abs_sumOn_le hw S).trans (by linarith [sumOn_nonneg hc S])

end TreeFrontier

end Complexity.Frontier
