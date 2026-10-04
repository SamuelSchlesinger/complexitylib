/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.NetworkDefs

/-!
# Counting aggregate-network states

A first large past set is charged to an outgoing transition, consisting of the old
cut values, old aggregate, and incident values. The transition need not be invertible.
-/

@[expose] public section

namespace Algebraic.Cutwidth.AggregateNetwork.Internal

open scoped Classical
open Network

variable {n : Nat} {V E M : Type} [CommMonoid M] [Fintype V] [Fintype E] [Fintype M]
  (N : AggregateNetwork n V E M)

private theorem card_large_le [LinearOrder V] [Nonempty V]
    {f : Cslib.BooleanFunction n} (hf : N.Computes f) (hdeg : N.MaxDegreeLE 3)
    {w : Nat} (hw : ∀ v, (N.cut (below v)).card ≤ w)
    {K : Nat} (hK : 1 < K) (hrect : RectangleFree f K)
    (S : Finset (Fin n → Bool)) (α : (Fin n → Bool) → E → Bool)
    (hα : ∀ x ∈ S, N.Satisfies x (α x))
    (hlarge : ∀ x ∈ S,
      K ≤ (N.pastSet Finset.univ (α x) (N.accumulated Finset.univ (α x))).card) :
    S.card ≤ Fintype.card V * 2 ^ (w + 3) * Fintype.card M * (K - 1) ^ 2 := by
  have univ_nonempty : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty
  -- The set of vertices at which the past set of `x` has become large.
  let big : (Fin n → Bool) → Finset V := fun x =>
    Finset.univ.filter fun v => K ≤ (N.pastSet (upto v) (α x) (N.accumulated (upto v) (α x))).card
  have big_nonempty : ∀ x ∈ S, (big x).Nonempty := by
    intro x hx
    refine ⟨Finset.univ.max' univ_nonempty, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [upto_max']
    exact hlarge x hx
  -- The first such vertex.
  let first : (Fin n → Bool) → V := fun x =>
    if h : (big x).Nonempty then (big x).min' h else Classical.arbitrary V
  have first_eq : ∀ x, (hx : x ∈ S) → first x = (big x).min' (big_nonempty x hx) := by
    intro x hx
    simp [first, big_nonempty x hx]
  have first_big : ∀ x ∈ S,
      K ≤ (N.pastSet (upto (first x)) (α x) (N.accumulated (upto (first x)) (α x))).card := by
    intro x hx
    have mem := Finset.min'_mem (big x) (big_nonempty x hx)
    rw [first_eq x hx]
    exact (Finset.mem_filter.mp mem).2
  have first_min : ∀ x ∈ S, ∀ u, u < first x →
      (N.pastSet (upto u) (α x) (N.accumulated (upto u) (α x))).card < K := by
    intro x hx u hu
    by_contra h
    rw [not_lt] at h
    have mem : u ∈ big x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    have := Finset.min'_le (big x) u mem
    rw [first_eq x hx] at hu
    exact absurd hu (not_lt.mpr this)
  have below_small : ∀ x ∈ S,
      (N.pastSet (below (first x)) (α x) (N.accumulated (below (first x)) (α x))).card < K := by
    intro x hx
    rcases below_eq_empty_or_exists_upto (first x) with h | ⟨u, hu, h⟩
    · rw [h]
      exact lt_of_le_of_lt (N.card_pastSet_empty_le _ _) hK
    · rw [h]
      exact first_min x hx u hu
  have future_small : ∀ x ∈ S,
      (N.futureSet (upto (first x)) (α x) (N.accumulated (upto (first x)) (α x))).card < K := by
    intro x hx
    rcases hrect (N.toNetwork.past (upto (first x)))
      (N.pastSet _ (α x) (N.accumulated (upto (first x)) (α x)))
      (N.futureSet _ (α x) (N.accumulated (upto (first x)) (α x)))
      (fun p hp q hq => N.accepted_of_mem_pastSet_of_mem_futureSet hf hp hq) with h | h
    · exact absurd h (not_lt.mpr (first_big x hx))
    · exact h
  -- The edges whose bits determine the charge: the cut before the first vertex
  -- and the edges incident to it.
  let D : V → Finset E := fun v => N.cut (below v) ∪ N.edgesAt v
  have D_card : ∀ v, (D v).card ≤ w + 3 := fun v =>
    (Finset.card_union_le _ _).trans (add_le_add (hw v) (hdeg v))
  have cut_upto_subset_D : ∀ v, N.cut (upto v) ⊆ D v := fun v => N.toNetwork.cut_upto_subset v
  have cut_below_subset_D : ∀ v, N.cut (below v) ⊆ D v := fun v => Finset.subset_union_left
  let key : (Fin n → Bool) → V × (E → Bool) × M := fun x =>
    (first x, (fun e => if e ∈ D (first x) then α x e else false),
      N.accumulated (below (first x)) (α x))
  -- Inputs with the same key are determined by a past and a future assignment.
  have fiber : ∀ κ ∈ S.image key,
      (S.filter fun x => key x = κ).card ≤ (K - 1) ^ 2 := by
    rintro ⟨v, τ, m⟩ _
    set F := S.filter fun x => key x = (v, τ, m) with hF
    rcases F.eq_empty_or_nonempty with hempty | ⟨x₁, hx₁⟩
    · rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
    have keyed : ∀ x ∈ F, first x = v ∧ (∀ e ∈ D v, α x e = τ e) ∧
        N.accumulated (below v) (α x) = m := by
      intro x hx
      have h := (Finset.mem_filter.mp hx).2
      simp only [key, Prod.mk.injEq] at h
      obtain ⟨hv, hτ, hm⟩ := h
      refine ⟨hv, (fun e he => ?_), hv ▸ hm⟩
      rw [← hτ]
      simp [hv, he]
    obtain ⟨hx₁acc, _⟩ := Finset.mem_filter.mp hx₁
    obtain ⟨hv₁, hτ₁, hm₁⟩ := keyed x₁ hx₁
    have agree : ∀ x ∈ F, ∀ e ∈ D v, α x e = α x₁ e := by
      intro x hx e he
      rw [(keyed x hx).2.1 e he, hτ₁ e he]
    have accum_below : ∀ x ∈ F,
        N.accumulated (below v) (α x) = N.accumulated (below v) (α x₁) := by
      intro x hx
      rw [(keyed x hx).2.2, hm₁]
    have accum_upto : ∀ x ∈ F,
        N.accumulated (upto v) (α x) = N.accumulated (upto v) (α x₁) := by
      intro x hx
      rw [N.accumulated_upto, N.accumulated_upto, accum_below x hx]
      congr 1
      exact N.contribution_local v _ _ fun e he =>
        agree x hx e (Finset.mem_union_right _ (N.toNetwork.mem_edgesAt.mpr he))
    let φ : (Fin n → Bool) →
        (↥(N.toNetwork.past (below v)) → Bool) × (↥(N.toNetwork.past (upto v))ᶜ → Bool) :=
      fun x => (fun j => x j, fun j => x j)
    have maps : Set.MapsTo φ ↑F
        ↑(N.pastSet (below v) (α x₁) (N.accumulated (below v) (α x₁)) ×ˢ
          N.futureSet (upto v) (α x₁) (N.accumulated (upto v) (α x₁))) := by
      intro x hx
      have hxacc := (Finset.mem_filter.mp hx).1
      rw [Finset.mem_coe, Finset.mem_product]
      constructor
      · rw [← accum_below x hx, N.pastSet_congr (σ' := α x)
          (fun e he => (agree x hx e (cut_below_subset_D v he)).symm)]
        exact N.restrict_mem_pastSet (hα x hxacc) _
      · rw [← accum_upto x hx, N.futureSet_congr (σ' := α x)
          (fun e he => (agree x hx e (cut_upto_subset_D v he)).symm)]
        exact N.restrict_mem_futureSet (hα x hxacc) _
    have inj : Set.InjOn φ F := by
      intro x hx y hy hxy
      have hxacc := (Finset.mem_filter.mp hx).1
      have hyacc := (Finset.mem_filter.mp hy).1
      simp only [φ, Prod.mk.injEq] at hxy
      obtain ⟨hpast, hfuture⟩ := hxy
      funext j
      by_cases h₁ : j ∈ N.toNetwork.past (below v)
      · exact congrFun hpast ⟨j, h₁⟩
      by_cases h₂ : j ∈ N.toNetwork.past (upto v)
      · obtain ⟨hj, hjv⟩ := N.toNetwork.mem_past.mp h₂
        have hv : N.portVertex j = v := by
          apply eq_of_le_of_not_lt (mem_upto.mp hjv)
          intro hlt
          exact h₁ (N.toNetwork.mem_past.mpr ⟨hj, mem_below.mpr hlt⟩)
        have hedge : N.portEdge j ∈ D v :=
          Finset.mem_union_right _ (N.toNetwork.mem_edgesAt.mpr (hv ▸ N.port_incident j hj))
        rw [← (hα x hxacc).1.2 j hj, ← (hα y hyacc).1.2 j hj,
          agree x hx _ hedge, agree y hy _ hedge]
      · exact congrFun hfuture ⟨j, Finset.mem_compl.mpr h₂⟩
    calc F.card ≤ (N.pastSet (below v) (α x₁) (N.accumulated (below v) (α x₁)) ×ˢ
          N.futureSet (upto v) (α x₁) (N.accumulated (upto v) (α x₁))).card :=
          Finset.card_le_card_of_injOn φ maps inj
      _ = (N.pastSet (below v) (α x₁) (N.accumulated (below v) (α x₁))).card *
          (N.futureSet (upto v) (α x₁) (N.accumulated (upto v) (α x₁))).card :=
          Finset.card_product _ _
      _ ≤ (K - 1) * (K - 1) := by
          apply Nat.mul_le_mul
          · exact Nat.le_sub_one_of_lt (hv₁ ▸ below_small x₁ hx₁acc)
          · exact Nat.le_sub_one_of_lt (hv₁ ▸ future_small x₁ hx₁acc)
      _ = (K - 1) ^ 2 := (sq _).symm
  -- Outgoing keys include the accumulator before the transition. No inverse is needed.
  have image_card : (S.image key).card ≤ Fintype.card V * 2 ^ (w + 3) * Fintype.card M := by
    let ψ : V × (E → Bool) × M → Σ v : V, (↥(D v) → Bool) × M :=
      fun vτ => ⟨vτ.1, (fun e => vτ.2.1 e), vτ.2.2⟩
    have inj : Set.InjOn ψ (S.image key) := by
      rintro ⟨v, τ, m⟩ hmem ⟨v', τ', m'⟩ hmem' heq
      simp only [ψ, Sigma.mk.inj_iff] at heq
      obtain ⟨rfl, hτ⟩ := heq
      have hτ' := eq_of_heq hτ
      have hvals := congrArg Prod.fst hτ'
      have hm := congrArg Prod.snd hτ'
      dsimp only at hm
      subst m'
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hmem
      obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hmem'
      simp only [key, Prod.mk.injEq] at hx hy
      obtain ⟨hxv, hxτ, _⟩ := hx
      obtain ⟨hyv, hyτ, _⟩ := hy
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      funext e
      by_cases he : e ∈ D v
      · exact congrFun hvals ⟨e, he⟩
      · rw [← hxτ, ← hyτ]
        simp [hxv, hyv, he]
    calc (S.image key).card
        ≤ (Finset.univ : Finset (Σ v : V, (↥(D v) → Bool) × M)).card :=
          Finset.card_le_card_of_injOn ψ (fun _ _ => Finset.mem_univ _) inj
      _ = ∑ v : V, 2 ^ (D v).card * Fintype.card M := by
          rw [Finset.card_univ, Fintype.card_sigma]
          simp [Fintype.card_bool]
      _ ≤ ∑ _v : V, 2 ^ (w + 3) * Fintype.card M :=
          Finset.sum_le_sum fun v _ =>
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos (D_card v))
      _ = Fintype.card V * 2 ^ (w + 3) * Fintype.card M := by
          simp [Finset.sum_const, Finset.card_univ, Nat.mul_assoc]
  calc S.card ≤ (K - 1) ^ 2 * (S.image key).card :=
        Finset.card_le_mul_card_image _ _ fiber
    _ ≤ (K - 1) ^ 2 * (Fintype.card V * 2 ^ (w + 3) * Fintype.card M) :=
      Nat.mul_le_mul_left _ image_card
    _ = Fintype.card V * 2 ^ (w + 3) * Fintype.card M * (K - 1) ^ 2 := by ring

private theorem card_small_le
    {K : Nat} (S : Finset (Fin n → Bool)) (α : (Fin n → Bool) → E → Bool)
    (hα : ∀ x ∈ S, N.Satisfies x (α x))
    (hsmall : ∀ x ∈ S,
      (N.pastSet Finset.univ (α x) (N.accumulated Finset.univ (α x))).card < K) :
    S.card ≤ Fintype.card M * (K - 1) * 2 ^ (n - N.read.card) := by
  let key : (Fin n → Bool) → M := fun x => N.accumulated Finset.univ (α x)
  have fiber : ∀ m ∈ S.image key,
      (S.filter fun x => key x = m).card ≤ (K - 1) * 2 ^ (n - N.read.card) := by
    intro m _
    set F := S.filter fun x => key x = m with hF
    rcases F.eq_empty_or_nonempty with hempty | ⟨x₁, hx₁⟩
    · rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
    have hx₁S := (Finset.mem_filter.mp hx₁).1
    have hm₁ := (Finset.mem_filter.mp hx₁).2
    let φ : (Fin n → Bool) →
        (↥(N.toNetwork.past Finset.univ) → Bool) ×
          (↥(N.toNetwork.past Finset.univ)ᶜ → Bool) :=
      fun x => (fun j => x j, fun j => x j)
    have inj : Function.Injective φ := by
      intro x y h
      have := congrArg
        (fun pq : (↥(N.toNetwork.past Finset.univ) → Bool) ×
          (↥(N.toNetwork.past Finset.univ)ᶜ → Bool) =>
            glue (N.toNetwork.past Finset.univ) pq.1 pq.2) h
      simpa [φ, glue_restrict] using this
    have maps : Set.MapsTo φ ↑F
        ↑((N.pastSet Finset.univ (α x₁) (key x₁)) ×ˢ
          (Finset.univ : Finset (↥(N.toNetwork.past Finset.univ)ᶜ → Bool))) := by
      intro x hx
      obtain ⟨hxS, hxm⟩ := Finset.mem_filter.mp hx
      rw [Finset.mem_coe, Finset.mem_product]
      refine ⟨?_, Finset.mem_univ _⟩
      rw [N.pastSet_congr (σ' := α x) (by simp), hm₁, ← hxm]
      exact N.restrict_mem_pastSet (hα x hxS) _
    have complCard : ((N.toNetwork.past Finset.univ)ᶜ).card = n - N.read.card := by
      rw [Finset.card_compl, Fintype.card_fin, Network.past_univ]
    calc F.card
        ≤ ((N.pastSet Finset.univ (α x₁) (key x₁)) ×ˢ
          (Finset.univ : Finset (↥(N.toNetwork.past Finset.univ)ᶜ → Bool))).card :=
            Finset.card_le_card_of_injOn φ maps inj.injOn
      _ = (N.pastSet Finset.univ (α x₁) (key x₁)).card *
          2 ^ (n - N.read.card) := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_coe, complCard]
      _ ≤ (K - 1) * 2 ^ (n - N.read.card) :=
        Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt (hsmall x₁ hx₁S))
  calc S.card ≤ ((K - 1) * 2 ^ (n - N.read.card)) * (S.image key).card :=
      Finset.card_le_mul_card_image _ _ fiber
    _ ≤ ((K - 1) * 2 ^ (n - N.read.card)) * Fintype.card M :=
      Nat.mul_le_mul_left _ (Finset.card_le_univ _)
    _ = Fintype.card M * (K - 1) * 2 ^ (n - N.read.card) := by ring

/-- Aggregate cut counting, with a separate term for terminal states whose past
sets never reach the rectangle threshold. The accumulator only needs a commutative
monoid structure; outgoing transition keys avoid any cancellation assumption. -/
theorem card_accepting_le [LinearOrder V] [Nonempty V]
    {f : Cslib.BooleanFunction n} (hf : N.Computes f) (hdeg : N.MaxDegreeLE 3)
    {w : Nat} (hw : ∀ v, (N.cut (below v)).card ≤ w)
    {K : Nat} (hK : 1 < K) (hrect : RectangleFree f K) :
    (accepting f).card ≤ Fintype.card M * (K - 1) * 2 ^ (n - N.read.card) +
      Fintype.card V * 2 ^ (w + 3) * Fintype.card M * (K - 1) ^ 2 := by
  have choice : ∀ x ∈ accepting f, ∃ α, N.Satisfies x α :=
    fun x hx => (hf x).mp (mem_accepting.mp hx)
  choose! α hα using choice
  let small : (Fin n → Bool) → Prop := fun x =>
    (N.pastSet Finset.univ (α x) (N.accumulated Finset.univ (α x))).card < K
  have hsmall := card_small_le N ((accepting f).filter small) α
    (fun x hx => hα x (Finset.mem_filter.mp hx).1)
    (fun _ hx => (Finset.mem_filter.mp hx).2)
  have hlarge := card_large_le N hf hdeg hw hK hrect
    ((accepting f).filter fun x => ¬ small x) α
    (fun x hx => hα x (Finset.mem_filter.mp hx).1)
    (fun _ hx => Nat.le_of_not_gt (Finset.mem_filter.mp hx).2)
  calc (accepting f).card
      = ((accepting f).filter small).card +
          ((accepting f).filter fun x => ¬ small x).card :=
        (Finset.card_filter_add_card_filter_not _).symm
    _ ≤ _ := Nat.add_le_add hsmall hlarge

/-- When every input is read, the terminal term is absorbed into one extra layer. -/
theorem card_accepting_le_of_read_eq_univ [LinearOrder V] [Nonempty V]
    {f : Cslib.BooleanFunction n} (hf : N.Computes f) (hread : N.read = Finset.univ)
    (hdeg : N.MaxDegreeLE 3) {w : Nat} (hw : ∀ v, (N.cut (below v)).card ≤ w)
    {K : Nat} (hK : 1 < K) (hrect : RectangleFree f K) :
    (accepting f).card ≤ (Fintype.card V * 2 ^ (w + 3) + 1) *
      Fintype.card M * (K - 1) ^ 2 := by
  have h := card_accepting_le N hf hdeg hw hK hrect
  simp only [hread, Finset.card_univ, Fintype.card_fin, Nat.sub_self, pow_zero,
    Nat.mul_one] at h
  have hk : K - 1 ≤ (K - 1) ^ 2 := Nat.le_self_pow (by lia) _
  calc (accepting f).card
      ≤ Fintype.card M * (K - 1) +
          Fintype.card V * 2 ^ (w + 3) * Fintype.card M * (K - 1) ^ 2 := h
    _ ≤ Fintype.card M * (K - 1) ^ 2 +
          Fintype.card V * 2 ^ (w + 3) * Fintype.card M * (K - 1) ^ 2 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ hk) _
    _ = _ := by ring

end Algebraic.Cutwidth.AggregateNetwork.Internal
