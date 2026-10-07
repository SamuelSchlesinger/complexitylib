/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Retained

/-!
# Two-way complementation: image bound

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/ImageBound.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace Complementation.Internal

universe u v

open scoped SetRel

/-- Exponential cost of a single edge for every finite source monoid and label type. -/
theorem single_edge_cost (h : ℕ) :
    ∀ {A : Type u} {H : Type v} [Monoid A] [Finite A] [Finite H] {m : ℕ},
      Nat.card H = h → 2 ≤ h →
      ∀ (ι : A →ₙ* Diagram m) (φ : A →* RelationMonoid H), Function.Surjective φ →
      (∀ a b, (ι a, ι b) ∈ Diagram.inclusion m → (φ b).toRel ⊆ (φ a).toRel) →
      (∀ σ : Equiv.Perm H, ∃ p : Aˣ, φ p = (permutationUnit σ).val) →
      ∀ a, IsIdempotentElem a → ∀ x y : H, x ≠ y →
      (φ a).toRel = SetRel.id ∪ {(x, y)} →
      lossBound h ≤ ((ι 1).missing (ι a)).ncard := by
  classical
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro A H _ _ _ m hH hh ι φ hφ hreverse hlift a ha x y hxy himage
    by_cases hsmall : h ≤ 128
    · simpa only [hH] using single_edge_base ι φ hreverse a x y hxy himage (by omega)
    have hlarge : 129 ≤ h := by omega
    obtain ⟨u, v, z, huv, huz, hvz⟩ := exists_hub_families (H := H) (by omega)
    choose s hs hsimage hscost using fun i =>
      pair_conjugate ι φ hlift a ha x y hxy himage (u i) z (huz i)
    choose s' hs' hsimage' hscost' using fun j =>
      pair_conjugate ι φ hlift a ha x y hxy himage z (v j) (hvz j).symm
    let f : Bool × Fin 64 → A := fun p => if p.1 then s' p.2 else s p.2
    let c := ((ι 1).missing (ι a)).ncard
    have hcost (p : Bool × Fin 64) : ((ι 1).missing (ι (f p))).ncard ≤ 2 * c := by
      obtain ⟨b, i⟩ := p
      cases b
      · exact hscost i
      · exact hscost' i
    let T : Set H := {w | w ≠ z}
    let P0 := restrictedIdentity T
    have hP0 : IsIdempotentElem (RelationMonoid.ofRel P0) :=
      RelationMonoid.ext (restrictedIdentity_comp_self T)
    obtain ⟨b0, hb0, hb0image, _⟩ := minimal_idempotent_lift φ.toMulHom hφ
      (RelationMonoid.ofRel P0) hP0
    have hφb0 : (φ b0).toRel = P0 := congrArg RelationMonoid.toRel hb0image
    obtain ⟨J0, _, hJcard, hJ⟩ := common_pair_budget ι f b0 hb0 hcost
    let index : Fin 4096 ≃ Fin 64 × Fin 64 := (finProdFinEquiv (m := 64) (n := 64)).symm
    let edge : Fin 4096 → H × H := fun r => (u (index r).1, v (index r).2)
    have hedgeinj : Function.Injective edge := by
      intro r s h
      apply index.injective
      exact Prod.ext (u.injective (congrArg Prod.fst h)) (v.injective (congrArg Prod.snd h))
    let E (j : ℕ) : SetRel H H := edge '' {r : Fin 4096 | r.val < j}
    let P (j : ℕ) := P0 ∪ E j
    let U := Set.range u
    let V := Set.range v
    have hUV : Disjoint U V := by
      apply Set.disjoint_left.mpr
      rintro w ⟨i, rfl⟩ ⟨j, heq⟩
      exact huv i j heq.symm
    have hUT : U ⊆ T := by rintro w ⟨i, rfl⟩; exact huz i
    have hVT : V ⊆ T := by rintro w ⟨j, rfl⟩; exact hvz j
    have hE (j : ℕ) : E j ⊆ U ×ˢ V := by
      rintro _ ⟨r, _, rfl⟩
      exact ⟨⟨(index r).1, rfl⟩, ⟨(index r).2, rfl⟩⟩
    have he (r : Fin 4096) : {edge r} ⊆ U ×ˢ V := by
      rintro w rfl
      exact ⟨⟨(index r).1, rfl⟩, ⟨(index r).2, rfl⟩⟩
    have hnew (r : Fin 4096) : edge r ∉ E r.val := by
      rintro ⟨s, hs, heq⟩
      change s.val < r.val at hs
      exact (hedgeinj heq ▸ hs).false
    have hEsucc (r : Fin 4096) : E (r.val + 1) = E r.val ∪ {edge r} := by
      have hidx : {s : Fin 4096 | s.val < r.val + 1} =
          {s : Fin 4096 | s.val < r.val} ∪ {r} := by
        ext s
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
        constructor
        · intro hs
          by_cases hlt : s.val < r.val
          · exact Or.inl hlt
          · exact Or.inr (Fin.ext (by omega))
        · rintro (hlt | rfl) <;> omega
      change edge '' _ = _
      rw [hidx, Set.image_union, Set.image_singleton]
    have hPidemp (j : ℕ) : P j ○ P j = P j := by
      simpa only [P, Set.union_self] using
        bipartite_relation_comp T U V hUT hVT hUV (E j) (E j) (hE j) (hE j)
    let g (j : ℕ) : A := if hj : j < 4096 then
      b0 * s (index ⟨j, hj⟩).1 * s' (index ⟨j, hj⟩).2 * b0 else b0
    have hgimage (r : Fin 4096) : (φ (g r.val)).toRel = P0 ∪ {edge r} := by
      simp only [g, dite_eq_left r.isLt, map_mul, RelationMonoid.toRel_mul,
        hφb0, hsimage, hsimage']
      exact hub_pair_relation _ _ z (huz _) (hvz _)
    have hgbudget : ∀ j < 4096,
        ι (g j) ∈ (ι b0).corner ∧ (ι b0).missing (ι (g j)) ⊆ J0 := by
      intro j hj
      simp only [g, dite_eq_left hj]
      constructor
      · constructor
        · change ι b0 * ι _ = _
          rw [← map_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc, hb0.eq]
        · change ι _ * ι b0 = _
          rw [← map_mul, mul_assoc, hb0.eq]
      · exact hJ _ _
    obtain ⟨b, hbzero, hbidemp, hbpower, _, _, htotal⟩ :=
      exists_nested_chain ι b0 hb0 g J0 hgbudget
    have hbimage : ∀ j ≤ 4096, (φ (b j)).toRel = P j := by
      intro j
      induction j with
      | zero => intro _; simp [hbzero, hφb0, P, E]
      | succ j hj =>
        intro hjle
        let r : Fin 4096 := ⟨j, by omega⟩
        have hprev := hj (by omega)
        have hnext : φ (b j * g j * b j) = RelationMonoid.ofRel (P (j + 1)) := by
          apply RelationMonoid.ext
          rw [map_mul, map_mul, RelationMonoid.toRel_mul, RelationMonoid.toRel_mul,
            hprev, hgimage r, RelationMonoid.toRel_ofRel]
          change (P0 ∪ E j) ○ (P0 ∪ {edge r}) ○ (P0 ∪ E j) = P0 ∪ E (j + 1)
          rw [bipartite_relation_comp T U V hUT hVT hUV _ _ (hE j) (he r)]
          rw [bipartite_relation_comp T U V hUT hVT hUV _ _
            (Set.union_subset (hE j) (he r)) (hE j)]
          rw [show E (j + 1) = E j ∪ {edge r} from hEsucc r]
          rw [Set.union_right_comm (E j) {edge r} (E j), Set.union_self]
        obtain ⟨n, hn⟩ := hbpower j
        rw [hn, map_pow, hnext]
        have hi : IsIdempotentElem (RelationMonoid.ofRel (P (j + 1))) :=
          RelationMonoid.ext (hPidemp (j + 1))
        rw [hi.pow_succ_eq, RelationMonoid.toRel_ofRel]
    let δ (r : Fin 4096) := ((ι (b r.val)).missing (ι (b (r.val + 1)))).ncard
    have hsum : ∑ r, δ r ≤ 1024 * c := by
      have heq : ∑ r, δ r =
          ∑ j ∈ Finset.range 4096, ((ι (b j)).missing (ι (b (j + 1)))).ncard := by
        exact Fin.sum_univ_eq_sum_range
          (fun j => ((ι (b j)).missing (ι (b (j + 1)))).ncard) 4096
      rw [heq]
      omega
    apply amplification_arithmetic hlarge δ hsum
    intro r
    obtain ⟨F, hFcard, hxF, hyF, hzF, hUF, hVF⟩ := retained_pair_set U V
      (by simpa [U] using Set.ncard_range_of_injective u.injective)
      (by simpa [V] using Set.ncard_range_of_injective v.injective) hUV z
      (edge r).1 (edge r).2
      (by rintro ⟨i, hi⟩; exact huz i hi)
      (by rintro ⟨j, hj⟩; exact hvz j hj)
      ⟨(index r).1, rfl⟩ ⟨(index r).2, rfl⟩
    have hrestrict : restrictedIdentity F ○ (φ (b r.val)).toRel ○ restrictedIdentity F =
        restrictedIdentity F := by
      rw [hbimage _ r.isLt.le]
      exact retained_relation_identity U V F z _ _ hzF hUF hVF (E r.val) (hE r.val) (hnew r)
    have hrestrict' : restrictedIdentity F ○ (φ (b (r.val + 1))).toRel ○
        restrictedIdentity F = restrictedIdentity F ∪ {edge r} := by
      rw [hbimage _ r.isLt, show P (r.val + 1) = P r.val ∪ {edge r} from
        (congrArg (P0 ∪ ·) (hEsucc r)).trans (Set.union_assoc _ _ _).symm]
      have hp : restrictedIdentity F ○ P r.val ○ restrictedIdentity F = restrictedIdentity F := by
        rwa [hbimage _ r.isLt.le] at hrestrict
      exact retained_relation_pair (P r.val) F hp _ _ hxF hyF
    obtain ⟨n, hn⟩ := hbpower r.val
    have habsorb := sandwich_power_absorption (b r.val) (g r.val) (hbidemp r.val) n
    rw [← hn] at habsorb
    obtain ⟨d, hd, ψ, hψ, hliftψ, hψrel, w, hw, hwimage, hwcost⟩ :=
      smaller_relation_instance ι φ hφ (b r.val) (b (r.val + 1)) (hbidemp r.val)
        habsorb.1 habsorb.2 F hrestrict ⟨(edge r).1, hxF⟩ ⟨(edge r).2, hyF⟩ hrestrict'
    let ιb : (hbidemp r.val).Corner →ₙ* Diagram m := ι.comp (MulMemClass.subtype _)
    let ιd : hd.Corner →ₙ* Diagram m := ιb.comp (MulMemClass.subtype _)
    have hreverseψ : ∀ s t, (ιd s, ιd t) ∈ Diagram.inclusion m →
        (ψ t).toRel ⊆ (ψ s).toRel := by
      intro s t hst
      rw [hψrel, hψrel]
      exact fun _ hp => hreverse s.val.val t.val.val hst hp
    have hlow := ih (h - 127) (by omega) (A := hd.Corner) (H := F)
      (by omega) (by omega) ιd ψ hψ hreverseψ hliftψ w hw
      ⟨(edge r).1, hxF⟩ ⟨(edge r).2, hyF⟩
      (fun heq => huv (index r).1 (index r).2 (congrArg Subtype.val heq)) hwimage
    exact hlow.trans hwcost

/-- A surjection has a unital identity corner with unit lifts for every target unit. -/
theorem minimal_unital_corner {A M : Type*} [Semigroup A] [Finite A] [Monoid M]
    (θ : A →ₙ* M) (hθ : Function.Surjective θ) :
    ∃ d : A, ∃ hd : IsIdempotentElem d, ∃ ψ : hd.Corner →* M,
      Function.Surjective ψ ∧ (∀ w, ψ w = θ w.val) ∧
      ∀ u : Mˣ, ∃ p : hd.Cornerˣ, ψ p = u.val := by
  have h1 : IsIdempotentElem (1 : M) := by simp [IsIdempotentElem]
  obtain ⟨d, hd, hθd, hminimal⟩ := minimal_idempotent_lift θ hθ 1 h1
  let ε : h1.Corner ≃* M :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, (Subsemigroup.mem_corner_iff h1).mpr ⟨one_mul x, mul_one x⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let γ := cornerMap θ hd h1 hθd
  let ψ := ε.toMonoidHom.comp γ
  have hψ : Function.Surjective ψ :=
    ε.surjective.comp (cornerMap_surjective θ hθ hd h1 hθd)
  refine ⟨d, hd, ψ, hψ, fun _ => rfl, ?_⟩
  intro u
  obtain ⟨w, hw⟩ := hψ u.val
  have hu : IsUnit (ψ w) := hw.symm ▸ u.isUnit
  have hγ : IsUnit (γ w) := by
    have hu' := hu.map ε.symm.toMonoidHom
    simpa only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using hu'
  obtain ⟨p, hp⟩ := minimal_corner_reflects_units θ hd h1 hθd hminimal w hγ
  exact ⟨p, hp ▸ hw⟩

/-- Identity plus a single pair is always an idempotent relation. -/
theorem identity_pair_idempotent {H : Type*} (x y : H) :
    IsIdempotentElem (RelationMonoid.ofRel (SetRel.id ∪ {(x, y)})) := by
  apply RelationMonoid.ext
  change (SetRel.id ∪ {(x, y)}) ○ (SetRel.id ∪ {(x, y)}) = SetRel.id ∪ {(x, y)}
  ext ⟨r, s⟩
  simp only [SetRel.comp, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff,
    SetRel.id, Prod.mk.injEq]
  aesop

/-- A surjective order-reversing multiplicative image has exponential cost. -/
theorem order_reversing_image_bound_finite {H : Type*} [Finite H]
    (m : ℕ) (_hm : 1 ≤ m) (hh : 2 ≤ Nat.card H)
    (S : Set (Diagram m)) (hidentity : Diagram.identity m ∈ S)
    (hclosed : ∀ ⦃a b⦄, a ∈ S → b ∈ S → Diagram.comp a b ∈ S)
    (φ : S → SetRel H H) (hsurj : Function.Surjective φ)
    (hmul : ∀ a b : S,
      φ ⟨Diagram.comp a.val b.val, hclosed a.property b.property⟩ = φ a ○ φ b)
    (hreverse : ∀ a b : S, (a.val, b.val) ∈ Diagram.inclusion m → φ b ⊆ φ a) :
    lossBound (Nat.card H) ≤ 2 * m := by
  classical
  let S0 : Submonoid (Diagram m) :=
    { carrier := S
      one_mem' := hidentity
      mul_mem' := by
        intro a b ha hb
        change Diagram.comp a b ∈ S
        exact hclosed ha hb }
  let θ : S0 →ₙ* RelationMonoid H :=
    { toFun := fun x => .ofRel (φ ⟨x.val, x.property⟩)
      map_mul' := fun a b => RelationMonoid.ext (hmul ⟨a.val, a.property⟩ ⟨b.val, b.property⟩) }
  have hθ : Function.Surjective θ := by
    intro R
    obtain ⟨x, hx⟩ := hsurj R.toRel
    exact ⟨⟨x.val, x.property⟩, RelationMonoid.ext hx⟩
  obtain ⟨e, he, ψ, hψ, hψval, hunit⟩ := minimal_unital_corner θ hθ
  let ι : he.Corner →ₙ* Diagram m :=
    { toFun := fun w => w.val.val
      map_mul' := fun _ _ => rfl }
  have hrev : ∀ a b, (ι a, ι b) ∈ Diagram.inclusion m → (ψ b).toRel ⊆ (ψ a).toRel := by
    intro a b hab
    rw [hψval, hψval]
    exact hreverse ⟨a.val.val, a.val.property⟩ ⟨b.val.val, b.val.property⟩ hab
  let := Fintype.ofFinite H
  obtain ⟨pair⟩ : Nonempty (Fin 2 ↪ H) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hh)
  let x := pair 0
  let y := pair 1
  have hxy : x ≠ y := fun heq => by
    have := congrArg Fin.val (pair.injective heq)
    norm_num at this
  obtain ⟨a, ha, haimage, _⟩ := minimal_idempotent_lift ψ.toMulHom hψ
    (RelationMonoid.ofRel (SetRel.id ∪ {(x, y)})) (identity_pair_idempotent x y)
  have hcost := single_edge_cost (Nat.card H) rfl hh ι ψ hψ hrev
    (fun σ => hunit (permutationUnit σ)) a ha x y hxy
    (congrArg RelationMonoid.toRel haimage)
  exact hcost.trans ((Set.ncard_le_ncard (show (ι 1).missing (ι a) ⊆ (ι 1).classes from
    fun _ h => h.1)).trans (Diagram.class_count (ι 1)))

/-- The order-reversing image bound for a finite label domain. -/
theorem order_reversing_image_bound
    (m h : ℕ) (_hm : 1 ≤ m) (hh : 2 ≤ h)
    (S : Set (Diagram m)) (hidentity : Diagram.identity m ∈ S)
    (hclosed : ∀ ⦃a b⦄, a ∈ S → b ∈ S → Diagram.comp a b ∈ S)
    (φ : S → SetRel (Fin h) (Fin h)) (hsurj : Function.Surjective φ)
    (hmul : ∀ a b : S,
      φ ⟨Diagram.comp a.val b.val, hclosed a.property b.property⟩ = φ a ○ φ b)
    (hreverse : ∀ a b : S, (a.val, b.val) ∈ Diagram.inclusion m → φ b ⊆ φ a) :
    lossBound h ≤ 2 * m := by
  simpa only [Nat.card_fin] using order_reversing_image_bound_finite (H := Fin h) m _hm
    (by simpa using hh) S hidentity hclosed φ hsurj hmul hreverse

end Complementation.Internal

end Complexity.FiniteAutomaton
