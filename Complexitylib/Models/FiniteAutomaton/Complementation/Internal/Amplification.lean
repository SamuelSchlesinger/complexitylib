/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.RelationMonoid
public import Mathlib.Data.Set.Card.Arithmetic

/-!
# Two-way complementation: amplification

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/Amplification.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace Complementation.Internal

open scoped SetRel

/-- The exponential lower bound for `2 ≤ h`. -/
def lossBound (h : ℕ) : ℕ := 2 ^ ((h - 2) / 127)

/-- The image of a monoid lies in the diagram corner of its image identity. -/
theorem map_identity_corner {A : Type*} [Monoid A] {m : ℕ}
    (ι : A →ₙ* Diagram m) (a : A) : ι a ∈ (ι 1).corner := by
  constructor
  · change ι 1 * ι a = ι a
    rw [← map_mul, one_mul]
  · change ι a * ι 1 = ι a
    rw [← map_mul, mul_one]

/-- The cardinality consequence of the uniform transport theorem. -/
theorem missing_context_card {m : ℕ} (e d u v z : Diagram m)
    (he : Diagram.comp e e = e) (hd : Diagram.comp d d = d)
    (hcontext : Diagram.comp (Diagram.comp u e) v = d) (hz : z ∈ e.corner)
    (hnew : Diagram.comp (Diagram.comp u z) v ∈ d.corner) :
    (d.missing (Diagram.comp (Diagram.comp u z) v)).ncard ≤ 2 * (e.missing z).ncard := by
  obtain ⟨J', _, hcard, hcover⟩ := Diagram.transport e d u v he hd hcontext
    (e.missing z) (fun _ h => h.1)
  exact (Set.ncard_le_ncard (hcover z hz Set.Subset.rfl hnew)).trans hcard

/-- Conjugating by a unit costs at most twice as many missing classes. -/
theorem conjugate_missing_bound {A : Type*} [Monoid A] {m : ℕ}
    (ι : A →ₙ* Diagram m) (p : Aˣ) (a : A) :
    ((ι 1).missing (ι (p * a * (↑p⁻¹ : A)))).ncard ≤
      2 * ((ι 1).missing (ι a)).ncard := by
  have he : Diagram.comp (ι 1) (ι 1) = ι 1 := (map_identity_corner ι 1).1
  have hcontext : Diagram.comp (Diagram.comp (ι p) (ι 1)) (ι (↑p⁻¹ : A)) = ι 1 := by
    change ι p * ι 1 * ι (↑p⁻¹ : A) = ι 1
    rw [← map_mul, ← map_mul]
    simp
  have hnew : Diagram.comp (Diagram.comp (ι p) (ι a)) (ι (↑p⁻¹ : A)) ∈ (ι 1).corner := by
    change ι p * ι a * ι (↑p⁻¹ : A) ∈ (ι 1).corner
    rw [← map_mul, ← map_mul]
    exact map_identity_corner ι _
  have h := missing_context_card (ι 1) (ι 1) (ι p) (ι (↑p⁻¹ : A)) (ι a)
    he he hcontext (map_identity_corner ι a) hnew
  change ((ι 1).missing (ι p * ι a * ι (↑p⁻¹ : A))).ncard ≤ _ at h
  simpa only [map_mul] using h

/-- All pair products share one missing-set bound after sandwiching by an idempotent. -/
theorem common_pair_budget {A : Type*} [Monoid A] {m t c : ℕ}
    (ι : A →ₙ* Diagram m) (f : Bool × Fin t → A) (b0 : A) (hb0 : IsIdempotentElem b0)
    (hcost : ∀ p, ((ι 1).missing (ι (f p))).ncard ≤ 2 * c) :
    ∃ J0 ⊆ (ι b0).classes, J0.ncard ≤ 8 * t * c ∧
      ∀ i j, (ι b0).missing (ι (b0 * f (false, i) * f (true, j) * b0)) ⊆ J0 := by
  classical
  let J := ⋃ p, (ι 1).missing (ι (f p))
  have hJ : J ⊆ (ι 1).classes := by
    intro C hC
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hC
    exact hp.1
  have hcard : J.ncard ≤ 4 * t * c := by
    calc
      J.ncard ≤ ∑ p : Bool × Fin t, ((ι 1).missing (ι (f p))).ncard :=
        Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : Bool × Fin t, 2 * c := Finset.sum_le_sum (fun p _ => hcost p)
      _ = 4 * t * c := by simp; ring
  have he : Diagram.comp (ι 1) (ι 1) = ι 1 := (map_identity_corner ι 1).1
  have hd : Diagram.comp (ι b0) (ι b0) = ι b0 :=
    (map_mul ι b0 b0).symm.trans (congrArg ι hb0.eq)
  have hcontext : Diagram.comp (Diagram.comp (ι b0) (ι 1)) (ι b0) = ι b0 := by
    change ι b0 * ι 1 * ι b0 = ι b0
    rw [← map_mul, ← map_mul, mul_one, hb0.eq]
  obtain ⟨J0, hJ0, hcard0, hcover⟩ := Diagram.transport (ι 1) (ι b0) (ι b0) (ι b0)
    he hd hcontext J hJ
  refine ⟨J0, hJ0, by nlinarith, ?_⟩
  intro i j
  have hproduct : (ι 1).missing (ι (f (false, i) * f (true, j))) ⊆ J := by
    rw [map_mul]
    exact (Diagram.missing_comp (ι 1) _ _ he (map_identity_corner ι _)
      (map_identity_corner ι _)).trans (Set.union_subset
        (Set.subset_iUnion (fun p => (ι 1).missing (ι (f p))) (false, i))
        (Set.subset_iUnion (fun p => (ι 1).missing (ι (f p))) (true, j)))
  have hnew : Diagram.comp (Diagram.comp (ι b0) (ι (f (false, i) * f (true, j))))
      (ι b0) ∈ (ι b0).corner := by
    constructor
    · rw [← Diagram.comp_assoc, ← Diagram.comp_assoc, hd]
    · rw [Diagram.comp_assoc, hd]
  have h := hcover _ (map_identity_corner ι _) hproduct hnew
  change (ι b0).missing (ι b0 * ι (f (false, i) * f (true, j)) * ι b0) ⊆ J0 at h
  simpa only [map_mul, mul_assoc] using h

/-- Disjoint source and target sets prevent two added edges from being concatenated. -/
theorem bipartite_relation_comp {H : Type*} (F U V : Set H)
    (hU : U ⊆ F) (hV : V ⊆ F) (hUV : Disjoint U V)
    (E E' : SetRel H H) (hE : E ⊆ U ×ˢ V) (hE' : E' ⊆ U ×ˢ V) :
    (restrictedIdentity F ∪ E) ○ (restrictedIdentity F ∪ E') =
      restrictedIdentity F ∪ (E ∪ E') := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨z, hxz | hxz, hzy | hzy⟩
    · exact Or.inl ⟨hxz.1.trans hzy.1, hxz.2⟩
    · exact Or.inr (Or.inr (hxz.1 ▸ hzy))
    · exact Or.inr (Or.inl (hzy.1 ▸ hxz))
    · exact (Set.disjoint_left.mp hUV (hE' hzy).1 (hE hxz).2).elim
  · rintro (hxy | hxy | hxy)
    · exact ⟨x, Or.inl ⟨rfl, hxy.2⟩, Or.inl hxy⟩
    · exact ⟨y, Or.inr hxy, Or.inl ⟨rfl, hV (hE hxy).2⟩⟩
    · exact ⟨x, Or.inl ⟨rfl, hU (hE' hxy).1⟩, Or.inr hxy⟩

/-- Removing the hub leaves exactly the desired pair between its two neighbours. -/
theorem hub_pair_relation {H : Type*} (u v z : H) (huz : u ≠ z) (hvz : v ≠ z) :
    restrictedIdentity {x | x ≠ z} ○ (SetRel.id ∪ {(u, z)}) ○
      (SetRel.id ∪ {(z, v)}) ○ restrictedIdentity {x | x ≠ z} =
        restrictedIdentity {x | x ≠ z} ∪ {(u, v)} := by
  ext ⟨a, b⟩
  simp only [SetRel.comp, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff,
    SetRel.id, restrictedIdentity, Prod.mk.injEq]
  aesop

/-- A permutation and its inverse form a unit in the full relation monoid. -/
def permutationUnit {H : Type*} (σ : Equiv.Perm H) : (RelationMonoid H)ˣ where
  val := .ofRel (Function.graph σ)
  inv := .ofRel (Function.graph σ.symm)
  val_inv := by
    apply RelationMonoid.ext
    change Function.graph σ ○ Function.graph σ.symm = SetRel.id
    ext ⟨a, b⟩
    simp [SetRel.comp, Function.graph, SetRel.id]
  inv_val := by
    apply RelationMonoid.ext
    change Function.graph σ.symm ○ Function.graph σ = SetRel.id
    ext ⟨a, b⟩
    simp [SetRel.comp, Function.graph, SetRel.id]

/-- Permutation conjugation relabels both endpoints of every relation edge. -/
theorem permutation_conjugate_relation {H : Type*} (σ : Equiv.Perm H) (R : SetRel H H) :
    Function.graph σ ○ R ○ Function.graph σ.symm = {xy | (σ xy.1, σ xy.2) ∈ R} := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨c, ⟨d, had, hdc⟩, hcb⟩
    change σ a = d at had
    change σ.symm c = b at hcb
    have hc : c = σ b := by rw [← hcb, σ.apply_symm_apply]
    rwa [← had, hc] at hdc
  · intro hab
    exact ⟨σ b, ⟨σ a, rfl, hab⟩, σ.symm_apply_apply b⟩

/-- Unit lifts move the initial added pair to any other ordered pair of distinct points. -/
theorem pair_conjugate {A H : Type*} [Monoid A] {m : ℕ}
    (ι : A →ₙ* Diagram m) (φ : A →* RelationMonoid H)
    (hlift : ∀ σ : Equiv.Perm H, ∃ p : Aˣ, φ p = (permutationUnit σ).val)
    (a : A) (ha : IsIdempotentElem a) (x y : H) (hxy : x ≠ y)
    (himage : (φ a).toRel = SetRel.id ∪ {(x, y)}) (u v : H) (huv : u ≠ v) :
    ∃ s : A, IsIdempotentElem s ∧ (φ s).toRel = SetRel.id ∪ {(u, v)} ∧
      ((ι 1).missing (ι s)).ncard ≤ 2 * ((ι 1).missing (ι a)).ncard := by
  have hinj {r s : H} (hrs : r ≠ s) : Function.Injective (fun b : Bool => if b then s else r) := by
    intro b c h
    cases b <;> cases c <;> simp_all
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun b : Bool => if b then v else u) (fun b : Bool => if b then y else x)
    (hinj huv) (hinj hxy)
  have hσu : σ u = x := by simpa using hσ false
  have hσv : σ v = y := by simpa using hσ true
  obtain ⟨p, hp⟩ := hlift σ
  have hunit : Units.map φ p = permutationUnit σ := Units.ext hp
  have hinv : φ (↑p⁻¹ : A) = (↑(permutationUnit σ)⁻¹ : RelationMonoid H) :=
    congrArg (fun q : (RelationMonoid H)ˣ => (↑q⁻¹ : RelationMonoid H)) hunit
  refine ⟨p * a * (↑p⁻¹ : A), ?_, ?_, conjugate_missing_bound ι p a⟩
  · change (↑p * a * ↑p⁻¹) * (↑p * a * ↑p⁻¹) = ↑p * a * ↑p⁻¹
    simp only [mul_assoc, Units.inv_mul_cancel_left, ← mul_assoc a a, ha.eq]
  · rw [map_mul, map_mul, hp, hinv, RelationMonoid.toRel_mul, RelationMonoid.toRel_mul, himage]
    change Function.graph σ ○ (SetRel.id ∪ {(x, y)}) ○ Function.graph σ.symm = _
    rw [permutation_conjugate_relation, ← hσu, ← hσv]
    ext ⟨r, s⟩
    simp [SetRel.id, σ.injective.eq_iff]

/-- Restricting an idempotent sandwich preserves the new pair and supplies all unit lifts. -/
theorem smaller_relation_instance {A H : Type*} [Monoid A] [Finite A] {m : ℕ}
    (ι : A →ₙ* Diagram m) (φ : A →* RelationMonoid H) (hφ : Function.Surjective φ)
    (b b' : A) (hb : IsIdempotentElem b) (hbb' : b * b' = b') (hb'b : b' * b = b')
    (F : Set H)
    (hiPi : restrictedIdentity F ○ (φ b).toRel ○ restrictedIdentity F = restrictedIdentity F)
    (x y : F)
    (hpair : restrictedIdentity F ○ (φ b').toRel ○ restrictedIdentity F =
      restrictedIdentity F ∪ {(x.val, y.val)}) :
    ∃ d : hb.Corner, ∃ hd : IsIdempotentElem d, ∃ ψ : hd.Corner →* RelationMonoid F,
      Function.Surjective ψ ∧
      (∀ σ : Equiv.Perm F, ∃ p : hd.Cornerˣ, ψ p = (permutationUnit σ).val) ∧
      (∀ w, (ψ w).toRel = {xy : F × F | (xy.1.val, xy.2.val) ∈ (φ w.val.val).toRel}) ∧
      ∃ v : hd.Corner, IsIdempotentElem v ∧ (ψ v).toRel = SetRel.id ∪ {(x, y)} ∧
        ((ι d.val).missing (ι v.val.val)).ncard ≤ 2 * ((ι b).missing (ι b')).ncard := by
  let P := (φ b).toRel
  let i := restrictedIdentity F
  let Q := P ○ i ○ P
  have hP : IsIdempotentElem (φ b) := by rw [IsIdempotentElem, ← map_mul, hb.eq]
  have hPP : P ○ P = P := congrArg RelationMonoid.toRel hP.eq
  obtain ⟨hQ, ρ, hρ⟩ := relation_corner_equiv P F hPP hiPi
  have hident := relation_corner_identities P i hPP hiPi
  let q : hP.Corner := ⟨.ofRel Q, (Subsemigroup.mem_corner_iff hP).mpr
    ⟨RelationMonoid.ext hident.2.1, RelationMonoid.ext hident.2.2.1⟩⟩
  have hq : IsIdempotentElem q := Subtype.ext hQ.eq
  let θ := cornerMap φ.toMulHom hb hP rfl
  have hθ : Function.Surjective θ := cornerMap_surjective φ.toMulHom hφ hb hP rfl
  obtain ⟨d, hd, hθd, hminimal⟩ := minimal_idempotent_lift θ.toMulHom hθ q hq
  let γ := cornerMap θ.toMulHom hd hq hθd
  let equiv := (cornerFlatten hP q hq).trans ρ
  let ψ := equiv.toMonoidHom.comp γ
  have hψ : Function.Surjective ψ :=
    equiv.surjective.comp (cornerMap_surjective θ.toMulHom hθ hd hq hθd)
  have hψrel (w : hd.Corner) :
      (ψ w).toRel = {xy : F × F | (xy.1.val, xy.2.val) ∈ (φ w.val.val).toRel} :=
    hρ _
  have hψunits (σ : Equiv.Perm F) : ∃ p : hd.Cornerˣ, ψ p = (permutationUnit σ).val := by
    obtain ⟨w, hw⟩ := hψ (permutationUnit σ).val
    have hunitψ : IsUnit (ψ w) := hw.symm ▸ (permutationUnit σ).isUnit
    have hunitγ : IsUnit (γ w) := by
      have h := hunitψ.map equiv.symm.toMonoidHom
      simpa only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply] using h
    obtain ⟨p, hp⟩ := minimal_corner_reflects_units θ.toMulHom hd hq hθd hminimal w hunitγ
    exact ⟨p, hp ▸ hw⟩
  have hdimage : φ d.val = RelationMonoid.ofRel Q := congrArg Subtype.val hθd
  let b'c : hb.Corner := ⟨b', (Subsemigroup.mem_corner_iff hb).mpr ⟨hbb', hb'b⟩⟩
  let w : hd.Corner := ⟨d * b'c * d, b'c, rfl⟩
  have hwimage : (ψ w).toRel = SetRel.id ∪ {(x, y)} := by
    rw [hψrel]
    change {xy : F × F | (xy.1.val, xy.2.val) ∈ (φ (d.val * b' * d.val)).toRel} = _
    rw [map_mul, map_mul, hdimage, RelationMonoid.toRel_mul, RelationMonoid.toRel_mul,
      RelationMonoid.toRel_ofRel]
    have habsorb : P ○ (φ b').toRel ○ P = (φ b').toRel := by
      change ((φ b * φ b') * φ b).toRel = _
      rw [← map_mul, ← map_mul, hbb', hb'b]
    have hsandwich : i ○ (Q ○ (φ b').toRel ○ Q) ○ i = i ∪ {(x.val, y.val)} := by
      calc
        i ○ (Q ○ (φ b').toRel ○ Q) ○ i =
            (i ○ Q) ○ (φ b').toRel ○ (Q ○ i) := by simp only [SetRel.comp_assoc]
        _ = i ○ (P ○ (φ b').toRel ○ P) ○ i := by
          rw [hident.2.2.2.1, hident.2.2.2.2.1]
          simp only [SetRel.comp_assoc]
        _ = i ∪ {(x.val, y.val)} := by rw [habsorb]; exact hpair
    ext ⟨r, s⟩
    have hmem : (r.val, s.val) ∈ i ○ (Q ○ (φ b').toRel ○ Q) ○ i ↔
        (r.val, s.val) ∈ Q ○ (φ b').toRel ○ Q := by
      simp [i, SetRel.comp, restrictedIdentity, r.property, s.property]
    change (r.val, s.val) ∈ Q ○ (φ b').toRel ○ Q ↔ (r, s) ∈ SetRel.id ∪ {(x, y)}
    rw [← hmem, hsandwich]
    simp [i, restrictedIdentity, SetRel.id, Subtype.ext_iff]
  have hiPair : IsIdempotentElem (ψ w) := by
    apply RelationMonoid.ext
    rw [RelationMonoid.toRel_mul, hwimage]
    ext ⟨r, s⟩
    simp only [SetRel.comp, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff,
      SetRel.id, Prod.mk.injEq]
    aesop
  obtain ⟨k, hk, hv⟩ := finite_idempotent_pow w
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  refine ⟨d, hd, ψ, hψ, hψunits, hψrel, w ^ (k + 1), hv, ?_, ?_⟩
  · rw [map_pow, hiPair.pow_succ_eq, hwimage]
  · let ιb : hb.Corner →ₙ* Diagram m := ι.comp (MulMemClass.subtype _)
    let ιd : hd.Corner →ₙ* Diagram m := ιb.comp (MulMemClass.subtype _)
    have hid : Diagram.comp (ι d.val) (ι d.val) = ι d.val :=
      (map_mul ιb d d).symm.trans (congrArg ιb hd.eq)
    have hib : Diagram.comp (ι b) (ι b) = ι b :=
      (map_mul ι b b).symm.trans (congrArg ι hb.eq)
    obtain ⟨hbd, hdb⟩ := (Subsemigroup.mem_corner_iff hb).mp d.property
    have hcontext : Diagram.comp (Diagram.comp (ι d.val) (ι b)) (ι d.val) = ι d.val := by
      change ι d.val * ι b * ι d.val = ι d.val
      rw [← map_mul, hdb]
      exact hid
    have hb' : ι b' ∈ (ι b).corner :=
      ⟨(map_mul ι b b').symm.trans (congrArg ι hbb'),
        (map_mul ι b' b).symm.trans (congrArg ι hb'b)⟩
    have hw : ιd w ∈ (ι d.val).corner := map_identity_corner ιd w
    have htransport := missing_context_card (ι b) (ι d.val) (ι d.val) (ι d.val) (ι b')
      hib hid hcontext hb' (by
        change ι d.val * ι b' * ι d.val ∈ (ι d.val).corner
        rw [← map_mul, ← map_mul]
        exact hw)
    have hpow := Diagram.missing_pow_succ (ι d.val) (ιd w) hid hw k
    rw [← map_positive_pow] at hpow
    apply (Set.ncard_le_ncard hpow).trans
    change ((ι d.val).missing (ι (d.val * b' * d.val))).ncard ≤ _
    rw [map_mul, map_mul]
    exact htransport

end Complementation.Internal

end Complexity.FiniteAutomaton
