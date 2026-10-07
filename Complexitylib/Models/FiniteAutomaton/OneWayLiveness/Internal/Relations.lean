/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Corners

/-!
# One-way-liveness proof: Relations

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Automata/Relations.lean

Module and namespace names, imports, and formatting are adapted to complexitylib.
The machine definitions are shared through `Models.FiniteAutomaton.Defs`.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace BRel
variable {H : Type*}

@[simp] lemma restrictedId_holds (F : Set H) (x y : H) :
    (restrictedId F).holds x y ↔ x = y ∧ x ∈ F := Iff.rfl
lemma restrictedId_idem (F : Set H) : restrictedId F * restrictedId F = restrictedId F := by
  ext x z; simp

lemma restrictedId_mul (F : Set H) (a : BRel H) (x y : H) :
    (restrictedId F * a).holds x y ↔ x ∈ F ∧ a.holds x y := by simp
lemma mul_restrictedId (F : Set H) (a : BRel H) (x y : H) :
    (a * restrictedId F).holds x y ↔ a.holds x y ∧ y ∈ F := by simp

lemma corner_supported {F : Set H} (z : Corner (restrictedId F) (restrictedId_idem F))
    {x y : H} (h : z.val.holds x y) : x ∈ F ∧ y ∈ F := by
  constructor
  · have h' : (restrictedId F * z.val).holds x y := by rw [z.left]; exact h
    exact ((restrictedId_mul F _ x y).mp h').1
  · have h' : (z.val * restrictedId F).holds x y := by rw [z.right]; exact h
    exact ((mul_restrictedId F _ x y).mp h').2

/-- Restrict a relation in the corner of a partial identity to its underlying subset. -/
def restriction (F : Set H) : Corner (restrictedId F) (restrictedId_idem F) →* BRel F where
  toFun z := ⟨fun x y => z.val.holds x.val y.val⟩
  map_one' := by ext x y; change (x.val = y.val ∧ x.val ∈ F) ↔ x = y; simp [Subtype.ext_iff]
  map_mul' z w := by
    ext x y
    change (∃ k : H, z.val.holds x.val k ∧ w.val.holds k y.val) ↔
      ∃ k : F, z.val.holds x.val k.val ∧ w.val.holds k.val y.val
    constructor
    · rintro ⟨k, hz, hw⟩
      exact ⟨⟨k, (corner_supported z hz).2⟩, hz, hw⟩
    · rintro ⟨k, hz, hw⟩
      exact ⟨k.val, hz, hw⟩

/-- Extend a relation on a subset by leaving all other pairs unrelated. -/
def extend (F : Set H) (a : BRel F) : BRel H :=
  ⟨fun x y => ∃ hx : x ∈ F, ∃ hy : y ∈ F, a.holds ⟨x, hx⟩ ⟨y, hy⟩⟩

/-- View an extended relation as an element of the partial-identity corner. -/
def extension (F : Set H) (a : BRel F) : Corner (restrictedId F) (restrictedId_idem F) :=
  ⟨extend F a, by ext x y; simp only [restrictedId_mul]; exact ⟨And.right, fun h => ⟨h.choose, h⟩⟩,
    by ext x y; simp only [mul_restrictedId]; exact ⟨And.left, fun h => ⟨h, h.choose_spec.choose⟩⟩⟩

/-- The corner of a partial identity is the relation monoid on its subset. -/
def restrictionEquiv (F : Set H) : Corner (restrictedId F) (restrictedId_idem F) ≃* BRel F :=
  { restriction F with
    invFun := extension F
    left_inv := by
      intro z
      apply Corner.ext
      ext x y
      change (∃ hx : x ∈ F, ∃ hy : y ∈ F, z.val.holds x y) ↔ z.val.holds x y
      exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨(corner_supported z h).1, (corner_supported z h).2, h⟩⟩
    right_inv := by
      intro a
      ext x y
      change (∃ hx : x.val ∈ F, ∃ hy : y.val ∈ F, a.holds ⟨x.val, hx⟩ ⟨y.val, hy⟩) ↔ a.holds x y
      simp }

/-- Restrict a relation corner with a split subidentity. -/
lemma relation_corner {P : BRel H} (hP : P * P = P) (F : Set H)
    (hF : restrictedId F * P * restrictedId F = restrictedId F) :
    let Q := P * restrictedId F * P
    ∃ hQ : Q * Q = Q, ∃ θ : Corner Q hQ ≃* BRel F,
      (∀ z x y, (θ z).holds x y ↔ z.val.holds x.val y.val) ∧ P * Q = Q ∧ Q * P = Q := by
  let E := restrictedId F
  have hE : E * E = E := restrictedId_idem F
  let u := P * E
  let v := E * P
  let Q := P * E * P
  have huv : u * v = Q := by dsimp [u, v, Q]; rw [← mul_assoc, mul_assoc P E E, hE]
  have hvu : v * u = E := by
    dsimp [u, v]
    rw [mul_assoc E P, ← mul_assoc P P E, hP]
    simpa only [E, mul_assoc] using hF
  have hu : u * E = u := by dsimp [u]; rw [mul_assoc, hE]
  have hv : E * v = v := by dsimp [v]; rw [← mul_assoc, hE]
  have hQ : Q * Q = Q := by
    rw [← huv, mul_assoc, ← mul_assoc v u, hvu, ← mul_assoc, hu]
  have hpq : P * Q = Q := by dsimp [Q]; rw [← mul_assoc, ← mul_assoc, hP]
  have hqp : Q * P = Q := by dsimp [Q]; rw [mul_assoc, hP]
  let θ := (Corner.equivOfSplit (he := hQ) (hf := hE) u v huv hvu hu hv).trans (restrictionEquiv F)
  refine ⟨hQ, θ, ?_, hpq, hqp⟩
  intro z x y
  change (v * z.val * u).holds x.val y.val ↔ z.val.holds x.val y.val
  have hpz : P * z.val = z.val := by
    calc
      _ = P * (Q * z.val) := by rw [z.left]
      _ = z.val := by rw [← mul_assoc, hpq, z.left]
  have hzp : z.val * P = z.val := by
    calc
      _ = (z.val * Q) * P := by rw [z.right]
      _ = z.val := by rw [mul_assoc, hqp, z.right]
  have heq : v * z.val * u = E * z.val * E := by
    dsimp [u, v]
    rw [mul_assoc E P, hpz, ← mul_assoc, mul_assoc E z.val P, hzp]
  rw [heq, mul_restrictedId, restrictedId_mul]
  simp
end BRel

namespace BRel
variable {H : Type*}
/-- The graph relation of a permutation. -/
def permGraph (σ : Equiv.Perm H) : BRel H := ⟨fun x y => σ x = y⟩
@[simp] lemma permGraph_holds (σ : Equiv.Perm H) (x y : H) :
    (permGraph σ).holds x y ↔ σ x = y := Iff.rfl

/-- The invertible relation represented by a permutation. -/
def permUnit (σ : Equiv.Perm H) : (BRel H)ˣ where
  val := permGraph σ
  inv := permGraph σ.symm
  val_inv := by ext x y; simp
  inv_val := by ext x y; simp

/-- The identity with one extra pair. -/
def addEdge (x y : H) : BRel H := ⟨fun u v => u = v ∨ u = x ∧ v = y⟩
@[simp] lemma addEdge_holds (x y u v : H) :
    (addEdge x y).holds u v ↔ u = v ∨ u = x ∧ v = y := Iff.rfl
lemma addEdge_idem (x y : H) : addEdge x y * addEdge x y = addEdge x y := by
  ext u v
  simp only [mul_holds, addEdge_holds]
  aesop
lemma addEdge_ne_one {x y : H} (hxy : x ≠ y) : addEdge x y ≠ 1 := by
  intro he
  have hh : (addEdge x y).holds x y := Or.inr ⟨rfl, rfl⟩
  rw [he] at hh
  exact hxy hh

lemma conjugate_addEdge (σ : Equiv.Perm H) (x y : H) :
    (↑(permUnit σ)⁻¹ : BRel H) * addEdge x y * ↑(permUnit σ) = addEdge (σ x) (σ y) := by
  ext u v
  change (∃ k, (∃ j, σ.symm u = j ∧ (j = k ∨ j = x ∧ k = y)) ∧ σ k = v) ↔
    u = v ∨ u = σ x ∧ v = σ y
  constructor
  · rintro ⟨k, ⟨j, hj, hk⟩, hv⟩
    subst j
    rcases hk with hk | ⟨hx, rfl⟩
    · exact Or.inl (by rw [← hk, σ.apply_symm_apply] at hv; exact hv)
    · exact Or.inr ⟨(σ.symm_apply_eq).mp hx, hv.symm⟩
  · rintro (rfl | ⟨rfl, rfl⟩)
    · exact ⟨σ.symm u, ⟨σ.symm u, rfl, Or.inl rfl⟩, σ.apply_symm_apply u⟩
    · exact ⟨y, ⟨x, σ.symm_apply_apply x, Or.inr ⟨rfl, rfl⟩⟩, rfl⟩

lemma exists_perm_pair {x y u v : H} (hxy : x ≠ y) (huv : u ≠ v) :
    ∃ σ : Equiv.Perm H, σ x = u ∧ σ y = v := by
  let f : Bool → H := fun b => if b then y else x
  let g : Bool → H := fun b => if b then v else u
  have hf : Function.Injective f := by
    intro b c h
    cases b <;> cases c <;> simp_all [f, Ne.symm hxy]
  have hg : Function.Injective g := by
    intro b c h
    cases b <;> cases c <;> simp_all [g, Ne.symm huv]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  exact ⟨σ, hσ false, hσ true⟩
end BRel

/-- Every target unit admits a unit lift (unitality included in the homomorphism). -/
def HasUnitLifts {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) : Prop :=
  ∀ u : Nˣ, ∃ v : Mˣ, f (↑v) = (↑u)

lemma unit_image_inv {M N : Type*} [Monoid M] [Monoid N] (f : M →* N)
    (u : Mˣ) (v : Nˣ) (h : f (↑u) = (↑v)) : f (↑u⁻¹) = (↑v⁻¹) := by
  have he : Units.map f u = v := Units.ext h
  exact congrArg (fun w : Nˣ => (↑w⁻¹ : N)) he

lemma conjugate_lift {M H A : Type*} [Monoid M] [Fintype A]
    (ρ : M →* Pairing (A ⊕ A)) (f : M →* BRel H) (hl : HasUnitLifts f)
    (a : M) (ha : a * a = a) (x y : H) (hxy : x ≠ y) (hfa : f a = BRel.addEdge x y)
    (u v : H) (huv : u ≠ v) :
    ∃ b : M, b * b = b ∧ f b = BRel.addEdge u v ∧ Pairing.rank (ρ b) = Pairing.rank (ρ a) := by
  obtain ⟨σ, hx, hy⟩ := BRel.exists_perm_pair hxy huv
  obtain ⟨w, hw⟩ := hl (BRel.permUnit σ)
  refine ⟨(↑w⁻¹ : M) * a * (↑w : M), ?_, ?_, ?_⟩
  · calc
      _ = (↑w⁻¹ : M) * (a * ((↑w : M) * ↑w⁻¹) * a) * ↑w := by simp only [mul_assoc]
      _ = (↑w⁻¹ : M) * a * ↑w := by rw [Units.mul_inv, mul_one, ha]
  · rw [map_mul, map_mul, hw, unit_image_inv f w _ hw, hfa, BRel.conjugate_addEdge, hx, hy]
  · rw [map_mul, map_mul]
    change Pairing.rank (((Units.map ρ w⁻¹ : (Pairing (A ⊕ A))ˣ) : Pairing (A ⊕ A)) * ρ a *
      ((Units.map ρ w : (Pairing (A ⊕ A))ˣ) : Pairing (A ⊕ A))) = _
    rw [Pairing.rank_mul_unit, Pairing.rank_unit_mul]

/-- Disjoint source/target points and a separate intermediate hub. -/
structure RectangleFrame (H I J : Type*) where
  /-- The row vertices of the frame. -/
  left : I → H
  /-- The column vertices of the frame. -/
  right : J → H
  /-- The distinguished vertex outside the rows and columns. -/
  hub : H
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  disjoint : ∀ i j, left i ≠ right j
  left_ne_hub : ∀ i, left i ≠ hub
  right_ne_hub : ∀ j, right j ≠ hub

namespace RectangleFrame
variable {H I J : Type*} (F : RectangleFrame H I J)
/-- The partial identity outside the frame hub. -/
def base : BRel H := BRel.restrictedId {x | x ≠ F.hub}
/-- Add the selected row-to-column edges to the identity outside the hub. -/
def rel (E : Set (I × J)) : BRel H :=
  ⟨fun x y => (x = y ∧ x ≠ F.hub) ∨ ∃ p ∈ E, x = F.left p.1 ∧ y = F.right p.2⟩

@[simp] lemma rel_holds (E : Set (I × J)) (x y : H) :
    (F.rel E).holds x y ↔ (x = y ∧ x ≠ F.hub) ∨ ∃ p ∈ E, x = F.left p.1 ∧ y = F.right p.2 := Iff.rfl
lemma rel_empty : F.rel ∅ = F.base := by ext x y; simp [base]

lemma rel_mul (E D : Set (I × J)) : F.rel E * F.rel D = F.rel (E ∪ D) := by
  ext x y
  constructor
  · rintro ⟨k, (⟨hx, hn⟩ | ⟨p, hp, hx, hk⟩), hy⟩
    · subst k
      rcases hy with ⟨hxy, _⟩ | ⟨p, hp, hp1, hp2⟩
      · exact Or.inl ⟨hxy, hn⟩
      · exact Or.inr ⟨p, Or.inr hp, hp1, hp2⟩
    · rcases hy with ⟨hky, _⟩ | ⟨q, _hq, hq1, _hq2⟩
      · exact Or.inr ⟨p, Or.inl hp, hx, hky.symm.trans hk⟩
      · exact (F.disjoint q.1 p.2 (hq1.symm.trans hk)).elim
  · rintro (⟨rfl, hn⟩ | ⟨p, hp | hp, rfl, rfl⟩)
    · exact ⟨x, Or.inl ⟨rfl, hn⟩, Or.inl ⟨rfl, hn⟩⟩
    · exact ⟨F.right p.2, Or.inr ⟨p, hp, rfl, rfl⟩,
        Or.inl ⟨rfl, F.right_ne_hub p.2⟩⟩
    · exact ⟨F.left p.1, Or.inl ⟨rfl, F.left_ne_hub p.1⟩,
        Or.inr ⟨p, hp, rfl, rfl⟩⟩

lemma rel_idem (E : Set (I × J)) : F.rel E * F.rel E = F.rel E := by
  rw [rel_mul, Set.union_self]
lemma rel_absorb {E D : Set (I × J)} (h : E ⊆ D) :
    F.rel E * F.rel D = F.rel D ∧ F.rel D * F.rel E = F.rel D := by
  rw [rel_mul, rel_mul, Set.union_eq_right.mpr h, Set.union_eq_left.mpr h]
  exact ⟨rfl, rfl⟩

lemma generator_image (i : I) (j : J) :
    F.base * BRel.addEdge (F.left i) F.hub * BRel.addEdge F.hub (F.right j) * F.base =
      F.rel {(i,j)} := by
  have hl := F.left_ne_hub i
  have hr := F.right_ne_hub j
  have he : F.base * BRel.addEdge (F.left i) F.hub * BRel.addEdge F.hub (F.right j) * F.base =
      F.base * (BRel.addEdge (F.left i) F.hub * BRel.addEdge F.hub (F.right j)) * F.base := by
    simp only [mul_assoc]
  rw [he]
  ext x y
  simp only [base, BRel.mul_holds, BRel.addEdge_holds, rel_holds,
    Set.mem_singleton_iff, exists_eq_left]
  aesop

lemma restricted_old (E : Set (I × J)) (K : Set H)
    (hK : ∀ x ∈ K, x ≠ F.hub)
    (hE : ∀ p ∈ E, F.left p.1 ∉ K ∨ F.right p.2 ∉ K) :
    BRel.restrictedId K * F.rel E * BRel.restrictedId K = BRel.restrictedId K := by
  ext x y
  simp only [BRel.mul_restrictedId, BRel.restrictedId_mul, BRel.restrictedId_holds]
  constructor
  · rintro ⟨⟨hx, (⟨hxy, _⟩ | ⟨p, hp, rfl, rfl⟩)⟩, hy⟩
    · exact ⟨hxy, hx⟩
    · exact ((hE p hp).elim (fun h => h hx) (fun h => h hy)).elim
  · rintro ⟨rfl, hx⟩
    exact ⟨⟨hx, Or.inl ⟨rfl, hK x hx⟩⟩, hx⟩

lemma restricted_new (E : Set (I × J)) (K : Set H)
    (hK : ∀ x ∈ K, x ≠ F.hub)
    (hE : ∀ p ∈ E, F.left p.1 ∉ K ∨ F.right p.2 ∉ K)
    (i : I) (j : J) (hi : F.left i ∈ K) (hj : F.right j ∈ K) :
    let u : K := ⟨F.left i,hi⟩
    let v : K := ⟨F.right j,hj⟩
    ∀ x y : K, (F.rel (insert (i,j) E)).holds x.val y.val ↔ (BRel.addEdge u v).holds x y := by
  intro u v x y
  simp only [rel_holds, BRel.addEdge_holds]
  constructor
  · rintro (⟨hxy, _⟩ | ⟨p, hp, hx, hy⟩)
    · exact Or.inl (Subtype.ext hxy)
    · rcases hp with rfl | hp
      · exact Or.inr ⟨Subtype.ext hx, Subtype.ext hy⟩
      · exact ((hE p hp).elim (fun h => h (hx ▸ x.property)) (fun h => h (hy ▸ y.property))).elim
  · rintro (rfl | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, hK x.val x.property⟩
    · exact Or.inr ⟨(i,j), Or.inl rfl, rfl, rfl⟩
end RectangleFrame

namespace Corner
variable {M : Type*} [Monoid M] {e : M} {he : e * e = e}

/-- Flatten an iterated corner into the corner of the underlying idempotent. -/
def flattenEquiv (q : Corner e he) (hq : q * q = q) :
    Corner q hq ≃* Corner q.val (val_idempotent q hq) where
  toFun z := ⟨z.val.val, congrArg Corner.val z.left, congrArg Corner.val z.right⟩
  invFun z :=
    ⟨⟨z.val, by
      calc
        e * z.val = e * (q.val * z.val) := by rw [z.left]
        _ = z.val := by rw [← mul_assoc, q.left, z.left], by
      calc
        z.val * e = (z.val * q.val) * e := by rw [z.right]
        _ = z.val := by rw [mul_assoc, q.right, z.right]⟩,
      Corner.ext z.left, Corner.ext z.right⟩
  left_inv z := Corner.ext (Corner.ext rfl)
  right_inv z := Corner.ext rfl
  map_mul' _ _ := Corner.ext rfl
end Corner

lemma HasUnitLifts.comp_equiv {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]
    {f : M →* N} (hf : HasUnitLifts f) (e : N ≃* P) : HasUnitLifts (e.toMonoidHom.comp f) := by
  intro u
  obtain ⟨v, hv⟩ := hf (Units.map e.symm.toMonoidHom u)
  refine ⟨v, ?_⟩
  change e (f (↑v)) = (↑u)
  rw [hv]
  exact e.apply_symm_apply _

lemma min_rank_corner_unitLifts {M N A : Type*} [Monoid M] [Monoid N] [Finite M] [Fintype A]
    (ρ : M →* Pairing (A ⊕ A)) (hρ : Function.Injective ρ)
    (f : M →* N) (hs : Function.Surjective f)
    (e : M) (he : e * e = e) (q : N) (hq : q * q = q) (hf : f e = q)
    (hmin : ∀ z : M, z * z = z → f z = q → Pairing.rank (ρ e) ≤ Pairing.rank (ρ z)) :
    HasUnitLifts (Corner.mapTo (he := he) (hq := hq) f hf) := by
  intro u
  obtain ⟨y, hy⟩ := Corner.mapTo_surjective (he := he) (hq := hq) f hf hs (↑u)
  have hunit : IsUnit y := min_rank_corner_isUnit ρ hρ f e he q hq hf hmin y (hy ▸ u.isUnit)
  obtain ⟨v, rfl⟩ := hunit
  exact ⟨v, hy⟩

namespace BRel
variable {H : Type*}
lemma restricted_sandwich {P N : BRel H} (F : Set H)
    (hF : restrictedId F * P * restrictedId F = restrictedId F)
    (hPN : P * N = N) (hNP : N * P = N) :
    let Q := P * restrictedId F * P
    restrictedId F * (Q * N * Q) * restrictedId F = restrictedId F * N * restrictedId F := by
  let E := restrictedId F
  have hl : E * (P * E * P) = E * P := by rw [← mul_assoc, ← mul_assoc, hF]
  have hr : (P * E * P) * E = P * E := by rw [mul_assoc P E P, mul_assoc, hF]
  change E * ((P * E * P) * N * (P * E * P)) * E = E * N * E
  calc
    _ = (E * (P * E * P)) * N * ((P * E * P) * E) := by simp only [mul_assoc]
    _ = (E * P) * N * (P * E) := by rw [hl, hr]
    _ = E * (P * N * P) * E := by simp only [mul_assoc]
    _ = E * N * E := by rw [hPN, hNP]

lemma sandwich_holds_on {P N : BRel H} (F : Set H)
    (hF : restrictedId F * P * restrictedId F = restrictedId F)
    (hPN : P * N = N) (hNP : N * P = N) (x y : F) :
    ((P * restrictedId F * P) * N * (P * restrictedId F * P)).holds x.val y.val ↔
      N.holds x.val y.val := by
  have hh := congrArg (fun a : BRel H => a.holds x.val y.val) (restricted_sandwich F hF hPN hNP)
  simpa only [mul_restrictedId, restrictedId_mul, x.property, y.property,
    true_and, and_true, eq_iff_iff] using hh
end BRel

end Complexity.FiniteAutomaton
