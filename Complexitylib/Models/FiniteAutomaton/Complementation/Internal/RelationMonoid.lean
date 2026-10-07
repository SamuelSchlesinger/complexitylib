/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Corners

/-!
# Two-way complementation: relation monoid

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/RelationMonoid.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace Complementation.Internal

open scoped SetRel

/-- Identity restricted to the retained points. -/
def restrictedIdentity {α : Type*} (F : Set α) : SetRel α α :=
  {(x, y) | x = y ∧ x ∈ F}

@[simp]
theorem restrictedIdentity_comp_self {α : Type*} (F : Set α) :
    restrictedIdentity F ○ restrictedIdentity F = restrictedIdentity F := by
  ext ⟨x, y⟩
  simp [SetRel.comp, restrictedIdentity]

/-- Singleton contexts test an individual relation edge. -/
theorem singleton_context {α : Type*} (R : SetRel α α) (p q : α) :
    restrictedIdentity {p} ○ R ○ restrictedIdentity {q} =
      {(x, y) | x = p ∧ y = q ∧ (p, q) ∈ R} := by
  ext ⟨x, y⟩
  simp [SetRel.comp, restrictedIdentity]
  aesop

/-- Restriction-corner identities.
    The supporting relation `i` can be any idempotent with `iPi = i`. -/
theorem relation_corner_identities {α : Type*} (P i : SetRel α α)
    (hP : P ○ P = P) (hiPi : i ○ P ○ i = i) :
    let Q := P ○ i ○ P
    Q ○ Q = Q ∧ P ○ Q = Q ∧ Q ○ P = Q ∧
    Q ○ i = P ○ i ∧ i ○ Q = i ○ P ∧ i ○ Q ○ i = i := by
  have hPP (R : SetRel α α) : P ○ (P ○ R) = P ○ R := by
    rw [← SetRel.comp_assoc, hP]
  have hiPiR (R : SetRel α α) : i ○ (P ○ (i ○ R)) = i ○ R := by
    rw [← SetRel.comp_assoc i P, ← SetRel.comp_assoc, hiPi]
  dsimp
  simp [SetRel.comp_assoc, hPP, hiPiR, hP, hiPi]

/-- Restriction and extension are inverse on the two supported corners. -/
theorem relation_corner_inverse {α : Type*} (P i : SetRel α α)
    (hP : P ○ P = P) (hiPi : i ○ P ○ i = i) :
    (∀ Z, (P ○ i ○ P) ○ Z ○ (P ○ i ○ P) = Z → P ○ (i ○ Z ○ i) ○ P = Z) ∧
    (∀ A, i ○ A ○ i = A →
      (P ○ i ○ P) ○ (P ○ A ○ P) ○ (P ○ i ○ P) = P ○ A ○ P ∧
      i ○ (P ○ A ○ P) ○ i = A) := by
  have hPP (R : SetRel α α) : P ○ (P ○ R) = P ○ R := by
    rw [← SetRel.comp_assoc, hP]
  have hiPiR (R : SetRel α α) : i ○ (P ○ (i ○ R)) = i ○ R := by
    rw [← SetRel.comp_assoc i P, ← SetRel.comp_assoc, hiPi]
  constructor
  · intro Z hZ
    have hPZP : P ○ Z ○ P = Z := by
      conv_lhs => rw [← hZ]
      simpa only [SetRel.comp_assoc, hPP, hP] using hZ
    calc
      P ○ (i ○ Z ○ i) ○ P = P ○ (i ○ (P ○ Z ○ P) ○ i) ○ P := by rw [hPZP]
      _ = Z := by simpa only [SetRel.comp_assoc] using hZ
  · intro A hA
    constructor
    · calc
        (P ○ i ○ P) ○ (P ○ A ○ P) ○ (P ○ i ○ P) =
            P ○ (i ○ A ○ i) ○ P := by
              conv_lhs => rw [← hA]
              simp only [SetRel.comp_assoc, hPP, hiPiR]
        _ = P ○ A ○ P := by rw [hA]
    · conv_lhs => rw [← hA]
      simpa only [SetRel.comp_assoc, hiPiR, hiPi] using hA

/-- Extension preserves products on the supported relation corner. -/
theorem relation_corner_comp {α : Type*} (P i A B : SetRel α α)
    (hP : P ○ P = P) (hi : i ○ i = i) (hiPi : i ○ P ○ i = i)
    (hA : i ○ A ○ i = A) (hB : i ○ B ○ i = B) :
    (P ○ A ○ P) ○ (P ○ B ○ P) = P ○ (A ○ B) ○ P := by
  have hPP (R : SetRel α α) : P ○ (P ○ R) = P ○ R := by
    rw [← SetRel.comp_assoc, hP]
  have hiPiR (R : SetRel α α) : i ○ (P ○ (i ○ R)) = i ○ R := by
    rw [← SetRel.comp_assoc i P, ← SetRel.comp_assoc, hiPi]
  have hii (R : SetRel α α) : i ○ (i ○ R) = i ○ R := by
    rw [← SetRel.comp_assoc, hi]
  conv_lhs => rw [← hA, ← hB]
  simpa only [SetRel.comp_assoc, hPP, hiPiR, hii] using
    congrArg (fun R => P ○ R ○ P) (congrArg₂ SetRel.comp hA hB)

/-- Relations in path order, using the opposite of Mathlib's endomorphism monoid. -/
abbrev RelationMonoid (H : Type*) :=
  (CategoryTheory.End (show CategoryTheory.RelCat from H))ᵐᵒᵖ

namespace RelationMonoid

/-- Regard a binary relation as a path-ordered endomorphism. -/
def ofRel {H : Type*} (R : SetRel H H) : RelationMonoid H :=
  MulOpposite.op (.ofRel R)

/-- The underlying binary relation. -/
def toRel {H : Type*} (R : RelationMonoid H) : SetRel H H := R.unop.rel

@[ext]
theorem ext {H : Type*} {R S : RelationMonoid H} (h : R.toRel = S.toRel) : R = S :=
  MulOpposite.unop_injective (CategoryTheory.RelCat.Hom.ext _ _ h)

@[simp]
theorem toRel_ofRel {H : Type*} (R : SetRel H H) : (ofRel R).toRel = R := rfl

@[simp]
theorem toRel_mul {H : Type*} (R S : RelationMonoid H) :
    (R * S).toRel = R.toRel ○ S.toRel := rfl

@[simp]
theorem toRel_one {H : Type*} : (1 : RelationMonoid H).toRel = SetRel.id := rfl

end RelationMonoid

/-- Extending a relation on a subset and restricting it again loses no pairs. -/
theorem relation_extend_restrict {H : Type*} (F : Set H) (R : SetRel F F) :
    {xy : F × F | (xy.1.val, xy.2.val) ∈ (Prod.map Subtype.val Subtype.val) '' R} = R := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.exists, Prod.map_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨a, b, hab, hax, hby⟩
    exact (Subtype.ext hax ▸ Subtype.ext hby ▸ hab)
  · intro hxy
    exact ⟨x, y, hxy, rfl, rfl⟩

/-- Extension of restriction is precisely the identity sandwich on the subset. -/
theorem relation_restrict_extend {H : Type*} (F : Set H) (R : SetRel H H) :
    (Prod.map Subtype.val Subtype.val) '' {xy : F × F | (xy.1.val, xy.2.val) ∈ R} =
      restrictedIdentity F ○ R ○ restrictedIdentity F := by
  ext ⟨x, y⟩
  simp only [Set.mem_image, Prod.exists, Set.mem_ofPred_eq, Prod.map_apply, Prod.mk.injEq,
    SetRel.comp, restrictedIdentity]
  constructor
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact ⟨b.val, ⟨a.val, ⟨rfl, a.property⟩, hab⟩, rfl, b.property⟩
  · rintro ⟨b, ⟨a, ⟨rfl, hx⟩, hab⟩, rfl, hy⟩
    exact ⟨⟨x, hx⟩, ⟨b, hy⟩, hab, rfl, rfl⟩

/-- Extension of relations on a subset preserves path composition. -/
theorem relation_extend_comp {H : Type*} (F : Set H) (A B : SetRel F F) :
    (Prod.map Subtype.val Subtype.val) '' (A ○ B) =
      ((Prod.map Subtype.val Subtype.val) '' A) ○
        ((Prod.map Subtype.val Subtype.val) '' B) := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨⟨a, b⟩, ⟨c, hac, hcb⟩, hxy⟩
    cases hxy
    exact ⟨c.val, ⟨(a, c), hac, rfl⟩, (c, b), hcb, rfl⟩
  · rintro ⟨z, ⟨⟨a, b⟩, hab, habxy⟩, ⟨⟨c, d⟩, hcd, hcdxy⟩⟩
    have hbc : b = c := Subtype.ext ((congrArg Prod.snd habxy).trans
      (congrArg Prod.fst hcdxy).symm)
    subst c
    have hax : a.val = x := congrArg Prod.fst habxy
    have hdy : d.val = y := congrArg Prod.snd hcdxy
    exact ⟨(a, d), ⟨b, hab, hcd⟩, Prod.ext hax hdy⟩

/-- The full relation monoid on a subset is the compressed relation corner. -/
theorem relation_corner_equiv {H : Type*} (P : SetRel H H) (F : Set H)
    (hP : P ○ P = P) (hiPi : restrictedIdentity F ○ P ○ restrictedIdentity F =
      restrictedIdentity F) :
    ∃ hQ : IsIdempotentElem (RelationMonoid.ofRel (P ○ restrictedIdentity F ○ P)),
      ∃ ρ : hQ.Corner ≃* RelationMonoid F,
        ∀ Z, (ρ Z).toRel = {xy : F × F | (xy.1.val, xy.2.val) ∈ Z.val.toRel} := by
  let i := restrictedIdentity F
  let Q := P ○ i ○ P
  have hQ : IsIdempotentElem (RelationMonoid.ofRel Q) :=
    RelationMonoid.ext (relation_corner_identities P i hP hiPi).1
  have hZ (Z : hQ.Corner) : Q ○ Z.val.toRel ○ Q = Z.val.toRel := by
    obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff hQ).mp Z.property
    exact congrArg RelationMonoid.toRel ((congrArg (· * RelationMonoid.ofRel Q) hl).trans hr)
  let extend (A : RelationMonoid F) : SetRel H H :=
    (Prod.map Subtype.val Subtype.val) '' A.toRel
  have hsupp (A : RelationMonoid F) : i ○ extend A ○ i = extend A := by
    rw [← relation_restrict_extend F, relation_extend_restrict]
  let f (Z : hQ.Corner) : RelationMonoid F :=
    .ofRel {xy : F × F | (xy.1.val, xy.2.val) ∈ Z.val.toRel}
  let g (A : RelationMonoid F) : hQ.Corner :=
    ⟨.ofRel (P ○ extend A ○ P), (Subsemigroup.mem_corner_iff hQ).mpr (by
      have hs := (relation_corner_inverse P i hP hiPi).2 (extend A) (hsupp A) |>.1
      change Q ○ (P ○ extend A ○ P) ○ Q = P ○ extend A ○ P at hs
      have hQQ : Q ○ Q = Q := (relation_corner_identities P i hP hiPi).1
      constructor <;> apply RelationMonoid.ext
      · change Q ○ (P ○ extend A ○ P) = P ○ extend A ○ P
        conv_lhs => rw [← hs]
        simpa only [← SetRel.comp_assoc, hQQ] using hs
      · change (P ○ extend A ○ P) ○ Q = P ○ extend A ○ P
        conv_lhs => rw [← hs]
        simpa only [SetRel.comp_assoc, hQQ] using hs)⟩
  have hleft (Z : hQ.Corner) : g (f Z) = Z := by
    apply Subtype.ext
    apply RelationMonoid.ext
    change P ○ ((Prod.map Subtype.val Subtype.val) ''
      {xy : F × F | (xy.1.val, xy.2.val) ∈ Z.val.toRel}) ○ P = Z.val.toRel
    rw [relation_restrict_extend]
    exact (relation_corner_inverse P i hP hiPi).1 _ (hZ Z)
  have hright (A : RelationMonoid F) : f (g A) = A := by
    apply RelationMonoid.ext
    have hext : extend (f (g A)) = extend A := by
      change (Prod.map Subtype.val Subtype.val) '' {xy : F × F |
        (xy.1.val, xy.2.val) ∈ P ○ extend A ○ P} = extend A
      rw [relation_restrict_extend]
      exact (relation_corner_inverse P i hP hiPi).2 (extend A) (hsupp A) |>.2
    have hinj : Function.Injective
        (Prod.map (Subtype.val : F → H) (Subtype.val : F → H)) :=
      fun _ _ h => Prod.ext (Subtype.ext (congrArg Prod.fst h))
        (Subtype.ext (congrArg Prod.snd h))
    exact Set.image_injective.mpr hinj hext
  have hgmul (A B : RelationMonoid F) : g (A * B) = g A * g B := by
    apply Subtype.ext
    apply RelationMonoid.ext
    change P ○ extend (A * B) ○ P = (P ○ extend A ○ P) ○ (P ○ extend B ○ P)
    have hext : extend (A * B) = extend A ○ extend B := relation_extend_comp F _ _
    rw [hext]
    exact (relation_corner_comp P i _ _ hP (restrictedIdentity_comp_self F)
      hiPi (hsupp A) (hsupp B)).symm
  let ρ : hQ.Corner ≃* RelationMonoid F :=
    { toFun := f
      invFun := g
      left_inv := hleft
      right_inv := hright
      map_mul' := by
        intro Z W
        apply_fun g
        · rw [hgmul, hleft, hleft, hleft]
        · exact Function.LeftInverse.injective hright }
  exact ⟨hQ, ρ, fun _ => rfl⟩

end Complementation.Internal

end Complexity.FiniteAutomaton
