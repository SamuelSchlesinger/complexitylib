/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Amplification

/-!
# Two-way complementation: retained

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/Retained.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace Complementation.Internal

open scoped SetRel

/-- Select the two 64-point families and a distinct hub. -/
theorem exists_hub_families {H : Type*} [Finite H] (hh : 129 ≤ Nat.card H) :
    ∃ u v : Fin 64 ↪ H, ∃ z : H,
      (∀ i j, u i ≠ v j) ∧ (∀ i, u i ≠ z) ∧ (∀ j, v j ≠ z) := by
  classical
  let := Fintype.ofFinite H
  obtain ⟨e⟩ : Nonempty (Fin 129 ↪ H) := Function.Embedding.nonempty_of_card_le (by simpa using hh)
  let u : Fin 64 ↪ H :=
    ⟨fun i => e ⟨i.val, by omega⟩,
      fun a b h => Fin.ext (congrArg (fun k : Fin 129 => k.val) (e.injective h))⟩
  let v : Fin 64 ↪ H := ⟨fun i => e ⟨64 + i.val, by omega⟩, by
    intro a b h
    have he := congrArg (fun k : Fin 129 => k.val) (e.injective h)
    apply Fin.ext
    change 64 + a.val = 64 + b.val at he
    omega⟩
  refine ⟨u, v, e 128, ?_, ?_, ?_⟩
  · intro i j h
    have he := congrArg (fun k : Fin 129 => k.val) (e.injective h)
    change i.val = 64 + j.val at he
    omega
  · intro i h
    have he := congrArg (fun k : Fin 129 => k.val) (e.injective h)
    change i.val = 128 at he
    omega
  · intro j h
    have he := congrArg (fun k : Fin 129 => k.val) (e.injective h)
    change 64 + j.val = 128 at he
    omega

/-- Retaining a new pair and all external points removes exactly 127 points. -/
theorem retained_pair_set {H : Type*} [Finite H] (U V : Set H)
    (hU : U.ncard = 64) (hV : V.ncard = 64) (hUV : Disjoint U V)
    (z x y : H) (hzU : z ∉ U) (hzV : z ∉ V) (hx : x ∈ U) (hy : y ∈ V) :
    ∃ F : Set H, Nat.card F = Nat.card H - 127 ∧ x ∈ F ∧ y ∈ F ∧ z ∉ F ∧
      (∀ a ∈ U, a ∈ F → a = x) ∧ (∀ b ∈ V, b ∈ F → b = y) := by
  classical
  let S := insert z (U ∪ V)
  let F := ({x, y} : Set H) ∪ Sᶜ
  have hxy : x ≠ y := fun h => Set.disjoint_left.mp hUV (h ▸ hx) hy
  have hS : S.ncard = 129 := by
    rw [Set.ncard_insert_of_notMem (by simpa using And.intro hzU hzV),
      Set.ncard_union_eq hUV, hU, hV]
  have hpair : ({x, y} : Set H).ncard = 2 := by simp [hxy]
  have hpS : ({x, y} : Set H) ⊆ S := by
    rintro a (rfl | rfl) <;> simp [S, hx, hy]
  have hdisj : Disjoint ({x, y} : Set H) Sᶜ := Set.disjoint_left.mpr (fun _ ha hn => hn (hpS ha))
  have hF : F.ncard = Nat.card H - 127 := by
    rw [Set.ncard_union_eq hdisj, hpair, Set.ncard_compl, hS]
    have hh : 129 ≤ Nat.card H := by simpa only [hS] using Set.ncard_le_card S
    omega
  refine ⟨F, by simpa only [Nat.card_coe_set_eq] using hF, Or.inl (Or.inl rfl),
    Or.inl (Or.inr rfl), ?_, ?_, ?_⟩
  · rintro (h | h)
    · rcases h with rfl | rfl
      · exact hzU hx
      · exact hzV hy
    · exact h (by simp [S])
  · intro a ha hF
    rcases hF with (rfl | rfl) | hout
    · rfl
    · exact (Set.disjoint_left.mp hUV ha hy).elim
    · exact (hout (by simp [S, ha])).elim
  · intro b hb hF
    rcases hF with (rfl | rfl) | hout
    · exact (Set.disjoint_left.mp hUV hx hb).elim
    · rfl
    · exact (hout (by simp [S, hb])).elim

/-- Identity sandwiches restrict exactly the two endpoints. -/
theorem mem_restricted_sandwich {H : Type*} (F : Set H) (R : SetRel H H) (a b : H) :
    (a, b) ∈ restrictedIdentity F ○ R ○ restrictedIdentity F ↔
      a ∈ F ∧ b ∈ F ∧ (a, b) ∈ R := by
  simp only [SetRel.comp, restrictedIdentity, Set.mem_ofPred_eq]
  aesop

/-- Before its turn, the selected pair is absent from the retained restriction. -/
theorem retained_relation_identity {H : Type*} (U V F : Set H) (z x y : H)
    (hz : z ∉ F) (hx : ∀ a ∈ U, a ∈ F → a = x) (hy : ∀ b ∈ V, b ∈ F → b = y)
    (E : SetRel H H) (hE : E ⊆ U ×ˢ V) (hnew : (x, y) ∉ E) :
    restrictedIdentity F ○ (restrictedIdentity {a | a ≠ z} ∪ E) ○ restrictedIdentity F =
      restrictedIdentity F := by
  ext ⟨a, b⟩
  rw [mem_restricted_sandwich]
  constructor
  · rintro ⟨ha, hb, hid | hedge⟩
    · exact ⟨hid.1, ha⟩
    · exact (hnew (by simpa only [hx a (hE hedge).1 ha, hy b (hE hedge).2 hb] using hedge)).elim
  · rintro ⟨rfl, ha⟩
    exact ⟨ha, ha, Or.inl ⟨rfl, fun h => hz (h ▸ ha)⟩⟩

/-- At its turn, restriction adds precisely the selected pair to the retained identity. -/
theorem retained_relation_pair {H : Type*} (P : SetRel H H) (F : Set H)
    (hP : restrictedIdentity F ○ P ○ restrictedIdentity F = restrictedIdentity F)
    (x y : H) (hx : x ∈ F) (hy : y ∈ F) :
    restrictedIdentity F ○ (P ∪ {(x, y)}) ○ restrictedIdentity F =
      restrictedIdentity F ∪ {(x, y)} := by
  rw [relComp_union, union_relComp, hP]
  congr 1
  ext ⟨a, b⟩
  rw [mem_restricted_sandwich]
  simp only [Set.mem_singleton_iff, Prod.mk.injEq]
  aesop

/-- The target doubles whenever the induction removes 127 points. -/
theorem lossBound_step {h : ℕ} (hh : 129 ≤ h) : lossBound h = 2 * lossBound (h - 127) := by
  have hexp : (h - 2) / 127 = (h - 127 - 2) / 127 + 1 := by omega
  simp only [lossBound, hexp, pow_succ, Nat.mul_comm]

/-- The numerical conclusion of summing the 4096 inductive lower bounds. -/
theorem amplification_arithmetic {h c : ℕ} (hh : 129 ≤ h) (δ : Fin 4096 → ℕ)
    (htotal : ∑ j, δ j ≤ 1024 * c)
    (hstep : ∀ j, lossBound (h - 127) ≤ 2 * δ j) : lossBound h ≤ c := by
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4096))) => hstep j)
  have hbound : 4096 * lossBound (h - 127) ≤ 2 * ∑ j, δ j := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      ← Finset.mul_sum] using hsum
  rw [lossBound_step hh]
  omega

/-- The base case detects the off-diagonal pair using rectangle coverage and order reversal. -/
theorem single_edge_base {A H : Type*} [Monoid A] {m : ℕ}
    (ι : A →ₙ* Diagram m) (φ : A →* RelationMonoid H)
    (hreverse : ∀ a b, (ι a, ι b) ∈ Diagram.inclusion m → (φ b).toRel ⊆ (φ a).toRel)
    (a : A) (x y : H) (hxy : x ≠ y)
    (himage : (φ a).toRel = SetRel.id ∪ {(x, y)}) (hh : Nat.card H ≤ 128) :
    lossBound (Nat.card H) ≤ ((ι 1).missing (ι a)).ncard := by
  have hsmall : lossBound (Nat.card H) = 1 := by
    have he : (Nat.card H - 2) / 127 = 0 := by omega
    simp [lossBound, he]
  rw [hsmall]
  by_contra h
  have hempty : (ι 1).missing (ι a) = ∅ := (Set.ncard_eq_zero).mp (by omega)
  have hinclusion := Diagram.inclusion_of_missing_empty (ι 1) (ι a)
    (map_identity_corner ι 1).1 (map_identity_corner ι a) hempty
  have hedge : (x, y) ∈ (φ a).toRel := by rw [himage]; exact Or.inr rfl
  have hid := hreverse 1 a hinclusion hedge
  rw [map_one, RelationMonoid.toRel_one] at hid
  exact hxy hid

/-- Every positive power of a sandwich is absorbed by its idempotent outer factor. -/
theorem sandwich_power_absorption {A : Type*} [Monoid A] (b a : A)
    (hb : IsIdempotentElem b) (k : ℕ) :
    b * (b * a * b) ^ (k + 1) = (b * a * b) ^ (k + 1) ∧
      (b * a * b) ^ (k + 1) * b = (b * a * b) ^ (k + 1) := by
  have hl : b * (b * a * b) = b * a * b := by rw [← mul_assoc, ← mul_assoc, hb.eq]
  have hr : b * a * b * b = b * a * b := by rw [mul_assoc, hb.eq]
  induction k with
  | zero => simpa using And.intro hl hr
  | succ k ih =>
    constructor
    · rw [pow_succ, ← mul_assoc, ih.1]
    · rw [pow_succ, mul_assoc, hr]

end Complementation.Internal

end Complexity.FiniteAutomaton
