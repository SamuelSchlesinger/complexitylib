/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Nesting
public import Mathlib.Topology.Algebra.Semigroup
public import Mathlib.RingTheory.Idempotents

/-!
# Two-way complementation: corners

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/Corners.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace Complementation.Internal

open scoped SetRel

/-- A finite nonempty subsemigroup contains an idempotent. -/
theorem finite_subsemigroup_idempotent {A : Type*} [Semigroup A] [Finite A]
    (S : Set A) (hne : S.Nonempty) (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) :
    ∃ e ∈ S, IsIdempotentElem e := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  exact exists_idempotent_in_compact_subsemigroup (fun _ => continuous_of_discreteTopology)
    S hne (Set.toFinite S).isCompact hmul

/-- Every element of a finite monoid has an idempotent positive power. -/
theorem finite_idempotent_pow {A : Type*} [Monoid A] [Finite A] (a : A) :
    ∃ k : ℕ, 0 < k ∧ IsIdempotentElem (a ^ k) := by
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := finite_subsemigroup_idempotent
    (Set.range (fun k : ℕ => a ^ (k + 1))) ⟨a, 0, by simp⟩ (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact ⟨i + j + 1, by simp only [← pow_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]⟩)
  exact ⟨k + 1, Nat.succ_pos _, hk⟩

/-- A multiplicative map preserves positive powers without any unitality assumption. -/
theorem map_positive_pow {A B : Type*} [Monoid A] [Monoid B]
    (f : A →ₙ* B) (a : A) (k : ℕ) : f (a ^ (k + 1)) = f a ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, map_mul, ih, ← pow_succ]

/-- A nested chain with a common missing-set budget. -/
theorem exists_nested_chain {A : Type*} [Monoid A] [Finite A] {m k : ℕ}
    (ι : A →ₙ* Diagram m) (b0 : A) (hb0 : IsIdempotentElem b0) (g : ℕ → A)
    (J : Set (Bool × Set (Fin m)))
    (hg : ∀ j < k, ι (g j) ∈ (ι b0).corner ∧ (ι b0).missing (ι (g j)) ⊆ J) :
    ∃ b : ℕ → A, b 0 = b0 ∧
      (∀ j, IsIdempotentElem (b j)) ∧
      (∀ j, ∃ n : ℕ, b (j + 1) = (b j * g j * b j) ^ (n + 1)) ∧
      (∀ j, (ι (b (j + 1)), ι (b j)) ∈ Diagram.nesting m) ∧
      (∀ j ≤ k, (ι b0).missing (ι (b j)) ⊆ J) ∧
      ∑ j ∈ Finset.range k, ((ι (b j)).missing (ι (b (j + 1)))).ncard ≤ 2 * J.ncard := by
  classical
  choose power hpower using fun a : A => finite_idempotent_pow a
  let b : ℕ → A := Nat.rec b0 (fun j prev => (prev * g j * prev) ^ power (prev * g j * prev))
  have hzero : b 0 = b0 := rfl
  have hsucc (j : ℕ) : b (j + 1) = (b j * g j * b j) ^ power (b j * g j * b j) := rfl
  have hidemp (j : ℕ) : IsIdempotentElem (b j) := by
    cases j with
    | zero => exact hb0
    | succ j => exact (hpower _).2
  have hstep (j : ℕ) : ∃ n : ℕ, b (j + 1) = (b j * g j * b j) ^ (n + 1) := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (hpower (b j * g j * b j)).1.ne'
    exact ⟨n, by rw [hsucc, hn]⟩
  have hmapidemp (j : ℕ) : Diagram.comp (ι (b j)) (ι (b j)) = ι (b j) := by
    exact (map_mul ι (b j) (b j)).symm.trans (congrArg ι (hidemp j).eq)
  have hnest (j : ℕ) : (ι (b (j + 1)), ι (b j)) ∈ Diagram.nesting m := by
    obtain ⟨n, hn⟩ := hstep j
    have hcorner : ι (b j * g j * b j) ∈ (ι (b j)).corner := by
      constructor
      · change ι (b j) * ι (b j * g j * b j) = _
        rw [← map_mul, ← mul_assoc, ← mul_assoc, (hidemp j).eq]
      · change ι (b j * g j * b j) * ι (b j) = _
        rw [← map_mul, mul_assoc, (hidemp j).eq]
    have hpow := Diagram.corner_pow_succ hcorner n
    rw [← map_positive_pow, ← hn] at hpow
    exact ⟨hmapidemp (j + 1), hmapidemp j, hpow.2, hpow.1⟩
  have hbase (j : ℕ) : (ι (b j), ι b0) ∈ Diagram.nesting m := by
    induction j with
    | zero => exact Diagram.nesting_refl (hmapidemp 0)
    | succ j ih => exact Diagram.nesting_trans (hnest j) ih
  have hbudget : ∀ j ≤ k, (ι b0).missing (ι (b j)) ⊆ J := by
    intro j
    induction j with
    | zero => intro _; rw [hzero, Diagram.missing_self]; exact Set.empty_subset _
    | succ j ih =>
      intro hj
      obtain ⟨n, hn⟩ := hstep j
      have hb : ι (b j) ∈ (ι b0).corner := ⟨(hbase j).2.2.2, (hbase j).2.2.1⟩
      have hgj := (hg j (by omega)).1
      have hbg := Diagram.corner_comp hb hgj
      have hpow := Diagram.missing_pow_succ (ι b0) (ι (b j * g j * b j))
        (hmapidemp 0) (by rw [map_mul, map_mul]; exact Diagram.corner_comp hbg hb) n
      rw [← map_positive_pow, ← hn] at hpow
      apply hpow.trans
      have hfirst := Diagram.missing_comp (ι b0) (ι (b j)) (ι (g j)) (hmapidemp 0) hb hgj
      have hsecond := Diagram.missing_comp (ι b0) (ι (b j) * ι (g j)) (ι (b j))
        (hmapidemp 0) hbg hb
      rw [map_mul, map_mul]
      exact hsecond.trans
        (Set.union_subset (hfirst.trans (Set.union_subset (ih (by omega)) (hg j (by omega)).2))
          (ih (by omega)))
  exact ⟨b, hzero, hidemp, hstep, hnest, hbudget,
    Diagram.nested_chain_bound (fun j => ι (b j)) (fun j _ => hmapidemp j)
      (fun j _ => hnest j) J (by simpa only [hzero] using hbudget)⟩

/-- An idempotent has a lift minimal in the nesting order. -/
theorem minimal_idempotent_lift {A M : Type*} [Semigroup A] [Finite A] [Semigroup M]
    (θ : A →ₙ* M) (hθ : Function.Surjective θ) (q : M) (hq : IsIdempotentElem q) :
    ∃ d, IsIdempotentElem d ∧ θ d = q ∧
      ∀ e, IsIdempotentElem e → θ e = q → e * d = e → d * e = e → e = d := by
  obtain ⟨a, ha⟩ := hθ q
  obtain ⟨d0, hd0q, hd0⟩ := finite_subsemigroup_idempotent
    {x | θ x = q} ⟨a, ha⟩ (by
      intro x hx y hy
      change θ (x * y) = q
      rw [map_mul, hx, hy, hq.eq])
  obtain ⟨d, ⟨hd, hdq⟩, hminimal⟩ := Set.exists_min_image
    {d | IsIdempotentElem d ∧ θ d = q}
    (fun d => (Subsemigroup.corner d : Set A).ncard) (Set.toFinite _) ⟨d0, hd0, hd0q⟩
  refine ⟨d, hd, hdq, ?_⟩
  intro e he heq hed hde
  have hsub : (Subsemigroup.corner e : Set A) ⊆ Subsemigroup.corner d := by
    rintro x ⟨y, rfl⟩
    apply (Subsemigroup.mem_corner_iff hd).mpr
    exact ⟨by simp only [← mul_assoc, hde], by simp only [mul_assoc, hed]⟩
  have heqcorner := Set.eq_of_subset_of_ncard_le hsub (hminimal e ⟨he, heq⟩)
  have hdin : d ∈ Subsemigroup.corner e := by
    change d ∈ (Subsemigroup.corner e : Set A)
    rw [heqcorner]
    exact (Subsemigroup.mem_corner_iff hd).mpr ⟨hd, hd⟩
  exact hed.symm.trans ((Subsemigroup.mem_corner_iff he).mp hdin).1

/-- Mathlib's semigroup corner, equipped with its idempotent as identity. -/
instance cornerMonoid {A : Type*} [Semigroup A] {e : A} (he : IsIdempotentElem e) :
    Monoid he.Corner where
  __ : Semigroup he.Corner := inferInstanceAs (Semigroup (Subsemigroup.corner e))
  one := ⟨e, (Subsemigroup.mem_corner_iff he).mpr ⟨he, he⟩⟩
  one_mul x := Subtype.ext ((Subsemigroup.mem_corner_iff he).mp x.property).1
  mul_one x := Subtype.ext ((Subsemigroup.mem_corner_iff he).mp x.property).2

@[instance]
theorem finite_corner {A : Type*} [Semigroup A] [Finite A] {e : A}
    (he : IsIdempotentElem e) : Finite he.Corner :=
  inferInstanceAs (Finite (Subsemigroup.corner e))

/-- A multiplicative map restricts to a unital map between matching idempotent corners. -/
def cornerMap {A M : Type*} [Semigroup A] [Semigroup M] (θ : A →ₙ* M)
    {d : A} {q : M} (hd : IsIdempotentElem d) (hq : IsIdempotentElem q) (hθd : θ d = q) :
    hd.Corner →* hq.Corner where
  toFun x := ⟨θ x.val, (Subsemigroup.mem_corner_iff hq).mpr (by
    obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff hd).mp x.property
    exact ⟨by rw [← hθd, ← map_mul, hl], by rw [← hθd, ← map_mul, hr]⟩)⟩
  map_one' := Subtype.ext hθd
  map_mul' x y := Subtype.ext (map_mul θ x.val y.val)

theorem cornerMap_surjective {A M : Type*} [Semigroup A] [Semigroup M]
    (θ : A →ₙ* M) (hθ : Function.Surjective θ) {d : A} {q : M}
    (hd : IsIdempotentElem d) (hq : IsIdempotentElem q) (hθd : θ d = q) :
    Function.Surjective (cornerMap θ hd hq hθd) := by
  intro y
  obtain ⟨x, hx⟩ := hθ y.val
  refine ⟨⟨d * x * d, x, rfl⟩, ?_⟩
  apply Subtype.ext
  change θ (d * x * d) = y.val
  obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff hq).mp y.property
  rw [map_mul, map_mul, hθd, hx, hl, hr]

/-- At a minimal idempotent lift, every element with unit image is a unit. -/
theorem minimal_corner_reflects_units {A M : Type*} [Semigroup A] [Finite A] [Semigroup M]
    (θ : A →ₙ* M) {d : A} {q : M} (hd : IsIdempotentElem d) (hq : IsIdempotentElem q)
    (hθd : θ d = q)
    (hminimal : ∀ e, IsIdempotentElem e → θ e = q → e * d = e → d * e = e → e = d)
    (w : hd.Corner) (hw : IsUnit (cornerMap θ hd hq hθd w)) : IsUnit w := by
  obtain ⟨k, hk, hpow⟩ := finite_idempotent_pow w
  have hmapIdem : IsIdempotentElem (cornerMap θ hd hq hθd (w ^ k)) := by
    change _ * _ = _
    rw [← map_mul, hpow.eq]
  have hmapUnit : IsUnit (cornerMap θ hd hq hθd (w ^ k)) := by
    rw [map_pow]
    exact hw.pow k
  have hmapOne := (IsIdempotentElem.iff_eq_one_of_isUnit hmapUnit).mp hmapIdem
  have hθpow : θ (w ^ k).val = q := congrArg Subtype.val hmapOne
  obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff hd).mp (w ^ k).property
  have hwd : (w ^ k).val = d := hminimal _ (congrArg Subtype.val hpow.eq) hθpow hr hl
  exact IsUnit.of_pow_eq_one (Subtype.ext hwd) hk.ne'

/-- Taking a corner inside an absorbing corner gives the same smaller corner. -/
def cornerFlatten {M : Type*} [Semigroup M] {p : M} (hp : IsIdempotentElem p)
    (q : hp.Corner) (hq : IsIdempotentElem q) :
    hq.Corner ≃* (show IsIdempotentElem q.val from congrArg Subtype.val hq.eq).Corner := by
  let hQ : IsIdempotentElem q.val := congrArg Subtype.val hq.eq
  have hqprop := (Subsemigroup.mem_corner_iff hp).mp q.property
  refine
    { toFun := fun x => ⟨x.val.val, (Subsemigroup.mem_corner_iff hQ).mpr ?_⟩
      invFun := fun y => ⟨⟨y.val, (Subsemigroup.mem_corner_iff hp).mpr ?_⟩,
        (Subsemigroup.mem_corner_iff hq).mpr ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  · obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff hq).mp x.property
    exact ⟨congrArg Subtype.val hl, congrArg Subtype.val hr⟩
  · obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff hQ).mp y.property
    constructor
    · calc
        p * y.val = p * (q.val * y.val) := by rw [hl]
        _ = y.val := by rw [← mul_assoc, hqprop.1, hl]
    · calc
        y.val * p = (y.val * q.val) * p := by rw [hr]
        _ = y.val := by rw [mul_assoc, hqprop.2, hr]
  · obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff hQ).mp y.property
    exact ⟨Subtype.ext hl, Subtype.ext hr⟩

end Complementation.Internal

end Complexity.FiniteAutomaton
