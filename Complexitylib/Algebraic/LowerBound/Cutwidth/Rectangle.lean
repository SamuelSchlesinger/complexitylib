/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Semantics
public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Powerset

/-!
# Rectangle-free Boolean functions

A *one-rectangle* of `f : {0,1}ⁿ → {0,1}` is a product `P × Q`, for a split
of the coordinates into `U` and its complement, on which `f` is identically
`1`. The function is `K`-rectangle-free when every one-rectangle, under every
split, has a side with fewer than `K` elements. The lower bound applies to
families that are `n ^ c`-rectangle-free with at least `2 ^ (n - 2)`
accepting inputs; this development takes that property as a hypothesis.

The support lemma `two_pow_lt_or_card_accepting_lt` records the only use of
rectangle-freeness outside the cut-counting argument: a rectangle-free function
with many accepting inputs cannot ignore many coordinates.
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth

open scoped Classical

variable {n : Nat}

/-- The inputs accepted by a Boolean function. -/
noncomputable def accepting (f : Cslib.BooleanFunction n) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun x => f x = true

theorem mem_accepting {f : Cslib.BooleanFunction n} {x : Fin n → Bool} :
    x ∈ accepting f ↔ f x = true := by
  simp [accepting]

/-- Combine an assignment to the coordinates in `U` with one to its complement. -/
def glue (U : Finset (Fin n)) (p : U → Bool) (q : ↥Uᶜ → Bool) : Fin n → Bool :=
  fun i => if h : i ∈ U then p ⟨i, h⟩ else q ⟨i, Finset.mem_compl.mpr h⟩

@[simp] theorem glue_apply_mem (U : Finset (Fin n)) (p : U → Bool) (q : ↥Uᶜ → Bool)
    (i : U) : glue U p q i = p i := by
  simp [glue, i.2]

@[simp] theorem glue_apply_compl (U : Finset (Fin n)) (p : U → Bool) (q : ↥Uᶜ → Bool)
    (i : ↥Uᶜ) : glue U p q i = q i := by
  have : ¬ (i.1 ∈ U) := Finset.mem_compl.mp i.2
  simp [glue, this]

/-- Restricting an input to `U` and to its complement, then gluing, recovers it. -/
theorem glue_restrict (U : Finset (Fin n)) (x : Fin n → Bool) :
    glue U (fun i => x i) (fun i => x i) = x := by
  funext i
  by_cases h : i ∈ U <;> simp [glue, h]

/-- Every one-rectangle of `f`, under every split of the coordinates, has a side
with fewer than `K` elements. -/
def RectangleFree (f : Cslib.BooleanFunction n) (K : Nat) : Prop :=
  ∀ (U : Finset (Fin n)) (P : Finset (U → Bool)) (Q : Finset (↥Uᶜ → Bool)),
    (∀ p ∈ P, ∀ q ∈ Q, f (glue U p q) = true) → P.card < K ∨ Q.card < K

/-- A nonzero rectangle-free function has threshold at least two. -/
theorem RectangleFree.one_lt {f : Cslib.BooleanFunction n} {K : Nat}
    (free : RectangleFree f K) {x : Fin n → Bool} (accepted : f x = true) : 1 < K := by
  have h := free ∅ {fun i : ↥(∅ : Finset (Fin n)) => x i.1}
    {fun i : ↥(∅ : Finset (Fin n))ᶜ => x i.1} (by
    intro p hp q hq
    rw [Finset.mem_singleton] at hp hq
    subst hp; subst hq
    simpa [glue_restrict] using accepted)
  simpa using h

/-- A rectangle-free function that ignores the coordinates in `U` either has
`2 ^ |U| < K`, or fewer than `2 ^ |U| * K` accepting inputs. -/
theorem two_pow_lt_or_card_accepting_lt
    {f : Cslib.BooleanFunction n} {K : Nat} (free : RectangleFree f K)
    {R U : Finset (Fin n)} (depends : DependsOnlyOn f R) (disjoint : Disjoint U R) :
    2 ^ U.card < K ∨ (accepting f).card < 2 ^ U.card * K := by
  -- Every assignment to `U` can be replaced by the all-zero one.
  have agree (p : U → Bool) (q : ↥Uᶜ → Bool) :
      f (glue U p q) = f (glue U (fun _ => false) q) := by
    apply depends
    intro k hk
    have : k ∉ U := Finset.disjoint_right.mp disjoint hk
    simp [glue, this]
  let Q : Finset (↥Uᶜ → Bool) :=
    Finset.univ.filter fun q => f (glue U (fun _ => false) q) = true
  have rectangle := free U Finset.univ Q (by
    intro p _ q hq
    rw [agree]
    exact (Finset.mem_filter.mp hq).2)
  have cardP : (Finset.univ : Finset (U → Bool)).card = 2 ^ U.card := by
    simp [Finset.card_univ, Fintype.card_bool]
  rcases rectangle with small | small
  · left
    rwa [cardP] at small
  · right
    have subset : accepting f ⊆
        (Finset.univ ×ˢ Q).image fun pq : (U → Bool) × (↥Uᶜ → Bool) => glue U pq.1 pq.2 := by
      intro x hx
      rw [Finset.mem_image]
      refine ⟨(fun i => x i, fun i => x i), ?_, glue_restrict U x⟩
      rw [Finset.mem_product]
      refine ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rw [← agree (fun i => x i), glue_restrict]
      exact mem_accepting.mp hx
    calc (accepting f).card
        ≤ ((Finset.univ ×ˢ Q).image fun pq : (U → Bool) × (↥Uᶜ → Bool) =>
            glue U pq.1 pq.2).card := Finset.card_le_card subset
      _ ≤ (Finset.univ ×ˢ Q).card := Finset.card_image_le
      _ = 2 ^ U.card * Q.card := by rw [Finset.card_product, cardP]
      _ < 2 ^ U.card * K := Nat.mul_lt_mul_of_pos_left small (Nat.two_pow_pos _)

end Cutwidth
end Algebraic
