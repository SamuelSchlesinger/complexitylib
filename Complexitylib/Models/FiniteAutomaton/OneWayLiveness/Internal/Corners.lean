/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Topology.Algebra.Semigroup
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Diagram

/-!
# One-way-liveness proof: Corners

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Automata/Corners.lean

Module and namespace names, imports, and formatting are adapted to complexitylib.
The machine definitions are shared through `Models.FiniteAutomaton.Defs`.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

/-- Positive powers in any finite monoid contain an idempotent. -/
lemma exists_idempotent_power {M : Type*} [Monoid M] [Finite M] (a : M) :
    ∃ n : ℕ, 0 < n ∧ a ^ n * a ^ n = a ^ n := by
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  let S : Set M := {x | ∃ n : ℕ, 0 < n ∧ a ^ n = x}
  have hS : S.Nonempty := ⟨a, 1, by omega, pow_one a⟩
  have hmul : ∀ᵉ (x ∈ S) (y ∈ S), x * y ∈ S := by
    rintro x ⟨n, hn, rfl⟩ y ⟨m, hm, rfl⟩
    exact ⟨n + m, by omega, pow_add a n m⟩
  obtain ⟨b, ⟨n, hn, rfl⟩, hb⟩ := exists_idempotent_in_compact_subsemigroup
    (fun _ => continuous_of_discreteTopology) S hS (Set.toFinite S).isCompact hmul
  exact ⟨n, hn, hb⟩

/-- The local monoid at an idempotent, with its genuine local identity. -/
@[ext] structure Corner {M : Type*} [Monoid M] (e : M) (he : e * e = e) where
  /-- The underlying element of the ambient monoid. -/
  val : M
  left : e * val = val
  right : val * e = val

namespace Corner
variable {M : Type*} [Monoid M] {e : M} {he : e * e = e}
instance : CoeOut (Corner e he) M := ⟨Corner.val⟩
instance : Monoid (Corner e he) where
  one := ⟨e, he, he⟩
  mul x y := ⟨x.val * y.val, by rw [← mul_assoc, x.left], by rw [mul_assoc, y.right]⟩
  mul_assoc _ _ _ := Corner.ext (mul_assoc _ _ _)
  one_mul x := Corner.ext x.left
  mul_one x := Corner.ext x.right
@[simp] lemma val_one : (1 : Corner e he).val = e := rfl
@[simp] lemma val_mul (x y : Corner e he) : (x * y).val = x.val * y.val := rfl
instance [Finite M] : Finite (Corner e he) :=
  Finite.of_injective Corner.val (fun _ _ h => Corner.ext h)

/-- Project an element into the corner by multiplication by the idempotent on both sides. -/
def sandwich (x : M) : Corner e he :=
  ⟨e * x * e, by rw [← mul_assoc, ← mul_assoc, he], by rw [mul_assoc, he]⟩

lemma val_pow_pos (x : Corner e he) {n : ℕ} (hn : 0 < n) : (x ^ n).val = x.val ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ x (k+1), pow_succ x.val (k+1), val_mul, ih (by omega)]
end Corner

lemma isUnit_of_injective_map_finite {M N : Type*} [Monoid M] [Monoid N] [Finite M]
    (f : M →* N) (hf : Function.Injective f) (a : M) (ha : IsUnit (f a)) : IsUnit a := by
  obtain ⟨n, hn, hi⟩ := exists_idempotent_power a
  have hp : f (a ^ n) = 1 := by
    have hu : IsUnit (f (a ^ n)) := by rw [map_pow]; exact ha.pow n
    apply (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp
    change f (a ^ n) * f (a ^ n) = f (a ^ n)
    rw [← map_mul, hi]
  have he : a ^ n = 1 := hf (by simpa using hp)
  apply (isUnit_pow_iff (Nat.ne_of_gt hn)).mp
  rw [he]
  exact isUnit_one

namespace Corner
variable {M N : Type*} [Monoid M] [Monoid N] {e : M} {he : e * e = e}
    {q : N} {hq : q * q = q}

/-- The monoid homomorphism induced on corners by an idempotent-preserving homomorphism. -/
def mapTo (f : M →* N) (hf : f e = q) : Corner e he →* Corner q hq where
  toFun x := ⟨f x.val, by rw [← hf, ← map_mul, x.left], by rw [← hf, ← map_mul, x.right]⟩
  map_one' := Corner.ext hf
  map_mul' x y := Corner.ext (map_mul f x.val y.val)

@[simp] lemma mapTo_val (f : M →* N) (hf : f e = q) (x : Corner e he) :
    (mapTo (he := he) (hq := hq) f hf x).val = f x.val := rfl

lemma mapTo_surjective (f : M →* N) (hf : f e = q) (hs : Function.Surjective f) :
    Function.Surjective (mapTo (he := he) (hq := hq) f hf) := by
  intro y
  obtain ⟨x, hx⟩ := hs y.val
  refine ⟨sandwich x, Corner.ext ?_⟩
  change f (e * x * e) = y.val
  rw [map_mul, map_mul, hf, hx, y.left, y.right]

lemma val_idempotent (x : Corner e he) (hx : x * x = x) : x.val * x.val = x.val :=
  congrArg Corner.val hx
end Corner

namespace Pairing
open scoped Classical
variable {A : Type*} [Fintype A]
    {M : Type*} [Monoid M] (ρ : M →* Pairing (A ⊕ A))
    (e : M) (he : e * e = e)

include he in
lemma image_idempotent : ρ e * ρ e = ρ e := by rw [← map_mul, he]

/-- Compress a pairing representation to the transversal ports of an idempotent. -/
noncomputable def reduceHom :
    Corner e he →* Pairing ({i // i ∈ lefts (ρ e)} ⊕ {i // i ∈ lefts (ρ e)}) where
  toFun x := reduce (ρ e) (ρ x.val)
  map_one' := reduce_self _ (image_idempotent ρ e he)
  map_mul' x y := by
    change reduce (ρ e) (ρ (x.val * y.val)) = _
    rw [map_mul]
    apply reduce_mul
    rw [← map_mul, x.right]

lemma reduceHom_injective (hρ : Function.Injective ρ) : Function.Injective (reduceHom ρ e he) := by
  intro x y hxy
  apply Corner.ext
  apply hρ
  apply reduce_injective (ρ e) (by rw [← map_mul, x.left]) (by rw [← map_mul, x.right])
    (by rw [← map_mul, y.left]) (by rw [← map_mul, y.right]) hxy

lemma reduceHom_rank (x : Corner e he) : rank (reduceHom ρ e he x) = rank (ρ x.val) :=
  rank_reduce _ _ (by rw [← map_mul, x.left]) (by rw [← map_mul, x.right])

lemma reduceHom_common_support (J : Finset A) :
    ∃ K : Finset {i // i ∈ lefts (ρ e)}, K.card ≤ J.card ∧
      ∀ a : M, support (ρ a) ⊆ J → support (reduceHom ρ e he (Corner.sandwich a)) ⊆ K := by
  obtain ⟨K, hK, hall⟩ := reduce_common_support (ρ e) (image_idempotent ρ e he) J
  refine ⟨K, hK, fun a ha => ?_⟩
  change support (reduce (ρ e) (ρ (e * a * e))) ⊆ K
  rw [map_mul, map_mul]
  exact hall (ρ a) ha

lemma rank_pow_le (a : Pairing (A ⊕ A)) {n : ℕ} (hn : 0 < n) : rank (a ^ n) ≤ rank a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ]
  exact rank_mul_le_right _ _

end Pairing

/-- A lift of an idempotent can always be made idempotent without changing its image. -/
lemma exists_idempotent_lift {M N : Type*} [Monoid M] [Monoid N] [Finite M]
    (f : M →* N) (hf : Function.Surjective f) (q : N) (hq : q * q = q) :
    ∃ e : M, e * e = e ∧ f e = q := by
  obtain ⟨a, ha⟩ := hf q
  obtain ⟨n, hn, hi⟩ := exists_idempotent_power a
  refine ⟨a ^ n, hi, ?_⟩
  rw [map_pow, ha]
  exact IsIdempotentElem.pow_eq hq (Nat.ne_of_gt hn)

lemma exists_min_rank_lift {M N A : Type*} [Monoid M] [Monoid N] [Finite M] [Fintype A]
    (ρ : M →* Pairing (A ⊕ A)) (f : M →* N) (hf : Function.Surjective f)
    (q : N) (hq : q * q = q) :
    ∃ e : M, e * e = e ∧ f e = q ∧
      ∀ z : M, z * z = z → f z = q → Pairing.rank (ρ e) ≤ Pairing.rank (ρ z) := by
  let S : Set M := {e | e * e = e ∧ f e = q}
  have hS : S.Nonempty := exists_idempotent_lift f hf q hq
  obtain ⟨e, he, hmin⟩ := Set.exists_min_image S (fun z => Pairing.rank (ρ z)) (Set.toFinite _) hS
  exact ⟨e, he.1, he.2, fun z hz hq => hmin z ⟨hz, hq⟩⟩

/-- Minimum rank over the local identity forces all local unit lifts to be units. -/
lemma min_rank_corner_isUnit {M N A : Type*} [Monoid M] [Monoid N] [Finite M] [Fintype A]
    (ρ : M →* Pairing (A ⊕ A)) (hρ : Function.Injective ρ)
    (f : M →* N) (e : M) (he : e * e = e) (q : N) (hq : q * q = q) (hf : f e = q)
    (hmin : ∀ z : M, z * z = z → f z = q → Pairing.rank (ρ e) ≤ Pairing.rank (ρ z))
    (y : Corner e he) (hy : IsUnit (Corner.mapTo (he := he) (hq := hq) f hf y)) : IsUnit y := by
  obtain ⟨n, hn, hi⟩ := exists_idempotent_power y
  have him : Corner.mapTo (he := he) (hq := hq) f hf (y ^ n) = 1 := by
    apply (IsIdempotentElem.iff_eq_one_of_isUnit ?_).mp
    · change _ * _ = _
      rw [← map_mul, hi]
    · rw [map_pow]
      exact hy.pow n
  have him' : f (y ^ n).val = q := congrArg Corner.val him
  have hlow := hmin (y ^ n).val (Corner.val_idempotent _ hi) him'
  have hbound : Pairing.rank (ρ (y ^ n).val) ≤ Pairing.rank (ρ y.val) := by
    rw [Corner.val_pow_pos y hn, map_pow]
    exact Pairing.rank_pow_le _ hn
  have hEq : Pairing.rank (Pairing.reduceHom ρ e he y) =
      Fintype.card {i // i ∈ Pairing.lefts (ρ e)} := by
    apply le_antisymm (Pairing.rank_le_card _)
    rw [Pairing.reduceHom_rank, Pairing.card_reduced]
    exact hlow.trans hbound
  exact isUnit_of_injective_map_finite (Pairing.reduceHom ρ e he)
    (Pairing.reduceHom_injective ρ e he hρ) y (Pairing.full_rank_isUnit _ hEq)

namespace Corner
variable {M : Type*} [Monoid M] {e f : M} {he : e * e = e} {hf : f * f = f}

/-- Transport a local monoid across a split pair. -/
def transfer (u v : M) (huv : u * v = e) (hvu : v * u = f)
    (hu : u * f = u) (hv : f * v = v) : Corner e he →* Corner f hf where
  toFun x := ⟨v * x.val * u, by rw [← mul_assoc, ← mul_assoc, hv], by rw [mul_assoc, hu]⟩
  map_one' := Corner.ext (by
    change v * e * u = f
    calc
      _ = (v * u) * (v * u) := by rw [← huv]; simp only [mul_assoc]
      _ = f := by rw [hvu, hf])
  map_mul' x y := Corner.ext (by
    change v * (x.val * y.val) * u = (v * x.val * u) * (v * y.val * u)
    calc
      _ = v * (x.val * e * y.val) * u := by rw [x.right]
      _ = v * (x.val * (u * v) * y.val) * u :=
        congrArg (fun t => v * (x.val * t * y.val) * u) huv.symm
      _ = _ := by simp only [mul_assoc])

/-- The corner equivalence induced by a split pair of elements. -/
def equivOfSplit (u v : M) (huv : u * v = e) (hvu : v * u = f)
    (hu : u * f = u) (hv : f * v = v) : Corner e he ≃* Corner f hf := by
  have heu : e * u = u := by rw [← huv, mul_assoc, hvu, hu]
  have hve : v * e = v := by rw [← huv, ← mul_assoc, hvu, hv]
  refine { transfer (he := he) (hf := hf) u v huv hvu hu hv with
    invFun := transfer (he := hf) (hf := he) v u hvu huv hve heu
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    apply Corner.ext
    change u * (v * x.val * u) * v = x.val
    calc
      _ = (u * v) * x.val * (u * v) := by simp only [mul_assoc]
      _ = x.val := by rw [huv, x.left, x.right]
  · intro x
    apply Corner.ext
    change v * (u * x.val * v) * u = x.val
    calc
      _ = (v * u) * x.val * (v * u) := by simp only [mul_assoc]
      _ = x.val := by rw [hvu, x.left, x.right]
end Corner

end Complexity.FiniteAutomaton
