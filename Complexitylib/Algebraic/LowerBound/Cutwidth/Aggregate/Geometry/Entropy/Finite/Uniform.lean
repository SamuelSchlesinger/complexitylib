/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Finite
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!+# Uniform changes of coordinates for finite weight certificates

An injective selection of Boolean coordinates is uniformly distributed. Splitting
the cube into selected and unused coordinates transports local certificates to
the full input cube without any independence hypotheses about other messages.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

open scoped BigOperators Classical

/-- Reindex the uniform source of a weight certificate by an equivalence. -/
noncomputable def WeightBound.precompEquiv {X X' Y : Type*}
    [Fintype X] [Fintype X'] [Fintype Y] {key : X → Y} {cost : ℝ}
    (bound : WeightBound key cost) (e : X' ≃ X) : WeightBound (key ∘ e) cost where
  weight := bound.weight
  nonneg := bound.nonneg
  mass := bound.mass
  positive x := bound.positive (e x)
  log_bound := by
    change -(Fintype.card X' : ℝ) * cost ≤
      ∑ x, Real.log (bound.weight (key (e x)))
    rw [e.sum_comp (fun x => Real.log (bound.weight (key x))), Fintype.card_congr e]
    exact bound.log_bound

/-- Add unused independent coordinates to a weight certificate. -/
noncomputable def WeightBound.precompFst {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] {key : X → Y} {cost : ℝ}
    (bound : WeightBound key cost) : WeightBound (fun x : X × Z => key x.1) cost where
  weight := bound.weight
  nonneg := bound.nonneg
  mass := bound.mass
  positive x := bound.positive x.1
  log_bound := by
    have h := mul_le_mul_of_nonneg_right bound.log_bound
      (Nat.cast_nonneg (α := ℝ) (Fintype.card Z))
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum, Fintype.card_prod, Nat.cast_mul]
    convert h using 1 <;> ring

/-- Reindex the uniform source of a conditional certificate. -/
noncomputable def ConditionalWeightBound.precompEquiv {X X' Y Z : Type*}
    [Fintype X] [Fintype X'] [Fintype Y] {key : X → Y} {parent : X → Z} {cost : ℝ}
    (bound : ConditionalWeightBound key parent cost) (e : X' ≃ X) :
    ConditionalWeightBound (key ∘ e) (parent ∘ e) cost where
  weight := bound.weight
  nonneg := bound.nonneg
  mass := bound.mass
  positive x := bound.positive (e x)
  log_bound := by
    change -(Fintype.card X' : ℝ) * cost ≤
      ∑ x, Real.log (bound.weight (parent (e x)) (key (e x)))
    rw [e.sum_comp (fun x => Real.log (bound.weight (parent x) (key x))),
      Fintype.card_congr e]
    exact bound.log_bound

/-- Add unused independent coordinates to a conditional certificate. -/
noncomputable def ConditionalWeightBound.precompFst {X Y Z W : Type*}
    [Fintype X] [Fintype Y] [Fintype W] {key : X → Y} {parent : X → Z} {cost : ℝ}
    (bound : ConditionalWeightBound key parent cost) :
    ConditionalWeightBound (fun x : X × W => key x.1) (fun x => parent x.1) cost where
  weight := bound.weight
  nonneg := bound.nonneg
  mass := bound.mass
  positive x := bound.positive x.1
  log_bound := by
    have h := mul_le_mul_of_nonneg_right bound.log_bound
      (Nat.cast_nonneg (α := ℝ) (Fintype.card W))
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum, Fintype.card_prod, Nat.cast_mul]
    convert h using 1 <;> ring

/-- Split a Boolean cube into injectively selected coordinates and their complement. -/
noncomputable def coordinateSplit {I V : Type*} (e : I ↪ V) :
    (V → Bool) ≃ (I → Bool) × ({v // v ∉ Set.range e} → Bool) :=
  (Equiv.piEquivPiSubtypeProd (fun v => v ∈ Set.range e) (fun _ => Bool)).trans
    (Equiv.prodCongr (Equiv.arrowCongr (Equiv.ofInjective e e.injective).symm
      (Equiv.refl Bool)) (Equiv.refl _))

@[simp] theorem coordinateSplit_fst {I V : Type*} (e : I ↪ V) (x : V → Bool) :
    (coordinateSplit e x).1 = x ∘ e := rfl

/-- Lift a local weight certificate along an injective choice of Boolean coordinates. -/
noncomputable def WeightBound.precompCoordinates {I V Y : Type*}
    [Fintype I] [Fintype V] [Fintype Y] [DecidableEq I] [DecidableEq V]
    {key : (I → Bool) → Y} {cost : ℝ}
    (bound : WeightBound key cost) (e : I ↪ V) :
    WeightBound (fun x => key (x ∘ e)) cost :=
  bound.precompFst.precompEquiv (coordinateSplit e)

/-- Lift a local conditional certificate along an injective choice of coordinates. -/
noncomputable def ConditionalWeightBound.precompCoordinates {I V Y Z : Type*}
    [Fintype I] [Fintype V] [Fintype Y] [DecidableEq I] [DecidableEq V]
    {key : (I → Bool) → Y} {parent : (I → Bool) → Z} {cost : ℝ}
    (bound : ConditionalWeightBound key parent cost) (e : I ↪ V) :
    ConditionalWeightBound (fun x => key (x ∘ e)) (fun x => parent (x ∘ e)) cost :=
  bound.precompFst.precompEquiv (coordinateSplit e)

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy
