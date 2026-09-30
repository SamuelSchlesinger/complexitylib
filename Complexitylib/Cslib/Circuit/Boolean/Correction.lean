/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Cslib.Circuit.Boolean.Correction.Defs
public import Complexitylib.Cslib.Circuit.Boolean.Correction.Internal

/-!
# Relative circuit complexity under sparse corrections

A correction consists of a support indicator and a partial vector of error
labels. Its cost is their joint synthesis cost plus five gates per active
output: one mask and a four-gate XOR. Output wires and fan-out are free.

These are finite composition theorems. Sharp estimates for sparse indicators
and partial scalar functions are separate synthesis results, treated by
A. V. Chashkin, *On computing partial Boolean functions* (in Russian),
Mathematical Problems of Cybernetics 22 (2024), pp. 152–222,
https://doi.org/10.20948/mvk-2024-152.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Correction

variable {n m : ℕ}

/-- A scalar correction is its support indicator; applying it costs four XOR gates. -/
theorem complexity_dist_le_indicator (f g : (Fin n → Bool) → Fin 1 → Bool) :
    Nat.dist (complexity interpretation f) (complexity interpretation g) ≤
      complexity interpretation (indicator (errorSupport f g)) + 4 := by
  have hf : (fun x (_ : Fin 1) => f x 0) = f := by
    ext x j; exact congrArg (f x) (Subsingleton.elim _ _)
  have hg : (fun x (_ : Fin 1) => g x 0) = g := by
    ext x j; exact congrArg (g x) (Subsingleton.elim _ _)
  have support : {x | f x 0 ≠ g x 0} = errorSupport f g := by
    ext x
    change (f x 0 ≠ g x 0) ↔ f x ≠ g x
    apply not_congr
    constructor
    · intro equal
      funext j
      simpa only [Fin.eq_zero j] using equal
    · intro equal
      exact congrFun equal 0
  have forward := Internal.scalar_complexity_le (fun x => f x 0) (fun x => g x 0)
  have backward := Internal.scalar_complexity_le (fun x => g x 0) (fun x => f x 0)
  rw [hf, hg, support] at forward
  have reverse : {x | g x 0 ≠ f x 0} = errorSupport f g := by
    rw [← support]
    ext; exact ne_comm
  rw [hf, hg, reverse] at backward
  unfold Nat.dist
  omega

/-- A support and a partial vector correction bound the cost of correcting `g` into `f`. -/
theorem complexityGiven_le_of_cover
    (f g : (Fin n → Bool) → Fin m → Bool) (s : Set (Fin n → Bool))
    (outputs : Finset (Fin m))
    (outside : ∀ x ∉ s, f x = g x)
    (unchanged : ∀ j ∉ outputs, ∀ x, f x j = g x j) :
    complexityGiven interpretation f g ≤ complexity interpretation (indicator s) +
      complexityOn interpretation s (errorVector f g outputs) + 5 * outputs.card :=
  Internal.complexityGiven_bound f g s outputs outside unchanged

/-- The canonical error support and active output set give a relative correction bound. -/
theorem complexityGiven_le (f g : (Fin n → Bool) → Fin m → Bool) :
    complexityGiven interpretation f g ≤
      complexity interpretation (indicator (errorSupport f g)) +
        complexityOn interpretation (errorSupport f g) (errorVector f g (activeOutputs f g)) +
          5 * (activeOutputs f g).card := by
  apply complexityGiven_le_of_cover
  · intro x hx
    simpa [errorSupport] using hx
  · classical
    intro j hj x
    exact (by simpa [activeOutputs] using hj : ∀ x, f x j = g x j) x

/-- The error vector is unchanged when the two functions are exchanged. -/
theorem errorVector_comm (f g : (Fin n → Bool) → Fin m → Bool)
    (outputs : Finset (Fin m)) : errorVector f g outputs = errorVector g f outputs := by
  funext x j
  exact Bool.xor_comm _ _

/-- Correcting either direction bounds the absolute change in minimum circuit size. -/
theorem complexity_dist_le_of_cover
    (f g : (Fin n → Bool) → Fin m → Bool) (s : Set (Fin n → Bool))
    (outputs : Finset (Fin m))
    (outside : ∀ x ∉ s, f x = g x)
    (unchanged : ∀ j ∉ outputs, ∀ x, f x j = g x j) :
    Nat.dist (complexity interpretation f) (complexity interpretation g) ≤
      complexity interpretation (indicator s) +
        complexityOn interpretation s (errorVector f g outputs) + 5 * outputs.card := by
  have forward := (complexity_le_add_complexityGiven (I := interpretation) f g).trans
    (Nat.add_le_add_left (complexityGiven_le_of_cover f g s outputs outside unchanged) _)
  have backward := (complexity_le_add_complexityGiven (I := interpretation) g f).trans
    (Nat.add_le_add_left (complexityGiven_le_of_cover g f s outputs
      (fun x hx => (outside x hx).symm) (fun j hj x => (unchanged j hj x).symm)) _)
  rw [← errorVector_comm f g outputs] at backward
  unfold Nat.dist
  omega

/-- Sparse vector correction with the exact support and the exact active output set. -/
theorem complexity_dist_le (f g : (Fin n → Bool) → Fin m → Bool) :
    Nat.dist (complexity interpretation f) (complexity interpretation g) ≤
      complexity interpretation (indicator (errorSupport f g)) +
        complexityOn interpretation (errorSupport f g) (errorVector f g (activeOutputs f g)) +
          5 * (activeOutputs f g).card := by
  apply complexity_dist_le_of_cover
  · intro x hx
    simpa [errorSupport] using hx
  · classical
    intro j hj x
    exact (by simpa [activeOutputs] using hj : ∀ x, f x j = g x j) x

/-- Scalar synthesis on the support can supply each label separately. -/
theorem complexity_dist_le_sum_of_cover
    (f g : (Fin n → Bool) → Fin m → Bool) (s : Set (Fin n → Bool))
    (outputs : Finset (Fin m))
    (outside : ∀ x ∉ s, f x = g x)
    (unchanged : ∀ j ∉ outputs, ∀ x, f x j = g x j) :
    Nat.dist (complexity interpretation f) (complexity interpretation g) ≤
      complexity interpretation (indicator s) +
        (∑ j : Fin outputs.card, complexityOn interpretation s
          (fun x (_ : Fin 1) => errorVector f g outputs x j)) + 5 * outputs.card :=
  (complexity_dist_le_of_cover f g s outputs outside unchanged).trans
    (Nat.add_le_add_right (Nat.add_le_add_left
      (complexityOn_le_sum (I := interpretation) (s := s) (errorVector f g outputs)) _) _)

end Cslib.Circuits.Boolean.Correction
