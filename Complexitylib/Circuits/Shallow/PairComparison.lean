/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Shallow.Layer.Operations
public import Complexitylib.Circuits.Shallow.Weights
public import Mathlib.Tactic.LinearCombination

/-!
# Block comparison is symmetric after input negation

This is the recursive step in Section 4 of Lecomte and Ramakrishnan,
*Optimal Shallow Circuits for Majority*. The difference of two block weights
is, up to a constant, the weight of their concatenation after complementing
the second block. Signed input substitution costs no gates and no depth.
-/

public section

namespace Complexity.Shallow

open Finset

/-- Lift a symmetric synthesis bound to one modular comparison of two blocks. -/
theorem exists_pairComparison {n k d B M : ℕ}
    (ih : ∀ m ≤ M, ∀ a : ℕ → Bool,
      ∃ f : Layer m (d + 2), Layer.size f ≤ B ∧
        ∀ x, Layer.eval .and f x = a (weight x))
    (hm : 2 * (n / k + 1) ≤ M) (i j si sj : ZMod k) :
    ∃ f : Layer n (d + 2), Layer.size f ≤ B ∧
      ∀ x, Layer.eval .and f x =
        decide ((blockWeight residueBlock x i : ZMod k) + si ≠
          (blockWeight residueBlock x j : ZMod k) + sj) := by
  classical
  let I := {u : Fin n // residueBlock u = i}
  let J := {u : Fin n // residueBlock u = j}
  let V := I ⊕ J
  let m := Fintype.card V
  let e : Fin m ≃ V := (Fintype.equivFin V).symm
  let select : Fin m → Fin n × Bool := fun u =>
    Sum.elim (fun v : I => (v.1, false)) (fun v : J => (v.1, true)) (e u)
  let a : ℕ → Bool := fun w =>
    decide ((w : ZMod k) + si ≠ (Fintype.card J : ZMod k) + sj)
  have hm' : m ≤ M := by
    have hi := card_residueBlock_le n k i
    have hj := card_residueBlock_le n k j
    change Fintype.card (I ⊕ J) ≤ M
    rw [Fintype.card_sum]
    dsimp [I, J]
    omega
  obtain ⟨f, hs, he⟩ := ih m hm' a
  refine ⟨Layer.mapInputs select f, ?_, fun x => ?_⟩
  · rwa [Layer.size_mapInputs]
  rw [Layer.eval_mapInputs, he]
  let z : Fin m → Bool := fun u => (select u).2.xor (x (select u).1)
  have hz : weight z = weight (Sum.elim (fun u : I => x u.1)
      (fun u : J => !(x u.1))) := by
    apply Fintype.sum_equiv e
    intro u
    dsimp [z, select]
    cases e u <;> simp
  have hw := weight_pair_not_add (fun u : I => x u.1) (fun u : J => x u.1)
  rw [← hz] at hw
  change weight z + blockWeight residueBlock x j =
    blockWeight residueBlock x i + Fintype.card J at hw
  have hcast : (weight z : ZMod k) + (blockWeight residueBlock x j : ZMod k) =
      (blockWeight residueBlock x i : ZMod k) + (Fintype.card J : ZMod k) := by
    simpa only [Nat.cast_add] using congrArg (fun r : ℕ => (r : ZMod k)) hw
  change decide ((weight z : ZMod k) + si ≠ (Fintype.card J : ZMod k) + sj) = _
  congr 1
  have heq : ((weight z : ZMod k) + si = (Fintype.card J : ZMod k) + sj) ↔
      (blockWeight residueBlock x i : ZMod k) + si =
        (blockWeight residueBlock x j : ZMod k) + sj := by
    constructor <;> intro h
    · linear_combination h - hcast
    · linear_combination hcast + h
  exact propext (not_congr heq)

end Complexity.Shallow
