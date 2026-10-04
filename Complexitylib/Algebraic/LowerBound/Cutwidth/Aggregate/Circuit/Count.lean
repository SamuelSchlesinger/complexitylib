/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Circuit.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting the actual guesses and register states

Operation symbols and their fan-in do not enter these counts. Each special
occurrence contributes one guessed bit and one finite register.
-/

@[expose] public section

namespace Algebraic.Aggregate

variable {J : Type} {State : J → Type} {n g : ℕ}

/-- The ordinary gate count of the mixed program. -/
def ordinaryCount (p : Program (signature State) n g) : ℕ := g - specialCount p

theorem specialCount_le (p : Program (signature State) n g) : specialCount p ≤ g := by
  simpa [specialCount] using Fintype.card_subtype_le (fun i : Fin g =>
    (p.lines i).op.isSpecial = true)

theorem ordinaryCount_add_specialCount (p : Program (signature State) n g) :
    ordinaryCount p + specialCount p = g :=
  Nat.sub_add_cancel (specialCount_le p)

/-- The ordinary gate count also counts the binary-operation filter. -/
theorem card_filter_ordinary (p : Program (signature State) n g) :
    (Finset.univ.filter (fun gate : Fin g => (p.lines gate).op.isSpecial = false)).card =
      ordinaryCount p := by
  have h := Fintype.card_subtype_compl (fun gate : Fin g => (p.lines gate).op.isSpecial = true)
  simpa [Fintype.card_subtype, ordinaryCount, specialCount, SpecialGate] using h

theorem card_guess (p : Program (signature State) n g) :
    Fintype.card (Guess p) = 2 ^ specialCount p := by
  simp [Guess, specialCount]

theorem card_registers [∀ j, Fintype (State j)] (p : Program (signature State) n g) :
    Fintype.card (Registers p) = ∏ gate : SpecialGate p, Fintype.card (Register p gate) :=
  Fintype.card_pi

theorem card_registers_le [∀ j, Fintype (State j)] (p : Program (signature State) n g) :
    Fintype.card (Registers p) ≤
      2 ^ ∑ gate : SpecialGate p, Nat.clog 2 (Fintype.card (Register p gate)) := by
  rw [card_registers, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun gate _ => Nat.le_pow_clog (by decide) _)

/-- The component-cover key space has at most `2 ^ budget p` elements. -/
theorem card_componentKey_le [∀ j, Fintype (State j)] (p : Program (signature State) n g) :
    Fintype.card (Guess p × Registers p) ≤ 2 ^ budget p := by
  rw [Fintype.card_prod, card_guess, budget, Nat.pow_add]
  exact Nat.mul_le_mul_left _ (card_registers_le p)

/-- Uniform register bit bounds turn the actual-occurrence budget into a gate-count bound. -/
theorem budget_le_of_register_bits [∀ j, Fintype (State j)]
    (p : Program (signature State) n g) (bits : ℕ)
    (h : ∀ gate : SpecialGate p, Nat.clog 2 (Fintype.card (Register p gate)) ≤ bits) :
    budget p ≤ (bits + 1) * specialCount p := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun gate _ => h gate)
  simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] at hs
  dsimp [budget, specialCount]
  lia

/-- A uniform state-count bound supplies the corresponding register bit bound. -/
theorem budget_le_of_register_card [∀ j, Fintype (State j)]
    (p : Program (signature State) n g) (bits : ℕ)
    (h : ∀ gate : SpecialGate p, Fintype.card (Register p gate) ≤ 2 ^ bits) :
    budget p ≤ (bits + 1) * specialCount p :=
  budget_le_of_register_bits p bits (fun gate => Nat.clog_le_of_le_pow (h gate))

end Algebraic.Aggregate
