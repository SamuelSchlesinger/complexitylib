/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Capacity.Circuit.Defs

/-!
# Counting one-way summary states

Binary occurrences cost one bit; special occurrences cost the logarithm of their
actual register cardinality. The count has no guessed-output-bit factor.
-/

@[expose] public section

namespace Algebraic.Aggregate.Capacity

variable {J : Type} {State : J → Type} {n g : ℕ}

/-- The register capacity of a single operation. -/
def registerBits [∀ j, Fintype (State j)] (op : Op State) : ℕ :=
  if op.isSpecial then Nat.clog 2 (Fintype.card op.Register) else 1

/-- The finite summary register fits in its charged number of bits. -/
theorem card_summaryRegister_le [∀ j, Fintype (State j)] (op : Op State) :
    Fintype.card (SummaryRegister op) ≤ 2 ^ registerBits op := by
  cases op with
  | binary f =>
      exact (Fintype.card_congr (Equiv.refl Bool)).trans_le (by simp [registerBits, Op.isSpecial])
  | special kind arity contribution readout =>
      simpa only [registerBits, Op.isSpecial, ↓reduceIte] using
        Nat.le_pow_clog (by decide : 1 < 2) (Fintype.card (State kind))

/-- The gatewise bit sum is the ordinary count plus the actual special-register costs. -/
theorem sum_registerBits_eq_capacity [∀ j, Fintype (State j)]
    (p : Program (signature State) n g) :
    (∑ gate, registerBits (p.lines gate).op) = capacity p := by
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun gate : Fin g => (p.lines gate).op.isSpecial = true)]
  have hs : (∑ gate : SpecialGate p, registerBits (p.lines gate).op) =
      ∑ gate : SpecialGate p, Nat.clog 2 (Fintype.card (Register p gate)) := by
    apply Finset.sum_congr rfl
    intro gate _
    simp [registerBits, gate.property, Register]
  have hb : (∑ gate : {gate : Fin g // ¬ (p.lines gate).op.isSpecial = true},
      registerBits (p.lines gate).op) = ordinaryCount p := by
    calc
      _ = ∑ _ : {gate : Fin g // ¬ (p.lines gate).op.isSpecial = true}, 1 := by
        apply Finset.sum_congr rfl
        intro gate _
        simp [registerBits, gate.property]
      _ = ordinaryCount p := by
        simpa [ordinaryCount, SpecialGate, specialCount] using
          Fintype.card_subtype_compl (fun gate : Fin g => (p.lines gate).op.isSpecial = true)
  rw [hs, hb]
  exact Nat.add_comm _ _

/-- The one-way key space has at most `2 ^ capacity p` elements. -/
theorem card_key_le [∀ j, Fintype (State j)] (p : Program (signature State) n g) :
    Fintype.card (Key p) ≤ 2 ^ capacity p := by
  rw [Fintype.card_pi, ← sum_registerBits_eq_capacity, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun gate _ => card_summaryRegister_le (p.lines gate).op)

/-- A uniform bound on every register charges at most `bits` per gate. -/
theorem capacity_le_of_register_bits [∀ j, Fintype (State j)]
    (p : Program (signature State) n g) (bits : ℕ) (hb : 1 ≤ bits)
    (h : ∀ gate : SpecialGate p, Nat.clog 2 (Fintype.card (Register p gate)) ≤ bits) :
    capacity p ≤ bits * g := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun gate _ => h gate)
  simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] at hs
  have hc := ordinaryCount_add_specialCount p
  change _ ≤ specialCount p * bits at hs
  have ho : ordinaryCount p ≤ bits * ordinaryCount p := by
    simpa using Nat.mul_le_mul_right (ordinaryCount p) hb
  calc
    capacity p ≤ ordinaryCount p + specialCount p * bits := Nat.add_le_add_left hs _
    _ ≤ bits * ordinaryCount p + bits * specialCount p := by
      simpa only [Nat.mul_comm (specialCount p) bits] using
        Nat.add_le_add_right ho (specialCount p * bits)
    _ = bits * g := by rw [← Nat.mul_add, hc]

/-- Uniform state cardinalities give a uniform gatewise capacity bound. -/
theorem capacity_le_of_register_card [∀ j, Fintype (State j)]
    (p : Program (signature State) n g) (bits : ℕ) (hb : 1 ≤ bits)
    (h : ∀ gate : SpecialGate p, Fintype.card (Register p gate) ≤ 2 ^ bits) :
    capacity p ≤ bits * g :=
  capacity_le_of_register_bits p bits hb (fun gate => Nat.clog_le_of_le_pow (h gate))

end Algebraic.Aggregate.Capacity
