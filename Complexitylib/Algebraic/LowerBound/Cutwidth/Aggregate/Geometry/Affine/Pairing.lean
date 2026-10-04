/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Count

/-!
# Affine restrictions with paired gate charges

A nonconstant internal affine predecessor can be fixed to a conjunction's controlling
value. This makes both the predecessor and the new gate permanently constant. Only
multiple-primary conjunctions can need a restriction without an internal partner.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

open scoped Classical

variable {n g : Nat}

/-- Combine affine old outputs with the affine output of the appended line. -/
private theorem affineOn_append (p : Program signature n g) (line : Line signature n g)
    (S : AffineFlat n) (old : ∀ i, AffineOn S (p.gateFunction interpretation i))
    (new : AffineOn S (lineFunction p line)) :
    ∀ i, AffineOn S ((p.gate line).gateFunction interpretation i) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Program.gateFunction_gate_last]
    exact new
  · simpa only [Program.gateFunction_gate_castSucc] using old j

/-- One exact halving increments the recorded affine codimension. -/
private theorem card_half_step {S T : AffineFlat n} {d : Nat}
    (old : 2 ^ d * S.carrier.card = 2 ^ n)
    (half : 2 * T.carrier.card = S.carrier.card) :
    2 ^ (d + 1) * T.carrier.card = 2 ^ n := by
  rw [Nat.pow_succ, Nat.mul_assoc, half, old]

/-- Processing an actual program keeps every gate affine, charging each affine
restriction to two newly constant gates or to one gate and one multiple-primary mark. -/
theorem exists_affine_restriction (p : Program signature n g) :
    ∃ (S : AffineFlat n) (d : Nat),
      (∀ i, AffineOn S (p.gateFunction interpretation i)) ∧
      2 ^ d * S.carrier.card = 2 ^ n ∧
      2 * d ≤ constantCount p S + multiCount p := by
  classical
  induction p with
  | empty =>
      refine ⟨AffineFlat.full n, 0, (fun i => Fin.elim0 i), ?_, ?_⟩
      · simp
      · simp [constantCount, multiCount]
  | @gate g p line ih =>
      obtain ⟨S, d, affine, size, charge⟩ := ih
      by_cases already : AffineOn S (lineFunction p line)
      · refine ⟨S, d, affineOn_append p line S affine already, size, ?_⟩
        rw [constantCount_gate]
        simp only [multiCount]
        split_ifs <;> lia
      · rcases line with ⟨op, wires⟩
        cases op with
        | affine r bias coefficient =>
            exact (already (affineOn_affineOp bias coefficient
              (fun slot => p.wireFunction interpretation (wires slot))
              (fun slot => affineOn_wire p affine (wires slot)))).elim
        | conjunction r polarity negated =>
            by_cases internal : ∃ slot i, wires slot = .gate i ∧
                ¬ ConstantOn S (p.gateFunction interpretation i)
            · obtain ⟨slot, i, hi, live⟩ := internal
              obtain ⟨T, sub, fixed, half⟩ := (affine i).exists_half live (!(polarity slot))
              have predecessor : ConstantOn T (p.gateFunction interpretation i) :=
                ⟨!(polarity slot), fixed⟩
              have current : ConstantOn T
                  (lineFunction p ⟨.conjunction r polarity negated, wires⟩) := by
                apply constantOn_conjunction p polarity negated wires slot
                simpa only [hi, Program.wireFunction_gate] using fixed
              have gain := constantCount_lt p sub i live predecessor
              refine ⟨T, d + 1, affineOn_append p _ T
                (fun j => (affine j).mono sub) current.affine,
                card_half_step size half, ?_⟩
              rw [constantCount_gate]
              simp only [multiCount, current, ite_true]
              split_ifs <;> lia
            · have old_constant : ∀ slot i, wires slot = .gate i →
                  ConstantOn S (p.gateFunction interpretation i) := by
                intro slot i hi
                by_contra live
                exact internal ⟨slot, i, hi, live⟩
              have large : 2 ≤ (primaryInputs
                  (⟨.conjunction r polarity negated, wires⟩ : Line signature n g)).card := by
                by_contra small
                exact already (affineOn_line_of_small_primary p _ (by lia) old_constant)
              have marked : multiPrimary
                  (⟨.conjunction r polarity negated, wires⟩ : Line signature n g) = true := by
                simp [multiPrimary, Op.isConjunction, large]
              have slot_live : ∃ slot,
                  ¬ ConstantOn S (p.wireFunction interpretation (wires slot)) := by
                by_contra absent
                push Not at absent
                exact already (constantOn_line_of_slots p _ absent).affine
              obtain ⟨slot, live⟩ := slot_live
              obtain ⟨T, sub, fixed, half⟩ :=
                (affineOn_wire p affine (wires slot)).exists_half live (!(polarity slot))
              have current := constantOn_conjunction p polarity negated wires slot fixed
              have gain := constantCount_mono p sub
              refine ⟨T, d + 1, affineOn_append p _ T
                (fun j => (affine j).mono sub) current.affine,
                card_half_step size half, ?_⟩
              rw [constantCount_gate]
              simp only [multiCount, current, marked, ite_true]
              lia

/-- Every signed AND/OR/XOR program has a nonempty monochromatic affine flat of
codimension at most half the gate count plus half its multiple-primary count, plus one.
The exact cardinality identity records the codimension without rounding logarithms. -/
theorem exists_monochromatic_affine (p : Program signature n g) (out : Wire n g) :
    ∃ (S : AffineFlat n) (d : Nat),
      ConstantOn S (p.wireFunction interpretation out) ∧
      2 ^ d * S.carrier.card = 2 ^ n ∧
      2 * d ≤ g + multiCount p + 2 := by
  obtain ⟨S, d, affine, size, charge⟩ := exists_affine_restriction p
  have count := constantCount_le p S
  by_cases constant : ConstantOn S (p.wireFunction interpretation out)
  · exact ⟨S, d, constant, size, by lia⟩
  · obtain ⟨T, sub, fixed, half⟩ := (affineOn_wire p affine out).exists_half constant false
    exact ⟨T, d + 1, ⟨false, fixed⟩, card_half_step size half, by lia⟩

end Algebraic.Aggregate.Geometry
