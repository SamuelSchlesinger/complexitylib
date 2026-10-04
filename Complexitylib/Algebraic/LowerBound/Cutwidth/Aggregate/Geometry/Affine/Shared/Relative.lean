/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Count

/-!
# Pairing after some primary coordinates have been fixed

The affine restriction argument starts on any affine flat. Its charge subtracts
outputs already constant there, including gates not yet reached in topological
order. Only conjunctions with two remaining primary coordinates need single charges.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Shared

open scoped Classical

variable {n g : Nat}

/-- A conjunction still having at least two primary coordinates outside the fixed set. -/
def remainingMark (line : Line signature n g) (fixed : Finset (Fin n)) : Bool :=
  line.op.isConjunction && decide (2 ≤ (primaryInputs line \ fixed).card)

/-- Number of conjunctions still having at least two unfixed primary coordinates. -/
def remainingCount : {g : Nat} → Program signature n g → Finset (Fin n) → Nat
  | _, .empty, _ => 0
  | _, .gate p line, fixed => remainingCount p fixed + if remainingMark line fixed then 1 else 0

/-- Fixed primary coordinates and constant internal predecessors can be omitted
when checking whether a line depends on at most one variable. -/
theorem affineOn_line_of_remaining_small (p : Program signature n g)
    (line : Line signature n g) (S : AffineFlat n) (fixed : Finset (Fin n))
    (fixedOn : ∀ i ∈ fixed, ConstantOn S (fun x => x i))
    (small : (primaryInputs line \ fixed).card ≤ 1)
    (constant : ∀ slot i, line.wires slot = .gate i →
      ConstantOn S (p.gateFunction interpretation i)) : AffineOn S (lineFunction p line) := by
  apply affineOn_of_depends_small (primaryInputs line \ fixed) small
  intro x hx y hy same
  apply congrArg (interpretation line.op)
  funext slot
  cases hw : line.wires slot with
  | input i =>
      have hi : i ∈ primaryInputs line :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨slot, hw⟩⟩
      have eq : x i = y i := by
        by_cases h : i ∈ fixed
        · obtain ⟨b, hb⟩ := fixedOn i h
          exact (hb x hx).trans (hb y hy).symm
        · exact same i (Finset.mem_sdiff.mpr ⟨hi, h⟩)
      simpa only [Function.comp_apply, hw, Wire.elim] using eq
  | gate i =>
      obtain ⟨b, hb⟩ := constant slot i hw
      simpa only [Function.comp_apply, hw, Wire.elim, Program.gateFunction_apply] using
        (hb x hx).trans (hb y hy).symm

/-- Appending one affine output preserves the affineness of the whole trace. -/
private theorem affineOn_append (p : Program signature n g) (line : Line signature n g)
    (S : AffineFlat n) (old : ∀ i, AffineOn S (p.gateFunction interpretation i))
    (new : AffineOn S (lineFunction p line)) :
    ∀ i, AffineOn S ((p.gate line).gateFunction interpretation i) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Program.gateFunction_gate_last]
    exact new
  · simpa only [Program.gateFunction_gate_castSucc] using old j

/-- Affine elimination from an arbitrary initial flat charges only new constants
and conjunctions with at least two still-unfixed primary variables. -/
theorem exists_affine_restriction (p : Program signature n g) (S : AffineFlat n)
    (fixed : Finset (Fin n)) (fixedOn : ∀ i ∈ fixed, ConstantOn S (fun x => x i)) :
    ∃ (T : AffineFlat n) (d : Nat), T.carrier ⊆ S.carrier ∧
      (∀ i, AffineOn T (p.gateFunction interpretation i)) ∧
      2 ^ d * T.carrier.card = S.carrier.card ∧
      2 * d + constantCount p S ≤ constantCount p T + remainingCount p fixed := by
  classical
  induction p with
  | empty =>
      exact ⟨S, 0, Finset.Subset.refl _, (fun i => Fin.elim0 i), by simp,
        by simp [constantCount, remainingCount]⟩
  | @gate g p line ih =>
      obtain ⟨T, d, sub, affine, size, charge⟩ := ih
      have fixedT : ∀ i ∈ fixed, ConstantOn T (fun x => x i) :=
        fun i hi => (fixedOn i hi).mono sub
      by_cases already : AffineOn T (lineFunction p line)
      · refine ⟨T, d, sub, affineOn_append p line T affine already, size, ?_⟩
        rw [constantCount_gate, constantCount_gate]
        simp only [remainingCount]
        have monotone : ConstantOn S (lineFunction p line) →
            ConstantOn T (lineFunction p line) := fun h => h.mono sub
        split_ifs <;> lia
      · have not_initial : ¬ ConstantOn S (lineFunction p line) :=
          fun h => already (h.mono sub).affine
        rcases line with ⟨op, wires⟩
        cases op with
        | affine r bias coefficient =>
            exact (already (affineOn_affineOp bias coefficient
              (fun slot => p.wireFunction interpretation (wires slot))
              (fun slot => affineOn_wire p affine (wires slot)))).elim
        | conjunction r polarity negated =>
            by_cases internal : ∃ slot i, wires slot = .gate i ∧
                ¬ ConstantOn T (p.gateFunction interpretation i)
            · obtain ⟨slot, i, hi, live⟩ := internal
              obtain ⟨U, smaller, value, half⟩ := (affine i).exists_half live (!(polarity slot))
              have predecessor : ConstantOn U (p.gateFunction interpretation i) :=
                ⟨!(polarity slot), value⟩
              have current : ConstantOn U
                  (lineFunction p ⟨.conjunction r polarity negated, wires⟩) := by
                apply constantOn_conjunction p polarity negated wires slot
                simpa only [hi, Program.wireFunction_gate] using value
              have gain := constantCount_lt p smaller i live predecessor
              refine ⟨U, d + 1, smaller.trans sub, affineOn_append p _ U
                (fun j => (affine j).mono smaller) current.affine, ?_, ?_⟩
              · rw [Nat.pow_succ, Nat.mul_assoc, half, size]
              · rw [constantCount_gate, constantCount_gate]
                simp only [remainingCount, current, not_initial, ite_true, ite_false]
                split_ifs <;> lia
            · have old_constant : ∀ slot i, wires slot = .gate i →
                  ConstantOn T (p.gateFunction interpretation i) := by
                intro slot i hi
                by_contra live
                exact internal ⟨slot, i, hi, live⟩
              have large : 2 ≤ (primaryInputs
                  (⟨.conjunction r polarity negated, wires⟩ : Line signature n g) \
                    fixed).card := by
                by_contra small
                exact already (affineOn_line_of_remaining_small p _ T fixed fixedT
                  (by lia) old_constant)
              have marked : remainingMark
                  (⟨.conjunction r polarity negated, wires⟩ : Line signature n g) fixed = true := by
                simp [remainingMark, Op.isConjunction, large]
              have slot_live : ∃ slot,
                  ¬ ConstantOn T (p.wireFunction interpretation (wires slot)) := by
                by_contra absent
                push Not at absent
                exact already (constantOn_line_of_slots p _ absent).affine
              obtain ⟨slot, live⟩ := slot_live
              obtain ⟨U, smaller, value, half⟩ :=
                (affineOn_wire p affine (wires slot)).exists_half live (!(polarity slot))
              have current := constantOn_conjunction p polarity negated wires slot value
              have gain := constantCount_mono p smaller
              refine ⟨U, d + 1, smaller.trans sub, affineOn_append p _ U
                (fun j => (affine j).mono smaller) current.affine, ?_, ?_⟩
              · rw [Nat.pow_succ, Nat.mul_assoc, half, size]
              · rw [constantCount_gate, constantCount_gate]
                simp only [remainingCount, current, marked, not_initial, ite_true, ite_false]
                lia

end Algebraic.Aggregate.Geometry.Shared
