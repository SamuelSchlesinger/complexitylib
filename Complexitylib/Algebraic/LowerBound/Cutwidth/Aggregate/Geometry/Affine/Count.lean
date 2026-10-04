/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Lines
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting permanently constant gate outputs

The pairing proof charges a restriction to newly constant outputs. Constancy is
preserved on smaller flats, so these charges cannot be reused by later gates.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

open scoped Classical

variable {n g : Nat} {S T : AffineFlat n}

/-- Number of actual gate outputs already constant on a flat. -/
noncomputable def constantCount (p : Program signature n g) (S : AffineFlat n) : Nat :=
  ∑ gate, if ConstantOn S (p.gateFunction interpretation gate) then 1 else 0

/-- Each actual gate can contribute at most one permanently constant output. -/
theorem constantCount_le (p : Program signature n g) (S : AffineFlat n) :
    constantCount p S ≤ g := by
  calc
    constantCount p S ≤ ∑ _ : Fin g, 1 := by
      apply Finset.sum_le_sum
      intro i _
      split <;> lia
    _ = g := by simp

/-- Further restrictions cannot decrease the constant-output count. -/
theorem constantCount_mono (p : Program signature n g) (sub : T.carrier ⊆ S.carrier) :
    constantCount p S ≤ constantCount p T := by
  apply Finset.sum_le_sum
  intro i _
  by_cases h : ConstantOn S (p.gateFunction interpretation i)
  · simp only [h, h.mono sub, ite_true, le_refl]
  · simp only [h, ite_false]
    exact Nat.zero_le _

/-- Freezing one previously live gate strictly increases the count. -/
theorem constantCount_lt (p : Program signature n g) (sub : T.carrier ⊆ S.carrier)
    (gate : Fin g) (before : ¬ ConstantOn S (p.gateFunction interpretation gate))
    (after : ConstantOn T (p.gateFunction interpretation gate)) :
    constantCount p S < constantCount p T := by
  apply Finset.sum_lt_sum
  · intro i _
    by_cases h : ConstantOn S (p.gateFunction interpretation i)
    · simp only [h, h.mono sub, ite_true, le_refl]
    · simp only [h, ite_false]
      exact Nat.zero_le _
  · exact ⟨gate, Finset.mem_univ _, by simp only [before, after, ite_false, ite_true]; lia⟩

/-- Appending a line contributes exactly its own constant-output indicator. -/
theorem constantCount_gate (p : Program signature n g) (line : Line signature n g)
    (S : AffineFlat n) :
    constantCount (p.gate line) S = constantCount p S +
      if ConstantOn S (lineFunction p line) then 1 else 0 := by
  simp only [constantCount, Fin.sum_univ_castSucc,
    Program.gateFunction_gate_castSucc, Program.gateFunction_gate_last]
  rfl

end Algebraic.Aggregate.Geometry
