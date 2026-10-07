/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AC0.Normalization.Cslib.Defs
public import Complexitylib.Circuits.AC0.Normalization
public import Complexitylib.Cslib.Circuit.Depth

/-!
# CSLib formula normalization preserves values, depths, and size bounds

The adapter preserves every program wire's evaluation and depth. The existing typed wire
normalizer therefore gives the same bounds for CSLib's selected output wire.
-/

public section

namespace Complexity.CslibAC0

open Cslib.Circuits

variable {n g : ℕ} [NeZero n]

lemma wireValue_asTyped (p : Program Basis.unboundedAndOr.signature n g)
    (x : BitString n) (w : Wire n g) :
    (asTyped p).wireValue x w.index = p.trace Basis.unboundedAndOr.interpretation x w := by
  set values : Fin g → Bool := fun j => (asTyped p).wireValue x (Fin.natAdd n j)
  have helim : ∀ w, Wire.elim x values w = (asTyped p).wireValue x w.index := by
    intro w
    cases w with
    | input i =>
      rw [Wire.elim_input, Wire.index_input, Complexity.Circuit.wireValue_of_lt _ _ _ (by simp)]
      rfl
    | gate j => rfl
  have heval : values = p.eval Basis.unboundedAndOr.interpretation x := by
    apply Program.eq_eval_of_forall_lines_eval
    intro j
    show _ = (asTyped p).wireValue x (Fin.natAdd n j)
    rw [Complexity.Circuit.wireValue_of_not_lt _ _ _ (by simp)]
    have hj : (⟨(Fin.natAdd n j).val - n, by simp⟩ : Fin g) = j := Fin.ext (by simp)
    rw [hj]
    change Basis.unboundedAndOr.interpretation (p.lines j).op
      (Wire.elim x values ∘ (p.lines j).wires) = _
    unfold Basis.interpretation
    congr 1
    funext a
    congr 1
    exact helim _
  rw [← helim, heval]
  rfl

lemma wireDepth_asTyped (p : Program Basis.unboundedAndOr.signature n g)
    (w : Wire n g) :
    (asTyped p).wireDepth w.index = p.wireDepths w := by
  suffices h : ∀ k (j : Fin g), j.val = k →
      (asTyped p).wireDepth (Fin.natAdd n j) = p.depths j by
    cases w with
    | input i => exact Complexity.Circuit.wireDepth_of_lt _ _ (by simp)
    | gate j => exact h _ j rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j hj
    rw [Complexity.Circuit.wireDepth_of_not_lt _ _ (by simp)]
    have he : (⟨(Fin.natAdd n j).val - n, by simp⟩ : Fin g) = j := Fin.ext (by simp)
    rw [he, Program.depths_eq_lines_depth]
    change 1 + Fin.foldl (p.lines j).op.fanIn
      (fun acc a => max acc ((asTyped p).wireDepth ((p.lines j).wires a).index)) 0 = _
    have hw : ∀ a, (asTyped p).wireDepth ((p.lines j).wires a).index =
        p.wireDepths ((p.lines j).wires a) := by
      intro a
      have hlt := Program.lines_wires_lt p j a
      generalize (p.lines j).wires a = w at hlt ⊢
      cases w with
      | input i => exact Complexity.Circuit.wireDepth_of_lt _ _ (by simp)
      | gate l => exact ih l (by simp at hlt; lia) l rfl
    have hfold : (fun (acc : ℕ) (a : Fin (p.lines j).op.fanIn) =>
        max acc ((asTyped p).wireDepth ((p.lines j).wires a).index)) =
        (fun acc a => max acc (p.wireDepths ((p.lines j).wires a))) := by
      funext acc a
      rw [hw a]
    rw [hfold]
    simp only [Line.depth, Basis.signature, Nat.succ_eq_add_one, Nat.add_comm]

lemma outputFormula_spec_proof (c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n 1) :
    (∀ x, (outputFormula c).eval x = c.eval Basis.unboundedAndOr.interpretation x 0) ∧
    (outputFormula c).depth ≤ c.depth ∧
    (outputFormula c).size ≤ (2 * (n + c.size) + 1) ^ (c.depth + 1) := by
  refine ⟨fun x => ?_, ?_, ?_⟩
  · simp only [outputFormula, Complexity.Circuit.eval_wireAC0Formula, Bool.false_xor,
      wireValue_asTyped, Cslib.Circuits.Circuit.eval, Function.comp_apply]
  · have h := (asTyped c.program).depth_wireAC0Formula false (c.outputs 0).index
    rw [wireDepth_asTyped] at h
    exact h.trans ((c.depth_le_iff _).mp le_rfl 0)
  · have h := (asTyped c.program).size_wireAC0Formula false (c.outputs 0).index
    rw [wireDepth_asTyped] at h
    exact h.trans (Nat.pow_le_pow_right (by lia) (Nat.add_le_add_right
      ((c.depth_le_iff _).mp le_rfl 0) 1))

end Complexity.CslibAC0
