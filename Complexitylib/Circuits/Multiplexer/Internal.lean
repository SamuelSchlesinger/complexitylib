/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Multiplexer.Defs

/-!
# Fixed-width multiplexers -- proof internals
-/


public section

namespace Complexity

namespace Circuit

/-- Evaluation over `Basis.andOr2` is `AndOrOp.eval`; stated as an equation so it can be
rewritten without unfolding the basis inside the circuit's type. -/
private theorem andOr2_eval_eq (op : AndOrOp) (n : ℕ)
    (h : (Basis.andOr2.arity op).satisfiedBy n) (inputs : BitString n) :
    Basis.andOr2.eval op n h inputs = AndOrOp.eval op n inputs := rfl

theorem wireValue_multiplexer_left_internal (width : ℕ) [NeZero width]
    (input : BitString (1 + (width + width))) (coordinate : Fin width) :
    (multiplexer width).wireValue input
        ⟨1 + (width + width) + coordinate.val, by omega⟩ =
      (input ⟨0, by omega⟩ && input ⟨1 + coordinate.val, by omega⟩) := by
  have hnot : ¬(⟨1 + (width + width) + coordinate.val, by omega⟩ :
      Fin ((1 + (width + width)) + (width + width))).val <
        1 + (width + width) := by
    change ¬(1 + (width + width) + coordinate.val < 1 + (width + width))
    omega
  rw [Circuit.wireValue_of_not_lt _ _ _ hnot]
  have hindex :
      (⟨(1 + (width + width) + coordinate.val) -
          (1 + (width + width)), by omega⟩ : Fin (width + width)) =
        Fin.castAdd width coordinate := by
    apply Fin.ext
    simp
  rw [hindex]
  change (multiplexerInternalGate width
      (Fin.castAdd width coordinate)).val.eval
        ((multiplexer width).wireValue input) = _
  unfold multiplexerInternalGate
  have hleft : (Fin.castAdd width coordinate).val < width := coordinate.isLt
  rw [dite_eq_left hleft]
  unfold Gate.eval
  simp only [andOr2_eval_eq]
  rw [AndOrOp.eval_two_and]
  simp only [Bool.false_xor]
  rw [ite_eq_left (by omega : (0 : Fin 2).val = 0)]
  rw [ite_eq_right (by omega : ¬(1 : Fin 2).val = 0)]
  rw [Circuit.wireValue_of_lt _ _ _ (by simp; omega)]
  rw [Circuit.wireValue_of_lt _ _ _ (by simp; omega)]
  simp

theorem wireValue_multiplexer_right_internal (width : ℕ) [NeZero width]
    (input : BitString (1 + (width + width))) (coordinate : Fin width) :
    (multiplexer width).wireValue input
        ⟨1 + (width + width) + width + coordinate.val, by omega⟩ =
      (!input ⟨0, by omega⟩ &&
        input ⟨1 + width + coordinate.val, by omega⟩) := by
  have hnot : ¬(⟨1 + (width + width) + width + coordinate.val, by omega⟩ :
      Fin ((1 + (width + width)) + (width + width))).val <
        1 + (width + width) := by
    change ¬(1 + (width + width) + width + coordinate.val <
      1 + (width + width))
    omega
  rw [Circuit.wireValue_of_not_lt _ _ _ hnot]
  have hindex :
      (⟨(1 + (width + width) + width + coordinate.val) -
          (1 + (width + width)), by omega⟩ : Fin (width + width)) =
        Fin.natAdd width coordinate := by
    apply Fin.ext
    simp
    omega
  rw [hindex]
  change (multiplexerInternalGate width
      (Fin.natAdd width coordinate)).val.eval
        ((multiplexer width).wireValue input) = _
  unfold multiplexerInternalGate
  have hright : ¬(Fin.natAdd width coordinate).val < width := by
    simp
  rw [dite_eq_right hright]
  unfold Gate.eval
  simp only [andOr2_eval_eq]
  rw [AndOrOp.eval_two_and]
  rw [ite_eq_left (by omega : (0 : Fin 2).val = 0)]
  rw [ite_eq_right (by omega : ¬(1 : Fin 2).val = 0)]
  rw [Circuit.wireValue_of_lt _ _ _ (by simp; omega)]
  rw [Circuit.wireValue_of_lt _ _ _ (by simp; omega)]
  simp

theorem eval_multiplexer_packed_internal (width : ℕ) [NeZero width]
    (input : BitString (1 + (width + width))) (coordinate : Fin width) :
    (multiplexer width).eval input coordinate =
      if input ⟨0, by omega⟩ then
        input ⟨1 + coordinate.val, by omega⟩
      else
        input ⟨1 + width + coordinate.val, by omega⟩ := by
  unfold Circuit.eval
  change (multiplexerOutputGate width coordinate).eval
      ((multiplexer width).wireValue input) = _
  unfold Gate.eval multiplexerOutputGate
  simp only [andOr2_eval_eq]
  rw [AndOrOp.eval_two_or]
  simp only [Bool.false_xor]
  rw [ite_eq_left (by omega : (0 : Fin 2).val = 0)]
  rw [ite_eq_right (by omega : ¬(1 : Fin 2).val = 0)]
  rw [wireValue_multiplexer_left_internal]
  rw [wireValue_multiplexer_right_internal]
  cases input ⟨0, by omega⟩ <;> simp

theorem eval_multiplexer_internal (width : ℕ) [NeZero width]
    (control : Bool) (left right : BitString width) :
    (multiplexer width).eval
        (BitString.multiplexerInput control left right) =
      if control then left else right := by
  funext coordinate
  rw [eval_multiplexer_packed_internal]
  cases control <;>
    simp [BitString.multiplexerInput, Fin.append, Fin.addCases]
  rw [dite_eq_right (by omega)]
  apply congrArg right
  apply Fin.ext
  simp
  omega

end Circuit

end Complexity
