/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM2.FP.Defs
import Complexitylib.Interop.Mathlib.TM0.Marked.Internal.Initialization

/-!
# Exact marked-input and output decoding identities

Copying a binary word in order builds the stack representation of its reverse.
Reading a clean final stack tape in order likewise emits the reversed stack.
Both identities include the single marker cell used for an empty stack.
-/

@[expose] public section

namespace Complexity.MathlibTM2

open Turing

lemma binaryAdapter_input (tm : FinTM2) [∀ k, Fintype (tm.Γ k)]
    (input : tm.Γ tm.k₀ ≃ Bool) (output : tm.Γ tm.k₁ ≃ Bool)
    {Q : Type} [Fintype Q] [Inhabited Q]
    (G : TM0.Machine (TM2to1.Γ' tm.K tm.Γ) Q) (w : List Bool) :
    (binaryAdapter tm input output G).inputCells true w =
      TM2to1.trInit tm.k₀ (w.reverse.map input.symm) := by
  cases w with
  | nil => rfl
  | cons b bs =>
      simp only [TM2to1.trInit, List.map_reverse, List.reverse_reverse]
      change (binaryAdapter tm input output G).bit true b ::
        (binaryAdapter tm input output G).inputCells false bs = _
      rw [MathlibTM0.MarkedMachine.inputCells_false]
      change (true, Function.update (fun _ => none) tm.k₀ (some (input.symm b))) ::
          bs.map (fun x => (false, Function.update (fun _ => none) tm.k₀ (some (input.symm x)))) =
        (true, Function.update (fun _ => none) tm.k₀ (some (input.symm b))) ::
          (bs.map input.symm).map (fun a => (false, Function.update (fun _ => none) tm.k₀ (some a)))
      rw [List.map_map]
      rfl

lemma decode_trInit {K α : Type} [DecidableEq K] {Γ : K → Type}
    (k : K) (e : Γ k ≃ α) (w : List (Γ k)) (j : ℕ) :
    (((Tape.mk₁ (TM2to1.trInit k w)).nth j).2 k).map e = (w.reverse.map e)[j]? := by
  rw [MathlibTM0.nth_mk₁]
  simp only [Int.natCast_nonneg, not_lt_of_ge, ite_false, Int.toNat_natCast]
  cases hw : w.reverse with
  | nil =>
      simp only [TM2to1.trInit, hw]
      change ((([(true, fun _ => none)] : List (TM2to1.Γ' K Γ)).getI j).2 k).map e =
        ([] : List α)[j]?
      cases j <;> rfl
  | cons b bs =>
      simp only [TM2to1.trInit, hw]
      change ((((true, Function.update (fun _ => none) k (some b)) ::
        bs.map (fun a => (false, Function.update (fun _ => none) k (some a)))).getI j).2 k).map e =
        ((b :: bs).map e)[j]?
      cases j with
      | zero => simp
      | succ j =>
          simp only [List.map_cons,
            List.getElem?_cons_succ, List.getI_eq_getElem?_getD,
            List.getElem?_map]
          cases bs[j]? with
          | none => simp; rfl
          | some a => simp

end Complexity.MathlibTM2
