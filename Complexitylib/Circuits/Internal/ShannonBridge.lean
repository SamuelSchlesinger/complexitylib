/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Internal.CircuitToDescriptor
import Std.Tactic.BVDecide.Normalize.Bool

/-!
# Internal: Shannon bridge from descriptors to typed circuits

This module pads the descriptor of a typed single-output circuit to the fixed
size used by the Shannon counting argument and transfers the resulting lower
bound back to `Circuit`.
-/

@[expose] public section

namespace Complexity

open CircDesc

/-- Pad a descriptor to a larger size by appending copy gates. -/
private def padDesc {N s : Nat} (d : CircDesc N s)
    (s' : Nat) (hs : 0 < s) (h : s ≤ s') :
    CircDesc N s' := fun i =>
  if hi : i.val < s then
    let slot := d ⟨i.val, hi⟩
    (slot.1,
      (⟨slot.2.1.1.val, by omega⟩,
        ⟨slot.2.1.2.val, by omega⟩),
      slot.2.2)
  else
    (false,
      (⟨N + s - 1, by omega⟩, ⟨N + s - 1, by omega⟩),
      (false, false))

private theorem wireVal_padDesc_lt {N s s' : Nat}
    (d : CircDesc N s) (hs : 0 < s) (h : s ≤ s')
    (x : BitString N) (w : Fin (N + s'))
    (hw : w.val < N + s) :
    wireVal (padDesc d s' hs h) x w =
      wireVal d x ⟨w.val, hw⟩ := by
  by_cases hwN : w.val < N
  · simp [wireVal, hwN]
  · push Not at hwN
    have hi : w.val - N < s := by omega
    conv_lhs => unfold wireVal
    simp only [show ¬(w.val < N) from by omega, dite_false]
    conv_rhs => unfold wireVal
    simp only [show ¬(w.val < N) from by omega, dite_false]
    simp only [padDesc, show w.val - N < s from hi, dite_true]
    have hw1 : (d ⟨w.val - N, hi⟩).2.1.1.val < N + s :=
      (d ⟨w.val - N, hi⟩).2.1.1.isLt
    have hw2 : (d ⟨w.val - N, hi⟩).2.1.2.val < N + s :=
      (d ⟨w.val - N, hi⟩).2.1.2.isLt
    congr 1 <;>
      (congr 1 <;>
        (first
          | rfl
          | (congr 1
             split_ifs with hlt <;>
               (first
                 | exact wireVal_padDesc_lt d hs h x _
                     (by first | exact hw1 | exact hw2)
                 | rfl))))
  termination_by w.val

private theorem wireVal_padDesc_ge {N s s' : Nat}
    (d : CircDesc N s) (hs : 0 < s) (h : s ≤ s')
    (x : BitString N) (w : Fin (N + s'))
    (hw : N + s ≤ w.val) :
    wireVal (padDesc d s' hs h) x w =
      wireVal d x ⟨N + s - 1, by omega⟩ := by
  conv_lhs => unfold wireVal
  simp only [show ¬(w.val < N) from by omega, dite_false]
  simp only [padDesc, show ¬(w.val - N < s) from by omega,
    dite_false]
  simp only [Bool.false_xor, Bool.or_self]
  simp only [show N + s - 1 < w.val from by omega, ↓reduceIte]
  have hlt : N + s - 1 < N + s := by omega
  exact wireVal_padDesc_lt d hs h x
    ⟨N + s - 1, by omega⟩ hlt

private theorem eval_padDesc {N s s' : Nat}
    (d : CircDesc N s) (hs : 0 < s) (h : s ≤ s')
    (hs' : 0 < s') :
    eval hs' (padDesc d s' hs h) = eval hs d := by
  funext x
  simp only [eval]
  by_cases hsle : N + s ≤ N + s' - 1
  · rw [wireVal_padDesc_ge d hs h x
      ⟨N + s' - 1, by omega⟩ (by omega)]
  · push Not at hsle
    have hsize : s = s' := by omega
    subst s'
    exact wireVal_padDesc_lt d hs h x
      ⟨N + s - 1, by omega⟩ (by omega)

/-- Internal Shannon lower bound transported to typed circuits. -/
theorem shannon_lower_bound_circuit_internal
    (N : Nat) [NeZero N] (hN : 6 ≤ N) :
    ∃ f : BitString N → Bool,
      ∀ G (c : Circuit Basis.andOr2 N 1 G),
        G + 1 ≤ 2 ^ N / (5 * N) →
        (fun x => (c.eval x) 0) ≠ f := by
  obtain ⟨f, hf⟩ := shannon_lower_bound N hN
  exact ⟨f, fun G c hsize habs => by
    have hspos := s_pos N hN
    have hG1 : 0 < G + 1 := Nat.succ_pos G
    let d := circuitToDesc c
    let d' := padDesc d (2 ^ N / (5 * N)) hG1 hsize
    have h1 : eval hspos d' = eval hG1 d :=
      eval_padDesc d hG1 hsize hspos
    have h2 : (fun x => (c.eval x) 0) = eval hG1 d :=
      circuit_eval_eq_eval c
    have h3 : eval hspos d' = f := by
      rw [h1, ← h2, habs]
    exact hf d' h3⟩

end Complexity
