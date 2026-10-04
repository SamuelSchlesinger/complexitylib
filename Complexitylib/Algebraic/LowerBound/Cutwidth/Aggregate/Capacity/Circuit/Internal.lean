/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Capacity.Circuit.Defs

/-!
# Exact reconstruction from primary-input summaries

Acyclic gate-equation uniqueness supplies topological reconstruction. Splitting a
special gate's product requires commutativity, but no inverses or cancellation.
-/

@[expose] public section

namespace Algebraic.Aggregate.Capacity

variable {J : Type} {State : J → Type} {n g : ℕ}

/-- A line summary depends only on the selected primary wires. -/
theorem lineSummary_eq_of_selected_agree [∀ j, CommMonoid (State j)]
    (line : Line (signature State) n g) (U : Finset (Fin n)) (x y : Wire n g → Bool)
    (h : ∀ wire, selected U wire → x wire = y wire) :
    lineSummary line U x = lineSummary line U y := by
  rcases line with ⟨op, wires⟩
  cases op with
  | binary f =>
      simp only [lineSummary]
      split <;> split <;> simp_all
  | special kind arity contribution readout =>
      apply Finset.prod_congr rfl
      intro slot hslot
      exact congrArg (contribution slot) (h _ (Finset.mem_filter.mp hslot).2)

/-- Equal summaries and equal unselected values determine the same gate output. -/
theorem line_eval_eq_of_summary_eq [∀ j, CommMonoid (State j)]
    (line : Line (signature State) n g) (U : Finset (Fin n)) (x y : Wire n g → Bool)
    (hs : lineSummary line U x = lineSummary line U y)
    (h : ∀ wire, ¬ selected U wire → x wire = y wire) :
    interpretation line.op (x ∘ line.wires) = interpretation line.op (y ∘ line.wires) := by
  rcases line with ⟨op, wires⟩
  cases op with
  | binary f =>
      simp only [lineSummary] at hs
      simp only [interpretation, Function.comp_apply]
      split_ifs at hs with h0 h1 h1
      · exact hs
      · rw [hs, h _ h1]
      · rw [h _ h0, hs]
      · rw [h _ h0, h _ h1]
  | special kind arity contribution readout =>
      apply congrArg readout
      dsimp only [lineSummary] at hs
      simp only [Function.comp_apply]
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
        (fun slot => selected U (wires slot)) (fun slot => contribution slot (x (wires slot))),
        ← Finset.prod_filter_mul_prod_filter_not Finset.univ
        (fun slot => selected U (wires slot)) (fun slot => contribution slot (y (wires slot))), hs]
      congr 1
      apply Finset.prod_congr rfl
      intro slot hslot
      exact congrArg (contribution slot) (h _ (Finset.mem_filter.mp hslot).2)

/-- Changing internal gate values does not affect a primary-input summary. -/
theorem lineSummary_elim [∀ j, CommMonoid (State j)]
    (line : Line (signature State) n g) (U : Finset (Fin n))
    (input : Fin n → Bool) (gates : Fin g → Bool) :
    lineSummary line U (Wire.elim input gates) =
      lineSummary line U (Wire.elim input (fun _ => false)) := by
  apply lineSummary_eq_of_selected_agree
  intro wire hw
  cases wire with
  | input => rfl
  | gate => exact hw.elim

/-- The complete key depends only on selected primary inputs. -/
theorem key_eq_of_inputs_agree [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (U : Finset (Fin n)) (x y : Fin n → Bool)
    (h : ∀ i ∈ U, x i = y i) : key p U x = key p U y := by
  funext gate
  apply lineSummary_eq_of_selected_agree
  intro wire hw
  cases wire with
  | input i => exact h i hw
  | gate => exact hw.elim

/-- Equal keys let the other party reconstruct every gate, regardless of depth. -/
theorem eval_eq_of_key_eq [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (U : Finset (Fin n)) (x y : Fin n → Bool)
    (hk : key p U x = key p U y) (h : ∀ i, i ∉ U → x i = y i) :
    p.eval interpretation x = p.eval interpretation y := by
  apply Program.eq_eval_of_forall_lines_eval
  intro gate
  calc
    _ = (p.lines gate).eval interpretation x (p.eval interpretation x) := by
      apply line_eval_eq_of_summary_eq (p.lines gate) U
      · simpa only [key, lineSummary_elim] using (congrFun hk gate).symm
      · intro wire hw
        cases wire with
        | input i => exact (h i hw).symm
        | gate => rfl
    _ = _ := Program.lines_eval p interpretation x gate

/-- Gate outputs and unselected primary outputs are reconstructed exactly. -/
theorem trace_eq_of_key_eq [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (U : Finset (Fin n)) (x y : Fin n → Bool)
    (hk : key p U x = key p U y) (h : ∀ i, i ∉ U → x i = y i)
    (wire : Wire n g) (hw : ¬ selected U wire) :
    p.trace interpretation x wire = p.trace interpretation y wire := by
  cases wire with
  | input i => exact h i hw
  | gate gate => exact congrFun (eval_eq_of_key_eq p U x y hk h) gate

end Algebraic.Aggregate.Capacity
