/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Cslib.Guard.Defs
public import Complexitylib.Interop.Cslib.FromMultiTape
import Complexitylib.Interop.Cslib.Guard.Internal

/-!
# Polynomial-time computation on a regular input domain

A DFA guard extends a binary CSLib computation to all strings, returning empty
output outside its regular domain. Only accepted inputs need source runtime
bounds, since rejection never starts the source machine.
-/

public section

namespace Complexity.CslibGuard

/-- Accepted inputs incur just linear validation and rewind overhead. -/
theorem computes_accepted {k : ℕ} {σ Q : Type}
    (M : Turing.MultiTapeTM k Bool Q) (D : DFA Bool σ)
    {w output : List Bool} {t s : ℕ} (hw : w ∈ D.accepts)
    (h : M.ComputesInTimeAndSpace w output t s) :
    (machine M D).ComputesInTimeAndSpace w output (2 * w.length + t + 2)
      ((machine M D).spaceUsed ((machine M D).initCfg w) (2 * w.length + t + 2)) := by
  have hr : (machine M D).runFrom ((machine M D).initCfg w) (2 * w.length + t + 2) =
      liftCfg (σ := σ) (M.runFrom (M.initCfg w) t) := by
    rw [show 2 * w.length + t + 2 = (2 * w.length + 2) + t by lia,
      run_add, prepare M D hw, run_lift]
  refine ⟨?_, ?_, rfl⟩
  · rw [hr]
    simp only [liftCfg, Turing.Cfg.mapState, h.1, Option.map_none]
  · rw [hr]
    exact h.2.1

/-- Rejected inputs halt with empty output after a single scan. -/
theorem computes_rejected {k : ℕ} {σ Q : Type}
    (M : Turing.MultiTapeTM k Bool Q) (D : DFA Bool σ)
    {w : List Bool} (hw : w ∉ D.accepts) :
    (machine M D).ComputesInTimeAndSpace w [] (w.length + 1)
      ((machine M D).spaceUsed ((machine M D).initCfg w) (w.length + 1)) :=
  ⟨(rejected M D hw).1, (rejected M D hw).2, rfl⟩

/-- Polynomial source bounds on a regular domain give a total canonical FP function. -/
theorem mem_FP_on_dfa {k : ℕ} {σ Q : Type} [Fintype σ] [Fintype Q]
    (M : Turing.MultiTapeTM k Bool Q) (D : DFA Bool σ)
    [DecidablePred (· ∈ D.accepts)] {f : List Bool → List Bool} {p : Polynomial ℕ}
    (h : ∀ w ∈ D.accepts, ∃ t ≤ p.eval w.length, ∃ s,
      M.ComputesInTimeAndSpace w (f w) t s) :
    (fun w => if w ∈ D.accepts then f w else []) ∈ FP := by
  let time (w : List Bool) := 2 * w.length + p.eval w.length + 2
  refine mem_FP_of_computableInTimeAndSpace
    (p := Polynomial.C 2 * Polynomial.X + p + Polynomial.C 2)
    (s := fun w => (machine M D).spaceUsed ((machine M D).initCfg w) (time w))
    ⟨k, State σ Q, inferInstance, machine M D, ?_⟩
  intro w
  refine ⟨time w, by simp [time], _, le_rfl, ?_⟩
  change (machine M D).ComputesInTimeAndSpace w (if w ∈ D.accepts then f w else [])
    (time w) ((machine M D).spaceUsed ((machine M D).initCfg w) (time w))
  by_cases hw : w ∈ D.accepts
  · rw [ite_eq_left hw]
    obtain ⟨t, ht, s, hs⟩ := h w hw
    have hc := computes_accepted M D hw hs
    have heq := (machine M D).runFrom_eq_of_halt ((machine M D).initCfg w)
      (by dsimp [time]; lia : 2 * w.length + t + 2 ≤ time w) hc.1
    exact ⟨by rw [heq]; exact hc.1, by rw [heq]; exact hc.2.1, rfl⟩
  · rw [ite_eq_right hw]
    have hc := computes_rejected M D hw
    have heq := (machine M D).runFrom_eq_of_halt ((machine M D).initCfg w)
      (by dsimp [time]; lia : w.length + 1 ≤ time w) hc.1
    exact ⟨by rw [heq]; exact hc.1, by rw [heq]; exact hc.2.1, rfl⟩

end Complexity.CslibGuard
