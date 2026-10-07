/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Mathlib.TM0.Guard.Defs

/-!
# Correctness of the DFA input guard

The scan takes one step per input bit. On acceptance, returning to the start
takes another input-length plus two steps. Rejection halts with empty output.
-/

public section

namespace Complexity.MathlibTM0.BinaryMachine

/-- Consecutive source runs compose by option bind. -/
theorem run_add (M : BinaryMachine) (t u : ℕ) (c : M.Config) :
    M.run (t + u) c = (M.run t c).bind (M.run u) := by
  induction t generalizing c with
  | zero => simp [run]
  | succ t ih => simp only [Nat.succ_add, run, ih, Option.bind_assoc]

namespace Guard

open Turing

variable (M : BinaryMachine) {σ : Type} [Fintype σ] (D : DFA Bool σ)

/-- Reading a bit advances the DFA and moves right. -/
theorem step_scan_bit (q : σ) (T : Tape M.Alphabet) (b : Bool)
    (h : M.readBit T.head = some b) :
    (M.guarded D).step ⟨.scan q, T⟩ =
      some ⟨.scan (D.step q b), T.move .right⟩ := by
  simp only [step, TM0.step, guarded, h, Option.map_some]

/-- Moving right consumes the next explicit tape cell. -/
theorem move_right (L R : List M.Alphabet) (a : M.Alphabet) :
    (Tape.mk₂ L (a :: R)).move .right = Tape.mk₂ (a :: L) R := by
  simp [Tape.mk₂, ListBlank.cons_mk, ListBlank.head_mk, ListBlank.tail_mk]

/-- Moving left exposes the nearest cell on the left. -/
theorem move_left (L R : List M.Alphabet) (a : M.Alphabet) :
    (Tape.mk₂ (a :: L) R).move .left = Tape.mk₂ L (a :: R) := by
  simp [Tape.mk₂, ListBlank.cons_mk, ListBlank.head_mk, ListBlank.tail_mk]

/-- The guard scans an explicit binary suffix without changing the tape. -/
theorem scan (w : List Bool) (L : List M.Alphabet) (q : σ) :
    (M.guarded D).run w.length ⟨.scan q, Tape.mk₂ L (w.map M.bit)⟩ =
      some ⟨.scan (D.evalFrom q w), Tape.mk₂ ((w.map M.bit).reverse ++ L) []⟩ := by
  induction w generalizing L q with
  | nil => rfl
  | cons b w ih =>
      rw [List.length_cons, run]
      have hb : M.readBit (Tape.mk₂ L ((b :: w).map M.bit)).head = some b :=
        M.readBit_bit b
      rw [step_scan_bit M D q _ b hb]
      simpa only [List.map_cons, move_right, Option.bind_some, List.reverse_cons,
        DFA.evalFrom_cons, List.append_assoc, List.singleton_append] using
        ih (M.bit b :: L) (D.step q b)

/-- Rewinding crosses the input once and returns from the preceding blank. -/
theorem rewind (w : List Bool) (R : List M.Alphabet) :
    (M.guarded D).run (w.length + 1)
        ⟨.rewind, (Tape.mk₂ (w.map M.bit) R).move .left⟩ =
      some ⟨.run default, Tape.mk₂ [] ((w.map M.bit).reverse ++ R)⟩ := by
  induction w generalizing R with
  | nil =>
      change ((M.guarded D).step
        ⟨.rewind, (Tape.mk₂ [] R).move .left⟩).bind ((M.guarded D).run 0) = _
      have hb : M.readBit ((Tape.mk₂ [] R).move .left).head = none := M.readBit_blank
      simp only [step, TM0.step, guarded, hb, Option.map_some, Option.bind_some, run,
        Tape.move_left_right, List.map_nil, List.reverse_nil, List.nil_append]
  | cons b w ih =>
      rw [List.length_cons, Nat.succ_add, run]
      have hb : M.readBit ((Tape.mk₂ ((b :: w).map M.bit) R).move .left).head =
          some b := M.readBit_bit b
      have hs : (M.guarded D).step
          ⟨.rewind, (Tape.mk₂ ((b :: w).map M.bit) R).move .left⟩ =
          some ⟨.rewind, (Tape.mk₂ (w.map M.bit) (M.bit b :: R)).move .left⟩ := by
        dsimp only [step, TM0.step, guarded]
        rw [hb]
        simp only [Option.map_some, List.map_cons, move_left]
      rw [hs, Option.bind_some, ih]
      simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Tag a source configuration with the execution phase. -/
def liftCfg (c : M.Config) : (M.guarded D).Config := ⟨.run c.q, c.Tape⟩

/-- The execution phase preserves one source transition. -/
theorem step_lift (c : M.Config) :
    (M.guarded D).step (liftCfg M D c) = (M.step c).map (liftCfg M D) := by
  simp only [step, TM0.step, guarded, liftCfg, Option.map_map, Function.comp_def]

/-- The execution phase preserves any finite source run. -/
theorem run_lift (t : ℕ) (c : M.Config) :
    (M.guarded D).run t (liftCfg M D c) = (M.run t c).map (liftCfg M D) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
      rw [run, step_lift, run]
      cases hc : M.step c with
      | none => rfl
      | some c' => simpa only [Option.map_some, Option.bind_some] using ih c'

/-- An accepted input is restored at the source's initial state in linear time. -/
theorem prepare {w : List Bool} (hw : w ∈ D.accepts) :
    (M.guarded D).run (2 * w.length + 2)
        ⟨.scan D.start, Tape.mk₁ (w.map M.bit)⟩ =
      some (liftCfg M D (TM0.init (w.map M.bit))) := by
  have ha : D.evalFrom D.start w ∈ D.accept := hw
  rw [show 2 * w.length + 2 = w.length + (w.length + 1 + 1) by lia, run_add]
  change ((M.guarded D).run w.length ⟨.scan D.start, Tape.mk₂ [] (w.map M.bit)⟩).bind
    ((M.guarded D).run (w.length + 1 + 1)) = _
  rw [scan, Option.bind_some, run]
  have hs : (M.guarded D).step
      ⟨.scan (D.evalFrom D.start w), Tape.mk₂ ((w.map M.bit).reverse ++ []) []⟩ =
      some ⟨.rewind, (Tape.mk₂ ((w.map M.bit).reverse) []).move .left⟩ := by
    simp only [step, TM0.step, guarded, Tape.mk₂, Tape.mk', ListBlank.head_mk,
      List.headI_nil, M.readBit_blank, ite_eq_left ha, Option.map_some, List.append_nil]
  rw [hs, Option.bind_some]
  simpa only [List.length_reverse, List.map_reverse, List.reverse_reverse, List.append_nil,
    liftCfg, TM0.init, Tape.mk₁] using rewind M D w.reverse []

/-- A valid input incurs just the scan-and-rewind overhead. -/
theorem accepted {w output : List Bool} {time : ℕ} (hw : w ∈ D.accepts)
    (h : M.OutputsWithin w output time) :
    (M.guarded D).OutputsWithin w output (2 * w.length + time + 2) := by
  obtain ⟨t, ht, c, hc, hhalt, hout⟩ := h
  refine ⟨2 * w.length + 2 + t, by lia, liftCfg M D c, ?_, ?_, hout⟩
  · rw [run_add]
    change ((M.guarded D).run (2 * w.length + 2)
      ⟨.scan D.start, Tape.mk₁ (w.map M.bit)⟩).bind ((M.guarded D).run t) = _
    rw [prepare M D hw, Option.bind_some, run_lift, hc, Option.map_some]
  · rw [step_lift, hhalt, Option.map_none]

/-- A rejected input halts at the first blank with empty output. -/
theorem rejected {w : List Bool} (hw : w ∉ D.accepts) :
    (M.guarded D).OutputsWithin w [] w.length := by
  have ha : D.evalFrom D.start w ∉ D.accept := hw
  refine ⟨w.length, le_rfl,
    ⟨.scan (D.evalFrom D.start w), Tape.mk₂ ((w.map M.bit).reverse ++ []) []⟩,
    scan M D w [] D.start, ?_, ?_⟩
  · simp only [step, TM0.step, guarded, Tape.mk₂, Tape.mk', ListBlank.head_mk,
      List.headI_nil, M.readBit_blank, ite_eq_right ha, Option.map_none]
  · exact Tape.mk'_right₀ _ _

end Guard
end Complexity.MathlibTM0.BinaryMachine
