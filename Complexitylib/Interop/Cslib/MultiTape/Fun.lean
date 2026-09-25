/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Cslib.MultiTape.Internal
import Complexitylib.Models.TuringMachine.Internal
import Complexitylib.Models.TuringMachine.OutputBounds
import Complexitylib.Interop.Cslib.MultiTape.Space

/-!
# Computing functions on CSLib multi-tape machines

A decider only constrains output cell 1, so the decision simulator
`TM.toMultiTape` emits that single cell. To compute a function, the simulator
`TM.toMultiTapeFun` shares its marking, simulation, and rewind phases, but its
final phase copies output cells `1, 2, …` to CSLib's output until the first
blank cell. Since both machines agree away from that final state, every lemma
about the shared phases transfers (`TM.runFrom_toMultiTapeFun`).

## Main results

- `Complexity.TM.toMultiTapeFun_computesFun` — if `tm` computes `f` within time
  `T`, the simulator computes `f` within time `3 T + 4` and space
  `(2n + 3) (3 T + 5)`
-/


public section

namespace Complexity

open Turing MultiTape

namespace TM

variable {n : ℕ} {tm : TM n}

/-- Away from the final state, the two simulators take the same step. -/
theorem toMultiTapeFun_step_eq {x : List Bool} {d : tm.SimCfg x}
    (h : d.state ≠ some .verdict) : tm.toMultiTapeFun.step d = tm.toMultiTape.step d := by
  unfold MultiTapeTM.step
  split
  · rfl
  · rename_i q hq
    cases q with
    | verdict => exact absurd hq h
    | _ => rfl

/-- Runs that avoid the final state agree on the two simulators. -/
theorem runFrom_toMultiTapeFun {x : List Bool} (d : tm.SimCfg x) (m : ℕ)
    (h : ∀ j < m, (tm.toMultiTape.runFrom d j).state ≠ some .verdict) :
    tm.toMultiTapeFun.runFrom d m = tm.toMultiTape.runFrom d m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have e := toMultiTapeFun_step_eq (h m (by omega))
    rw [MultiTapeTM.runFrom, MultiTapeTM.runFrom, Function.iterate_succ_apply',
      Function.iterate_succ_apply', ← MultiTapeTM.runFrom, ← MultiTapeTM.runFrom,
      ih (fun j hj => h j (by omega)), e]

/-- The rewind phase from output-head position `m` stays in the rewind state for
`m + 1` configurations and then reaches the final state. -/
theorem Rewinding.toVerdict {x : List Bool} :
    ∀ (m : ℕ) {t : Tape} {d : tm.SimCfg x}, Rewinding tm x t d → t.head = m →
      (∀ s ≤ m, (tm.toMultiTape.runFrom d s).state = some .rewind) ∧
      ∃ t' : Tape, t'.cells = t.cells ∧ AtVerdict tm x t' (tm.toMultiTape.runFrom d (m + 1))
  | 0, t, d, h, hm => by
    refine ⟨fun s hs => ?_, _, Tape.move_cells t .right, ?_⟩
    · obtain rfl : s = 0 := by omega
      simpa [MultiTapeTM.runFrom] using h.state
    · simpa [MultiTapeTM.runFrom] using h.step_of_eq_zero hm
  | m + 1, t, d, h, hm => by
    obtain ⟨hs, t', ht', hv⟩ :=
      Rewinding.toVerdict m (h.step_of_ne_zero (by omega)) (by simp [Tape.move, hm])
    refine ⟨fun s hsm => ?_, t', by rw [ht', Tape.move_cells], ?_⟩
    · rcases s with _ | s
      · simpa [MultiTapeTM.runFrom] using h.state
      · rw [MultiTapeTM.runFrom, Function.iterate_succ_apply, ← MultiTapeTM.runFrom]
        exact hs s (by omega)
    · rw [MultiTapeTM.runFrom, Function.iterate_succ_apply, ← MultiTapeTM.runFrom]
      exact hv

variable (tm) in
/-- The function simulator is copying its simulated output tape `t` to CSLib's
output, having emitted `pre` so far. -/
structure Dumping (x : List Bool) (t : Tape) (pre : List Bool) (d : tm.SimCfg x) : Prop where
  state : d.state = some .verdict
  out : TapeSim t (d.workTapePos (dataIdx (Fin.last n))) (d.workTapePos (markIdx (Fin.last n)))
    (d.workTapes (dataIdx (Fin.last n))) (d.workTapes (markIdx (Fin.last n)))
  head : 1 ≤ t.head
  output : d.output = pre

/-- The data cell under the simulated output head holds the output cell there. -/
theorem Dumping.ofCell {x : List Bool} {t : Tape} {pre : List Bool} {d : tm.SimCfg x}
    (h : Dumping tm x t pre d) :
    Γ.ofCell (d.workTapeSymbols (dataIdx (Fin.last n))) = t.cells t.head := by
  have := h.out.cells t.head h.head
  rw [← h.out.pos] at this
  exact this

/-- Copying a non-blank output cell. -/
theorem Dumping.step_some {x : List Bool} {t : Tape} {pre : List Bool} {d : tm.SimCfg x}
    (h : Dumping tm x t pre d) {b : Bool} (hb : t.cells t.head = Γ.ofBool b) :
    Dumping tm x (t.move .right) (pre ++ [b]) (tm.toMultiTapeFun.step d) := by
  have hsym : d.workTapeSymbols (dataIdx (Fin.last n)) = some b := by
    have := h.ofCell
    rw [hb] at this
    revert this
    cases d.workTapeSymbols (dataIdx (Fin.last n)) with
    | none => cases b <;> simp [Γ.ofCell, Γ.ofBool]
    | some c => cases b <;> cases c <;> simp [Γ.ofCell, Γ.ofBool]
  rw [step_of_state_eq_some _ h.state]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [toMultiTapeFun, toMultiTapeFunTr, hsym]
  · simpa [toMultiTapeFun, toMultiTapeFunTr, applyWrite, Dir3.toSign] using
      h.out.move .right (by simp)
  · simp [Tape.move]
  · simp [toMultiTapeFun, toMultiTapeFunTr, hsym, h.output]

/-- Halting at the first blank output cell. -/
theorem Dumping.step_none {x : List Bool} {t : Tape} {pre : List Bool} {d : tm.SimCfg x}
    (h : Dumping tm x t pre d) (hb : t.cells t.head = Γ.blank) :
    (tm.toMultiTapeFun.step d).state = none ∧ (tm.toMultiTapeFun.step d).output = pre := by
  have hsym : d.workTapeSymbols (dataIdx (Fin.last n)) = none := by
    have := h.ofCell
    rw [hb] at this
    revert this
    cases d.workTapeSymbols (dataIdx (Fin.last n)) with
    | none => simp
    | some c => cases c <;> simp [Γ.ofCell, Γ.ofBool]
  rw [step_of_state_eq_some _ h.state]
  exact ⟨by simp [toMultiTapeFun, toMultiTapeFunTr, hsym],
    by simp [toMultiTapeFun, toMultiTapeFunTr, hsym, h.output]⟩

/-- The copy phase emits the output string `y` found from the head onward and
halts after `|y| + 1` steps. -/
theorem Dumping.run {x : List Bool} :
    ∀ (y : List Bool) {t : Tape} {pre : List Bool} {d : tm.SimCfg x},
      Dumping tm x t pre d →
      (∀ (i : ℕ) (hi : i < y.length), t.cells (t.head + i) = Γ.ofBool y[i]) →
      t.cells (t.head + y.length) = Γ.blank →
      (tm.toMultiTapeFun.runFrom d (y.length + 1)).state = none ∧
      (tm.toMultiTapeFun.runFrom d (y.length + 1)).output = pre ++ y
  | [], t, pre, d, h, _, hb => by
    simp only [List.length_nil, Nat.add_zero, zero_add, List.append_nil] at hb ⊢
    simpa [MultiTapeTM.runFrom] using h.step_none hb
  | b :: y, t, pre, d, h, hy, hb => by
    have h1 := h.step_some (b := b) (hy 0 (by simp))
    have := Dumping.run y h1
      (fun i hi => by
        rw [Tape.move_cells, show (t.move .right).head + i = t.head + (i + 1) by
          simp [Tape.move]; omega]
        exact hy (i + 1) (by simp; omega))
      (by
        rw [Tape.move_cells, show (t.move .right).head + y.length = t.head + (b :: y).length by
          simp [Tape.move]; omega]
        exact hb)
    rw [show (b :: y).length + 1 = (y.length + 1) + 1 by simp, MultiTapeTM.runFrom,
      Function.iterate_succ_apply, ← MultiTapeTM.runFrom]
    simpa using this

variable (tm) in
/-- **The function simulator computes what `tm` computes**, within time
`3 T + 4` and space `(2n + 3) (3 T + 5)` when `tm` computes within time `T`. -/
theorem toMultiTapeFun_computesFun {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hf : tm.ComputesInTime f T) :
    tm.toMultiTapeFun.ComputesFunInTimeAndSpace (Function.Embedding.refl _)
      (Function.Embedding.refl _) f (fun x => 3 * T x.length + 4)
      (fun x => simTapes n * (3 * T x.length + 5)) := by
  intro x
  obtain ⟨c', t, ht, hreach, hhalt, hout⟩ := hf x
  have hp : c'.output.head ≤ t := (head_le_of_reachesIn tm hreach).2.1
  have hlen : (f x).length ≤ t := output_length_le_of_reachesIn hreach hout
  obtain ⟨z, hsim⟩ := (multiTapeSim_init tm x).reachesIn hreach
  obtain ⟨hrw, t', ht', hv⟩ := (hsim.halt hhalt).toVerdict c'.output.head rfl
  have hsplit : ∀ s, tm.toMultiTape.runFrom (tm.toMultiTape.initCfg x) (1 + t + 1 + s) =
      tm.toMultiTape.runFrom (tm.toMultiTape.step (tm.toMultiTape.runFrom
        (tm.toMultiTape.step (tm.toMultiTape.initCfg x)) t)) s := by
    intro s
    simp only [MultiTapeTM.runFrom]
    have e : ∀ y : tm.SimCfg x, tm.toMultiTape.step y = tm.toMultiTape.step^[1] y :=
      fun _ => rfl
    rw [e (tm.toMultiTape.initCfg x), e (tm.toMultiTape.step^[t] _),
      ← Function.iterate_add_apply, ← Function.iterate_add_apply,
      ← Function.iterate_add_apply]
    congr 1
    omega
  have hagree : tm.toMultiTapeFun.runFrom (tm.toMultiTape.initCfg x)
      (1 + t + 1 + (c'.output.head + 1)) =
      tm.toMultiTape.runFrom (tm.toMultiTape.initCfg x) (1 + t + 1 + (c'.output.head + 1)) := by
    apply runFrom_toMultiTapeFun
    intro j hj
    rcases j with _ | j
    · simp [MultiTapeTM.runFrom, MultiTapeTM.initCfg, Turing.Cfg.init, toMultiTape]
    by_cases hjt : j ≤ t
    · obtain ⟨cj, z', -, hs⟩ := (multiTapeSim_init tm x).reachesIn_prefix hreach j hjt
      rw [MultiTapeTM.runFrom, Function.iterate_succ_apply, ← MultiTapeTM.runFrom, hs.state]
      simp
    · obtain ⟨s, hs⟩ : ∃ s, j + 1 = 1 + t + 1 + s := ⟨j - t - 1, by omega⟩
      rw [hs, hsplit, hrw s (by omega)]
      simp
  have hdump := Dumping.run (f x) (d := tm.toMultiTape.runFrom (tm.toMultiTape.step
      (tm.toMultiTape.runFrom (tm.toMultiTape.step (tm.toMultiTape.initCfg x)) t))
      (c'.output.head + 1)) (pre := [])
    ⟨hv.state, hv.out, by rw [hv.head], hv.output⟩
    (fun i hi => by rw [hv.head, ht', add_comm]; exact hout.1 i hi)
    (by rw [hv.head, ht', add_comm]; exact hout.2)
  rw [← hsplit, ← hagree] at hdump
  have htot : tm.toMultiTapeFun.runFrom (tm.toMultiTapeFun.initCfg x)
      (1 + t + 1 + (c'.output.head + 1) + ((f x).length + 1)) =
      tm.toMultiTapeFun.runFrom (tm.toMultiTapeFun.runFrom (tm.toMultiTape.initCfg x)
        (1 + t + 1 + (c'.output.head + 1))) ((f x).length + 1) := by
    simp only [MultiTapeTM.runFrom]
    rw [add_comm, Function.iterate_add_apply]
    rfl
  refine ⟨1 + t + 1 + (c'.output.head + 1) + ((f x).length + 1), by dsimp only; omega,
    tm.toMultiTapeFun.spaceUsed (tm.toMultiTapeFun.initCfg x)
      (1 + t + 1 + (c'.output.head + 1) + ((f x).length + 1)),
    (MultiTape.spaceUsed_le _ _ _).trans (Nat.mul_le_mul_left (simTapes n) (by omega)), ?_⟩
  change tm.toMultiTapeFun.ComputesInTimeAndSpace x (f x) _ _
  exact ⟨by rw [htot]; exact hdump.1, by rw [htot, hdump.2]; rfl, rfl⟩

end TM

end Complexity
