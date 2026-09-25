/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Cslib.MultiTape.Internal
import Complexitylib.Models.TuringMachine.Internal
import Mathlib.Data.Int.Interval

/-!
# Space bounds for the CSLib multi-tape simulation

The simulator `TM.toMultiTape` keeps each CSLib work head at the position of
the head it simulates: data and marker tapes follow our work and output heads,
and the overshoot counter sits `h - (|x| + 1)` cells right of position 0 when
our input head is at `h`. The rewind phase only walks the output copy back to
cell 0 and then to cell 1. So when every reachable configuration of `tm`
obeys `Cfg.WithinDecisionSpace` with bound `S`, every CSLib head stays in the
interval `[0, S + 1]`, and the simulator uses at most `(2n + 3) (S + 2)` cells
(`TM.toMultiTape_computesFun_space`).
-/


public section

namespace Complexity

open Turing

namespace MultiTape

variable {k : ℕ} {S Q : Type*} {input : List S}

/-- All work heads of `d` lie in the interval `[0, B]`. -/
@[expose] def PosBound (B : ℕ) (d : Turing.Cfg k S Q input) : Prop :=
  ∀ i, 0 ≤ d.workTapePos i ∧ d.workTapePos i ≤ B

/-- If every work head stays in `[0, B]` for the first `t` steps, the run uses
at most `k (B + 1)` cells. -/
theorem spaceUsed_le_of_posBound (M : MultiTapeTM k S Q) (d : Turing.Cfg k S Q input)
    (t B : ℕ) (h : ∀ m ≤ t, PosBound B (M.runFrom d m)) : M.spaceUsed d t ≤ k * (B + 1) := by
  unfold MultiTapeTM.spaceUsed
  calc ∑ i, M.spaceUsedByTape d t i ≤ ∑ _i : Fin k, (B + 1) :=
        Finset.sum_le_sum fun i _ => by
          unfold MultiTapeTM.spaceUsedByTape MultiTapeTM.visitedByTapeHead
          calc _ ≤ (Finset.Icc (0 : ℤ) B).card := Finset.card_le_card (by
                intro p hp
                simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
                obtain ⟨m, rfl⟩ := hp
                exact Finset.mem_Icc.mpr (h m (by omega) i))
            _ = B + 1 := by simp
    _ = k * (B + 1) := by simp

end MultiTape

namespace TM

open MultiTape

variable {n : ℕ} {tm : TM n}

/-- Every CSLib work tape of the simulator is a data tape, a marker tape, or the
overshoot counter. -/
theorem simIdx_cases (i : Fin (simTapes n)) :
    (∃ j, i = dataIdx j) ∨ (∃ j, i = markIdx j) ∨ i = overIdx := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) a
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr (Or.inl ⟨j, rfl⟩)
  · exact Or.inr (Or.inr (by rw [Fin.fin_one_eq_zero b]; rfl))

/-- Within the decision-space bound `s`, every simulated read-write head is at
most at `s + 1`. -/
theorem simTape_head_le {c : Cfg n tm.Q} {N s : ℕ} (hc : c.WithinDecisionSpace N s)
    (j : Fin (n + 1)) : (simTape c j).head ≤ s + 1 := by
  induction j using Fin.lastCases with
  | last => simpa using hc.2
  | cast j => simpa using (hc.1.1 j).trans (Nat.le_succ s)

/-- A simulated configuration within the decision-space bound `s` keeps every
CSLib head in `[0, s + 1]`. -/
theorem MultiTapeSim.posBound {x : List Bool} {c : Cfg n tm.Q} {z : InputZone}
    {d : tm.SimCfg x} (h : MultiTapeSim tm x c z d) {s : ℕ}
    (hc : c.WithinDecisionSpace x.length s) : PosBound (s + 1) d := by
  intro i
  rcases simIdx_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ | rfl
  · have := simTape_head_le hc j
    rw [(h.tapes j).pos]
    exact ⟨by omega, by exact_mod_cast this⟩
  · have := simTape_head_le hc j
    rw [(h.tapes j).mpos]
    exact ⟨by omega, by exact_mod_cast this⟩
  · have := hc.1.2
    rw [h.overPos]
    exact ⟨by omega, by exact_mod_cast (show c.input.head - (x.length + 1) ≤ s + 1 by omega)⟩

/-- Every prefix of a run of our machine is simulated by the same prefix of the
simulator's run. -/
theorem MultiTapeSim.reachesIn_prefix {x : List Bool} {t : ℕ} {c c' : Cfg n tm.Q}
    (hreach : tm.reachesIn t c c') {z : InputZone} {d : tm.SimCfg x}
    (h : MultiTapeSim tm x c z d) :
    ∀ j ≤ t, ∃ (cj : Cfg n tm.Q) (z' : InputZone),
      tm.reachesIn j c cj ∧ MultiTapeSim tm x cj z' (tm.toMultiTape.runFrom d j) := by
  induction hreach generalizing z d with
  | zero =>
    intro j hj
    obtain rfl : j = 0 := by omega
    exact ⟨_, z, .zero, by simpa [MultiTapeTM.runFrom] using h⟩
  | step hstep _ ih =>
    intro j hj
    rcases j with _ | j
    · exact ⟨_, z, .zero, by simpa [MultiTapeTM.runFrom] using h⟩
    · obtain ⟨z'', h''⟩ := h.step hstep
      obtain ⟨cj, z', hr, hs⟩ := ih h'' j (by omega)
      exact ⟨cj, z', .step hstep hr, by
        rw [MultiTapeTM.runFrom, Function.iterate_succ_apply]
        exact hs⟩

/-- The step leaving the simulation phase moves no head. -/
theorem MultiTapeSim.halt_workTapePos {x : List Bool} {c : Cfg n tm.Q} {z : InputZone}
    {d : tm.SimCfg x} (h : MultiTapeSim tm x c z d) (hc : c.state = tm.qhalt) :
    (tm.toMultiTape.step d).workTapePos = d.workTapePos := by
  rw [step_of_state_eq_some _ h.state]
  funext i
  simp [toMultiTape, toMultiTapeTr, hc]

/-- The verdict step moves no head. -/
theorem AtVerdict.workTapePos_step {x : List Bool} {t : Tape} {d : tm.SimCfg x}
    (h : AtVerdict tm x t d) : (tm.toMultiTape.step d).workTapePos = d.workTapePos := by
  rw [step_of_state_eq_some _ h.state]
  funext i
  simp [toMultiTape, toMultiTapeTr]

/-- A rewind step keeps every CSLib head in `[0, B]` when `1 ≤ B`. -/
theorem Rewinding.posBound_step {x : List Bool} {t : Tape} {d : tm.SimCfg x} {B : ℕ}
    (h : Rewinding tm x t d) (hb : PosBound B d) (hB : 1 ≤ B) :
    PosBound B (tm.toMultiTape.step d) := by
  have hd := hb (dataIdx (Fin.last n))
  have hm := hb (markIdx (Fin.last n))
  rw [h.out.pos] at hd
  rw [h.out.mpos] at hm
  rw [step_of_state_eq_some _ h.state]
  intro i
  by_cases h0 : t.head = 0
  · have hat : d.workTapeSymbols (markIdx (Fin.last n)) = some true :=
      (decide_eq_decide.mp h.out.atStart).2 h0
    rcases simIdx_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ | rfl
    · by_cases hj : j = Fin.last n
      · subst hj
        simp only [toMultiTape, toMultiTapeTr, hat, tapeLayout_dataIdx, ite_true]
        rw [h.out.pos, h0]
        simp only [SignType.coe_one]
        omega
      · simpa [toMultiTape, toMultiTapeTr, hat, hj] using hb (dataIdx j)
    · by_cases hj : j = Fin.last n
      · subst hj
        simp only [toMultiTape, toMultiTapeTr, hat, tapeLayout_markIdx, ite_true]
        rw [h.out.mpos, h0]
        simp only [SignType.coe_one]
        omega
      · simpa [toMultiTape, toMultiTapeTr, hat, hj] using hb (markIdx j)
    · simpa [toMultiTape, toMultiTapeTr] using hb overIdx
  · have hat : d.workTapeSymbols (markIdx (Fin.last n)) ≠ some true := fun h' =>
      h0 ((decide_eq_decide.mp h.out.atStart).1 h')
    rcases simIdx_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ | rfl
    · by_cases hj : j = Fin.last n
      · subst hj
        simp only [toMultiTape, toMultiTapeTr, hat, tapeLayout_dataIdx, ite_true, ite_false]
        rw [h.out.pos]
        simp only [SignType.coe_neg_one]
        omega
      · simpa [toMultiTape, toMultiTapeTr, hat, hj] using hb (dataIdx j)
    · by_cases hj : j = Fin.last n
      · subst hj
        simp only [toMultiTape, toMultiTapeTr, hat, tapeLayout_markIdx, ite_true, ite_false]
        rw [h.out.mpos]
        simp only [SignType.coe_neg_one]
        omega
      · simpa [toMultiTape, toMultiTapeTr, hat, hj] using hb (markIdx j)
    · simpa [toMultiTape, toMultiTapeTr] using hb overIdx

/-- The whole rewind phase from output-head position `m` keeps every CSLib head
in `[0, B]` when `1 ≤ B`. -/
theorem Rewinding.posBound_run {x : List Bool} {B : ℕ} (hB : 1 ≤ B) :
    ∀ (m : ℕ) {t : Tape} {d : tm.SimCfg x}, Rewinding tm x t d → t.head = m →
      PosBound B d → ∀ s ≤ m + 2, PosBound B (tm.toMultiTape.runFrom d s)
  | 0, t, d, h, hm, hb, s, hs => by
    have hv := h.step_of_eq_zero hm
    have hb1 := h.posBound_step hb hB
    rcases s with _ | _ | _ | s
    · simpa [MultiTapeTM.runFrom] using hb
    · simpa [MultiTapeTM.runFrom] using hb1
    · simp only [MultiTapeTM.runFrom, Function.iterate_succ_apply, Function.iterate_zero,
        id_eq]
      intro i
      rw [hv.workTapePos_step]
      exact hb1 i
    · omega
  | m + 1, t, d, h, hm, hb, s, hs => by
    rcases s with _ | s
    · simpa [MultiTapeTM.runFrom] using hb
    · rw [MultiTapeTM.runFrom, Function.iterate_succ_apply, ← MultiTapeTM.runFrom]
      exact Rewinding.posBound_run hB m (h.step_of_ne_zero (by omega))
        (by simp [Tape.move, hm]) (h.posBound_step hb hB) s (by omega)

variable (tm) in
/-- **The simulator decides what `tm` decides, space-faithfully.** If `tm`
decides `L` within time `T` and space `S`, the simulator decides `L` within time
`2 T + 4` and space `(2n + 3) (S + 2)`. -/
theorem toMultiTape_computesFun_space {L : Language} {T S : ℕ → ℕ}
    (hdec : tm.DecidesInTimeSpace L T S) :
    tm.toMultiTape.ComputesFunInTimeAndSpace (Function.Embedding.refl _) verdictEmb
      (MultiTapeTM.indicator L) (fun x => 2 * T x.length + 4)
      (fun x => simTapes n * (S x.length + 2)) := by
  intro x
  obtain ⟨c', t, ht, hreach, hhalt, hyes, hno⟩ := hdec.2 x
  have hp : c'.output.head ≤ t := (head_le_of_reachesIn tm hreach).2.1
  obtain ⟨z, hsim⟩ := (multiTapeSim_init tm x).reachesIn hreach
  have hrun := (hsim.halt hhalt).run c'.output.head rfl
  have hsplit : tm.toMultiTape.runFrom (tm.toMultiTape.initCfg x)
      (1 + t + 1 + (c'.output.head + 2)) =
      tm.toMultiTape.runFrom (tm.toMultiTape.step (tm.toMultiTape.runFrom
        (tm.toMultiTape.step (tm.toMultiTape.initCfg x)) t)) (c'.output.head + 2) := by
    simp only [MultiTapeTM.runFrom]
    have e : ∀ y : tm.SimCfg x, tm.toMultiTape.step y = tm.toMultiTape.step^[1] y :=
      fun _ => rfl
    rw [e (tm.toMultiTape.initCfg x), e (tm.toMultiTape.step^[t] _),
      ← Function.iterate_add_apply, ← Function.iterate_add_apply,
      ← Function.iterate_add_apply]
    congr 1
    omega
  have hspace : ∀ m ≤ 1 + t + 1 + (c'.output.head + 2),
      PosBound (S x.length + 1) (tm.toMultiTape.runFrom (tm.toMultiTape.initCfg x) m) := by
    intro m hm
    rcases m with _ | m
    · intro i
      simp [MultiTapeTM.runFrom, MultiTapeTM.initCfg, Turing.Cfg.init]
      omega
    rw [MultiTapeTM.runFrom, Function.iterate_succ_apply, ← MultiTapeTM.runFrom]
    by_cases hmt : m ≤ t
    · obtain ⟨cj, z', hr, hs⟩ := (multiTapeSim_init tm x).reachesIn_prefix hreach m hmt
      exact hs.posBound (hdec.1 x cj (reaches_of_reachesIn hr))
    · obtain ⟨s, rfl⟩ : ∃ s, m = t + 1 + s := ⟨m - (t + 1), by omega⟩
      have e : tm.toMultiTape.runFrom (tm.toMultiTape.step (tm.toMultiTape.initCfg x))
          (t + 1 + s) = tm.toMultiTape.runFrom (tm.toMultiTape.step (tm.toMultiTape.runFrom
            (tm.toMultiTape.step (tm.toMultiTape.initCfg x)) t)) s := by
        simp only [MultiTapeTM.runFrom]
        rw [add_comm, Function.iterate_add_apply, Function.iterate_succ_apply']
      rw [e]
      have hb := hsim.posBound (hdec.1 x c' (reaches_of_reachesIn hreach))
      refine Rewinding.posBound_run (by omega) c'.output.head (hsim.halt hhalt) rfl
        (fun i => ?_) s (by omega)
      rw [hsim.halt_workTapePos hhalt]
      exact hb i
  refine ⟨1 + t + 1 + (c'.output.head + 2), by dsimp only; omega,
    tm.toMultiTape.spaceUsed (tm.toMultiTape.initCfg x) (1 + t + 1 + (c'.output.head + 2)),
    spaceUsed_le_of_posBound _ _ _ _ hspace, ?_⟩
  change tm.toMultiTape.ComputesInTimeAndSpace x (verdictEmb (MultiTapeTM.indicator L x)) _ _
  refine ⟨by rw [hsplit]; exact hrun.1, ?_, rfl⟩
  rw [hsplit, hrun.2]
  simp only [verdictEmb, MultiTapeTM.indicator]
  by_cases hx : x ∈ L
  · simp [hyes hx, hx]
  · simp [hno hx, hx]

end TM

end Complexity
