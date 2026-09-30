/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Witness.Defs

/-!
# Online witness equivalence: proof internals

The existing guess-tape simulation identifies the visible endpoints of witness
runs with NTM traces at each exact clock. Halting, acceptance, and prefix-space
bounds then transfer without changing either resource bound.
-/

public section

namespace Complexity

namespace WitnessTM

variable {k : ℕ}

private theorem traceD_dropChoice_congr_prefix (W : WitnessTM k) :
    ∀ (t : ℕ) (c d : Cfg (k + 1) W.machine.Q),
      (c.work (Fin.last k)).BoolFrom t → (d.work (Fin.last k)).BoolFrom t →
      NTM.dropChoice c = NTM.dropChoice d →
      (∀ j < t,
        (c.work (Fin.last k)).cells ((c.work (Fin.last k)).head + j) =
          (d.work (Fin.last k)).cells ((d.work (Fin.last k)).head + j)) →
      NTM.dropChoice (W.machine.traceD t c) =
        NTM.dropChoice (W.machine.traceD t d) := by
  intro t
  induction t with
  | zero => intro c d _ _ hvis _; exact hvis
  | succ t ih =>
    intro c d hc hd hvis hcells
    have hstate : c.state = d.state := congrArg (fun e : Cfg k W.machine.Q => e.state) hvis
    by_cases hhalt : c.state = W.machine.qhalt
    · rw [TM.traceD_of_halted W.machine _ hhalt,
        TM.traceD_of_halted W.machine _ (hstate.symm.trans hhalt)]
      exact hvis
    · have dhalt : d.state ≠ W.machine.qhalt := fun h => hhalt (hstate.trans h)
      obtain ⟨b, hb⟩ := hc.read
      have hread : (c.work (Fin.last k)).read = (d.work (Fin.last k)).read := by
        simpa [Tape.read] using hcells 0 (Nat.zero_lt_succ t)
      have db : (d.work (Fin.last k)).read = Γ.ofBool b := hread.symm.trans hb
      have hwc := NTM.work_last_stepCfg' W.machine W.protocol c hhalt hc.read_ne_start
      have hwd := NTM.work_last_stepCfg' W.machine W.protocol d dhalt hd.read_ne_start
      rw [TM.traceD_succ_of_not_halted W.machine t hhalt,
        TM.traceD_succ_of_not_halted W.machine t dhalt]
      apply ih _ _
        (NTM.boolFrom_stepCfg W.machine W.protocol hhalt hc)
        (NTM.boolFrom_stepCfg W.machine W.protocol dhalt hd)
      · rw [NTM.dropChoice_stepCfg W.machine hb, NTM.dropChoice_stepCfg W.machine db]
        exact congrArg (fun e : Cfg k W.machine.Q =>
          (NTM.ofGuess W.machine).stepCfg b e) hvis
      · intro j hj
        rw [hwc, hwd, ← hstate]
        cases ha : W.advancing c.state
        · simpa [ha, Tape.move] using hcells j (by omega)
        · simpa [ha, Tape.move, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hcells (j + 1) (by omega)

/-- The visible result of a bounded witness run depends only on the corresponding
finite Boolean prefix. Unread witness tails need not agree. -/
theorem run_congr_prefix_internal (W : WitnessTM k) (x : List Bool) (t : ℕ)
    (g h : ℕ → Bool) (hprefix : ∀ i < t, g i = h i) :
    NTM.dropChoice (W.run x g t) = NTM.dropChoice (W.run x h t) := by
  apply traceD_dropChoice_congr_prefix W t
  · simpa using NTM.loadTape_boolFrom g t
  · simpa using NTM.loadTape_boolFrom h t
  · rw [NTM.dropChoice_loadCfg, NTM.dropChoice_loadCfg]
  · intro j hj
    simp only [NTM.loadCfg_work_last, NTM.loadTape_head]
    rw [Nat.add_comm 1 j, NTM.loadTape_cells_succ, NTM.loadTape_cells_succ, hprefix j hj]


theorem exists_run_eq_trace_internal (W : WitnessTM k) (x : List Bool) (t : ℕ)
    (choices : Fin t → Bool) :
    ∃ g, NTM.dropChoice (W.run x g t) = W.toNTM.trace t choices (W.toNTM.initCfg x) := by
  obtain ⟨g, c, s, hs, hr, hstop, heq⟩ :=
    NTM.exists_loadTape W.machine W.protocol x t choices
  refine ⟨g, ?_⟩
  have hrun : W.run x g t = c := by
    rcases Nat.lt_or_eq_of_le hs with hlt | rfl
    · exact TM.traceD_of_reachesIn_halted W.machine hs hr (hstop hlt)
    · exact TM.traceD_of_reachesIn W.machine s hr
  rw [hrun]
  exact heq

theorem exists_trace_eq_run_internal (W : WitnessTM k) (x : List Bool) (t : ℕ)
    (g : ℕ → Bool) :
    ∃ choices, W.toNTM.trace t choices (W.toNTM.initCfg x) =
      NTM.dropChoice (W.run x g t) := by
  refine ⟨fun i => NTM.guessBit W.machine (NTM.loadCfg W.machine x g) i.val, ?_⟩
  have h := NTM.dropChoice_traceD W.machine W.protocol t (NTM.loadCfg W.machine x g)
    (by simpa using NTM.loadTape_boolFrom g t)
  have hinit := NTM.dropChoice_loadCfg W.machine x g
  exact (congrArg (fun c => W.toNTM.trace t _ c) hinit).symm.trans h.symm

theorem exists_run_iff_internal (W : WitnessTM k) (x : List Bool) (t : ℕ)
    (P : Cfg k W.machine.Q → Prop) :
    (∃ g, P (NTM.dropChoice (W.run x g t))) ↔
      ∃ choices, P (W.toNTM.trace t choices (W.toNTM.initCfg x)) := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨choices, heq⟩ := exists_trace_eq_run_internal W x t g
    exact ⟨choices, heq.symm ▸ hg⟩
  · rintro ⟨choices, hc⟩
    obtain ⟨g, heq⟩ := exists_run_eq_trace_internal W x t choices
    exact ⟨g, heq.symm ▸ hc⟩

theorem forall_run_iff_internal (W : WitnessTM k) (x : List Bool) (t : ℕ)
    (P : Cfg k W.machine.Q → Prop) :
    (∀ g, P (NTM.dropChoice (W.run x g t))) ↔
      ∀ choices, P (W.toNTM.trace t choices (W.toNTM.initCfg x)) := by
  constructor
  · intro h choices
    obtain ⟨g, heq⟩ := exists_run_eq_trace_internal W x t choices
    exact heq ▸ h g
  · intro h g
    obtain ⟨choices, heq⟩ := exists_trace_eq_run_internal W x t g
    exact heq ▸ h choices

theorem decidesInTime_iff_internal (W : WitnessTM k) (L : Language) (T : ℕ → ℕ) :
    W.DecidesInTime L T ↔ W.toNTM.DecidesInTime L T := by
  have hh : W.AllWitnessesHaltIn T ↔ W.toNTM.AllPathsHaltIn T := by
    exact forall_congr' fun x => forall_run_iff_internal W x (T x.length)
      (fun c => c.state = W.machine.qhalt)
  have ha : ∀ x, W.AcceptsInTime x (T x.length) ↔
      W.toNTM.AcceptsInTime x (T x.length) := fun x =>
    exists_run_iff_internal W x (T x.length)
      (fun c => c.state = W.machine.qhalt ∧ c.output.cells 1 = Γ.one)
  exact and_congr hh (forall_congr' fun x => iff_congr Iff.rfl (ha x))

theorem decidesInTimeSpace_iff_internal (W : WitnessTM k) (L : Language) (T S : ℕ → ℕ) :
    W.DecidesInTimeSpace L T S ↔ W.toNTM.DecidesInTimeSpace L T S := by
  refine and_congr (decidesInTime_iff_internal W L T) ?_
  constructor
  · intro h x choices t ht
    obtain ⟨g, heq⟩ := exists_run_eq_trace_internal W x t
      (fun j => choices ⟨j.val, by omega⟩)
    exact heq ▸ h x g t ht
  · intro h x g t ht
    obtain ⟨choices, heq⟩ := exists_trace_eq_run_internal W x t g
    let full : Fin (T x.length) → Bool := fun i =>
      if hi : i.val < t then choices ⟨i.val, hi⟩ else false
    have hprefix : (fun j : Fin t => full ⟨j.val, by omega⟩) = choices := by
      funext j
      simp [full, j.isLt]
    have hp := h x full t ht
    rw [hprefix, heq] at hp
    exact hp

end WitnessTM

namespace NTM

theorem toNTM_toWitnessTM_internal (N : NTM k) : N.toWitnessTM.toNTM = N := by
  cases N
  simp only [WitnessTM.toNTM, toWitnessTM, ofGuess, choiceTM]
  congr 1
  funext b q i w o
  cases b <;> simp [Γ.ofBool]

end NTM

end Complexity
