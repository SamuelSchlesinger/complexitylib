/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PHBodyWindow
public import Complexitylib.Classes.Containments.Internal.PHLoop

/-!
# The enumerator's loop, in space

⚠️ Unreviewed by Bolton

The loop runs exponentially many iterations, so no bound derived from its total running time can
be polynomial. What is polynomial is one iteration, and every state the loop returns to has all
its heads at cell one — that is what `TM.loopTM_keepsWindowOn_phases` turns into a window for the
whole run.

## Main results

- `PolyExists.enumTest_keepsWindowOn` — the test's window, straight from its running time
-/

@[expose] public section

namespace Complexity

namespace PolyExists

variable {k : ℕ}

/-- **The loop's test keeps a window.** Unlike the body, the test is short: its window is read
off its running time. -/
theorem enumTest_keepsWindowOn {L' : Language} (k : ℕ) (x : List Bool) (N H v : ℕ) (I : Tape)
    (hI : TM.Parked I) (hIz : I.cells 0 = Γ.start) (hIhead : I.head = 1) (B G : ℕ)
    (hB : 1 + 1 + TM.binaryEqTime (v + 1).bits N.bits ≤ B) (hG1 : 1 ≤ G) :
    (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)).KeepsWindowOn
      (fun c => c.state = (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)).qstart ∧
        (c.input = I ∧
          c.work = enumBank k x N H (v + 1) (NTM.tally (enumP L' x) (v + 1))
            (NTM.tally (fun u => !enumP L' x u) (v + 1)) ∧
          c.output = TM.blankTape))
      x.length (G + testTime B N v) :=
  TM.keepsWindowOn_of_hoareTime (h₀ := G)
    (enumTest_hoareTime (L' := L') k x N H v I hI hIz B hB)
    (fun inp work out hpre i => by
      rw [hpre.2.1]
      exact enumBank_head_le k x N H (v + 1) _ _ G hG1 i)
    (fun inp work out hpre => by rw [hpre.1, hIhead]; omega)
    (fun inp work out hpre => by
      rw [hpre.2.2]
      show (1 : ℕ) ≤ G + 1
      omega)

open Classical in
/-- The tapes the loop's body is entered on: the counting state at some count below the
horizon. -/
noncomputable def loopPB (L' : Language) (k : ℕ) (x : List Bool) (N H : ℕ) (I : Tape) :
    TM.TapePred (enumTapes k) := fun inp work out =>
  ∃ j, j < N ∧ NTM.tallyPre (cIdx k) (aIdx k) (rIdx k) I (enumRest k x N H (j + 1))
    (enumP L' x) j inp work out

open Classical in
/-- The tapes the loop's test is entered on: what one pass leaves. -/
noncomputable def loopPT (L' : Language) (k : ℕ) (x : List Bool) (N H : ℕ) (I : Tape) :
    TM.TapePred (enumTapes k) := fun inp work out =>
  ∃ j, j < N ∧ inp = I ∧
    work = enumBank k x N H (j + 1) (NTM.tally (enumP L' x) (j + 1))
      (NTM.tally (fun u => !enumP L' x u) (j + 1)) ∧ out = TM.blankTape

open Classical in
/-- The tapes of the rewind-and-check phases: the same bank, with the verdict slot's head on its
way back to cell one. -/
noncomputable def loopPL (L' : Language) (k : ℕ) (x : List Bool) (N H : ℕ) (I : Tape) :
    TM.LoopPhase → TM.TapePred (enumTapes k) := fun ph inp work out =>
  ∃ j, j ≤ N ∧ inp = I ∧
    work = enumBank k x N H j (NTM.tally (enumP L' x) j) (NTM.tally (fun u => !enumP L' x u) j) ∧
    out.cells = (NTM.outSlot (if j = N then Γw.one else Γw.zero)).cells ∧
    (if ph = TM.LoopPhase.check then out.head = 1 else out.head ≤ 1)

/-- **Leaving the body.** When the pass halts, the tapes are the ones the test is entered on. -/
theorem loop_hBT (M : TM k) {L' : Language} {T S : ℕ → ℕ} (hdec : M.DecidesInTime L' T)
    (hdecS : M.DecidesInSpace L' S) (x : List Bool) (N H : ℕ) (I : Tape) (hI : TM.Parked I)
    (hIsi : Tape.StartInvariant I) (hIhead : I.head = 1) (hIz : I.cells 0 = Γ.start)
    (B Hb : ℕ) (hB1 : 1 ≤ B) (hHb1 : 1 ≤ Hb) (hHbH : Hb + 1 ≤ H)
    (hpair : ∀ j, j < N → 1 + TM.pairInputWorkTime x (dropTop (j + 1)) ≤ B)
    (hspace : ∀ j, j < N → (pair x (dropTop (j + 1))).length +
      S (pair x (dropTop (j + 1))).length + 2 ≤ Hb)
    (hlenH : ∀ j, j < N → (pair x (dropTop (j + 1))).length + 1 ≤ H) :
    ∀ (c c' : Cfg (enumTapes k)
        (TM.loopTM (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).Q),
      c.state = Sum.inl (bodyTM M).qhalt →
      (∃ d : Cfg (enumTapes k) (bodyTM M).Q, d.state = (bodyTM M).qstart ∧
        loopPB L' k x N H I d.input d.work d.output ∧
        (bodyTM M).reaches d ⟨(bodyTM M).qhalt, c.input, c.work, c.output⟩) →
      (TM.loopTM (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).step c = some c' →
      TM.LoopTapeInv (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))
        (loopPB L' k x N H I) (loopPT L' k x N H I) (loopPL L' k x N H I) c' := by
  rintro c c' hstate ⟨d, hd0, ⟨j, hj, hpre⟩, hreach⟩ hstep
  have hbody := enumBody_hoareTime M hdec hdecS x N H j I hI hIsi hIhead hIz B Hb
    (hpair j hj) hB1 hHb1 (hspace j hj) hHbH (hlenH j hj)
  obtain ⟨e, t, -, hreachE, hhaltE, hpostE⟩ := hbody d.input d.work d.output hpre
  have hd : (⟨(bodyTM M).qstart, d.input, d.work, d.output⟩ :
      Cfg (enumTapes k) (bodyTM M).Q) = d := Cfg.ext hd0.symm rfl rfl rfl
  rw [hd] at hreachE
  obtain ⟨s, hreachS⟩ := TM.reaches_to_reachesIn _ hreach
  have hhalt2 : (bodyTM M).halted
      (⟨(bodyTM M).qhalt, c.input, c.work, c.output⟩ : Cfg (enumTapes k) (bodyTM M).Q) := rfl
  have heq := TM.reachesIn_halted_unique hreachE hreachS hhaltE hhalt2
  rw [heq] at hpostE
  obtain ⟨hi, hw, ho⟩ := hpostE
  have hc : c = TM.loopBodyWrap (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))
      ⟨(bodyTM M).qhalt, c.input, c.work, c.output⟩ := Cfg.ext hstate rfl rfl rfl
  rw [hc, TM.loopTM_body_to_test (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))
    rfl] at hstep
  rw [← Option.some_inj.mp hstep]
  refine ⟨fun hcon => absurd hcon (by nofun), fun _ => ⟨j, hj, ?_, ?_, ?_⟩,
    fun ph hph => absurd hph (by nofun)⟩
  · show TM.transitionInput c.input = I
    rw [hi]
    exact TM.transitionInput_eq_self hI.read_ne_start
  · show (fun i => TM.transitionTape (c.work i)) = _
    rw [hw]
    exact funext fun i => TM.transitionTape_eq_self
      (enumBank_parked k x N H (j + 1) _ _ i).read_ne_start
  · show TM.transitionTape c.output = TM.blankTape
    rw [ho]
    exact TM.transitionTape_eq_self TM.blankTape_parked.read_ne_start

/-- **Leaving the test.** Its verdict sits in the slot, and the loop begins rewinding it. -/
theorem loop_hTL (M : TM k) {L' : Language} (x : List Bool) (N H : ℕ) (I : Tape)
    (hI : TM.Parked I) (hIz : I.cells 0 = Γ.start) (B : ℕ)
    (hB : ∀ j, j < N → 1 + 1 + TM.binaryEqTime (j + 1).bits N.bits ≤ B) :
    ∀ (c c' : Cfg (enumTapes k)
        (TM.loopTM (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).Q),
      c.state = Sum.inr (Sum.inr (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)).qhalt) →
      (∃ d : Cfg (enumTapes k) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)).Q,
        d.state = (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)).qstart ∧
        loopPT L' k x N H I d.input d.work d.output ∧
        (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)).reaches d
          ⟨(TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)).qhalt, c.input, c.work, c.output⟩) →
      (TM.loopTM (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).step c = some c' →
      TM.LoopTapeInv (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))
        (loopPB L' k x N H I) (loopPT L' k x N H I) (loopPL L' k x N H I) c' := by
  rintro c c' hstate ⟨d, hd0, ⟨j, hj, hi, hw, ho⟩, hreach⟩ hstep
  have htest := enumTest_hoareTime (L' := L') k x N H j I hI hIz B (hB j hj)
  obtain ⟨e, t, -, hreachE, hhaltE, hpostE⟩ := htest d.input d.work d.output ⟨hi, hw, ho⟩
  have hd : (⟨(TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)).qstart, d.input, d.work, d.output⟩ :
      Cfg (enumTapes k) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)).Q) = d :=
    Cfg.ext hd0.symm rfl rfl rfl
  rw [hd] at hreachE
  obtain ⟨s, hreachS⟩ := TM.reaches_to_reachesIn _ hreach
  have hhalt2 : (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)).halted
      (⟨(TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)).qhalt, c.input, c.work, c.output⟩ :
        Cfg (enumTapes k) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)).Q) := rfl
  have heq := TM.reachesIn_halted_unique hreachE hreachS hhaltE hhalt2
  rw [heq] at hpostE
  obtain ⟨hi', hw', ho'⟩ := hpostE
  have hc : c = TM.loopTestWrap (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))
      ⟨(TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)).qhalt, c.input, c.work, c.output⟩ :=
    Cfg.ext hstate rfl rfl rfl
  rw [hc, TM.loopTM_test_to_rewind (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))
    rfl] at hstep
  rw [← Option.some_inj.mp hstep]
  refine ⟨fun hcon => absurd hcon (by nofun), fun hcon => absurd hcon (by nofun),
    fun ph hph => Or.inr ?_⟩
  have hph' : ph = TM.LoopPhase.rewindOut := by
    injection hph with h
    injection h with h'
    exact h'.symm
  refine ⟨j + 1, by omega, ?_, ?_, ?_, ?_⟩
  · show TM.transitionInput c.input = I
    rw [hi']
    exact TM.transitionInput_eq_self hI.read_ne_start
  · show (fun i => TM.transitionTape (c.work i)) = _
    rw [hw']
    exact funext fun i => TM.transitionTape_eq_self
      (enumBank_parked k x N H (j + 1) _ _ i).read_ne_start
  · show (TM.transitionTape c.output).cells = _
    rw [ho', TM.transitionTape_eq_self (NTM.outSlot_parked _).read_ne_start]
  · rw [hph']
    show (TM.transitionTape c.output).head ≤ 1
    rw [ho', TM.transitionTape_eq_self (NTM.outSlot_parked _).read_ne_start]
    exact le_of_eq rfl

theorem outSlot_cells_startInvariant (s : Γw) (t : Tape)
    (hcells : t.cells = (NTM.outSlot s).cells) : Tape.StartInvariant t := by
  rw [Tape.StartInvariant, hcells]
  exact ⟨rfl, fun j hj => (NTM.outSlot_parked s).2 j hj⟩

/-- **The bookkeeping phases.** The rewind moves only the output head; the check either halts the
loop or starts the next pass on the very same tapes. -/
theorem loop_hLL (M : TM k) {L' : Language} (x : List Bool) (N H : ℕ) (I : Tape)
    (hI : TM.Parked I) :
    ∀ (c c' : Cfg (enumTapes k)
        (TM.loopTM (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).Q)
      (ph : TM.LoopPhase),
      c.state = Sum.inr (Sum.inl ph) → loopPL L' k x N H I ph c.input c.work c.output →
      (TM.loopTM (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).step c = some c' →
      TM.LoopTapeInv (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))
        (loopPB L' k x N H I) (loopPT L' k x N H I) (loopPL L' k x N H I) c' := by
  rintro c c' ph hstate ⟨j, hjN, hi, hw, hcells, hhead⟩ hstep
  have hoSI : Tape.StartInvariant c.output := outSlot_cells_startInvariant _ c.output hcells
  have hwP : ∀ i, TM.Parked (c.work i) := by
    rw [hw]
    exact enumBank_parked k x N H j _ _
  have hIp : TM.Parked c.input := by rw [hi]; exact hI
  cases ph with
  | done =>
      exact absurd hstep (by
        simp only [TM.step, show c.state = (TM.loopTM (bodyTM M)
          (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).qhalt from hstate, ↓reduceIte]
        nofun)
  | rewindOut =>
      rw [ite_eq_right (by nofun : ¬ (TM.LoopPhase.rewindOut = TM.LoopPhase.check))] at hhead
      obtain ⟨hin', hwork', hcells', hhead'⟩ :=
        TM.loop_phase_step_tapes (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))
          hstate (by nofun) hoSI hstep
      obtain ⟨hto, hstay⟩ := TM.loop_rewind_step_state (bodyTM M)
        (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)) hstate hstep
      have hbase : c'.input = I ∧ c'.work = enumBank k x N H j
          (NTM.tally (enumP L' x) j) (NTM.tally (fun u => !enumP L' x u) j) ∧
          c'.output.cells = (NTM.outSlot (if j = N then Γw.one else Γw.zero)).cells := by
        refine ⟨?_, ?_, by rw [hcells', hcells]⟩
        · rw [hin', hi]
          exact TM.transitionInput_eq_self hI.read_ne_start
        · funext i
          rw [hwork' i, hw]
          exact TM.transitionTape_eq_self (enumBank_parked k x N H j _ _ i).read_ne_start
      refine ⟨fun hcon => ?_, fun hcon => ?_, fun ph' hph' => Or.inr ?_⟩
      · by_cases hread : c.output.read = Γ.start
        · rw [(hto hread).1] at hcon
          exact absurd hcon (by nofun)
        · rw [hstay hread] at hcon
          exact absurd hcon (by nofun)
      · by_cases hread : c.output.read = Γ.start
        · rw [(hto hread).1] at hcon
          exact absurd hcon (by nofun)
        · rw [hstay hread] at hcon
          exact absurd hcon (by nofun)
      · refine ⟨j, hjN, hbase.1, hbase.2.1, hbase.2.2, ?_⟩
        by_cases hread : c.output.read = Γ.start
        · have hph2 : ph' = TM.LoopPhase.check := by
            rw [(hto hread).1] at hph'
            injection hph' with h
            injection h with h'
            exact h'.symm
          rw [hph2]
          show c'.output.head = 1
          have hhead0 : c.output.head = 0 := by
            by_contra hc0
            exact absurd hread (hoSI.2 c.output.head (by omega))
          have hh := (hto hread).2
          omega
        · have hph2 : ph' = TM.LoopPhase.rewindOut := by
            rw [hstay hread] at hph'
            injection hph' with h
            injection h with h'
            exact h'.symm
          rw [hph2]
          show c'.output.head ≤ 1
          have := hhead'
          omega
  | check =>
      rw [ite_eq_left rfl] at hhead
      have hhead1 : c.output.head = 1 := hhead
      have hread : c.output.read ≠ Γ.start := by
        show c.output.cells c.output.head ≠ Γ.start
        rw [hhead1, hcells]
        exact (NTM.outSlot_parked _).2 1 (by omega)
      obtain ⟨hin', hwork', hout'⟩ :=
        TM.loop_check_step_tapes (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))
          hstate hread hstep
      have hbase : c'.input = I ∧ c'.work = enumBank k x N H j
          (NTM.tally (enumP L' x) j) (NTM.tally (fun u => !enumP L' x u) j) ∧
          c'.output = c.output := by
        refine ⟨?_, ?_, hout'⟩
        · rw [hin', hi]
          exact TM.transitionInput_eq_self hI.read_ne_start
        · funext i
          rw [hwork' i, hw]
          exact TM.transitionTape_eq_self (enumBank_parked k x N H j _ _ i).read_ne_start
      by_cases hone : c.output.cells 1 = Γ.one
      · obtain ⟨d, hd, hdstate, -⟩ := TM.loopTM_check_halt (bodyTM M)
          (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)) c hstate hhead1 hone
        rw [hd] at hstep
        have hc'eq : c' = d := Option.some_inj.mp hstep.symm
        refine ⟨fun hcon => absurd (hc'eq ▸ hcon) (by rw [hdstate]; nofun),
          fun hcon => absurd (hc'eq ▸ hcon) (by rw [hdstate]; nofun), fun ph' hph' => Or.inl ?_⟩
        rw [hc'eq, hdstate] at hph'
        injection hph' with h
        injection h with h'
        exact h'.symm
      · have hnostart : ∀ i, i ≥ 1 → c.output.cells i ≠ Γ.start := by
          intro i hi'
          rw [hcells]
          exact (NTM.outSlot_parked _).2 i hi'
        obtain ⟨d, hd, hdstate, -⟩ := TM.loopTM_check_continue (bodyTM M)
          (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)) c hstate hhead1 hone hnostart
        rw [hd] at hstep
        have hc'eq : c' = d := Option.some_inj.mp hstep.symm
        have hjN' : j ≠ N := by
          intro hjeq
          rw [hjeq, ite_eq_left rfl] at hcells
          exact hone (by rw [hcells]; rfl)
        refine ⟨fun _ => ⟨j, by omega, hbase.1, hbase.2.1,
            ⟨if j = N then Γw.one else Γw.zero, by rw [ite_eq_right hjN']; nofun, ?_⟩⟩,
          fun hcon => absurd (hc'eq ▸ hcon) (by rw [hdstate]; nofun),
          fun ph' hph' => absurd (hc'eq ▸ hph') (by rw [hdstate]; nofun)⟩
        rw [hbase.2.2]
        exact Tape.ext hhead1 hcells

/-- **The enumerator's loop keeps a window.** The loop runs exponentially many iterations; what
bounds its space is one iteration's width, and the fact that every state it returns to has all
its heads at cell one. -/
theorem enumLoop_keepsWindowOn (M : TM k) {L' : Language} {T S : ℕ → ℕ}
    (hdec : M.DecidesInTime L' T) (hdecS : M.DecidesInSpace L' S) (hne : M.qstart ≠ M.qhalt)
    (x : List Bool) (N H : ℕ) (hN : 1 ≤ N) (I : Tape) (hI : TM.Parked I)
    (hIsi : Tape.StartInvariant I) (hIhead : I.head = 1) (hIz : I.cells 0 = Γ.start)
    (B Hb G W : ℕ) (hB1 : 1 ≤ B) (hHb1 : 1 ≤ Hb) (hHbH : Hb + 1 ≤ H)
    (hpair : ∀ j, j < N → 1 + TM.pairInputWorkTime x (dropTop (j + 1)) ≤ B)
    (hspace : ∀ j, j < N → (pair x (dropTop (j + 1))).length +
      S (pair x (dropTop (j + 1))).length + 2 ≤ Hb)
    (hlenH : ∀ j, j < N → (pair x (dropTop (j + 1))).length + 1 ≤ H)
    (heqB : ∀ j, j < N → 1 + 1 + TM.binaryEqTime (j + 1).bits N.bits ≤ B)
    (hG1 : 1 ≤ G) (hGB : B ≤ G) (hGHb : Hb + 1 ≤ G)
    (hGpair : ∀ j, j < N → (pair x (dropTop (j + 1))).length + 1 ≤ G)
    (hW1 : G + 1 ≤ W)
    (hW2 : ∀ j, j < N → G + TM.pairInputWorkTime x (dropTop (j + 1)) ≤ W)
    (hW3 : G + (1 + 1 + (2 * (max (B + 2) (3 * (B + 3) + 1) + 1) + 1)) ≤ W)
    (hW4 : ∀ j, j < N → G + (2 * (pair x (dropTop (j + 1))).length + 5) ≤ W)
    (hW6 : G + (1 + 1 + (2 * (max (Hb + 2) (1 * (Hb + 3) + 1) + 1) + 1)) ≤ W)
    (hW8 : ∀ j, j < N → G + (3 * (max (1 + 1 +
      max (TM.binarySuccTime (NTM.tally (enumP L' x) j))
        (TM.binarySuccTime (NTM.tally (fun u => !enumP L' x u) j)) + 5)
      (TM.binarySuccTime j) + 1) + 1) ≤ W)
    (hW9 : ∀ j, j < N → G + TM.binaryBumpTime (dropTop (j + 1)) ≤ W)
    (hW10 : G + ((scratchTargets k).length * (H + 4) + H * 4 + 8 + 1 +
      ((scratchTargets k).length * (H + 4) + 1)) ≤ W)
    (hWtest : ∀ j, j < N → G + testTime B N j ≤ W) :
    ∀ inp work out,
      NTM.tallyPre (cIdx k) (aIdx k) (rIdx k) I (enumRest k x N H 1) (enumP L' x) 0
        inp work out →
      ∀ c, (TM.loopTM (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).reaches
        ⟨(TM.loopTM (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).qstart,
          inp, work, out⟩ c →
        c.WithinDecisionSpace x.length W := by
  intro inp work out hpre c hreach
  have hs : 1 ≤ W := by omega
  have hbodyW : (bodyTM M).KeepsWindowOn
      (fun d => d.state = (bodyTM M).qstart ∧ loopPB L' k x N H I d.input d.work d.output)
      x.length W := by
    intro d hd D hD
    obtain ⟨j, hj, hpj⟩ := hd.2
    exact bodyTM_keepsWindowOn M hdec hdecS hne x N H j (NTM.tally (enumP L' x) j)
      (NTM.tally (fun u => !enumP L' x u) j) I hI hIsi hIhead hIz B Hb G W (hpair j hj) hB1
      hHb1 (hspace j hj) hHbH (hlenH j hj) (enumP L' x j) (enumP_iff L' x j) hG1 hGB hGHb
      (hGpair j hj) hW1 (hW2 j hj) hW3 (hW4 j hj) hW6 (hW8 j hj) (hW9 j hj) hW10
      d ⟨hd.1, hpj.1, hpj.2.1, hpj.2.2⟩ D hD
  have htestW : (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)).KeepsWindowOn
      (fun d => d.state = (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)).qstart ∧
        loopPT L' k x N H I d.input d.work d.output) x.length W := by
    intro d hd D hD
    obtain ⟨j, hj, hpj⟩ := hd.2
    exact ((enumTest_keepsWindowOn (L' := L') k x N H j I hI hIz hIhead B G (heqB j hj)
      hG1).mono_space (hWtest j hj)) d ⟨hd.1, hpj.1, hpj.2.1, hpj.2.2⟩ D hD
  refine TM.loopTM_keepsWindowOn_phases (bodyTM M)
    (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)) hs
    (loopPB L' k x N H I) (loopPT L' k x N H I) (loopPL L' k x N H I) hbodyW htestW
    (loop_hBT M hdec hdecS x N H I hI hIsi hIhead hIz B Hb hB1 hHb1 hHbH hpair hspace hlenH)
    (loop_hTL M x N H I hI hIz B heqB)
    (loop_hLL M x N H I hI)
    ⟨(TM.loopTM (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).qstart, inp, work, out⟩
    rfl ⟨0, hN, hpre⟩ ?_ ?_ c hreach
  · obtain ⟨hi, hw, sy, -, ho⟩ := hpre
    exact ⟨⟨fun i => by
        rw [hw]
        show (enumBank k x N H 0 _ _ i).head ≤ W
        rw [enumBank_head]
        omega,
      by rw [hi, hIhead]; omega⟩, by rw [ho]; show (1 : ℕ) ≤ W + 1; omega⟩
  · obtain ⟨hi, hw, sy, -, ho⟩ := hpre
    exact ⟨by rw [hi]; exact hIsi,
      fun i => by
        rw [hw]
        exact enumBank_startInvariant k x N H 0 _ _ i,
      by
        rw [ho]
        exact ⟨rfl, fun j hj => (NTM.outSlot_parked sy).2 j hj⟩⟩

end PolyExists

end Complexity
