/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.NP.Internal.PairBuildTM
public import Complexitylib.Models.TuringMachine.Subroutines.Internal

/-!
# `pairSelfTM`: build `pair x x` from input `x`

The input-preparation prefix of the time-hierarchy diagonalizer `D : TM 8`.
Starting from the fresh initial configuration on input `x`, it builds the
self-pair `pair x x` onto work tape `7` and leaves every other tape clean:

- input tape: cells unchanged, head parked at cell `1`;
- work tapes `≠ 7`: exactly the started blank tape `(Tape.init []).move right`;
- work tape `7`: exactly the started pair tape
  `(Tape.init ((pair x x).map Γ.ofBool)).move right`;
- output tape: blank cells, head parked at cell `1`.

Tape layout of `D`: tapes `0`–`5` are the UTM's six tapes, `6` is the clock,
`7` holds the pair.

## Phase structure

```
copyInputToWorkTM 0    copy x onto work tape 0
rewindWorkTM 0         rewind work tape 0 to cell 1
rewindInputTM          rewind the input head to cell 1
pairBuildTM 0 7        build pair x x on work tape 7 (x from input, y from tape 0)
rewindInputTM          re-park the input head at cell 1
rewindWorkTM 0         rewind work tape 0 (still holding x) to cell 1
clearWorkTM 0          erase work tape 0 back to the started blank tape
```

## Main results

- `pairSelfTM` — the machine
- `pairSelfTime` — its running-time bound, `23·n + 58`
- `pairSelfTM_hoareTime` — the Hoare specification described above
- `pairSelfTime_le` — the clean quadratic bound `pairSelfTime n ≤ 58·(n+1)²`
-/

@[expose] public section

namespace Complexity

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Definition
-- ════════════════════════════════════════════════════════════════════════

/-- Build `pair x x` (the input paired with itself) on work tape `7`,
    leaving all other tapes clean: input and output heads parked at cell `1`,
    work tapes `≠ 7` as started blank tapes. -/
def pairSelfTM : TM 8 :=
  seqTM (copyInputToWorkTM (0 : Fin 8))
    (seqTM (rewindWorkTM (0 : Fin 8))
      (seqTM rewindInputTM
        (seqTM (pairBuildTM (0 : Fin 8) (7 : Fin 8))
          (seqTM rewindInputTM
            (seqTM (rewindWorkTM (0 : Fin 8))
              (clearWorkTM (0 : Fin 8)))))))

/-- Running-time bound for `pairSelfTM` on inputs of length `n`: the sum of
    the seven phase bounds plus the six `seqTM` seam steps. -/
def pairSelfTime (n : ℕ) : ℕ :=
  23 * n + 58

-- ════════════════════════════════════════════════════════════════════════
-- Small tape helpers
-- ════════════════════════════════════════════════════════════════════════

/-- The started blank tape reads `□`. -/
private theorem blankStarted_read :
    ((Tape.init []).move Dir3.right).read = Γ.blank := by
  exact Tape.init_nil_move_right_read

/-- A started `ofBool` data tape never reads `▷`. -/
private theorem started_read_ne_start (l : List Bool) :
    ((Tape.init (l.map Γ.ofBool)).move Dir3.right).read ≠ Γ.start := by
  exact Tape.init_ofBool_move_right_read_ne_start l

/-- The started blank tape never reads `▷`. -/
private theorem blankStarted_read_ne_start :
    ((Tape.init []).move Dir3.right).read ≠ Γ.start := by
  rw [blankStarted_read]; decide

/-- A tape whose cells agree with an `Tape.init` of `ofBool` data and whose
    head is right of `▷` never reads `▷`. -/
private theorem read_ne_start_of_cells_initTape {t : Tape} {x : List Bool}
    (hc : t.cells = (Tape.init (x.map Γ.ofBool)).cells) (hh : t.head ≥ 1) :
    t.read ≠ Γ.start := by
  show t.cells t.head ≠ Γ.start
  rw [hc]
  exact Tape.init_ofBool_cells_ne_start x _ hh

/-- Binary-prefix cell clauses rule out `▷` right of the marker. -/
private theorem cells_ne_start_of_bits {t : Tape} {x : List Bool}
    (hbits : ∀ i, (h : i < x.length) → t.cells (i + 1) = Γ.ofBool (x[i]'h))
    (htail : ∀ i, x.length ≤ i → t.cells (i + 1) = Γ.blank) :
    ∀ j, j ≥ 1 → t.cells j ≠ Γ.start := by
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  by_cases hilt : i < x.length
  · rw [hbits i hilt]; cases x[i] <;> simp [Γ.ofBool]
  · rw [htail i (by omega)]; decide

/-- `transitionInput` moves the head at most one cell to the right. -/
private theorem transitionInput_head_le (t : Tape) :
    (transitionInput t).head ≤ t.head + 1 := by
  unfold transitionInput
  cases idleDir t.read
  · simp only [Tape.move]; omega
  · simp only [Tape.move]; omega
  · simp only [Tape.move]; omega

/-- Writing `□` under a head that reads `□` and idling is a no-op. -/
private theorem write_blank_idle_of_read_blank {t : Tape} (h : t.read = Γ.blank) :
    t.writeAndMove Γ.blank (idleDir t.read) = t := by
  have hd : idleDir t.read = Dir3.stay := by rw [h]; rfl
  rw [hd]
  show (t.write Γ.blank).move Dir3.stay = t
  simp only [Tape.move]
  unfold Tape.write
  split
  · rfl
  · rw [← h]
    show { t with cells := Function.update t.cells t.head (t.cells t.head) } = t
    rw [Function.update_eq_self]

/-- A read-back write followed by a right move preserves cells and bumps
    the head by one. -/
private theorem writeAndMove_readBack_right (t : Tape) (hread : t.read ≠ Γ.start) :
    (t.writeAndMove (readBackWrite t.read) Dir3.right).cells = t.cells ∧
    (t.writeAndMove (readBackWrite t.read) Dir3.right).head = t.head + 1 := by
  constructor
  · exact tape_readBackWrite_preserves t Dir3.right (Or.inr hread)
  · show ((t.write _).move Dir3.right).head = t.head + 1
    simp [Tape.move, Tape.write_head]

/-- Cell `0` of any work tape is never modified by a TM step. -/
private theorem writeAndMove_cells_zero (t : Tape) (s : Γ) (d : Dir3) :
    (t.writeAndMove s d).cells 0 = t.cells 0 := by
  show ((t.write s).move d).cells 0 = t.cells 0
  rw [Tape.move_cells]
  unfold Tape.write
  split
  · rfl
  · exact Function.update_of_ne (by omega) _ _

/-- Cell `0` of any work tape is preserved along any run of any TM. -/
private theorem reachesIn_work_cells_zero {m : ℕ} {tm : TM m} :
    ∀ {t : ℕ} {c c' : Cfg m tm.Q}, tm.reachesIn t c c' →
      ∀ i, (c'.work i).cells 0 = (c.work i).cells 0 := by
  intro t c c' h
  induction h with
  | zero => exact fun _ => rfl
  | step hstep _ ih =>
    intro i
    rename_i c₀ c₁ _ _ _
    have h1 : (c₁.work i).cells 0 = (c₀.work i).cells 0 := by
      have hq := state_ne_qhalt_of_step hstep
      simp only [TM.step, hq, ↓reduceIte, Option.some.injEq] at hstep
      subst hstep
      exact writeAndMove_cells_zero ..
    rw [ih i, h1]

-- ════════════════════════════════════════════════════════════════════════
-- Phase 1: `copyInputToWorkTM 0` from the fresh initial configuration
-- ════════════════════════════════════════════════════════════════════════

/-- The first step of `copyInputToWorkTM` from the fresh initial configuration
    moves every tape from `▷` to cell `1`. -/
private theorem copy_fresh_step (x : List Bool) :
    (copyInputToWorkTM (0 : Fin 8)).step
      { state := CopyPhase.copying,
        input := Tape.init (x.map Γ.ofBool),
        work := fun _ => Tape.init [],
        output := Tape.init [] } =
    some { state := CopyPhase.copying,
           input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
           work := fun _ => (Tape.init []).move Dir3.right,
           output := (Tape.init []).move Dir3.right } := by
  simp [TM.step, copyInputToWorkTM, Tape.read, Tape.init, Tape.writeAndMove,
        Tape.write, idleDir]

/-- Any `copyInputToWorkTM 0` step preserves a non-target work tape that
    reads `□`. -/
private theorem copy_step_frame_work {c c' : Cfg 8 (copyInputToWorkTM (0 : Fin 8)).Q}
    (hstep : (copyInputToWorkTM (0 : Fin 8)).step c = some c')
    (i : Fin 8) (hi : i ≠ 0) (hread : (c.work i).read = Γ.blank) :
    c'.work i = c.work i := by
  have hq := state_ne_qhalt_of_step hstep
  simp only [TM.step, hq, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  dsimp only []
  cases hstate : c.state with
  | done => exact absurd hstate hq
  | copying =>
    by_cases hin : c.input.read = Γ.blank
    · simp only [copyInputToWorkTM, hin, ↓reduceIte, allIdle]
      exact write_blank_idle_of_read_blank hread
    · simp only [copyInputToWorkTM, hin, ↓reduceIte, hi, Γw.toΓ]
      exact write_blank_idle_of_read_blank hread

/-- Any `copyInputToWorkTM 0` step preserves the output tape when it
    reads `□`. -/
private theorem copy_step_frame_out {c c' : Cfg 8 (copyInputToWorkTM (0 : Fin 8)).Q}
    (hstep : (copyInputToWorkTM (0 : Fin 8)).step c = some c')
    (hread : c.output.read = Γ.blank) :
    c'.output = c.output := by
  have hq := state_ne_qhalt_of_step hstep
  simp only [TM.step, hq, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  dsimp only []
  cases hstate : c.state with
  | done => exact absurd hstate hq
  | copying =>
    by_cases hin : c.input.read = Γ.blank
    · simp only [copyInputToWorkTM, hin, ↓reduceIte, allIdle]
      exact write_blank_idle_of_read_blank hread
    · simp only [copyInputToWorkTM, hin, ↓reduceIte, Γw.toΓ]
      exact write_blank_idle_of_read_blank hread

private theorem copy_reachesIn_frame_work
    {t : ℕ} {c c' : Cfg 8 (copyInputToWorkTM (0 : Fin 8)).Q}
    (h : (copyInputToWorkTM (0 : Fin 8)).reachesIn t c c') :
    ∀ i : Fin 8, i ≠ 0 → (c.work i).read = Γ.blank → c'.work i = c.work i := by
  induction h with
  | zero => exact fun _ _ _ => rfl
  | step hstep _ ih =>
    intro i hi hread
    have h1 := copy_step_frame_work hstep i hi hread
    rw [ih i hi (by rw [h1]; exact hread), h1]

private theorem copy_reachesIn_frame_out
    {t : ℕ} {c c' : Cfg 8 (copyInputToWorkTM (0 : Fin 8)).Q}
    (h : (copyInputToWorkTM (0 : Fin 8)).reachesIn t c c')
    (hread : c.output.read = Γ.blank) : c'.output = c.output := by
  induction h with
  | zero => rfl
  | step hstep _ ih =>
    have h1 := copy_step_frame_out hstep hread
    rw [ih (by rw [h1]; exact hread), h1]

/-- Fresh-start Hoare specification for `copyInputToWorkTM 0`, with framing
    of all untouched tapes. -/
private theorem copyInput_fresh_hoareTime (x : List Bool) :
    (copyInputToWorkTM (0 : Fin 8)).HoareTime
      (fun inp work out =>
        inp = Tape.init (x.map Γ.ofBool) ∧
        (∀ i : Fin 8, work i = Tape.init []) ∧
        out = Tape.init [])
      (fun inp work out =>
        inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        inp.head = x.length + 1 ∧
        (work 0).cells 0 = Γ.start ∧
        (work 0).HasBinaryPrefix x ∧
        (∀ i : Fin 8, i ≠ 0 → work i = (Tape.init []).move Dir3.right) ∧
        out = (Tape.init []).move Dir3.right)
      (x.length + 2) := by
  intro inp work out ⟨hinp, hwork, hout⟩
  have hwork' : work = fun _ => Tape.init [] := funext hwork
  subst hinp hout hwork'
  obtain ⟨c₂, t, ht, hreach, hhalt, hcells, hhead, hprefix⟩ :=
    copyInputToWorkTM_started_hoareTime (0 : Fin 8) x
      ((Tape.init (x.map Γ.ofBool)).move Dir3.right)
      (fun _ => (Tape.init []).move Dir3.right)
      ((Tape.init []).move Dir3.right)
      ⟨rfl, Tape.init_nil_move_right_hasBinaryPrefix_nil⟩
  have hreach' : (copyInputToWorkTM (0 : Fin 8)).reachesIn (t + 1)
      { state := CopyPhase.copying,
        input := Tape.init (x.map Γ.ofBool),
        work := fun _ => Tape.init [],
        output := Tape.init [] } c₂ :=
    .step (copy_fresh_step x) hreach
  refine ⟨c₂, t + 1, by omega, hreach', hhalt, hcells, hhead, ?_, hprefix, ?_, ?_⟩
  · rw [reachesIn_work_cells_zero hreach 0]
    rfl
  · intro i hi
    rw [copy_reachesIn_frame_work hreach i hi blankStarted_read]
  · exact copy_reachesIn_frame_out hreach blankStarted_read

-- ════════════════════════════════════════════════════════════════════════
-- Phase 4: `pairBuildTM 0 7` with framing of all tapes
-- ════════════════════════════════════════════════════════════════════════

/-- Any `pairBuildTM 0 7` step preserves the `y` tape's cells and never moves
    its head left, as long as it reads `≠ ▷`. -/
private theorem pairBuild_step_ytape
    {c c' : Cfg 8 (pairBuildTM (0 : Fin 8) (7 : Fin 8)).Q}
    (hstep : (pairBuildTM (0 : Fin 8) (7 : Fin 8)).step c = some c')
    (hread : (c.work 0).read ≠ Γ.start) :
    (c'.work 0).cells = (c.work 0).cells ∧
    ((c'.work 0).head = (c.work 0).head ∨
     (c'.work 0).head = (c.work 0).head + 1) := by
  have hq := state_ne_qhalt_of_step hstep
  simp only [TM.step, hq, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  dsimp only []
  have h07 : ¬ ((0 : Fin 8) = (7 : Fin 8)) := by decide
  have hidle : (c.work 0).writeAndMove (readBackWrite (c.work 0).read).toΓ
      (idleDir (c.work 0).read) = c.work 0 :=
    by simpa [transitionTape] using
      (transitionTape_eq_self (t := c.work 0) hread)
  obtain ⟨hrc, hrh⟩ := writeAndMove_readBack_right (c.work 0) hread
  cases hstate : c.state with
  | done => exact absurd hstate hq
  | init =>
    simp only [pairBuildTM]
    rw [hidle]; exact ⟨rfl, Or.inl rfl⟩
  | copyX1 =>
    by_cases hin : c.input.read = Γ.blank
    · simp only [pairBuildTM, hin, ↓reduceIte]
      rw [hidle]; exact ⟨rfl, Or.inl rfl⟩
    · simp only [pairBuildTM, hin, ↓reduceIte, h07]
      rw [hidle]; exact ⟨rfl, Or.inl rfl⟩
  | copyX2 =>
    simp only [pairBuildTM, h07, ↓reduceIte]
    rw [hidle]; exact ⟨rfl, Or.inl rfl⟩
  | writeSep1 =>
    simp only [pairBuildTM, h07, ↓reduceIte]
    rw [hidle]; exact ⟨rfl, Or.inl rfl⟩
  | writeSep2 =>
    simp only [pairBuildTM, h07, ↓reduceIte]
    rw [hidle]; exact ⟨rfl, Or.inl rfl⟩
  | copyY =>
    by_cases hy : (c.work 0).read = Γ.blank
    · rw [hy] at hidle
      simp only [pairBuildTM, hy, ↓reduceIte]
      rw [hidle]; exact ⟨rfl, Or.inl rfl⟩
    · simp only [pairBuildTM, hy, ↓reduceIte, h07]
      exact ⟨hrc, Or.inr hrh⟩
  | rewindP1 =>
    by_cases hp : (c.work 7).read = Γ.start
    · simp only [pairBuildTM, hp, ↓reduceIte, h07]
      rw [hidle]; exact ⟨rfl, Or.inl rfl⟩
    · simp only [pairBuildTM, hp, ↓reduceIte, h07]
      rw [hidle]; exact ⟨rfl, Or.inl rfl⟩
  | rewindP2 =>
    simp only [pairBuildTM]
    rw [hidle]; exact ⟨rfl, Or.inl rfl⟩

/-- Along any `pairBuildTM 0 7` run, the `y` tape keeps its cells, its head
    stays right of `▷`, and the head advances at most one cell per step. -/
private theorem pairBuild_reachesIn_ytape
    {t : ℕ} {c c' : Cfg 8 (pairBuildTM (0 : Fin 8) (7 : Fin 8)).Q}
    (h : (pairBuildTM (0 : Fin 8) (7 : Fin 8)).reachesIn t c c') :
    (∀ j, j ≥ 1 → (c.work 0).cells j ≠ Γ.start) →
    (c.work 0).head ≥ 1 →
    (c'.work 0).cells = (c.work 0).cells ∧
    (c'.work 0).head ≥ 1 ∧ (c'.work 0).head ≤ (c.work 0).head + t := by
  induction h with
  | zero => exact fun _ hh => ⟨rfl, hh, by omega⟩
  | step hstep _ ih =>
    intro hns hh
    rename_i c₀ c₁ _ _ _
    have hread : (c₀.work 0).read ≠ Γ.start := by
      simp only [Tape.read]; exact hns _ hh
    obtain ⟨hcells, hhd⟩ := pairBuild_step_ytape hstep hread
    obtain ⟨hc2, hh2, hb2⟩ := ih
      (by intro j hj; rw [hcells]; exact hns j hj)
      (by cases hhd <;> omega)
    exact ⟨hc2.trans hcells, hh2, by cases hhd <;> omega⟩

/-- Rich Hoare specification for `pairBuildTM 0 7` on the concrete tape layout
    used by `pairSelfTM`: builds the pair on tape `7` and frames or bounds
    every other tape. -/
private theorem pairBuild_rich_hoareTime (x : List Bool) :
    (pairBuildTM (0 : Fin 8) (7 : Fin 8)).HoareTime
      (fun inp work out =>
        inp = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
        work 0 = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
        work 7 = (Tape.init []).move Dir3.right ∧
        (∀ i : Fin 8, i ≠ 0 → i ≠ 7 →
          work i = (Tape.init []).move Dir3.right) ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        inp.head ≤ 6 * x.length + 11 ∧
        (work 0).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        (work 0).head ≥ 1 ∧ (work 0).head ≤ 6 * x.length + 11 ∧
        work 7 = (Tape.init ((pair x x).map Γ.ofBool)).move Dir3.right ∧
        (∀ i : Fin 8, i ≠ 0 → i ≠ 7 →
          work i = (Tape.init []).move Dir3.right) ∧
        out = (Tape.init []).move Dir3.right)
      (6 * x.length + 10) := by
  intro inp work out ⟨hinp, hw0, hw7, hother, hout⟩
  obtain ⟨c', t, ht, hreach, hhalt, hpair⟩ :=
    pairBuildTM_hoareTime_all_started_initTape_move_right (0 : Fin 8) (7 : Fin 8)
      (by decide) x x inp work out ⟨hinp, hw0, hw7⟩
  have htime : pairBuildTime x.length x.length = 6 * x.length + 10 := by
    unfold pairBuildTime; omega
  have hbridge :=
    (pairBuildTM (0 : Fin 8) (7 : Fin 8)).toNTM_trace_of_reachesIn
      hreach hhalt ht (fun _ => false)
  -- output tape is framed exactly
  have hout_eq : c'.output = out := by
    have h := pairBuildTM_trace_preserves_output (0 : Fin 8) (7 : Fin 8)
      (pairBuildTime x.length x.length) (fun _ => false)
      { state := (pairBuildTM (0 : Fin 8) (7 : Fin 8)).qstart,
        input := inp, work := work, output := out }
      (by show out.read ≠ Γ.start
          rw [hout, blankStarted_read]; decide)
    rw [hbridge] at h
    exact h
  -- work tapes other than 0 and 7 are framed exactly
  have hother_eq : ∀ i : Fin 8, i ≠ 0 → i ≠ 7 → c'.work i = work i := by
    intro i hi0 hi7
    have h := pairBuildTM_trace_preserves_other_work (0 : Fin 8) (7 : Fin 8) i
      (pairBuildTime x.length x.length) (fun _ => false)
      { state := (pairBuildTM (0 : Fin 8) (7 : Fin 8)).qstart,
        input := inp, work := work, output := out }
      hi0 hi7
      (by show (work i).read ≠ Γ.start
          rw [hother i hi0 hi7, blankStarted_read]; decide)
    rw [hbridge] at h
    exact h
  -- input cells are preserved
  have hinp_cells : c'.input.cells = (Tape.init (x.map Γ.ofBool)).cells := by
    have h : c'.input.cells = inp.cells := by
      rw [← hbridge]
      exact NTM.input_cells_trace _ _ _ _
    rw [h, hinp]
    exact Tape.move_cells _ _
  -- input head is bounded
  have hinp_head : c'.input.head ≤ 6 * x.length + 11 := by
    have h : c'.input.head ≤ inp.head + pairBuildTime x.length x.length := by
      rw [← hbridge]
      exact NTM.input_head_trace_le _ _ _ _
    have hh1 : inp.head = 1 := by rw [hinp]; rfl
    omega
  -- the y tape keeps its cells and its head stays right of ▷, boundedly
  have hy := pairBuild_reachesIn_ytape hreach
    (by show ∀ j, j ≥ 1 → (work 0).cells j ≠ Γ.start
        intro j hj
        rw [hw0, Tape.move_cells]
        exact Tape.init_ofBool_cells_ne_start x j hj)
    (by show (work 0).head ≥ 1
        rw [hw0]; exact le_refl 1)
  obtain ⟨hy_cells, hy_head1, hy_head_le⟩ := hy
  have hw0_head : (work 0).head = 1 := by rw [hw0]; rfl
  refine ⟨c', t, by omega, hreach, hhalt, hinp_cells, hinp_head, ?_, hy_head1,
    ?_, hpair, ?_, hout_eq ▸ hout⟩
  · rw [hy_cells]
    show (work 0).cells = _
    rw [hw0]
    exact Tape.move_cells _ _
  · have : (c'.work 0).head ≤ (work 0).head + t := hy_head_le
    omega
  · intro i hi0 hi7
    rw [hother_eq i hi0 hi7]
    exact hother i hi0 hi7

-- ════════════════════════════════════════════════════════════════════════
-- Main theorem
-- ════════════════════════════════════════════════════════════════════════

/-- **Input preparation for the diagonalizer.** Starting from the fresh
    initial configuration on input `x`, `pairSelfTM` halts within
    `pairSelfTime |x|` steps with `pair x x` started on work tape `7`, all
    other work tapes as started blank tapes, and the input and output heads
    parked at cell `1` with unchanged cells. -/
theorem pairSelfTM_hoareTime (x : List Bool) :
    pairSelfTM.HoareTime
      (fun inp work out =>
        inp = Tape.init (x.map Γ.ofBool) ∧
        (∀ i : Fin 8, work i = Tape.init []) ∧
        out = Tape.init [])
      (fun inp work out =>
        inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ inp.head = 1 ∧
        (∀ i : Fin 8, i ≠ 7 →
          work i = (Tape.init []).move Dir3.right) ∧
        work 7 = (Tape.init ((pair x x).map Γ.ofBool)).move Dir3.right ∧
        out.cells = (Tape.init []).cells ∧ out.head = 1)
      (pairSelfTime x.length) := by
  -- Phase 7: clear work tape 0 (holding x) back to the started blank tape.
  have h7 := clearWorkTM_hoareTime_frame_of_binaryString (0 : Fin 8) x
    (P := fun inp work out =>
      inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ inp.head = 1 ∧
      work 7 = (Tape.init ((pair x x).map Γ.ofBool)).move Dir3.right ∧
      (∀ i : Fin 8, i ≠ 0 → i ≠ 7 →
        work i = (Tape.init []).move Dir3.right) ∧
      out = (Tape.init []).move Dir3.right)
    (by
      intro inp work out inp' work' out' hP _hclear hinp hout' hother
      obtain ⟨p1, p2, p3, p4, p5⟩ := hP
      subst hinp hout'
      exact ⟨p1, p2, by rw [hother 7 (by decide)]; exact p3,
        fun i hi0 hi7 => by rw [hother i hi0]; exact p4 i hi0 hi7, p5⟩)
  -- Phase 6: rewind work tape 0 to cell 1.
  have h6 := rewindWorkTM_hoareTime_frame (0 : Fin 8) (6 * x.length + 13)
    (P := fun inp work out =>
      inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ inp.head = 1 ∧
      (work 0).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
      work 7 = (Tape.init ((pair x x).map Γ.ofBool)).move Dir3.right ∧
      (∀ i : Fin 8, i ≠ 0 → i ≠ 7 →
        work i = (Tape.init []).move Dir3.right) ∧
      out = (Tape.init []).move Dir3.right)
    (by
      intro inp work out inp' work' out' hP hcells _hhead hother hinp houtc houth
      obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hP
      subst hinp
      have hout_eq : out' = out := Tape.ext houth houtc
      subst hout_eq
      exact ⟨p1, p2, by rw [hcells]; exact p3,
        by rw [hother 7 (by decide)]; exact p4,
        fun i hi0 hi7 => by rw [hother i hi0]; exact p5 i hi0 hi7, p6⟩)
  -- Seam 6→7: the cleared tape layout re-enters `clearWorkTM`'s precondition.
  have h67 := seqTM_hoareTime (rewindWorkTM (0 : Fin 8)) (clearWorkTM (0 : Fin 8)) h6
    (by
      rintro inp work out ⟨hw0h, hic, hih, hw0c, hw7, hother, hout⟩
      dsimp only []
      have hi_ne : inp.read ≠ Γ.start :=
        read_ne_start_of_cells_initTape hic (by omega)
      have hw0_ne : (work 0).read ≠ Γ.start :=
        read_ne_start_of_cells_initTape hw0c (by omega)
      have hw7_ne : (work 7).read ≠ Γ.start := by
        rw [hw7]; exact started_read_ne_start _
      have hworkRead : ∀ i, (work i).read ≠ Γ.start := by
        intro i
        by_cases hi0 : i = 0
        · subst hi0; exact hw0_ne
        · by_cases hi7 : i = 7
          · subst hi7; exact hw7_ne
          · rw [hother i hi0 hi7]
            exact blankStarted_read_ne_start
      have hout_ne : out.read ≠ Γ.start := by
        rw [hout]; exact blankStarted_read_ne_start
      obtain ⟨hinputEq, hworkEq, houtputEq⟩ :=
        phaseTransition_eq_self_of_reads_ne_start hi_ne hworkRead hout_ne
      rw [hinputEq, houtputEq]
      simp_rw [congrFun hworkEq]
      refine ⟨Tape.ext (by rw [hw0h]; rfl) hw0c, hi_ne, hout_ne, ?_, ?_, ?_⟩
      · rw [hout]; exact le_refl 1
      · intro i hi0
        refine ⟨hworkRead i, ?_⟩
        by_cases hi7 : i = 7
        · subst hi7
          rw [hw7]; exact le_refl 1
        · rw [hother i hi0 hi7]; exact le_refl 1
      · exact ⟨hic, hih, hw7, hother, hout⟩)
    h7
  -- Phase 5: rewind the input head to cell 1.
  have h5 := rewindInputTM_hoareTime_frame (n := 8) (6 * x.length + 12)
    (P := fun inp work out =>
      inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
      (work 0).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
      (work 0).head ≥ 1 ∧ (work 0).head ≤ 6 * x.length + 12 ∧
      work 7 = (Tape.init ((pair x x).map Γ.ofBool)).move Dir3.right ∧
      (∀ i : Fin 8, i ≠ 0 → i ≠ 7 →
        work i = (Tape.init []).move Dir3.right) ∧
      out = (Tape.init []).move Dir3.right)
    (by
      intro inp work out inp' work' out' hP hcells _hhead hwork hout'
      obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hP
      subst hwork hout'
      exact ⟨by rw [hcells]; exact p1, p2, p3, p4, p5, p6, p7⟩)
  -- Seam 5→6: enter the rewind of work tape 0.
  have h567 := seqTM_hoareTime rewindInputTM _ h5
    (by
      rintro inp work out ⟨hih, hic, hw0c, hw0h1, hw0hle, hw7, hother, hout⟩
      dsimp only []
      have hi_ne : inp.read ≠ Γ.start :=
        read_ne_start_of_cells_initTape hic (by omega)
      have hw0_ne : (work 0).read ≠ Γ.start :=
        read_ne_start_of_cells_initTape hw0c hw0h1
      have hw7_ne : (work 7).read ≠ Γ.start := by
        rw [hw7]; exact started_read_ne_start _
      have hworkRead : ∀ i, (work i).read ≠ Γ.start := by
        intro i
        by_cases hi0 : i = 0
        · subst hi0; exact hw0_ne
        · by_cases hi7 : i = 7
          · subst hi7; exact hw7_ne
          · rw [hother i hi0 hi7]
            exact blankStarted_read_ne_start
      have hout_ne : out.read ≠ Γ.start := by
        rw [hout]; exact blankStarted_read_ne_start
      obtain ⟨hinputEq, hworkEq, houtputEq⟩ :=
        phaseTransition_eq_self_of_reads_ne_start hi_ne hworkRead hout_ne
      rw [hinputEq, houtputEq]
      simp_rw [congrFun hworkEq]
      refine ⟨?_, ?_, ?_, hi_ne, hout_ne, ?_, ?_, ?_⟩
      · rw [hw0c]; rfl
      · intro j hj
        rw [hw0c]
        exact Tape.init_ofBool_cells_ne_start x j hj
      · omega
      · rw [hout]; exact le_refl 1
      · intro i hi0
        refine ⟨hworkRead i, ?_⟩
        by_cases hi7 : i = 7
        · subst hi7
          rw [hw7]; exact le_refl 1
        · rw [hother i hi0 hi7]; exact le_refl 1
      · exact ⟨hic, hih, hw0c, hw7, hother, hout⟩)
    h67
  -- Phase 4: build `pair x x` on work tape 7.
  have h4 := pairBuild_rich_hoareTime x
  -- Seam 4→5: enter the input rewind after the pair build.
  have h4567 := seqTM_hoareTime (pairBuildTM (0 : Fin 8) (7 : Fin 8)) _ h4
    (by
      rintro inp work out ⟨hic, hih, hw0c, hw0h1, hw0hle, hw7, hother, hout⟩
      dsimp only []
      have hw0_ne : (work 0).read ≠ Γ.start :=
        read_ne_start_of_cells_initTape hw0c hw0h1
      have hw7_ne : (work 7).read ≠ Γ.start := by
        rw [hw7]; exact started_read_ne_start _
      have htw0 : transitionTape (work 0) = work 0 := transitionTape_eq_self hw0_ne
      have htw7 : transitionTape (work 7) = work 7 := transitionTape_eq_self hw7_ne
      have hto : transitionTape out = out := by
        rw [hout]; exact transitionTape_eq_self blankStarted_read_ne_start
      have htwo : ∀ i : Fin 8, i ≠ 0 → i ≠ 7 →
          transitionTape (work i) = work i := by
        intro i hi0 hi7
        rw [hother i hi0 hi7]
        exact transitionTape_eq_self blankStarted_read_ne_start
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [transitionInput_cells, hic]; rfl
      · intro j hj
        rw [transitionInput_cells, hic]
        exact Tape.init_ofBool_cells_ne_start x j hj
      · have := transitionInput_head_le inp
        omega
      · rw [hto, hout]; exact blankStarted_read_ne_start
      · rw [hto, hout]; exact le_refl 1
      · intro i
        by_cases hi0 : i = 0
        · subst hi0
          rw [htw0]
          exact ⟨hw0_ne, hw0h1⟩
        · by_cases hi7 : i = 7
          · subst hi7
            rw [htw7, hw7]
            exact ⟨started_read_ne_start _, le_refl 1⟩
          · rw [htwo i hi0 hi7, hother i hi0 hi7]
            exact ⟨blankStarted_read_ne_start, le_refl 1⟩
      · exact ⟨by rw [transitionInput_cells]; exact hic,
          by rw [htw0]; exact hw0c,
          by rw [htw0]; exact hw0h1,
          by rw [htw0]; omega,
          by rw [htw7]; exact hw7,
          fun i hi0 hi7 => by rw [htwo i hi0 hi7]; exact hother i hi0 hi7,
          by rw [hto]; exact hout⟩)
    h567
  -- Phase 3: rewind the input head to cell 1 before the pair build.
  have h3 := rewindInputTM_hoareTime_frame (n := 8) (x.length + 1)
    (P := fun inp work out =>
      inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
      work 0 = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
      (∀ i : Fin 8, i ≠ 0 →
        work i = (Tape.init []).move Dir3.right) ∧
      out = (Tape.init []).move Dir3.right)
    (by
      intro inp work out inp' work' out' hP hcells _hhead hwork hout'
      obtain ⟨p1, p2, p3, p4⟩ := hP
      subst hwork hout'
      exact ⟨by rw [hcells]; exact p1, p2, p3, p4⟩)
  -- Seam 3→4: all tapes are exactly started; enter the pair build.
  have h34567 := seqTM_hoareTime rewindInputTM _ h3
    (by
      rintro inp work out ⟨hih, hic, hw0, hwother, hout⟩
      dsimp only []
      have hi_ne : inp.read ≠ Γ.start :=
        read_ne_start_of_cells_initTape hic (by omega)
      have hw0_ne : (work 0).read ≠ Γ.start := by
        rw [hw0]; exact started_read_ne_start x
      have hworkRead : ∀ i, (work i).read ≠ Γ.start := by
        intro i
        by_cases hi0 : i = 0
        · subst hi0; exact hw0_ne
        · rw [hwother i hi0]
          exact blankStarted_read_ne_start
      have hout_ne : out.read ≠ Γ.start := by
        rw [hout]; exact blankStarted_read_ne_start
      obtain ⟨hinputEq, hworkEq, houtputEq⟩ :=
        phaseTransition_eq_self_of_reads_ne_start hi_ne hworkRead hout_ne
      rw [hinputEq, houtputEq]
      simp_rw [congrFun hworkEq]
      exact ⟨Tape.ext (by rw [hih]; rfl) hic, hw0,
        hwother 7 (by decide), fun i hi0 _ => hwother i hi0, hout⟩)
    h4567
  -- Phase 2: rewind work tape 0 after the copy.
  have h2 := rewindWorkTM_hoareTime_frame (0 : Fin 8) (x.length + 1)
    (P := fun inp work out =>
      inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
      inp.head = x.length + 1 ∧
      (work 0).cells 0 = Γ.start ∧
      (∀ i, (h : i < x.length) →
        (work 0).cells (i + 1) = Γ.ofBool (x[i]'h)) ∧
      (∀ i, x.length ≤ i → (work 0).cells (i + 1) = Γ.blank) ∧
      (∀ i : Fin 8, i ≠ 0 →
        work i = (Tape.init []).move Dir3.right) ∧
      out = (Tape.init []).move Dir3.right)
    (by
      intro inp work out inp' work' out' hP hcells _hhead hother hinp houtc houth
      obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hP
      subst hinp
      have hout_eq : out' = out := Tape.ext houth houtc
      subst hout_eq
      exact ⟨p1, p2, by rw [hcells]; exact p3,
        fun i hlt => by rw [hcells]; exact p4 i hlt,
        fun i hge => by rw [hcells]; exact p5 i hge,
        fun i hi => by rw [hother i hi]; exact p6 i hi, p7⟩)
  -- Seam 2→3: work tape 0 is exactly the started x tape; enter the input rewind.
  have h234567 := seqTM_hoareTime (rewindWorkTM (0 : Fin 8)) _ h2
    (by
      rintro inp work out ⟨hw0h, hic, hih, hw0c0, hbits, htail, hwother, hout⟩
      dsimp only []
      have hw0ns := cells_ne_start_of_bits hbits htail
      have hw0_ne : (work 0).read ≠ Γ.start := by
        show (work 0).cells (work 0).head ≠ Γ.start
        exact hw0ns _ (by omega)
      have hi_ne : inp.read ≠ Γ.start :=
        read_ne_start_of_cells_initTape hic (by omega)
      have hworkRead : ∀ i, (work i).read ≠ Γ.start := by
        intro i
        by_cases hi0 : i = 0
        · subst hi0; exact hw0_ne
        · rw [hwother i hi0]
          exact blankStarted_read_ne_start
      have hout_ne : out.read ≠ Γ.start := by
        rw [hout]; exact blankStarted_read_ne_start
      have hw0xs : work 0 = (Tape.init (x.map Γ.ofBool)).move Dir3.right :=
        Tape.eq_init_move_right_of_hasBinaryString ⟨hw0h, hbits, htail⟩ hw0c0
      obtain ⟨hinputEq, hworkEq, houtputEq⟩ :=
        phaseTransition_eq_self_of_reads_ne_start hi_ne hworkRead hout_ne
      rw [hinputEq, houtputEq]
      simp_rw [congrFun hworkEq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hic]; rfl
      · intro j hj
        rw [hic]
        exact Tape.init_ofBool_cells_ne_start x j hj
      · omega
      · exact hout_ne
      · rw [hout]; exact le_refl 1
      · intro i
        refine ⟨hworkRead i, ?_⟩
        by_cases hi0 : i = 0
        · subst hi0; omega
        · rw [hwother i hi0]; exact le_refl 1
      · exact ⟨hic, hw0xs, hwother, hout⟩)
    h34567
  -- Phase 1: copy the input onto work tape 0 from the fresh configuration.
  have h1 := copyInput_fresh_hoareTime x
  -- Seam 1→2: enter the rewind of work tape 0.
  have hall := seqTM_hoareTime (copyInputToWorkTM (0 : Fin 8)) _ h1
    (by
      rintro inp work out ⟨hic, hih, hw0c0, hw0pre, hwother, hout⟩
      dsimp only []
      have hi_ne : inp.read ≠ Γ.start :=
        read_ne_start_of_cells_initTape hic (by omega)
      have hw0_ne : (work 0).read ≠ Γ.start := by
        show (work 0).cells (work 0).head ≠ Γ.start
        rw [hw0pre.1, hw0pre.2.2 x.length le_rfl]
        decide
      have hw0ns := Tape.cells_ne_start_of_hasBinaryPrefix hw0pre
      have hworkRead : ∀ i, (work i).read ≠ Γ.start := by
        intro i
        by_cases hi0 : i = 0
        · subst hi0; exact hw0_ne
        · rw [hwother i hi0]
          exact blankStarted_read_ne_start
      have hout_ne : out.read ≠ Γ.start := by
        rw [hout]; exact blankStarted_read_ne_start
      obtain ⟨hinputEq, hworkEq, houtputEq⟩ :=
        phaseTransition_eq_self_of_reads_ne_start hi_ne hworkRead hout_ne
      rw [hinputEq, houtputEq]
      simp_rw [congrFun hworkEq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hw0c0
      · intro j hj
        exact hw0ns j hj
      · rw [hw0pre.1]
      · exact hi_ne
      · exact hout_ne
      · rw [hout]; exact le_refl 1
      · intro i hi0
        refine ⟨hworkRead i, ?_⟩
        rw [hwother i hi0]; exact le_refl 1
      · exact ⟨hic, hih, hw0c0, hw0pre.2.1, hw0pre.2.2, hwother, hout⟩)
    h234567
  -- Assemble: massage the final postcondition and the time bound.
  refine hall.consequence (fun _ _ _ h => h) ?_ ?_
  · rintro inp work out ⟨hw0, hic, hih, hw7, hother, hout⟩
    refine ⟨hic, hih, ?_, hw7, by rw [hout]; rfl, by rw [hout]; rfl⟩
    intro i hi7
    by_cases hi0 : i = 0
    · subst hi0; exact hw0
    · exact hother i hi0 hi7
  · unfold pairSelfTime
    omega

/-- Clean closed quadratic bound for `pairSelfTime`. -/
theorem pairSelfTime_le (n : ℕ) : pairSelfTime n ≤ 58 * (n + 1) ^ 2 := by
  unfold pairSelfTime
  calc 23 * n + 58 ≤ 58 * (n + 1) := by omega
    _ ≤ 58 * ((n + 1) * (n + 1)) :=
        Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
    _ = 58 * (n + 1) ^ 2 := by rw [pow_two]

end TM

end Complexity
