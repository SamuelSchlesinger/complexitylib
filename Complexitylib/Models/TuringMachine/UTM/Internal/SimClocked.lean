/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Internal.SimLoop
public import Complexitylib.Models.TuringMachine.UTM.Internal.ClockFrontier

/-!
# Universal machine: the clocked (time-bounded) simulate/halt-test loop

The time-bounded variant of `utm_loop_simulates`: the 7-tape loop
`clockedLoop = loopTM clockedBody clockedTest` runs the interpreted machine
for `min` (halting time, clock budget) steps, where

* `clockedBody = seqTM (bodyTM.liftTM 1) decFrontierTM` — one body pass of
  the 6-tape UTM (lifted to 7 tapes, the clock tape pinned by the frame
  rule `liftTM_hoareTime_frame`) followed by an O(1) decrement of the
  frontier-parked unary clock on tape 6 (`clkT`);
* `clockedTest = seqTM (haltTestTM.liftTM 1) orZeroTM` — the lifted halt
  test writes the halt verdict at output cell 1, and `orZeroTM` overwrites
  it with the combined loop-exit verdict (halted **or** clock zero).

**Frontier representation**: clock value `v` ⟺ tape-6 cells are
`regCells v` and the head is at `max v 1`.

## Proof structure

Composition strategy (option (i) of the design space): `bodyIteration` is
packaged as a ghost-style `HoareTime` triple at fixed tapes
(`clockedBody_hoareTime`'s inner triple), lifted through
`liftTM_hoareTime_frame` with the clock tape as the pinned extra, and
composed with `decFrontierTM_hoareTime` via `seqTM_hoareTime`; similarly
for the test half with `haltTestTM_hoareTime` and `orZeroTM_hoareTime`.
The per-iteration lemma `clocked_iteration` then mirrors `SimLoop`'s
`loop_iteration` at the loop level (body/test phase embeddings plus a
local copy of the rewind/check bookkeeping), and two strong inductions on
the remaining fuel (`clocked_aux_halt` / `clocked_aux_timeout`) deliver
the two cases of the headline theorem `clocked_loop_simulates`.

## Statement notes (deviations from the naive statement)

The loop is do-while: even a `T = 0` run (initial configuration already
halted) executes one full iteration, which decrements the clock. Hence
case A leaves the clock at `V - max T 1` (equal to `V - T` for `T ≥ 1`).
Case B requires `1 ≤ V`: with a zero budget the do-while loop still
simulates one interpreted step before its first exit test, so "exactly
`V` simulated steps" would be false for `V = 0`. In both cases the exit
verdict at output cell 1 is `Γ.one`; the two exits are distinguished by
the state tape (`SimInv` at the final interpreted configuration makes a
subsequent halt test conclusive via `simInv_verdict`).
-/


public section

namespace Complexity

namespace TM.UTMBody

-- ════════════════════════════════════════════════════════════════════════
-- The clocked machines
-- ════════════════════════════════════════════════════════════════════════

/-- The clocked loop body: one (lifted) UTM body pass, then one O(1)
    decrement of the frontier-parked clock on tape 6. -/
def clockedBody : TM 7 := seqTM (bodyTM.liftTM 1) decFrontierTM

/-- The clocked loop test: the (lifted) halt test writes the halt verdict
    at output cell 1; `orZeroTM` replaces it with the combined loop-exit
    verdict (halted **or** clock zero). -/
def clockedTest : TM 7 := seqTM (haltTestTM.liftTM 1) orZeroTM

/-- The clocked simulate/halt-test loop. -/
def clockedLoop : TM 7 := loopTM clockedBody clockedTest

-- ════════════════════════════════════════════════════════════════════════
-- Generic `reachesIn` helpers (local copies of `SimLoop`'s private ones)
-- ════════════════════════════════════════════════════════════════════════

/-- Extend a bounded run by one step at the end. -/
private theorem reachesIn_snoc {n : ℕ} {tm : TM n} {t : ℕ} {c c' c'' : Cfg n tm.Q}
    (h : tm.reachesIn t c c') :
    tm.step c' = some c'' → tm.reachesIn (t + 1) c c'' := by
  induction h with
  | zero => exact fun hstep => .step hstep .zero
  | step hs _ ih => exact fun hstep => .step hs (ih hstep)

/-- A configuration with no step is halted. -/
private theorem state_eq_of_step_none {n : ℕ} {tm : TM n} {c : Cfg n tm.Q}
    (h : tm.step c = none) : c.state = tm.qhalt := by
  by_contra hne
  simp [TM.step, hne] at h

/-- Two tapes with the same head and cells are equal. -/
private theorem tape_eq_of_parts' {t t' : Tape} (hh : t.head = t'.head)
    (hc : t.cells = t'.cells) : t = t' := by
  cases t; cases t'; simp_all

-- ════════════════════════════════════════════════════════════════════════
-- Fin-7 index bookkeeping
-- ════════════════════════════════════════════════════════════════════════

/-- The single lifted extra tape is the clock tape. -/
private theorem natAdd_eq_clkT (j : Fin 1) : Fin.natAdd 6 j = clkT := by
  obtain ⟨jv, hj⟩ := j
  obtain rfl : jv = 0 := by omega
  rfl

/-- The six embedded body tapes are not the clock tape. -/
private theorem castAdd_ne_clkT (k : Fin 6) : Fin.castAdd 1 k ≠ clkT := by
  intro h
  have hv : k.val = 6 := congrArg Fin.val h
  have := k.isLt
  omega

/-- A non-clock index of the 7-tape layout is one of the six body tapes. -/
private theorem val_lt_of_ne_clkT {k : Fin 7} (h : k ≠ clkT) : k.val < 6 := by
  have h7 := k.isLt
  have hc : (clkT : Fin 7).val = 6 := rfl
  rcases Nat.lt_or_ge k.val 6 with h6 | h6
  · exact h6
  · exact absurd (Fin.ext (by omega : k.val = clkT.val)) h

-- ════════════════════════════════════════════════════════════════════════
-- regCells parking
-- ════════════════════════════════════════════════════════════════════════

/-- A frontier-parked clock tape reads a non-`▷` symbol. -/
private theorem clk_read_ne_start {t : Tape} {v : ℕ}
    (hc : t.cells = regCells v) (hh : t.head = max v 1) :
    t.read ≠ Γ.start := by
  rw [Tape.read, hh, hc]
  exact regCells_ne_start (le_max_right v 1)

-- ════════════════════════════════════════════════════════════════════════
-- SimInv bookkeeping (local copies of `SimLoop`'s private ones)
-- ════════════════════════════════════════════════════════════════════════

/-- Every work tape of a `SimInv` configuration is parked: it reads a
    non-`▷` symbol. -/
private theorem simInv_work_reads' (α : List Bool) {mc : Cfg 1 (decodeDesc α).toTM.Q}
    {inp : Tape} {work : Fin 6 → Tape} {out : Tape}
    (hinv : SimInv α mc inp work out) (i : Fin 6) : (work i).read ≠ Γ.start := by
  by_cases hiS : i = stT
  · subst hiS
    obtain ⟨S, hSh, -, -⟩ := hinv.state_syms_ne_blank
    exact SimInv.read_ne_start_of_holdsExact hSh hinv.state_head.ge
  · by_cases hiD : i = dsT
    · subst hiD
      exact SimInv.read_ne_start_of_holdsExact hinv.desc hinv.desc_head.ge
    · exact hinv.others_read i hiS hiD

private theorem takeField_fst_length_le'' (l : List Γw) :
    (takeField l).1.length ≤ l.length := by
  rcases takeField_structure l with hsp | ⟨hsp, -⟩
  · have := congrArg List.length hsp
    simp only [List.length_append, List.length_cons] at this
    omega
  · exact le_of_eq (congrArg List.length hsp)

private theorem qhaltField_length_le'' (l : List Γw) :
    (qhaltField l).length ≤ l.length :=
  le_trans (takeField_fst_length_le'' (takeField l).2) (takeField_rest_length l)

/-- `simInv_verdict`, strengthened with the length bound needed for the
    halt test's time accounting (local copy of `SimLoop`'s private one). -/
private theorem simInv_verdict_len' (α : List Bool) (mc : Cfg 1 (decodeDesc α).toTM.Q)
    {inp : Tape} {work : Fin 6 → Tape} {out : Tape}
    (hinv : SimInv α mc inp work out) :
    ∃ stSyms, (work stT).HoldsExact stSyms ∧ (∀ s ∈ stSyms, s ≠ Γw.blank) ∧
      stSyms.length ≤ (groupPairs α).length ∧
      ((stSyms = qhaltField (groupPairs α))
        ↔ mc.state = (decodeDesc α).toTM.qhalt) := by
  obtain ⟨S, hhold, hnb, hwhich⟩ := hinv.state_syms_ne_blank
  refine ⟨S, hhold, hnb, ?_, ?_⟩
  · rcases hwhich with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · rw [bitsToSyms_length, Nat.length_toBits, decodeDesc_w]
      exact takeField_fst_length_le'' _
    · exact qhaltField_length_le'' _
  · rcases hwhich with ⟨hlt, rfl⟩ | ⟨hq, rfl⟩
    · rw [verdict_running α hlt]
      constructor
      · intro hv
        exact Fin.val_injective (by
          show mc.state.val = min (decodeDesc α).qhalt (2 ^ (decodeDesc α).w)
          exact hv)
      · intro hs
        show mc.state.val = min (decodeDesc α).qhalt (2 ^ (decodeDesc α).w)
        rw [hs]
        rfl
    · exact iff_of_true rfl hq

/-- `SimInv` only inspects the output tape through its read. -/
private theorem simInv_with_out {α : List Bool} {mc : Cfg 1 (decodeDesc α).toTM.Q}
    {inp : Tape} {work : Fin 6 → Tape} {out : Tape}
    (h : SimInv α mc inp work out) {out' : Tape} (hread : out'.read ≠ Γ.start) :
    SimInv α mc inp work out' :=
  ⟨h.vin, h.vwk, h.vout, h.wf_in, h.wf_wk, h.wf_out, h.state, h.state_head,
   h.desc, h.desc_head, h.scratch, h.scratch_head, h.inp_read, hread⟩

-- ════════════════════════════════════════════════════════════════════════
-- 7-tape parked reads under `SimInv` + frontier clock
-- ════════════════════════════════════════════════════════════════════════

/-- The six embedded body tapes of the 7-tape layout are parked under
    `SimInv`. -/
private theorem work7_reads_ne_clk {α : List Bool} {mc : Cfg 1 (decodeDesc α).toTM.Q}
    {inp : Tape} {w : Fin 7 → Tape} {out : Tape}
    (hsi : SimInv α mc inp (fun k : Fin 6 => w (Fin.castAdd 1 k)) out) :
    ∀ k : Fin 7, k ≠ clkT → (w k).read ≠ Γ.start := by
  intro k hk
  exact simInv_work_reads' α hsi ⟨k.val, val_lt_of_ne_clkT hk⟩

/-- All seven work tapes are parked under `SimInv` plus the frontier
    clock representation. -/
private theorem work7_reads {α : List Bool} {mc : Cfg 1 (decodeDesc α).toTM.Q}
    {inp : Tape} {w : Fin 7 → Tape} {out : Tape} {v : ℕ}
    (hsi : SimInv α mc inp (fun k : Fin 6 => w (Fin.castAdd 1 k)) out)
    (hc : (w clkT).cells = regCells v) (hh : (w clkT).head = max v 1) :
    ∀ k : Fin 7, (w k).read ≠ Γ.start := by
  intro k
  by_cases hk : k = clkT
  · subst hk
    exact clk_read_ne_start hc hh
  · exact work7_reads_ne_clk hsi k hk

-- ════════════════════════════════════════════════════════════════════════
-- The loop's rewind/check bookkeeping (local copy of `SimLoop`'s private
-- `loopTM_rewind_check`; the combinator machinery is arity-polymorphic)
-- ════════════════════════════════════════════════════════════════════════

/-- From the loop's rewind state with the output head at cell 1 and every
    tape parked, three steps (rewind to `▷`, bounce to cell 1, check) reach
    the branch decision: the loop's `done` state if output cell 1 reads
    `Γ.one`, else the body's start state. All tapes are exactly
    preserved. -/
private theorem clocked_rewind_check {n : ℕ} (tmBody tmTest : TM n)
    (c : Cfg n (LoopQ tmBody.Q tmTest.Q))
    (hstate : c.state = Sum.inr (Sum.inl LoopPhase.rewindOut))
    (hin : c.input.read ≠ Γ.start)
    (hwk : ∀ i, (c.work i).read ≠ Γ.start)
    (hoh : c.output.head = 1)
    (hoc0 : c.output.cells 0 = Γ.start)
    (hons : ∀ j, 1 ≤ j → c.output.cells j ≠ Γ.start) :
    ∃ c', (loopTM tmBody tmTest).reachesIn 3 c c' ∧
      c'.state = (if c.output.cells 1 = Γ.one then
          (Sum.inr (Sum.inl LoopPhase.done) : LoopQ tmBody.Q tmTest.Q)
        else Sum.inl tmBody.qstart) ∧
      c'.input = c.input ∧ c'.work = c.work ∧ c'.output = c.output := by
  have hread1 : c.output.read ≠ Γ.start := by
    rw [Tape.read, hoh]; exact hons 1 le_rfl
  -- ── step 1: rewind left off cell 1 ──
  obtain ⟨c₁, hs1, hst1, hin1, hwk1, hoh1, hoc1⟩ :
      ∃ c₁, (loopTM tmBody tmTest).step c = some c₁ ∧
        c₁.state = Sum.inr (Sum.inl LoopPhase.rewindOut) ∧
        c₁.input = c.input ∧ c₁.work = c.work ∧
        c₁.output.head = 0 ∧ c₁.output.cells = c.output.cells := by
    simp only [TM.step, ↓reduceIte, hstate, loopTM, hread1]
    refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · exact transitionInput_eq_self hin
    · exact funext fun i => transitionTape_eq_self (hwk i)
    · simp [Tape.writeAndMove, Tape.move, Tape.write_head, hoh]
    · exact tape_readBackWrite_preserves _ _ (Or.inr hread1)
  -- ── step 2: bounce off ▷ to cell 1, entering check ──
  have hread2 : c₁.output.read = Γ.start := by
    rw [Tape.read, hoh1, hoc1]; exact hoc0
  obtain ⟨c₂, hs2, hst2, hin2, hwk2, hoh2, hoc2⟩ :
      ∃ c₂, (loopTM tmBody tmTest).step c₁ = some c₂ ∧
        c₂.state = Sum.inr (Sum.inl LoopPhase.check) ∧
        c₂.input = c₁.input ∧ c₂.work = c₁.work ∧
        c₂.output.head = 1 ∧ c₂.output.cells = c₁.output.cells := by
    simp only [TM.step, ↓reduceIte, hst1, loopTM, hread2]
    refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · exact transitionInput_eq_self (by rw [hin1]; exact hin)
    · refine funext fun i => transitionTape_eq_self ?_
      rw [hwk1]
      exact hwk i
    · simp [Tape.writeAndMove, Tape.move, Tape.write_head, hoh1]
    · show ((c₁.output.write (Γw.blank).toΓ).move Dir3.right).cells
        = c₁.output.cells
      rw [Tape.move_cells]
      simp only [Tape.write, hoh1, ↓reduceIte]
  have hout_eq : c₂.output = c.output :=
    tape_eq_of_parts' (by rw [hoh2, hoh]) (by rw [hoc2, hoc1])
  -- ── step 3: the check ──
  by_cases hone : c.output.cells 1 = Γ.one
  · have hread3 : c₂.output.read = Γ.one := by
      rw [Tape.read, hoh2, hoc2, hoc1]; exact hone
    obtain ⟨c₃, hs3, hst3, hin3, hwk3, hout3⟩ :
        ∃ c₃, (loopTM tmBody tmTest).step c₂ = some c₃ ∧
          c₃.state = Sum.inr (Sum.inl LoopPhase.done) ∧
          c₃.input = c₂.input ∧ c₃.work = c₂.work ∧ c₃.output = c₂.output := by
      simp only [TM.step, ↓reduceIte, hst2, loopTM, hread3]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
      · exact transitionInput_eq_self (by rw [hin2, hin1]; exact hin)
      · refine funext fun i => transitionTape_eq_self ?_
        rw [hwk2, hwk1]
        exact hwk i
      · rw [← hread3]
        exact transitionTape_eq_self (by rw [hread3]; simp)
    refine ⟨c₃, .step hs1 (.step hs2 (.step hs3 .zero)), ?_, ?_, ?_, ?_⟩
    · rw [hst3, ite_eq_left hone]
    · rw [hin3, hin2, hin1]
    · rw [hwk3, hwk2, hwk1]
    · rw [hout3, hout_eq]
  · have hread3 : c₂.output.read ≠ Γ.one := by
      rw [Tape.read, hoh2, hoc2, hoc1]; exact hone
    have hread3s : c₂.output.read ≠ Γ.start := by
      rw [Tape.read, hoh2, hoc2, hoc1]; exact hons 1 le_rfl
    obtain ⟨c₃, hs3, hst3, hin3, hwk3, hout3⟩ :
        ∃ c₃, (loopTM tmBody tmTest).step c₂ = some c₃ ∧
          c₃.state = Sum.inl tmBody.qstart ∧
          c₃.input = c₂.input ∧ c₃.work = c₂.work ∧ c₃.output = c₂.output := by
      simp only [TM.step, ↓reduceIte, hst2, loopTM, hread3]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
      · exact transitionInput_eq_self (by rw [hin2, hin1]; exact hin)
      · refine funext fun i => transitionTape_eq_self ?_
        rw [hwk2, hwk1]
        exact hwk i
      · exact transitionTape_eq_self hread3s
    refine ⟨c₃, .step hs1 (.step hs2 (.step hs3 .zero)), ?_, ?_, ?_, ?_⟩
    · rw [hst3, ite_eq_right hone]
    · rw [hin3, hin2, hin1]
    · rw [hwk3, hwk2, hwk1]
    · rw [hout3, hout_eq]

-- ════════════════════════════════════════════════════════════════════════
-- The clocked body: Hoare triple for one iteration's body half
-- ════════════════════════════════════════════════════════════════════════

/-- **`clockedBody` runs one interpreted step and one clock tick.**
    Ghost-style Hoare triple at fixed initial tapes: from `SimInv` at `mc`
    on the six embedded tapes and the frontier-parked clock at `v` on tape
    6, `clockedBody` halts within `bodyIterTime α + 4` steps with `SimInv`
    re-established at `mc₂` (the interpreted step of `mc`, or `mc` itself
    when halted), the clock decremented to `v - 1`, and the input/output
    tapes exactly preserved. The precondition is the frame-rule shape
    produced by `liftTM_hoareTime_frame`. -/
private theorem clockedBody_hoareTime (α : List Bool) (hterm : TerminatedRegion α)
    (mc mc₂ : Cfg 1 (decodeDesc α).toTM.Q)
    (hstepd : (decodeDesc α).toTM.step mc = some mc₂ ∨
      ((decodeDesc α).toTM.step mc = none ∧ mc₂ = mc))
    (v : ℕ) (inp : Tape) (work : Fin 7 → Tape) (out : Tape)
    (hinv : SimInv α mc inp (fun k : Fin 6 => work (Fin.castAdd 1 k)) out)
    (hclk : (work clkT).cells = regCells v)
    (hclkh : (work clkT).head = max v 1) :
    clockedBody.HoareTime
      (fun i w o =>
        (i = inp ∧ (fun k : Fin 6 => w (Fin.castAdd 1 k))
            = (fun k : Fin 6 => work (Fin.castAdd 1 k)) ∧ o = out) ∧
        ∀ j : Fin 1, w (Fin.natAdd 6 j) = work clkT)
      (fun i w o => i = inp ∧
        SimInv α mc₂ i (fun k : Fin 6 => w (Fin.castAdd 1 k)) o ∧
        (w clkT).cells = regCells (v - 1) ∧
        (w clkT).head = max (v - 1) 1 ∧ o = out)
      (bodyIterTime α + 1 + 3) := by
  -- ── the 6-tape ghost triple for one body pass ──
  have hbody6 : bodyTM.HoareTime
      (fun i w o => i = inp ∧ (w = fun k : Fin 6 => work (Fin.castAdd 1 k)) ∧
        o = out)
      (fun i w o => i = inp ∧ o = out ∧ SimInv α mc₂ i w o)
      (bodyIterTime α) := by
    rintro i w o ⟨rfl, rfl, rfl⟩
    obtain ⟨c', t, ht, hr, hst, hin, hout, hmatch⟩ :=
      bodyIteration α mc hterm
        ⟨BodyQ.hc0, i, fun k : Fin 6 => work (Fin.castAdd 1 k), o⟩ rfl hinv
    refine ⟨c', t, ht, hr, hst, hin, hout, ?_⟩
    rcases hstepd with hsome | ⟨hnone, rfl⟩
    · rw [hsome] at hmatch
      exact hmatch
    · rw [hnone] at hmatch
      have hw : c'.work = fun k : Fin 6 => work (Fin.castAdd 1 k) :=
        funext hmatch
      rw [hin, hout, hw]
      exact hinv
  -- ── lift to 7 tapes, pinning the clock tape ──
  have hex : ∀ j : Fin 1, 1 ≤ (work clkT).head ∧ (work clkT).read ≠ Γ.start :=
    fun _ => ⟨by rw [hclkh]; exact le_max_right v 1, clk_read_ne_start hclk hclkh⟩
  have hlift := liftTM_hoareTime_frame bodyTM (fun _ : Fin 1 => work clkT)
    hex hbody6
  -- ── compose with the clock decrement ──
  refine seqTM_hoareTime (bodyTM.liftTM 1) decFrontierTM
    (mid' := fun i w o => i = inp ∧ o = out ∧
      SimInv α mc₂ i (fun k : Fin 6 => w (Fin.castAdd 1 k)) o ∧
      (w clkT).cells = regCells v ∧ (w clkT).head = max v 1)
    hlift ?_ ?_
  · -- lifted-body post → decrement pre, through the (identity) transition
    rintro i w o ⟨⟨rfl, rfl, hsi⟩, hpin⟩
    have hwclk : w clkT = work clkT := by
      have h := hpin ⟨0, Nat.zero_lt_one⟩
      rwa [natAdd_eq_clkT] at h
    have hckc : (w clkT).cells = regCells v := by rw [hwclk]; exact hclk
    have hckh : (w clkT).head = max v 1 := by rw [hwclk]; exact hclkh
    have h1 : transitionInput i = i := transitionInput_eq_self hsi.inp_read
    have h2 : (fun k => transitionTape (w k)) = w :=
      funext fun k => transitionTape_eq_self (work7_reads hsi hckc hckh k)
    have h3 : transitionTape o = o := transitionTape_eq_self hsi.out_read
    rw [h1, h2, h3]
    exact ⟨rfl, rfl, hsi, hckc, hckh⟩
  · -- the decrement phase, pointwise from `decFrontierTM_hoareTime`
    rintro i w o ⟨rfl, rfl, hsi, hckc, hckh⟩
    obtain ⟨c', t, ht, hr, hh, hin', hwoth, hckc', hckh', hout'⟩ :=
      decFrontierTM_hoareTime v i w o hckc hckh hsi.inp_read
        (work7_reads_ne_clk hsi) hsi.out_read i w o ⟨rfl, rfl, rfl⟩
    have hwproj : (fun k : Fin 6 => c'.work (Fin.castAdd 1 k))
        = fun k : Fin 6 => w (Fin.castAdd 1 k) :=
      funext fun k => hwoth (Fin.castAdd 1 k) (castAdd_ne_clkT k)
    refine ⟨c', t, by omega, hr, hh, hin', ?_, hckc', hckh', hout'⟩
    rw [hin', hwproj, hout']
    exact hsi

-- ════════════════════════════════════════════════════════════════════════
-- The clocked test: Hoare triple for one iteration's test half
-- ════════════════════════════════════════════════════════════════════════

/-- **`clockedTest` writes the combined loop-exit verdict.** From `SimInv`
    at `mc₂` on the six embedded tapes, the frontier-parked clock at `v`,
    and a parked output tape, `clockedTest` halts within
    `4·|groupPairs α| + 15` steps having written the combined verdict at
    output cell 1 — `Γ.one` iff `mc₂` is halted **or** the clock is zero —
    with everything else (including the clock) exactly preserved and the
    output tape still parked at cell 1. -/
private theorem clockedTest_hoareTime (α : List Bool)
    (mc₂ : Cfg 1 (decodeDesc α).toTM.Q) (v : ℕ) (inp : Tape) :
    clockedTest.HoareTime
      (fun i w o => i = inp ∧
        SimInv α mc₂ i (fun k : Fin 6 => w (Fin.castAdd 1 k)) o ∧
        (w clkT).cells = regCells v ∧ (w clkT).head = max v 1 ∧
        o.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → o.cells j ≠ Γ.start) ∧ o.head = 1)
      (fun i w o => i = inp ∧
        SimInv α mc₂ i (fun k : Fin 6 => w (Fin.castAdd 1 k)) o ∧
        (w clkT).cells = regCells v ∧ (w clkT).head = max v 1 ∧
        o.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → o.cells j ≠ Γ.start) ∧ o.head = 1 ∧
        o.cells 1 = (if mc₂.state = (decodeDesc α).toTM.qhalt ∨ v = 0
          then Γ.one else Γ.zero))
      (4 * (groupPairs α).length + 12 + 1 + 2) := by
  refine seqTM_hoareTime (haltTestTM.liftTM 1) orZeroTM
    (mid := fun i w o => i = inp ∧
      SimInv α mc₂ i (fun k : Fin 6 => w (Fin.castAdd 1 k)) o ∧
      (w clkT).cells = regCells v ∧ (w clkT).head = max v 1 ∧
      o.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → o.cells j ≠ Γ.start) ∧ o.head = 1 ∧
      o.cells 1 = (if mc₂.state = (decodeDesc α).toTM.qhalt
        then Γ.one else Γ.zero))
    (mid' := fun i w o => i = inp ∧
      SimInv α mc₂ i (fun k : Fin 6 => w (Fin.castAdd 1 k)) o ∧
      (w clkT).cells = regCells v ∧ (w clkT).head = max v 1 ∧
      o.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → o.cells j ≠ Γ.start) ∧ o.head = 1 ∧
      o.cells 1 = (if mc₂.state = (decodeDesc α).toTM.qhalt
        then Γ.one else Γ.zero))
    ?_ ?_ ?_
  · -- ── the lifted halt test, pointwise ──
    rintro i w o ⟨rfl, hsi, hckc, hckh, hoc0, hons, hoh⟩
    obtain ⟨S, hSh, hSnb, hSlen, hSiff⟩ := simInv_verdict_len' α mc₂ hsi
    have h6 := haltTestTM_hoareTime S (groupPairs α) hSnb i
      (fun k : Fin 6 => w (Fin.castAdd 1 k)) o
      hSh hsi.state_head hsi.desc hsi.desc_head hoc0 hons hoh hsi.inp_read
      (fun k h3 h4 => hsi.others_read k h3 h4)
    have hex : ∀ j : Fin 1, 1 ≤ (w clkT).head ∧ (w clkT).read ≠ Γ.start :=
      fun _ => ⟨by rw [hckh]; exact le_max_right v 1,
        clk_read_ne_start hckc hckh⟩
    obtain ⟨c', t, ht, hr, hh, ⟨hin', hwoth, hw3, hw4, hoc', hoh'⟩, hpin⟩ :=
      liftTM_hoareTime_frame haltTestTM (fun _ : Fin 1 => w clkT) hex h6
        i w o ⟨⟨rfl, rfl, rfl⟩, fun j => congrArg w (natAdd_eq_clkT j)⟩
    -- the six embedded tapes are exactly restored
    have hwproj : (fun k : Fin 6 => c'.work (Fin.castAdd 1 k))
        = fun k : Fin 6 => w (Fin.castAdd 1 k) := by
      funext k
      by_cases h3 : k = 3
      · subst h3; exact hw3
      · by_cases h4 : k = 4
        · subst h4; exact hw4
        · exact hwoth k h3 h4
    -- the clock tape is exactly preserved
    have hwclk : c'.work clkT = w clkT := by
      have h := hpin ⟨0, Nat.zero_lt_one⟩
      rwa [natAdd_eq_clkT] at h
    -- the written verdict is the interpreted halt test's
    have hvd : (if S = (takeField (takeField (groupPairs α)).2).1
          then Γ.one else Γ.zero)
        = (if mc₂.state = (decodeDesc α).toTM.qhalt then Γ.one else Γ.zero) := by
      by_cases hq : mc₂.state = (decodeDesc α).toTM.qhalt
      · rw [ite_eq_left hq, ite_eq_left
          (show S = (takeField (takeField (groupPairs α)).2).1 from hSiff.mpr hq)]
      · rw [ite_eq_right hq, ite_eq_right
          (show ¬S = (takeField (takeField (groupPairs α)).2).1 from
            fun hc => hq (hSiff.mp hc))]
    have hoc1' : c'.output.cells 1
        = (if mc₂.state = (decodeDesc α).toTM.qhalt then Γ.one else Γ.zero) := by
      rw [hoc', Function.update_self]
      exact hvd
    have hor' : c'.output.read ≠ Γ.start := by
      rw [Tape.read, hoh', hoc1']
      split <;> simp
    refine ⟨c', t, by omega, hr, hh, hin', ?_, ?_, ?_, ?_, ?_, hoh', hoc1'⟩
    · rw [hin', hwproj]
      exact simInv_with_out hsi hor'
    · rw [hwclk]; exact hckc
    · rw [hwclk]; exact hckh
    · rw [hoc', Function.update_of_ne (by omega : (0 : ℕ) ≠ 1)]
      exact hoc0
    · intro j hj
      rw [hoc']
      by_cases hj1 : j = 1
      · subst hj1
        rw [Function.update_self]
        split <;> simp
      · rw [Function.update_of_ne hj1]
        exact hons j hj
  · -- ── halt-test post → or-zero pre, through the (identity) transition ──
    rintro i w o ⟨rfl, hsi, hckc, hckh, hoc0, hons, hoh, hoc1⟩
    have h1 : transitionInput i = i := transitionInput_eq_self hsi.inp_read
    have h2 : (fun k => transitionTape (w k)) = w :=
      funext fun k => transitionTape_eq_self (work7_reads hsi hckc hckh k)
    have h3 : transitionTape o = o := transitionTape_eq_self hsi.out_read
    rw [h1, h2, h3]
    exact ⟨rfl, hsi, hckc, hckh, hoc0, hons, hoh, hoc1⟩
  · -- ── the combined-verdict step, pointwise from `orZeroTM_hoareTime` ──
    rintro i w o ⟨rfl, hsi, hckc, hckh, hoc0, hons, hoh, hoc1⟩
    obtain ⟨c', t, ht, hr, hh, hin', hw', hoc', hoh'⟩ :=
      orZeroTM_hoareTime v
        (if mc₂.state = (decodeDesc α).toTM.qhalt then Γ.one else Γ.zero)
        i w o hckc hckh hoc1 (by split <;> simp) hoh hoc0 hsi.inp_read
        (work7_reads_ne_clk hsi) i w o ⟨rfl, rfl, rfl⟩
    -- identify the combined verdict with the exit condition
    have hcond : ((if mc₂.state = (decodeDesc α).toTM.qhalt
          then Γ.one else Γ.zero) = Γ.one ∨ v = 0)
        ↔ (mc₂.state = (decodeDesc α).toTM.qhalt ∨ v = 0) := by
      by_cases hq : mc₂.state = (decodeDesc α).toTM.qhalt <;> simp [hq]
    have hoc1' : c'.output.cells 1
        = (if mc₂.state = (decodeDesc α).toTM.qhalt ∨ v = 0
          then Γ.one else Γ.zero) := by
      rw [hoc', Function.update_self, if_congr hcond rfl rfl]
    have hor' : c'.output.read ≠ Γ.start := by
      rw [Tape.read, hoh', hoc1']
      split <;> simp
    refine ⟨c', t, by omega, hr, hh, hin', ?_, ?_, ?_, ?_, ?_, hoh', hoc1'⟩
    · rw [hin', hw']
      exact simInv_with_out hsi hor'
    · rw [hw']; exact hckc
    · rw [hw']; exact hckh
    · rw [hoc', Function.update_of_ne (by omega : (0 : ℕ) ≠ 1)]
      exact hoc0
    · intro j hj
      by_cases hj1 : j = 1
      · subst hj1
        rw [hoc1']
        split <;> simp
      · rw [hoc', Function.update_of_ne hj1]
        exact hons j hj

-- ════════════════════════════════════════════════════════════════════════
-- One clocked loop iteration
-- ════════════════════════════════════════════════════════════════════════

/-- **One iteration of the clocked UTM loop** interprets one step of the
    simulated machine and one clock tick. From the loop's start state under
    `SimInv` at `mc` with the frontier-parked clock at `v` (output parked
    at cell 1), within `utmStepTime α + 10` steps the loop either

    * halts (the combined verdict at output cell 1 is `Γ.one`) — exactly
      when the post-step configuration `mc₂` is halted **or** the
      decremented clock is zero — or
    * returns to the loop's start state,

    in both cases with `SimInv` at `mc₂`, the clock at `v - 1`, and the
    output tape again parked. The input tape is untouched throughout. -/
private theorem clocked_iteration (α : List Bool) (hterm : TerminatedRegion α)
    (mc : Cfg 1 (decodeDesc α).toTM.Q) (v : ℕ)
    (inp : Tape) (work : Fin 7 → Tape) (out : Tape)
    (hinv : SimInv α mc inp (fun k : Fin 6 => work (Fin.castAdd 1 k)) out)
    (hclk : (work clkT).cells = regCells v)
    (hclkh : (work clkT).head = max v 1)
    (hout0 : out.cells 0 = Γ.start)
    (houtns : ∀ j, 1 ≤ j → out.cells j ≠ Γ.start)
    (houth : out.head = 1) :
    ∃ (mc₂ : Cfg 1 (decodeDesc α).toTM.Q) (work' : Fin 7 → Tape) (out' : Tape)
      (t : ℕ),
      t ≤ utmStepTime α + 10 ∧
      ((decodeDesc α).toTM.step mc = some mc₂ ∨
        ((decodeDesc α).toTM.step mc = none ∧ mc₂ = mc)) ∧
      SimInv α mc₂ inp (fun k : Fin 6 => work' (Fin.castAdd 1 k)) out' ∧
      (work' clkT).cells = regCells (v - 1) ∧
      (work' clkT).head = max (v - 1) 1 ∧
      out'.cells 0 = Γ.start ∧
      (∀ j, 1 ≤ j → out'.cells j ≠ Γ.start) ∧
      out'.head = 1 ∧
      (((mc₂.state = (decodeDesc α).toTM.qhalt ∨ v - 1 = 0) ∧
        out'.cells 1 = Γ.one ∧
        clockedLoop.reachesIn t ⟨clockedLoop.qstart, inp, work, out⟩
          ⟨Sum.inr (Sum.inl LoopPhase.done), inp, work', out'⟩) ∨
       (¬(mc₂.state = (decodeDesc α).toTM.qhalt ∨ v - 1 = 0) ∧
        clockedLoop.reachesIn t ⟨clockedLoop.qstart, inp, work, out⟩
          ⟨clockedLoop.qstart, inp, work', out'⟩)) := by
  -- the interpreted step
  obtain ⟨mc₂, hstepd⟩ : ∃ mc₂, (decodeDesc α).toTM.step mc = some mc₂ ∨
      ((decodeDesc α).toTM.step mc = none ∧ mc₂ = mc) := by
    cases hse : (decodeDesc α).toTM.step mc with
    | none => exact ⟨mc, Or.inr ⟨rfl, rfl⟩⟩
    | some mc' => exact ⟨mc', Or.inl rfl⟩
  -- ── the body half ──
  obtain ⟨cb, t_body, ht_body, hr_body, hb_halt, hb_in, hb_si, hb_ckc, hb_ckh,
      hb_out⟩ :=
    clockedBody_hoareTime α hterm mc mc₂ hstepd v inp work out hinv hclk hclkh
      inp work out ⟨⟨rfl, rfl, rfl⟩, fun j => congrArg work (natAdd_eq_clkT j)⟩
  have hb_si' : SimInv α mc₂ inp
      (fun k : Fin 6 => cb.work (Fin.castAdd 1 k)) out := by
    rw [hb_in, hb_out] at hb_si
    exact hb_si
  -- loop embedding of the body run
  have hr₁ : (loopTM clockedBody clockedTest).reachesIn t_body
      (loopBodyWrap clockedBody clockedTest ⟨clockedBody.qstart, inp, work, out⟩)
      (loopBodyWrap clockedBody clockedTest cb) :=
    loopTM_body_simulation clockedBody clockedTest hr_body
  -- body → test transition (an identity on all tapes)
  have hcfg : (⟨clockedTest.qstart, transitionInput cb.input,
        fun i => transitionTape (cb.work i), transitionTape cb.output⟩ :
          Cfg 7 clockedTest.Q)
      = ⟨clockedTest.qstart, inp, cb.work, out⟩ := by
    have h1 : transitionInput cb.input = inp := by
      rw [hb_in]
      exact transitionInput_eq_self hinv.inp_read
    have h2 : (fun i => transitionTape (cb.work i)) = cb.work :=
      funext fun i => transitionTape_eq_self (work7_reads hb_si' hb_ckc hb_ckh i)
    have h3 : transitionTape cb.output = out := by
      rw [hb_out]
      exact transitionTape_eq_self hinv.out_read
    rw [h1, h2, h3]
  have hbt := loopTM_body_to_test clockedBody clockedTest
    (show cb.state = clockedBody.qhalt from hb_halt)
  rw [hcfg] at hbt
  -- ── the test half ──
  obtain ⟨ct, t_test, ht_test, hr_test, ht_halt, ht_in, ht_si, ht_ckc, ht_ckh,
      ht_oc0, ht_ons, ht_oh, ht_oc1⟩ :=
    clockedTest_hoareTime α mc₂ (v - 1) inp inp cb.work out
      ⟨rfl, hb_si', hb_ckc, hb_ckh, hout0, houtns, houth⟩
  have hr₃ : (loopTM clockedBody clockedTest).reachesIn t_test
      (loopTestWrap clockedBody clockedTest
        ⟨clockedTest.qstart, inp, cb.work, out⟩)
      (loopTestWrap clockedBody clockedTest ct) :=
    loopTM_test_simulation clockedBody clockedTest hr_test
  -- test → rewind transition (an identity on all tapes)
  have ht_or : ct.output.read ≠ Γ.start := by
    rw [Tape.read, ht_oh, ht_oc1]
    split <;> simp
  have hcfg₂ : (⟨(Sum.inr (Sum.inl LoopPhase.rewindOut) :
          LoopQ clockedBody.Q clockedTest.Q), transitionInput ct.input,
        fun i => transitionTape (ct.work i), transitionTape ct.output⟩ :
          Cfg 7 (LoopQ clockedBody.Q clockedTest.Q))
      = ⟨Sum.inr (Sum.inl LoopPhase.rewindOut), inp, ct.work, ct.output⟩ := by
    have h1 : transitionInput ct.input = inp := by
      rw [ht_in]
      exact transitionInput_eq_self hinv.inp_read
    have h2 : (fun i => transitionTape (ct.work i)) = ct.work :=
      funext fun i => transitionTape_eq_self (work7_reads ht_si ht_ckc ht_ckh i)
    have h3 : transitionTape ct.output = ct.output := transitionTape_eq_self ht_or
    rw [h1, h2, h3]
  have htr := (loopTM_test_to_rewind clockedBody clockedTest
    (show ct.state = clockedTest.qhalt from ht_halt)).trans (congrArg some hcfg₂)
  -- ── rewind + check ──
  obtain ⟨⟨cfs, cfi, cfw, cfo⟩, hr₅, hstf, hinf, hwkf, houtf⟩ :=
    clocked_rewind_check clockedBody clockedTest
      ⟨Sum.inr (Sum.inl LoopPhase.rewindOut), inp, ct.work, ct.output⟩
      rfl hinv.inp_read (work7_reads ht_si ht_ckc ht_ckh) ht_oh ht_oc0 ht_ons
  dsimp only at hstf hinf hwkf houtf
  obtain rfl := hinf.symm
  subst hwkf houtf hstf
  -- assemble the whole run
  have hr_all := reachesIn_trans _ (reachesIn_trans _ (reachesIn_trans _
    (reachesIn_trans _ hr₁ (.step hbt .zero)) hr₃) (.step htr .zero)) hr₅
  -- `SimInv` at the concrete input tape
  have ht_si' : SimInv α mc₂ inp
      (fun k : Fin 6 => ct.work (Fin.castAdd 1 k)) ct.output := by
    rw [ht_in] at ht_si
    exact ht_si
  -- time bound
  have htime : t_body + 1 + t_test + 1 + 3 ≤ utmStepTime α + 10 := by
    show _ ≤ bodyIterTime α + 4 * (groupPairs α).length + 20 + 10
    omega
  -- ── branch on the combined verdict ──
  by_cases hcond : mc₂.state = (decodeDesc α).toTM.qhalt ∨ v - 1 = 0
  · have hone : ct.output.cells 1 = Γ.one := by
      rw [ht_oc1, ite_eq_left hcond]
    rw [ite_eq_left hone] at hr_all
    exact ⟨mc₂, ct.work, ct.output, t_body + 1 + t_test + 1 + 3, htime, hstepd,
      ht_si', ht_ckc, ht_ckh, ht_oc0, ht_ons, ht_oh, Or.inl ⟨hcond, hone, hr_all⟩⟩
  · have hzero : ct.output.cells 1 = Γ.zero := by
      rw [ht_oc1, ite_eq_right hcond]
    have hone_ne : ct.output.cells 1 ≠ Γ.one := by
      rw [hzero]; simp
    rw [ite_eq_right hone_ne] at hr_all
    exact ⟨mc₂, ct.work, ct.output, t_body + 1 + t_test + 1 + 3, htime, hstepd,
      ht_si', ht_ckc, ht_ckh, ht_oc0, ht_ons, ht_oh, Or.inr ⟨hcond, hr_all⟩⟩

-- ════════════════════════════════════════════════════════════════════════
-- Case A: the interpreted machine halts within the clock budget
-- ════════════════════════════════════════════════════════════════════════

/-- Strong induction on the remaining interpreted steps `fuel = T - t'`.
    The clock holds `V - t'` at the start of each iteration; the loop exits
    exactly at the halting iteration (the invariant `t' = 0 ∨ t' < T` rules
    out re-entering the loop at a halted configuration except for the
    degenerate `T = 0` first iteration). -/
private theorem clocked_aux_halt (α x : List Bool) (hterm : TerminatedRegion α)
    (V T : ℕ) (mcF : Cfg 1 (decodeDesc α).toTM.Q) (hTV : T ≤ V)
    (hrun : (decodeDesc α).toTM.reachesIn T ((decodeDesc α).toTM.initCfg x) mcF)
    (hhaltF : (decodeDesc α).toTM.halted mcF) :
    ∀ (fuel t' : ℕ) (mc : Cfg 1 (decodeDesc α).toTM.Q)
      (inp : Tape) (work : Fin 7 → Tape) (out : Tape),
      t' + fuel = T →
      (t' = 0 ∨ t' < T) →
      (decodeDesc α).toTM.reachesIn t' ((decodeDesc α).toTM.initCfg x) mc →
      SimInv α mc inp (fun k : Fin 6 => work (Fin.castAdd 1 k)) out →
      (work clkT).cells = regCells (V - t') →
      (work clkT).head = max (V - t') 1 →
      out.cells 0 = Γ.start →
      (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) →
      out.head = 1 →
      ∃ c' t, t ≤ (fuel + 1) * (utmStepTime α + 10) ∧
        clockedLoop.reachesIn t ⟨clockedLoop.qstart, inp, work, out⟩ c' ∧
        clockedLoop.halted c' ∧
        SimInv α mcF c'.input (fun k : Fin 6 => c'.work (Fin.castAdd 1 k))
          c'.output ∧
        (c'.work clkT).cells = regCells (V - max T 1) ∧
        (c'.work clkT).head = max (V - max T 1) 1 ∧
        c'.output.cells 0 = Γ.start ∧
        (∀ j, 1 ≤ j → c'.output.cells j ≠ Γ.start) ∧
        c'.output.head = 1 ∧
        c'.output.cells 1 = Γ.one := by
  intro fuel
  induction fuel with
  | zero =>
    intro t' mc inp work out hT hpre hreach hinv hckc hckh hout0 houtns houth
    -- out of fuel: `T = 0`, the interpreted machine starts halted
    have hT0 : T = 0 := by rcases hpre with h | h <;> omega
    subst hT0
    obtain rfl : t' = 0 := by omega
    have hmc : mc = mcF := TM.reachesIn_right_unique hreach hrun
    obtain ⟨mc₂, work', out', t, ht, hstepd, hinv', hckc', hckh', hoc0', hons',
        hoh', hbranch⟩ :=
      clocked_iteration α hterm mc (V - 0) inp work out hinv hckc hckh
        hout0 houtns houth
    rcases hstepd with hsome | ⟨-, heq⟩
    · exact absurd hsome (by
        simp [TM.step,
          show mc.state = (decodeDesc α).toTM.qhalt from hmc.symm ▸ hhaltF])
    · rw [heq, hmc] at hinv'
      rcases hbranch with ⟨-, hone, hr⟩ | ⟨hncond, -⟩
      · have hVeq : V - max 0 1 = V - 0 - 1 := by
          rw [max_eq_right (Nat.zero_le 1)]
          omega
        refine ⟨⟨Sum.inr (Sum.inl LoopPhase.done), inp, work', out'⟩, t,
          by omega, hr, rfl, hinv', ?_, ?_, hoc0', hons', hoh', hone⟩
        · rw [hVeq]; exact hckc'
        · rw [hVeq]; exact hckh'
      · refine absurd (Or.inl ?_) hncond
        rw [heq, hmc]
        exact hhaltF
  | succ fuel ih =>
    intro t' mc inp work out hT hpre hreach hinv hckc hckh hout0 houtns houth
    obtain ⟨mc₂, work', out', t, ht, hstepd, hinv', hckc', hckh', hoc0', hons',
        hoh', hbranch⟩ :=
      clocked_iteration α hterm mc (V - t') inp work out hinv hckc hckh
        hout0 houtns houth
    rcases hbranch with ⟨hcond, hone, hr⟩ | ⟨hncond, hr⟩
    · -- the loop exits: identify the exit with `mcF` at time `T = t' + 1`
      rcases hstepd with hsome | ⟨hnone, -⟩
      · have hreach₂ := reachesIn_snoc hreach hsome
        -- `mc₂` is halted (directly, or because the exhausted clock forces
        -- `t' + 1 = V = T`)
        have hq : mc₂.state = (decodeDesc α).toTM.qhalt := by
          rcases hcond with hq | hclk0
          · exact hq
          · have hTeq : t' + 1 = T := by omega
            rw [hTeq] at hreach₂
            obtain rfl : mc₂ = mcF := TM.reachesIn_right_unique hreach₂ hrun
            exact hhaltF
        have hTle : T ≤ t' + 1 := TM.reachesIn_le_halt _ hrun hreach₂ hq
        have hTeq : t' + 1 = T := by omega
        rw [hTeq] at hreach₂
        obtain rfl : mc₂ = mcF := TM.reachesIn_right_unique hreach₂ hrun
        have hVeq : V - max T 1 = V - t' - 1 := by
          rw [max_eq_left (by omega : 1 ≤ T)]
          omega
        have hmul : utmStepTime α + 10
            ≤ (fuel + 1 + 1) * (utmStepTime α + 10) := by
          calc utmStepTime α + 10 = 1 * (utmStepTime α + 10) :=
                (Nat.one_mul _).symm
            _ ≤ (fuel + 1 + 1) * (utmStepTime α + 10) :=
                Nat.mul_le_mul_right _ (by omega)
        refine ⟨⟨Sum.inr (Sum.inl LoopPhase.done), inp, work', out'⟩, t,
          by omega, hr, rfl, hinv', ?_, ?_, hoc0', hons', hoh', hone⟩
        · rw [hVeq]; exact hckc'
        · rw [hVeq]; exact hckh'
      · -- a halted configuration strictly before `T`: impossible
        exfalso
        have hhalt_mc : (decodeDesc α).toTM.halted mc :=
          state_eq_of_step_none hnone
        have hTle : T ≤ t' := TM.reachesIn_le_halt _ hrun hreach hhalt_mc
        omega
    · -- the loop continues: one interpreted step and one clock tick consumed
      have hsome : (decodeDesc α).toTM.step mc = some mc₂ := by
        rcases hstepd with h | ⟨hnone, heq⟩
        · exact h
        · refine absurd (Or.inl ?_) hncond
          rw [heq]
          exact state_eq_of_step_none hnone
      have hreach₂ := reachesIn_snoc hreach hsome
      have hq2 : mc₂.state ≠ (decodeDesc α).toTM.qhalt :=
        fun h => hncond (Or.inl h)
      have hlt : t' + 1 < T := by
        rcases Nat.lt_or_ge (t' + 1) T with h | h
        · exact h
        · exfalso
          have hTeq : t' + 1 = T := by omega
          rw [hTeq] at hreach₂
          obtain rfl : mc₂ = mcF := TM.reachesIn_right_unique hreach₂ hrun
          exact hq2 hhaltF
      -- the clock representation at `t' + 1`
      have hsub : V - t' - 1 = V - (t' + 1) := by omega
      rw [hsub] at hckc' hckh'
      obtain ⟨c', t₂, ht₂, hr₂, hhalt', hinvF, hckcF, hckhF, h0, hns, hh1, hc1⟩ :=
        ih (t' + 1) mc₂ inp work' out' (by omega) (Or.inr hlt) hreach₂ hinv'
          hckc' hckh' hoc0' hons' hoh'
      refine ⟨c', t + t₂, ?_, reachesIn_trans _ hr hr₂, hhalt', hinvF,
        hckcF, hckhF, h0, hns, hh1, hc1⟩
      calc t + t₂
          ≤ (utmStepTime α + 10) + (fuel + 1) * (utmStepTime α + 10) :=
            Nat.add_le_add ht ht₂
        _ = (fuel + 1 + 1) * (utmStepTime α + 10) := by ring

-- ════════════════════════════════════════════════════════════════════════
-- Case B: the clock runs out first
-- ════════════════════════════════════════════════════════════════════════

/-- Strong induction on the remaining clock `fuel = V - t'`. The prefix
    configurations of the `V`-step run all step (so are non-halted), and
    the loop's exit is forced exactly when the clock reaches zero, at the
    `V`-step configuration `mcV`. -/
private theorem clocked_aux_timeout (α x : List Bool) (hterm : TerminatedRegion α)
    (V : ℕ) (mcV : Cfg 1 (decodeDesc α).toTM.Q)
    (hrun : (decodeDesc α).toTM.reachesIn V ((decodeDesc α).toTM.initCfg x) mcV)
    (hnh : ¬(decodeDesc α).toTM.halted mcV) :
    ∀ (fuel t' : ℕ) (mc : Cfg 1 (decodeDesc α).toTM.Q)
      (inp : Tape) (work : Fin 7 → Tape) (out : Tape),
      t' + fuel = V →
      1 ≤ fuel →
      (decodeDesc α).toTM.reachesIn t' ((decodeDesc α).toTM.initCfg x) mc →
      SimInv α mc inp (fun k : Fin 6 => work (Fin.castAdd 1 k)) out →
      (work clkT).cells = regCells fuel →
      (work clkT).head = max fuel 1 →
      out.cells 0 = Γ.start →
      (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) →
      out.head = 1 →
      ∃ c' t, t ≤ fuel * (utmStepTime α + 10) ∧
        clockedLoop.reachesIn t ⟨clockedLoop.qstart, inp, work, out⟩ c' ∧
        clockedLoop.halted c' ∧
        SimInv α mcV c'.input (fun k : Fin 6 => c'.work (Fin.castAdd 1 k))
          c'.output ∧
        (c'.work clkT).cells = regCells 0 ∧
        (c'.work clkT).head = 1 ∧
        c'.output.cells 0 = Γ.start ∧
        (∀ j, 1 ≤ j → c'.output.cells j ≠ Γ.start) ∧
        c'.output.head = 1 ∧
        c'.output.cells 1 = Γ.one := by
  intro fuel
  induction fuel with
  | zero =>
    intro t' mc inp work out hT hfuel
    exact absurd hfuel (by omega)
  | succ fuel ih =>
    intro t' mc inp work out hT hfuel hreach hinv hckc hckh hout0 houtns houth
    obtain ⟨mc₂, work', out', t, ht, hstepd, hinv', hckc', hckh', hoc0', hons',
        hoh', hbranch⟩ :=
      clocked_iteration α hterm mc (fuel + 1) inp work out hinv hckc hckh
        hout0 houtns houth
    -- the interpreted machine cannot be halted before `V`
    have hsome : (decodeDesc α).toTM.step mc = some mc₂ := by
      rcases hstepd with h | ⟨hnone, -⟩
      · exact h
      · exfalso
        have hhalt_mc : (decodeDesc α).toTM.halted mc :=
          state_eq_of_step_none hnone
        have hVle : V ≤ t' := TM.reachesIn_le_halt _ hrun hreach hhalt_mc
        omega
    have hreach₂ := reachesIn_snoc hreach hsome
    -- `mc₂` is not halted (else the whole run would already be over)
    have hq2 : mc₂.state ≠ (decodeDesc α).toTM.qhalt := by
      intro hq
      have hVle : V ≤ t' + 1 := TM.reachesIn_le_halt _ hrun hreach₂ hq
      have hTeq : t' + 1 = V := by omega
      rw [hTeq] at hreach₂
      obtain rfl : mc₂ = mcV := TM.reachesIn_right_unique hreach₂ hrun
      exact hnh hq
    rcases hbranch with ⟨hcond, hone, hr⟩ | ⟨hncond, hr⟩
    · -- exit: forced by the exhausted clock, at exactly `V` interpreted steps
      have hfuel0 : fuel = 0 := by
        rcases hcond with hq | hz
        · exact absurd hq hq2
        · omega
      subst hfuel0
      have hTeq : t' + 1 = V := by omega
      rw [hTeq] at hreach₂
      obtain rfl : mc₂ = mcV := TM.reachesIn_right_unique hreach₂ hrun
      refine ⟨⟨Sum.inr (Sum.inl LoopPhase.done), inp, work', out'⟩, t,
        by omega, hr, rfl, hinv', hckc', ?_, hoc0', hons', hoh', hone⟩
      rw [hckh']
      exact max_eq_right (by omega)
    · -- continue: the clock is still positive
      have hfuel1 : 1 ≤ fuel := by
        rcases Nat.eq_zero_or_pos fuel with rfl | h
        · exact absurd (Or.inr rfl) hncond
        · exact h
      have hs : fuel + 1 - 1 = fuel := by omega
      rw [hs] at hckc' hckh'
      obtain ⟨c', t₂, ht₂, hr₂, hhalt', hinvF, hckcF, hckhF, h0, hns, hh1, hc1⟩ :=
        ih (t' + 1) mc₂ inp work' out' (by omega) hfuel1 hreach₂ hinv'
          hckc' hckh' hoc0' hons' hoh'
      refine ⟨c', t + t₂, ?_, reachesIn_trans _ hr hr₂, hhalt', hinvF,
        hckcF, hckhF, h0, hns, hh1, hc1⟩
      calc t + t₂
          ≤ (utmStepTime α + 10) + fuel * (utmStepTime α + 10) :=
            Nat.add_le_add ht ht₂
        _ = (fuel + 1) * (utmStepTime α + 10) := by ring

-- ════════════════════════════════════════════════════════════════════════
-- The headline clocked-loop simulation theorem
-- ════════════════════════════════════════════════════════════════════════

/-- **The clocked UTM loop simulates the interpreted machine for
    `min` (halting time, clock budget) steps.** From any tapes realizing
    `SimInv` at the interpreted machine's initial configuration on the six
    embedded tapes — with the frontier-parked unary clock at `V` on tape 6
    (`clkT`) and the output tape `▷`-clean and parked at cell 1 — the loop
    `clockedLoop = loopTM clockedBody clockedTest` halts with the exit
    verdict `Γ.one` at output cell 1, and:

    * **(A: halt within budget)** if `(decodeDesc α).toTM` halts on `x` at
      `mcF` in `T ≤ V` steps, the loop exits within
      `(T + 1) * (utmStepTime α + 10)` steps with `SimInv` re-established
      at `mcF` and the clock at `V - max T 1` (i.e. `V - T` for `T ≥ 1`;
      the do-while loop burns one tick even when the machine starts
      halted);
    * **(B: timeout)** if the machine is still running after `V ≥ 1` steps
      (at `mcV`), the loop exits within `(V + 1) * (utmStepTime α + 10)`
      steps with `SimInv` at the `V`-step configuration `mcV` and the
      clock at `0`.

    In both cases the output tape is parked (`▷`-clean, head at cell 1).
    The two exits are distinguished by the final state tape: `SimInv` at
    the exit configuration makes a subsequent (lifted) halt test
    conclusive via `simInv_verdict`. Note that no-halt-before-`V` in case
    B is automatic: the prefix configurations of the `V`-step run all
    step, and halted configurations cannot step. -/
theorem clocked_loop_simulates (α x : List Bool) (hterm : TerminatedRegion α)
    (V : ℕ) (inp : Tape) (work : Fin 7 → Tape) (out : Tape)
    (hinv : SimInv α ((decodeDesc α).toTM.initCfg x) inp
      (fun k : Fin 6 => work (Fin.castAdd 1 k)) out)
    (hclk : (work clkT).cells = regCells V)
    (hclkh : (work clkT).head = max V 1)
    (hout0 : out.cells 0 = Γ.start)
    (houtns : ∀ j, 1 ≤ j → out.cells j ≠ Γ.start)
    (houth : out.head = 1) :
    -- CASE A: the interpreted machine halts within the clock budget
    (∀ (T : ℕ) (mcF : Cfg 1 (decodeDesc α).toTM.Q), T ≤ V →
      (decodeDesc α).toTM.reachesIn T ((decodeDesc α).toTM.initCfg x) mcF →
      (decodeDesc α).toTM.halted mcF →
      ∃ c' t, t ≤ (T + 1) * (utmStepTime α + 10) ∧
        clockedLoop.reachesIn t ⟨clockedLoop.qstart, inp, work, out⟩ c' ∧
        clockedLoop.halted c' ∧
        SimInv α mcF c'.input (fun k : Fin 6 => c'.work (Fin.castAdd 1 k))
          c'.output ∧
        (c'.work clkT).cells = regCells (V - max T 1) ∧
        (c'.work clkT).head = max (V - max T 1) 1 ∧
        c'.output.cells 0 = Γ.start ∧
        (∀ j, 1 ≤ j → c'.output.cells j ≠ Γ.start) ∧
        c'.output.head = 1 ∧
        c'.output.cells 1 = Γ.one)
    ∧
    -- CASE B: the clock runs out first
    (∀ mcV : Cfg 1 (decodeDesc α).toTM.Q, 1 ≤ V →
      (decodeDesc α).toTM.reachesIn V ((decodeDesc α).toTM.initCfg x) mcV →
      ¬(decodeDesc α).toTM.halted mcV →
      ∃ c' t, t ≤ (V + 1) * (utmStepTime α + 10) ∧
        clockedLoop.reachesIn t ⟨clockedLoop.qstart, inp, work, out⟩ c' ∧
        clockedLoop.halted c' ∧
        SimInv α mcV c'.input (fun k : Fin 6 => c'.work (Fin.castAdd 1 k))
          c'.output ∧
        (c'.work clkT).cells = regCells 0 ∧
        (c'.work clkT).head = 1 ∧
        c'.output.cells 0 = Γ.start ∧
        (∀ j, 1 ≤ j → c'.output.cells j ≠ Γ.start) ∧
        c'.output.head = 1 ∧
        c'.output.cells 1 = Γ.one) := by
  constructor
  · intro T mcF hTV hrun hhalt
    exact clocked_aux_halt α x hterm V T mcF hTV hrun hhalt T 0
      ((decodeDesc α).toTM.initCfg x) inp work out (by omega) (Or.inl rfl)
      .zero hinv hclk hclkh hout0 houtns houth
  · intro mcV hV hrun hnh
    obtain ⟨c', t, ht, hr, hh, hsi, hckc, hckh', h0, hns, hh1, hc1⟩ :=
      clocked_aux_timeout α x hterm V mcV hrun hnh V 0
        ((decodeDesc α).toTM.initCfg x) inp work out (by omega) hV
        .zero hinv hclk hclkh hout0 houtns houth
    exact ⟨c', t, le_trans ht (Nat.mul_le_mul_right _ (by omega)), hr, hh,
      hsi, hckc, hckh', h0, hns, hh1, hc1⟩

end TM.UTMBody

end Complexity
