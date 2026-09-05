/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Internal.SimClocked
public import Complexitylib.Models.TuringMachine.UTM.Internal.SeekFrontier
public import Complexitylib.Models.TuringMachine.Subroutines.Internal

/-!
# The clocked universal machine

`clockedUtmTM` — the 7-tape time-bounded universal machine that the
time-hierarchy diagonalizer runs under `retargetInput`. On input `pair α x`
with the unary clock `V` preloaded on the clock tape (`clkT`):

* the lifted `initTM` parses the input onto the six UTM tapes (the frame
  rule pins the clock tape);
* `seekFrontierTM` walks the clock head from cell 1 to the frontier
  (`max V 1`), the representation expected by the clocked loop;
* `clockedLoop` simulates the interpreted machine `(decodeDesc α).toTM`
  for `min` (halting time, clock budget) steps;
* a lifted `haltTestTM`, as the test of an `ifTM`, re-derives whether the
  simulation halted: verdict `Γ.one` routes to the lifted `extractTM`
  (copy the simulated output to the real output tape), verdict `Γ.zero`
  (timeout) routes to `writeTM Γw.one` (the timeout sentinel at output
  cell 1).

## Main results

* `clockedUtmTM_hoareTime_halt` — if the interpreted machine halts at
  `mcF` within `T ≤ V` steps, the real output tape agrees with `mcF`'s
  output tape through the latter's first blank;
* `clockedUtmTM_hoareTime_timeout` — if the interpreted machine is still
  running after `V ≥ 1` steps, output cell 1 holds the sentinel `Γ.one`;

both within `clockedUtmTime α x V` steps from the started tapes
`clockedUtmPre α x V` (the shape delivered by the diagonalizer's
`retargetInput` mid-sequence).
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Runs preserve output-tape well-formedness: writes are `Γw` (never `▷`)
    and cell 0 is immutable. -/
private theorem reachesIn_output_wfCells {n : ℕ} {tm : TM n} :
    ∀ {t : ℕ} {c c' : Cfg n tm.Q}, tm.reachesIn t c c' →
      c.output.StartInvariant → c'.output.StartInvariant := by
  intro t
  induction t with
  | zero =>
    intro c c' h hwf
    cases h
    exact hwf
  | succ t ih =>
    intro c c' h hwf
    cases h with
    | step hstep hrest =>
      next c'' =>
      refine ih hrest ?_
      unfold TM.step at hstep
      split at hstep
      · exact absurd hstep (by simp)
      · simp only [Option.some.injEq] at hstep
        subst hstep
        exact hwf.writeAndMove _ _

/-- **Output-WF strengthening for Hoare triples.** If the precondition puts
    a well-formed output tape at the start (cell 0 = `▷` and nowhere else),
    the postcondition may be strengthened with the same well-formedness of
    the final output tape — writes are `Γw` and cell 0 is immutable, so the
    shape survives any run. This is what lets branch postconditions survive
    the combinators' final `transitionTape` (which preserves cells only on
    `▷`-clean tapes). -/
theorem HoareTime.with_output_wf {n : ℕ} {tm : TM n}
    {pre post : TapePred n} {b : ℕ}
    (h : tm.HoareTime pre post b)
    (hpre : ∀ inp work out, pre inp work out →
      out.cells 0 = Γ.start ∧ ∀ j, 1 ≤ j → out.cells j ≠ Γ.start) :
    tm.HoareTime pre
      (fun inp work out => post inp work out ∧
        out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start)) b := by
  intro inp work out hp
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ := h inp work out hp
  have hwf : c'.output.StartInvariant := reachesIn_output_wfCells hreach (hpre _ _ _ hp)
  exact ⟨c', t, ht, hreach, hhalt, hpost, hwf.1, hwf.2⟩

end TM

namespace TM.UTMBody

-- ════════════════════════════════════════════════════════════════════════
-- Generic run-level tape preservation
-- ════════════════════════════════════════════════════════════════════════

/-- Runs never alter the input tape's cells (the input tape is read-only). -/
private theorem reachesIn_input_cells {n : ℕ} {tm : TM n} :
    ∀ {t : ℕ} {c c' : Cfg n tm.Q}, tm.reachesIn t c c' →
      c'.input.cells = c.input.cells := by
  intro t
  induction t with
  | zero =>
    intro c c' h
    cases h
    rfl
  | succ t ih =>
    intro c c' h
    cases h with
    | step hstep hrest =>
      next c'' =>
      have h1 : c''.input.cells = c.input.cells := by
        unfold TM.step at hstep
        split at hstep
        · exact absurd hstep (by simp)
        · simp only [Option.some.injEq] at hstep
          subst hstep
          exact Tape.move_cells ..
      rw [ih hrest, h1]



-- ════════════════════════════════════════════════════════════════════════
-- Fin-7 index bookkeeping (local copies of `SimClocked`'s private ones)
-- ════════════════════════════════════════════════════════════════════════

/-- The single lifted extra tape is the clock tape. -/
private theorem natAdd_eq_clkT' (j : Fin 1) : Fin.natAdd 6 j = clkT := by
  obtain ⟨jv, hj⟩ := j
  obtain rfl : jv = 0 := by omega
  rfl

/-- The six embedded body tapes are not the clock tape. -/
private theorem castAdd_ne_clkT' (k : Fin 6) : Fin.castAdd 1 k ≠ clkT := by
  intro h
  have hv : k.val = 6 := congrArg Fin.val h
  have := k.isLt
  omega

/-- A non-clock index of the 7-tape layout is one of the six body tapes. -/
private theorem val_lt_of_ne_clkT' {k : Fin 7} (h : k ≠ clkT) : k.val < 6 := by
  have h7 := k.isLt
  have hc : (clkT : Fin 7).val = 6 := rfl
  rcases Nat.lt_or_ge k.val 6 with h6 | h6
  · exact h6
  · exact absurd (Fin.ext (by omega : k.val = clkT.val)) h

-- ════════════════════════════════════════════════════════════════════════
-- regCells parking (local copies)
-- ════════════════════════════════════════════════════════════════════════

/-- A frontier-parked clock tape reads a non-`▷` symbol. -/
private theorem clk_read_ne_start' {t : Tape} {v : ℕ}
    (hc : t.cells = regCells v) (hh : t.head = max v 1) :
    t.read ≠ Γ.start := by
  rw [Tape.read, hh, hc]
  exact regCells_ne_start (le_max_right v 1)

-- ════════════════════════════════════════════════════════════════════════
-- SimInv bookkeeping (local copies of `SimLoop`/`SimClocked` private ones)
-- ════════════════════════════════════════════════════════════════════════

/-- Every work tape of a `SimInv` configuration is parked: it reads a
    non-`▷` symbol. -/
private theorem simInv_work_reads'' (α : List Bool)
    {mc : Cfg 1 (decodeDesc α).toTM.Q}
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

/-- Every work tape of a `SimInv` configuration is well-formed. -/
private theorem simInv_work_wf (α : List Bool)
    {mc : Cfg 1 (decodeDesc α).toTM.Q}
    {inp : Tape} {work : Fin 6 → Tape} {out : Tape}
    (hinv : SimInv α mc inp work out) (i : Fin 6) : (work i).StartInvariant := by
  rcases i with ⟨iv, hv⟩
  rcases iv with _ | _ | _ | _ | _ | _ | n
  · exact hinv.vin.startInvariant hinv.wf_in
  · exact hinv.vwk.startInvariant hinv.wf_wk
  · exact hinv.vout.startInvariant hinv.wf_out
  · obtain ⟨S, hSh, -, -⟩ := hinv.state_syms_ne_blank
    exact Tape.HoldsExact.startInvariant hSh
  · exact Tape.HoldsExact.startInvariant hinv.desc
  · exact Tape.HoldsExact.startInvariant hinv.scratch
  · exact absurd hv (by omega)

/-- The six embedded body tapes of the 7-tape layout are parked under
    `SimInv`. -/
private theorem work7_reads_ne_clk' {α : List Bool}
    {mc : Cfg 1 (decodeDesc α).toTM.Q}
    {inp : Tape} {w : Fin 7 → Tape} {out : Tape}
    (hsi : SimInv α mc inp (fun k : Fin 6 => w (Fin.castAdd 1 k)) out) :
    ∀ k : Fin 7, k ≠ clkT → (w k).read ≠ Γ.start := by
  intro k hk
  exact simInv_work_reads'' α hsi ⟨k.val, val_lt_of_ne_clkT' hk⟩

/-- All seven work tapes are parked under `SimInv` plus the frontier
    clock representation. -/
private theorem work7_reads' {α : List Bool}
    {mc : Cfg 1 (decodeDesc α).toTM.Q}
    {inp : Tape} {w : Fin 7 → Tape} {out : Tape} {v : ℕ}
    (hsi : SimInv α mc inp (fun k : Fin 6 => w (Fin.castAdd 1 k)) out)
    (hc : (w clkT).cells = regCells v) (hh : (w clkT).head = max v 1) :
    ∀ k : Fin 7, (w k).read ≠ Γ.start := by
  intro k
  by_cases hk : k = clkT
  · subst hk
    exact clk_read_ne_start' hc hh
  · exact work7_reads_ne_clk' hsi k hk

/-- `SimInv` only inspects the output tape through its read. -/
private theorem simInv_with_out' {α : List Bool}
    {mc : Cfg 1 (decodeDesc α).toTM.Q}
    {inp : Tape} {work : Fin 6 → Tape} {out : Tape}
    (h : SimInv α mc inp work out) {out' : Tape} (hread : out'.read ≠ Γ.start) :
    SimInv α mc inp work out' :=
  ⟨h.vin, h.vwk, h.vout, h.wf_in, h.wf_wk, h.wf_out, h.state, h.state_head,
   h.desc, h.desc_head, h.scratch, h.scratch_head, h.inp_read, hread⟩

private theorem takeField_fst_length_le''' (l : List Γw) :
    (takeField l).1.length ≤ l.length := by
  rcases takeField_structure l with hsp | ⟨hsp, -⟩
  · have := congrArg List.length hsp
    simp only [List.length_append, List.length_cons] at this
    omega
  · exact le_of_eq (congrArg List.length hsp)

private theorem qhaltField_length_le''' (l : List Γw) :
    (qhaltField l).length ≤ l.length :=
  le_trans (takeField_fst_length_le''' (takeField l).2) (takeField_rest_length l)

/-- `simInv_verdict`, strengthened with the length bound needed for the
    halt test's time accounting (local copy of `SimClocked`'s private one). -/
private theorem simInv_verdict_len'' (α : List Bool)
    (mc : Cfg 1 (decodeDesc α).toTM.Q)
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
      exact takeField_fst_length_le''' _
    · exact qhaltField_length_le''' _
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

/-- The simulated output tape has a first blank at cell `m + 1` for some
    `m ≤ T` (local copy of `SimLoop`'s private `output_first_blank_shift`). -/
private theorem output_first_blank_shift' {n : ℕ} {tm : TM n} {T : ℕ}
    {x : List Bool} {c' : Cfg n tm.Q}
    (h : tm.reachesIn T (tm.initCfg x) c') :
    ∃ m, m ≤ T ∧ c'.output.cells (m + 1) = Γ.blank ∧
      ∀ j, j < m → c'.output.cells (j + 1) ≠ Γ.blank := by
  classical
  have hblank : c'.output.cells (T + 1) = Γ.blank := by
    rw [reachesIn_output_cells_far h (T + 1) (by show (0 : ℕ) + T < T + 1; omega)]
    show (Tape.init []).cells (T + 1) = Γ.blank
    simp [Tape.init]
  have hP : ∃ m, c'.output.cells (m + 1) = Γ.blank := ⟨T, hblank⟩
  refine ⟨Nat.find hP, ?_, Nat.find_spec hP, fun j hj => Nat.find_min hP hj⟩
  exact Nat.le_of_not_lt fun hcon => (Nat.find_min hP hcon) hblank

-- ════════════════════════════════════════════════════════════════════════
-- The machine, precondition, and time bound
-- ════════════════════════════════════════════════════════════════════════

/-- **The clocked universal machine**: initialize the six UTM tapes (the
    lifted `initTM`, clock tape pinned), park the clock head at the
    frontier, run the clocked simulate/decrement loop, then test whether
    the simulation halted: extract its output on verdict `Γ.one`, write
    the timeout sentinel `Γw.one` on verdict `Γ.zero`. -/
def clockedUtmTM : TM 7 :=
  seqTM (initTM.liftTM 1)
    (seqTM seekFrontierTM
      (seqTM clockedLoop
        (ifTM (haltTestTM.liftTM 1) (extractTM.liftTM 1) (writeTM Γw.one))))

/-- The clocked universal machine's precondition, in started form (the
    machine runs under `retargetInput` mid-sequence): input `pair α x` with
    the head parked at cell 1, the six UTM tapes blank and parked, the
    clock tape holding the canonical unary register `regTape V`, and the
    output tape blank and parked. -/
def clockedUtmPre (α x : List Bool) (V : ℕ) : TapePred 7 :=
  fun inp work out =>
    inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧ inp.head = 1 ∧
    (∀ i : Fin 6, work (Fin.castAdd 1 i) = (Tape.init []).move Dir3.right) ∧
    work clkT = regTape V ∧
    out.cells = (Tape.init []).cells ∧ out.head = 1

/-- The clocked universal machine's time bound, covering both the
    halt-within-budget and timeout cases: initialization, the frontier
    seek, the clocked loop (at most `V + 1` iterations), and the final
    halt-test/extract-or-write branch. -/
def clockedUtmTime (α x : List Bool) (V : ℕ) : ℕ :=
  4 * (pair α x).length + 4 * (groupPairs α).length + 24
    + 1 + (V + 3)
    + 1 + (V + 1) * (utmStepTime α + 10)
    + 1 + (4 * (groupPairs α).length + 12 + 1 + (2 * V + 9) + 5)

-- ════════════════════════════════════════════════════════════════════════
-- Phase predicates
-- ════════════════════════════════════════════════════════════════════════

/-- The six UTM work tapes' shape at the exit of the init phase. -/
private def body6Shape (α x : List Bool) (w : Fin 6 → Tape) : Prop :=
  (w 0).cells = (fun k => if k = 0 then Γ.start else if k = 1 then Γ.blank
    else (((x.map Γ.ofBool))[k - 2]?).getD Γ.blank) ∧ (w 0).head = 1 ∧
  (w 1).HoldsExact [] ∧ (w 1).head = 1 ∧
  (w 2).HoldsExact [] ∧ (w 2).head = 1 ∧
  (w 3).HoldsExact (takeField (groupPairs α)).1 ∧ (w 3).head = 1 ∧
  (w 4).HoldsExact (groupPairs α) ∧ (w 4).head = 1 ∧
  (w 5).HoldsExact [] ∧ (w 5).head = 1

/-- Exit of the (lifted) init phase: six shaped UTM tapes, blank parked
    output, and the untouched register-parked clock. -/
private def initPost7 (α x : List Bool) (V : ℕ) : TapePred 7 :=
  fun inp work out =>
    inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧
    body6Shape α x (fun k : Fin 6 => work (Fin.castAdd 1 k)) ∧
    out.cells = (Tape.init []).cells ∧ out.head = 1 ∧
    work clkT = regTape V

/-- Entry of the frontier-seek phase (`initPost7` after the seam, with the
    input head bounced off `▷`). -/
private def seekPre (α x : List Bool) (V : ℕ) : TapePred 7 :=
  fun inp work out =>
    inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧ 1 ≤ inp.head ∧
    body6Shape α x (fun k : Fin 6 => work (Fin.castAdd 1 k)) ∧
    work clkT = regTape V ∧
    out.cells = (Tape.init []).cells ∧ out.head = 1

/-- Exit of the frontier-seek phase: the clock head has walked to the
    frontier `max V 1`. -/
private def seekPost (α x : List Bool) (V : ℕ) : TapePred 7 :=
  fun inp work out =>
    inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧ 1 ≤ inp.head ∧
    body6Shape α x (fun k : Fin 6 => work (Fin.castAdd 1 k)) ∧
    (work clkT).cells = regCells V ∧ (work clkT).head = max V 1 ∧
    out.cells = (Tape.init []).cells ∧ out.head = 1

/-- Entry of the clocked loop: `SimInv` at the interpreted machine's
    initial configuration, the frontier-parked clock at `V`, and a
    `▷`-clean parked output tape. -/
private def loopPre (α x : List Bool) (V : ℕ) : TapePred 7 :=
  fun inp work out =>
    inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧
    SimInv α ((decodeDesc α).toTM.initCfg x) inp
      (fun k : Fin 6 => work (Fin.castAdd 1 k)) out ∧
    (work clkT).cells = regCells V ∧ (work clkT).head = max V 1 ∧
    out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
    out.head = 1

/-- Exit of the clocked loop: `SimInv` at the final interpreted
    configuration `mc`, the frontier-parked clock at the remaining budget
    `v`, and the loop-exit verdict `Γ.one` at output cell 1. -/
private def loopExit (α x : List Bool) (mc : Cfg 1 (decodeDesc α).toTM.Q)
    (v : ℕ) : TapePred 7 :=
  fun inp work out =>
    inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧
    SimInv α mc inp (fun k : Fin 6 => work (Fin.castAdd 1 k)) out ∧
    (work clkT).cells = regCells v ∧ (work clkT).head = max v 1 ∧
    out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
    out.head = 1 ∧ out.cells 1 = Γ.one

/-- Exit of the (lifted) halt-test phase: everything preserved, with the
    interpreted halt verdict now at output cell 1. -/
private def testExit (α x : List Bool) (mc : Cfg 1 (decodeDesc α).toTM.Q)
    (v : ℕ) : TapePred 7 :=
  fun inp work out =>
    inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧
    SimInv α mc inp (fun k : Fin 6 => work (Fin.castAdd 1 k)) out ∧
    (work clkT).cells = regCells v ∧ (work clkT).head = max v 1 ∧
    out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
    out.head = 1 ∧
    out.cells 1 = (if mc.state = (decodeDesc α).toTM.qhalt
      then Γ.one else Γ.zero)

/-- Entry of either `ifTM` branch: `SimInv` at `mc`, the parked clock, and
    a `▷`-clean output tape parked at cell 1. -/
private def branchPre (α : List Bool) (mc : Cfg 1 (decodeDesc α).toTM.Q)
    (v : ℕ) : TapePred 7 :=
  fun inp work out =>
    SimInv α mc inp (fun k : Fin 6 => work (Fin.castAdd 1 k)) out ∧
    (work clkT).cells = regCells v ∧ (work clkT).head = max v 1 ∧
    out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
    out.head = 1

-- ════════════════════════════════════════════════════════════════════════
-- Parked reads from the phase predicates
-- ════════════════════════════════════════════════════════════════════════

/-- Every shaped UTM work tape is parked: it reads a non-`▷` symbol. -/
private theorem body6Shape_reads {α x : List Bool} {w : Fin 6 → Tape}
    (h : body6Shape α x w) : ∀ k : Fin 6, (w k).read ≠ Γ.start := by
  obtain ⟨hw0c, hw0h, hw1, hw1h, hw2, hw2h, hw3, hw3h, hw4, hw4h, hw5, hw5h⟩ := h
  intro k
  rcases k with ⟨kv, hv⟩
  rcases kv with _ | _ | _ | _ | _ | _ | n
  · show (w 0).read ≠ Γ.start
    rw [Tape.read, hw0h, hw0c]
    simp
  · exact SimInv.read_ne_start_of_holdsExact hw1 hw1h.ge
  · exact SimInv.read_ne_start_of_holdsExact hw2 hw2h.ge
  · exact SimInv.read_ne_start_of_holdsExact hw3 hw3h.ge
  · exact SimInv.read_ne_start_of_holdsExact hw4 hw4h.ge
  · exact SimInv.read_ne_start_of_holdsExact hw5 hw5h.ge
  · exact absurd hv (by omega)

/-- The canonical register tape is parked at cell 1. -/
private theorem regT_read_ne_start (V : ℕ) : (regTape V).read ≠ Γ.start := by
  show regCells V 1 ≠ Γ.start
  exact regCells_ne_start le_rfl

-- ════════════════════════════════════════════════════════════════════════
-- Phase 1: the lifted init
-- ════════════════════════════════════════════════════════════════════════

/-- The lifted init phase: `initTM_hoareTime_started` through the frame
    rule, the clock tape pinned at `regTape V`. -/
private theorem initPhase (α x : List Bool) (V : ℕ) :
    (initTM.liftTM 1).HoareTime (clockedUtmPre α x V) (initPost7 α x V)
      (4 * (pair α x).length + 4 * (groupPairs α).length + 24) := by
  have hex : ∀ j : Fin 1, 1 ≤ (regTape V).head ∧ (regTape V).read ≠ Γ.start :=
    fun _ => ⟨le_rfl, regT_read_ne_start V⟩
  refine (liftTM_hoareTime_frame initTM (fun _ : Fin 1 => regTape V) hex
    (initTM_hoareTime_started α x)).consequence ?_ ?_ le_rfl
  · rintro inp work out ⟨hic, hih, hw, hclk, hoc, hoh⟩
    exact ⟨⟨hic, hih, hw, hoc, hoh⟩,
      fun j => by rw [natAdd_eq_clkT' j]; exact hclk⟩
  · rintro inp work out ⟨⟨hic, hw0c, hw0h, hw1, hw1h, hw2, hw2h, hw3, hw3h,
      hw4, hw4h, hw5, hw5h, hoc, hoh⟩, hpin⟩
    refine ⟨hic, ⟨hw0c, hw0h, hw1, hw1h, hw2, hw2h, hw3, hw3h, hw4, hw4h,
      hw5, hw5h⟩, hoc, hoh, ?_⟩
    rw [← natAdd_eq_clkT' ⟨0, Nat.zero_lt_one⟩]
    exact hpin _

/-- Seam init → seek: the combinator transition bounces the input head off
    `▷` and is the identity on every parked tape. -/
private theorem initSeam (α x : List Bool) (V : ℕ) :
    ∀ inp work out, initPost7 α x V inp work out →
      seekPre α x V (transitionInput inp)
        (fun i => transitionTape (work i)) (transitionTape out) := by
  rintro inp work out ⟨hic, hshape, hoc, hoh, hclk⟩
  have hinp0 : inp.cells 0 = Γ.start := by
    rw [hic]
    simp [Tape.init]
  have hout_read : out.read ≠ Γ.start := by
    rw [Tape.read, hoh, hoc]
    simp [Tape.init]
  have hwtr : (fun i : Fin 7 => transitionTape (work i)) = work := by
    funext i
    refine transitionTape_eq_self ?_
    by_cases hi : i = clkT
    · subst hi
      rw [hclk]
      exact regT_read_ne_start V
    · exact body6Shape_reads hshape ⟨i.val, val_lt_of_ne_clkT' hi⟩
  have hotr : transitionTape out = out := transitionTape_eq_self hout_read
  rw [hwtr, hotr]
  exact ⟨by rw [transitionInput_cells]; exact hic,
    transitionInput_head_ge inp hinp0, hshape, hclk, hoc, hoh⟩

-- ════════════════════════════════════════════════════════════════════════
-- Phase 2: the frontier seek
-- ════════════════════════════════════════════════════════════════════════

/-- The frontier-seek phase: `seekFrontierTM_hoareTime` instantiated
    pointwise, everything but the clock head exactly preserved. -/
private theorem seekPhase (α x : List Bool) (V : ℕ) :
    seekFrontierTM.HoareTime (seekPre α x V) (seekPost α x V) (V + 3) := by
  rintro inp work out ⟨hic, hih, hshape, hclk, hoc, hoh⟩
  have hinp : inp.read ≠ Γ.start := by
    rw [Tape.read, hic]
    exact (Tape.StartInvariant.init_ofBool (pair α x)).2 inp.head hih
  have hothers : ∀ i : Fin 7, i ≠ clkT → (work i).read ≠ Γ.start := fun i hi =>
    body6Shape_reads hshape ⟨i.val, val_lt_of_ne_clkT' hi⟩
  have hout : out.read ≠ Γ.start := by
    rw [Tape.read, hoh, hoc]
    simp [Tape.init]
  obtain ⟨c', t, ht, hr, hh, hin', hwoth, hckc, hckh, hout'⟩ :=
    seekFrontierTM_hoareTime V inp work out hclk hinp hothers hout
      inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨c', t, ht, hr, hh, ?_, ?_, ?_, hckc, hckh, ?_, ?_⟩
  · rw [hin']
    exact hic
  · rw [hin']
    exact hih
  · have hproj : (fun k : Fin 6 => c'.work (Fin.castAdd 1 k))
        = fun k : Fin 6 => work (Fin.castAdd 1 k) :=
      funext fun k => hwoth _ (castAdd_ne_clkT' k)
    rw [hproj]
    exact hshape
  · rw [hout']
    exact hoc
  · rw [hout']
    exact hoh

/-- Seam seek → loop: the transition is the identity on the parked tapes,
    and the init shape realizes `SimInv` at the interpreted machine's
    initial configuration (`initPost_simInv`). -/
private theorem seekSeam (α x : List Bool) (V : ℕ) :
    ∀ inp work out, seekPost α x V inp work out →
      loopPre α x V (transitionInput inp)
        (fun i => transitionTape (work i)) (transitionTape out) := by
  rintro inp work out ⟨hic, hih, hshape, hckc, hckh, hoc, hoh⟩
  have hinp0 : inp.cells 0 = Γ.start := by
    rw [hic]
    simp [Tape.init]
  have hout_read : out.read ≠ Γ.start := by
    rw [Tape.read, hoh, hoc]
    simp [Tape.init]
  have hwtr : (fun i : Fin 7 => transitionTape (work i)) = work := by
    funext i
    refine transitionTape_eq_self ?_
    by_cases hi : i = clkT
    · subst hi
      exact clk_read_ne_start' hckc hckh
    · exact body6Shape_reads hshape ⟨i.val, val_lt_of_ne_clkT' hi⟩
  have hotr : transitionTape out = out := transitionTape_eq_self hout_read
  rw [hwtr, hotr]
  obtain ⟨hw0c, hw0h, hw1, hw1h, hw2, hw2h, hw3, hw3h, hw4, hw4h, hw5, hw5h⟩ :=
    hshape
  refine ⟨by rw [transitionInput_cells]; exact hic, ?_, hckc, hckh, ?_, ?_, hoh⟩
  · exact initPost_simInv α x (transitionInput inp)
      (fun k : Fin 6 => work (Fin.castAdd 1 k)) out
      ⟨by rw [transitionInput_cells]; exact hic, hw0c, hw0h, hw1, hw1h,
       hw2, hw2h, hw3, hw3h, hw4, hw4h, hw5, hw5h, hoc, hoh⟩
      (transitionInput_head_ge inp hinp0)
  · rw [hoc]
    simp [Tape.init]
  · intro j hj
    rw [hoc]
    simp [Tape.init, show j ≠ 0 by omega]

-- ════════════════════════════════════════════════════════════════════════
-- Phase 3: the clocked loop (both exit cases)
-- ════════════════════════════════════════════════════════════════════════

/-- The clocked loop phase, case A: the interpreted machine halts at `mcF`
    within `T ≤ V` steps; the loop exits with the clock at `V - max T 1`. -/
private theorem loopPhase_halt (α x : List Bool) (hterm : TerminatedRegion α)
    (V T : ℕ) (mcF : Cfg 1 (decodeDesc α).toTM.Q) (hTV : T ≤ V)
    (hrun : (decodeDesc α).toTM.reachesIn T ((decodeDesc α).toTM.initCfg x) mcF)
    (hhalt : (decodeDesc α).toTM.halted mcF) :
    clockedLoop.HoareTime (loopPre α x V) (loopExit α x mcF (V - max T 1))
      ((V + 1) * (utmStepTime α + 10)) := by
  rintro inp work out ⟨hic, hinv, hckc, hckh, h0, hns, hoh⟩
  obtain ⟨c', t, ht, hr, hh, hsi', hckc', hckh', h0', hns', hoh', hone'⟩ :=
    (clocked_loop_simulates α x hterm V inp work out hinv hckc hckh
      h0 hns hoh).1 T mcF hTV hrun hhalt
  refine ⟨c', t, le_trans ht (Nat.mul_le_mul_right _ (by omega)), hr, hh,
    (reachesIn_input_cells hr).trans hic,
    hsi', hckc', hckh', h0', hns', hoh', hone'⟩

/-- The clocked loop phase, case B: the interpreted machine is still
    running at `mcV` after `V ≥ 1` steps; the loop exits with the clock
    exhausted. -/
private theorem loopPhase_timeout (α x : List Bool) (hterm : TerminatedRegion α)
    (V : ℕ) (hV : 1 ≤ V) (mcV : Cfg 1 (decodeDesc α).toTM.Q)
    (hrun : (decodeDesc α).toTM.reachesIn V ((decodeDesc α).toTM.initCfg x) mcV)
    (hnh : ¬(decodeDesc α).toTM.halted mcV) :
    clockedLoop.HoareTime (loopPre α x V) (loopExit α x mcV 0)
      ((V + 1) * (utmStepTime α + 10)) := by
  rintro inp work out ⟨hic, hinv, hckc, hckh, h0, hns, hoh⟩
  obtain ⟨c', t, ht, hr, hh, hsi', hckc', hckh', h0', hns', hoh', hone'⟩ :=
    (clocked_loop_simulates α x hterm V inp work out hinv hckc hckh
      h0 hns hoh).2 mcV hV hrun hnh
  refine ⟨c', t, ht, hr, hh,
    (reachesIn_input_cells hr).trans hic,
    hsi', hckc', ?_, h0', hns', hoh', hone'⟩
  rw [hckh']
  exact (max_eq_right (Nat.zero_le 1)).symm

/-- Seam loop → branch phase: the transition is the identity on the parked
    loop-exit tapes. -/
private theorem loopSeam (α x : List Bool) (mc : Cfg 1 (decodeDesc α).toTM.Q)
    (v : ℕ) :
    ∀ inp work out, loopExit α x mc v inp work out →
      loopExit α x mc v (transitionInput inp)
        (fun i => transitionTape (work i)) (transitionTape out) := by
  rintro inp work out ⟨hic, hsi, hckc, hckh, h0, hns, hoh, hone⟩
  have h1 : transitionInput inp = inp := transitionInput_eq_self hsi.inp_read
  have h2 : (fun i => transitionTape (work i)) = work :=
    funext fun i => transitionTape_eq_self (work7_reads' hsi hckc hckh i)
  have h3 : transitionTape out = out := transitionTape_eq_self hsi.out_read
  rw [h1, h2, h3]
  exact ⟨hic, hsi, hckc, hckh, h0, hns, hoh, hone⟩

-- ════════════════════════════════════════════════════════════════════════
-- Phase 4a: the lifted halt test (the `ifTM` test)
-- ════════════════════════════════════════════════════════════════════════

/-- The lifted halt-test phase: from the loop-exit shape, write the
    interpreted halt verdict at output cell 1 with everything else exactly
    preserved (`haltTestTM_hoareTime` through the frame rule, converted by
    `simInv_verdict`). -/
private theorem testPhase (α x : List Bool) (mc : Cfg 1 (decodeDesc α).toTM.Q)
    (v : ℕ) :
    (haltTestTM.liftTM 1).HoareTime (loopExit α x mc v) (testExit α x mc v)
      (4 * (groupPairs α).length + 12) := by
  rintro inp work out ⟨hic, hsi, hckc, hckh, hoc0, hons, hoh, -⟩
  obtain ⟨S, hSh, hSnb, hSlen, hSiff⟩ := simInv_verdict_len'' α mc hsi
  have h6 := haltTestTM_hoareTime S (groupPairs α) hSnb inp
    (fun k : Fin 6 => work (Fin.castAdd 1 k)) out
    hSh hsi.state_head hsi.desc hsi.desc_head hoc0 hons hoh hsi.inp_read
    (fun k h3 h4 => hsi.others_read k h3 h4)
  have hex : ∀ j : Fin 1, 1 ≤ (work clkT).head ∧ (work clkT).read ≠ Γ.start :=
    fun _ => ⟨by rw [hckh]; exact le_max_right v 1,
      clk_read_ne_start' hckc hckh⟩
  obtain ⟨c', t, ht, hr, hh, ⟨hin', hwoth, hw3, hw4, hoc', hoh'⟩, hpin⟩ :=
    liftTM_hoareTime_frame haltTestTM (fun _ : Fin 1 => work clkT) hex h6
      inp work out ⟨⟨rfl, rfl, rfl⟩, fun j => congrArg work (natAdd_eq_clkT' j)⟩
  -- the six embedded tapes are exactly restored
  have hwproj : (fun k : Fin 6 => c'.work (Fin.castAdd 1 k))
      = fun k : Fin 6 => work (Fin.castAdd 1 k) := by
    funext k
    by_cases h3 : k = 3
    · subst h3; exact hw3
    · by_cases h4 : k = 4
      · subst h4; exact hw4
      · exact hwoth k h3 h4
  -- the clock tape is exactly preserved
  have hwclk : c'.work clkT = work clkT := by
    have h := hpin ⟨0, Nat.zero_lt_one⟩
    rwa [natAdd_eq_clkT'] at h
  -- the written verdict is the interpreted halt test's
  have hvd : (if S = (takeField (takeField (groupPairs α)).2).1
        then Γ.one else Γ.zero)
      = (if mc.state = (decodeDesc α).toTM.qhalt then Γ.one else Γ.zero) := by
    by_cases hq : mc.state = (decodeDesc α).toTM.qhalt
    · rw [ite_eq_left hq, ite_eq_left
        (show S = (takeField (takeField (groupPairs α)).2).1 from hSiff.mpr hq)]
    · rw [ite_eq_right hq, ite_eq_right
        (show ¬S = (takeField (takeField (groupPairs α)).2).1 from
          fun hc => hq (hSiff.mp hc))]
  have hoc1' : c'.output.cells 1
      = (if mc.state = (decodeDesc α).toTM.qhalt then Γ.one else Γ.zero) := by
    rw [hoc', Function.update_self]
    exact hvd
  have hor' : c'.output.read ≠ Γ.start := by
    rw [Tape.read, hoh', hoc1']
    split <;> simp
  refine ⟨c', t, by omega, hr, hh, by rw [hin']; exact hic, ?_, ?_, ?_, ?_, ?_,
    hoh', hoc1'⟩
  · rw [hin', hwproj]
    exact simInv_with_out' hsi hor'
  · rw [hwclk]
    exact hckc
  · rw [hwclk]
    exact hckh
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

-- ════════════════════════════════════════════════════════════════════════
-- `ifTM` side conditions on the test's exit shape
-- ════════════════════════════════════════════════════════════════════════

/-- The test-exit shape is well-formed on every tape (for the `ifTM`
    rewind bookkeeping). -/
private theorem testExit_allWF (α x : List Bool)
    (mc : Cfg 1 (decodeDesc α).toTM.Q) (v : ℕ) :
    ∀ inp work out, testExit α x mc v inp work out →
      AllTapesWF inp work out := by
  rintro inp work out ⟨hic, hsi, hckc, hckh, h0, hns, -, -⟩
  refine ⟨?_, ?_, ?_, ?_, h0, hns⟩
  · rw [hic]
    simp [Tape.init]
  · intro j hj
    rw [hic]
    exact (Tape.StartInvariant.init_ofBool (pair α x)).2 j hj
  · intro i
    by_cases hi : i = clkT
    · subst hi
      rw [hckc]
      rfl
    · exact (simInv_work_wf α hsi ⟨i.val, val_lt_of_ne_clkT' hi⟩).1
  · intro i j hj
    by_cases hi : i = clkT
    · subst hi
      rw [hckc]
      exact regCells_ne_start hj
    · exact (simInv_work_wf α hsi ⟨i.val, val_lt_of_ne_clkT' hi⟩).2 j hj

/-- The test leaves the output head at cell 1. -/
private theorem testExit_head (α x : List Bool)
    (mc : Cfg 1 (decodeDesc α).toTM.Q) (v : ℕ) :
    ∀ inp work out, testExit α x mc v inp work out → out.head ≤ 1 := by
  rintro inp work out ⟨-, -, -, -, -, -, hoh, -⟩
  exact le_of_eq hoh

/-- Branch routing: the `ifTM` check transition (identity on the parked
    tapes, output head reset to 1) turns the test-exit shape into the
    branch precondition. Shared by both branches — the verdict value is
    irrelevant here. -/
private theorem testExit_to_branch (α x : List Bool)
    (mc : Cfg 1 (decodeDesc α).toTM.Q) (v : ℕ) :
    ∀ inp work out, testExit α x mc v inp work out →
      branchPre α mc v (transitionInput inp)
        (fun i => transitionTape (work i)) ⟨1, out.cells⟩ := by
  rintro inp work out ⟨-, hsi, hckc, hckh, h0, hns, -, -⟩
  have h1 : transitionInput inp = inp := transitionInput_eq_self hsi.inp_read
  have h2 : (fun i => transitionTape (work i)) = work :=
    funext fun i => transitionTape_eq_self (work7_reads' hsi hckc hckh i)
  rw [h1, h2]
  have hread : (⟨1, out.cells⟩ : Tape).read ≠ Γ.start := by
    show out.cells 1 ≠ Γ.start
    exact hns 1 le_rfl
  exact ⟨simInv_with_out' hsi hread, hckc, hckh, h0, hns, rfl⟩

-- ════════════════════════════════════════════════════════════════════════
-- Phase 4b: the lifted extract (the `ifTM` then-branch, case A)
-- ════════════════════════════════════════════════════════════════════════

/-- The lifted extract phase: from the branch precondition at the halted
    configuration `mcF`, copy the virtual output tape (work 2, through the
    `VShift` bridge) onto the real output tape, cells `1 … m + 1`. -/
private theorem extractPhase (α x : List Bool) (V T m v : ℕ)
    (mcF : Cfg 1 (decodeDesc α).toTM.Q)
    (hmT : m ≤ T) (hTV : T ≤ V)
    (hrun : (decodeDesc α).toTM.reachesIn T ((decodeDesc α).toTM.initCfg x) mcF)
    (hmb : mcF.output.cells (m + 1) = Γ.blank)
    (hmnb : ∀ j, j < m → mcF.output.cells (j + 1) ≠ Γ.blank) :
    (extractTM.liftTM 1).HoareTime (branchPre α mcF v)
      (fun _ _ out => ∀ j, j ≤ m → out.cells (j + 1) = mcF.output.cells (j + 1))
      (2 * V + 9) := by
  rintro inp work out ⟨hsi, hckc, hckh, h0, hns, hoh⟩
  -- the virtual-output shift bridge
  have hvout : VShift mcF.output (work (Fin.castAdd 1 2)) := hsi.vout
  have hcells2 : ∀ k, (work (Fin.castAdd 1 2)).cells (k + 2)
      = mcF.output.cells (k + 1) := by
    intro k
    rw [hvout.1]
    simp only [show ¬(k + 2 = 0) by omega, show ¬(k + 2 = 1) by omega,
      ite_false, show k + 2 - 1 = k + 1 by omega]
  have hblank2 : (work (Fin.castAdd 1 2)).cells (m + 2) = Γ.blank := by
    rw [hcells2 m]
    exact hmb
  have hnb2 : ∀ j, j < m → (work (Fin.castAdd 1 2)).cells (j + 2) ≠ Γ.blank := by
    intro j hj
    rw [hcells2 j]
    exact hmnb j hj
  have hwf2 : (work (Fin.castAdd 1 2)).StartInvariant := hvout.startInvariant hsi.wf_out
  have hheadF : mcF.output.head ≤ T := by
    have h := reachesIn_output_head_le hrun
    have h0' : ((decodeDesc α).toTM.initCfg x).output.head = 0 := rfl
    omega
  have hhead2 : (work (Fin.castAdd 1 2)).head ≤ V + 1 := by
    have h := hvout.head_eq
    omega
  -- the 6-tape ghost triple, lifted with the clock pinned
  have h6 := extractTM_hoareTime m (V + 1) inp
    (fun k : Fin 6 => work (Fin.castAdd 1 k)) out
    hblank2 hnb2 hwf2 hhead2 hvout.head_pos h0 hns hoh hsi.inp_read
    (fun i _ => simInv_work_reads'' α hsi i)
  have hex : ∀ j : Fin 1, 1 ≤ (work clkT).head ∧ (work clkT).read ≠ Γ.start :=
    fun _ => ⟨by rw [hckh]; exact le_max_right v 1,
      clk_read_ne_start' hckc hckh⟩
  obtain ⟨c', t, ht, hr, hh, ⟨hin', hwoth, hw2c, hocopy⟩, hpin⟩ :=
    liftTM_hoareTime_frame extractTM (fun _ : Fin 1 => work clkT) hex h6
      inp work out ⟨⟨rfl, rfl, rfl⟩, fun j => congrArg work (natAdd_eq_clkT' j)⟩
  refine ⟨c', t, by omega, hr, hh, ?_⟩
  intro j hj
  rw [hocopy j hj, hcells2 j]

-- ════════════════════════════════════════════════════════════════════════
-- The headline theorems
-- ════════════════════════════════════════════════════════════════════════

/-- **The clocked universal machine, halting case.** On the started tapes
    `clockedUtmPre α x V`, if the interpreted machine `(decodeDesc α).toTM`
    halts on `x` at `mcF` within `T ≤ V` steps, then `clockedUtmTM` halts
    within `clockedUtmTime α x V` steps with its real output tape agreeing
    with `mcF`'s output tape through the latter's first blank — i.e. the
    clocked UTM computes exactly the simulated machine's output. -/
theorem clockedUtmTM_hoareTime_halt (α x : List Bool)
    (hterm : TerminatedRegion α)
    (V T : ℕ) (mcF : Cfg 1 (decodeDesc α).toTM.Q) (hTV : T ≤ V)
    (hrun : (decodeDesc α).toTM.reachesIn T ((decodeDesc α).toTM.initCfg x) mcF)
    (hhalt : (decodeDesc α).toTM.halted mcF) :
    clockedUtmTM.HoareTime (clockedUtmPre α x V)
      (fun _ _ out => ∃ m, m ≤ T ∧
        mcF.output.cells (m + 1) = Γ.blank ∧
        (∀ j, j < m → mcF.output.cells (j + 1) ≠ Γ.blank) ∧
        (∀ j, j ≤ m → out.cells (j + 1) = mcF.output.cells (j + 1)))
      (clockedUtmTime α x V) := by
  obtain ⟨m, hmT, hmb, hmnb⟩ := output_first_blank_shift' hrun
  -- ── the then-branch: extract the simulated output ──
  have h_then : (extractTM.liftTM 1).HoareTime (branchPre α mcF (V - max T 1))
      (fun _ _ out =>
        (∀ j, j ≤ m → out.cells (j + 1) = mcF.output.cells (j + 1)) ∧
        out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start))
      (2 * V + 9) := by
    refine HoareTime.with_output_wf
      (extractPhase α x V T m (V - max T 1) mcF hmT hTV hrun hmb hmnb) ?_
    rintro inp work out ⟨-, -, -, h0, hns, -⟩
    exact ⟨h0, hns⟩
  -- ── the else-branch is vacuous: the halt test reports `Γ.one` ──
  have h_else : (writeTM Γw.one : TM 7).HoareTime (fun _ _ _ => False)
      (fun _ _ _ => False) (2 * V + 9) := fun _ _ _ h => h.elim
  -- ── the if phase ──
  have h_if : (ifTM (haltTestTM.liftTM 1) (extractTM.liftTM 1)
      (writeTM Γw.one)).HoareTime (loopExit α x mcF (V - max T 1))
      (fun _ _ out => ∃ m', m' ≤ T ∧
        mcF.output.cells (m' + 1) = Γ.blank ∧
        (∀ j, j < m' → mcF.output.cells (j + 1) ≠ Γ.blank) ∧
        (∀ j, j ≤ m' → out.cells (j + 1) = mcF.output.cells (j + 1)))
      (4 * (groupPairs α).length + 12 + 1 + (2 * V + 9) + 5) := by
    refine HoareTime.mono_bound
      (ifTM_hoareTime (haltTestTM.liftTM 1) (extractTM.liftTM 1)
        (writeTM Γw.one)
        (testPhase α x mcF (V - max T 1))
        (testExit_allWF α x mcF (V - max T 1))
        (testExit_head α x mcF (V - max T 1)) ?_ ?_ h_then h_else ?_ ?_)
      (le_of_eq (by rw [Nat.max_self]))
    · -- test → then routing
      rintro inp work out htest -
      exact testExit_to_branch α x mcF (V - max T 1) inp work out htest
    · -- test → else routing: vacuous (the verdict is `Γ.one`)
      rintro inp work out ⟨-, -, -, -, -, -, -, hcell1⟩ hne
      rw [ite_eq_left hhalt] at hcell1
      exact absurd hcell1 hne
    · -- then-branch post survives the final transition (output WF)
      rintro inp work out ⟨hcopy, h0, hns⟩
      refine ⟨m, hmT, hmb, hmnb, ?_⟩
      intro j hj
      rw [transitionTape_cells out hns]
      exact hcopy j hj
    · -- else-branch post: vacuous
      exact fun _ _ _ h => h.elim
  -- ── assemble the four phases ──
  refine HoareTime.mono_bound
    (seqTM_hoareTime (initTM.liftTM 1) _ (initPhase α x V) (initSeam α x V)
      (seqTM_hoareTime seekFrontierTM _ (seekPhase α x V) (seekSeam α x V)
        (seqTM_hoareTime clockedLoop _
          (loopPhase_halt α x hterm V T mcF hTV hrun hhalt)
          (loopSeam α x mcF (V - max T 1)) h_if))) ?_
  unfold clockedUtmTime
  generalize (V + 1) * (utmStepTime α + 10) = L
  omega

/-- **The clocked universal machine, timeout case.** On the started tapes
    `clockedUtmPre α x V`, if the interpreted machine `(decodeDesc α).toTM`
    is still running after `V ≥ 1` steps on `x`, then `clockedUtmTM` halts
    within `clockedUtmTime α x V` steps with the timeout sentinel `Γ.one`
    at output cell 1. -/
theorem clockedUtmTM_hoareTime_timeout (α x : List Bool)
    (hterm : TerminatedRegion α)
    (V : ℕ) (hV : 1 ≤ V) (mcV : Cfg 1 (decodeDesc α).toTM.Q)
    (hrun : (decodeDesc α).toTM.reachesIn V ((decodeDesc α).toTM.initCfg x) mcV)
    (hnh : ¬(decodeDesc α).toTM.halted mcV) :
    clockedUtmTM.HoareTime (clockedUtmPre α x V)
      (fun _ _ out => out.cells 1 = Γ.one)
      (clockedUtmTime α x V) := by
  -- ── the then-branch is vacuous: the halt test reports `Γ.zero` ──
  have h_then : (extractTM.liftTM 1).HoareTime (fun _ _ _ => False)
      (fun _ _ _ => False) (2 * V + 9) := fun _ _ _ h => h.elim
  -- ── the else-branch: write the timeout sentinel at output cell 1 ──
  have h_else : (writeTM Γw.one).HoareTime (branchPre α mcV 0)
      (fun _ _ out => out.cells 1 = Γw.one.toΓ ∧
        out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start))
      (2 * V + 9) := by
    refine HoareTime.mono_bound (HoareTime.with_output_wf
      ((writeTM_hoareTime Γw.one 1).weaken_pre ?_) ?_) (by omega)
    · rintro inp work out ⟨-, -, -, h0, hns, hoh⟩
      exact ⟨h0, hns, le_of_eq hoh⟩
    · rintro inp work out ⟨-, -, -, h0, hns, -⟩
      exact ⟨h0, hns⟩
  -- ── the if phase ──
  have h_if : (ifTM (haltTestTM.liftTM 1) (extractTM.liftTM 1)
      (writeTM Γw.one)).HoareTime (loopExit α x mcV 0)
      (fun _ _ out => out.cells 1 = Γ.one)
      (4 * (groupPairs α).length + 12 + 1 + (2 * V + 9) + 5) := by
    refine HoareTime.mono_bound
      (ifTM_hoareTime (haltTestTM.liftTM 1) (extractTM.liftTM 1)
        (writeTM Γw.one)
        (testPhase α x mcV 0) (testExit_allWF α x mcV 0)
        (testExit_head α x mcV 0) ?_ ?_ h_then h_else ?_ ?_)
      (le_of_eq (by rw [Nat.max_self]))
    · -- test → then routing: vacuous (the verdict is `Γ.zero`)
      rintro inp work out ⟨-, -, -, -, -, -, -, hcell1⟩ hone
      rw [hcell1, ite_eq_right hnh] at hone
      exact absurd hone (by decide)
    · -- test → else routing
      rintro inp work out htest -
      exact testExit_to_branch α x mcV 0 inp work out htest
    · -- then-branch post: vacuous
      exact fun _ _ _ h => h.elim
    · -- else-branch post survives the final transition (output WF)
      rintro inp work out ⟨h1, h0, hns⟩
      rw [transitionTape_cells out hns]
      exact h1
  -- ── assemble the four phases ──
  refine HoareTime.mono_bound
    (seqTM_hoareTime (initTM.liftTM 1) _ (initPhase α x V) (initSeam α x V)
      (seqTM_hoareTime seekFrontierTM _ (seekPhase α x V) (seekSeam α x V)
        (seqTM_hoareTime clockedLoop _
          (loopPhase_timeout α x hterm V hV mcV hrun hnh)
          (loopSeam α x mcV 0) h_if))) ?_
  unfold clockedUtmTime
  generalize (V + 1) * (utmStepTime α + 10) = L
  omega

end TM.UTMBody

end Complexity
