/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Internal.BodyIteration
public import Complexitylib.Models.TuringMachine.UTM.Internal.Sim
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Loop
public import Complexitylib.Models.TuringMachine.Hoare
public import Complexitylib.Models.TuringMachine.UTM.Machine
public import Mathlib.Tactic.Ring.RingNF

/-!
# Universal machine: the simulate/halt-test loop

The headline correctness theorem for the UTM's main loop
`loopTM bodyTM haltTestTM`: if the interpreted machine
`(decodeDesc α).toTM` halts on `x` in `T` steps at the configuration
`mcF`, then from any tapes realizing the standing invariant `SimInv` at
the interpreted machine's initial configuration (output tape cleared,
head parked at cell 1), the loop halts within `(T + 1) * utmStepTime α`
steps with `SimInv` re-established at `mcF` and the halt verdict `Γ.one`
at output cell 1.

## Proof structure

One loop iteration = one interpreted step:

* `bodyIteration` runs one body pass (`SimInv` at `mc` ↦ `SimInv` at
  `(decodeDesc α).toTM.step mc`, or an exact no-op when halted);
* the body→test / test→rewind combinator transitions apply
  `transitionInput`/`transitionTape` to every tape — literal identities
  here, since every `SimInv` tape is parked (head ≥ 1, read ≠ `▷`);
* `haltTestTM_hoareTime` compares the state tape against the
  description's qhalt field, writing the verdict at output cell 1;
  `simInv_verdict` identifies the comparison with the interpreted halt
  test;
* the rewind/check bookkeeping (3 steps, output head 1 → 0 → 1) either
  halts the loop (verdict `Γ.one`) or returns to the loop start with the
  invariant re-established (`loopTM_rewind_check` below).

The outer induction (`loop_sim_aux`) is a strong induction on the
remaining fuel `T - t'` rather than an instance of `loopTM_hoareTime`:
the loop variant would have to be a *function* of the tapes, while here
it is determined only through the existentially quantified prefix run of
the interpreted machine. Determinism of `reachesIn` plus the
halted-configurations-don't-step principle (`TM.reachesIn_le_halt`)
identify the loop's exit configuration with `mcF`.
-/


@[expose] public section

namespace Complexity

namespace TM.UTMBody

-- ════════════════════════════════════════════════════════════════════════
-- Generic `reachesIn` helpers
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
-- Description-field length bookkeeping
-- ════════════════════════════════════════════════════════════════════════

private theorem takeField_fst_length_le' (l : List Γw) :
    (takeField l).1.length ≤ l.length := by
  rcases takeField_structure l with hsp | ⟨hsp, -⟩
  · have := congrArg List.length hsp
    simp only [List.length_append, List.length_cons] at this
    omega
  · exact le_of_eq (congrArg List.length hsp)

private theorem qhaltField_length_le' (l : List Γw) :
    (qhaltField l).length ≤ l.length :=
  le_trans (takeField_fst_length_le' (takeField l).2) (takeField_rest_length l)

-- ════════════════════════════════════════════════════════════════════════
-- SimInv bookkeeping
-- ════════════════════════════════════════════════════════════════════════

/-- Every work tape of a `SimInv` configuration is parked: it reads a
    non-`▷` symbol. -/
private theorem simInv_work_reads (α : List Bool) {mc : Cfg 1 (decodeDesc α).toTM.Q}
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

/-- `simInv_verdict`, strengthened with the length bound needed for the
    halt test's time accounting. -/
private theorem simInv_verdict_len (α : List Bool) (mc : Cfg 1 (decodeDesc α).toTM.Q)
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
      exact takeField_fst_length_le' _
    · exact qhaltField_length_le' _
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

-- ════════════════════════════════════════════════════════════════════════
-- The loop's rewind/check bookkeeping (3 steps from output head 1)
-- ════════════════════════════════════════════════════════════════════════

/-- From the loop's rewind state with the output head at cell 1 and every
    tape parked, three steps (rewind to `▷`, bounce to cell 1, check) reach
    the branch decision: the loop's `done` state if output cell 1 reads
    `Γ.one`, else the body's start state. All tapes are exactly
    preserved. -/
private theorem loopTM_rewind_check {n : ℕ} (tmBody tmTest : TM n)
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
-- One loop iteration
-- ════════════════════════════════════════════════════════════════════════

/-- Per-`α` time cost of one iteration of the UTM's simulate/halt-test
    loop: one body pass, the two combinator transitions, the halt test,
    and the loop's rewind/check bookkeeping. -/
def utmStepTime (α : List Bool) : ℕ :=
  bodyIterTime α + 4 * (groupPairs α).length + 20

/-- **One iteration of the UTM loop** interprets one step of the simulated
    machine. From the loop's start state under `SimInv` at `mc` (output
    parked at cell 1), within `utmStepTime α` steps the loop either

    * halts (the fresh verdict at output cell 1 is `Γ.one`) — exactly when
      the post-step configuration `mc₂` is halted — or
    * returns to the loop's start state with `SimInv` at `mc₂` and the
      output tape again parked,

    where `mc₂` is `(decodeDesc α).toTM.step mc` when defined and `mc`
    itself otherwise. The input tape is untouched throughout. -/
private theorem loop_iteration (α : List Bool) (hterm : TerminatedRegion α)
    (mc : Cfg 1 (decodeDesc α).toTM.Q)
    (inp : Tape) (work : Fin 6 → Tape) (out : Tape)
    (hinv : SimInv α mc inp work out)
    (hout0 : out.cells 0 = Γ.start)
    (houtns : ∀ j, 1 ≤ j → out.cells j ≠ Γ.start)
    (houth : out.head = 1) :
    ∃ (mc₂ : Cfg 1 (decodeDesc α).toTM.Q) (work' : Fin 6 → Tape) (out' : Tape)
      (t : ℕ),
      t ≤ utmStepTime α ∧
      ((decodeDesc α).toTM.step mc = some mc₂ ∨
        ((decodeDesc α).toTM.step mc = none ∧ mc₂ = mc)) ∧
      SimInv α mc₂ inp work' out' ∧
      out'.cells 0 = Γ.start ∧
      (∀ j, 1 ≤ j → out'.cells j ≠ Γ.start) ∧
      out'.head = 1 ∧
      ((mc₂.state = (decodeDesc α).toTM.qhalt ∧
        out'.cells 1 = Γ.one ∧
        (loopTM bodyTM haltTestTM).reachesIn t
          ⟨(loopTM bodyTM haltTestTM).qstart, inp, work, out⟩
          ⟨Sum.inr (Sum.inl LoopPhase.done), inp, work', out'⟩) ∨
       (mc₂.state ≠ (decodeDesc α).toTM.qhalt ∧
        (loopTM bodyTM haltTestTM).reachesIn t
          ⟨(loopTM bodyTM haltTestTM).qstart, inp, work, out⟩
          ⟨(loopTM bodyTM haltTestTM).qstart, inp, work', out'⟩)) := by
  -- ── the body pass ──
  obtain ⟨cb, t_body, ht_body, hr_body, hst_body, hin_body, hout_body, hmatch⟩ :=
    bodyIteration α mc hterm ⟨BodyQ.hc0, inp, work, out⟩ rfl hinv
  -- unify the halted/running cases of the body's conclusion
  obtain ⟨mc₂, hstepd, hinv₂⟩ :
      ∃ mc₂, ((decodeDesc α).toTM.step mc = some mc₂ ∨
        ((decodeDesc α).toTM.step mc = none ∧ mc₂ = mc)) ∧
        SimInv α mc₂ inp cb.work out := by
    cases hse : (decodeDesc α).toTM.step mc with
    | none =>
      rw [hse] at hmatch
      have hw : cb.work = work := funext hmatch
      exact ⟨mc, Or.inr ⟨rfl, rfl⟩, hw ▸ hinv⟩
    | some mc' =>
      rw [hse] at hmatch
      dsimp only at hmatch
      rw [hin_body, hout_body] at hmatch
      exact ⟨mc', Or.inl rfl, hmatch⟩
  -- parked reads
  have hinp_read : inp.read ≠ Γ.start := hinv.inp_read
  have hout_read : out.read ≠ Γ.start := hinv.out_read
  have hwreads₂ : ∀ i : Fin 6, (cb.work i).read ≠ Γ.start :=
    simInv_work_reads α hinv₂
  -- ── the halt test ──
  obtain ⟨S, hSh, hSnb, hSlen, hSiff⟩ := simInv_verdict_len α mc₂ hinv₂
  obtain ⟨ct, t_test, ht_test, hr_test, hthalt, htin, htoth, ht3, ht4, htoc, htoh⟩ :=
    haltTestTM_hoareTime S (groupPairs α) hSnb inp cb.work out
      hSh hinv₂.state_head hinv₂.desc hinv₂.desc_head
      hout0 houtns houth hinp_read
      (fun i h3 h4 => hinv₂.others_read i h3 h4)
      inp cb.work out ⟨rfl, rfl, rfl⟩
  have htwork : ct.work = cb.work := by
    funext i
    by_cases h3 : i = 3
    · subst h3; exact ht3
    · by_cases h4 : i = 4
      · subst h4; exact ht4
      · exact htoth i h3 h4
  -- the written verdict is the interpreted halt test's
  have hvd : (if S = (takeField (takeField (groupPairs α)).2).1
        then Γ.one else Γ.zero)
      = (if mc₂.state = (decodeDesc α).toTM.qhalt then Γ.one else Γ.zero) := by
    by_cases h : mc₂.state = (decodeDesc α).toTM.qhalt
    · rw [ite_eq_left h, ite_eq_left
        (show S = (takeField (takeField (groupPairs α)).2).1 from hSiff.mpr h)]
    · rw [ite_eq_right h, ite_eq_right
        (show ¬S = (takeField (takeField (groupPairs α)).2).1 from
          fun hc => h (hSiff.mp hc))]
  have hcell1 : ct.output.cells 1
      = (if mc₂.state = (decodeDesc α).toTM.qhalt then Γ.one else Γ.zero) := by
    rw [htoc, Function.update_self]
    exact hvd
  have hctout_read : ct.output.read ≠ Γ.start := by
    rw [Tape.read, htoh, htoc, Function.update_self]
    split <;> simp
  have hctoc0 : ct.output.cells 0 = Γ.start := by
    rw [htoc, Function.update_of_ne (by omega : (0 : ℕ) ≠ 1)]
    exact hout0
  have hctons : ∀ j, 1 ≤ j → ct.output.cells j ≠ Γ.start := by
    intro j hj
    rw [htoc]
    by_cases hj1 : j = 1
    · subst hj1
      rw [Function.update_self]
      split <;> simp
    · rw [Function.update_of_ne hj1]
      exact houtns j hj
  -- ── the loop-level run ──
  -- body simulation
  have hr₁ : (loopTM bodyTM haltTestTM).reachesIn t_body
      (loopBodyWrap bodyTM haltTestTM ⟨BodyQ.hc0, inp, work, out⟩)
      (loopBodyWrap bodyTM haltTestTM cb) :=
    loopTM_body_simulation bodyTM haltTestTM hr_body
  -- body → test transition (an identity on all tapes)
  have hcfg : (⟨haltTestTM.qstart, transitionInput cb.input,
        fun i => transitionTape (cb.work i), transitionTape cb.output⟩ :
          Cfg 6 haltTestTM.Q)
      = ⟨haltTestTM.qstart, inp, cb.work, out⟩ := by
    have h1 : transitionInput cb.input = inp := by
      rw [hin_body]
      exact transitionInput_eq_self hinp_read
    have h2 : (fun i => transitionTape (cb.work i)) = cb.work :=
      funext fun i => transitionTape_eq_self (hwreads₂ i)
    have h3 : transitionTape cb.output = out := by
      rw [hout_body]
      exact transitionTape_eq_self hout_read
    rw [h1, h2, h3]
  have hbt := loopTM_body_to_test bodyTM haltTestTM
    (show cb.state = bodyTM.qhalt from hst_body)
  rw [hcfg] at hbt
  -- test simulation
  have hr₃ : (loopTM bodyTM haltTestTM).reachesIn t_test
      (loopTestWrap bodyTM haltTestTM ⟨haltTestTM.qstart, inp, cb.work, out⟩)
      (loopTestWrap bodyTM haltTestTM ct) :=
    loopTM_test_simulation bodyTM haltTestTM hr_test
  -- test → rewind transition (an identity on all tapes)
  have hcfg₂ : (⟨(Sum.inr (Sum.inl LoopPhase.rewindOut) :
          LoopQ bodyTM.Q haltTestTM.Q), transitionInput ct.input,
        fun i => transitionTape (ct.work i), transitionTape ct.output⟩ :
          Cfg 6 (LoopQ bodyTM.Q haltTestTM.Q))
      = ⟨Sum.inr (Sum.inl LoopPhase.rewindOut), inp, cb.work, ct.output⟩ := by
    have h1 : transitionInput ct.input = inp := by
      rw [htin]
      exact transitionInput_eq_self hinp_read
    have h2 : (fun i => transitionTape (ct.work i)) = cb.work := by
      funext i
      rw [htwork]
      exact transitionTape_eq_self (hwreads₂ i)
    have h3 : transitionTape ct.output = ct.output :=
      transitionTape_eq_self hctout_read
    rw [h1, h2, h3]
  have htr := (loopTM_test_to_rewind bodyTM haltTestTM
    (show ct.state = haltTestTM.qhalt from hthalt)).trans (congrArg some hcfg₂)
  -- rewind + check
  obtain ⟨⟨cfs, cfi, cfw, cfo⟩, hr₅, hstf, hinf, hwkf, houtf⟩ :=
    loopTM_rewind_check bodyTM haltTestTM
      ⟨Sum.inr (Sum.inl LoopPhase.rewindOut), inp, cb.work, ct.output⟩
      rfl hinp_read hwreads₂ htoh hctoc0 hctons
  dsimp only at hstf hinf hwkf houtf
  obtain rfl := hinf.symm
  subst hwkf houtf hstf
  -- assemble the whole run
  have hr_all := reachesIn_trans _ (reachesIn_trans _ (reachesIn_trans _
    (reachesIn_trans _ hr₁ (.step hbt .zero)) hr₃) (.step htr .zero)) hr₅
  -- the invariant at the fresh output tape
  have hinv' : SimInv α mc₂ inp cb.work ct.output :=
    ⟨hinv₂.vin, hinv₂.vwk, hinv₂.vout, hinv₂.wf_in, hinv₂.wf_wk, hinv₂.wf_out,
     hinv₂.state, hinv₂.state_head, hinv₂.desc, hinv₂.desc_head,
     hinv₂.scratch, hinv₂.scratch_head, hinv₂.inp_read, hctout_read⟩
  -- time bound
  have htime : t_body + 1 + t_test + 1 + 3 ≤ utmStepTime α := by
    show _ ≤ bodyIterTime α + 4 * (groupPairs α).length + 20
    omega
  -- branch on the verdict
  by_cases hq : mc₂.state = (decodeDesc α).toTM.qhalt
  · have hone : ct.output.cells 1 = Γ.one := by
      rw [hcell1, ite_eq_left hq]
    rw [ite_eq_left hone] at hr_all
    exact ⟨mc₂, cb.work, ct.output, t_body + 1 + t_test + 1 + 3, htime, hstepd,
      hinv', hctoc0, hctons, htoh, Or.inl ⟨hq, hone, hr_all⟩⟩
  · have hzero : ct.output.cells 1 = Γ.zero := by
      rw [hcell1, ite_eq_right hq]
    have hone_ne : ct.output.cells 1 ≠ Γ.one := by
      rw [hzero]; simp
    rw [ite_eq_right hone_ne] at hr_all
    exact ⟨mc₂, cb.work, ct.output, t_body + 1 + t_test + 1 + 3, htime, hstepd,
      hinv', hctoc0, hctons, htoh, Or.inr ⟨hq, hr_all⟩⟩

-- ════════════════════════════════════════════════════════════════════════
-- The loop simulation, by induction on the remaining fuel
-- ════════════════════════════════════════════════════════════════════════

private theorem loop_sim_aux (α x : List Bool) (hterm : TerminatedRegion α)
    (T : ℕ) (mcF : Cfg 1 (decodeDesc α).toTM.Q)
    (hrun : (decodeDesc α).toTM.reachesIn T ((decodeDesc α).toTM.initCfg x) mcF)
    (hhaltF : (decodeDesc α).toTM.halted mcF) :
    ∀ (fuel t' : ℕ) (mc : Cfg 1 (decodeDesc α).toTM.Q)
      (inp : Tape) (work : Fin 6 → Tape) (out : Tape),
      t' + fuel = T →
      (decodeDesc α).toTM.reachesIn t' ((decodeDesc α).toTM.initCfg x) mc →
      SimInv α mc inp work out →
      out.cells 0 = Γ.start →
      (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) →
      out.head = 1 →
      ∃ c' t, t ≤ (fuel + 1) * utmStepTime α ∧
        (loopTM bodyTM haltTestTM).reachesIn t
          ⟨(loopTM bodyTM haltTestTM).qstart, inp, work, out⟩ c' ∧
        (loopTM bodyTM haltTestTM).halted c' ∧
        SimInv α mcF c'.input c'.work c'.output ∧
        c'.output.cells 0 = Γ.start ∧
        (∀ j, 1 ≤ j → c'.output.cells j ≠ Γ.start) ∧
        c'.output.head = 1 ∧
        c'.output.cells 1 = Γ.one := by
  intro fuel
  induction fuel with
  | zero =>
    intro t' mc inp work out hT hreach hinv hout0 houtns houth
    -- out of fuel: the interpreted run is complete, `mc = mcF`
    have ht'T : t' = T := by omega
    subst ht'T
    obtain rfl : mc = mcF := TM.reachesIn_right_unique hreach hrun
    obtain ⟨mc₂, work', out', t, ht, hstepd, hinv', hoc0', hons', hoh', hbranch⟩ :=
      loop_iteration α hterm mc inp work out hinv hout0 houtns houth
    rcases hstepd with hsome | ⟨-, rfl⟩
    · exact absurd hsome (by
        simp [TM.step,
          show mc.state = (decodeDesc α).toTM.qhalt from hhaltF])
    · rcases hbranch with ⟨-, hone, hr⟩ | ⟨hq, -⟩
      · exact ⟨⟨Sum.inr (Sum.inl LoopPhase.done), inp, work', out'⟩, t,
          by omega, hr, rfl, hinv', hoc0', hons', hoh', hone⟩
      · exact absurd hhaltF hq
  | succ fuel ih =>
    intro t' mc inp work out hT hreach hinv hout0 houtns houth
    obtain ⟨mc₂, work', out', t, ht, hstepd, hinv', hoc0', hons', hoh', hbranch⟩ :=
      loop_iteration α hterm mc inp work out hinv hout0 houtns houth
    rcases hbranch with ⟨hq, hone, hr⟩ | ⟨hq, hr⟩
    · -- the loop exits: identify the exit configuration with `mcF`
      have hmul : utmStepTime α ≤ (fuel + 1 + 1) * utmStepTime α := by
        calc utmStepTime α = 1 * utmStepTime α := (Nat.one_mul _).symm
          _ ≤ (fuel + 1 + 1) * utmStepTime α := Nat.mul_le_mul_right _ (by omega)
      rcases hstepd with hsome | ⟨hnone, rfl⟩
      · have hreach₂ := reachesIn_snoc hreach hsome
        have hne : mc.state ≠ (decodeDesc α).toTM.qhalt := state_ne_qhalt_of_step hsome
        have hlt : t' < T := by
          rcases Nat.lt_or_ge t' T with h | h
          · exact h
          · exfalso
            have ht'T : t' = T := by omega
            subst ht'T
            obtain rfl : mc = mcF := TM.reachesIn_right_unique hreach hrun
            exact hne hhaltF
        have hTle : T ≤ t' + 1 := TM.reachesIn_le_halt _ hrun hreach₂ hq
        have hTeq : t' + 1 = T := by omega
        rw [hTeq] at hreach₂
        obtain rfl : mc₂ = mcF := TM.reachesIn_right_unique hreach₂ hrun
        exact ⟨⟨Sum.inr (Sum.inl LoopPhase.done), inp, work', out'⟩, t,
          by omega, hr, rfl, hinv', hoc0', hons', hoh', hone⟩
      · -- a halted configuration strictly before `T`: impossible
        exfalso
        have hhalt_mc : (decodeDesc α).toTM.halted mc₂ := state_eq_of_step_none hnone
        have : T ≤ t' := TM.reachesIn_le_halt _ hrun hreach hhalt_mc
        omega
    · -- the loop continues: one interpreted step consumed, recurse
      have hsome : (decodeDesc α).toTM.step mc = some mc₂ := by
        rcases hstepd with h | ⟨hnone, rfl⟩
        · exact h
        · exact absurd (state_eq_of_step_none hnone) hq
      have hreach₂ := reachesIn_snoc hreach hsome
      obtain ⟨c', t₂, ht₂, hr₂, hhalt', hinvF, h0, hns, hh1, hc1⟩ :=
        ih (t' + 1) mc₂ inp work' out' (by omega) hreach₂ hinv' hoc0' hons' hoh'
      refine ⟨c', t + t₂, ?_, reachesIn_trans _ hr hr₂, hhalt', hinvF,
        h0, hns, hh1, hc1⟩
      calc t + t₂ ≤ utmStepTime α + (fuel + 1) * utmStepTime α :=
            Nat.add_le_add ht ht₂
        _ = (fuel + 1 + 1) * utmStepTime α := by ring

-- ════════════════════════════════════════════════════════════════════════
-- The headline loop simulation theorem
-- ════════════════════════════════════════════════════════════════════════

/-- **The UTM loop simulates the interpreted machine.** Suppose
    `(decodeDesc α).toTM` halts on `x` in `T` steps at `mcF`. Then from
    any tapes realizing `SimInv` at the interpreted machine's initial
    configuration — with the output tape `▷`-clean and parked at cell 1 —
    the loop `loopTM bodyTM haltTestTM` halts within
    `(T + 1) * utmStepTime α` steps, with `SimInv` re-established at `mcF`
    (so the virtual output tape shadows the simulated output) and the halt
    verdict `Γ.one` at output cell 1. -/
theorem utm_loop_simulates (α x : List Bool) (hterm : TerminatedRegion α)
    (T : ℕ) (mcF : Cfg 1 (decodeDesc α).toTM.Q)
    (hrun : (decodeDesc α).toTM.reachesIn T ((decodeDesc α).toTM.initCfg x) mcF)
    (hhalt : (decodeDesc α).toTM.halted mcF)
    (inp : Tape) (work : Fin 6 → Tape) (out : Tape)
    (hinv : SimInv α ((decodeDesc α).toTM.initCfg x) inp work out)
    (hout0 : out.cells 0 = Γ.start)
    (houtns : ∀ j, 1 ≤ j → out.cells j ≠ Γ.start)
    (houth : out.head = 1) :
    ∃ c' t, t ≤ (T + 1) * utmStepTime α ∧
      (loopTM bodyTM haltTestTM).reachesIn t
        ⟨(loopTM bodyTM haltTestTM).qstart, inp, work, out⟩ c' ∧
      (loopTM bodyTM haltTestTM).halted c' ∧
      SimInv α mcF c'.input c'.work c'.output ∧
      c'.output.cells 0 = Γ.start ∧
      (∀ j, 1 ≤ j → c'.output.cells j ≠ Γ.start) ∧
      c'.output.head = 1 ∧
      c'.output.cells 1 = Γ.one :=
  loop_sim_aux α x hterm T mcF hrun hhalt T 0
    ((decodeDesc α).toTM.initCfg x) inp work out (by omega) .zero
    hinv hout0 houtns houth

/-- Hoare-style packaging of `utm_loop_simulates`, ready for `seqTM`
    composition with the init and extract phases. -/
theorem utm_loop_hoareTime (α x : List Bool) (hterm : TerminatedRegion α)
    (T : ℕ) (mcF : Cfg 1 (decodeDesc α).toTM.Q)
    (hrun : (decodeDesc α).toTM.reachesIn T ((decodeDesc α).toTM.initCfg x) mcF)
    (hhalt : (decodeDesc α).toTM.halted mcF) :
    (loopTM bodyTM haltTestTM).HoareTime
      (fun inp work out =>
        SimInv α ((decodeDesc α).toTM.initCfg x) inp work out ∧
        out.cells 0 = Γ.start ∧
        (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
        out.head = 1)
      (fun inp work out =>
        SimInv α mcF inp work out ∧
        out.cells 0 = Γ.start ∧
        (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
        out.head = 1 ∧
        out.cells 1 = Γ.one)
      ((T + 1) * utmStepTime α) := by
  rintro inp work out ⟨hinv, hout0, houtns, houth⟩
  obtain ⟨c', t, ht, hr, hh, hinv', h0, hns, hh1, hc1⟩ :=
    utm_loop_simulates α x hterm T mcF hrun hhalt inp work out
      hinv hout0 houtns houth
  exact ⟨c', t, ht, hr, hh, hinv', h0, hns, hh1, hc1⟩

-- ════════════════════════════════════════════════════════════════════════
-- Composition end-caps: extraction and initialization
-- ════════════════════════════════════════════════════════════════════════

/-- The simulated output tape has a first blank at cell `m + 1` for some
    `m ≤ T` — offset to start at cell 1, matching the extract machine's
    copy range through the virtual-output shift. -/
private theorem output_first_blank_shift {n : ℕ} {tm : TM n} {T : ℕ}
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

/-- **Loop + extraction**: after the simulate/halt-test loop, `extractTM`
    copies the virtual output tape onto the real output tape. The combined
    machine turns the loop's precondition into the final output guarantee:
    the real output tape agrees with the simulated machine's final output
    tape (cells `1, …, m + 1`) through the latter's first blank. -/
theorem utm_loop_extract_hoareTime (α x : List Bool) (hterm : TerminatedRegion α)
    (T : ℕ) (mcF : Cfg 1 (decodeDesc α).toTM.Q)
    (hrun : (decodeDesc α).toTM.reachesIn T ((decodeDesc α).toTM.initCfg x) mcF)
    (hhalt : (decodeDesc α).toTM.halted mcF) :
    (seqTM (loopTM bodyTM haltTestTM) extractTM).HoareTime
      (fun inp work out =>
        SimInv α ((decodeDesc α).toTM.initCfg x) inp work out ∧
        out.cells 0 = Γ.start ∧
        (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
        out.head = 1)
      (fun _ _ out => ∃ m, m ≤ T ∧
        mcF.output.cells (m + 1) = Γ.blank ∧
        (∀ j, j < m → mcF.output.cells (j + 1) ≠ Γ.blank) ∧
        (∀ j, j ≤ m → out.cells (j + 1) = mcF.output.cells (j + 1)))
      ((T + 1) * utmStepTime α + 1 + (2 * T + 9)) := by
  obtain ⟨m, hmT, hmb, hmnb⟩ := output_first_blank_shift hrun
  refine seqTM_hoareTime (loopTM bodyTM haltTestTM) extractTM
    (mid' := fun inp work out =>
      SimInv α mcF inp work out ∧
      out.cells 0 = Γ.start ∧
      (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
      out.head = 1 ∧
      out.cells 1 = Γ.one)
    (utm_loop_hoareTime α x hterm T mcF hrun hhalt) ?_ ?_
  · -- the loop's postcondition is parked, so the transition is an identity
    rintro inp work out ⟨hinv, hout0, houtns, houth, hone⟩
    have h1 : transitionInput inp = inp := transitionInput_eq_self hinv.inp_read
    have h2 : (fun i => transitionTape (work i)) = work :=
      funext fun i => transitionTape_eq_self (simInv_work_reads α hinv i)
    have h3 : transitionTape out = out := transitionTape_eq_self hinv.out_read
    rw [h1, h2, h3]
    exact ⟨hinv, hout0, houtns, houth, hone⟩
  · -- the extraction phase, through the virtual-output shift
    rintro inp work out ⟨hinv, hout0, houtns, houth, hone⟩
    have hvout : VShift mcF.output (work 2) := hinv.vout
    have hcells2 : ∀ k, (work 2).cells (k + 2) = mcF.output.cells (k + 1) := by
      intro k
      rw [hvout.1]
      simp only [show ¬(k + 2 = 0) by omega, show ¬(k + 2 = 1) by omega,
        ite_false, show k + 2 - 1 = k + 1 by omega]
    have hblank2 : (work 2).cells (m + 2) = Γ.blank := by
      rw [hcells2 m]
      exact hmb
    have hnb2 : ∀ j, j < m → (work 2).cells (j + 2) ≠ Γ.blank := by
      intro j hj
      rw [hcells2 j]
      exact hmnb j hj
    have hwf2 : (work 2).StartInvariant := hvout.startInvariant hinv.wf_out
    have hheadF : mcF.output.head ≤ T := by
      have h := reachesIn_output_head_le hrun
      have h0 : ((decodeDesc α).toTM.initCfg x).output.head = 0 := rfl
      omega
    have hhead_eq : (work 2).head = mcF.output.head + 1 := hvout.head_eq
    obtain ⟨c', t, ht, hreach, hhalt', hpin, hpoth, hpc2, hpout⟩ :=
      extractTM_hoareTime m (T + 1) inp work out hblank2 hnb2 hwf2
        (by omega) hvout.head_pos hout0 houtns houth hinv.inp_read
        (fun i _ => simInv_work_reads α hinv i)
        inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨c', t, by omega, hreach, hhalt', m, hmT, hmb, hmnb, ?_⟩
    intro j hj
    rw [hpout j hj, hcells2 j]

/-- **The universal machine's end-to-end specification.** On the standard
    initial tapes for input `pair α x`, if the interpreted machine
    `(decodeDesc α).toTM` halts on `x` at `mcF` within `T` steps, then
    `utmTM` halts within
    `4·|pair α x| + 4·|groupPairs α| + 26 + (T + 1)·utmStepTime α + 2T + 9`
    steps with its real output tape agreeing with the simulated machine's
    final output tape through the latter's first blank — i.e. the UTM
    computes exactly the simulated machine's output. -/
theorem utmTM_hoareTime (α x : List Bool) (hterm : TerminatedRegion α)
    (T : ℕ) (mcF : Cfg 1 (decodeDesc α).toTM.Q)
    (hrun : (decodeDesc α).toTM.reachesIn T ((decodeDesc α).toTM.initCfg x) mcF)
    (hhalt : (decodeDesc α).toTM.halted mcF) :
    utmTM.HoareTime
      (fun inp work out =>
        inp = Tape.init ((pair α x).map Γ.ofBool) ∧
        (∀ i : Fin 6, work i = Tape.init []) ∧
        out = Tape.init [])
      (fun _ _ out => ∃ m, m ≤ T ∧
        mcF.output.cells (m + 1) = Γ.blank ∧
        (∀ j, j < m → mcF.output.cells (j + 1) ≠ Γ.blank) ∧
        (∀ j, j ≤ m → out.cells (j + 1) = mcF.output.cells (j + 1)))
      (4 * (pair α x).length + 4 * (groupPairs α).length + 24 + 1 +
        ((T + 1) * utmStepTime α + 1 + (2 * T + 9))) := by
  refine seqTM_hoareTime initTM (seqTM (loopTM bodyTM haltTestTM) extractTM)
    (mid' := fun inp work out =>
      SimInv α ((decodeDesc α).toTM.initCfg x) inp work out ∧
      out.cells 0 = Γ.start ∧
      (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
      out.head = 1)
    (initTM_hoareTime α x) ?_
    (utm_loop_extract_hoareTime α x hterm T mcF hrun hhalt)
  rintro inp work out ⟨hinp, hw0c, hw0h, hw1, hw1h, hw2, hw2h, hw3, hw3h,
    hw4, hw4h, hw5, hw5h, houtc, houth⟩
  -- parked reads on the work and output tapes
  have hr0 : (work 0).read ≠ Γ.start := by
    rw [Tape.read, hw0h, hw0c]
    simp
  have hr1 : (work 1).read ≠ Γ.start :=
    SimInv.read_ne_start_of_holdsExact hw1 hw1h.ge
  have hr2 : (work 2).read ≠ Γ.start :=
    SimInv.read_ne_start_of_holdsExact hw2 hw2h.ge
  have hr3 : (work 3).read ≠ Γ.start :=
    SimInv.read_ne_start_of_holdsExact hw3 hw3h.ge
  have hr4 : (work 4).read ≠ Γ.start :=
    SimInv.read_ne_start_of_holdsExact hw4 hw4h.ge
  have hr5 : (work 5).read ≠ Γ.start :=
    SimInv.read_ne_start_of_holdsExact hw5 hw5h.ge
  have hrout : out.read ≠ Γ.start := by
    rw [Tape.read, houth, houtc]
    simp [Tape.init]
  have hinp0 : inp.cells 0 = Γ.start := by
    rw [hinp]
    simp [Tape.init]
  have hwtr : (fun i => transitionTape (work i)) = work := by
    funext i
    refine transitionTape_eq_self ?_
    rcases i with ⟨iv, hv⟩
    rcases iv with _ | _ | _ | _ | _ | _ | n
    · exact hr0
    · exact hr1
    · exact hr2
    · exact hr3
    · exact hr4
    · exact hr5
    · exact absurd hv (by omega)
  have hotr : transitionTape out = out := transitionTape_eq_self hrout
  rw [hwtr, hotr]
  refine ⟨initPost_simInv α x (transitionInput inp) work out
    ⟨by rw [transitionInput_cells]; exact hinp,
     hw0c, hw0h, hw1, hw1h, hw2, hw2h, hw3, hw3h, hw4, hw4h, hw5, hw5h,
     houtc, houth⟩
    (transitionInput_head_ge inp hinp0), ?_, ?_, houth⟩
  · rw [houtc]
    simp [Tape.init]
  · intro j hj
    rw [houtc]
    simp [Tape.init, show j ≠ 0 by omega]

end TM.UTMBody

end Complexity
