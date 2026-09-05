/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.SAT.Verifier
public import Complexitylib.Models.TuringMachine.Subroutines.Counter
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Retarget

/-!
# SAT verifier TMs

Machine-level implementation of the deterministic SAT verifier, in the
`SAT.VerifierTM` namespace (recently renamed from a namespace that shadowed
`TM`). Building blocks, in dependency order:

* a deterministic checker for the witness-length side-condition
  `|α| ≤ |z| + 1` (`satLengthCheckTM` and its retargeted variants);
* a streaming evaluator `satEvalOnInputTM` for a SAT-encoded CNF against a
  staged assignment tape, together with its pure semantic model
  (`SatEvalSemState`, `satEvalSemStep`, `satEvalSemRun`, `satEvalSemBits`);
* the three-work-tape machine `verifyPairTM`, which computes the Boolean
  reference verifier `SAT.verifyPair` and hence decides `pairLang Witness`
  within the quadratic budget `verifyPairTMTime`
  (`verifyPairTM_decidesInTime`).

The pure model is tied to the reference verifier by `verifyPairSem` and
`verifyPairSem_eq_verifyPair`, so membership in `pairLang Witness` — the
paired witness language underlying `SAT.language ∈ NP` — is characterized
both semantically and at the machine level.
-/


@[expose] public section

namespace Complexity

namespace SAT

namespace VerifierTM

-- ════════════════════════════════════════════════════════════════════════
-- Small tape helpers
-- ════════════════════════════════════════════════════════════════════════

private theorem eq_initTape_move_right_of_cells_head_one {t : Tape} (bits : List Bool)
    (hcells : t.cells = (Tape.init (bits.map Γ.ofBool)).cells)
    (hhead : t.head = 1) :
    t = (Tape.init (bits.map Γ.ofBool)).move Dir3.right := by
  have hbits : t.HasBinaryString bits := by
    refine ⟨hhead, ?_, ?_⟩
    · intro i hi
      rw [hcells]
      exact Tape.init_ofBool_cells_lt bits i hi
    · intro i hi
      rw [hcells]
      exact Tape.init_ofBool_cells_ge bits i hi
  have h0 : t.cells 0 = Γ.start := by
    rw [hcells]
    simp [Tape.init]
  exact Tape.eq_init_move_right_of_hasBinaryString hbits h0

private theorem cells_eq_initTape_ofBool_cell0 {t : Tape} (bits : List Bool)
    (hcells : t.cells = (Tape.init (bits.map Γ.ofBool)).cells) :
    t.cells 0 = Γ.start := by
  rw [hcells]
  simp [Tape.init]

private theorem cells_eq_initTape_ofBool_ne_start {t : Tape} (bits : List Bool)
    (hcells : t.cells = (Tape.init (bits.map Γ.ofBool)).cells) :
    ∀ j, j ≥ 1 → t.cells j ≠ Γ.start := by
  intro j hj
  rw [hcells]
  exact Tape.init_ofBool_cells_ne_start bits j hj

private theorem read_ne_start_of_cells_eq_initTape_ofBool {t : Tape} (bits : List Bool)
    (hcells : t.cells = (Tape.init (bits.map Γ.ofBool)).cells)
    (hhead : t.head ≥ 1) :
    t.read ≠ Γ.start := by
  simp [Tape.read]
  exact cells_eq_initTape_ofBool_ne_start bits hcells t.head hhead

private abbrev hasBoolSuffix := Tape.HasBinarySuffix

private theorem initTape_move_right_hasBoolSuffix (bits : List Bool) :
    hasBoolSuffix ((Tape.init (bits.map Γ.ofBool)).move Dir3.right) bits :=
  Tape.init_move_right_hasBinarySuffix bits

private theorem hasBoolSuffix_read_cons {t : Tape} {b : Bool} {bits : List Bool}
    (h : hasBoolSuffix t (b :: bits)) :
    t.read = Γ.ofBool b :=
  h.read_cons

private theorem hasBoolSuffix_move_right_cons {t : Tape} {b : Bool} {bits : List Bool}
    (h : hasBoolSuffix t (b :: bits)) :
    hasBoolSuffix (t.move Dir3.right) bits :=
  h.move_right_cons

private theorem hasBoolSuffix_read_nil {t : Tape}
    (h : hasBoolSuffix t []) :
    t.read = Γ.blank :=
  h.read_nil

private theorem hasBoolSuffix_read_ne_start {t : Tape} {bits : List Bool}
    (h : hasBoolSuffix t bits) :
    t.read ≠ Γ.start :=
  h.read_ne_start

private theorem retargetInput_step_preserves_input_of_read_ne_start {k : ℕ} (M : TM k)
    {c c' : Cfg (k + 1) (TM.retargetInput M).Q}
    (hstep : (TM.retargetInput M).step c = some c')
    (hinp : c.input.read ≠ Γ.start) :
    c'.input = c.input := by
  simp only [TM.step, TM.retargetInput] at hstep
  split at hstep
  · simp at hstep
  · injection hstep with hstep
    subst hstep
    simp [TM.idleDir, hinp, Tape.move]

private theorem retargetInput_reachesIn_preserves_input_of_read_ne_start {k : ℕ}
    (M : TM k)
    {t : ℕ} {c c' : Cfg (k + 1) (TM.retargetInput M).Q}
    (hreach : (TM.retargetInput M).reachesIn t c c')
    (hinp : c.input.read ≠ Γ.start) :
    c'.input = c.input := by
  induction hreach with
  | zero =>
      rfl
  | step hstep hrest ih =>
      have hmid : _ := retargetInput_step_preserves_input_of_read_ne_start M hstep hinp
      rw [← hmid]
      exact ih (by simpa [hmid] using hinp)

private theorem started_blank_output_read_ne_start :
    (((Tape.init []).move Dir3.right).read) ≠ Γ.start := by
  rw [Tape.init_nil_move_right_read]
  decide

private theorem unaryCounter_read_ne_start {t : Tape} {B : ℕ}
    (h : t.HasUnaryCounter B) : t.read ≠ Γ.start := by
  by_cases hB : B = 0
  · subst hB
    rw [Tape.hasUnaryCounter_read_zero h]
    simp
  · have hpos : 0 < B := Nat.pos_of_ne_zero hB
    rw [Tape.hasUnaryCounter_read_pos h hpos]
    simp

private theorem started_input_read_ne_start (α : List Bool) :
    (((Tape.init (α.map Γ.ofBool)).move Dir3.right).read) ≠ Γ.start := by
  exact Tape.init_ofBool_move_right_read_ne_start α

private theorem fin2_ne_zero_eq_one (i : Fin 2) (h : i ≠ ⟨0, by omega⟩) :
    i = ⟨1, by omega⟩ := by
  apply Fin.ext
  have hne0 : (i : ℕ) ≠ 0 := by
    intro hi0
    apply h
    apply Fin.ext
    simpa using hi0
  have hlt : (i : ℕ) < 2 := i.isLt
  have hi1 : (i : ℕ) = 1 := by
    omega
  simpa using hi1

-- ════════════════════════════════════════════════════════════════════════
-- Deterministic witness-length checker
-- ════════════════════════════════════════════════════════════════════════

/-- Control states for the SAT witness-length checker. -/
inductive SatLengthCheckPhase where
  /-- Initial state: step off the left marker before scanning. -/
  | init
  /-- Scanning state: consume one counter mark per input bit. -/
  | scan
  /-- Halt state: the verdict has been written to the output tape. -/
  | done
  deriving DecidableEq

instance : Fintype SatLengthCheckPhase where
  elems := {.init, .scan, .done}
  complete := by
    intro q
    cases q <;> simp

/-- Deterministic checker for `|input| ≤ B`, where `B` is given as a unary
counter on work tape `0`. The machine scans one input bit per counter mark,
accepts when the input ends, and rejects if the counter is exhausted first. -/
def satLengthCheckTM : TM 1 where
  Q := SatLengthCheckPhase
  qstart := .init
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    let counterHead := wHeads ⟨0, by omega⟩
    match state with
    | .init =>
        (.scan,
          fun _ => TM.readBackWrite counterHead,
          TM.readBackWrite oHead,
          TM.idleDir iHead,
          fun _ => TM.idleDir counterHead,
          TM.idleDir oHead)
    | .scan =>
        if iHead = Γ.blank then
          (.done,
            fun _ => TM.readBackWrite counterHead,
            Γw.one,
            TM.idleDir iHead,
            fun _ => TM.idleDir counterHead,
            TM.idleDir oHead)
        else if counterHead = Γ.one then
          (.scan,
            fun _ => Γw.blank,
            TM.readBackWrite oHead,
            Dir3.right,
            fun _ => Dir3.right,
            TM.idleDir oHead)
        else
          (.done,
            fun _ => TM.readBackWrite counterHead,
            Γw.zero,
            TM.idleDir iHead,
            fun _ => TM.idleDir counterHead,
            TM.idleDir oHead)
    | .done =>
        TM.allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    let counterHead := wHeads ⟨0, by omega⟩
    match state with
    | .init =>
        refine ⟨TM.idleDir_right_of_start, ?_, TM.idleDir_right_of_start⟩
        intro i hi
        have hi0 : i = ⟨0, by omega⟩ := by
          apply Fin.ext
          omega
        subst hi0
        simpa [counterHead] using TM.idleDir_right_of_start hi
    | .scan =>
        dsimp only []
        split
        · refine ⟨TM.idleDir_right_of_start, ?_, TM.idleDir_right_of_start⟩
          intro i hi
          have hi0 : i = ⟨0, by omega⟩ := by
            apply Fin.ext
            omega
          subst hi0
          simpa [counterHead] using TM.idleDir_right_of_start hi
        · split
          · refine ⟨fun _ => rfl, ?_, TM.idleDir_right_of_start⟩
            intro i _
            have hi0 : i = ⟨0, by omega⟩ := by
              apply Fin.ext
              omega
            subst hi0
            rfl
          · refine ⟨TM.idleDir_right_of_start, ?_, TM.idleDir_right_of_start⟩
            intro i hi
            have hi0 : i = ⟨0, by omega⟩ := by
              apply Fin.ext
              omega
            subst hi0
            simpa [counterHead] using TM.idleDir_right_of_start hi
    | .done =>
        exact TM.rightOfStart_allIdle iHead wHeads oHead

/-- A convenient linear upper bound for the length checker. -/
def satLengthCheckTime (n : ℕ) : ℕ :=
  n + 2

-- ════════════════════════════════════════════════════════════════════════
-- Step lemmas
-- ════════════════════════════════════════════════════════════════════════

private theorem satLengthCheck_init_step (α : List Bool) (B : ℕ)
    (c : Cfg 1 satLengthCheckTM.Q)
    (hstate : c.state = .init)
    (hinput : c.input = (Tape.init (α.map Γ.ofBool)).move Dir3.right)
    (hcounter : (c.work ⟨0, by omega⟩).HasUnaryCounter B)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satLengthCheckTM.step c = some c' ∧
      c'.state = .scan ∧
      c'.input = c.input ∧
      c'.work ⟨0, by omega⟩ = c.work ⟨0, by omega⟩ ∧
      c'.output = c.output := by
  have hinp : c.input.read ≠ Γ.start := by
    rw [hinput]
    exact started_input_read_ne_start α
  have hwork : (c.work ⟨0, by omega⟩).read ≠ Γ.start := unaryCounter_read_ne_start hcounter
  have hout' : c.output.read ≠ Γ.start := by
    rw [hout]
    exact started_blank_output_read_ne_start
  simp only [TM.step, hstate, satLengthCheckTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · change TM.transitionInput c.input = c.input
    exact TM.transitionInput_eq_self hinp
  · change TM.transitionTape (c.work ⟨0, by omega⟩) = c.work ⟨0, by omega⟩
    exact TM.transitionTape_eq_self hwork
  · change TM.transitionTape c.output = c.output
    exact TM.transitionTape_eq_self hout'

private theorem satLengthCheck_scan_continue_step (α : List Bool) (B k : ℕ)
    (c : Cfg 1 satLengthCheckTM.Q)
    (hk : k < α.length)
    (hkB : k < B)
    (hstate : c.state = .scan)
    (hinput_cells : c.input.cells = (Tape.init (α.map Γ.ofBool)).cells)
    (hinput_head : c.input.head = k + 1)
    (hcounter : (c.work ⟨0, by omega⟩).HasCounterRemainder k B)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satLengthCheckTM.step c = some c' ∧
      c'.state = .scan ∧
      c'.input.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
      c'.input.head = k + 2 ∧
      (c'.work ⟨0, by omega⟩).HasCounterRemainder (k + 1) B ∧
      c'.output = c.output := by
  have hread_input : c.input.read = Γ.ofBool (α[k]'hk) := by
    show c.input.cells c.input.head = _
    rw [hinput_head, hinput_cells]
    exact Tape.init_ofBool_cells_lt α k hk
  have hinput_nb : c.input.read ≠ Γ.blank := by
    rw [hread_input]
    exact Γ.ofBool_ne_blank _
  have hcounter_read : (c.work ⟨0, by omega⟩).read = Γ.one :=
    Tape.hasCounterRemainder_read_one_of_remaining hcounter hkB
  have hout' : c.output.read ≠ Γ.start := by
    rw [hout]
    exact started_blank_output_read_ne_start
  simp only [TM.step, hstate, satLengthCheckTM, hinput_nb, hcounter_read]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [Tape.move_cells]
    exact hinput_cells
  · simp [Tape.move, hinput_head]
  · simpa using Tape.hasCounterRemainder_consume hcounter hkB
  · change TM.transitionTape c.output = c.output
    exact TM.transitionTape_eq_self hout'

private theorem satLengthCheck_scan_accept_step (α : List Bool) (B : ℕ)
    (c : Cfg 1 satLengthCheckTM.Q)
    (hstate : c.state = .scan)
    (hinput_cells : c.input.cells = (Tape.init (α.map Γ.ofBool)).cells)
    (hinput_head : c.input.head = α.length + 1)
    (_hcounter : (c.work ⟨0, by omega⟩).HasCounterRemainder α.length B)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satLengthCheckTM.step c = some c' ∧
      satLengthCheckTM.halted c' ∧
      c'.input.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
      c'.output.cells 1 = Γ.one := by
  have hread_input : c.input.read = Γ.blank := by
    show c.input.cells c.input.head = Γ.blank
    rw [hinput_head, hinput_cells]
    exact Tape.init_ofBool_cells_ge α α.length le_rfl
  have hout_read : c.output.read = Γ.blank := by
    rw [hout]
    simp [Tape.read, Tape.move, Tape.init]
  simp only [TM.step, hstate, satLengthCheckTM, hread_input, hout_read]
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · rw [Tape.move_cells]
    exact hinput_cells
  · have ho_head : c.output.head = 1 := by
      rw [hout]
      simp [Tape.move, Tape.init]
    simp [Tape.writeAndMove, Tape.move, Tape.write, ho_head, TM.idleDir, Γw.toΓ]

private theorem satLengthCheck_scan_reject_step (α : List Bool) (B : ℕ)
    (c : Cfg 1 satLengthCheckTM.Q)
    (hB : B < α.length)
    (hstate : c.state = .scan)
    (hinput_cells : c.input.cells = (Tape.init (α.map Γ.ofBool)).cells)
    (hinput_head : c.input.head = B + 1)
    (hcounter : (c.work ⟨0, by omega⟩).HasCounterRemainder B B)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satLengthCheckTM.step c = some c' ∧
      satLengthCheckTM.halted c' ∧
      c'.input.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
      c'.output.cells 1 = Γ.zero := by
  have hread_input : c.input.read ≠ Γ.blank := by
    have hcell : c.input.read = Γ.ofBool (α[B]'hB) := by
      show c.input.cells c.input.head = _
      rw [hinput_head, hinput_cells]
      exact Tape.init_ofBool_cells_lt α B hB
    rw [hcell]
    exact Γ.ofBool_ne_blank _
  have hread_counter : (c.work ⟨0, by omega⟩).read = Γ.blank :=
    Tape.hasCounterRemainder_read_blank_of_done hcounter
  have hout_read : c.output.read = Γ.blank := by
    rw [hout]
    simp [Tape.read, Tape.move, Tape.init]
  simp only [TM.step, hstate, satLengthCheckTM, hread_input, hread_counter, hout_read]
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · rw [Tape.move_cells]
    exact hinput_cells
  · have ho_head : c.output.head = 1 := by
      rw [hout]
      simp [Tape.move, Tape.init]
    simp [Tape.writeAndMove, Tape.move, Tape.write, ho_head, TM.idleDir, Γw.toΓ]

-- ════════════════════════════════════════════════════════════════════════
-- Prefix scan loop
-- ════════════════════════════════════════════════════════════════════════

private theorem satLengthCheck_scan_prefix_loop (α : List Bool) (B : ℕ) :
    ∀ (m k : ℕ) (c : Cfg 1 satLengthCheckTM.Q),
      k + m ≤ α.length →
      k + m ≤ B →
      c.state = .scan →
      c.input.cells = (Tape.init (α.map Γ.ofBool)).cells →
      c.input.head = k + 1 →
      (c.work ⟨0, by omega⟩).HasCounterRemainder k B →
      c.output = (Tape.init []).move Dir3.right →
      ∃ c',
        satLengthCheckTM.reachesIn m c c' ∧
        c'.state = .scan ∧
        c'.input.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
        c'.input.head = k + m + 1 ∧
        (c'.work ⟨0, by omega⟩).HasCounterRemainder (k + m) B ∧
        c'.output = (Tape.init []).move Dir3.right := by
  intro m
  induction m with
  | zero =>
      intro k c _ _ hstate hinput_cells hinput_head hcounter hout
      refine ⟨c, .zero, hstate, hinput_cells, ?_, ?_, hout⟩
      · omega
      · simpa using hcounter
  | succ m ih =>
      intro k c hlen hbound hstate hinput_cells hinput_head hcounter hout
      have hk : k < α.length := by omega
      have hkB : k < B := by omega
      obtain ⟨c1, hstep, hstate1, hcells1, hhead1, hcounter1, hout1⟩ :=
        satLengthCheck_scan_continue_step α B k c hk hkB hstate hinput_cells
          hinput_head hcounter hout
      have hlen1 : k + 1 + m ≤ α.length := by omega
      have hbound1 : k + 1 + m ≤ B := by omega
      have hout1_started : c1.output = (Tape.init []).move Dir3.right := by
        rw [hout1]
        exact hout
      obtain ⟨c', hreach, hstate', hcells', hhead', hcounter', hout'⟩ :=
        ih (k + 1) c1 hlen1 hbound1 hstate1 hcells1 hhead1 hcounter1 hout1_started
      refine ⟨c', .step hstep hreach, hstate', hcells', ?_, ?_, hout'⟩
      · rw [hhead']
        omega
      · convert hcounter' using 1
        omega

-- ════════════════════════════════════════════════════════════════════════
-- Main started Hoare theorem
-- ════════════════════════════════════════════════════════════════════════

/-- Started-tape correctness for the witness-length checker. The input tape is
already positioned at cell `1`, the counter tape stores a unary bound `B`, and
the output tape is the started blank tape. The machine halts with output `1`
iff `|α| ≤ B`. -/
theorem satLengthCheckTM_started_hoareTime (B : ℕ) (α : List Bool) :
    satLengthCheckTM.HoareTime
      (fun inp work out =>
        inp = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨0, by omega⟩).HasUnaryCounter B ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp _work out =>
        inp.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
        out.cells 1 = (if α.length ≤ B then Γ.one else Γ.zero))
      (satLengthCheckTime α.length) := by
  intro inp work out hpre
  rcases hpre with ⟨hinput, hcounter, hout⟩
  let c0 : Cfg 1 satLengthCheckTM.Q :=
    { state := satLengthCheckTM.qstart, input := inp, work := work, output := out }
  obtain ⟨c1, hstep1, hstate1, hinput1, hwork1, hout1⟩ :=
    satLengthCheck_init_step α B c0 rfl hinput hcounter hout
  have hcells0 : c0.input.cells = (Tape.init (α.map Γ.ofBool)).cells := by
    change inp.cells = (Tape.init (α.map Γ.ofBool)).cells
    rw [hinput]
    exact Tape.move_cells _ _
  have hhead0 : c0.input.head = 1 := by
    change inp.head = 1
    rw [hinput]
    simp [Tape.move, Tape.init]
  have hcells1 : c1.input.cells = (Tape.init (α.map Γ.ofBool)).cells := by
    rw [hinput1]
    exact hcells0
  have hhead1 : c1.input.head = 1 := by
    rw [hinput1]
    exact hhead0
  have hcounter1 : (c1.work ⟨0, by omega⟩).HasCounterRemainder 0 B := by
    rw [hwork1]
    exact (Tape.hasUnaryCounter_iff_remainder_zero).mp hcounter
  have hout1_started : c1.output = (Tape.init []).move Dir3.right := by
    rw [hout1]
    exact hout
  by_cases hle : α.length ≤ B
  · obtain ⟨c2, hreach2, hstate2, hcells2, hhead2, hcounter2, hout2⟩ :=
      satLengthCheck_scan_prefix_loop α B α.length 0 c1
        (by omega) (by simpa using hle) hstate1 hcells1 hhead1 hcounter1 hout1_started
    obtain ⟨c3, hstep3, hhalt3, hcells3, hout3⟩ :=
      satLengthCheck_scan_accept_step α B c2 hstate2 hcells2
        (by simpa using hhead2) (by simpa using hcounter2) hout2
    have hreach_total : satLengthCheckTM.reachesIn (1 + α.length + 1) c0 c3 := by
      simpa [Nat.add_assoc] using
        TM.reachesIn_trans _ (.step hstep1 .zero)
          (TM.reachesIn_trans _ hreach2 (.step hstep3 .zero))
    refine ⟨c3, 1 + α.length + 1, by
      simp [satLengthCheckTime]
      omega, hreach_total, hhalt3, ?_⟩
    refine ⟨hcells3, ?_⟩
    simpa [hle] using hout3
  · have hlt : B < α.length := by omega
    obtain ⟨c2, hreach2, hstate2, hcells2, hhead2, hcounter2, hout2⟩ :=
      satLengthCheck_scan_prefix_loop α B B 0 c1
        (by omega) (by omega) hstate1 hcells1 hhead1 hcounter1 hout1_started
    obtain ⟨c3, hstep3, hhalt3, hcells3, hout3⟩ :=
      satLengthCheck_scan_reject_step α B c2 hlt hstate2 hcells2
        (by simpa using hhead2) (by simpa using hcounter2) hout2
    have hreach_total : satLengthCheckTM.reachesIn (1 + B + 1) c0 c3 := by
      simpa [Nat.add_assoc] using
        TM.reachesIn_trans _ (.step hstep1 .zero)
          (TM.reachesIn_trans _ hreach2 (.step hstep3 .zero))
    refine ⟨c3, 1 + B + 1, by
      simp [satLengthCheckTime]
      omega, hreach_total, hhalt3, ?_⟩
    refine ⟨hcells3, ?_⟩
    simpa [hle] using hout3

/-- Virtual-input/work-tape version of `satLengthCheckTM_started_hoareTime`.
The last work tape supplies the witness bits, work tape `0` supplies a unary
counter bound, and the output tape receives `1` iff the witness length is at
most that bound. The counter tape precondition includes the structural
no-`▷` invariant required by `retargetInput`. -/
theorem retargetInput_satLengthCheckTM_started_hoareTime (B : ℕ) (α : List Bool) :
    (TM.retargetInput satLengthCheckTM).HoareTime
      (fun _inp work out =>
        work ⟨1, by omega⟩ = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨0, by omega⟩).HasUnaryCounter B ∧
        (work ⟨0, by omega⟩).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (work ⟨0, by omega⟩).cells j ≠ Γ.start) ∧
        out = (Tape.init []).move Dir3.right)
      (fun _inp work out =>
        (work ⟨1, by omega⟩).cells = (Tape.init (α.map Γ.ofBool)).cells ∧
        out.cells 1 = (if α.length ≤ B then Γ.one else Γ.zero))
      (satLengthCheckTime α.length) := by
  have hmove_right_invariant : ∀ {t : Tape}, Tape.StartInvariant t →
      Tape.StartInvariant (t.move Dir3.right) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · simpa [Tape.move_cells] using ht.1
    · intro j hj
      simpa [Tape.move_cells] using ht.2 j hj
  have hlen :
      satLengthCheckTM.HoareTime
        (fun inp work out =>
          inp = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
          (work ⟨0, by omega⟩).HasUnaryCounter B ∧
          (work ⟨0, by omega⟩).cells 0 = Γ.start ∧
          (∀ j, j ≥ 1 → (work ⟨0, by omega⟩).cells j ≠ Γ.start) ∧
          out = (Tape.init []).move Dir3.right)
        (fun inp _work out =>
          inp.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
          out.cells 1 = (if α.length ≤ B then Γ.one else Γ.zero))
        (satLengthCheckTime α.length) :=
    (satLengthCheckTM_started_hoareTime B α).weaken_pre (by
      intro inp work out hpre
      exact ⟨hpre.1, hpre.2.1, hpre.2.2.2.2⟩)
  have hret := TM.retargetInput_hoareTime (M := satLengthCheckTM)
    hlen
    (hpre_inp := by
      intro _inp work out hpre
      rcases hpre with ⟨hvin, _hcounter, _hcell0, _hnostart, _hout⟩
      rw [hvin]
      exact hmove_right_invariant (Tape.StartInvariant.init_ofBool α))
    (hpre_work := by
      intro _inp work out hpre i
      rcases hpre with ⟨_hvin, _hcounter, hcell0, hnostart, _hout⟩
      have hi0 : i = ⟨0, by omega⟩ := by
        apply Fin.ext
        omega
      subst hi0
      exact ⟨hcell0, hnostart⟩)
    (hpre_out := by
      intro _inp work out hpre
      rcases hpre with ⟨_hvin, _hcounter, _hcell0, _hnostart, hout⟩
      rw [hout]
      exact hmove_right_invariant (Tape.StartInvariant.init_nil))
  refine hret.strengthen_post ?_
  intro _inp work out hpost
  rcases hpost with ⟨vin, innerWork, hinner, hmap, hvin⟩
  exact ⟨by rw [hvin]; exact hinner.1,
    by simpa using hinner.2⟩

-- ════════════════════════════════════════════════════════════════════════
-- Counter-builder verifier slice
-- ════════════════════════════════════════════════════════════════════════

/-- Three-work-tape counter builder obtained by retargeting the input of
`inputLengthPlusOneCounterTM` to work tape `2`. Tape `0` stores the unary
counter, tape `1` is preserved, and tape `2` provides the formula bits. -/
def satCounter3TM : TM 3 :=
  TM.retargetInput (TM.inputLengthPlusOneCounterTM ⟨0, by omega⟩)

/-- Build the unary counter `|z| + 1` on tape `0` from staged formula tape `2`
while preserving the staged witness on tape `1` and leaving the output tape in
the started blank configuration. -/
theorem satCounter3TM_started_hoareTime (z α : List Bool) :
    satCounter3TM.HoareTime
      (fun _inp work out =>
        work ⟨2, by omega⟩ = (Tape.init (z.map Γ.ofBool)).move Dir3.right ∧
        work ⟨0, by omega⟩ = (Tape.init []).move Dir3.right ∧
        work ⟨1, by omega⟩ = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        out = (Tape.init []).move Dir3.right)
      (fun _inp work out =>
        (work ⟨2, by omega⟩).cells = (Tape.init (z.map Γ.ofBool)).cells ∧
        (work ⟨2, by omega⟩).head = z.length + 1 ∧
        work ⟨1, by omega⟩ = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨0, by omega⟩).HasUnaryCounter (z.length + 1) ∧
        (work ⟨0, by omega⟩).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (work ⟨0, by omega⟩).cells j ≠ Γ.start) ∧
        out = (Tape.init []).move Dir3.right)
      (TM.inputLengthPlusOneCounterTime z.length) := by
  let counterIdx : Fin 2 := ⟨0, by decide⟩
  let passiveIdx : Fin 2 := ⟨1, by decide⟩
  have hmove_right_invariant : ∀ {t : Tape}, Tape.StartInvariant t →
      Tape.StartInvariant (t.move Dir3.right) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · simpa [Tape.move_cells] using ht.1
    · intro j hj
      simpa [Tape.move_cells] using ht.2 j hj
  have hcounter :
      (TM.inputLengthPlusOneCounterTM counterIdx).HoareTime
        (fun inp work out =>
          inp = (Tape.init (z.map Γ.ofBool)).move Dir3.right ∧
          work counterIdx = (Tape.init []).move Dir3.right ∧
          work passiveIdx = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
          out = (Tape.init []).move Dir3.right)
        (fun inp work out =>
          inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
          inp.head = z.length + 1 ∧
          work passiveIdx = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
          (work counterIdx).HasUnaryCounter (z.length + 1) ∧
          (work counterIdx).cells 0 = Γ.start ∧
          (∀ j, j ≥ 1 → (work counterIdx).cells j ≠ Γ.start) ∧
          out = (Tape.init []).move Dir3.right)
        (TM.inputLengthPlusOneCounterTime z.length) :=
    TM.inputLengthPlusOneCounterTM_started_tracksInput_preserves_work_hoareTime
      counterIdx passiveIdx (by decide) z α
  have hret := TM.retargetInput_hoareTime
      (M := TM.inputLengthPlusOneCounterTM counterIdx)
      hcounter
    (hpre_inp := by
      intro _inp work out hpre
      rcases hpre with ⟨hvin, _hblank, _hpassive, _hout⟩
      rw [hvin]
      exact hmove_right_invariant (Tape.StartInvariant.init_ofBool z))
    (hpre_work := by
      intro _inp work out hpre i
      rcases hpre with ⟨_hvin, hblank, hpassive, _hout⟩
      by_cases hi0 : i = counterIdx
      · subst hi0
        rw [hblank]
        exact hmove_right_invariant (Tape.StartInvariant.init_nil)
      · have hi1 := fin2_ne_zero_eq_one i hi0
        subst hi1
        rw [hpassive]
        exact hmove_right_invariant (Tape.StartInvariant.init_ofBool α))
    (hpre_out := by
      intro _inp work out hpre
      rcases hpre with ⟨_hvin, _hblank, _hpassive, hout⟩
      rw [hout]
      exact hmove_right_invariant (Tape.StartInvariant.init_nil))
  have hret' : satCounter3TM.HoareTime
      (fun _inp work out =>
        work ⟨2, by omega⟩ = (Tape.init (z.map Γ.ofBool)).move Dir3.right ∧
        work ⟨0, by omega⟩ = (Tape.init []).move Dir3.right ∧
        work ⟨1, by omega⟩ = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        out = (Tape.init []).move Dir3.right)
      (fun _inp work out =>
        ∃ vin : Tape, ∃ innerWork : Fin 2 → Tape,
          (vin.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
            vin.head = z.length + 1 ∧
            innerWork passiveIdx = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
            (innerWork counterIdx).HasUnaryCounter (z.length + 1) ∧
            (innerWork counterIdx).cells 0 = Γ.start ∧
            (∀ j, j ≥ 1 → (innerWork counterIdx).cells j ≠ Γ.start) ∧
            out = (Tape.init []).move Dir3.right) ∧
          (∀ i : Fin 2, work ⟨i.val, by omega⟩ = innerWork i) ∧
          work ⟨2, by omega⟩ = vin)
      (TM.inputLengthPlusOneCounterTime z.length) := by
    exact hret
  refine hret'.strengthen_post ?_
  intro _inp work out hpost
  rcases hpost with ⟨vin, innerWork, hinner, hmap, hvin⟩
  have hmap0 : work ⟨0, by omega⟩ = innerWork counterIdx := by
    simpa [counterIdx] using hmap counterIdx
  exact ⟨by rw [hvin]; exact hinner.1,
    by rw [hvin]; exact hinner.2.1,
    (hmap passiveIdx).trans hinner.2.2.1,
    by rw [hmap0]; exact hinner.2.2.2.1,
    by rw [hmap0]; exact hinner.2.2.2.2.1,
    by rw [hmap0]; exact hinner.2.2.2.2.2.1,
    hinner.2.2.2.2.2.2⟩

/-- Richer started-tape wrapper for `satCounter3TM` that also records that the
real input tape remains stable when it starts past `▷`. -/
theorem satCounter3TM_started_stableInput_hoareTime (z α : List Bool) :
    satCounter3TM.HoareTime
      (fun inp work out =>
        inp.read ≠ Γ.start ∧
        work ⟨2, by omega⟩ = (Tape.init (z.map Γ.ofBool)).move Dir3.right ∧
        work ⟨0, by omega⟩ = (Tape.init []).move Dir3.right ∧
        work ⟨1, by omega⟩ = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp.read ≠ Γ.start ∧
        (work ⟨2, by omega⟩).cells = (Tape.init (z.map Γ.ofBool)).cells ∧
        (work ⟨2, by omega⟩).head = z.length + 1 ∧
        work ⟨1, by omega⟩ = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨0, by omega⟩).HasUnaryCounter (z.length + 1) ∧
        (work ⟨0, by omega⟩).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (work ⟨0, by omega⟩).cells j ≠ Γ.start) ∧
        out = (Tape.init []).move Dir3.right)
      (TM.inputLengthPlusOneCounterTime z.length) := by
  intro inp work out hpre
  let counterIdx : Fin 2 := ⟨0, by omega⟩
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ :=
    satCounter3TM_started_hoareTime z α inp work out hpre.2
  have hinput_keep :
      c'.input = inp :=
    retargetInput_reachesIn_preserves_input_of_read_ne_start
      (TM.inputLengthPlusOneCounterTM (n := 2) counterIdx)
      (by simp only [satCounter3TM] at hreach; exact hreach)
      hpre.1
  refine ⟨c', t, ht, hreach, hhalt, ?_⟩
  rw [hinput_keep]
  exact ⟨hpre.1, hpost⟩

-- ════════════════════════════════════════════════════════════════════════
-- Passive-preserving verifier slice
-- ════════════════════════════════════════════════════════════════════════

/-- A two-work-tape version of the SAT witness-length checker. Work tape `0`
stores the unary bound, while work tape `1` is preserved exactly. -/
def satLengthCheckPassiveTM : TM 2 where
  Q := SatLengthCheckPhase
  qstart := .init
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    let counterHead := wHeads ⟨0, by omega⟩
    let passiveHead := wHeads ⟨1, by omega⟩
    match state with
    | .init =>
        (.scan,
          fun i =>
            if i = ⟨0, by omega⟩ then TM.readBackWrite counterHead
            else TM.readBackWrite passiveHead,
          TM.readBackWrite oHead,
          TM.idleDir iHead,
          fun i =>
            if i = ⟨0, by omega⟩ then TM.idleDir counterHead
            else TM.idleDir passiveHead,
          TM.idleDir oHead)
    | .scan =>
        if iHead = Γ.blank then
          (.done,
            fun i =>
              if i = ⟨0, by omega⟩ then TM.readBackWrite counterHead
              else TM.readBackWrite passiveHead,
            Γw.one,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨0, by omega⟩ then TM.idleDir counterHead
              else TM.idleDir passiveHead,
            TM.idleDir oHead)
        else if counterHead = Γ.one then
          (.scan,
            fun i => if i = ⟨0, by omega⟩ then Γw.blank else TM.readBackWrite passiveHead,
            TM.readBackWrite oHead,
            Dir3.right,
            fun i => if i = ⟨0, by omega⟩ then Dir3.right else TM.idleDir passiveHead,
            TM.idleDir oHead)
        else
          (.done,
            fun i =>
              if i = ⟨0, by omega⟩ then TM.readBackWrite counterHead
              else TM.readBackWrite passiveHead,
            Γw.zero,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨0, by omega⟩ then TM.idleDir counterHead
              else TM.idleDir passiveHead,
            TM.idleDir oHead)
    | .done =>
        TM.allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    let counterHead := wHeads ⟨0, by omega⟩
    let passiveHead := wHeads ⟨1, by omega⟩
    match state with
    | .init =>
        refine ⟨TM.idleDir_right_of_start, ?_, TM.idleDir_right_of_start⟩
        intro i hi
        by_cases hi0 : i = ⟨0, by omega⟩
        · subst hi0
          simpa [counterHead] using TM.idleDir_right_of_start hi
        · have hi1 := fin2_ne_zero_eq_one i hi0
          subst hi1
          simpa [passiveHead] using TM.idleDir_right_of_start hi
    | .scan =>
        dsimp only []
        split
        · refine ⟨TM.idleDir_right_of_start, ?_, TM.idleDir_right_of_start⟩
          intro i hi
          by_cases hi0 : i = ⟨0, by omega⟩
          · subst hi0
            simpa [counterHead] using TM.idleDir_right_of_start hi
          · have hi1 := fin2_ne_zero_eq_one i hi0
            subst hi1
            simpa [passiveHead] using TM.idleDir_right_of_start hi
        · split
          · refine ⟨fun _ => rfl, ?_, TM.idleDir_right_of_start⟩
            intro i hi
            by_cases hi0 : i = ⟨0, by omega⟩
            · subst hi0
              rfl
            · have hi1 := fin2_ne_zero_eq_one i hi0
              subst hi1
              simpa [passiveHead] using TM.idleDir_right_of_start hi
          · refine ⟨TM.idleDir_right_of_start, ?_, TM.idleDir_right_of_start⟩
            intro i hi
            by_cases hi0 : i = ⟨0, by omega⟩
            · subst hi0
              simpa [counterHead] using TM.idleDir_right_of_start hi
            · have hi1 := fin2_ne_zero_eq_one i hi0
              subst hi1
              simpa [passiveHead] using TM.idleDir_right_of_start hi
    | .done =>
        exact TM.rightOfStart_allIdle iHead wHeads oHead

private theorem satLengthCheckPassive_init_step (α β : List Bool) (B : ℕ)
    (c : Cfg 2 satLengthCheckPassiveTM.Q)
    (hstate : c.state = .init)
    (hinput : c.input = (Tape.init (α.map Γ.ofBool)).move Dir3.right)
    (hcounter : (c.work ⟨0, by omega⟩).HasUnaryCounter B)
    (hpassive : c.work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satLengthCheckPassiveTM.step c = some c' ∧
      c'.state = .scan ∧
      c'.input = c.input ∧
      c'.work ⟨0, by omega⟩ = c.work ⟨0, by omega⟩ ∧
      c'.work ⟨1, by omega⟩ = c.work ⟨1, by omega⟩ ∧
      c'.output = c.output := by
  have hinp : c.input.read ≠ Γ.start := by
    rw [hinput]
    exact started_input_read_ne_start α
  have hwork0 : (c.work ⟨0, by omega⟩).read ≠ Γ.start := unaryCounter_read_ne_start hcounter
  have hwork1 : (c.work ⟨1, by omega⟩).read ≠ Γ.start := by
    rw [hpassive]
    exact started_input_read_ne_start β
  have hout' : c.output.read ≠ Γ.start := by
    rw [hout]
    exact started_blank_output_read_ne_start
  simp only [TM.step, hstate, satLengthCheckPassiveTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · change TM.transitionInput c.input = c.input
    exact TM.transitionInput_eq_self hinp
  · change TM.transitionTape (c.work ⟨0, by omega⟩) = c.work ⟨0, by omega⟩
    exact TM.transitionTape_eq_self hwork0
  · change TM.transitionTape (c.work ⟨1, by omega⟩) = c.work ⟨1, by omega⟩
    exact TM.transitionTape_eq_self hwork1
  · change TM.transitionTape c.output = c.output
    exact TM.transitionTape_eq_self hout'

private theorem satLengthCheckPassive_scan_continue_step (α β : List Bool) (B k : ℕ)
    (c : Cfg 2 satLengthCheckPassiveTM.Q)
    (hk : k < α.length)
    (hkB : k < B)
    (hstate : c.state = .scan)
    (hinput_cells : c.input.cells = (Tape.init (α.map Γ.ofBool)).cells)
    (hinput_head : c.input.head = k + 1)
    (hcounter : (c.work ⟨0, by omega⟩).HasCounterRemainder k B)
    (hpassive : c.work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satLengthCheckPassiveTM.step c = some c' ∧
      c'.state = .scan ∧
      c'.input.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
      c'.input.head = k + 2 ∧
      (c'.work ⟨0, by omega⟩).HasCounterRemainder (k + 1) B ∧
      c'.work ⟨1, by omega⟩ = c.work ⟨1, by omega⟩ ∧
      c'.output = c.output := by
  have hread_input : c.input.read = Γ.ofBool (α[k]'hk) := by
    show c.input.cells c.input.head = _
    rw [hinput_head, hinput_cells]
    exact Tape.init_ofBool_cells_lt α k hk
  have hinput_nb : c.input.read ≠ Γ.blank := by
    rw [hread_input]
    exact Γ.ofBool_ne_blank _
  have hcounter_read : (c.work ⟨0, by omega⟩).read = Γ.one :=
    Tape.hasCounterRemainder_read_one_of_remaining hcounter hkB
  have hpassive_read : (c.work ⟨1, by omega⟩).read ≠ Γ.start := by
    rw [hpassive]
    exact started_input_read_ne_start β
  have hout' : c.output.read ≠ Γ.start := by
    rw [hout]
    exact started_blank_output_read_ne_start
  simp only [TM.step, hstate, satLengthCheckPassiveTM, hinput_nb, hcounter_read]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Tape.move_cells]
    exact hinput_cells
  · simp [Tape.move, hinput_head]
  · simpa using Tape.hasCounterRemainder_consume hcounter hkB
  · change TM.transitionTape (c.work ⟨1, by omega⟩) = c.work ⟨1, by omega⟩
    exact TM.transitionTape_eq_self hpassive_read
  · change TM.transitionTape c.output = c.output
    exact TM.transitionTape_eq_self hout'

private theorem satLengthCheckPassive_scan_accept_step (α β : List Bool) (B : ℕ)
    (c : Cfg 2 satLengthCheckPassiveTM.Q)
    (hstate : c.state = .scan)
    (hinput_cells : c.input.cells = (Tape.init (α.map Γ.ofBool)).cells)
    (hinput_head : c.input.head = α.length + 1)
    (_hcounter : (c.work ⟨0, by omega⟩).HasCounterRemainder α.length B)
    (hpassive : c.work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satLengthCheckPassiveTM.step c = some c' ∧
      satLengthCheckPassiveTM.halted c' ∧
      c'.input.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
      c'.work ⟨1, by omega⟩ = c.work ⟨1, by omega⟩ ∧
      c'.output.cells 1 = Γ.one := by
  have hread_input : c.input.read = Γ.blank := by
    show c.input.cells c.input.head = Γ.blank
    rw [hinput_head, hinput_cells]
    exact Tape.init_ofBool_cells_ge α α.length le_rfl
  have hpassive_read : (c.work ⟨1, by omega⟩).read ≠ Γ.start := by
    rw [hpassive]
    exact started_input_read_ne_start β
  have hout_read : c.output.read = Γ.blank := by
    rw [hout]
    simp [Tape.read, Tape.move, Tape.init]
  simp only [TM.step, hstate, satLengthCheckPassiveTM, hread_input, hout_read]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · rw [Tape.move_cells]
    exact hinput_cells
  · change TM.transitionTape (c.work ⟨1, by omega⟩) = c.work ⟨1, by omega⟩
    exact TM.transitionTape_eq_self hpassive_read
  · have ho_head : c.output.head = 1 := by
      rw [hout]
      simp [Tape.move, Tape.init]
    simp [Tape.writeAndMove, Tape.move, Tape.write, ho_head, TM.idleDir, Γw.toΓ]

private theorem satLengthCheckPassive_scan_reject_step (α β : List Bool) (B : ℕ)
    (c : Cfg 2 satLengthCheckPassiveTM.Q)
    (hB : B < α.length)
    (hstate : c.state = .scan)
    (hinput_cells : c.input.cells = (Tape.init (α.map Γ.ofBool)).cells)
    (hinput_head : c.input.head = B + 1)
    (hcounter : (c.work ⟨0, by omega⟩).HasCounterRemainder B B)
    (hpassive : c.work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satLengthCheckPassiveTM.step c = some c' ∧
      satLengthCheckPassiveTM.halted c' ∧
      c'.input.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
      c'.work ⟨1, by omega⟩ = c.work ⟨1, by omega⟩ ∧
      c'.output.cells 1 = Γ.zero := by
  have hread_input : c.input.read ≠ Γ.blank := by
    have hcell : c.input.read = Γ.ofBool (α[B]'hB) := by
      show c.input.cells c.input.head = _
      rw [hinput_head, hinput_cells]
      exact Tape.init_ofBool_cells_lt α B hB
    rw [hcell]
    exact Γ.ofBool_ne_blank _
  have hread_counter : (c.work ⟨0, by omega⟩).read = Γ.blank :=
    Tape.hasCounterRemainder_read_blank_of_done hcounter
  have hpassive_read : (c.work ⟨1, by omega⟩).read ≠ Γ.start := by
    rw [hpassive]
    exact started_input_read_ne_start β
  have hout_read : c.output.read = Γ.blank := by
    rw [hout]
    simp [Tape.read, Tape.move, Tape.init]
  simp only [TM.step, hstate, satLengthCheckPassiveTM, hread_input, hread_counter, hout_read]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · rw [Tape.move_cells]
    exact hinput_cells
  · change TM.transitionTape (c.work ⟨1, by omega⟩) = c.work ⟨1, by omega⟩
    exact TM.transitionTape_eq_self hpassive_read
  · have ho_head : c.output.head = 1 := by
      rw [hout]
      simp [Tape.move, Tape.init]
    simp [Tape.writeAndMove, Tape.move, Tape.write, ho_head, TM.idleDir, Γw.toΓ]

private theorem satLengthCheckPassive_scan_prefix_loop (α β : List Bool) (B : ℕ) :
    ∀ (m k : ℕ) (c : Cfg 2 satLengthCheckPassiveTM.Q),
      k + m ≤ α.length →
      k + m ≤ B →
      c.state = .scan →
      c.input.cells = (Tape.init (α.map Γ.ofBool)).cells →
      c.input.head = k + 1 →
      (c.work ⟨0, by omega⟩).HasCounterRemainder k B →
      c.work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right →
      c.output = (Tape.init []).move Dir3.right →
      ∃ c',
        satLengthCheckPassiveTM.reachesIn m c c' ∧
        c'.state = .scan ∧
        c'.input.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
        c'.input.head = k + m + 1 ∧
        (c'.work ⟨0, by omega⟩).HasCounterRemainder (k + m) B ∧
        c'.work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right ∧
        c'.output = (Tape.init []).move Dir3.right := by
  intro m
  induction m with
  | zero =>
      intro k c _ _ hstate hinput_cells hinput_head hcounter hpassive hout
      refine ⟨c, .zero, hstate, hinput_cells, ?_, ?_, hpassive, hout⟩
      · omega
      · simpa using hcounter
  | succ m ih =>
      intro k c hlen hbound hstate hinput_cells hinput_head hcounter hpassive hout
      have hk : k < α.length := by omega
      have hkB : k < B := by omega
      obtain ⟨c1, hstep, hstate1, hcells1, hhead1, hcounter1, hpassive1, hout1⟩ :=
        satLengthCheckPassive_scan_continue_step α β B k c hk hkB hstate hinput_cells
          hinput_head hcounter hpassive hout
      have hlen1 : k + 1 + m ≤ α.length := by omega
      have hbound1 : k + 1 + m ≤ B := by omega
      have hpassive1_started :
          c1.work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right := by
        rw [hpassive1]
        exact hpassive
      have hout1_started : c1.output = (Tape.init []).move Dir3.right := by
        rw [hout1]
        exact hout
      obtain ⟨c', hreach, hstate', hcells', hhead', hcounter', hpassive', hout'⟩ :=
        ih (k + 1) c1 hlen1 hbound1 hstate1 hcells1 hhead1 hcounter1 hpassive1_started
          hout1_started
      refine ⟨c', .step hstep hreach, hstate', hcells', ?_, ?_, hpassive', hout'⟩
      · rw [hhead']
        omega
      · convert hcounter' using 1
        omega

/-- Started-tape correctness for `satLengthCheckPassiveTM`: the machine checks
`|α| ≤ B` while leaving work tape `1` unchanged. -/
theorem satLengthCheckPassiveTM_started_hoareTime (B : ℕ) (α β : List Bool) :
    satLengthCheckPassiveTM.HoareTime
      (fun inp work out =>
        inp = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨0, by omega⟩).HasUnaryCounter B ∧
        work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
        work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right ∧
        out.cells 1 = (if α.length ≤ B then Γ.one else Γ.zero))
      (satLengthCheckTime α.length) := by
  intro inp work out hpre
  rcases hpre with ⟨hinput, hcounter, hpassive, hout⟩
  let c0 : Cfg 2 satLengthCheckPassiveTM.Q :=
    { state := satLengthCheckPassiveTM.qstart, input := inp, work := work, output := out }
  obtain ⟨c1, hstep1, hstate1, hinput1, hwork01, hwork11, hout1⟩ :=
    satLengthCheckPassive_init_step α β B c0 rfl hinput hcounter hpassive hout
  have hcells0 : c0.input.cells = (Tape.init (α.map Γ.ofBool)).cells := by
    change inp.cells = (Tape.init (α.map Γ.ofBool)).cells
    rw [hinput]
    exact Tape.move_cells _ _
  have hhead0 : c0.input.head = 1 := by
    change inp.head = 1
    rw [hinput]
    simp [Tape.move, Tape.init]
  have hcells1 : c1.input.cells = (Tape.init (α.map Γ.ofBool)).cells := by
    rw [hinput1]
    exact hcells0
  have hhead1 : c1.input.head = 1 := by
    rw [hinput1]
    exact hhead0
  have hcounter1 : (c1.work ⟨0, by omega⟩).HasCounterRemainder 0 B := by
    rw [hwork01]
    exact (Tape.hasUnaryCounter_iff_remainder_zero).mp hcounter
  have hpassive1 : c1.work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right := by
    rw [hwork11]
    exact hpassive
  have hout1_started : c1.output = (Tape.init []).move Dir3.right := by
    rw [hout1]
    exact hout
  by_cases hle : α.length ≤ B
  · obtain ⟨c2, hreach2, hstate2, hcells2, hhead2, hcounter2, hpassive2, hout2⟩ :=
      satLengthCheckPassive_scan_prefix_loop α β B α.length 0 c1
        (by omega) (by simpa using hle) hstate1 hcells1 hhead1 hcounter1 hpassive1 hout1_started
    obtain ⟨c3, hstep3, hhalt3, hcells3, hpassive3, hout3⟩ :=
      satLengthCheckPassive_scan_accept_step α β B c2 hstate2 hcells2
        (by simpa using hhead2) (by simpa using hcounter2) hpassive2 hout2
    have hreach_total : satLengthCheckPassiveTM.reachesIn (1 + α.length + 1) c0 c3 := by
      simpa [Nat.add_assoc] using
        TM.reachesIn_trans _ (.step hstep1 .zero)
          (TM.reachesIn_trans _ hreach2 (.step hstep3 .zero))
    refine ⟨c3, 1 + α.length + 1, by
      simp [satLengthCheckTime]
      omega, hreach_total, hhalt3, ?_⟩
    exact ⟨hcells3, by rw [hpassive3]; exact hpassive2, by simpa [hle] using hout3⟩
  · have hlt : B < α.length := by omega
    obtain ⟨c2, hreach2, hstate2, hcells2, hhead2, hcounter2, hpassive2, hout2⟩ :=
      satLengthCheckPassive_scan_prefix_loop α β B B 0 c1
        (by omega) (by omega) hstate1 hcells1 hhead1 hcounter1 hpassive1 hout1_started
    obtain ⟨c3, hstep3, hhalt3, hcells3, hpassive3, hout3⟩ :=
      satLengthCheckPassive_scan_reject_step α β B c2 hlt hstate2 hcells2
        (by simpa using hhead2) (by simpa using hcounter2) hpassive2 hout2
    have hreach_total : satLengthCheckPassiveTM.reachesIn (1 + B + 1) c0 c3 := by
      simpa [Nat.add_assoc] using
        TM.reachesIn_trans _ (.step hstep1 .zero)
          (TM.reachesIn_trans _ hreach2 (.step hstep3 .zero))
    refine ⟨c3, 1 + B + 1, by
      simp [satLengthCheckTime]
      omega, hreach_total, hhalt3, ?_⟩
    exact ⟨hcells3, by rw [hpassive3]; exact hpassive2, by simpa [hle] using hout3⟩

/-- Three-work-tape length checker obtained by retargeting the input of
`satLengthCheckPassiveTM` to work tape `2`. Tape `0` stores the unary bound,
tape `1` is preserved, and tape `2` provides the witness bits. -/
def satLengthCheck3TM : TM 3 :=
  TM.retargetInput satLengthCheckPassiveTM

/-- Virtual-input/work-tape version of `satLengthCheckPassiveTM`: work tape
`2` supplies the witness bits, work tape `0` supplies the unary bound, and
work tape `1` is preserved exactly. -/
theorem satLengthCheck3TM_started_hoareTime (B : ℕ) (α β : List Bool) :
    satLengthCheck3TM.HoareTime
      (fun _inp work out =>
        (work ⟨2, by omega⟩) = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨0, by omega⟩).HasUnaryCounter B ∧
        work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨0, by omega⟩).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (work ⟨0, by omega⟩).cells j ≠ Γ.start) ∧
        out = (Tape.init []).move Dir3.right)
      (fun _inp work out =>
        work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨2, by omega⟩).cells = (Tape.init (α.map Γ.ofBool)).cells ∧
        out.cells 1 = (if α.length ≤ B then Γ.one else Γ.zero))
      (satLengthCheckTime α.length) := by
  have hmove_right_invariant : ∀ {t : Tape}, Tape.StartInvariant t →
      Tape.StartInvariant (t.move Dir3.right) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · simpa [Tape.move_cells] using ht.1
    · intro j hj
      simpa [Tape.move_cells] using ht.2 j hj
  have hlen :
      satLengthCheckPassiveTM.HoareTime
        (fun inp work out =>
          inp = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
          (work ⟨0, by omega⟩).HasUnaryCounter B ∧
          work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right ∧
          (work ⟨0, by omega⟩).cells 0 = Γ.start ∧
          (∀ j, j ≥ 1 → (work ⟨0, by omega⟩).cells j ≠ Γ.start) ∧
          out = (Tape.init []).move Dir3.right)
        (fun inp work out =>
          inp.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
          work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right ∧
          out.cells 1 = (if α.length ≤ B then Γ.one else Γ.zero))
        (satLengthCheckTime α.length) :=
    (satLengthCheckPassiveTM_started_hoareTime B α β).weaken_pre (by
      intro inp work out hpre
      exact ⟨hpre.1, hpre.2.1, hpre.2.2.1, hpre.2.2.2.2.2⟩)
  have hret := TM.retargetInput_hoareTime (M := satLengthCheckPassiveTM)
    hlen
    (hpre_inp := by
      intro _inp work out hpre
      rcases hpre with ⟨hvin, _hrest⟩
      rw [hvin]
      exact hmove_right_invariant (Tape.StartInvariant.init_ofBool α))
    (hpre_work := by
      intro _inp work out hpre i
      rcases hpre with ⟨_hvin, hrest⟩
      rcases hrest with ⟨_hcounter, hrest⟩
      rcases hrest with ⟨hpassive, hrest⟩
      rcases hrest with ⟨hcell0, hrest⟩
      rcases hrest with ⟨hnostart, _hout⟩
      by_cases hi0 : i = ⟨0, by omega⟩
      · subst hi0
        exact ⟨hcell0, hnostart⟩
      · have hi1 := fin2_ne_zero_eq_one i hi0
        subst hi1
        rw [hpassive]
        exact hmove_right_invariant (Tape.StartInvariant.init_ofBool β))
    (hpre_out := by
      intro _inp work out hpre
      rcases hpre with ⟨_hvin, hrest⟩
      rcases hrest with ⟨_hcounter, hrest⟩
      rcases hrest with ⟨_hpassive, hrest⟩
      rcases hrest with ⟨_hcell0, hrest⟩
      rcases hrest with ⟨_hnostart, hout⟩
      rw [hout]
      exact hmove_right_invariant (Tape.StartInvariant.init_nil))
  have hret' : satLengthCheck3TM.HoareTime
      (fun _inp work out =>
        (work ⟨2, by omega⟩) = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨0, by omega⟩).HasUnaryCounter B ∧
        work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨0, by omega⟩).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (work ⟨0, by omega⟩).cells j ≠ Γ.start) ∧
        out = (Tape.init []).move Dir3.right)
      (fun _inp work out =>
        ∃ vin : Tape, ∃ innerWork : Fin 2 → Tape,
          (vin.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
            innerWork ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right ∧
            out.cells 1 = (if α.length ≤ B then Γ.one else Γ.zero)) ∧
          (∀ i : Fin 2, work ⟨i.val, by omega⟩ = innerWork i) ∧
          work ⟨2, by omega⟩ = vin)
      (satLengthCheckTime α.length) := by
    simpa [satLengthCheck3TM] using hret
  refine hret'.strengthen_post ?_
  intro _inp work out hpost
  rcases hpost with ⟨vin, innerWork, hinner, hmap, hvin⟩
  exact ⟨(hmap ⟨1, by omega⟩).trans hinner.2.1,
    by rw [hvin]; exact hinner.1,
    hinner.2.2⟩

/-- Tail of the SAT witness-length verifier after the witness has been copied
to tape `2`: rewind tapes `1` and `2`, then run `satLengthCheck3TM`. -/
def satWitnessLengthTailTM : TM 3 :=
  TM.seqTM (TM.rewindWorkTM ⟨1, by omega⟩) <|
    TM.seqTM (TM.rewindWorkTM ⟨2, by omega⟩) satLengthCheck3TM

/-- Time bound for `satWitnessLengthTailTM`. -/
def satWitnessLengthTailTime (αLen : ℕ) : ℕ :=
  (αLen + 1 + 2) + 1 + (αLen + 1 + 2) + 1 + satLengthCheckTime αLen

-- ════════════════════════════════════════════════════════════════════════
-- Streaming CNF evaluator
-- ════════════════════════════════════════════════════════════════════════

/-- Parser/evaluator mode for the deterministic CNF evaluator.

`boundary cnf clause empty` means the machine is between raw literals. `cnf`
is the value of all completed clauses so far, `clause` is the disjunction
accumulated for the current clause, and `empty` records whether the current
clause has no completed literals. `inLit ... sign` means a raw literal has
started with sign bit `sign`; each following raw bit must be `true`, and the
assignment work-tape head tracks the current unary variable index. -/
inductive SatEvalMode where
  /-- Between raw literals: `cnf` is the conjunction of completed clauses,
  `clause` the disjunction so far, `empty` whether the clause has no literals. -/
  | boundary (cnf clause empty : Bool)
  /-- Inside a raw literal with sign bit `sign`; the assignment head tracks
  the unary variable index. -/
  | inLit (cnf clause empty sign : Bool)
  deriving DecidableEq, Repr

instance : Fintype SatEvalMode where
  elems :=
    (Finset.univ.image fun p : Bool × Bool × Bool =>
      SatEvalMode.boundary p.1 p.2.1 p.2.2) ∪
    (Finset.univ.image fun p : Bool × Bool × Bool × Bool =>
      SatEvalMode.inLit p.1 p.2.1 p.2.2.1 p.2.2.2)
  complete := by
    intro m
    cases m with
    | boundary cnf clause empty =>
        simp
    | inLit cnf clause empty sign =>
        simp

/-- Control states for the streaming CNF evaluator. The input tape supplies the
SAT encoding `z`; work tape `0` supplies the assignment `α`. -/
inductive SatEvalPhase where
  /-- Reading the first bit of a doubled-bit token in mode `mode`. -/
  | readFirst (mode : SatEvalMode)
  /-- Reading the second bit of a token whose first bit was `first`. -/
  | readSecond (mode : SatEvalMode) (first : Bool)
  /-- Rewinding the assignment tape to its left marker before continuing
  in mode `mode`. -/
  | rewindAlpha (mode : SatEvalMode)
  /-- Halt state: the verdict has been written to the output tape. -/
  | done
  deriving DecidableEq, Repr

instance : Fintype SatEvalPhase where
  elems :=
    insert SatEvalPhase.done <|
      (Finset.univ.image SatEvalPhase.readFirst) ∪
      (Finset.univ.image fun p : SatEvalMode × Bool =>
        SatEvalPhase.readSecond p.1 p.2) ∪
      (Finset.univ.image SatEvalPhase.rewindAlpha)
  complete := by
    intro q
    cases q with
    | done =>
        simp
    | readFirst mode =>
        simp
    | readSecond mode first =>
        simp
    | rewindAlpha mode =>
        simp

/-- Writable tape symbol encoding of a Boolean. -/
def boolWrite (b : Bool) : Γw :=
  if b then Γw.one else Γw.zero

/-- Decodes a tape symbol as a bit when it is `0` or `1`. -/
def readBit? : Γ → Option Bool
  | Γ.zero => some false
  | Γ.one => some true
  | _ => none

/-- Assignment value represented by the symbol under the assignment-tape head. -/
def assignmentBitAtHead (g : Γ) : Bool :=
  g = Γ.one

/-- Truth value of a signed literal at the assignment-tape head. -/
def literalValueAtHead (sign : Bool) (g : Γ) : Bool :=
  assignmentBitAtHead g == sign

private theorem assignmentBitAtHead_initTape_eq_get (α : Assignment) (var : ℕ) :
    assignmentBitAtHead ((Tape.init (α.map Γ.ofBool)).cells (var + 1)) =
      Assignment.get α var := by
  by_cases h : var < α.length
  · rw [Tape.init_ofBool_cells_lt α var h]
    simp [assignmentBitAtHead, Assignment.get, List.getElem?_eq_getElem h]
    cases α[var]'h <;> simp [Γ.ofBool]
  · have hge : var ≥ α.length := by omega
    rw [Tape.init_ofBool_cells_ge α var hge]
    simp [assignmentBitAtHead, Assignment.get, List.getElem?_eq_none hge]

private theorem literalValueAtHead_initTape_eq_litEval
    (α : Assignment) (sign : Bool) (var : ℕ) :
    literalValueAtHead sign ((Tape.init (α.map Γ.ofBool)).cells (var + 1)) =
      (Assignment.get α var == sign) := by
  simp [literalValueAtHead, assignmentBitAtHead_initTape_eq_get]

/-- Output written when the evaluator reaches the end of the encoded formula. -/
def finishEvalMode : SatEvalMode → Γw
  | .boundary cnf _clause empty => boolWrite (cnf && empty)
  | .inLit .. => Γw.zero

/-- Rejecting transition that preserves the current tape contents. -/
def satEvalReject {n : ℕ} (state : SatEvalPhase)
    (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ) :
    SatEvalPhase × (Fin n → Γw) × Γw × Dir3 × (Fin n → Dir3) × Dir3 :=
  (state, fun i => TM.readBackWrite (wHeads i), Γw.zero,
    TM.idleDir iHead, fun i => TM.idleDir (wHeads i), TM.idleDir oHead)

/-- Pure evaluator-state transition for one decoded encoding token. -/
def satEvalTokenStep (mode : SatEvalMode) (tok : EncToken) (αHead : Γ) :
    SatEvalPhase × Dir3 × Γw :=
  match mode with
  | .boundary cnf clause empty =>
      match tok with
      | .bit sign => (.readFirst (.inLit cnf clause empty sign), Dir3.stay, Γw.blank)
      | .litSep => (.done, Dir3.stay, Γw.zero)
      | .clauseSep => (.readFirst (.boundary (cnf && clause) false true), Dir3.stay, Γw.blank)
  | .inLit cnf clause _empty sign =>
      match tok with
      | .bit b =>
          if b then
            (.readFirst (.inLit cnf clause false sign), Dir3.right, Γw.blank)
          else
            (.done, Dir3.stay, Γw.zero)
      | .litSep =>
          let litVal := literalValueAtHead sign αHead
          (.rewindAlpha (.boundary cnf (clause || litVal) false), Dir3.stay, Γw.blank)
      | .clauseSep =>
          (.done, Dir3.stay, Γw.zero)

/-- Decodes the fixed two-bit representation of an encoding token. -/
def tokenOfBits (first second : Bool) : EncToken :=
  match first, second with
  | false, false => .bit false
  | true, true => .bit true
  | false, true => .litSep
  | true, false => .clauseSep

/-- Transition function of the one-work-tape SAT evaluator. -/
def satEvalDelta :
    SatEvalPhase → Γ → (Fin 1 → Γ) → Γ →
      SatEvalPhase × (Fin 1 → Γw) × Γw × Dir3 × (Fin 1 → Dir3) × Dir3 :=
  fun state iHead wHeads oHead =>
    let αHead := wHeads ⟨0, by omega⟩
    match state with
    | .readFirst mode =>
        if iHead = Γ.blank then
          (.done,
            fun i => TM.readBackWrite (wHeads i),
            finishEvalMode mode,
            TM.idleDir iHead,
            fun i => TM.idleDir (wHeads i),
            TM.idleDir oHead)
        else
          match readBit? iHead with
          | some b =>
              (.readSecond mode b,
                fun i => TM.readBackWrite (wHeads i),
                TM.readBackWrite oHead,
                Dir3.right,
                fun i => TM.idleDir (wHeads i),
                TM.idleDir oHead)
          | none =>
              satEvalReject .done iHead wHeads oHead
    | .readSecond mode first =>
        match readBit? iHead with
        | some second =>
            let (nextState, αDir, outWrite) :=
              satEvalTokenStep mode (tokenOfBits first second) αHead
            (nextState,
              fun i => TM.readBackWrite (wHeads i),
              outWrite,
              Dir3.right,
              fun i =>
                if i = ⟨0, by omega⟩ then
                  if αHead = Γ.start then Dir3.right else αDir
                else
                  TM.idleDir (wHeads i),
              TM.idleDir oHead)
        | none =>
            satEvalReject .done iHead wHeads oHead
    | .rewindAlpha mode =>
        if αHead = Γ.start then
          (.readFirst mode,
            fun i => TM.readBackWrite (wHeads i),
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i => if i = ⟨0, by omega⟩ then Dir3.right else TM.idleDir (wHeads i),
            TM.idleDir oHead)
        else
          (.rewindAlpha mode,
            fun i => TM.readBackWrite (wHeads i),
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i => if i = ⟨0, by omega⟩ then Dir3.left else TM.idleDir (wHeads i),
            TM.idleDir oHead)
    | .done =>
        TM.allIdle .done iHead wHeads oHead

private theorem satEvalDelta_right_of_start
    (state : SatEvalPhase) (iHead : Γ) (wHeads : Fin 1 → Γ) (oHead : Γ) :
    let tr := satEvalDelta state iHead wHeads oHead
    (iHead = Γ.start → tr.2.2.2.1 = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → tr.2.2.2.2.1 i = Dir3.right) ∧
    (oHead = Γ.start → tr.2.2.2.2.2 = Dir3.right) := by
  aesop (add simp [satEvalDelta, satEvalReject, readBit?, satEvalTokenStep,
    tokenOfBits, TM.allIdle, TM.idleDir_right_of_start,
    TM.rightOfStart_allIdle])

/-- Deterministic evaluator for a SAT-encoded CNF on the input tape and an
assignment on work tape `0`.

The evaluator tokenizes the input in two-bit groups. It rejects odd-length
inputs and malformed raw literals, treats assignment positions beyond `α` as
`false` by reading blanks, and writes the Boolean value of the decoded CNF to
output cell `1`. The formal correctness theorem is the next layer; this
definition is the concrete finite-state machine that theorem targets. -/
def satEvalOnInputTM : TM 1 where
  Q := SatEvalPhase
  qstart := .readFirst (.boundary true false true)
  qhalt := .done
  δ := satEvalDelta
  δ_right_of_start := by
    intro state iHead wHeads oHead
    exact satEvalDelta_right_of_start state iHead wHeads oHead

private theorem satEval_readFirst_bit_step (mode : SatEvalMode) (b : Bool)
    (c : Cfg 1 satEvalOnInputTM.Q)
    (hstate : c.state = .readFirst mode)
    (hread : c.input.read = Γ.ofBool b)
    (hwork : (c.work ⟨0, by omega⟩).read ≠ Γ.start)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satEvalOnInputTM.step c = some c' ∧
      c'.state = .readSecond mode b ∧
      c'.input = c.input.move Dir3.right ∧
      c'.work = c.work ∧
      c'.output = c.output := by
  have hnot_blank : c.input.read ≠ Γ.blank := by
    rw [hread]
    exact Γ.ofBool_ne_blank b
  have hout_read : c.output.read ≠ Γ.start := by
    rw [hout]
    exact started_blank_output_read_ne_start
  let c' : Cfg 1 satEvalOnInputTM.Q :=
    { state := .readSecond mode b
      input := c.input.move Dir3.right
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read) <|
          TM.idleDir (c.work i).read
      output := c.output.writeAndMove (TM.readBackWrite c.output.read) <|
        TM.idleDir c.output.read }
  refine ⟨c', ?_, rfl, rfl, ?_, ?_⟩
  · cases b <;>
      simp [c', satEvalOnInputTM, TM.step, satEvalDelta, hstate, hread,
        readBit?, Γ.ofBool]
  · funext i
    have hi0 : i = ⟨0, by omega⟩ := by
      apply Fin.ext
      omega
    subst hi0
    exact TM.transitionTape_eq_self hwork
  · exact TM.transitionTape_eq_self hout_read

private theorem satEval_readFirst_blank_step (mode : SatEvalMode)
    (c : Cfg 1 satEvalOnInputTM.Q)
    (hstate : c.state = .readFirst mode)
    (hread : c.input.read = Γ.blank)
    (hwork : (c.work ⟨0, by omega⟩).read ≠ Γ.start)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satEvalOnInputTM.step c = some c' ∧
      satEvalOnInputTM.halted c' ∧
      c'.input = c.input ∧
      c'.work = c.work ∧
      c'.output.cells 1 = (finishEvalMode mode).toΓ := by
  have hout_read : c.output.read = Γ.blank := by
    rw [hout]
    simp [Tape.read, Tape.move, Tape.init]
  let c' : Cfg 1 satEvalOnInputTM.Q :=
    { state := .done
      input := c.input.move (TM.idleDir c.input.read)
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read) <|
          TM.idleDir (c.work i).read
      output := c.output.writeAndMove (finishEvalMode mode) (TM.idleDir c.output.read) }
  refine ⟨c', ?_, rfl, ?_, ?_, ?_⟩
  · simp [c', satEvalOnInputTM, TM.step, satEvalDelta, hstate, hread]
  · have hinp : c.input.read ≠ Γ.start := by rw [hread]; simp
    exact TM.transitionInput_eq_self hinp
  · funext i
    have hi0 : i = ⟨0, by omega⟩ := by
      apply Fin.ext
      omega
    subst hi0
    exact TM.transitionTape_eq_self hwork
  · have ho_head : c.output.head = 1 := by
      rw [hout]
      simp [Tape.move, Tape.init]
    simp [c', Tape.writeAndMove, Tape.write, Tape.move, TM.idleDir, hout_read,
      ho_head, Γw.toΓ]

private theorem satEval_readSecond_bit_step (mode : SatEvalMode) (first second : Bool)
    (c : Cfg 1 satEvalOnInputTM.Q)
    (hstate : c.state = .readSecond mode first)
    (hread : c.input.read = Γ.ofBool second)
    (hwork : (c.work ⟨0, by omega⟩).read ≠ Γ.start)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    let tr := satEvalTokenStep mode (tokenOfBits first second) (c.work ⟨0, by omega⟩).read
    ∃ c', satEvalOnInputTM.step c = some c' ∧
      c'.state = tr.1 ∧
      c'.input = c.input.move Dir3.right ∧
      c'.work ⟨0, by omega⟩ =
        (c.work ⟨0, by omega⟩).writeAndMove
          (TM.readBackWrite (c.work ⟨0, by omega⟩).read).toΓ tr.2.1 ∧
      c'.output = c.output.writeAndMove tr.2.2.toΓ (TM.idleDir c.output.read) := by
  have hout_read : c.output.read ≠ Γ.start := by
    rw [hout]
    exact started_blank_output_read_ne_start
  let tr := satEvalTokenStep mode (tokenOfBits first second) (c.work ⟨0, by omega⟩).read
  let c' : Cfg 1 satEvalOnInputTM.Q :=
    { state := tr.1
      input := c.input.move Dir3.right
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read) <|
          if i = ⟨0, by omega⟩ then
            if (c.work ⟨0, by omega⟩).read = Γ.start then Dir3.right else tr.2.1
          else
            TM.idleDir (c.work i).read
      output := c.output.writeAndMove tr.2.2 (TM.idleDir c.output.read) }
  refine ⟨c', ?_, rfl, rfl, ?_, rfl⟩
  · cases second <;>
      simp [c', tr, satEvalOnInputTM, TM.step, satEvalDelta, hstate, hread,
        readBit?, Γ.ofBool]
  · have hwork0 : (c.work (0 : Fin 1)).read ≠ Γ.start := by
      simpa using hwork
    simp [c', tr, hwork0]

private theorem satEval_readSecond_blank_step (mode : SatEvalMode) (first : Bool)
    (c : Cfg 1 satEvalOnInputTM.Q)
    (hstate : c.state = .readSecond mode first)
    (hread : c.input.read = Γ.blank)
    (hwork : (c.work ⟨0, by omega⟩).read ≠ Γ.start)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satEvalOnInputTM.step c = some c' ∧
      satEvalOnInputTM.halted c' ∧
      c'.input = c.input ∧
      c'.work = c.work ∧
      c'.output.cells 1 = Γ.zero := by
  have hout_read : c.output.read = Γ.blank := by
    rw [hout]
    simp [Tape.read, Tape.move, Tape.init]
  let c' : Cfg 1 satEvalOnInputTM.Q :=
    { state := .done
      input := c.input.move (TM.idleDir c.input.read)
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read) <|
          TM.idleDir (c.work i).read
      output := c.output.writeAndMove Γw.zero (TM.idleDir c.output.read) }
  refine ⟨c', ?_, rfl, ?_, ?_, ?_⟩
  · cases first <;>
      simp [c', satEvalOnInputTM, TM.step, satEvalDelta, satEvalReject,
        hstate, hread, readBit?]
  · have hinp : c.input.read ≠ Γ.start := by rw [hread]; simp
    exact TM.transitionInput_eq_self hinp
  · funext i
    have hi0 : i = ⟨0, by omega⟩ := by
      apply Fin.ext
      omega
    subst hi0
    exact TM.transitionTape_eq_self hwork
  · have ho_head : c.output.head = 1 := by
      rw [hout]
      simp [Tape.move, Tape.init]
    simp [c', Tape.writeAndMove, Tape.write, Tape.move, TM.idleDir, hout_read,
      ho_head, Γw.toΓ]

private theorem satEval_rewindAlpha_left_step (mode : SatEvalMode)
    (c : Cfg 1 satEvalOnInputTM.Q)
    (hstate : c.state = .rewindAlpha mode)
    (hinp : c.input.read ≠ Γ.start)
    (hread : (c.work ⟨0, by omega⟩).read ≠ Γ.start)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satEvalOnInputTM.step c = some c' ∧
      c'.state = .rewindAlpha mode ∧
      c'.input = c.input ∧
      (c'.work ⟨0, by omega⟩).head = (c.work ⟨0, by omega⟩).head - 1 ∧
      (c'.work ⟨0, by omega⟩).cells = (c.work ⟨0, by omega⟩).cells ∧
      c'.output = c.output := by
  have hout_read : c.output.read ≠ Γ.start := by
    rw [hout]
    exact started_blank_output_read_ne_start
  let c' : Cfg 1 satEvalOnInputTM.Q :=
    { state := .rewindAlpha mode
      input := c.input.move (TM.idleDir c.input.read)
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read) <|
          if i = ⟨0, by omega⟩ then Dir3.left else TM.idleDir (c.work i).read
      output := c.output.writeAndMove (TM.readBackWrite c.output.read) <|
        TM.idleDir c.output.read }
  refine ⟨c', ?_, rfl, ?_, ?_, ?_, ?_⟩
  · have hread0 : (c.work (0 : Fin 1)).read ≠ Γ.start := by
      simpa using hread
    simp [c', satEvalOnInputTM, TM.step, satEvalDelta, hstate, hread0]
  · exact TM.transitionInput_eq_self hinp
  · simp [c', Tape.writeAndMove, Tape.move, Tape.write_head]
  · exact TM.tape_readBackWrite_preserves _ _ (Or.inr hread)
  · exact TM.transitionTape_eq_self hout_read

private theorem satEval_rewindAlpha_base_step (mode : SatEvalMode)
    (c : Cfg 1 satEvalOnInputTM.Q)
    (hstate : c.state = .rewindAlpha mode)
    (hinp : c.input.read ≠ Γ.start)
    (hread : (c.work ⟨0, by omega⟩).read = Γ.start)
    (hnostart : ∀ j, j ≥ 1 → (c.work ⟨0, by omega⟩).cells j ≠ Γ.start)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satEvalOnInputTM.step c = some c' ∧
      c'.state = .readFirst mode ∧
      c'.input = c.input ∧
      (c'.work ⟨0, by omega⟩).head = 1 ∧
      (c'.work ⟨0, by omega⟩).cells = (c.work ⟨0, by omega⟩).cells ∧
      c'.output = c.output := by
  have hout_read : c.output.read ≠ Γ.start := by
    rw [hout]
    exact started_blank_output_read_ne_start
  let c' : Cfg 1 satEvalOnInputTM.Q :=
    { state := .readFirst mode
      input := c.input.move (TM.idleDir c.input.read)
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read) <|
          if i = ⟨0, by omega⟩ then Dir3.right else TM.idleDir (c.work i).read
      output := c.output.writeAndMove (TM.readBackWrite c.output.read) <|
        TM.idleDir c.output.read }
  have hhead0 : (c.work ⟨0, by omega⟩).head = 0 := by
    by_contra hne
    have hge : (c.work ⟨0, by omega⟩).head ≥ 1 := by omega
    exact hnostart (c.work ⟨0, by omega⟩).head hge (by simpa [Tape.read] using hread)
  refine ⟨c', ?_, rfl, ?_, ?_, ?_, ?_⟩
  · have hread0 : (c.work (0 : Fin 1)).read = Γ.start := by
      simpa using hread
    simp [c', satEvalOnInputTM, TM.step, satEvalDelta, hstate, hread0]
  · exact TM.transitionInput_eq_self hinp
  · have hhead00 : (c.work (0 : Fin 1)).head = 0 := by
      simpa using hhead0
    simp [c', Tape.writeAndMove, Tape.move, Tape.write_head, hhead00]
  · exact TM.tape_readBackWrite_preserves _ _ (Or.inl hhead0)
  · exact TM.transitionTape_eq_self hout_read

private theorem satEval_rewindAlpha_loop (mode : SatEvalMode) :
    ∀ (p : ℕ) (c : Cfg 1 satEvalOnInputTM.Q),
      c.state = .rewindAlpha mode →
      c.input.read ≠ Γ.start →
      (c.work ⟨0, by omega⟩).cells 0 = Γ.start →
      (∀ j, j ≥ 1 → (c.work ⟨0, by omega⟩).cells j ≠ Γ.start) →
      (c.work ⟨0, by omega⟩).head = p →
      c.output = (Tape.init []).move Dir3.right →
      ∃ c',
        satEvalOnInputTM.reachesIn (p + 1) c c' ∧
        c'.state = .readFirst mode ∧
        c'.input = c.input ∧
        (c'.work ⟨0, by omega⟩).head = 1 ∧
        (c'.work ⟨0, by omega⟩).cells = (c.work ⟨0, by omega⟩).cells ∧
        c'.output = c.output := by
  intro p
  induction p with
  | zero =>
      intro c hstate hinp hcell0 hnostart hhead hout
      have hread : (c.work ⟨0, by omega⟩).read = Γ.start := by
        have hhead0 : (c.work (0 : Fin 1)).head = 0 := by
          simpa using hhead
        have hcell00 : (c.work (0 : Fin 1)).cells 0 = Γ.start := by
          simpa using hcell0
        simp [Tape.read, hhead0, hcell00]
      obtain ⟨c', hstep, hst, hinp', hhead', hcells', hout'⟩ :=
        satEval_rewindAlpha_base_step mode c hstate hinp hread hnostart hout
      exact ⟨c', .step hstep .zero, hst, hinp', hhead', hcells', hout'⟩
  | succ p ih =>
      intro c hstate hinp hcell0 hnostart hhead hout
      have hread : (c.work ⟨0, by omega⟩).read ≠ Γ.start := by
        have hhead0 : (c.work (0 : Fin 1)).head = p + 1 := by
          simpa using hhead
        have hnostart0 : ∀ j, j ≥ 1 → (c.work (0 : Fin 1)).cells j ≠ Γ.start := by
          intro j hj
          simpa using hnostart j hj
        simp [Tape.read, hhead0]
        exact hnostart0 (p + 1) (by omega)
      obtain ⟨c1, hstep, hst1, hinp1, hhead1, hcells1, hout1⟩ :=
        satEval_rewindAlpha_left_step mode c hstate hinp hread hout
      have hhead1' : (c1.work ⟨0, by omega⟩).head = p := by
        rw [hhead1, hhead]
        omega
      have hinp1_read : c1.input.read ≠ Γ.start := by
        rw [hinp1]
        exact hinp
      obtain ⟨c', hreach, hst, hinp', hhead', hcells', hout'⟩ :=
        ih c1 hst1 hinp1_read
          (by rw [hcells1]; exact hcell0)
          (by intro j hj; rw [hcells1]; exact hnostart j hj)
          hhead1'
          (by rw [hout1]; exact hout)
      refine ⟨c', .step hstep hreach, hst, ?_, hhead', ?_, ?_⟩
      · rw [hinp', hinp1]
      · rw [hcells', hcells1]
      · rw [hout', hout1]

private theorem satEval_two_bit_step (mode : SatEvalMode) (first second : Bool)
    (rest : List Bool) (c : Cfg 1 satEvalOnInputTM.Q)
    (hstate : c.state = .readFirst mode)
    (hinput : hasBoolSuffix c.input (first :: second :: rest))
    (hwork : (c.work ⟨0, by omega⟩).read ≠ Γ.start)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    let tr := satEvalTokenStep mode (tokenOfBits first second) (c.work ⟨0, by omega⟩).read
    ∃ c', satEvalOnInputTM.reachesIn 2 c c' ∧
      c'.state = tr.1 ∧
      hasBoolSuffix c'.input rest ∧
      c'.work ⟨0, by omega⟩ =
        (c.work ⟨0, by omega⟩).writeAndMove
          (TM.readBackWrite (c.work ⟨0, by omega⟩).read).toΓ tr.2.1 ∧
      c'.output = c.output.writeAndMove tr.2.2.toΓ (TM.idleDir c.output.read) := by
  have hread1 : c.input.read = Γ.ofBool first :=
    hasBoolSuffix_read_cons hinput
  obtain ⟨c1, hstep1, hst1, hinp1, hwork1, hout1⟩ :=
    satEval_readFirst_bit_step mode first c hstate hread1 hwork hout
  have hinput1 : hasBoolSuffix c1.input (second :: rest) := by
    rw [hinp1]
    exact hasBoolSuffix_move_right_cons hinput
  have hread2 : c1.input.read = Γ.ofBool second :=
    hasBoolSuffix_read_cons hinput1
  have hwork1_read : (c1.work ⟨0, by omega⟩).read ≠ Γ.start := by
    rw [hwork1]
    exact hwork
  have hout1_started : c1.output = (Tape.init []).move Dir3.right := by
    rw [hout1]
    exact hout
  obtain ⟨c2, hstep2, hst2, hinp2, hwork2, hout2⟩ :=
    satEval_readSecond_bit_step mode first second c1 hst1 hread2 hwork1_read hout1_started
  let tr := satEvalTokenStep mode (tokenOfBits first second) (c.work ⟨0, by omega⟩).read
  refine ⟨c2, .step hstep1 (.step hstep2 .zero), ?_, ?_, ?_, ?_⟩
  · simpa [tr, hwork1] using hst2
  · rw [hinp2]
    exact hasBoolSuffix_move_right_cons hinput1
  · simpa [tr, hwork1] using hwork2
  · simpa [tr, hout1, hwork1] using hout2

private theorem satEval_output_blank_id (w : Γw) :
    w = Γw.blank →
      ((Tape.init []).move Dir3.right).writeAndMove w.toΓ
          (TM.idleDir (((Tape.init []).move Dir3.right).read)) =
        (Tape.init []).move Dir3.right := by
  intro hw
  subst hw
  apply TM.tape_writeAndMove_stable
  · simp [Tape.move, Tape.init]
  · intro j hj
    simp [Tape.move, Tape.init, show j ≠ 0 by omega]

private theorem satEval_work_stay_id {t : Tape}
    (hread : t.read ≠ Γ.start) :
    t.writeAndMove (TM.readBackWrite t.read).toΓ Dir3.stay = t := by
  simpa [TM.transitionTape, TM.idleDir, hread] using
    (TM.transitionTape_eq_self hread)

private theorem satEval_work_cells_preserved_readBack {t : Tape} (d : Dir3)
    (hread : t.read ≠ Γ.start) :
    (t.writeAndMove (TM.readBackWrite t.read).toΓ d).cells = t.cells := by
  exact TM.tape_readBackWrite_preserves t d (Or.inr hread)

private theorem satEval_reject_output_zero (w : Γw) :
    w = Γw.zero →
      (((Tape.init []).move Dir3.right).writeAndMove w.toΓ
          (TM.idleDir (((Tape.init []).move Dir3.right).read))).cells 1 =
        Γ.zero := by
  intro hw
  subst hw
  have hidle :
      TM.idleDir (((Tape.init []).move Dir3.right).read) = Dir3.stay := by
    simp [Tape.read, Tape.move, TM.idleDir, Tape.init]
  rw [hidle]
  simp [Tape.writeAndMove, Tape.write, Tape.move, Tape.init]

-- ════════════════════════════════════════════════════════════════════════
-- Pure semantic target for the streaming evaluator
-- ════════════════════════════════════════════════════════════════════════

/-- Pure parser/evaluator state for the streaming CNF evaluator, abstracting
the machine mode `SatEvalMode`: either at a token `boundary` (tracking the
CNF-so-far, clause-so-far, and clause-emptiness Booleans) or `inLit` scanning
a raw literal with its sign and unary variable counter `var`. -/
inductive SatEvalSemState where
  /-- Between tokens: `cnf` is the conjunction of completed clauses, `clause`
  the disjunction so far, `empty` whether the clause has no literals. -/
  | boundary (cnf clause empty : Bool)
  /-- Inside a raw literal with sign bit `sign` and unary variable counter
  `var`. -/
  | inLit (cnf clause empty sign : Bool) (var : Nat)
  deriving DecidableEq, Repr

/-- End-of-input result: at a `boundary` the value is `cnf && empty` (the CNF
so far, provided the trailing clause is empty, i.e. the last token was `#`);
ending inside a literal is malformed and yields `false`. -/
def SatEvalSemState.finish : SatEvalSemState → Bool
  | .boundary cnf _ empty => cnf && empty
  | .inLit .. => false

private def SatEvalMode.toSemState : SatEvalMode → ℕ → SatEvalSemState
  | .boundary cnf clause empty, _ => .boundary cnf clause empty
  | .inLit cnf clause empty sign, var => .inLit cnf clause empty sign var

private def SatEvalMode.assignmentHead : SatEvalMode → ℕ → ℕ
  | .boundary .., _ => 1
  | .inLit .., var => var + 1

private def SatEvalMode.varBound : SatEvalMode → ℕ → ℕ → Prop
  | .boundary .., _, _ => True
  | .inLit .., var, k => var ≤ k

private theorem finishEvalMode_toΓ_eq_finish (mode : SatEvalMode) (var : ℕ) :
    (finishEvalMode mode).toΓ =
      (if (mode.toSemState var).finish then Γ.one else Γ.zero) := by
  cases mode with
  | boundary cnf clause empty =>
      cases cnf <;> cases empty <;>
        simp [finishEvalMode, SatEvalMode.toSemState, SatEvalSemState.finish, boolWrite]
  | inLit cnf clause empty sign =>
      simp [finishEvalMode, SatEvalMode.toSemState, SatEvalSemState.finish]

/-- One-token transition of the pure evaluator under assignment `α`:
`none` on malformed input (a separator with no literal, or a `false` bit
inside a literal body); otherwise the updated `SatEvalSemState`, folding a
completed literal's value into the clause accumulator at each `litSep`. -/
def satEvalSemStep (α : Assignment) : SatEvalSemState → EncToken → Option SatEvalSemState
  | .boundary cnf clause empty, .bit sign => some (.inLit cnf clause empty sign 0)
  | .boundary _ _ _, .litSep => none
  | .boundary cnf clause _, .clauseSep => some (.boundary (cnf && clause) false true)
  | .inLit cnf clause _ sign var, .bit b =>
      if b then some (.inLit cnf clause false sign (var + 1)) else none
  | .inLit cnf clause _ sign var, .litSep =>
      some (.boundary cnf (clause || (Assignment.get α var == sign)) false)
  | .inLit _ _ _ _ _, .clauseSep => none

/-- Run the pure evaluator over a token stream from a given state: fold
`satEvalSemStep` over the tokens, returning `false` on any malformed step and
`SatEvalSemState.finish` at the end of input. -/
def satEvalSemRun (α : Assignment) : List EncToken → SatEvalSemState → Bool
  | [], st => st.finish
  | tok :: toks, st =>
      match satEvalSemStep α st tok with
      | none => false
      | some st' => satEvalSemRun α toks st'

private theorem satEvalOnInputTM_token_loop_correct (α : Assignment) :
    ∀ (toks : List EncToken) (mode : SatEvalMode) (var : ℕ)
      (c : Cfg 1 satEvalOnInputTM.Q),
      c.state = .readFirst mode →
      hasBoolSuffix c.input (encodeTokens toks) →
      (c.work ⟨0, by omega⟩).cells =
        (Tape.init (α.map Γ.ofBool)).cells →
      (c.work ⟨0, by omega⟩).head = mode.assignmentHead var →
      c.output = (Tape.init []).move Dir3.right →
      ∃ c' t,
        t ≤ 4 * toks.length + var + 1 ∧
        satEvalOnInputTM.reachesIn t c c' ∧
        satEvalOnInputTM.halted c' ∧
        c'.output.cells 1 =
          (if satEvalSemRun α toks (mode.toSemState var) then Γ.one else Γ.zero) := by
  intro toks
  induction toks with
  | nil =>
      intro mode var c hstate hinput hcells hhead hout
      have hread : c.input.read = Γ.blank := hasBoolSuffix_read_nil hinput
      have hwork_read : (c.work ⟨0, by omega⟩).read ≠ Γ.start := by
        exact read_ne_start_of_cells_eq_initTape_ofBool α hcells (by
          rw [hhead]
          cases mode <;> simp [SatEvalMode.assignmentHead])
      obtain ⟨c', hstep, hhalt, _hinp, _hwork, hout'⟩ :=
        satEval_readFirst_blank_step mode c hstate hread hwork_read hout
      refine ⟨c', 1, by simp only [List.length_nil]; omega, .step hstep .zero, hhalt, ?_⟩
      rw [hout', finishEvalMode_toΓ_eq_finish mode var]
      simp [satEvalSemRun]
      rfl
  | cons tok toks ih =>
      intro mode var c hstate hinput hcells hhead hout
      have hwork_read : (c.work ⟨0, by omega⟩).read ≠ Γ.start := by
        exact read_ne_start_of_cells_eq_initTape_ofBool α hcells (by
          rw [hhead]
          cases mode <;> simp [SatEvalMode.assignmentHead])
      cases tok with
      | bit bit =>
          cases bit with
          | false =>
              have hinput_bits : hasBoolSuffix c.input (false :: false :: encodeTokens toks) := by
                simpa [encodeTokens_cons, EncToken.encode] using hinput
              obtain ⟨c2, hreach2, hstate2, hinput2, hwork2, hout2⟩ :=
                satEval_two_bit_step mode false false (encodeTokens toks) c
                  hstate hinput_bits hwork_read hout
              cases mode with
              | boundary cnf clause empty =>
                  have hwork2_eq : c2.work ⟨0, by omega⟩ = c.work ⟨0, by omega⟩ := by
                    rw [hwork2]
                    simpa [satEvalTokenStep, tokenOfBits] using
                      satEval_work_stay_id hwork_read
                  have hcells2 : (c2.work ⟨0, by omega⟩).cells =
                      (Tape.init (α.map Γ.ofBool)).cells := by
                    rw [hwork2_eq]
                    exact hcells
                  have hhead2 : (c2.work ⟨0, by omega⟩).head =
                      (SatEvalMode.inLit cnf clause empty false).assignmentHead 0 := by
                    rw [hwork2_eq, hhead]
                    simp [SatEvalMode.assignmentHead]
                  have hout2_started : c2.output = (Tape.init []).move Dir3.right := by
                    rw [hout2, hout]
                    exact satEval_output_blank_id _ (by rfl)
                  obtain ⟨c', t, htb, hreach, hhalt, hout'⟩ :=
                    ih (.inLit cnf clause empty false) 0 c2
                      hstate2 hinput2 hcells2 hhead2 hout2_started
                  refine ⟨c', 2 + t, by simp only [List.length_cons]; omega,
                    TM.reachesIn_trans _ hreach2 hreach, hhalt, ?_⟩
                  simp [satEvalSemRun, satEvalSemStep]
                  exact hout'
              | inLit cnf clause empty sign =>
                  refine ⟨c2, 2, by simp only [List.length_cons]; omega, hreach2, ?_, ?_⟩
                  · simp [satEvalOnInputTM]
                    exact hstate2
                  · rw [hout2, hout]
                    simp [satEvalSemRun, satEvalSemStep, tokenOfBits, satEvalTokenStep]
                    exact satEval_reject_output_zero _ (by rfl)
          | true =>
              have hinput_bits : hasBoolSuffix c.input (true :: true :: encodeTokens toks) := by
                simpa [encodeTokens_cons, EncToken.encode] using hinput
              obtain ⟨c2, hreach2, hstate2, hinput2, hwork2, hout2⟩ :=
                satEval_two_bit_step mode true true (encodeTokens toks) c
                  hstate hinput_bits hwork_read hout
              cases mode with
              | boundary cnf clause empty =>
                  have hwork2_eq : c2.work ⟨0, by omega⟩ = c.work ⟨0, by omega⟩ := by
                    rw [hwork2]
                    simpa [satEvalTokenStep, tokenOfBits] using
                      satEval_work_stay_id hwork_read
                  have hcells2 : (c2.work ⟨0, by omega⟩).cells =
                      (Tape.init (α.map Γ.ofBool)).cells := by
                    rw [hwork2_eq]
                    exact hcells
                  have hhead2 : (c2.work ⟨0, by omega⟩).head =
                      (SatEvalMode.inLit cnf clause empty true).assignmentHead 0 := by
                    rw [hwork2_eq, hhead]
                    simp [SatEvalMode.assignmentHead]
                  have hout2_started : c2.output = (Tape.init []).move Dir3.right := by
                    rw [hout2, hout]
                    exact satEval_output_blank_id _ (by rfl)
                  obtain ⟨c', t, htb, hreach, hhalt, hout'⟩ :=
                    ih (.inLit cnf clause empty true) 0 c2
                      hstate2 hinput2 hcells2 hhead2 hout2_started
                  refine ⟨c', 2 + t, by simp only [List.length_cons]; omega,
                    TM.reachesIn_trans _ hreach2 hreach, hhalt, ?_⟩
                  simp [satEvalSemRun, satEvalSemStep]
                  exact hout'
              | inLit cnf clause empty sign =>
                  have hcells2 : (c2.work ⟨0, by omega⟩).cells =
                      (Tape.init (α.map Γ.ofBool)).cells := by
                    rw [hwork2]
                    exact (satEval_work_cells_preserved_readBack Dir3.right hwork_read).trans hcells
                  have hhead2 : (c2.work ⟨0, by omega⟩).head =
                      (SatEvalMode.inLit cnf clause false sign).assignmentHead (var + 1) := by
                    rw [hwork2]
                    simp [satEvalTokenStep, tokenOfBits, Tape.writeAndMove, Tape.move,
                      Tape.write_head]
                    simpa [SatEvalMode.assignmentHead] using hhead
                  have hout2_started : c2.output = (Tape.init []).move Dir3.right := by
                    rw [hout2, hout]
                    exact satEval_output_blank_id _ (by rfl)
                  obtain ⟨c', t, htb, hreach, hhalt, hout'⟩ :=
                    ih (.inLit cnf clause false sign) (var + 1) c2
                      hstate2 hinput2 hcells2 hhead2 hout2_started
                  refine ⟨c', 2 + t, by simp only [List.length_cons]; omega,
                    TM.reachesIn_trans _ hreach2 hreach, hhalt, ?_⟩
                  simp [satEvalSemRun, satEvalSemStep]
                  exact hout'
      | litSep =>
          have hinput_bits : hasBoolSuffix c.input (false :: true :: encodeTokens toks) := by
            simpa [encodeTokens_cons, EncToken.encode] using hinput
          obtain ⟨c2, hreach2, hstate2, hinput2, hwork2, hout2⟩ :=
            satEval_two_bit_step mode false true (encodeTokens toks) c
              hstate hinput_bits hwork_read hout
          cases mode with
          | boundary cnf clause empty =>
              refine ⟨c2, 2, by simp only [List.length_cons]; omega, hreach2, ?_, ?_⟩
              · simp [satEvalOnInputTM]
                exact hstate2
              · rw [hout2, hout]
                simp [satEvalSemRun, satEvalSemStep, tokenOfBits, satEvalTokenStep]
                exact satEval_reject_output_zero _ (by rfl)
          | inLit cnf clause empty sign =>
              have hread_alpha :
                  (c.work ⟨0, by omega⟩).read =
                    (Tape.init (α.map Γ.ofBool)).cells (var + 1) := by
                show (c.work ⟨0, by omega⟩).cells (c.work ⟨0, by omega⟩).head =
                  (Tape.init (α.map Γ.ofBool)).cells (var + 1)
                rw [hhead, hcells]
                simp [SatEvalMode.assignmentHead]
              have hstate2' : c2.state =
                  .rewindAlpha (.boundary cnf
                    (clause || (Assignment.get α var == sign)) false) := by
                have hread_alpha0 :
                    (c.work (0 : Fin 1)).read =
                      (Tape.init (α.map Γ.ofBool)).cells (var + 1) := by
                  simpa using hread_alpha
                have hstate2a : c2.state =
                    .rewindAlpha (.boundary cnf
                      (clause ||
                        literalValueAtHead sign
                          ((Tape.init (α.map Γ.ofBool)).cells (var + 1))) false) := by
                  simpa [satEvalTokenStep, tokenOfBits, hread_alpha0] using hstate2
                simpa [literalValueAtHead_initTape_eq_litEval α sign var] using hstate2a
              have hcells2 : (c2.work ⟨0, by omega⟩).cells =
                  (Tape.init (α.map Γ.ofBool)).cells := by
                rw [hwork2]
                exact (satEval_work_cells_preserved_readBack Dir3.stay hwork_read).trans hcells
              have hhead2 : (c2.work ⟨0, by omega⟩).head = var + 1 := by
                rw [hwork2]
                simp [satEvalTokenStep, tokenOfBits, Tape.writeAndMove, Tape.move,
                  Tape.write_head]
                simpa [SatEvalMode.assignmentHead] using hhead
              have hout2_started : c2.output = (Tape.init []).move Dir3.right := by
                rw [hout2, hout]
                exact satEval_output_blank_id _ (by rfl)
              have hcell0 : (c2.work ⟨0, by omega⟩).cells 0 = Γ.start :=
                cells_eq_initTape_ofBool_cell0 α hcells2
              have hnostart : ∀ j, j ≥ 1 → (c2.work ⟨0, by omega⟩).cells j ≠ Γ.start :=
                cells_eq_initTape_ofBool_ne_start α hcells2
              obtain ⟨c3, hrewind, hstate3, hinp3, hhead3, hcells3, hout3⟩ :=
                satEval_rewindAlpha_loop (.boundary cnf
                  (clause || (Assignment.get α var == sign)) false)
                  (var + 1) c2 hstate2' (hasBoolSuffix_read_ne_start hinput2)
                  hcell0 hnostart hhead2 hout2_started
              have hcells3_init : (c3.work ⟨0, by omega⟩).cells =
                  (Tape.init (α.map Γ.ofBool)).cells := by
                rw [hcells3]
                exact hcells2
              have hhead3' : (c3.work ⟨0, by omega⟩).head =
                  (SatEvalMode.boundary cnf
                    (clause || (Assignment.get α var == sign)) false).assignmentHead 0 := by
                simpa [SatEvalMode.assignmentHead] using hhead3
              have hout3_started : c3.output = (Tape.init []).move Dir3.right := by
                rw [hout3]
                exact hout2_started
              obtain ⟨c', t, htb, hreach, hhalt, hout'⟩ :=
                ih (.boundary cnf (clause || (Assignment.get α var == sign)) false) 0 c3
                  hstate3 (by rw [hinp3]; exact hinput2)
                  hcells3_init hhead3' hout3_started
              refine ⟨c', 2 + (var + 1 + 1) + t, by simp only [List.length_cons]; omega,
                TM.reachesIn_trans _
                  (TM.reachesIn_trans _ hreach2 hrewind) hreach,
                hhalt, ?_⟩
              simp [satEvalSemRun, satEvalSemStep]
              exact hout'
      | clauseSep =>
          have hinput_bits : hasBoolSuffix c.input (true :: false :: encodeTokens toks) := by
            simpa [encodeTokens_cons, EncToken.encode] using hinput
          obtain ⟨c2, hreach2, hstate2, hinput2, hwork2, hout2⟩ :=
            satEval_two_bit_step mode true false (encodeTokens toks) c
              hstate hinput_bits hwork_read hout
          cases mode with
          | boundary cnf clause empty =>
              have hwork2_eq : c2.work ⟨0, by omega⟩ = c.work ⟨0, by omega⟩ := by
                rw [hwork2]
                simpa [satEvalTokenStep, tokenOfBits] using
                  satEval_work_stay_id hwork_read
              have hcells2 : (c2.work ⟨0, by omega⟩).cells =
                  (Tape.init (α.map Γ.ofBool)).cells := by
                rw [hwork2_eq]
                exact hcells
              have hhead2 : (c2.work ⟨0, by omega⟩).head =
                  (SatEvalMode.boundary (cnf && clause) false true).assignmentHead 0 := by
                rw [hwork2_eq, hhead]
                simp [SatEvalMode.assignmentHead]
              have hout2_started : c2.output = (Tape.init []).move Dir3.right := by
                rw [hout2, hout]
                exact satEval_output_blank_id _ (by rfl)
              obtain ⟨c', t, htb, hreach, hhalt, hout'⟩ :=
                ih (.boundary (cnf && clause) false true) 0 c2
                  hstate2 hinput2 hcells2 hhead2 hout2_started
              refine ⟨c', 2 + t, by simp only [List.length_cons]; omega,
                TM.reachesIn_trans _ hreach2 hreach, hhalt, ?_⟩
              simp [satEvalSemRun, satEvalSemStep]
              exact hout'
          | inLit cnf clause empty sign =>
              refine ⟨c2, 2, by simp only [List.length_cons]; omega, hreach2, ?_, ?_⟩
              · simp [satEvalOnInputTM]
                exact hstate2
              · rw [hout2, hout]
                simp [satEvalSemRun, satEvalSemStep, tokenOfBits, satEvalTokenStep]
                exact satEval_reject_output_zero _ (by rfl)

private theorem satEvalOnInputTM_tokenize_none_reject (α : Assignment) :
    ∀ (suffix : List Bool) (mode : SatEvalMode) (var : ℕ)
      (c : Cfg 1 satEvalOnInputTM.Q),
      tokenize? suffix = none →
      c.state = .readFirst mode →
      hasBoolSuffix c.input suffix →
      (c.work ⟨0, by omega⟩).cells =
        (Tape.init (α.map Γ.ofBool)).cells →
      (c.work ⟨0, by omega⟩).head = mode.assignmentHead var →
      c.output = (Tape.init []).move Dir3.right →
      ∃ c' t,
        t ≤ 2 * suffix.length + var + 1 ∧
        satEvalOnInputTM.reachesIn t c c' ∧
        satEvalOnInputTM.halted c' ∧
        c'.output.cells 1 = Γ.zero := by
  intro suffix
  induction hlen : suffix.length using Nat.strong_induction_on generalizing suffix with
  | h n ih =>
    intro mode var c htok hstate hinput hcells hhead hout
    cases suffix with
    | nil =>
      simp [tokenize?] at htok
    | cons first rest =>
      have hwork_read : (c.work ⟨0, by omega⟩).read ≠ Γ.start := by
        exact read_ne_start_of_cells_eq_initTape_ofBool α hcells (by
          rw [hhead]
          cases mode <;> simp [SatEvalMode.assignmentHead])
      cases rest with
      | nil =>
          have hinput_one : hasBoolSuffix c.input (first :: []) := by
            simpa using hinput
          have hread_first : c.input.read = Γ.ofBool first :=
            hasBoolSuffix_read_cons hinput_one
          obtain ⟨c1, hstep1, hstate1, hinp1, hwork1, hout1⟩ :=
            satEval_readFirst_bit_step mode first c hstate hread_first hwork_read hout
          have hinput1 : hasBoolSuffix c1.input [] := by
            rw [hinp1]
            exact hasBoolSuffix_move_right_cons hinput_one
          have hread_blank : c1.input.read = Γ.blank :=
            hasBoolSuffix_read_nil hinput1
          have hwork1_read : (c1.work ⟨0, by omega⟩).read ≠ Γ.start := by
            rw [hwork1]
            exact hwork_read
          have hout1_started : c1.output = (Tape.init []).move Dir3.right := by
            rw [hout1]
            exact hout
          obtain ⟨c2, hstep2, hhalt2, _hinp2, _hwork2, hout2⟩ :=
            satEval_readSecond_blank_step mode first c1 hstate1 hread_blank hwork1_read
              hout1_started
          exact ⟨c2, 2, by simp only [List.length_cons, List.length_nil] at hlen; omega,
            .step hstep1 (.step hstep2 .zero), hhalt2, hout2⟩
      | cons second tail =>
          have htail_tok : tokenize? tail = none := by
            cases first <;> cases second <;> simpa [tokenize?] using htok
          have htail_len : tail.length < n := by
            simp at hlen
            omega
          have hinput_bits : hasBoolSuffix c.input (first :: second :: tail) := by
            simpa using hinput
          obtain ⟨c2, hreach2, hstate2, hinput2, hwork2, hout2⟩ :=
            satEval_two_bit_step mode first second tail c
              hstate hinput_bits hwork_read hout
          cases first <;> cases second
          · -- false false: raw bit `false`
            cases mode with
            | boundary cnf clause empty =>
                have hwork2_eq : c2.work ⟨0, by omega⟩ = c.work ⟨0, by omega⟩ := by
                  rw [hwork2]
                  simpa [satEvalTokenStep, tokenOfBits] using
                    satEval_work_stay_id hwork_read
                have hcells2 : (c2.work ⟨0, by omega⟩).cells =
                    (Tape.init (α.map Γ.ofBool)).cells := by
                  rw [hwork2_eq]
                  exact hcells
                have hhead2 : (c2.work ⟨0, by omega⟩).head =
                    (SatEvalMode.inLit cnf clause empty false).assignmentHead 0 := by
                  rw [hwork2_eq, hhead]
                  simp [SatEvalMode.assignmentHead]
                have hout2_started : c2.output = (Tape.init []).move Dir3.right := by
                  rw [hout2, hout]
                  exact satEval_output_blank_id _ (by rfl)
                obtain ⟨c', t, htb, hreach, hhalt, hout'⟩ :=
                  ih tail.length htail_len tail rfl (.inLit cnf clause empty false) 0 c2 htail_tok
                    hstate2 hinput2 hcells2 hhead2 hout2_started
                exact ⟨c', 2 + t, by simp only [List.length_cons] at hlen; omega,
                  TM.reachesIn_trans _ hreach2 hreach, hhalt, hout'⟩
            | inLit cnf clause empty sign =>
                refine ⟨c2, 2, by simp only [List.length_cons] at hlen; omega, hreach2, ?_, ?_⟩
                · simp [satEvalOnInputTM]
                  exact hstate2
                · rw [hout2, hout]
                  simpa [tokenOfBits, satEvalTokenStep] using
                    satEval_reject_output_zero _ (by rfl)
          · -- false true: literal separator
            cases mode with
            | boundary cnf clause empty =>
                refine ⟨c2, 2, by simp only [List.length_cons] at hlen; omega, hreach2, ?_, ?_⟩
                · simp [satEvalOnInputTM]
                  exact hstate2
                · rw [hout2, hout]
                  simpa [tokenOfBits, satEvalTokenStep] using
                    satEval_reject_output_zero _ (by rfl)
            | inLit cnf clause empty sign =>
                have hread_alpha :
                    (c.work ⟨0, by omega⟩).read =
                      (Tape.init (α.map Γ.ofBool)).cells (var + 1) := by
                  show (c.work ⟨0, by omega⟩).cells (c.work ⟨0, by omega⟩).head =
                    (Tape.init (α.map Γ.ofBool)).cells (var + 1)
                  rw [hhead, hcells]
                  simp [SatEvalMode.assignmentHead]
                have hstate2' : c2.state =
                    .rewindAlpha (.boundary cnf
                      (clause || (Assignment.get α var == sign)) false) := by
                  have hread_alpha0 :
                      (c.work (0 : Fin 1)).read =
                        (Tape.init (α.map Γ.ofBool)).cells (var + 1) := by
                    simpa using hread_alpha
                  have hstate2a : c2.state =
                      .rewindAlpha (.boundary cnf
                        (clause ||
                          literalValueAtHead sign
                            ((Tape.init (α.map Γ.ofBool)).cells (var + 1))) false) := by
                    simpa [satEvalTokenStep, tokenOfBits, hread_alpha0] using hstate2
                  simpa [literalValueAtHead_initTape_eq_litEval α sign var] using hstate2a
                have hcells2 : (c2.work ⟨0, by omega⟩).cells =
                    (Tape.init (α.map Γ.ofBool)).cells := by
                  rw [hwork2]
                  exact (satEval_work_cells_preserved_readBack Dir3.stay hwork_read).trans hcells
                have hhead2 : (c2.work ⟨0, by omega⟩).head = var + 1 := by
                  rw [hwork2]
                  simp [satEvalTokenStep, tokenOfBits, Tape.writeAndMove, Tape.move,
                    Tape.write_head]
                  simpa [SatEvalMode.assignmentHead] using hhead
                have hout2_started : c2.output = (Tape.init []).move Dir3.right := by
                  rw [hout2, hout]
                  exact satEval_output_blank_id _ (by rfl)
                have hcell0 : (c2.work ⟨0, by omega⟩).cells 0 = Γ.start :=
                  cells_eq_initTape_ofBool_cell0 α hcells2
                have hnostart : ∀ j, j ≥ 1 → (c2.work ⟨0, by omega⟩).cells j ≠ Γ.start :=
                  cells_eq_initTape_ofBool_ne_start α hcells2
                obtain ⟨c3, hrewind, hstate3, hinp3, hhead3, hcells3, hout3⟩ :=
                  satEval_rewindAlpha_loop (.boundary cnf
                    (clause || (Assignment.get α var == sign)) false)
                    (var + 1) c2 hstate2' (hasBoolSuffix_read_ne_start hinput2)
                    hcell0 hnostart hhead2 hout2_started
                have hcells3_init : (c3.work ⟨0, by omega⟩).cells =
                    (Tape.init (α.map Γ.ofBool)).cells := by
                  rw [hcells3]
                  exact hcells2
                have hhead3' : (c3.work ⟨0, by omega⟩).head =
                    (SatEvalMode.boundary cnf
                      (clause || (Assignment.get α var == sign)) false).assignmentHead 0 := by
                  simpa [SatEvalMode.assignmentHead] using hhead3
                have hout3_started : c3.output = (Tape.init []).move Dir3.right := by
                  rw [hout3]
                  exact hout2_started
                obtain ⟨c', t, htb, hreach, hhalt, hout'⟩ :=
                  ih tail.length htail_len tail rfl
                    (.boundary cnf (clause || (Assignment.get α var == sign)) false) 0 c3
                    htail_tok hstate3 (by rw [hinp3]; exact hinput2)
                    hcells3_init hhead3' hout3_started
                exact ⟨c', 2 + (var + 1 + 1) + t, by simp only [List.length_cons] at hlen; omega,
                  TM.reachesIn_trans _
                    (TM.reachesIn_trans _ hreach2 hrewind) hreach,
                  hhalt, hout'⟩
          · -- true false: clause separator
            cases mode with
            | boundary cnf clause empty =>
                have hwork2_eq : c2.work ⟨0, by omega⟩ = c.work ⟨0, by omega⟩ := by
                  rw [hwork2]
                  simpa [satEvalTokenStep, tokenOfBits] using
                    satEval_work_stay_id hwork_read
                have hcells2 : (c2.work ⟨0, by omega⟩).cells =
                    (Tape.init (α.map Γ.ofBool)).cells := by
                  rw [hwork2_eq]
                  exact hcells
                have hhead2 : (c2.work ⟨0, by omega⟩).head =
                    (SatEvalMode.boundary (cnf && clause) false true).assignmentHead 0 := by
                  rw [hwork2_eq, hhead]
                  simp [SatEvalMode.assignmentHead]
                have hout2_started : c2.output = (Tape.init []).move Dir3.right := by
                  rw [hout2, hout]
                  exact satEval_output_blank_id _ (by rfl)
                obtain ⟨c', t, htb, hreach, hhalt, hout'⟩ :=
                  ih tail.length htail_len tail rfl (.boundary (cnf && clause) false true)
                    0 c2 htail_tok
                    hstate2 hinput2 hcells2 hhead2 hout2_started
                exact ⟨c', 2 + t, by simp only [List.length_cons] at hlen; omega,
                  TM.reachesIn_trans _ hreach2 hreach, hhalt, hout'⟩
            | inLit cnf clause empty sign =>
                refine ⟨c2, 2, by simp only [List.length_cons] at hlen; omega, hreach2, ?_, ?_⟩
                · simp [satEvalOnInputTM]
                  exact hstate2
                · rw [hout2, hout]
                  simpa [tokenOfBits, satEvalTokenStep] using
                    satEval_reject_output_zero _ (by rfl)
          · -- true true: raw bit `true`
            cases mode with
            | boundary cnf clause empty =>
                have hwork2_eq : c2.work ⟨0, by omega⟩ = c.work ⟨0, by omega⟩ := by
                  rw [hwork2]
                  simpa [satEvalTokenStep, tokenOfBits] using
                    satEval_work_stay_id hwork_read
                have hcells2 : (c2.work ⟨0, by omega⟩).cells =
                    (Tape.init (α.map Γ.ofBool)).cells := by
                  rw [hwork2_eq]
                  exact hcells
                have hhead2 : (c2.work ⟨0, by omega⟩).head =
                    (SatEvalMode.inLit cnf clause empty true).assignmentHead 0 := by
                  rw [hwork2_eq, hhead]
                  simp [SatEvalMode.assignmentHead]
                have hout2_started : c2.output = (Tape.init []).move Dir3.right := by
                  rw [hout2, hout]
                  exact satEval_output_blank_id _ (by rfl)
                obtain ⟨c', t, htb, hreach, hhalt, hout'⟩ :=
                  ih tail.length htail_len tail rfl (.inLit cnf clause empty true) 0 c2 htail_tok
                    hstate2 hinput2 hcells2 hhead2 hout2_started
                exact ⟨c', 2 + t, by simp only [List.length_cons] at hlen; omega,
                  TM.reachesIn_trans _ hreach2 hreach, hhalt, hout'⟩
            | inLit cnf clause empty sign =>
                have hcells2 : (c2.work ⟨0, by omega⟩).cells =
                    (Tape.init (α.map Γ.ofBool)).cells := by
                  rw [hwork2]
                  exact (satEval_work_cells_preserved_readBack Dir3.right hwork_read).trans hcells
                have hhead2 : (c2.work ⟨0, by omega⟩).head =
                    (SatEvalMode.inLit cnf clause false sign).assignmentHead (var + 1) := by
                  rw [hwork2]
                  simp [satEvalTokenStep, tokenOfBits, Tape.writeAndMove, Tape.move,
                    Tape.write_head]
                  simpa [SatEvalMode.assignmentHead] using hhead
                have hout2_started : c2.output = (Tape.init []).move Dir3.right := by
                  rw [hout2, hout]
                  exact satEval_output_blank_id _ (by rfl)
                obtain ⟨c', t, htb, hreach, hhalt, hout'⟩ :=
                  ih tail.length htail_len tail rfl (.inLit cnf clause false sign) (var + 1)
                    c2 htail_tok
                    hstate2 hinput2 hcells2 hhead2 hout2_started
                exact ⟨c', 2 + t, by simp only [List.length_cons] at hlen; omega,
                  TM.reachesIn_trans _ hreach2 hreach, hhalt, hout'⟩

/-- Bit-level pure evaluator: tokenize `z` (rejecting odd-length inputs) and
run `satEvalSemRun` from the initial state `.boundary true false true`.
Equals `CNF.eval α` on the decoded CNF by `satEvalSemBits_eq_decode_eval`. -/
def satEvalSemBits (α z : List Bool) : Bool :=
  match tokenize? z with
  | none => false
  | some toks => satEvalSemRun α toks (.boundary true false true)

private theorem encodeTokens_length (toks : List EncToken) :
    (encodeTokens toks).length = 2 * toks.length := by
  induction toks with
  | nil => rfl
  | cons t ts ih =>
      have htlen : t.encode.length = 2 := by
        cases t with
        | bit b => cases b <;> rfl
        | litSep => rfl
        | clauseSep => rfl
      simp only [encodeTokens_cons, List.length_append, htlen, ih, List.length_cons]
      omega

private theorem satEvalOnInputTM_started_correct (α z : List Bool)
    (c : Cfg 1 satEvalOnInputTM.Q)
    (hstate : c.state = .readFirst (.boundary true false true))
    (hinput : c.input = (Tape.init (z.map Γ.ofBool)).move Dir3.right)
    (hwork : c.work ⟨0, by omega⟩ = (Tape.init (α.map Γ.ofBool)).move Dir3.right)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c' t,
      t ≤ 2 * z.length + 1 ∧
      satEvalOnInputTM.reachesIn t c c' ∧
      satEvalOnInputTM.halted c' ∧
      c'.output.cells 1 = (if satEvalSemBits α z then Γ.one else Γ.zero) := by
  have hcells : (c.work ⟨0, by omega⟩).cells =
      (Tape.init (α.map Γ.ofBool)).cells := by
    rw [hwork]
    exact Tape.move_cells _ _
  have hhead : (c.work ⟨0, by omega⟩).head =
      (SatEvalMode.boundary true false true).assignmentHead 0 := by
    rw [hwork]
    simp [Tape.move, Tape.init, SatEvalMode.assignmentHead]
  cases htok : tokenize? z with
  | none =>
      have hsuffix : hasBoolSuffix c.input z := by
        rw [hinput]
        exact initTape_move_right_hasBoolSuffix z
      obtain ⟨c', t, htb, hreach, hhalt, hout'⟩ :=
        satEvalOnInputTM_tokenize_none_reject α z (.boundary true false true) 0 c
          htok hstate hsuffix hcells hhead hout
      refine ⟨c', t, by omega, hreach, hhalt, ?_⟩
      simpa [satEvalSemBits, htok] using hout'
  | some toks =>
      have hz : z = encodeTokens toks := tokenize?_sound htok
      have hsuffix : hasBoolSuffix c.input (encodeTokens toks) := by
        rw [hinput, hz]
        exact initTape_move_right_hasBoolSuffix (encodeTokens toks)
      obtain ⟨c', t, htb, hreach, hhalt, hout'⟩ :=
        satEvalOnInputTM_token_loop_correct α toks (.boundary true false true) 0 c
          hstate hsuffix hcells hhead hout
      refine ⟨c', t, ?_, hreach, hhalt, ?_⟩
      · have hzlen : z.length = 2 * toks.length := by rw [hz, encodeTokens_length]
        rw [hzlen]; omega
      · simp [satEvalSemBits, htok]
        exact hout'

/-- Coarse polynomial budget for the split-input evaluator. Rewinding the
assignment after each completed literal gives a quadratic upper bound once
`α.length ≤ z.length + 1`; this standalone bound keeps both lengths explicit. -/
def satEvalOnInputTime (zLen αLen : ℕ) : ℕ :=
  (zLen + 1) * (αLen + 3) + 2

private def satEvalSemFrom (α suffix : List Bool) (mode : SatEvalMode) (var : ℕ) : Bool :=
  match tokenize? suffix with
  | none => false
  | some toks => satEvalSemRun α toks (mode.toSemState var)

private def parseEvalResult (α : Assignment) (toks : List EncToken)
    (rawRev : List Bool) (clauseRev : Clause) (cnfRev : CNF) : Bool :=
  match parseTokensAux toks rawRev clauseRev cnfRev with
  | none => false
  | some φ => CNF.eval α φ

private def RawInvalid (rawRev : List Bool) : Prop :=
  ∃ sign rest, rawRev.reverse = sign :: rest ∧ false ∈ rest

private lemma RawInvalid.cons (b : Bool) {rawRev : List Bool} (h : RawInvalid rawRev) :
    RawInvalid (b :: rawRev) := by
  rcases h with ⟨sign, rest, hrev, hmem⟩
  refine ⟨sign, rest ++ [b], ?_, ?_⟩ <;> simp [hrev, hmem]

private lemma RawInvalid.ne_nil {rawRev : List Bool} (h : RawInvalid rawRev) : rawRev ≠ [] := by
  rintro rfl
  rcases h with ⟨_sign, _rest, hrev, _⟩
  simp at hrev

private lemma RawInvalid.decodeRaw?_eq_none {rawRev : List Bool} (h : RawInvalid rawRev) :
    Lit.decodeRaw? rawRev.reverse = none := by
  rcases h with ⟨sign, rest, hrev, hmem⟩
  rw [hrev]
  simp only [Lit.decodeRaw?]
  split
  · have hfalse : false = true := ‹∀ b ∈ rest, b = true› false hmem
    cases hfalse
  · rfl

private lemma parseEvalResult_invalid_raw (α : Assignment) (toks : List EncToken)
    {rawRev : List Bool} (hbad : RawInvalid rawRev)
    (clauseRev : Clause) (cnfRev : CNF) :
    parseEvalResult α toks rawRev clauseRev cnfRev = false := by
  induction toks generalizing rawRev clauseRev cnfRev with
  | nil =>
      simp [parseEvalResult, parseTokensAux, RawInvalid.ne_nil hbad]
  | cons tok toks ih =>
      cases tok <;> simp [parseEvalResult, parseTokensAux]
      · exact ih (RawInvalid.cons _ hbad) clauseRev cnfRev
      · simp [RawInvalid.decodeRaw?_eq_none hbad]
      · simp [RawInvalid.ne_nil hbad]



/-- A singleton clause evaluates to the value of its unique literal. -/
@[simp] theorem Clause.eval_singleton (α : Assignment) (ℓ : Lit) :
    Clause.eval α [ℓ] = Lit.eval α ℓ := by
  simp [Clause.eval]

private def SatEvalSemRel (α : Assignment) :
    SatEvalSemState → List Bool → Clause → CNF → Prop
  | .boundary cnf clause empty, rawRev, clauseRev, cnfRev =>
      rawRev = [] ∧ cnf = CNF.eval α cnfRev.reverse ∧
      clause = Clause.eval α clauseRev.reverse ∧ empty = decide (clauseRev = [])
  | .inLit cnf clause _ sign var, rawRev, clauseRev, cnfRev =>
      rawRev = List.replicate var true ++ [sign] ∧
      cnf = CNF.eval α cnfRev.reverse ∧ clause = Clause.eval α clauseRev.reverse

private lemma rawInvalid_false_cons_valid (sign : Bool) (var : Nat) :
    RawInvalid (false :: (List.replicate var true ++ [sign])) := by
  refine ⟨sign, List.replicate var true ++ [false], ?_, ?_⟩
  · simp [List.reverse_append]
  · simp

private lemma lit_decode_replicate (sign : Bool) (var : Nat) :
    Lit.decodeRaw? (sign :: List.replicate var true) = some { sign := sign, var := var } := by
  simp [Lit.decodeRaw?]

private lemma satEvalSemRun_correct (α : Assignment) (toks : List EncToken) :
    ∀ (st : SatEvalSemState) (rawRev : List Bool) (clauseRev : Clause) (cnfRev : CNF),
      SatEvalSemRel α st rawRev clauseRev cnfRev →
      satEvalSemRun α toks st = parseEvalResult α toks rawRev clauseRev cnfRev := by
  induction toks with
  | nil =>
      intro st rawRev clauseRev cnfRev hrel
      cases st with
      | boundary cnf clause empty =>
          rcases hrel with ⟨hraw, hcnf, hclause, hempty⟩
          subst hraw; subst hcnf; subst hclause; subst hempty
          by_cases hcl : clauseRev = []
          · subst hcl
            simp [satEvalSemRun, SatEvalSemState.finish, parseEvalResult, parseTokensAux]
          · simp [satEvalSemRun, SatEvalSemState.finish, parseEvalResult, parseTokensAux, hcl]
      | inLit _ _ _ _ _ =>
          rcases hrel with ⟨hraw, _, _⟩
          subst hraw
          simp [satEvalSemRun, SatEvalSemState.finish, parseEvalResult, parseTokensAux]
  | cons tok toks ih =>
      intro st rawRev clauseRev cnfRev hrel
      cases st with
      | boundary cnf clause empty =>
          rcases hrel with ⟨hraw, hcnf, hclause, hempty⟩
          subst hraw; subst hcnf; subst hclause; subst hempty
          cases tok with
          | bit b =>
              simp [satEvalSemRun, satEvalSemStep, parseEvalResult, parseTokensAux]
              exact ih (.inLit (CNF.eval α cnfRev.reverse) (Clause.eval α clauseRev.reverse)
                (decide (clauseRev = [])) b 0) [b] clauseRev cnfRev
                ⟨by simp, rfl, rfl⟩
          | litSep =>
              simp [satEvalSemRun, satEvalSemStep, parseEvalResult, parseTokensAux, Lit.decodeRaw?]
          | clauseSep =>
              simp [satEvalSemRun, satEvalSemStep, parseEvalResult, parseTokensAux]
              have h := ih
                (.boundary (CNF.eval α cnfRev.reverse && Clause.eval α clauseRev.reverse)
                  false true)
                [] [] (clauseRev.reverse :: cnfRev)
                ⟨rfl, ?_, ?_, ?_⟩
              · exact h
              · simp [CNF.eval, List.reverse_cons]
              · simp [Clause.eval]
              · simp
      | inLit _ _ _ sign var =>
          rcases hrel with ⟨hraw, hcnf, hclause⟩
          subst hraw; subst hcnf; subst hclause
          cases tok with
          | bit b =>
              cases b
              · simp [satEvalSemRun, satEvalSemStep, parseEvalResult, parseTokensAux]
                exact parseEvalResult_invalid_raw α toks
                  (rawInvalid_false_cons_valid sign var) clauseRev cnfRev
              · simp [satEvalSemRun, satEvalSemStep, parseEvalResult, parseTokensAux]
                exact ih
                  (.inLit (CNF.eval α cnfRev.reverse) (Clause.eval α clauseRev.reverse)
                    false sign (var + 1))
                  (true :: (List.replicate var true ++ [sign])) clauseRev cnfRev
                  ⟨by simp [List.replicate_succ, List.cons_append], rfl, rfl⟩
          | litSep =>
              simp [satEvalSemRun, satEvalSemStep, parseEvalResult, parseTokensAux]
              have hdecode : Lit.decodeRaw? (sign :: List.replicate var true) =
                  some { sign := sign, var := var } := lit_decode_replicate sign var
              simp [hdecode]
              have h := ih
                (.boundary (CNF.eval α cnfRev.reverse)
                  (Clause.eval α clauseRev.reverse || (Assignment.get α var == sign)) false)
                [] ({ sign := sign, var := var } :: clauseRev) cnfRev
                ⟨rfl, rfl, ?_, ?_⟩
              · exact h
              · simp [Clause.eval, Lit.eval]
              · simp
          | clauseSep =>
              simp [satEvalSemRun, satEvalSemStep, parseEvalResult, parseTokensAux]

/-- Correctness of the pure evaluator: `satEvalSemBits α z` is `false` when
`z` fails to decode as a CNF, and otherwise is `CNF.eval α` of the decoded
formula. -/
theorem satEvalSemBits_eq_decode_eval (α z : List Bool) :
    satEvalSemBits α z =
      match CNF.decode? z with
      | none => false
      | some φ => CNF.eval α φ := by
  unfold satEvalSemBits CNF.decode?
  cases htok : tokenize? z with
  | none =>
      simp
  | some toks =>
      simp
      have h := satEvalSemRun_correct α toks (.boundary true false true) [] [] []
        ⟨rfl, by simp [CNF.eval], by simp [Clause.eval], by simp⟩
      exact h

/-- Pure semantic model of the paired SAT verifier: unpair `w` into `(z, α)`,
check the witness-length bound `|α| ≤ |z| + 1`, and evaluate the encoded CNF
`z` under `α` via `satEvalSemBits`; `false` on malformed pairs. -/
def verifyPairSem (w : List Bool) : Bool :=
  match unpair? w with
  | none => false
  | some (z, α) => decide (α.length ≤ z.length + 1) && satEvalSemBits α z

/-- The pure semantic model agrees with the reference Boolean verifier
`SAT.verifyPair` on every input. -/
theorem verifyPairSem_eq_verifyPair (w : List Bool) :
    verifyPairSem w = verifyPair w := by
  unfold verifyPairSem verifyPair
  cases hunpair : unpair? w with
  | none =>
      simp
  | some za =>
      rcases za with ⟨z, α⟩
      simp
      rw [satEvalSemBits_eq_decode_eval]
      cases CNF.decode? z <;> simp

/-- `verifyPairSem` accepts exactly the members of the paired witness
language `pairLang Witness`. -/
theorem verifyPairSem_eq_true_iff_mem_pairLang (w : List Bool) :
    verifyPairSem w = true ↔ w ∈ pairLang Witness := by
  rw [verifyPairSem_eq_verifyPair, verifyPair_eq_true_iff_mem_pairLang]

/-- Set-level restatement: `pairLang Witness` is the language accepted by the
pure semantic verifier `verifyPairSem`. -/
theorem pairLang_witness_eq_verifyPairSemLang :
    pairLang Witness = {w | verifyPairSem w = true} := by
  ext w
  exact (verifyPairSem_eq_true_iff_mem_pairLang w).symm

-- ════════════════════════════════════════════════════════════════════════
-- Full paired SAT verifier machine
-- ════════════════════════════════════════════════════════════════════════

/-- Control states for the deterministic paired SAT verifier.

Work-tape layout:

* tape `0`: decoded formula encoding `z`,
* tape `1`: decoded assignment `α`,
* tape `2`: a unary counter initially holding `|z| + 1`, consumed while
  copying `α`.

The machine first validates and splits the outer `pair z α` encoding, checks
the SAT witness length bound during the split, rewinds the staged `z` and `α`
tapes, and then runs the same streaming CNF evaluator as `satEvalOnInputTM`
against the staged work tapes. -/
inductive VerifyPairPhase where
  /-- Initial state: step off the left markers. -/
  | init
  /-- Write the extra leading counter tally before the split scan. -/
  | initCounter
  /-- Split scan: expecting the first bit of a doubled input bit or of the
  separator `01`. -/
  | splitScan
  /-- Split scan after a first `false`: a `false` completes a doubled bit,
  a `true` completes the separator. -/
  | splitAfterFalse
  /-- Split scan after a first `true`: only a second `true` is valid. -/
  | splitAfterTrue
  /-- Rewind the counter tape before copying the assignment. -/
  | rewindCounterForAlpha
  /-- Copy the assignment suffix to work tape `1`, consuming counter tallies
  to enforce the witness-length bound. -/
  | copyAlpha
  /-- Rewind the staged formula tape to its left marker. -/
  | rewindFormula
  /-- Rewind the staged assignment tape to its left marker. -/
  | rewindAssignment
  /-- Evaluator phase mirroring `SatEvalPhase.readFirst`. -/
  | evalReadFirst (mode : SatEvalMode)
  /-- Evaluator phase mirroring `SatEvalPhase.readSecond`. -/
  | evalReadSecond (mode : SatEvalMode) (first : Bool)
  /-- Evaluator phase mirroring `SatEvalPhase.rewindAlpha`. -/
  | evalRewindAlpha (mode : SatEvalMode)
  /-- Halt state: the verdict has been written to the output tape. -/
  | done
  deriving DecidableEq, Repr

instance : Fintype VerifyPairPhase where
  elems :=
    insert VerifyPairPhase.init <|
    insert VerifyPairPhase.initCounter <|
    insert VerifyPairPhase.splitScan <|
    insert VerifyPairPhase.splitAfterFalse <|
    insert VerifyPairPhase.splitAfterTrue <|
    insert VerifyPairPhase.rewindCounterForAlpha <|
    insert VerifyPairPhase.copyAlpha <|
    insert VerifyPairPhase.rewindFormula <|
    insert VerifyPairPhase.rewindAssignment <|
    insert VerifyPairPhase.done <|
      (Finset.univ.image VerifyPairPhase.evalReadFirst) ∪
      (Finset.univ.image fun p : SatEvalMode × Bool =>
        VerifyPairPhase.evalReadSecond p.1 p.2) ∪
      (Finset.univ.image VerifyPairPhase.evalRewindAlpha)
  complete := by
    intro q
    cases q <;> simp

/-- Rejecting transition for the paired-formula verifier. -/
def verifyPairReject (iHead : Γ) (wHeads : Fin 3 → Γ) (oHead : Γ) :
    VerifyPairPhase × (Fin 3 → Γw) × Γw × Dir3 × (Fin 3 → Dir3) × Dir3 :=
  (.done, fun i => TM.readBackWrite (wHeads i), Γw.zero,
    TM.idleDir iHead, fun i => TM.idleDir (wHeads i),
    TM.idleDir oHead)

/-- Rewrites every paired-verifier work symbol without changing its value. -/
def verifyPairPreserveWork (wHeads : Fin 3 → Γ) : Fin 3 → Γw :=
  fun i => TM.readBackWrite (wHeads i)

/-- Work-tape writes while splitting the formula and assignment encodings. -/
def verifyPairSplitWrite (zBit : Bool) (wHeads : Fin 3 → Γ) : Fin 3 → Γw :=
  fun i =>
    if i = ⟨0, by omega⟩ then boolWrite zBit
    else if i = ⟨2, by omega⟩ then Γw.one
    else TM.readBackWrite (wHeads i)

/-- Work-tape head directions while splitting the paired encoding. -/
def verifyPairSplitDirs (wHeads : Fin 3 → Γ) : Fin 3 → Dir3 :=
  fun i =>
    if i = ⟨0, by omega⟩ then Dir3.right
    else if i = ⟨2, by omega⟩ then Dir3.right
    else TM.idleDir (wHeads i)

/-- Work-tape writes while copying the assignment component. -/
def verifyPairCopyAlphaWrite (aBit : Bool) (wHeads : Fin 3 → Γ) :
    Fin 3 → Γw :=
  fun i =>
    if i = ⟨1, by omega⟩ then boolWrite aBit
    else if i = ⟨2, by omega⟩ then Γw.blank
    else TM.readBackWrite (wHeads i)

/-- Work-tape head directions while copying the assignment component. -/
def verifyPairCopyAlphaDirs (wHeads : Fin 3 → Γ) : Fin 3 → Dir3 :=
  fun i =>
    if i = ⟨1, by omega⟩ then Dir3.right
    else if i = ⟨2, by omega⟩ then Dir3.right
    else TM.idleDir (wHeads i)

/-- Work-tape directions induced by one evaluator step. -/
def verifyPairEvalDirs (αHead : Γ) (αDir : Dir3) (wHeads : Fin 3 → Γ) :
    Fin 3 → Dir3 :=
  fun i =>
    if i = ⟨0, by omega⟩ then Dir3.right
    else if i = ⟨1, by omega⟩ then
      if αHead = Γ.start then Dir3.right else αDir
    else
      TM.idleDir (wHeads i)

/-- Transition function for verifying a paired formula-and-assignment encoding. -/
def verifyPairDelta :
    VerifyPairPhase → Γ → (Fin 3 → Γ) → Γ →
      VerifyPairPhase × (Fin 3 → Γw) × Γw × Dir3 × (Fin 3 → Dir3) × Dir3 :=
  fun state iHead wHeads oHead =>
    let zHead := wHeads ⟨0, by omega⟩
    let αHead := wHeads ⟨1, by omega⟩
    let counterHead := wHeads ⟨2, by omega⟩
    match state with
    | .init =>
        (.initCounter,
          verifyPairPreserveWork wHeads,
          TM.readBackWrite oHead,
          Dir3.right,
          fun _ => Dir3.right,
          Dir3.right)
    | .initCounter =>
        (.splitScan,
          fun i =>
            if i = ⟨2, by omega⟩ then Γw.one
            else TM.readBackWrite (wHeads i),
          TM.readBackWrite oHead,
          TM.idleDir iHead,
          fun i => if i = ⟨2, by omega⟩ then Dir3.right else TM.idleDir (wHeads i),
          TM.idleDir oHead)
    | .splitScan =>
        match readBit? iHead with
        | some false =>
            (.splitAfterFalse, verifyPairPreserveWork wHeads, TM.readBackWrite oHead,
              Dir3.right, fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
        | some true =>
            (.splitAfterTrue, verifyPairPreserveWork wHeads, TM.readBackWrite oHead,
              Dir3.right, fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
        | none =>
            verifyPairReject iHead wHeads oHead
    | .splitAfterFalse =>
        match readBit? iHead with
        | some false =>
            (.splitScan,
              verifyPairSplitWrite false wHeads,
              TM.readBackWrite oHead,
              Dir3.right,
              verifyPairSplitDirs wHeads,
              TM.idleDir oHead)
        | some true =>
            (.rewindCounterForAlpha,
              verifyPairPreserveWork wHeads,
              TM.readBackWrite oHead,
              Dir3.right,
              fun i => TM.idleDir (wHeads i),
              TM.idleDir oHead)
        | none =>
            verifyPairReject iHead wHeads oHead
    | .splitAfterTrue =>
        match readBit? iHead with
        | some true =>
            (.splitScan,
              verifyPairSplitWrite true wHeads,
              TM.readBackWrite oHead,
              Dir3.right,
              verifyPairSplitDirs wHeads,
              TM.idleDir oHead)
        | _ =>
            verifyPairReject iHead wHeads oHead
    | .rewindCounterForAlpha =>
        if counterHead = Γ.start then
          (.copyAlpha,
            verifyPairPreserveWork wHeads,
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨2, by omega⟩ then Dir3.right else TM.idleDir (wHeads i),
            TM.idleDir oHead)
        else
          (.rewindCounterForAlpha,
            verifyPairPreserveWork wHeads,
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨2, by omega⟩ then Dir3.left else TM.idleDir (wHeads i),
            TM.idleDir oHead)
    | .copyAlpha =>
        if iHead = Γ.blank then
          (.rewindFormula,
            verifyPairPreserveWork wHeads,
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i => TM.idleDir (wHeads i),
            TM.idleDir oHead)
        else
          match readBit? iHead with
          | some b =>
              if counterHead = Γ.one then
                (.copyAlpha,
                  verifyPairCopyAlphaWrite b wHeads,
                  TM.readBackWrite oHead,
                  Dir3.right,
                  verifyPairCopyAlphaDirs wHeads,
                  TM.idleDir oHead)
              else
                verifyPairReject iHead wHeads oHead
          | none =>
              verifyPairReject iHead wHeads oHead
    | .rewindFormula =>
        if zHead = Γ.start then
          (.rewindAssignment,
            verifyPairPreserveWork wHeads,
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨0, by omega⟩ then Dir3.right else TM.idleDir (wHeads i),
            TM.idleDir oHead)
        else
          (.rewindFormula,
            verifyPairPreserveWork wHeads,
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨0, by omega⟩ then Dir3.left else TM.idleDir (wHeads i),
            TM.idleDir oHead)
    | .rewindAssignment =>
        if αHead = Γ.start then
          (.evalReadFirst (.boundary true false true),
            verifyPairPreserveWork wHeads,
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨1, by omega⟩ then Dir3.right else TM.idleDir (wHeads i),
            TM.idleDir oHead)
        else
          (.rewindAssignment,
            verifyPairPreserveWork wHeads,
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨1, by omega⟩ then Dir3.left else TM.idleDir (wHeads i),
            TM.idleDir oHead)
    | .evalReadFirst mode =>
        if zHead = Γ.blank then
          (.done,
            verifyPairPreserveWork wHeads,
            finishEvalMode mode,
            TM.idleDir iHead,
            fun i => TM.idleDir (wHeads i),
            TM.idleDir oHead)
        else
          match readBit? zHead with
          | some b =>
              (.evalReadSecond mode b,
                verifyPairPreserveWork wHeads,
                TM.readBackWrite oHead,
                TM.idleDir iHead,
                fun i =>
                  if i = ⟨0, by omega⟩ then Dir3.right else TM.idleDir (wHeads i),
                TM.idleDir oHead)
          | none =>
              verifyPairReject iHead wHeads oHead
    | .evalReadSecond mode first =>
        match readBit? zHead with
        | some second =>
            let (nextState, αDir, outWrite) :=
              satEvalTokenStep mode (tokenOfBits first second) αHead
            let nextState' : VerifyPairPhase :=
              match nextState with
              | .readFirst mode' => .evalReadFirst mode'
              | .readSecond mode' first' => .evalReadSecond mode' first'
              | .rewindAlpha mode' => .evalRewindAlpha mode'
              | .done => .done
            (nextState',
              verifyPairPreserveWork wHeads,
              outWrite,
              TM.idleDir iHead,
              verifyPairEvalDirs αHead αDir wHeads,
              TM.idleDir oHead)
        | none =>
            verifyPairReject iHead wHeads oHead
    | .evalRewindAlpha mode =>
        if αHead = Γ.start then
          (.evalReadFirst mode,
            verifyPairPreserveWork wHeads,
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨1, by omega⟩ then Dir3.right else TM.idleDir (wHeads i),
            TM.idleDir oHead)
        else
          (.evalRewindAlpha mode,
            verifyPairPreserveWork wHeads,
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨1, by omega⟩ then Dir3.left else TM.idleDir (wHeads i),
            TM.idleDir oHead)
    | .done =>
        TM.allIdle .done iHead wHeads oHead

private theorem verifyPairDelta_right_of_start
    (state : VerifyPairPhase) (iHead : Γ) (wHeads : Fin 3 → Γ) (oHead : Γ) :
    let tr := verifyPairDelta state iHead wHeads oHead
    (iHead = Γ.start → tr.2.2.2.1 = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → tr.2.2.2.2.1 i = Dir3.right) ∧
    (oHead = Γ.start → tr.2.2.2.2.2 = Dir3.right) := by
  aesop (add simp [verifyPairDelta, verifyPairReject, verifyPairPreserveWork,
    verifyPairSplitWrite, verifyPairSplitDirs, verifyPairCopyAlphaWrite,
    verifyPairCopyAlphaDirs, verifyPairEvalDirs, readBit?, satEvalTokenStep,
    tokenOfBits, TM.allIdle, TM.idleDir_right_of_start,
    TM.rightOfStart_allIdle])

/-- Deterministic three-work-tape verifier for the Boolean function
`SAT.verifyPair`.

This is the machine-level verifier construction. The polynomial budget below
is proved quadratic, and the end-to-end tape simulation below shows that this
split/length/evaluation pipeline writes `1` exactly when
`verifyPair w = true`. -/
def verifyPairTM : TM 3 where
  Q := VerifyPairPhase
  qstart := .init
  qhalt := .done
  δ := verifyPairDelta
  δ_right_of_start := by
    intro state iHead wHeads oHead
    exact verifyPairDelta_right_of_start state iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- Eval phase: projection onto the proven single-tape evaluator
-- ════════════════════════════════════════════════════════════════════════

/-- Writing back the symbol just read is a no-op when no interior cell holds the
left marker (so the head, if `≥ 1`, reads a non-marker). -/
private theorem writeBack_self (t : Tape) (h : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start) :
    t.write (TM.readBackWrite t.read).toΓ = t := by
  by_cases hh : t.head = 0
  · simp [Tape.write, hh]
  · have hne : t.read ≠ Γ.start := by simp only [Tape.read]; exact h t.head (by omega)
    rw [TM.toΓ_readBackWrite_of_ne_start hne]
    simp [Tape.write, hh, Tape.read, Function.update_eq_self]

/-- Hence a write-back-and-move on such a tape is just a move (read-only behavior). -/
private theorem writeBackMove_eq_move (t : Tape) (d : Dir3)
    (h : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start) :
    t.writeAndMove (TM.readBackWrite t.read).toΓ d = t.move d := by
  rw [Tape.writeAndMove, writeBack_self t h]

/-- Project a `verifyPairTM` eval-phase state to the single-tape evaluator's. -/
private def projEvalState : VerifyPairPhase → SatEvalPhase
  | .evalReadFirst m => .readFirst m
  | .evalReadSecond m first => .readSecond m first
  | .evalRewindAlpha m => .rewindAlpha m
  | _ => .done

/-- Project a `verifyPairTM` configuration onto a `satEvalOnInputTM`
configuration: the formula tape `0` becomes the (read-only) input, the
assignment tape `1` becomes work tape `0`, and the output is shared. -/
private def projEvalCfg (c : Cfg 3 verifyPairTM.Q) : Cfg 1 satEvalOnInputTM.Q :=
  { state := projEvalState c.state
    input := c.work ⟨0, by omega⟩
    work := fun _ => c.work ⟨1, by omega⟩
    output := c.output }

private theorem verifyPairTM_init_steps (w : List Bool) :
    ∃ c',
      verifyPairTM.reachesIn 2 (verifyPairTM.initCfg w) c' ∧
      c'.state = .splitScan ∧
      c'.input = (Tape.init (w.map Γ.ofBool)).move Dir3.right ∧
      c'.work ⟨0, by omega⟩ = (Tape.init []).move Dir3.right ∧
      c'.work ⟨1, by omega⟩ = (Tape.init []).move Dir3.right ∧
      (c'.work ⟨2, by omega⟩).HasUnaryPrefix 1 ∧
      (c'.work ⟨2, by omega⟩).cells 0 = Γ.start ∧
      c'.output = (Tape.init []).move Dir3.right := by
  let c₁ : Cfg 3 verifyPairTM.Q :=
    { state := .initCounter
      input := (Tape.init (w.map Γ.ofBool)).move Dir3.right
      work := fun _ => (Tape.init []).move Dir3.right
      output := (Tape.init []).move Dir3.right }
  let c₂ : Cfg 3 verifyPairTM.Q :=
    { state := .splitScan
      input := (Tape.init (w.map Γ.ofBool)).move Dir3.right
      work := fun i =>
        if i = ⟨2, by omega⟩ then
          ((Tape.init []).move Dir3.right).writeAndMove Γ.one Dir3.right
        else
          (Tape.init []).move Dir3.right
      output := (Tape.init []).move Dir3.right }
  have hstep₁ : verifyPairTM.step (verifyPairTM.initCfg w) = some c₁ := by
    simp [c₁, verifyPairTM, TM.step, verifyPairDelta,
      TM.readBackWrite, Tape.writeAndMove, Tape.write, Tape.move, Tape.init]
  have hstep₂ : verifyPairTM.step c₁ = some c₂ := by
    simp [c₁, c₂, verifyPairTM, TM.step, verifyPairDelta,
      TM.readBackWrite, TM.idleDir, Tape.writeAndMove, Tape.write,
      Tape.move, Tape.read, Tape.init]
    constructor
    · cases h : w[0]? with
      | none => simp
      | some b => cases b <;> simp [Γ.ofBool]
    · funext i
      rcases i with ⟨i, hi⟩
      have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hcases with rfl | rfl | rfl <;> simp
  refine ⟨c₂, .step hstep₁ (.step hstep₂ .zero), ?_⟩
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl⟩
  · simp [c₂]
  · simp [c₂]
  · refine ⟨?_, ?_, ?_⟩
    · simp [c₂, Tape.writeAndMove, Tape.write, Tape.move,
        Tape.init]
    · intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      simp [c₂, Tape.writeAndMove, Tape.write, Tape.move, Tape.init]
    · intro i hi
      have hne : i + 1 ≠ 1 := by omega
      simp [c₂, Tape.writeAndMove, Tape.write, Tape.move, Tape.init,
        Function.update_of_ne hne]
  · simp [c₂, Tape.writeAndMove, Tape.write, Tape.move, Tape.init]

-- ════════════════════════════════════════════════════════════════════════
-- Split phase: parse `pair z α`, stage `z`/`α`, build counter, check length
-- ════════════════════════════════════════════════════════════════════════

/-- In `.splitScan`, reading the first `false` advances to `.splitAfterFalse`,
moving the input head right and leaving all work tapes and the output tape
unchanged. -/
private theorem verifyPairSplit_scanX_false_step
    (c : Cfg 3 verifyPairTM.Q)
    (hst : c.state = .splitScan) (hiread : c.input.read = Γ.zero)
    (hwst : ∀ i, (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.step c = some c' ∧
      c'.state = .splitAfterFalse ∧
      c'.input.head = c.input.head + 1 ∧
      c'.input.cells = c.input.cells ∧
      c'.work = c.work ∧
      c'.output = c.output := by
  let c' : Cfg 3 verifyPairTM.Q :=
    { state := .splitAfterFalse
      input := c.input.move Dir3.right
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
          (TM.idleDir (c.work i).read)
      output := c.output.writeAndMove (TM.readBackWrite c.output.read)
        (TM.idleDir c.output.read) }
  refine ⟨c', ?_, rfl, ?_, ?_, ?_, ?_⟩
  · simp [c', verifyPairTM, TM.step, verifyPairDelta, hst, hiread, readBit?,
      verifyPairPreserveWork]
  · simp [c', Tape.move]
  · simpa using Tape.move_cells c.input Dir3.right
  · funext i
    exact TM.tape_writeAndMove_stable (c.work i) (hwst i).1 (hwst i).2
  · exact TM.tape_writeAndMove_stable c.output hoh hons

/-- In `.splitAfterFalse`, reading the second `false` writes `false` to the
formula tape `0`, adds a tally to the counter tape `2`, advances back to
`.splitScan`, and leaves the assignment tape `1` and the output tape
unchanged. -/
private theorem verifyPairSplit_afterFalse_zero_step
    (c : Cfg 3 verifyPairTM.Q)
    (hst : c.state = .splitAfterFalse) (hiread : c.input.read = Γ.zero)
    (h0h : (c.work ⟨0, by omega⟩).head ≥ 1)
    (h1st : (c.work ⟨1, by omega⟩).head ≥ 1 ∧
      ∀ j, j ≥ 1 → (c.work ⟨1, by omega⟩).cells j ≠ Γ.start)
    (h2h : (c.work ⟨2, by omega⟩).head ≥ 1)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.step c = some c' ∧
      c'.state = .splitScan ∧
      c'.input.head = c.input.head + 1 ∧
      c'.input.cells = c.input.cells ∧
      (c'.work ⟨0, by omega⟩).head = (c.work ⟨0, by omega⟩).head + 1 ∧
      (c'.work ⟨0, by omega⟩).cells =
        Function.update (c.work ⟨0, by omega⟩).cells (c.work ⟨0, by omega⟩).head Γ.zero ∧
      c'.work ⟨1, by omega⟩ = c.work ⟨1, by omega⟩ ∧
      (c'.work ⟨2, by omega⟩).head = (c.work ⟨2, by omega⟩).head + 1 ∧
      (c'.work ⟨2, by omega⟩).cells =
        Function.update (c.work ⟨2, by omega⟩).cells (c.work ⟨2, by omega⟩).head Γ.one ∧
      c'.output = c.output := by
  let c' : Cfg 3 verifyPairTM.Q :=
    { state := .splitScan
      input := c.input.move Dir3.right
      work := fun i =>
        (c.work i).writeAndMove (verifyPairSplitWrite false (fun j => (c.work j).read) i)
          (verifyPairSplitDirs (fun j => (c.work j).read) i)
      output := c.output.writeAndMove (TM.readBackWrite c.output.read)
        (TM.idleDir c.output.read) }
  have hstep : verifyPairTM.step c = some c' := by
    simp [c', verifyPairTM, TM.step, verifyPairDelta, hst, hiread, readBit?]
  refine ⟨c', hstep, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [c', Tape.move]
  · simpa using Tape.move_cells c.input Dir3.right
  · show (((c.work ⟨0, by omega⟩).writeAndMove _ _)).head = _
    simp [verifyPairSplitDirs, Tape.writeAndMove, Tape.move, Tape.write_head]
  · show (((c.work ⟨0, by omega⟩).writeAndMove _ _)).cells = _
    have hne0 : (c.work ⟨0, by omega⟩).head ≠ 0 := by omega
    simp only [Tape.writeAndMove, Tape.move_cells, Tape.write, ite_eq_right hne0]
    simp [verifyPairSplitWrite, boolWrite, Γw.toΓ]
  · show ((c.work ⟨1, by omega⟩).writeAndMove _ _) = _
    rw [show verifyPairSplitWrite false (fun j => (c.work j).read) ⟨1, by omega⟩ =
          TM.readBackWrite (c.work ⟨1, by omega⟩).read by simp [verifyPairSplitWrite],
      show verifyPairSplitDirs (fun j => (c.work j).read) ⟨1, by omega⟩ =
          TM.idleDir (c.work ⟨1, by omega⟩).read by simp [verifyPairSplitDirs]]
    exact TM.tape_writeAndMove_stable (c.work ⟨1, by omega⟩) h1st.1 h1st.2
  · show (((c.work ⟨2, by omega⟩).writeAndMove _ _)).head = _
    simp [verifyPairSplitDirs, Tape.writeAndMove, Tape.move, Tape.write_head]
  · show (((c.work ⟨2, by omega⟩).writeAndMove _ _)).cells = _
    have hne2 : (c.work ⟨2, by omega⟩).head ≠ 0 := by omega
    simp only [Tape.writeAndMove, Tape.move_cells, Tape.write, ite_eq_right hne2]
    simp [verifyPairSplitWrite, Γw.toΓ]
  · exact TM.tape_writeAndMove_stable c.output hoh hons

/-- In `.splitScan`, reading the first `true` advances to `.splitAfterTrue`,
moving the input head right and leaving all work tapes and the output tape
unchanged. -/
private theorem verifyPairSplit_scanX_true_step
    (c : Cfg 3 verifyPairTM.Q)
    (hst : c.state = .splitScan) (hiread : c.input.read = Γ.one)
    (hwst : ∀ i, (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.step c = some c' ∧
      c'.state = .splitAfterTrue ∧
      c'.input.head = c.input.head + 1 ∧
      c'.input.cells = c.input.cells ∧
      c'.work = c.work ∧
      c'.output = c.output := by
  let c' : Cfg 3 verifyPairTM.Q :=
    { state := .splitAfterTrue
      input := c.input.move Dir3.right
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
          (TM.idleDir (c.work i).read)
      output := c.output.writeAndMove (TM.readBackWrite c.output.read)
        (TM.idleDir c.output.read) }
  refine ⟨c', ?_, rfl, ?_, ?_, ?_, ?_⟩
  · simp [c', verifyPairTM, TM.step, verifyPairDelta, hst, hiread, readBit?,
      verifyPairPreserveWork]
  · simp [c', Tape.move]
  · simpa using Tape.move_cells c.input Dir3.right
  · funext i
    exact TM.tape_writeAndMove_stable (c.work i) (hwst i).1 (hwst i).2
  · exact TM.tape_writeAndMove_stable c.output hoh hons

/-- In `.splitAfterFalse`, reading `true` recognizes the separator `01` and
advances to `.rewindCounterForAlpha`, leaving all work tapes and the output
tape unchanged. -/
private theorem verifyPairSplit_afterFalse_sep_step
    (c : Cfg 3 verifyPairTM.Q)
    (hst : c.state = .splitAfterFalse) (hiread : c.input.read = Γ.one)
    (hwst : ∀ i, (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.step c = some c' ∧
      c'.state = .rewindCounterForAlpha ∧
      c'.input.head = c.input.head + 1 ∧
      c'.input.cells = c.input.cells ∧
      c'.work = c.work ∧
      c'.output = c.output := by
  let c' : Cfg 3 verifyPairTM.Q :=
    { state := .rewindCounterForAlpha
      input := c.input.move Dir3.right
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
          (TM.idleDir (c.work i).read)
      output := c.output.writeAndMove (TM.readBackWrite c.output.read)
        (TM.idleDir c.output.read) }
  refine ⟨c', ?_, rfl, ?_, ?_, ?_, ?_⟩
  · simp [c', verifyPairTM, TM.step, verifyPairDelta, hst, hiread, readBit?,
      verifyPairPreserveWork]
  · simp [c', Tape.move]
  · simpa using Tape.move_cells c.input Dir3.right
  · funext i
    exact TM.tape_writeAndMove_stable (c.work i) (hwst i).1 (hwst i).2
  · exact TM.tape_writeAndMove_stable c.output hoh hons

/-- In `.splitAfterTrue`, reading the second `true` writes `true` to the formula
tape `0`, adds a tally to the counter tape `2`, advances back to `.splitScan`,
and leaves the assignment tape `1` and the output tape unchanged. -/
private theorem verifyPairSplit_afterTrue_one_step
    (c : Cfg 3 verifyPairTM.Q)
    (hst : c.state = .splitAfterTrue) (hiread : c.input.read = Γ.one)
    (h0h : (c.work ⟨0, by omega⟩).head ≥ 1)
    (h1st : (c.work ⟨1, by omega⟩).head ≥ 1 ∧
      ∀ j, j ≥ 1 → (c.work ⟨1, by omega⟩).cells j ≠ Γ.start)
    (h2h : (c.work ⟨2, by omega⟩).head ≥ 1)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.step c = some c' ∧
      c'.state = .splitScan ∧
      c'.input.head = c.input.head + 1 ∧
      c'.input.cells = c.input.cells ∧
      (c'.work ⟨0, by omega⟩).head = (c.work ⟨0, by omega⟩).head + 1 ∧
      (c'.work ⟨0, by omega⟩).cells =
        Function.update (c.work ⟨0, by omega⟩).cells (c.work ⟨0, by omega⟩).head Γ.one ∧
      c'.work ⟨1, by omega⟩ = c.work ⟨1, by omega⟩ ∧
      (c'.work ⟨2, by omega⟩).head = (c.work ⟨2, by omega⟩).head + 1 ∧
      (c'.work ⟨2, by omega⟩).cells =
        Function.update (c.work ⟨2, by omega⟩).cells (c.work ⟨2, by omega⟩).head Γ.one ∧
      c'.output = c.output := by
  let c' : Cfg 3 verifyPairTM.Q :=
    { state := .splitScan
      input := c.input.move Dir3.right
      work := fun i =>
        (c.work i).writeAndMove (verifyPairSplitWrite true (fun j => (c.work j).read) i)
          (verifyPairSplitDirs (fun j => (c.work j).read) i)
      output := c.output.writeAndMove (TM.readBackWrite c.output.read)
        (TM.idleDir c.output.read) }
  have hstep : verifyPairTM.step c = some c' := by
    simp [c', verifyPairTM, TM.step, verifyPairDelta, hst, hiread, readBit?]
  refine ⟨c', hstep, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [c', Tape.move]
  · simpa using Tape.move_cells c.input Dir3.right
  · show (((c.work ⟨0, by omega⟩).writeAndMove _ _)).head = _
    simp [verifyPairSplitDirs, Tape.writeAndMove, Tape.move, Tape.write_head]
  · show (((c.work ⟨0, by omega⟩).writeAndMove _ _)).cells = _
    have hne0 : (c.work ⟨0, by omega⟩).head ≠ 0 := by omega
    simp only [Tape.writeAndMove, Tape.move_cells, Tape.write, ite_eq_right hne0]
    simp [verifyPairSplitWrite, boolWrite, Γw.toΓ]
  · show ((c.work ⟨1, by omega⟩).writeAndMove _ _) = _
    rw [show verifyPairSplitWrite true (fun j => (c.work j).read) ⟨1, by omega⟩ =
          TM.readBackWrite (c.work ⟨1, by omega⟩).read by simp [verifyPairSplitWrite],
      show verifyPairSplitDirs (fun j => (c.work j).read) ⟨1, by omega⟩ =
          TM.idleDir (c.work ⟨1, by omega⟩).read by simp [verifyPairSplitDirs]]
    exact TM.tape_writeAndMove_stable (c.work ⟨1, by omega⟩) h1st.1 h1st.2
  · show (((c.work ⟨2, by omega⟩).writeAndMove _ _)).head = _
    simp [verifyPairSplitDirs, Tape.writeAndMove, Tape.move, Tape.write_head]
  · show (((c.work ⟨2, by omega⟩).writeAndMove _ _)).cells = _
    have hne2 : (c.work ⟨2, by omega⟩).head ≠ 0 := by omega
    simp only [Tape.writeAndMove, Tape.move_cells, Tape.write, ite_eq_right hne2]
    simp [verifyPairSplitWrite, Γw.toΓ]
  · exact TM.tape_writeAndMove_stable c.output hoh hons

/-- Two-step decoding of a doubled `false` bit: writes `false` to the formula
tape, a tally to the counter tape, and returns to `.splitScan`. -/
private theorem verifyPairSplit_false_bit_step
    (c : Cfg 3 verifyPairTM.Q)
    (hst : c.state = .splitScan)
    (hread0 : c.input.read = Γ.zero)
    (hnext0 : c.input.cells (c.input.head + 1) = Γ.zero)
    (hwst : ∀ i, (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.reachesIn 2 c c' ∧
      c'.state = .splitScan ∧
      c'.input.head = c.input.head + 2 ∧
      c'.input.cells = c.input.cells ∧
      (c'.work ⟨0, by omega⟩).head = (c.work ⟨0, by omega⟩).head + 1 ∧
      (c'.work ⟨0, by omega⟩).cells =
        Function.update (c.work ⟨0, by omega⟩).cells (c.work ⟨0, by omega⟩).head Γ.zero ∧
      c'.work ⟨1, by omega⟩ = c.work ⟨1, by omega⟩ ∧
      (c'.work ⟨2, by omega⟩).head = (c.work ⟨2, by omega⟩).head + 1 ∧
      (c'.work ⟨2, by omega⟩).cells =
        Function.update (c.work ⟨2, by omega⟩).cells (c.work ⟨2, by omega⟩).head Γ.one ∧
      c'.output = c.output := by
  obtain ⟨c1, hstep1, hst1, hc1_ih, hc1_ic, hc1_w, hc1_o⟩ :=
    verifyPairSplit_scanX_false_step c hst hread0 hwst hoh hons
  have hc1_read : c1.input.read = Γ.zero := by
    show c1.input.cells c1.input.head = Γ.zero
    rw [hc1_ic, hc1_ih]; exact hnext0
  have h0h : (c1.work ⟨0, by omega⟩).head ≥ 1 := by rw [hc1_w]; exact (hwst ⟨0, by omega⟩).1
  have h1st : (c1.work ⟨1, by omega⟩).head ≥ 1 ∧
      ∀ j, j ≥ 1 → (c1.work ⟨1, by omega⟩).cells j ≠ Γ.start := by
    rw [hc1_w]; exact hwst ⟨1, by omega⟩
  have h2h : (c1.work ⟨2, by omega⟩).head ≥ 1 := by rw [hc1_w]; exact (hwst ⟨2, by omega⟩).1
  have hoh1 : c1.output.head ≥ 1 := by rw [hc1_o]; exact hoh
  have hons1 : ∀ j, j ≥ 1 → c1.output.cells j ≠ Γ.start := by rw [hc1_o]; exact hons
  obtain ⟨c2, hstep2, hst2, hc2_ih, hc2_ic, hc2_0h, hc2_0c, hc2_1w, hc2_2h, hc2_2c, hc2_o⟩ :=
    verifyPairSplit_afterFalse_zero_step c1 hst1 hc1_read h0h h1st h2h hoh1 hons1
  refine ⟨c2, .step hstep1 (.step hstep2 .zero), hst2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc2_ih, hc1_ih]
  · rw [hc2_ic, hc1_ic]
  · rw [hc2_0h, hc1_w]
  · rw [hc2_0c, hc1_w]
  · rw [hc2_1w, hc1_w]
  · rw [hc2_2h, hc1_w]
  · rw [hc2_2c, hc1_w]
  · rw [hc2_o, hc1_o]

/-- Two-step decoding of a doubled `true` bit: writes `true` to the formula
tape, a tally to the counter tape, and returns to `.splitScan`. -/
private theorem verifyPairSplit_true_bit_step
    (c : Cfg 3 verifyPairTM.Q)
    (hst : c.state = .splitScan)
    (hread1 : c.input.read = Γ.one)
    (hnext1 : c.input.cells (c.input.head + 1) = Γ.one)
    (hwst : ∀ i, (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.reachesIn 2 c c' ∧
      c'.state = .splitScan ∧
      c'.input.head = c.input.head + 2 ∧
      c'.input.cells = c.input.cells ∧
      (c'.work ⟨0, by omega⟩).head = (c.work ⟨0, by omega⟩).head + 1 ∧
      (c'.work ⟨0, by omega⟩).cells =
        Function.update (c.work ⟨0, by omega⟩).cells (c.work ⟨0, by omega⟩).head Γ.one ∧
      c'.work ⟨1, by omega⟩ = c.work ⟨1, by omega⟩ ∧
      (c'.work ⟨2, by omega⟩).head = (c.work ⟨2, by omega⟩).head + 1 ∧
      (c'.work ⟨2, by omega⟩).cells =
        Function.update (c.work ⟨2, by omega⟩).cells (c.work ⟨2, by omega⟩).head Γ.one ∧
      c'.output = c.output := by
  obtain ⟨c1, hstep1, hst1, hc1_ih, hc1_ic, hc1_w, hc1_o⟩ :=
    verifyPairSplit_scanX_true_step c hst hread1 hwst hoh hons
  have hc1_read : c1.input.read = Γ.one := by
    show c1.input.cells c1.input.head = Γ.one
    rw [hc1_ic, hc1_ih]; exact hnext1
  have h0h : (c1.work ⟨0, by omega⟩).head ≥ 1 := by rw [hc1_w]; exact (hwst ⟨0, by omega⟩).1
  have h1st : (c1.work ⟨1, by omega⟩).head ≥ 1 ∧
      ∀ j, j ≥ 1 → (c1.work ⟨1, by omega⟩).cells j ≠ Γ.start := by
    rw [hc1_w]; exact hwst ⟨1, by omega⟩
  have h2h : (c1.work ⟨2, by omega⟩).head ≥ 1 := by rw [hc1_w]; exact (hwst ⟨2, by omega⟩).1
  have hoh1 : c1.output.head ≥ 1 := by rw [hc1_o]; exact hoh
  have hons1 : ∀ j, j ≥ 1 → c1.output.cells j ≠ Γ.start := by rw [hc1_o]; exact hons
  obtain ⟨c2, hstep2, hst2, hc2_ih, hc2_ic, hc2_0h, hc2_0c, hc2_1w, hc2_2h, hc2_2c, hc2_o⟩ :=
    verifyPairSplit_afterTrue_one_step c1 hst1 hc1_read h0h h1st h2h hoh1 hons1
  refine ⟨c2, .step hstep1 (.step hstep2 .zero), hst2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc2_ih, hc1_ih]
  · rw [hc2_ic, hc1_ic]
  · rw [hc2_0h, hc1_w]
  · rw [hc2_0c, hc1_w]
  · rw [hc2_1w, hc1_w]
  · rw [hc2_2h, hc1_w]
  · rw [hc2_2c, hc1_w]
  · rw [hc2_o, hc1_o]

/-- Two-step decoding of a doubled `b` bit, uniform in `b`. -/
private theorem verifyPairSplit_bit_step (b : Bool)
    (c : Cfg 3 verifyPairTM.Q)
    (hst : c.state = .splitScan)
    (hread : c.input.read = Γ.ofBool b)
    (hnext : c.input.cells (c.input.head + 1) = Γ.ofBool b)
    (hwst : ∀ i, (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.reachesIn 2 c c' ∧
      c'.state = .splitScan ∧
      c'.input.head = c.input.head + 2 ∧
      c'.input.cells = c.input.cells ∧
      (c'.work ⟨0, by omega⟩).head = (c.work ⟨0, by omega⟩).head + 1 ∧
      (c'.work ⟨0, by omega⟩).cells =
        Function.update (c.work ⟨0, by omega⟩).cells (c.work ⟨0, by omega⟩).head (Γ.ofBool b) ∧
      c'.work ⟨1, by omega⟩ = c.work ⟨1, by omega⟩ ∧
      (c'.work ⟨2, by omega⟩).head = (c.work ⟨2, by omega⟩).head + 1 ∧
      (c'.work ⟨2, by omega⟩).cells =
        Function.update (c.work ⟨2, by omega⟩).cells (c.work ⟨2, by omega⟩).head Γ.one ∧
      c'.output = c.output := by
  cases b with
  | false =>
      have hr : c.input.read = Γ.zero := hread
      have hn : c.input.cells (c.input.head + 1) = Γ.zero := hnext
      simpa [Γ.ofBool] using verifyPairSplit_false_bit_step c hst hr hn hwst hoh hons
  | true =>
      have hr : c.input.read = Γ.one := hread
      have hn : c.input.cells (c.input.head + 1) = Γ.one := hnext
      simpa [Γ.ofBool] using verifyPairSplit_true_bit_step c hst hr hn hwst hoh hons

/-- Two-step recognition of the separator `01`, transitioning from the split
loop into `.rewindCounterForAlpha`, leaving all work tapes and the output
tape unchanged. -/
private theorem verifyPairSplit_separator_step
    (c : Cfg 3 verifyPairTM.Q)
    (hst : c.state = .splitScan)
    (hread0 : c.input.read = Γ.zero)
    (hnext1 : c.input.cells (c.input.head + 1) = Γ.one)
    (hwst : ∀ i, (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.reachesIn 2 c c' ∧
      c'.state = .rewindCounterForAlpha ∧
      c'.input.head = c.input.head + 2 ∧
      c'.input.cells = c.input.cells ∧
      c'.work = c.work ∧
      c'.output = c.output := by
  obtain ⟨c1, hstep1, hst1, hc1_ih, hc1_ic, hc1_w, hc1_o⟩ :=
    verifyPairSplit_scanX_false_step c hst hread0 hwst hoh hons
  have hc1_read : c1.input.read = Γ.one := by
    show c1.input.cells c1.input.head = Γ.one
    rw [hc1_ic, hc1_ih]; exact hnext1
  have hwst1 : ∀ i, (c1.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c1.work i).cells j ≠ Γ.start := by
    rw [hc1_w]; exact hwst
  have hoh1 : c1.output.head ≥ 1 := by rw [hc1_o]; exact hoh
  have hons1 : ∀ j, j ≥ 1 → c1.output.cells j ≠ Γ.start := by rw [hc1_o]; exact hons
  obtain ⟨c2, hstep2, hst2, hc2_ih, hc2_ic, hc2_w, hc2_o⟩ :=
    verifyPairSplit_afterFalse_sep_step c1 hst1 hc1_read hwst1 hoh1 hons1
  refine ⟨c2, .step hstep1 (.step hstep2 .zero), hst2, ?_, ?_, ?_, ?_⟩
  · rw [hc2_ih, hc1_ih]
  · rw [hc2_ic, hc1_ic]
  · rw [hc2_w, hc1_w]
  · rw [hc2_o, hc1_o]

/-- The split loop. Starting in `.splitScan` on an input segment encoding the
doubled bits of `bits`, the machine consumes `2 * |bits|` input cells, writes
`bits` to the formula tape `0` and `|bits|` tallies to the counter tape `2`,
and returns to `.splitScan`, leaving the assignment tape `1` and the output
tape unchanged. -/
private theorem verifyPairSplit_scanX_loop :
    ∀ (bits : List Bool) (c : Cfg 3 verifyPairTM.Q),
      c.state = .splitScan →
      c.input.head ≥ 1 →
      c.input.cells 0 = Γ.start →
      (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
      (∀ i, (h : i < bits.length) →
        c.input.cells (c.input.head + 2 * i) = Γ.ofBool (bits[i]'h) ∧
        c.input.cells (c.input.head + (2 * i + 1)) = Γ.ofBool (bits[i]'h)) →
      (c.work ⟨0, by omega⟩).head ≥ 1 →
      (c.work ⟨0, by omega⟩).cells 0 = Γ.start →
      (∀ j, j ≥ 1 → (c.work ⟨0, by omega⟩).cells j ≠ Γ.start) →
      (c.work ⟨1, by omega⟩).head ≥ 1 →
      (∀ j, j ≥ 1 → (c.work ⟨1, by omega⟩).cells j ≠ Γ.start) →
      (c.work ⟨2, by omega⟩).head ≥ 1 →
      (c.work ⟨2, by omega⟩).cells 0 = Γ.start →
      (∀ j, j ≥ 1 → (c.work ⟨2, by omega⟩).cells j ≠ Γ.start) →
      c.output.head ≥ 1 →
      (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
      ∃ c',
        verifyPairTM.reachesIn (2 * bits.length) c c' ∧
        c'.state = .splitScan ∧
        c'.input.head = c.input.head + 2 * bits.length ∧
        c'.input.cells = c.input.cells ∧
        (c'.work ⟨0, by omega⟩).head = (c.work ⟨0, by omega⟩).head + bits.length ∧
        (c'.work ⟨0, by omega⟩).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (c'.work ⟨0, by omega⟩).cells j ≠ Γ.start) ∧
        (∀ j, j < (c.work ⟨0, by omega⟩).head →
            (c'.work ⟨0, by omega⟩).cells j = (c.work ⟨0, by omega⟩).cells j) ∧
        (∀ j, j ≥ (c.work ⟨0, by omega⟩).head + bits.length →
            (c'.work ⟨0, by omega⟩).cells j = (c.work ⟨0, by omega⟩).cells j) ∧
        (∀ i, (h : i < bits.length) →
            (c'.work ⟨0, by omega⟩).cells ((c.work ⟨0, by omega⟩).head + i)
              = Γ.ofBool (bits[i]'h)) ∧
        c'.work ⟨1, by omega⟩ = c.work ⟨1, by omega⟩ ∧
        (c'.work ⟨2, by omega⟩).head = (c.work ⟨2, by omega⟩).head + bits.length ∧
        (c'.work ⟨2, by omega⟩).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (c'.work ⟨2, by omega⟩).cells j ≠ Γ.start) ∧
        (∀ j, j < (c.work ⟨2, by omega⟩).head →
            (c'.work ⟨2, by omega⟩).cells j = (c.work ⟨2, by omega⟩).cells j) ∧
        (∀ j, j ≥ (c.work ⟨2, by omega⟩).head + bits.length →
            (c'.work ⟨2, by omega⟩).cells j = (c.work ⟨2, by omega⟩).cells j) ∧
        (∀ i, (_ : i < bits.length) →
            (c'.work ⟨2, by omega⟩).cells ((c.work ⟨2, by omega⟩).head + i) = Γ.one) ∧
        c'.output = c.output := by
  intro bits
  induction bits with
  | nil =>
      intro c hst hih _ _ _ h0h h0c0 h0ns h1h h1ns h2h h2c0 h2ns _ _
      refine ⟨c, by simpa using (TM.reachesIn.zero (tm := verifyPairTM) (c := c)),
        hst, by simp, rfl, by simp, h0c0, h0ns, ?_, ?_, ?_, rfl, by simp, h2c0, h2ns, ?_, ?_, ?_,
          rfl⟩
      · intro j _; rfl
      · intro j _; rfl
      · intro i h; exact absurd h (by simp)
      · intro j _; rfl
      · intro j _; rfl
      · intro i h; exact absurd h (by simp)
  | cons b bs ih =>
      intro c hst hih hic0 hins hbits h0h h0c0 h0ns h1h h1ns h2h h2c0 h2ns hoh hons
      have hbits0 := hbits 0 (by simp)
      have hwst : ∀ i, (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start := by
        intro i
        match i with
        | ⟨0, _⟩ => exact ⟨h0h, h0ns⟩
        | ⟨1, _⟩ => exact ⟨h1h, h1ns⟩
        | ⟨2, _⟩ => exact ⟨h2h, h2ns⟩
      have hofb : Γ.ofBool b ≠ Γ.start := by cases b <;> decide
      have hread : c.input.read = Γ.ofBool b := by
        show c.input.cells c.input.head = Γ.ofBool b; simpa using hbits0.1
      have hnext : c.input.cells (c.input.head + 1) = Γ.ofBool b := by simpa using hbits0.2
      obtain ⟨c1, hreach1, hst1, hc1_ih, hc1_ic, hc1_0h, hc1_0c, hc1_1w, hc1_2h, hc1_2c, hc1_o⟩ :=
        verifyPairSplit_bit_step b c hst hread hnext hwst hoh hons
      have h1c1_ih : c1.input.head ≥ 1 := by rw [hc1_ih]; omega
      have h1c1_ic0 : c1.input.cells 0 = Γ.start := by rw [hc1_ic]; exact hic0
      have h1c1_ins : ∀ j, j ≥ 1 → c1.input.cells j ≠ Γ.start := by
        intro j hj; rw [hc1_ic]; exact hins j hj
      have hc1_hbits : ∀ i, (h : i < bs.length) →
          c1.input.cells (c1.input.head + 2 * i) = Γ.ofBool (bs[i]'h) ∧
          c1.input.cells (c1.input.head + (2 * i + 1)) = Γ.ofBool (bs[i]'h) := by
        intro i hi
        have horig := hbits (i + 1) (by simpa using hi)
        refine ⟨?_, ?_⟩
        · rw [hc1_ic, hc1_ih,
            show c.input.head + 2 + 2 * i = c.input.head + 2 * (i + 1) from by ring]
          simpa using horig.1
        · rw [hc1_ic, hc1_ih,
            show c.input.head + 2 + (2 * i + 1) = c.input.head + (2 * (i + 1) + 1) from by ring]
          simpa using horig.2
      have h0h1 : (c1.work ⟨0, by omega⟩).head ≥ 1 := by rw [hc1_0h]; omega
      have h0c01 : (c1.work ⟨0, by omega⟩).cells 0 = Γ.start := by
        rw [hc1_0c, Function.update_of_ne (by omega)]; exact h0c0
      have h0ns1 : ∀ j, j ≥ 1 → (c1.work ⟨0, by omega⟩).cells j ≠ Γ.start := by
        intro j hj; rw [hc1_0c]
        by_cases hjx : j = (c.work ⟨0, by omega⟩).head
        · rw [hjx, Function.update_self]; exact hofb
        · rw [Function.update_of_ne hjx]; exact h0ns j hj
      have h1h1 : (c1.work ⟨1, by omega⟩).head ≥ 1 := by rw [hc1_1w]; exact h1h
      have h1ns1 : ∀ j, j ≥ 1 → (c1.work ⟨1, by omega⟩).cells j ≠ Γ.start := by
        intro j hj; rw [hc1_1w]; exact h1ns j hj
      have h2h1 : (c1.work ⟨2, by omega⟩).head ≥ 1 := by rw [hc1_2h]; omega
      have h2c01 : (c1.work ⟨2, by omega⟩).cells 0 = Γ.start := by
        rw [hc1_2c, Function.update_of_ne (by omega)]; exact h2c0
      have h2ns1 : ∀ j, j ≥ 1 → (c1.work ⟨2, by omega⟩).cells j ≠ Γ.start := by
        intro j hj; rw [hc1_2c]
        by_cases hjx : j = (c.work ⟨2, by omega⟩).head
        · rw [hjx, Function.update_self]; decide
        · rw [Function.update_of_ne hjx]; exact h2ns j hj
      have hoh1 : c1.output.head ≥ 1 := by rw [hc1_o]; exact hoh
      have hons1 : ∀ j, j ≥ 1 → c1.output.cells j ≠ Γ.start := by
        intro j hj; rw [hc1_o]; exact hons j hj
      obtain ⟨c', hreach, hst', hc_ih, hc_ic, hc_0h, hc_0c0, hc_0ns, hc_0below,
          hc_0above, hc_0data, hc_1w, hc_2h, hc_2c0, hc_2ns, hc_2below, hc_2above,
          hc_2data, hc_o⟩ :=
        ih c1 hst1 h1c1_ih h1c1_ic0 h1c1_ins hc1_hbits h0h1 h0c01 h0ns1 h1h1 h1ns1
          h2h1 h2c01 h2ns1 hoh1 hons1
      have hreach_total : verifyPairTM.reachesIn (2 * (b :: bs).length) c c' := by
        have htot : verifyPairTM.reachesIn (2 + 2 * bs.length) c c' :=
          TM.reachesIn_trans _ hreach1 hreach
        have heq : 2 * (b :: bs).length = 2 + 2 * bs.length := by
          simp only [List.length_cons]; omega
        rw [heq]; exact htot
      refine ⟨c', hreach_total, hst', ?_, ?_, ?_, hc_0c0, hc_0ns, ?_, ?_, ?_, ?_, ?_,
        hc_2c0, hc_2ns, ?_, ?_, ?_, ?_⟩
      · rw [hc_ih, hc1_ih]; simp only [List.length_cons]; omega
      · rw [hc_ic, hc1_ic]
      · rw [hc_0h, hc1_0h]; simp only [List.length_cons]; omega
      · intro j hj
        have hj1 : j < (c1.work ⟨0, by omega⟩).head := by rw [hc1_0h]; omega
        rw [hc_0below j hj1, hc1_0c, Function.update_of_ne (Nat.ne_of_lt hj)]
      · intro j hj
        have hj1 : j ≥ (c1.work ⟨0, by omega⟩).head + bs.length := by
          rw [hc1_0h]; simp only [List.length_cons] at hj; omega
        rw [hc_0above j hj1, hc1_0c, Function.update_of_ne (by omega)]
      · intro i hi
        cases i with
        | zero =>
            have hj1 : (c.work ⟨0, by omega⟩).head < (c1.work ⟨0, by omega⟩).head := by
              rw [hc1_0h]; omega
            rw [show (c.work ⟨0, by omega⟩).head + 0 = (c.work ⟨0, by omega⟩).head from by omega,
              hc_0below _ hj1, hc1_0c, Function.update_self]
            rfl
        | succ i' =>
            have hi' : i' < bs.length := by simpa using hi
            have hpos : (c.work ⟨0, by omega⟩).head + (i' + 1) =
                (c1.work ⟨0, by omega⟩).head + i' := by rw [hc1_0h]; omega
            rw [hpos, hc_0data i' hi']; rfl
      · rw [hc_1w, hc1_1w]
      · rw [hc_2h, hc1_2h]; simp only [List.length_cons]; omega
      · intro j hj
        have hj1 : j < (c1.work ⟨2, by omega⟩).head := by rw [hc1_2h]; omega
        rw [hc_2below j hj1, hc1_2c, Function.update_of_ne (Nat.ne_of_lt hj)]
      · intro j hj
        have hj1 : j ≥ (c1.work ⟨2, by omega⟩).head + bs.length := by
          rw [hc1_2h]; simp only [List.length_cons] at hj; omega
        rw [hc_2above j hj1, hc1_2c, Function.update_of_ne (by omega)]
      · intro i hi
        cases i with
        | zero =>
            have hj1 : (c.work ⟨2, by omega⟩).head < (c1.work ⟨2, by omega⟩).head := by
              rw [hc1_2h]; omega
            rw [show (c.work ⟨2, by omega⟩).head + 0 = (c.work ⟨2, by omega⟩).head from by omega,
              hc_2below _ hj1, hc1_2c, Function.update_self]
        | succ i' =>
            have hi' : i' < bs.length := by simpa using hi
            have hpos : (c.work ⟨2, by omega⟩).head + (i' + 1) =
                (c1.work ⟨2, by omega⟩).head + i' := by rw [hc1_2h]; omega
            rw [hpos, hc_2data i' hi']
      · rw [hc_o, hc1_o]

/-- Generic full-frame rewind loop for `verifyPairTM`. Given step lemmas that,
in `rState`, move the tracked tape `rIdx` left while preserving everything else
(and at head `0` enter `tState` moving `rIdx` to cell `1`), the machine rewinds
tape `rIdx` from head `p` to head `1` in `p + 1` steps, preserving all cells of
`rIdx`, every other work tape, the input, and the output. -/
private theorem verifyPair_rewind_loop (rIdx : Fin 3) (rState tState : VerifyPairPhase)
    (hleft : ∀ c : Cfg 3 verifyPairTM.Q, c.state = rState → (c.work rIdx).read ≠ Γ.start →
      c.input.head ≥ 1 → (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
      (∀ i, i ≠ rIdx → (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start) →
      c.output.head ≥ 1 → (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
      ∃ c', verifyPairTM.step c = some c' ∧ c'.state = rState ∧
        (c'.work rIdx).head = (c.work rIdx).head - 1 ∧
        (c'.work rIdx).cells = (c.work rIdx).cells ∧
        (∀ i, i ≠ rIdx → c'.work i = c.work i) ∧ c'.input = c.input ∧ c'.output = c.output)
    (hbase : ∀ c : Cfg 3 verifyPairTM.Q, c.state = rState → (c.work rIdx).read = Γ.start →
      (c.work rIdx).head = 0 →
      c.input.head ≥ 1 → (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
      (∀ i, i ≠ rIdx → (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start) →
      c.output.head ≥ 1 → (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
      ∃ c', verifyPairTM.step c = some c' ∧ c'.state = tState ∧
        (c'.work rIdx).head = 1 ∧ (c'.work rIdx).cells = (c.work rIdx).cells ∧
        (∀ i, i ≠ rIdx → c'.work i = c.work i) ∧ c'.input = c.input ∧ c'.output = c.output) :
    ∀ (p : ℕ) (c : Cfg 3 verifyPairTM.Q), c.state = rState →
      (c.work rIdx).cells 0 = Γ.start → (∀ j, j ≥ 1 → (c.work rIdx).cells j ≠ Γ.start) →
      (c.work rIdx).head = p →
      c.input.head ≥ 1 → (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
      (∀ i, i ≠ rIdx → (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start) →
      c.output.head ≥ 1 → (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
      ∃ c', verifyPairTM.reachesIn (p + 1) c c' ∧ c'.state = tState ∧
        (c'.work rIdx).head = 1 ∧ (c'.work rIdx).cells = (c.work rIdx).cells ∧
        (∀ i, i ≠ rIdx → c'.work i = c.work i) ∧ c'.input = c.input ∧ c'.output = c.output := by
  intro p
  induction p with
  | zero =>
      intro c hst hc0 _ hhead hih hins hframe hoh hons
      have hread : (c.work rIdx).read = Γ.start := by
        show (c.work rIdx).cells (c.work rIdx).head = Γ.start; rw [hhead]; exact hc0
      obtain ⟨c', hstep, hst', hrh, hrc, hfr, hinp, hout⟩ :=
        hbase c hst hread hhead hih hins hframe hoh hons
      exact ⟨c', .step hstep .zero, hst', hrh, hrc, hfr, hinp, hout⟩
  | succ p ih =>
      intro c hst hc0 hns hhead hih hins hframe hoh hons
      have hread : (c.work rIdx).read ≠ Γ.start := by
        show (c.work rIdx).cells (c.work rIdx).head ≠ Γ.start
        rw [hhead]; exact hns (p + 1) (by omega)
      obtain ⟨c1, hstep, hst1, hrh1, hrc1, hfr1, hinp1, hout1⟩ :=
        hleft c hst hread hih hins hframe hoh hons
      have hc1_head : (c1.work rIdx).head = p := by rw [hrh1, hhead]; omega
      have hc1_c0 : (c1.work rIdx).cells 0 = Γ.start := by rw [hrc1]; exact hc0
      have hc1_ns : ∀ j, j ≥ 1 → (c1.work rIdx).cells j ≠ Γ.start := by rw [hrc1]; exact hns
      have hc1_ih : c1.input.head ≥ 1 := by rw [hinp1]; exact hih
      have hc1_ins : ∀ j, j ≥ 1 → c1.input.cells j ≠ Γ.start := by rw [hinp1]; exact hins
      have hc1_frame : ∀ i, i ≠ rIdx →
          (c1.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c1.work i).cells j ≠ Γ.start := by
        intro i hi; rw [hfr1 i hi]; exact hframe i hi
      have hc1_oh : c1.output.head ≥ 1 := by rw [hout1]; exact hoh
      have hc1_ons : ∀ j, j ≥ 1 → c1.output.cells j ≠ Γ.start := by rw [hout1]; exact hons
      obtain ⟨c', hreach, hst', hrh', hrc', hfr', hinp', hout'⟩ :=
        ih c1 hst1 hc1_c0 hc1_ns hc1_head hc1_ih hc1_ins hc1_frame hc1_oh hc1_ons
      refine ⟨c', .step hstep hreach, hst', hrh', ?_, ?_, ?_, ?_⟩
      · rw [hrc', hrc1]
      · intro i hi; rw [hfr' i hi, hfr1 i hi]
      · rw [hinp', hinp1]
      · rw [hout', hout1]

/-- `.rewindCounterForAlpha` left step: with a non-start counter cell under the
head, move the counter tape left, preserving everything else. -/
private theorem verifyPairSplit_rewindCounter_left_step
    (c : Cfg 3 verifyPairTM.Q) (hst : c.state = .rewindCounterForAlpha)
    (hread : (c.work ⟨2, by omega⟩).read ≠ Γ.start)
    (hih : c.input.head ≥ 1) (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hframe : ∀ i, i ≠ (⟨2, by omega⟩ : Fin 3) →
      (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.step c = some c' ∧ c'.state = .rewindCounterForAlpha ∧
      (c'.work ⟨2, by omega⟩).head = (c.work ⟨2, by omega⟩).head - 1 ∧
      (c'.work ⟨2, by omega⟩).cells = (c.work ⟨2, by omega⟩).cells ∧
      (∀ i, i ≠ (⟨2, by omega⟩ : Fin 3) → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output := by
  have hinp_read : c.input.read ≠ Γ.start := by
    show c.input.cells c.input.head ≠ Γ.start; exact hins _ hih
  have hread2 : (c.work (2 : Fin 3)).read ≠ Γ.start := hread
  let c' : Cfg 3 verifyPairTM.Q :=
    { state := .rewindCounterForAlpha
      input := c.input.move (TM.idleDir c.input.read)
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
          (if i = (⟨2, by omega⟩ : Fin 3) then Dir3.left else TM.idleDir (c.work i).read)
      output := c.output.writeAndMove (TM.readBackWrite c.output.read)
        (TM.idleDir c.output.read) }
  have hstep : verifyPairTM.step c = some c' := by
    simp [c', verifyPairTM, TM.step, verifyPairDelta, hst, hread2,
      verifyPairPreserveWork]
  refine ⟨c', hstep, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show ((c.work ⟨2, by omega⟩).writeAndMove (TM.readBackWrite
      (c.work ⟨2, by omega⟩).read).toΓ Dir3.left).head = _
    simp [Tape.writeAndMove, Tape.move, Tape.write_head]
  · show ((c.work ⟨2, by omega⟩).writeAndMove (TM.readBackWrite
      (c.work ⟨2, by omega⟩).read).toΓ Dir3.left).cells = _
    rw [Tape.writeAndMove, Tape.move_cells, TM.toΓ_readBackWrite_of_ne_start hread]
    simp [Tape.write, Tape.read, Function.update_eq_self]
  · intro i hi
    show (c.work i).writeAndMove _ _ = c.work i
    rw [ite_eq_right hi]
    exact TM.tape_writeAndMove_stable (c.work i) (hframe i hi).1 (hframe i hi).2
  · exact TM.transitionInput_eq_self hinp_read
  · exact TM.tape_writeAndMove_stable c.output hoh hons

/-- `.rewindCounterForAlpha` base step: with the counter head at the left
marker, move right into `.copyAlpha`, preserving everything else. -/
private theorem verifyPairSplit_rewindCounter_base_step
    (c : Cfg 3 verifyPairTM.Q) (hst : c.state = .rewindCounterForAlpha)
    (hread : (c.work ⟨2, by omega⟩).read = Γ.start)
    (hhead0 : (c.work ⟨2, by omega⟩).head = 0)
    (hih : c.input.head ≥ 1) (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hframe : ∀ i, i ≠ (⟨2, by omega⟩ : Fin 3) →
      (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.step c = some c' ∧ c'.state = .copyAlpha ∧
      (c'.work ⟨2, by omega⟩).head = 1 ∧
      (c'.work ⟨2, by omega⟩).cells = (c.work ⟨2, by omega⟩).cells ∧
      (∀ i, i ≠ (⟨2, by omega⟩ : Fin 3) → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output := by
  have hinp_read : c.input.read ≠ Γ.start := by
    show c.input.cells c.input.head ≠ Γ.start; exact hins _ hih
  have hread2 : (c.work (2 : Fin 3)).read = Γ.start := hread
  have hhead2 : (c.work (2 : Fin 3)).head = 0 := hhead0
  let c' : Cfg 3 verifyPairTM.Q :=
    { state := .copyAlpha
      input := c.input.move (TM.idleDir c.input.read)
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
          (if i = (⟨2, by omega⟩ : Fin 3) then Dir3.right else TM.idleDir (c.work i).read)
      output := c.output.writeAndMove (TM.readBackWrite c.output.read)
        (TM.idleDir c.output.read) }
  have hstep : verifyPairTM.step c = some c' := by
    simp [c', verifyPairTM, TM.step, verifyPairDelta, hst, hread2,
      verifyPairPreserveWork]
  refine ⟨c', hstep, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show ((c.work ⟨2, by omega⟩).writeAndMove (TM.readBackWrite
      (c.work ⟨2, by omega⟩).read).toΓ Dir3.right).head = _
    simp [Tape.writeAndMove, Tape.move, Tape.write_head, hhead2]
  · show ((c.work ⟨2, by omega⟩).writeAndMove (TM.readBackWrite
      (c.work ⟨2, by omega⟩).read).toΓ Dir3.right).cells = _
    rw [Tape.writeAndMove, Tape.move_cells]
    simp [Tape.write, hhead2]
  · intro i hi
    show (c.work i).writeAndMove _ _ = c.work i
    rw [ite_eq_right hi]
    exact TM.tape_writeAndMove_stable (c.work i) (hframe i hi).1 (hframe i hi).2
  · exact TM.transitionInput_eq_self hinp_read
  · exact TM.tape_writeAndMove_stable c.output hoh hons

/-- `.rewindFormula` left step: move the formula tape left, preserving the rest. -/
private theorem verifyPairSplit_rewindFormula_left_step
    (c : Cfg 3 verifyPairTM.Q) (hst : c.state = .rewindFormula)
    (hread : (c.work ⟨0, by omega⟩).read ≠ Γ.start)
    (hih : c.input.head ≥ 1) (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hframe : ∀ i, i ≠ (⟨0, by omega⟩ : Fin 3) →
      (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.step c = some c' ∧ c'.state = .rewindFormula ∧
      (c'.work ⟨0, by omega⟩).head = (c.work ⟨0, by omega⟩).head - 1 ∧
      (c'.work ⟨0, by omega⟩).cells = (c.work ⟨0, by omega⟩).cells ∧
      (∀ i, i ≠ (⟨0, by omega⟩ : Fin 3) → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output := by
  have hinp_read : c.input.read ≠ Γ.start := by
    show c.input.cells c.input.head ≠ Γ.start; exact hins _ hih
  have hread2 : (c.work (0 : Fin 3)).read ≠ Γ.start := hread
  let c' : Cfg 3 verifyPairTM.Q :=
    { state := .rewindFormula
      input := c.input.move (TM.idleDir c.input.read)
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
          (if i = (⟨0, by omega⟩ : Fin 3) then Dir3.left else TM.idleDir (c.work i).read)
      output := c.output.writeAndMove (TM.readBackWrite c.output.read)
        (TM.idleDir c.output.read) }
  have hstep : verifyPairTM.step c = some c' := by
    simp [c', verifyPairTM, TM.step, verifyPairDelta, hst, hread2,
      verifyPairPreserveWork]
  refine ⟨c', hstep, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show ((c.work ⟨0, by omega⟩).writeAndMove (TM.readBackWrite
      (c.work ⟨0, by omega⟩).read).toΓ Dir3.left).head = _
    simp [Tape.writeAndMove, Tape.move, Tape.write_head]
  · show ((c.work ⟨0, by omega⟩).writeAndMove (TM.readBackWrite
      (c.work ⟨0, by omega⟩).read).toΓ Dir3.left).cells = _
    rw [Tape.writeAndMove, Tape.move_cells, TM.toΓ_readBackWrite_of_ne_start hread]
    simp [Tape.write, Tape.read, Function.update_eq_self]
  · intro i hi
    show (c.work i).writeAndMove _ _ = c.work i
    rw [ite_eq_right hi]
    exact TM.tape_writeAndMove_stable (c.work i) (hframe i hi).1 (hframe i hi).2
  · exact TM.transitionInput_eq_self hinp_read
  · exact TM.tape_writeAndMove_stable c.output hoh hons

/-- `.rewindFormula` base step: move right into `.rewindAssignment`. -/
private theorem verifyPairSplit_rewindFormula_base_step
    (c : Cfg 3 verifyPairTM.Q) (hst : c.state = .rewindFormula)
    (hread : (c.work ⟨0, by omega⟩).read = Γ.start)
    (hhead0 : (c.work ⟨0, by omega⟩).head = 0)
    (hih : c.input.head ≥ 1) (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hframe : ∀ i, i ≠ (⟨0, by omega⟩ : Fin 3) →
      (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.step c = some c' ∧ c'.state = .rewindAssignment ∧
      (c'.work ⟨0, by omega⟩).head = 1 ∧
      (c'.work ⟨0, by omega⟩).cells = (c.work ⟨0, by omega⟩).cells ∧
      (∀ i, i ≠ (⟨0, by omega⟩ : Fin 3) → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output := by
  have hinp_read : c.input.read ≠ Γ.start := by
    show c.input.cells c.input.head ≠ Γ.start; exact hins _ hih
  have hread2 : (c.work (0 : Fin 3)).read = Γ.start := hread
  have hhead2 : (c.work (0 : Fin 3)).head = 0 := hhead0
  let c' : Cfg 3 verifyPairTM.Q :=
    { state := .rewindAssignment
      input := c.input.move (TM.idleDir c.input.read)
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
          (if i = (⟨0, by omega⟩ : Fin 3) then Dir3.right else TM.idleDir (c.work i).read)
      output := c.output.writeAndMove (TM.readBackWrite c.output.read)
        (TM.idleDir c.output.read) }
  have hstep : verifyPairTM.step c = some c' := by
    simp [c', verifyPairTM, TM.step, verifyPairDelta, hst, hread2,
      verifyPairPreserveWork]
  refine ⟨c', hstep, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show ((c.work ⟨0, by omega⟩).writeAndMove (TM.readBackWrite
      (c.work ⟨0, by omega⟩).read).toΓ Dir3.right).head = _
    simp [Tape.writeAndMove, Tape.move, Tape.write_head, hhead2]
  · show ((c.work ⟨0, by omega⟩).writeAndMove (TM.readBackWrite
      (c.work ⟨0, by omega⟩).read).toΓ Dir3.right).cells = _
    rw [Tape.writeAndMove, Tape.move_cells]
    simp [Tape.write, hhead2]
  · intro i hi
    show (c.work i).writeAndMove _ _ = c.work i
    rw [ite_eq_right hi]
    exact TM.tape_writeAndMove_stable (c.work i) (hframe i hi).1 (hframe i hi).2
  · exact TM.transitionInput_eq_self hinp_read
  · exact TM.tape_writeAndMove_stable c.output hoh hons

/-- `.rewindAssignment` left step: move the assignment tape left. -/
private theorem verifyPairSplit_rewindAssignment_left_step
    (c : Cfg 3 verifyPairTM.Q) (hst : c.state = .rewindAssignment)
    (hread : (c.work ⟨1, by omega⟩).read ≠ Γ.start)
    (hih : c.input.head ≥ 1) (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hframe : ∀ i, i ≠ (⟨1, by omega⟩ : Fin 3) →
      (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.step c = some c' ∧ c'.state = .rewindAssignment ∧
      (c'.work ⟨1, by omega⟩).head = (c.work ⟨1, by omega⟩).head - 1 ∧
      (c'.work ⟨1, by omega⟩).cells = (c.work ⟨1, by omega⟩).cells ∧
      (∀ i, i ≠ (⟨1, by omega⟩ : Fin 3) → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output := by
  have hinp_read : c.input.read ≠ Γ.start := by
    show c.input.cells c.input.head ≠ Γ.start; exact hins _ hih
  have hread2 : (c.work (1 : Fin 3)).read ≠ Γ.start := hread
  let c' : Cfg 3 verifyPairTM.Q :=
    { state := .rewindAssignment
      input := c.input.move (TM.idleDir c.input.read)
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
          (if i = (⟨1, by omega⟩ : Fin 3) then Dir3.left else TM.idleDir (c.work i).read)
      output := c.output.writeAndMove (TM.readBackWrite c.output.read)
        (TM.idleDir c.output.read) }
  have hstep : verifyPairTM.step c = some c' := by
    simp [c', verifyPairTM, TM.step, verifyPairDelta, hst, hread2,
      verifyPairPreserveWork]
  refine ⟨c', hstep, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show ((c.work ⟨1, by omega⟩).writeAndMove (TM.readBackWrite
      (c.work ⟨1, by omega⟩).read).toΓ Dir3.left).head = _
    simp [Tape.writeAndMove, Tape.move, Tape.write_head]
  · show ((c.work ⟨1, by omega⟩).writeAndMove (TM.readBackWrite
      (c.work ⟨1, by omega⟩).read).toΓ Dir3.left).cells = _
    rw [Tape.writeAndMove, Tape.move_cells, TM.toΓ_readBackWrite_of_ne_start hread]
    simp [Tape.write, Tape.read, Function.update_eq_self]
  · intro i hi
    show (c.work i).writeAndMove _ _ = c.work i
    rw [ite_eq_right hi]
    exact TM.tape_writeAndMove_stable (c.work i) (hframe i hi).1 (hframe i hi).2
  · exact TM.transitionInput_eq_self hinp_read
  · exact TM.tape_writeAndMove_stable c.output hoh hons

/-- `.rewindAssignment` base step: move right into the evaluator's first read. -/
private theorem verifyPairSplit_rewindAssignment_base_step
    (c : Cfg 3 verifyPairTM.Q) (hst : c.state = .rewindAssignment)
    (hread : (c.work ⟨1, by omega⟩).read = Γ.start)
    (hhead0 : (c.work ⟨1, by omega⟩).head = 0)
    (hih : c.input.head ≥ 1) (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hframe : ∀ i, i ≠ (⟨1, by omega⟩ : Fin 3) →
      (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.step c = some c' ∧
      c'.state = .evalReadFirst (.boundary true false true) ∧
      (c'.work ⟨1, by omega⟩).head = 1 ∧
      (c'.work ⟨1, by omega⟩).cells = (c.work ⟨1, by omega⟩).cells ∧
      (∀ i, i ≠ (⟨1, by omega⟩ : Fin 3) → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output := by
  have hinp_read : c.input.read ≠ Γ.start := by
    show c.input.cells c.input.head ≠ Γ.start; exact hins _ hih
  have hread2 : (c.work (1 : Fin 3)).read = Γ.start := hread
  have hhead2 : (c.work (1 : Fin 3)).head = 0 := hhead0
  let c' : Cfg 3 verifyPairTM.Q :=
    { state := .evalReadFirst (.boundary true false true)
      input := c.input.move (TM.idleDir c.input.read)
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
          (if i = (⟨1, by omega⟩ : Fin 3) then Dir3.right else TM.idleDir (c.work i).read)
      output := c.output.writeAndMove (TM.readBackWrite c.output.read)
        (TM.idleDir c.output.read) }
  have hstep : verifyPairTM.step c = some c' := by
    simp [c', verifyPairTM, TM.step, verifyPairDelta, hst, hread2,
      verifyPairPreserveWork]
  refine ⟨c', hstep, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show ((c.work ⟨1, by omega⟩).writeAndMove (TM.readBackWrite
      (c.work ⟨1, by omega⟩).read).toΓ Dir3.right).head = _
    simp [Tape.writeAndMove, Tape.move, Tape.write_head, hhead2]
  · show ((c.work ⟨1, by omega⟩).writeAndMove (TM.readBackWrite
      (c.work ⟨1, by omega⟩).read).toΓ Dir3.right).cells = _
    rw [Tape.writeAndMove, Tape.move_cells]
    simp [Tape.write, hhead2]
  · intro i hi
    show (c.work i).writeAndMove _ _ = c.work i
    rw [ite_eq_right hi]
    exact TM.tape_writeAndMove_stable (c.work i) (hframe i hi).1 (hframe i hi).2
  · exact TM.transitionInput_eq_self hinp_read
  · exact TM.tape_writeAndMove_stable c.output hoh hons

/-- `.copyAlpha` bit step: with an assignment bit under the input head and a
live counter tally, copy the bit to the assignment tape `1`, erase one counter
tally on tape `2`, advance the input, and stay in `.copyAlpha`. This is the
witness-length check: the counter has `|z| + 1` tallies, so it runs dry exactly
when `|α| > |z| + 1`. -/
private theorem verifyPairSplit_copyAlpha_bit_step (b : Bool)
    (c : Cfg 3 verifyPairTM.Q) (hst : c.state = .copyAlpha)
    (hib : c.input.read = Γ.ofBool b)
    (hcounter : (c.work ⟨2, by omega⟩).read = Γ.one)
    (h0st : (c.work ⟨0, by omega⟩).head ≥ 1 ∧
      ∀ j, j ≥ 1 → (c.work ⟨0, by omega⟩).cells j ≠ Γ.start)
    (h1h : (c.work ⟨1, by omega⟩).head ≥ 1)
    (h2h : (c.work ⟨2, by omega⟩).head ≥ 1)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.step c = some c' ∧ c'.state = .copyAlpha ∧
      c'.input.head = c.input.head + 1 ∧ c'.input.cells = c.input.cells ∧
      c'.work ⟨0, by omega⟩ = c.work ⟨0, by omega⟩ ∧
      (c'.work ⟨1, by omega⟩).head = (c.work ⟨1, by omega⟩).head + 1 ∧
      (c'.work ⟨1, by omega⟩).cells =
        Function.update (c.work ⟨1, by omega⟩).cells (c.work ⟨1, by omega⟩).head (Γ.ofBool b) ∧
      (c'.work ⟨2, by omega⟩).head = (c.work ⟨2, by omega⟩).head + 1 ∧
      (c'.work ⟨2, by omega⟩).cells =
        Function.update (c.work ⟨2, by omega⟩).cells (c.work ⟨2, by omega⟩).head Γ.blank ∧
      c'.output = c.output := by
  have hib_blank : c.input.read ≠ Γ.blank := by rw [hib]; exact Γ.ofBool_ne_blank b
  have hcounter2 : (c.work (2 : Fin 3)).read = Γ.one := hcounter
  let c' : Cfg 3 verifyPairTM.Q :=
    { state := .copyAlpha
      input := c.input.move Dir3.right
      work := fun i =>
        (c.work i).writeAndMove (verifyPairCopyAlphaWrite b (fun j => (c.work j).read) i)
          (verifyPairCopyAlphaDirs (fun j => (c.work j).read) i)
      output := c.output.writeAndMove (TM.readBackWrite c.output.read)
        (TM.idleDir c.output.read) }
  have hstep : verifyPairTM.step c = some c' := by
    have hbit : readBit? c.input.read = some b := by rw [hib]; cases b <;> rfl
    simp [c', verifyPairTM, TM.step, verifyPairDelta, hst, hib_blank, hbit,
      hcounter2]
  refine ⟨c', hstep, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [c', Tape.move]
  · simpa using Tape.move_cells c.input Dir3.right
  · show (c.work ⟨0, by omega⟩).writeAndMove _ _ = c.work ⟨0, by omega⟩
    rw [show verifyPairCopyAlphaWrite b (fun j => (c.work j).read) ⟨0, by omega⟩ =
          TM.readBackWrite (c.work ⟨0, by omega⟩).read by simp [verifyPairCopyAlphaWrite],
      show verifyPairCopyAlphaDirs (fun j => (c.work j).read) ⟨0, by omega⟩ =
          TM.idleDir (c.work ⟨0, by omega⟩).read by simp [verifyPairCopyAlphaDirs]]
    exact TM.tape_writeAndMove_stable (c.work ⟨0, by omega⟩) h0st.1 h0st.2
  · show ((c.work ⟨1, by omega⟩).writeAndMove _ _).head = _
    simp [verifyPairCopyAlphaDirs, Tape.writeAndMove, Tape.move, Tape.write_head]
  · show ((c.work ⟨1, by omega⟩).writeAndMove _ _).cells = _
    have hne1 : (c.work ⟨1, by omega⟩).head ≠ 0 := by omega
    simp only [Tape.writeAndMove, Tape.move_cells, Tape.write, ite_eq_right hne1]
    cases b <;> simp [verifyPairCopyAlphaWrite, boolWrite, Γw.toΓ, Γ.ofBool]
  · show ((c.work ⟨2, by omega⟩).writeAndMove _ _).head = _
    simp [verifyPairCopyAlphaDirs, Tape.writeAndMove, Tape.move, Tape.write_head]
  · show ((c.work ⟨2, by omega⟩).writeAndMove _ _).cells = _
    have hne2 : (c.work ⟨2, by omega⟩).head ≠ 0 := by omega
    simp only [Tape.writeAndMove, Tape.move_cells, Tape.write, ite_eq_right hne2]
    simp [verifyPairCopyAlphaWrite, Γw.toΓ]
  · exact TM.tape_writeAndMove_stable c.output hoh hons

/-- `.copyAlpha` blank step: once the input head reaches the blank after `α`,
transition to `.rewindFormula`, leaving all work tapes and the output
unchanged. -/
private theorem verifyPairSplit_copyAlpha_blank_step
    (c : Cfg 3 verifyPairTM.Q) (hst : c.state = .copyAlpha)
    (hib : c.input.read = Γ.blank)
    (hwst : ∀ i, (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start)
    (_hih : c.input.head ≥ 1) (_hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.step c = some c' ∧ c'.state = .rewindFormula ∧
      c'.input = c.input ∧ c'.work = c.work ∧ c'.output = c.output := by
  have hinp_read : c.input.read ≠ Γ.start := by rw [hib]; decide
  let c' : Cfg 3 verifyPairTM.Q :=
    { state := .rewindFormula
      input := c.input.move (TM.idleDir c.input.read)
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
          (TM.idleDir (c.work i).read)
      output := c.output.writeAndMove (TM.readBackWrite c.output.read)
        (TM.idleDir c.output.read) }
  have hstep : verifyPairTM.step c = some c' := by
    simp [c', verifyPairTM, TM.step, verifyPairDelta, hst, hib,
      verifyPairPreserveWork]
  refine ⟨c', hstep, rfl, ?_, ?_, ?_⟩
  · exact TM.transitionInput_eq_self hinp_read
  · funext i
    exact TM.tape_writeAndMove_stable (c.work i) (hwst i).1 (hwst i).2
  · exact TM.tape_writeAndMove_stable c.output hoh hons

/-- The copyAlpha success loop. Given enough counter tallies ahead (cells
`head .. head + |as| - 1` all `Γ.one`), the machine copies the assignment bits
`as` from the input to tape `1`, erasing one counter tally per bit, and returns
to `.copyAlpha`. Tape `0` and the output are untouched; tape `2` stays stable
(its exact erased content is irrelevant downstream). -/
private theorem verifyPairSplit_copyAlpha_loop :
    ∀ (as : List Bool) (c : Cfg 3 verifyPairTM.Q),
      c.state = .copyAlpha →
      c.input.head ≥ 1 → c.input.cells 0 = Γ.start →
      (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
      (∀ i, (h : i < as.length) → c.input.cells (c.input.head + i) = Γ.ofBool (as[i]'h)) →
      (c.work ⟨0, by omega⟩).head ≥ 1 →
      (∀ j, j ≥ 1 → (c.work ⟨0, by omega⟩).cells j ≠ Γ.start) →
      (c.work ⟨1, by omega⟩).head ≥ 1 →
      (c.work ⟨1, by omega⟩).cells 0 = Γ.start →
      (∀ j, j ≥ 1 → (c.work ⟨1, by omega⟩).cells j ≠ Γ.start) →
      (c.work ⟨2, by omega⟩).head ≥ 1 →
      (c.work ⟨2, by omega⟩).cells 0 = Γ.start →
      (∀ j, j ≥ 1 → (c.work ⟨2, by omega⟩).cells j ≠ Γ.start) →
      (∀ i, i < as.length → (c.work ⟨2, by omega⟩).cells ((c.work ⟨2, by omega⟩).head + i)
        = Γ.one) →
      c.output.head ≥ 1 → (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
      ∃ c',
        verifyPairTM.reachesIn as.length c c' ∧
        c'.state = .copyAlpha ∧
        c'.input.head = c.input.head + as.length ∧
        c'.input.cells = c.input.cells ∧
        c'.work ⟨0, by omega⟩ = c.work ⟨0, by omega⟩ ∧
        (c'.work ⟨1, by omega⟩).head = (c.work ⟨1, by omega⟩).head + as.length ∧
        (c'.work ⟨1, by omega⟩).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (c'.work ⟨1, by omega⟩).cells j ≠ Γ.start) ∧
        (∀ j, j < (c.work ⟨1, by omega⟩).head →
            (c'.work ⟨1, by omega⟩).cells j = (c.work ⟨1, by omega⟩).cells j) ∧
        (∀ j, j ≥ (c.work ⟨1, by omega⟩).head + as.length →
            (c'.work ⟨1, by omega⟩).cells j = (c.work ⟨1, by omega⟩).cells j) ∧
        (∀ i, (h : i < as.length) →
            (c'.work ⟨1, by omega⟩).cells ((c.work ⟨1, by omega⟩).head + i) = Γ.ofBool (as[i]'h)) ∧
        (c'.work ⟨2, by omega⟩).head ≥ 1 ∧
        (c'.work ⟨2, by omega⟩).head = (c.work ⟨2, by omega⟩).head + as.length ∧
        (c'.work ⟨2, by omega⟩).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (c'.work ⟨2, by omega⟩).cells j ≠ Γ.start) ∧
        (∀ j, j ≥ (c.work ⟨2, by omega⟩).head + as.length →
            (c'.work ⟨2, by omega⟩).cells j = (c.work ⟨2, by omega⟩).cells j) ∧
        c'.output = c.output := by
  intro as
  induction as with
  | nil =>
      intro c hst _ _ _ _ _ _ h1h h1c0 h1ns h2h h2c0 h2ns _ _ _
      refine ⟨c, by simpa using (TM.reachesIn.zero (tm := verifyPairTM) (c := c)),
        hst, by simp, rfl, rfl, by simp, h1c0, h1ns, ?_, ?_, ?_, h2h, by simp, h2c0, h2ns,
        ?_, rfl⟩
      · intro j _; rfl
      · intro j _; rfl
      · intro i h; exact absurd h (by simp)
      · intro j _; rfl
  | cons a as ih =>
      intro c hst hih hic0 hins hdata h0h h0ns h1h h1c0 h1ns h2h h2c0 h2ns hcnt hoh hons
      have hib : c.input.read = Γ.ofBool a := by
        have := hdata 0 (by simp)
        simp only [Nat.add_zero] at this
        exact this
      have hcounter : (c.work ⟨2, by omega⟩).read = Γ.one := by
        have := hcnt 0 (by simp)
        simp only [Nat.add_zero] at this
        exact this
      obtain ⟨c1, hstep, hst1, hc1_ih, hc1_ic, hc1_0w, hc1_1h, hc1_1c, hc1_2h, hc1_2c, hc1_o⟩ :=
        verifyPairSplit_copyAlpha_bit_step a c hst hib hcounter ⟨h0h, h0ns⟩ h1h h2h hoh hons
      -- transfer input invariants to c1
      have h1c1_ih : c1.input.head ≥ 1 := by rw [hc1_ih]; omega
      have h1c1_ic0 : c1.input.cells 0 = Γ.start := by rw [hc1_ic]; exact hic0
      have h1c1_ins : ∀ j, j ≥ 1 → c1.input.cells j ≠ Γ.start := by
        intro j hj; rw [hc1_ic]; exact hins j hj
      have hc1_data : ∀ i, (h : i < as.length) →
          c1.input.cells (c1.input.head + i) = Γ.ofBool (as[i]'h) := by
        intro i hi
        have := hdata (i + 1) (by simpa using hi)
        rw [hc1_ic, hc1_ih,
          show c.input.head + 1 + i = c.input.head + (i + 1) from by ring]
        simpa using this
      -- tape0 stable for c1
      have h0h1 : (c1.work ⟨0, by omega⟩).head ≥ 1 := by rw [hc1_0w]; exact h0h
      have h0ns1 : ∀ j, j ≥ 1 → (c1.work ⟨0, by omega⟩).cells j ≠ Γ.start := by
        intro j hj; rw [hc1_0w]; exact h0ns j hj
      -- tape1 invariants for c1
      have h1h1 : (c1.work ⟨1, by omega⟩).head ≥ 1 := by rw [hc1_1h]; omega
      have h1c01 : (c1.work ⟨1, by omega⟩).cells 0 = Γ.start := by
        rw [hc1_1c, Function.update_of_ne (by omega)]; exact h1c0
      have h1ns1 : ∀ j, j ≥ 1 → (c1.work ⟨1, by omega⟩).cells j ≠ Γ.start := by
        intro j hj; rw [hc1_1c]
        by_cases hjx : j = (c.work ⟨1, by omega⟩).head
        · rw [hjx, Function.update_self]; cases a <;> decide
        · rw [Function.update_of_ne hjx]; exact h1ns j hj
      -- tape2 invariants for c1
      have h2h1 : (c1.work ⟨2, by omega⟩).head ≥ 1 := by rw [hc1_2h]; omega
      have h2c01 : (c1.work ⟨2, by omega⟩).cells 0 = Γ.start := by
        rw [hc1_2c, Function.update_of_ne (by omega)]; exact h2c0
      have h2ns1 : ∀ j, j ≥ 1 → (c1.work ⟨2, by omega⟩).cells j ≠ Γ.start := by
        intro j hj; rw [hc1_2c]
        by_cases hjx : j = (c.work ⟨2, by omega⟩).head
        · rw [hjx, Function.update_self]; decide
        · rw [Function.update_of_ne hjx]; exact h2ns j hj
      have hcnt1 : ∀ i, i < as.length →
          (c1.work ⟨2, by omega⟩).cells ((c1.work ⟨2, by omega⟩).head + i) = Γ.one := by
        intro i hi
        rw [hc1_2h, hc1_2c, Function.update_of_ne (by omega),
          show (c.work ⟨2, by omega⟩).head + 1 + i
            = (c.work ⟨2, by omega⟩).head + (i + 1) from by ring]
        exact hcnt (i + 1) (by simpa using hi)
      have hoh1 : c1.output.head ≥ 1 := by rw [hc1_o]; exact hoh
      have hons1 : ∀ j, j ≥ 1 → c1.output.cells j ≠ Γ.start := by
        intro j hj; rw [hc1_o]; exact hons j hj
      obtain ⟨c', hreach, hst', hc_ih, hc_ic, hc_0w, hc_1h, hc_1c0, hc_1ns, hc_1below,
          hc_1above, hc_1data, hc_2h, hc_2hexact, hc_2c0, hc_2ns, hc_2above, hc_o⟩ :=
        ih c1 hst1 h1c1_ih h1c1_ic0 h1c1_ins hc1_data h0h1 h0ns1 h1h1 h1c01 h1ns1
          h2h1 h2c01 h2ns1 hcnt1 hoh1 hons1
      have hreach_total : verifyPairTM.reachesIn (a :: as).length c c' := by
        have htot : verifyPairTM.reachesIn (1 + as.length) c c' :=
          TM.reachesIn_trans _ (.step hstep .zero) hreach
        have heq : (a :: as).length = 1 + as.length := by simp only [List.length_cons]; omega
        rw [heq]; exact htot
      refine ⟨c', hreach_total, hst', ?_, ?_, ?_, ?_, hc_1c0, hc_1ns, ?_, ?_, ?_,
        hc_2h, ?_, hc_2c0, hc_2ns, ?_, ?_⟩
      · rw [hc_ih, hc1_ih]; simp only [List.length_cons]; omega
      · rw [hc_ic, hc1_ic]
      · rw [hc_0w, hc1_0w]
      · rw [hc_1h, hc1_1h]; simp only [List.length_cons]; omega
      · intro j hj
        have hj1 : j < (c1.work ⟨1, by omega⟩).head := by rw [hc1_1h]; omega
        rw [hc_1below j hj1, hc1_1c, Function.update_of_ne (Nat.ne_of_lt hj)]
      · intro j hj
        have hj1 : j ≥ (c1.work ⟨1, by omega⟩).head + as.length := by
          rw [hc1_1h]; simp only [List.length_cons] at hj; omega
        rw [hc_1above j hj1, hc1_1c, Function.update_of_ne (by omega)]
      · intro i hi
        cases i with
        | zero =>
            have hj1 : (c.work ⟨1, by omega⟩).head < (c1.work ⟨1, by omega⟩).head := by
              rw [hc1_1h]; omega
            rw [show (c.work ⟨1, by omega⟩).head + 0 = (c.work ⟨1, by omega⟩).head from by omega,
              hc_1below _ hj1, hc1_1c, Function.update_self]
            rfl
        | succ i' =>
            have hi' : i' < as.length := by simpa using hi
            have hpos : (c.work ⟨1, by omega⟩).head + (i' + 1) =
                (c1.work ⟨1, by omega⟩).head + i' := by rw [hc1_1h]; omega
            rw [hpos, hc_1data i' hi']; rfl
      · rw [hc_2hexact, hc1_2h]; simp only [List.length_cons]; omega
      · intro j hj
        simp only [List.length_cons] at hj
        have hj1 : j ≥ (c1.work ⟨2, by omega⟩).head + as.length := by rw [hc1_2h]; omega
        rw [hc_2above j hj1, hc1_2c, Function.update_of_ne (by omega)]
      · rw [hc_o, hc1_o]

/-- The counter-rewind phase: from `.rewindCounterForAlpha` with the counter
head at `p`, reach `.copyAlpha` with the counter head back at `1` in `p + 1`
steps, preserving every tape's contents. -/
private theorem verifyPairSplit_rewindCounter_phase (p : ℕ) (c : Cfg 3 verifyPairTM.Q)
    (hst : c.state = .rewindCounterForAlpha)
    (hc0 : (c.work ⟨2, by omega⟩).cells 0 = Γ.start)
    (hns : ∀ j, j ≥ 1 → (c.work ⟨2, by omega⟩).cells j ≠ Γ.start)
    (hhead : (c.work ⟨2, by omega⟩).head = p)
    (hih : c.input.head ≥ 1) (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hframe : ∀ i, i ≠ (⟨2, by omega⟩ : Fin 3) →
      (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.reachesIn (p + 1) c c' ∧ c'.state = .copyAlpha ∧
      (c'.work ⟨2, by omega⟩).head = 1 ∧ (c'.work ⟨2, by omega⟩).cells
        = (c.work ⟨2, by omega⟩).cells ∧
      (∀ i, i ≠ (⟨2, by omega⟩ : Fin 3) → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output :=
  verifyPair_rewind_loop ⟨2, by omega⟩ .rewindCounterForAlpha .copyAlpha
    verifyPairSplit_rewindCounter_left_step verifyPairSplit_rewindCounter_base_step
    p c hst hc0 hns hhead hih hins hframe hoh hons

/-- The formula-rewind phase: from `.rewindFormula` with the formula head at
`p`, reach `.rewindAssignment` with the formula head back at `1`. -/
private theorem verifyPairSplit_rewindFormula_phase (p : ℕ) (c : Cfg 3 verifyPairTM.Q)
    (hst : c.state = .rewindFormula)
    (hc0 : (c.work ⟨0, by omega⟩).cells 0 = Γ.start)
    (hns : ∀ j, j ≥ 1 → (c.work ⟨0, by omega⟩).cells j ≠ Γ.start)
    (hhead : (c.work ⟨0, by omega⟩).head = p)
    (hih : c.input.head ≥ 1) (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hframe : ∀ i, i ≠ (⟨0, by omega⟩ : Fin 3) →
      (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.reachesIn (p + 1) c c' ∧ c'.state = .rewindAssignment ∧
      (c'.work ⟨0, by omega⟩).head = 1 ∧ (c'.work ⟨0, by omega⟩).cells
        = (c.work ⟨0, by omega⟩).cells ∧
      (∀ i, i ≠ (⟨0, by omega⟩ : Fin 3) → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output :=
  verifyPair_rewind_loop ⟨0, by omega⟩ .rewindFormula .rewindAssignment
    verifyPairSplit_rewindFormula_left_step verifyPairSplit_rewindFormula_base_step
    p c hst hc0 hns hhead hih hins hframe hoh hons

/-- The assignment-rewind phase: from `.rewindAssignment` with the assignment
head at `p`, reach the evaluator's first read with the assignment head back at
`1`. -/
private theorem verifyPairSplit_rewindAssignment_phase (p : ℕ) (c : Cfg 3 verifyPairTM.Q)
    (hst : c.state = .rewindAssignment)
    (hc0 : (c.work ⟨1, by omega⟩).cells 0 = Γ.start)
    (hns : ∀ j, j ≥ 1 → (c.work ⟨1, by omega⟩).cells j ≠ Γ.start)
    (hhead : (c.work ⟨1, by omega⟩).head = p)
    (hih : c.input.head ≥ 1) (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hframe : ∀ i, i ≠ (⟨1, by omega⟩ : Fin 3) →
      (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start)
    (hoh : c.output.head ≥ 1) (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) :
    ∃ c', verifyPairTM.reachesIn (p + 1) c c' ∧
      c'.state = .evalReadFirst (.boundary true false true) ∧
      (c'.work ⟨1, by omega⟩).head = 1 ∧ (c'.work ⟨1, by omega⟩).cells
        = (c.work ⟨1, by omega⟩).cells ∧
      (∀ i, i ≠ (⟨1, by omega⟩ : Fin 3) → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output :=
  verifyPair_rewind_loop ⟨1, by omega⟩ .rewindAssignment (.evalReadFirst (.boundary true false
    true))
    verifyPairSplit_rewindAssignment_left_step verifyPairSplit_rewindAssignment_base_step
    p c hst hc0 hns hhead hih hins hframe hoh hons

/-- `.copyAlpha` reject step: an assignment bit with the counter already
exhausted (`≠ Γ.one`) means `|α| > |z| + 1`; the machine halts with output `0`. -/
private theorem verifyPairSplit_copyAlpha_reject_step (b : Bool)
    (c : Cfg 3 verifyPairTM.Q) (hst : c.state = .copyAlpha)
    (hib : c.input.read = Γ.ofBool b)
    (hcounter : (c.work ⟨2, by omega⟩).read ≠ Γ.one)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', verifyPairTM.step c = some c' ∧ verifyPairTM.halted c' ∧
      c'.output.cells 1 = Γ.zero := by
  have hib_blank : c.input.read ≠ Γ.blank := by rw [hib]; exact Γ.ofBool_ne_blank b
  have hcounter2 : (c.work (2 : Fin 3)).read ≠ Γ.one := hcounter
  let c' : Cfg 3 verifyPairTM.Q :=
    { state := .done
      input := c.input.move (TM.idleDir c.input.read)
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
          (TM.idleDir (c.work i).read)
      output := c.output.writeAndMove Γw.zero (TM.idleDir c.output.read) }
  have hstep : verifyPairTM.step c = some c' := by
    have hbit : readBit? c.input.read = some b := by rw [hib]; cases b <;> rfl
    simp [c', verifyPairTM, TM.step, verifyPairDelta, hst, hib_blank, hbit,
      hcounter2, verifyPairReject]
  refine ⟨c', hstep, rfl, ?_⟩
  show (c.output.writeAndMove Γw.zero (TM.idleDir c.output.read)).cells 1 = Γ.zero
  rw [hout]
  simp [Tape.writeAndMove, Tape.write, Tape.move, TM.idleDir, Tape.read,
    Tape.init, Γw.toΓ]

/-- The input tape after the initial `▷→cell 1` shift exposes the doubled bits
of `z` at the positions the split loop reads them. -/
private theorem verifyPair_input_doubled (z α : List Bool) (i : ℕ) (hi : i < z.length) :
    ((Tape.init ((pair z α).map Γ.ofBool)).move Dir3.right).cells (1 + 2 * i) =
        Γ.ofBool (z[i]'hi) ∧
    ((Tape.init ((pair z α).map Γ.ofBool)).move Dir3.right).cells (1 + (2 * i + 1)) =
        Γ.ofBool (z[i]'hi) := by
  have hlen2 : 2 * i < (pair z α).length := by rw [pair_length]; omega
  have hlen2' : 2 * i + 1 < (pair z α).length := by rw [pair_length]; omega
  refine ⟨?_, ?_⟩
  · rw [Tape.move_cells, show 1 + 2 * i = 2 * i + 1 from by ring,
      Tape.init_ofBool_cells_lt (pair z α) (2 * i) hlen2, pair_getElem_left_first z α i hi]
  · rw [Tape.move_cells, show 1 + (2 * i + 1) = (2 * i + 1) + 1 from by ring,
      Tape.init_ofBool_cells_lt (pair z α) (2 * i + 1) hlen2', pair_getElem_left_second z α i hi]

/-- From the initial configuration on `pair z α`, the machine runs the init,
formula-scan, and separator phases, reaching `.rewindCounterForAlpha` with the
formula `z` staged on tape `0`, the `|z|+1`-tally counter on tape `2`, the
assignment tape `1` still blank, and the input head positioned at the start of
`α`'s region. -/
private theorem verifyPairSplit_setup_through_separator (z α : List Bool) :
    ∃ c', verifyPairTM.reachesIn (2 * z.length + 4) (verifyPairTM.initCfg (pair z α)) c' ∧
      c'.state = .rewindCounterForAlpha ∧
      c'.input.head = 2 * z.length + 3 ∧
      c'.input.cells = ((Tape.init ((pair z α).map Γ.ofBool)).move Dir3.right).cells ∧
      (c'.work ⟨0, by omega⟩).head = 1 + z.length ∧
      (c'.work ⟨0, by omega⟩).cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → (c'.work ⟨0, by omega⟩).cells j ≠ Γ.start) ∧
      (∀ i, (h : i < z.length) → (c'.work ⟨0, by omega⟩).cells (1 + i) = Γ.ofBool (z[i]'h)) ∧
      (∀ j, j ≥ 1 + z.length → (c'.work ⟨0, by omega⟩).cells j = Γ.blank) ∧
      c'.work ⟨1, by omega⟩ = (Tape.init []).move Dir3.right ∧
      (c'.work ⟨2, by omega⟩).head = z.length + 2 ∧
      (c'.work ⟨2, by omega⟩).cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → (c'.work ⟨2, by omega⟩).cells j ≠ Γ.start) ∧
      (∀ i, i < z.length + 1 → (c'.work ⟨2, by omega⟩).cells (1 + i) = Γ.one) ∧
      (∀ j, j ≥ z.length + 2 → (c'.work ⟨2, by omega⟩).cells j = Γ.blank) ∧
      c'.output = (Tape.init []).move Dir3.right := by
  -- Phase 0: init (2 steps → .splitScan)
  obtain ⟨c1, hr1, hs1, hi1, hw01, hw11, hu2, hc2start, ho1⟩ :=
    verifyPairTM_init_steps (pair z α)
  -- Unpack the counter's `HasUnaryPrefix 1`
  obtain ⟨hu2h, hu2one, hu2blank⟩ := hu2
  -- input/work/output stability facts for c1
  have hi1_head : c1.input.head = 1 := by rw [hi1]; simp [Tape.move, Tape.init]
  have hi1_cells0 : c1.input.cells 0 = Γ.start := by
    rw [hi1]; simp [Tape.move, Tape.init]
  have hi1_ns : ∀ j, j ≥ 1 → c1.input.cells j ≠ Γ.start := by
    intro j hj; rw [hi1, Tape.move_cells]
    exact Tape.init_ofBool_cells_ne_start (pair z α) j hj
  have hw01_head : (c1.work ⟨0, by omega⟩).head = 1 := by
    rw [hw01]; simp [Tape.move, Tape.init]
  have hw01_cells0 : (c1.work ⟨0, by omega⟩).cells 0 = Γ.start := by
    rw [hw01]; simp [Tape.move, Tape.init]
  have hw01_ns : ∀ j, j ≥ 1 → (c1.work ⟨0, by omega⟩).cells j ≠ Γ.start := by
    intro j hj; rw [hw01, Tape.move_cells]
    cases j with
    | zero => omega
    | succ k => simp [Tape.init]
  have hw11_head : (c1.work ⟨1, by omega⟩).head = 1 := by
    rw [hw11]; simp [Tape.move, Tape.init]
  have hw11_ns : ∀ j, j ≥ 1 → (c1.work ⟨1, by omega⟩).cells j ≠ Γ.start := by
    intro j hj; rw [hw11, Tape.move_cells]
    cases j with
    | zero => omega
    | succ k => simp [Tape.init]
  have hw21_ns : ∀ j, j ≥ 1 → (c1.work ⟨2, by omega⟩).cells j ≠ Γ.start := by
    intro j hj
    cases j with
    | zero => omega
    | succ k =>
        by_cases hk : k < 1
        · have : k = 0 := by omega
          subst this; rw [hu2one 0 (by omega)]; decide
        · rw [hu2blank k (by omega)]; decide
  have ho1_head : c1.output.head = 1 := by rw [ho1]; simp [Tape.move, Tape.init]
  have ho1_ns : ∀ j, j ≥ 1 → c1.output.cells j ≠ Γ.start := by
    intro j hj; rw [ho1, Tape.move_cells]
    cases j with
    | zero => omega
    | succ k => simp [Tape.init]
  -- doubled-bit hypothesis for scanX
  have hdoubled : ∀ i, (h : i < z.length) →
      c1.input.cells (c1.input.head + 2 * i) = Γ.ofBool (z[i]'h) ∧
      c1.input.cells (c1.input.head + (2 * i + 1)) = Γ.ofBool (z[i]'h) := by
    intro i hi
    rw [hi1_head, hi1]
    exact verifyPair_input_doubled z α i hi
  -- Phase 1: scanX (2*|z| steps → .splitScan, formula on tape 0, tallies on tape 2)
  obtain ⟨c2, hr2, hs2, hi2h, hi2c, hw02h, hw02c0, hw02ns, hw02below, hw02above,
      hw02data, hw12, hw22h, hw22c0, hw22ns, hw22below, hw22above, hw22data, ho2⟩ :=
    verifyPairSplit_scanX_loop z c1 hs1 hi1_head.ge hi1_cells0 hi1_ns hdoubled
      hw01_head.ge hw01_cells0 hw01_ns hw11_head.ge hw11_ns
      (by rw [hu2h]; omega) hc2start hw21_ns ho1_head.ge ho1_ns
  -- separator read values
  have hc1_sep0 : c1.input.cells (1 + 2 * z.length) = Γ.zero := by
    rw [hi1, Tape.move_cells, show 1 + 2 * z.length = 2 * z.length + 1 from by ring,
      Tape.init_ofBool_cells_lt (pair z α) (2 * z.length) (by rw [pair_length]; omega),
      pair_getElem_sep_zero z α]; rfl
  have hc1_sep1 : c1.input.cells (1 + 2 * z.length + 1) = Γ.one := by
    rw [hi1, Tape.move_cells,
      show 1 + 2 * z.length + 1 = (2 * z.length + 1) + 1 from by ring,
      Tape.init_ofBool_cells_lt (pair z α) (2 * z.length + 1) (by rw [pair_length]; omega),
      pair_getElem_sep_one z α]; rfl
  have hsep0 : c2.input.read = Γ.zero := by
    show c2.input.cells c2.input.head = Γ.zero
    rw [hi2c, hi2h, hi1_head]; exact hc1_sep0
  have hsep1 : c2.input.cells (c2.input.head + 1) = Γ.one := by
    rw [hi2c, hi2h, hi1_head]; exact hc1_sep1
  have hwst2 : ∀ i, (c2.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c2.work i).cells j ≠ Γ.start := by
    intro i
    match i with
    | ⟨0, _⟩ => exact ⟨by rw [hw02h]; omega, hw02ns⟩
    | ⟨1, _⟩ => exact ⟨by rw [hw12]; exact hw11_head.ge, by rw [hw12]; exact hw11_ns⟩
    | ⟨2, _⟩ => exact ⟨by rw [hw22h]; omega, hw22ns⟩
  -- Phase 2: separator (2 steps → .rewindCounterForAlpha)
  obtain ⟨c3, hr3, hs3, hi3h, hi3c, hw3, ho3⟩ :=
    verifyPairSplit_separator_step c2 hs2 hsep0 hsep1 hwst2
      (by rw [ho2]; exact ho1_head.ge) (by rw [ho2]; exact ho1_ns)
  refine ⟨c3, ?_, hs3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : verifyPairTM.reachesIn (2 + (2 * z.length + 2)) (verifyPairTM.initCfg (pair z α)) c3 :=
      TM.reachesIn_trans _ hr1 (TM.reachesIn_trans _ hr2 hr3)
    rwa [show 2 * z.length + 4 = 2 + (2 * z.length + 2) from by omega]
  · rw [hi3h, hi2h, hi1_head]; omega
  · rw [hi3c, hi2c, hi1]
  · rw [hw3, hw02h, hw01_head]
  · rw [hw3]; exact hw02c0
  · rw [hw3]; exact hw02ns
  · intro i h
    rw [hw3]
    have := hw02data i h; rw [hw01_head] at this; exact this
  · intro j hj
    rw [hw3]
    have hab := hw02above j (by rw [hw01_head]; omega)
    rw [hab, hw01, Tape.move_cells]
    cases j with
    | zero => omega
    | succ k => simp [Tape.init]
  · rw [hw3, hw12, hw11]
  · rw [hw3, hw22h, hu2h]; omega
  · rw [hw3]; exact hw22c0
  · rw [hw3]; exact hw22ns
  · intro i hi
    rw [hw3]
    cases i with
    | zero =>
        have hb := hw22below 1 (by rw [hu2h]; omega)
        rw [show (1 : ℕ) + 0 = 1 from rfl, hb]
        exact hu2one 0 (by omega)
    | succ i' =>
        have hi'' : i' < z.length := by omega
        have hd := hw22data i' hi''
        rw [hu2h] at hd
        rw [show 1 + (i' + 1) = 1 + 1 + i' from by ring]; exact hd
  · intro j hj
    rw [hw3]
    have hab := hw22above j (by rw [hu2h]; omega)
    rw [hab]
    cases j with
    | zero => omega
    | succ k => exact hu2blank k (by omega)
  · rw [ho3, ho2]; exact ho1

/-- A tape pinned down by its cell contents (left marker, `l`'s bits, then
blanks) with head at cell `1` is exactly `Tape.init (l.map Γ.ofBool)` shifted
right — the canonical "started binary input" shape consumed by the evaluator. -/
private theorem tape_eq_initTape_of_cells (t : Tape) (l : List Bool)
    (hh : t.head = 1) (h0 : t.cells 0 = Γ.start)
    (hdata : ∀ i, (h : i < l.length) → t.cells (1 + i) = Γ.ofBool (l[i]'h))
    (hblank : ∀ j, j ≥ 1 + l.length → t.cells j = Γ.blank) :
    t = (Tape.init (l.map Γ.ofBool)).move Dir3.right := by
  have hc2 : t.cells = ((Tape.init (l.map Γ.ofBool)).move Dir3.right).cells := by
    funext j
    rw [Tape.move_cells]
    cases j with
    | zero => rw [h0]; simp [Tape.init]
    | succ k =>
        by_cases hk : k < l.length
        · rw [Tape.init_ofBool_cells_lt l k hk]
          have hd := hdata k hk
          rwa [show (1 : ℕ) + k = k + 1 from by ring] at hd
        · rw [Tape.init_ofBool_cells_ge l k (by omega)]
          exact hblank (k + 1) (by omega)
  have hh2 : t.head = ((Tape.init (l.map Γ.ofBool)).move Dir3.right).head := by
    rw [hh]; simp [Tape.move, Tape.init]
  calc t = ⟨t.head, t.cells⟩ := rfl
    _ = ⟨((Tape.init (l.map Γ.ofBool)).move Dir3.right).head,
          ((Tape.init (l.map Γ.ofBool)).move Dir3.right).cells⟩ := by rw [hh2, hc2]
    _ = (Tape.init (l.map Γ.ofBool)).move Dir3.right := rfl

/-- **Setup success path.** When `|α| ≤ |z| + 1`, the full split/setup pipeline
runs from the initial configuration on `pair z α` to the evaluator's first read,
leaving the formula `z` staged on tape `0` and the assignment `α` on tape `1`,
both as left-anchored binary tapes with head at cell `1`. -/
private theorem verifyPairSplit_setup_success (z α : List Bool)
    (hlen : α.length ≤ z.length + 1) :
    ∃ c', verifyPairTM.reachesIn (4 * z.length + 2 * α.length + 12)
        (verifyPairTM.initCfg (pair z α)) c' ∧
      c'.state = .evalReadFirst (.boundary true false true) ∧
      (c'.work ⟨0, by omega⟩).head = 1 ∧ (c'.work ⟨0, by omega⟩).cells 0 = Γ.start ∧
      (∀ i, (h : i < z.length) → (c'.work ⟨0, by omega⟩).cells (1 + i) = Γ.ofBool (z[i]'h)) ∧
      (∀ j, j ≥ 1 + z.length → (c'.work ⟨0, by omega⟩).cells j = Γ.blank) ∧
      (c'.work ⟨1, by omega⟩).head = 1 ∧ (c'.work ⟨1, by omega⟩).cells 0 = Γ.start ∧
      (∀ i, (h : i < α.length) → (c'.work ⟨1, by omega⟩).cells (1 + i) = Γ.ofBool (α[i]'h)) ∧
      (∀ j, j ≥ 1 + α.length → (c'.work ⟨1, by omega⟩).cells j = Γ.blank) ∧
      c'.output = (Tape.init []).move Dir3.right := by
  obtain ⟨c3, hr3, hs3, hi3h, hi3c, hw30h, hw30c0, hw30ns, hw30data, hw30blank, hw31,
      hw32h, hw32c0, hw32ns, hw32tally, _hw32blank, ho3⟩ :=
    verifyPairSplit_setup_through_separator z α
  -- input invariants common to the remaining phases
  have hi3c0 : c3.input.cells 0 = Γ.start := by rw [hi3c]; simp [Tape.move, Tape.init]
  have hi3ns : ∀ j, j ≥ 1 → c3.input.cells j ≠ Γ.start := by
    intro j hj; rw [hi3c, Tape.move_cells]
    exact Tape.init_ofBool_cells_ne_start (pair z α) j hj
  -- tape-1 (blank) stability facts
  have hw31h : (c3.work ⟨1, by omega⟩).head = 1 := by rw [hw31]; simp [Tape.move, Tape.init]
  have hw31c0 : (c3.work ⟨1, by omega⟩).cells 0 = Γ.start := by
    rw [hw31]; simp [Tape.move, Tape.init]
  have hw31ns : ∀ j, j ≥ 1 → (c3.work ⟨1, by omega⟩).cells j ≠ Γ.start := by
    intro j hj; rw [hw31, Tape.move_cells]
    cases j with | zero => omega | succ k => simp [Tape.init]
  have hframe3 : ∀ i, i ≠ (⟨2, by omega⟩ : Fin 3) →
      (c3.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c3.work i).cells j ≠ Γ.start := by
    intro i hi
    match i with
    | ⟨0, _⟩ => exact ⟨by rw [hw30h]; omega, hw30ns⟩
    | ⟨1, _⟩ => exact ⟨by rw [hw31h], hw31ns⟩
    | ⟨2, _⟩ => exact absurd rfl hi
  have hi3h1 : c3.input.head ≥ 1 := by omega
  -- Phase 3: rewind the counter (head |z|+2 → 1)
  obtain ⟨c4, hr4, hs4, hw42h, hw42c, hw4frame, hi4, ho4⟩ :=
    verifyPairSplit_rewindCounter_phase (z.length + 2) c3 hs3 hw32c0 hw32ns hw32h
      hi3h1 hi3ns hframe3 (by rw [ho3]; simp [Tape.move, Tape.init])
      (by rw [ho3]; intro j hj; rw [Tape.move_cells];
          cases j with | zero => omega | succ k => simp [Tape.init])
  have hw40 : c4.work ⟨0, by omega⟩ = c3.work ⟨0, by omega⟩ := hw4frame ⟨0, by omega⟩ (by simp)
  have hw41 : c4.work ⟨1, by omega⟩ = c3.work ⟨1, by omega⟩ := hw4frame ⟨1, by omega⟩ (by simp)
  have hc4ih : c4.input.head = 2 * z.length + 3 := by rw [hi4, hi3h]
  have hc4w0h : (c4.work ⟨0, by omega⟩).head = 1 + z.length := by rw [hw40, hw30h]
  have hc4w1h : (c4.work ⟨1, by omega⟩).head = 1 := by rw [hw41, hw31h]
  -- α-bit input data and the blank after α
  have halpha : ∀ j, (h : j < α.length) →
      c4.input.cells (c4.input.head + j) = Γ.ofBool (α[j]'h) := by
    intro j h
    rw [hi4, hi3h, hi3c, Tape.move_cells,
      show 2 * z.length + 3 + j = (2 * z.length + 2 + j) + 1 from by ring,
      Tape.init_ofBool_cells_lt (pair z α) (2 * z.length + 2 + j) (by rw [pair_length]; omega),
      pair_getElem_right z α j h]
  have hcnt4 : ∀ i, i < α.length →
      (c4.work ⟨2, by omega⟩).cells ((c4.work ⟨2, by omega⟩).head + i) = Γ.one := by
    intro i hi; rw [hw42h, hw42c]; exact hw32tally i (by omega)
  -- Phase 4: copy α onto tape 1, consuming counter tallies (|α| steps)
  obtain ⟨c5, hr5, hs5, hi5h, hi5c, hw50, hw51h, hw51c0, hw51ns, hw51below, hw51above,
      hw51data, hw52h, _hw52hexact, hw52c0, hw52ns, _hw52above, ho5⟩ :=
    verifyPairSplit_copyAlpha_loop α c4 hs4 (by rw [hi4]; exact hi3h1)
      (by rw [hi4]; exact hi3c0) (by rw [hi4]; exact hi3ns) halpha
      (by rw [hc4w0h]; omega) (by rw [hw40]; exact hw30ns)
      hc4w1h.ge (by rw [hw41]; exact hw31c0) (by rw [hw41]; exact hw31ns)
      hw42h.ge (by rw [hw42c]; exact hw32c0) (by rw [hw42c]; exact hw32ns)
      hcnt4 (by rw [ho4, ho3]; simp [Tape.move, Tape.init])
      (by rw [ho4, ho3]; intro j hj; rw [Tape.move_cells];
          cases j with | zero => omega | succ k => simp [Tape.init])
  have hc5w1h : (c5.work ⟨1, by omega⟩).head = 1 + α.length := by rw [hw51h, hc4w1h]
  -- after copyAlpha, the input head sits on the blank past α
  have hi5read : c5.input.read = Γ.blank := by
    show c5.input.cells c5.input.head = Γ.blank
    rw [hi5c, hi5h, hc4ih, hi4, hi3c, Tape.move_cells,
      show 2 * z.length + 3 + α.length = (2 * z.length + 2 + α.length) + 1 from by ring]
    exact Tape.init_ofBool_cells_ge (pair z α) (2 * z.length + 2 + α.length) (by rw [pair_length])
  have hwst5 : ∀ i, (c5.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c5.work i).cells j ≠ Γ.start := by
    intro i
    match i with
    | ⟨0, _⟩ => exact ⟨by rw [hw50, hw40, hw30h]; omega, by rw [hw50, hw40]; exact hw30ns⟩
    | ⟨1, _⟩ => exact ⟨by rw [hc5w1h]; omega, hw51ns⟩
    | ⟨2, _⟩ => exact ⟨hw52h, hw52ns⟩
  -- Phase 5: detect end of α, transition to rewinding the formula
  obtain ⟨c6, hr6, hs6, hi6, hw6, ho6⟩ :=
    verifyPairSplit_copyAlpha_blank_step c5 hs5 hi5read hwst5
      (by rw [hi5h, hc4ih]; omega)
      (by rw [hi5c, hi4, hi3c]; intro j hj; rw [Tape.move_cells];
          exact Tape.init_ofBool_cells_ne_start (pair z α) j hj)
      (by rw [ho5, ho4, ho3]; simp [Tape.move, Tape.init])
      (by rw [ho5, ho4, ho3]; intro j hj; rw [Tape.move_cells];
          cases j with | zero => omega | succ k => simp [Tape.init])
  -- tape-0/tape-1 facts at c6
  have hw60h : (c6.work ⟨0, by omega⟩).head = 1 + z.length := by
    rw [hw6, hw50, hw40, hw30h]
  have hw60c0 : (c6.work ⟨0, by omega⟩).cells 0 = Γ.start := by rw [hw6, hw50, hw40]; exact hw30c0
  have hw60ns : ∀ j, j ≥ 1 → (c6.work ⟨0, by omega⟩).cells j ≠ Γ.start := by
    rw [hw6, hw50, hw40]; exact hw30ns
  have hw61h : (c6.work ⟨1, by omega⟩).head = 1 + α.length := by rw [hw6, hc5w1h]
  have hw61c0 : (c6.work ⟨1, by omega⟩).cells 0 = Γ.start := by rw [hw6]; exact hw51c0
  have hw61ns : ∀ j, j ≥ 1 → (c6.work ⟨1, by omega⟩).cells j ≠ Γ.start := by
    rw [hw6]; exact hw51ns
  have hframe6F : ∀ i, i ≠ (⟨0, by omega⟩ : Fin 3) →
      (c6.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c6.work i).cells j ≠ Γ.start := by
    intro i hi
    match i with
    | ⟨0, _⟩ => exact absurd rfl hi
    | ⟨1, _⟩ => exact ⟨by rw [hw61h]; omega, hw61ns⟩
    | ⟨2, _⟩ => exact ⟨by rw [hw6]; exact hw52h, by rw [hw6]; exact hw52ns⟩
  have hi6ns : ∀ j, j ≥ 1 → c6.input.cells j ≠ Γ.start := by
    rw [hi6, hi5c, hi4, hi3c]; intro j hj; rw [Tape.move_cells]
    exact Tape.init_ofBool_cells_ne_start (pair z α) j hj
  have ho6' : c6.output = (Tape.init []).move Dir3.right := by rw [ho6, ho5, ho4, ho3]
  -- Phase 6: rewind the formula (head 1+|z| → 1)
  obtain ⟨c7, hr7, hs7, hw70h, hw70c, hw7frame, hi7, ho7⟩ :=
    verifyPairSplit_rewindFormula_phase (1 + z.length) c6 hs6 hw60c0 hw60ns hw60h
      (by rw [hi6, hi5h, hc4ih]; omega) hi6ns hframe6F
      (by rw [ho6']; simp [Tape.move, Tape.init])
      (by rw [ho6']; intro j hj; rw [Tape.move_cells];
          cases j with | zero => omega | succ k => simp [Tape.init])
  have hw71 : c7.work ⟨1, by omega⟩ = c6.work ⟨1, by omega⟩ := hw7frame ⟨1, by omega⟩ (by simp)
  have hw72h : (c7.work ⟨2, by omega⟩).head ≥ 1 := by
    rw [hw7frame ⟨2, by omega⟩ (by simp), hw6]; exact hw52h
  have hw72ns : ∀ j, j ≥ 1 → (c7.work ⟨2, by omega⟩).cells j ≠ Γ.start := by
    rw [hw7frame ⟨2, by omega⟩ (by simp), hw6]; exact hw52ns
  have hframe7A : ∀ i, i ≠ (⟨1, by omega⟩ : Fin 3) →
      (c7.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c7.work i).cells j ≠ Γ.start := by
    intro i hi
    match i with
    | ⟨0, _⟩ => exact ⟨hw70h.ge, by rw [hw70c]; exact hw60ns⟩
    | ⟨1, _⟩ => exact absurd rfl hi
    | ⟨2, _⟩ => exact ⟨hw72h, hw72ns⟩
  have hi7ns : ∀ j, j ≥ 1 → c7.input.cells j ≠ Γ.start := by rw [hi7]; exact hi6ns
  have ho7' : c7.output = (Tape.init []).move Dir3.right := by rw [ho7]; exact ho6'
  -- Phase 7: rewind the assignment (head 1+|α| → 1) into the evaluator
  obtain ⟨c8, hr8, hs8, hw81h, hw81c, hw8frame, hi8, ho8⟩ :=
    verifyPairSplit_rewindAssignment_phase (1 + α.length) c7
      hs7 (by rw [hw71]; exact hw61c0) (by rw [hw71]; exact hw61ns) (by rw [hw71]; exact hw61h)
      (by rw [hi7, hi6, hi5h, hc4ih]; omega) hi7ns hframe7A
      (by rw [ho7']; simp [Tape.move, Tape.init])
      (by rw [ho7']; intro j hj; rw [Tape.move_cells];
          cases j with | zero => omega | succ k => simp [Tape.init])
  have hw80 : c8.work ⟨0, by omega⟩ = c7.work ⟨0, by omega⟩ := hw8frame ⟨0, by omega⟩ (by simp)
  -- Assemble
  refine ⟨c8, ?_, hs8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hchain : verifyPairTM.reachesIn
        ((2 * z.length + 4) + ((z.length + 2 + 1) + (α.length + (1 +
          ((1 + z.length + 1) + (1 + α.length + 1)))))) (verifyPairTM.initCfg (pair z α)) c8 :=
      TM.reachesIn_trans _ hr3 (TM.reachesIn_trans _ hr4
        (TM.reachesIn_trans _ hr5 (TM.reachesIn_trans _ (.step hr6 .zero)
          (TM.reachesIn_trans _ hr7 hr8))))
    rwa [show 4 * z.length + 2 * α.length + 12 =
      (2 * z.length + 4) + ((z.length + 2 + 1) + (α.length + (1 +
        ((1 + z.length + 1) + (1 + α.length + 1))))) from by omega]
  · rw [hw80, hw70h]
  · rw [hw80, hw70c]; exact hw60c0
  · intro i h
    rw [hw80, hw70c, hw6, hw50, hw40]
    exact hw30data i h
  · intro j hj
    rw [hw80, hw70c, hw6, hw50, hw40]
    exact hw30blank j hj
  · rw [hw81h]
  · rw [hw81c, hw71]; exact hw61c0
  · intro i h
    rw [hw81c, hw71, hw6]
    have := hw51data i h; rw [hc4w1h] at this; exact this
  · intro j hj
    rw [hw81c, hw71, hw6]
    have hab := hw51above j (by rw [hc4w1h]; omega)
    rw [hab, hw41, hw31, Tape.move_cells]
    cases j with | zero => omega | succ k => simp [Tape.init]
  · rw [ho8]; exact ho7'

/-- The setup success path, with the staged formula and assignment tapes
repackaged in the exact `Tape.init`-shifted shape consumed by the evaluator. -/
private theorem verifyPairSplit_setup_success_initTape (z α : List Bool)
    (hlen : α.length ≤ z.length + 1) :
    ∃ c', verifyPairTM.reachesIn (4 * z.length + 2 * α.length + 12)
        (verifyPairTM.initCfg (pair z α)) c' ∧
      c'.state = .evalReadFirst (.boundary true false true) ∧
      c'.work ⟨0, by omega⟩ = (Tape.init (z.map Γ.ofBool)).move Dir3.right ∧
      c'.work ⟨1, by omega⟩ = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
      c'.output = (Tape.init []).move Dir3.right := by
  obtain ⟨c', hr, hs, h0h, h0c0, h0data, h0blank, h1h, h1c0, h1data, h1blank, ho⟩ :=
    verifyPairSplit_setup_success z α hlen
  exact ⟨c', hr, hs,
    tape_eq_initTape_of_cells _ z h0h h0c0 h0data h0blank,
    tape_eq_initTape_of_cells _ α h1h h1c0 h1data h1blank, ho⟩

/-- Coarse polynomial budget for `verifyPairTM`. The split/length prefix is
linear, and the staged evaluator is quadratic in the input length because each
literal may rewind the assignment tape. -/
def verifyPairTMTime (n : ℕ) : ℕ :=
  (n + 3) * (n + 3) + 6 * n + 20

/-- The verifier's time budget `verifyPairTMTime` is `O(n²)`. -/
theorem verifyPairTMTime_bigO_quadratic :
    Complexity.BigO verifyPairTMTime ((· ^ 2) : ℕ → ℕ) := by
  unfold Complexity.BigO
  apply Asymptotics.IsBigO.of_bound 50
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  simp only [Real.norm_natCast]
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hcalc : ((verifyPairTMTime n : ℕ) : ℝ) ≤ 50 * ((n ^ 2 : ℕ) : ℝ) := by
    simp [verifyPairTMTime]
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  exact hcalc

/-- The verifier's time budget is polynomially bounded (witnessed by
degree `2`), the form needed for polynomial-time verifier packaging. -/
theorem verifyPairTMTime_polynomial :
    ∃ d : ℕ, Complexity.BigO verifyPairTMTime ((· ^ d) : ℕ → ℕ) :=
  ⟨2, verifyPairTMTime_bigO_quadratic⟩

-- ════════════════════════════════════════════════════════════════════════
-- Lemma B (eval projection) + combine: `verifyPairTM` decides `pairLang Witness`
-- ════════════════════════════════════════════════════════════════════════

/-- Predicate isolating the three evaluator-phase states of `verifyPairTM`. -/
private def isEvalState : VerifyPairPhase → Prop
  | .evalReadFirst _ => True
  | .evalReadSecond _ _ => True
  | .evalRewindAlpha _ => True
  | _ => False

/-- The projection only sends `.done` (among eval-or-done states) to the
evaluator's halt state, so a halted projection forces a halted verifier. -/
private theorem state_done_of_isEvalOrDone {s : VerifyPairPhase}
    (h : isEvalState s ∨ s = .done) (hd : projEvalState s = .done) : s = .done := by
  cases s <;> simp_all [isEvalState, projEvalState]

/-- **One-step projection.** A verifier step from an eval-phase configuration
whose formula tape carries no interior left-markers maps onto a single
`satEvalOnInputTM` step of the projected configuration. -/
private theorem projEval_step (c c' : Cfg 3 verifyPairTM.Q)
    (heval : isEvalState c.state)
    (hnostart : ∀ j, j ≥ 1 → (c.work ⟨0, by omega⟩).cells j ≠ Γ.start)
    (hstep : verifyPairTM.step c = some c') :
    satEvalOnInputTM.step (projEvalCfg c) = some (projEvalCfg c') := by
  have hwbm : ∀ d : Dir3, (c.work (0 : Fin 3)).writeAndMove
      (TM.readBackWrite (c.work (0 : Fin 3)).read).toΓ d
      = (c.work (0 : Fin 3)).move d := fun d => writeBackMove_eq_move _ d hnostart
  have main : satEvalOnInputTM.step (projEvalCfg c) =
      Option.map projEvalCfg (verifyPairTM.step c) := by
    cases hcst : c.state with
    | evalReadFirst mode =>
        by_cases hb : (c.work (0 : Fin 3)).read = Γ.blank
        · simp [Option.map, TM.step, hcst, verifyPairTM, satEvalOnInputTM, projEvalCfg,
            projEvalState, verifyPairDelta, satEvalDelta, verifyPairPreserveWork, hb]
          have hh := hwbm (TM.idleDir Γ.blank)
          rw [hb] at hh; exact hh.symm
        · cases hr : readBit? (c.work (0 : Fin 3)).read with
          | some b =>
              simp [Option.map, TM.step, hcst, verifyPairTM, satEvalOnInputTM, projEvalCfg,
                projEvalState, verifyPairDelta, satEvalDelta, verifyPairPreserveWork, hb, hr]
              exact (hwbm _).symm
          | none =>
              simp [Option.map, TM.step, hcst, verifyPairTM, satEvalOnInputTM, projEvalCfg,
                projEvalState, verifyPairDelta, satEvalDelta,
                verifyPairReject, satEvalReject, hb, hr]
              exact (hwbm _).symm
    | evalReadSecond mode first =>
        cases hr : readBit? (c.work (0 : Fin 3)).read with
        | some second =>
            simp [Option.map, TM.step, hcst, verifyPairTM, satEvalOnInputTM, projEvalCfg,
              projEvalState, verifyPairDelta, satEvalDelta, verifyPairPreserveWork,
              verifyPairEvalDirs, hr]
            refine ⟨?_, (hwbm _).symm, ?_⟩
            · cases h : (satEvalTokenStep mode (tokenOfBits first second) (c.work 1).read).1 <;> rfl
            · funext i
              obtain rfl : i = 0 := Subsingleton.elim i 0
              simp
        | none =>
            simp [Option.map, TM.step, hcst, verifyPairTM, satEvalOnInputTM, projEvalCfg,
              projEvalState, verifyPairDelta, satEvalDelta, verifyPairReject, satEvalReject, hr]
            exact (hwbm _).symm
    | evalRewindAlpha mode =>
        by_cases ha : (c.work (1 : Fin 3)).read = Γ.start
        · simp [Option.map, TM.step, hcst, verifyPairTM, satEvalOnInputTM, projEvalCfg,
            projEvalState, verifyPairDelta, satEvalDelta, verifyPairPreserveWork, ha]
          refine ⟨(hwbm _).symm, ?_⟩
          funext i; obtain rfl : i = 0 := Subsingleton.elim i 0; simp
        · simp [Option.map, TM.step, hcst, verifyPairTM, satEvalOnInputTM, projEvalCfg,
            projEvalState, verifyPairDelta, satEvalDelta, verifyPairPreserveWork, ha]
          refine ⟨(hwbm _).symm, ?_⟩
          funext i; obtain rfl : i = 0 := Subsingleton.elim i 0; simp
    | init => rw [hcst] at heval; simp [isEvalState] at heval
    | initCounter => rw [hcst] at heval; simp [isEvalState] at heval
    | splitScan => rw [hcst] at heval; simp [isEvalState] at heval
    | splitAfterFalse => rw [hcst] at heval; simp [isEvalState] at heval
    | splitAfterTrue => rw [hcst] at heval; simp [isEvalState] at heval
    | rewindCounterForAlpha => rw [hcst] at heval; simp [isEvalState] at heval
    | copyAlpha => rw [hcst] at heval; simp [isEvalState] at heval
    | rewindFormula => rw [hcst] at heval; simp [isEvalState] at heval
    | rewindAssignment => rw [hcst] at heval; simp [isEvalState] at heval
    | done => rw [hcst] at heval; simp [isEvalState] at heval
  rw [main, hstep]; rfl

/-- A TM step never modifies its read-only input tape's cells (only its head). -/
private theorem step_input_cells {m : ℕ} {tm : TM m} {c c' : Cfg m tm.Q}
    (h : tm.step c = some c') : c'.input.cells = c.input.cells := by
  rw [TM.step] at h
  split at h
  · simp at h
  · rw [← Option.some.inj h]
    exact Tape.move_cells _ _

/-- The evaluator phases only transition to evaluator phases or the halt state. -/
private theorem verify_eval_next_state (c c' : Cfg 3 verifyPairTM.Q)
    (hev : isEvalState c.state) (hvstep : verifyPairTM.step c = some c') :
    isEvalState c'.state ∨ c'.state = .done := by
  have hcne : c.state ≠ verifyPairTM.qhalt := by
    intro h; rw [h] at hev; simp [isEvalState, verifyPairTM] at hev
  have hmap : c'.state = (verifyPairDelta c.state c.input.read
      (fun i => (c.work i).read) c.output.read).1 := by
    have h := hvstep
    rw [TM.step, ite_eq_right hcne] at h
    exact congrArg Cfg.state (Option.some.inj h).symm
  cases hcst : c.state with
  | evalReadFirst mode =>
      rw [hcst] at hmap
      simp only [verifyPairDelta, verifyPairReject] at hmap
      split at hmap
      · right; exact hmap
      · split at hmap
        · left; rw [hmap]; trivial
        · right; exact hmap
  | evalReadSecond mode first =>
      rw [hcst] at hmap
      simp only [verifyPairDelta, verifyPairReject] at hmap
      split at hmap
      · rw [hmap]
        cases (satEvalTokenStep mode (tokenOfBits first _)
          ((fun i => (c.work i).read) ⟨1, by omega⟩)).1 <;>
          (simp [isEvalState]; try rfl)
      · right; exact hmap
  | evalRewindAlpha mode =>
      rw [hcst] at hmap
      simp only [verifyPairDelta] at hmap
      split at hmap
      · left; rw [hmap]; trivial
      · left; rw [hmap]; trivial
  | init => rw [hcst] at hev; simp [isEvalState] at hev
  | initCounter => rw [hcst] at hev; simp [isEvalState] at hev
  | splitScan => rw [hcst] at hev; simp [isEvalState] at hev
  | splitAfterFalse => rw [hcst] at hev; simp [isEvalState] at hev
  | splitAfterTrue => rw [hcst] at hev; simp [isEvalState] at hev
  | rewindCounterForAlpha => rw [hcst] at hev; simp [isEvalState] at hev
  | copyAlpha => rw [hcst] at hev; simp [isEvalState] at hev
  | rewindFormula => rw [hcst] at hev; simp [isEvalState] at hev
  | rewindAssignment => rw [hcst] at hev; simp [isEvalState] at hev
  | done => rw [hcst] at hev; simp [isEvalState] at hev

/-- **Trace transfer.** A halting `satEvalOnInputTM` trace on the projected
configuration lifts back to a verifier trace of the same length, preserving the
eval-or-done invariant and the no-interior-marker invariant on the formula
tape. -/
private theorem projEval_reaches :
    ∀ (t : ℕ) (c : Cfg 3 verifyPairTM.Q) (d : Cfg 1 satEvalOnInputTM.Q),
      (isEvalState c.state ∨ c.state = .done) →
      (∀ j, j ≥ 1 → (c.work ⟨0, by omega⟩).cells j ≠ Γ.start) →
      satEvalOnInputTM.reachesIn t (projEvalCfg c) d →
      ∃ c', verifyPairTM.reachesIn t c c' ∧ projEvalCfg c' = d ∧
        (isEvalState c'.state ∨ c'.state = .done) ∧
        (∀ j, j ≥ 1 → (c'.work ⟨0, by omega⟩).cells j ≠ Γ.start) := by
  intro t
  induction t with
  | zero =>
      intro c d heod hns hreach
      cases hreach
      exact ⟨c, .zero, rfl, heod, hns⟩
  | succ t ih =>
      intro c d heod hns hreach
      cases hreach with
      | step hstep_sat hrest =>
          rcases heod with hev | hdone
          · obtain ⟨c', hvstep⟩ : ∃ c', verifyPairTM.step c = some c' := by
              have hcne : c.state ≠ verifyPairTM.qhalt := by
                intro h; rw [h] at hev; simp [isEvalState, verifyPairTM] at hev
              rw [TM.step, ite_eq_right hcne]; exact ⟨_, rfl⟩
            have hps := projEval_step c c' hev hns hvstep
            rw [hps] at hstep_sat
            obtain rfl := Option.some.inj hstep_sat
            have hev' := verify_eval_next_state c c' hev hvstep
            have hcell_eq : (c'.work ⟨0, by omega⟩).cells = (c.work ⟨0, by omega⟩).cells :=
              step_input_cells hps
            have hns' : ∀ j, j ≥ 1 → (c'.work ⟨0, by omega⟩).cells j ≠ Γ.start := by
              intro j hj
              rw [show (c'.work ⟨0, by omega⟩).cells j = (c.work ⟨0, by omega⟩).cells j from by
                rw [hcell_eq]]
              exact hns j hj
            obtain ⟨c'', hr'', hproj'', heod'', hns''⟩ := ih c' d hev' hns' hrest
            exact ⟨c'', .step hvstep hr'', hproj'', heod'', hns''⟩
          · exfalso
            have hq : (projEvalCfg c).state = satEvalOnInputTM.qhalt := by
              simp only [projEvalCfg, hdone, projEvalState, satEvalOnInputTM]
            exact TM.state_ne_qhalt_of_step hstep_sat hq

/-- **Lemma A-success + Lemma B.** When `|α| ≤ |z| + 1`, the verifier runs the
whole split/setup/eval pipeline from `initCfg (pair z α)`, halting within
`(4·|z| + 2·|α| + 12) + (2·|z| + 1)` steps with output equal to the SAT
semantics `satEvalSemBits α z`. -/
private theorem verifyPairSplit_eval_success (z α : List Bool)
    (hlen : α.length ≤ z.length + 1) :
    ∃ c' t,
      t ≤ 4 * z.length + 2 * α.length + 12 + (2 * z.length + 1) ∧
      verifyPairTM.reachesIn t (verifyPairTM.initCfg (pair z α)) c' ∧
      verifyPairTM.halted c' ∧
      c'.output.cells 1 = (if satEvalSemBits α z then Γ.one else Γ.zero) := by
  obtain ⟨c0, hr0, hs0, hw0, hw1, ho0⟩ := verifyPairSplit_setup_success_initTape z α hlen
  -- `projEvalCfg c0` is exactly the evaluator's started configuration.
  have hproj0_state : (projEvalCfg c0).state = .readFirst (.boundary true false true) := by
    simp only [projEvalCfg, hs0, projEvalState]
    rfl
  have hproj0_input : (projEvalCfg c0).input =
      (Tape.init (z.map Γ.ofBool)).move Dir3.right := hw0
  have hproj0_work : (projEvalCfg c0).work ⟨0, by omega⟩ =
      (Tape.init (α.map Γ.ofBool)).move Dir3.right := hw1
  have hproj0_out : (projEvalCfg c0).output = (Tape.init []).move Dir3.right := ho0
  obtain ⟨d, t2, ht2, hreach2, hhalt2, hout2⟩ :=
    satEvalOnInputTM_started_correct α z (projEvalCfg c0)
      hproj0_state hproj0_input hproj0_work hproj0_out
  -- the formula tape has no interior left-markers (it holds `z`)
  have hns0 : ∀ j, j ≥ 1 → (c0.work ⟨0, by omega⟩).cells j ≠ Γ.start := by
    intro j hj
    rw [hw0, Tape.move_cells]
    exact Tape.init_ofBool_cells_ne_start z j hj
  have hc0eod : isEvalState c0.state ∨ c0.state = .done := Or.inl (by rw [hs0]; trivial)
  obtain ⟨c', hreach', hproj', heod', _hns'⟩ :=
    projEval_reaches t2 c0 d hc0eod hns0 hreach2
  refine ⟨c', 4 * z.length + 2 * α.length + 12 + t2, by omega,
    TM.reachesIn_trans _ hr0 hreach', ?_, ?_⟩
  · -- halted
    have hcs : projEvalState c'.state = .done := by
      have h1 : projEvalState c'.state = d.state := congrArg Cfg.state hproj'
      rw [h1]; exact hhalt2
    exact state_done_of_isEvalOrDone heod' hcs
  · -- output bit
    have hco : c'.output = d.output := congrArg Cfg.output hproj'
    rw [hco, hout2]

/-- **Reject (witness too long).** When `|z| + 1 < |α|`, the counter is exhausted
during the copy of `α`, so the verifier halts with output `0`. -/
private theorem verifyPairSplit_reject_long (z α : List Bool)
    (hlen : z.length + 1 < α.length) :
    ∃ c' t,
      t ≤ 4 * z.length + 10 ∧
      verifyPairTM.reachesIn t (verifyPairTM.initCfg (pair z α)) c' ∧
      verifyPairTM.halted c' ∧
      c'.output.cells 1 = Γ.zero := by
  obtain ⟨c3, hr3, hs3, hi3h, hi3c, hw30h, hw30c0, hw30ns, hw30data, hw30blank, hw31,
      hw32h, hw32c0, hw32ns, hw32tally, hw32blank, ho3⟩ :=
    verifyPairSplit_setup_through_separator z α
  have hi3c0 : c3.input.cells 0 = Γ.start := by rw [hi3c]; simp [Tape.move, Tape.init]
  have hi3ns : ∀ j, j ≥ 1 → c3.input.cells j ≠ Γ.start := by
    intro j hj; rw [hi3c, Tape.move_cells]
    exact Tape.init_ofBool_cells_ne_start (pair z α) j hj
  have hw31h : (c3.work ⟨1, by omega⟩).head = 1 := by rw [hw31]; simp [Tape.move, Tape.init]
  have hw31c0 : (c3.work ⟨1, by omega⟩).cells 0 = Γ.start := by
    rw [hw31]; simp [Tape.move, Tape.init]
  have hw31ns : ∀ j, j ≥ 1 → (c3.work ⟨1, by omega⟩).cells j ≠ Γ.start := by
    intro j hj; rw [hw31, Tape.move_cells]
    cases j with | zero => omega | succ k => simp [Tape.init]
  have hframe3 : ∀ i, i ≠ (⟨2, by omega⟩ : Fin 3) →
      (c3.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c3.work i).cells j ≠ Γ.start := by
    intro i hi
    match i with
    | ⟨0, _⟩ => exact ⟨by rw [hw30h]; omega, hw30ns⟩
    | ⟨1, _⟩ => exact ⟨by rw [hw31h], hw31ns⟩
    | ⟨2, _⟩ => exact absurd rfl hi
  have hi3h1 : c3.input.head ≥ 1 := by rw [hi3h]; omega
  -- Rewind the counter (head |z|+2 → 1)
  obtain ⟨c4, hr4, hs4, hw42h, hw42c, hw4frame, hi4, ho4⟩ :=
    verifyPairSplit_rewindCounter_phase (z.length + 2) c3 hs3 hw32c0 hw32ns hw32h
      hi3h1 hi3ns hframe3 (by rw [ho3]; simp [Tape.move, Tape.init])
      (by rw [ho3]; intro j hj; rw [Tape.move_cells];
          cases j with | zero => omega | succ k => simp [Tape.init])
  have hw40 : c4.work ⟨0, by omega⟩ = c3.work ⟨0, by omega⟩ := hw4frame ⟨0, by omega⟩ (by simp)
  have hw41 : c4.work ⟨1, by omega⟩ = c3.work ⟨1, by omega⟩ := hw4frame ⟨1, by omega⟩ (by simp)
  have hc4ih : c4.input.head = 2 * z.length + 3 := by rw [hi4, hi3h]
  -- copy only the first `|z|+1` bits of `α`, exhausting the counter
  set as := α.take (z.length + 1) with has_def
  have haslen : as.length = z.length + 1 := by rw [has_def, List.length_take]; omega
  have halpha : ∀ j, (h : j < as.length) →
      c4.input.cells (c4.input.head + j) = Γ.ofBool (as[j]'h) := by
    intro j h
    have hjα : j < α.length := by rw [haslen] at h; omega
    rw [hi4, hi3h, hi3c, Tape.move_cells,
      show 2 * z.length + 3 + j = (2 * z.length + 2 + j) + 1 from by ring,
      Tape.init_ofBool_cells_lt (pair z α) (2 * z.length + 2 + j) (by rw [pair_length]; omega),
      pair_getElem_right z α j hjα]
    simp only [has_def, List.getElem_take]
  have hcnt4 : ∀ i, i < as.length →
      (c4.work ⟨2, by omega⟩).cells ((c4.work ⟨2, by omega⟩).head + i) = Γ.one := by
    intro i hi; rw [hw42h, hw42c]; exact hw32tally i (by rw [haslen] at hi; omega)
  obtain ⟨c5, hr5, hs5, hi5h, hi5c, hw50, hw51h, hw51c0, hw51ns, hw51below, hw51above,
      hw51data, hw52h, hw52hexact, hw52c0, hw52ns, hw52above, ho5⟩ :=
    verifyPairSplit_copyAlpha_loop as c4 hs4 (by rw [hi4]; exact hi3h1)
      (by rw [hi4]; exact hi3c0) (by rw [hi4]; exact hi3ns) halpha
      (by rw [hw40, hw30h]; omega) (by rw [hw40]; exact hw30ns)
      (by rw [hw41, hw31h]) (by rw [hw41]; exact hw31c0) (by rw [hw41]; exact hw31ns)
      hw42h.ge (by rw [hw42c]; exact hw32c0) (by rw [hw42c]; exact hw32ns)
      hcnt4 (by rw [ho4, ho3]; simp [Tape.move, Tape.init])
      (by rw [ho4, ho3]; intro j hj; rw [Tape.move_cells];
          cases j with | zero => omega | succ k => simp [Tape.init])
  -- the `(|z|+2)`-th assignment bit sits under the input head; the counter is dry
  have hib5 : c5.input.read = Γ.ofBool (α[z.length + 1]'(by omega)) := by
    show c5.input.cells c5.input.head = _
    rw [hi5c, hi5h, hc4ih, haslen, hi4, hi3c, Tape.move_cells,
      show 2 * z.length + 3 + (z.length + 1) = (2 * z.length + 2 + (z.length + 1)) + 1 from by ring,
      Tape.init_ofBool_cells_lt (pair z α) (2 * z.length + 2 + (z.length + 1))
        (by rw [pair_length]; omega),
      pair_getElem_right z α (z.length + 1) (by omega)]
  have hcounter5 : (c5.work ⟨2, by omega⟩).read ≠ Γ.one := by
    show (c5.work ⟨2, by omega⟩).cells (c5.work ⟨2, by omega⟩).head ≠ Γ.one
    rw [hw52hexact, hw42h, haslen, show 1 + (z.length + 1) = z.length + 2 from by omega,
      hw52above (z.length + 2) (by rw [hw42h, haslen]; omega), hw42c,
      hw32blank (z.length + 2) (by omega)]
    decide
  obtain ⟨c6, hstep6, hhalt6, hzero6⟩ :=
    verifyPairSplit_copyAlpha_reject_step (α[z.length + 1]'(by omega)) c5 hs5 hib5 hcounter5
      (by rw [ho5, ho4, ho3])
  refine ⟨c6, (2 * z.length + 4) + ((z.length + 2 + 1) + (as.length + 1)), ?_, ?_, hhalt6, hzero6⟩
  · rw [haslen]; omega
  · exact TM.reachesIn_trans _ hr3 (TM.reachesIn_trans _ hr4
      (TM.reachesIn_trans _ hr5 (.step hstep6 .zero)))

/-- A split-phase reject from `.splitScan` reading a blank (end of input). -/
private theorem verifyPairSplit_splitScan_reject (c : Cfg 3 verifyPairTM.Q)
    (hst : c.state = .splitScan) (hread : c.input.read = Γ.blank)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', verifyPairTM.step c = some c' ∧ verifyPairTM.halted c' ∧
      c'.output.cells 1 = Γ.zero := by
  let c' : Cfg 3 verifyPairTM.Q :=
    { state := .done
      input := c.input.move (TM.idleDir c.input.read)
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
          (TM.idleDir (c.work i).read)
      output := c.output.writeAndMove Γw.zero (TM.idleDir c.output.read) }
  have hstep : verifyPairTM.step c = some c' := by
    simp [c', verifyPairTM, TM.step, verifyPairDelta, hst, hread, readBit?,
      verifyPairReject]
  refine ⟨c', hstep, rfl, ?_⟩
  show (c.output.writeAndMove Γw.zero (TM.idleDir c.output.read)).cells 1 = Γ.zero
  rw [hout]
  simp [Tape.writeAndMove, Tape.write, Tape.move, TM.idleDir, Tape.read,
    Tape.init, Γw.toΓ]

/-- A split-phase reject from `.splitAfterFalse` reading a blank. -/
private theorem verifyPairSplit_afterFalse_reject (c : Cfg 3 verifyPairTM.Q)
    (hst : c.state = .splitAfterFalse) (hread : c.input.read = Γ.blank)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', verifyPairTM.step c = some c' ∧ verifyPairTM.halted c' ∧
      c'.output.cells 1 = Γ.zero := by
  let c' : Cfg 3 verifyPairTM.Q :=
    { state := .done
      input := c.input.move (TM.idleDir c.input.read)
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
          (TM.idleDir (c.work i).read)
      output := c.output.writeAndMove Γw.zero (TM.idleDir c.output.read) }
  have hstep : verifyPairTM.step c = some c' := by
    simp [c', verifyPairTM, TM.step, verifyPairDelta, hst, hread, readBit?,
      verifyPairReject]
  refine ⟨c', hstep, rfl, ?_⟩
  show (c.output.writeAndMove Γw.zero (TM.idleDir c.output.read)).cells 1 = Γ.zero
  rw [hout]
  simp [Tape.writeAndMove, Tape.write, Tape.move, TM.idleDir, Tape.read,
    Tape.init, Γw.toΓ]

/-- A split-phase reject from `.splitAfterTrue` reading anything other than a
second `true` (a blank, or a `0`). -/
private theorem verifyPairSplit_afterTrue_reject (c : Cfg 3 verifyPairTM.Q)
    (hst : c.state = .splitAfterTrue)
    (hread : c.input.read = Γ.blank ∨ c.input.read = Γ.zero)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', verifyPairTM.step c = some c' ∧ verifyPairTM.halted c' ∧
      c'.output.cells 1 = Γ.zero := by
  let c' : Cfg 3 verifyPairTM.Q :=
    { state := .done
      input := c.input.move (TM.idleDir c.input.read)
      work := fun i =>
        (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
          (TM.idleDir (c.work i).read)
      output := c.output.writeAndMove Γw.zero (TM.idleDir c.output.read) }
  have hstep : verifyPairTM.step c = some c' := by
    rcases hread with h | h <;>
      simp [c', verifyPairTM, TM.step, verifyPairDelta, hst, h, readBit?,
        verifyPairReject]
  refine ⟨c', hstep, rfl, ?_⟩
  show (c.output.writeAndMove Γw.zero (TM.idleDir c.output.read)).cells 1 = Γ.zero
  rw [hout]
  simp [Tape.writeAndMove, Tape.write, Tape.move, TM.idleDir, Tape.read,
    Tape.init, Γw.toΓ]

/-- The split scan rejects every input that is not a valid `pair` encoding,
mirroring the recursion of `unpair?`. -/
private theorem verifyPairSplit_scan_reject :
    ∀ (suffix : List Bool) (c : Cfg 3 verifyPairTM.Q),
      c.state = .splitScan →
      unpair? suffix = none →
      hasBoolSuffix c.input suffix →
      (∀ i, (c.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c.work i).cells j ≠ Γ.start) →
      c.output = (Tape.init []).move Dir3.right →
      ∃ c' t,
        t ≤ 2 * suffix.length + 2 ∧
        verifyPairTM.reachesIn t c c' ∧ verifyPairTM.halted c' ∧
        c'.output.cells 1 = Γ.zero := by
  intro suffix
  induction hlen : suffix.length using Nat.strong_induction_on generalizing suffix with
  | h n ih =>
    intro c hst hnone hsuf hwst hout
    have hoh : c.output.head ≥ 1 := by rw [hout]; simp [Tape.move, Tape.init]
    have hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start := by
      rw [hout]; intro j hj; rw [Tape.move_cells]
      cases j with | zero => omega | succ k => simp [Tape.init]
    cases suffix with
    | nil =>
        obtain ⟨c', hstep, hhalt, hz⟩ :=
          verifyPairSplit_splitScan_reject c hst (hasBoolSuffix_read_nil hsuf) hout
        exact ⟨c', 1, by omega, .step hstep .zero, hhalt, hz⟩
    | cons b1 rest =>
      cases rest with
      | nil =>
          have hread1 : c.input.read = Γ.ofBool b1 := hasBoolSuffix_read_cons hsuf
          cases b1 with
          | false =>
              obtain ⟨c1, hstep1, hst1, hc1ih, hc1ic, hc1w, hc1o⟩ :=
                verifyPairSplit_scanX_false_step c hst hread1 hwst hoh hons
              have hc1read : c1.input.read = Γ.blank := by
                show c1.input.cells c1.input.head = _
                rw [hc1ic, hc1ih]; simpa using hsuf.2.2.1
              obtain ⟨c', hstep2, hhalt, hz⟩ :=
                verifyPairSplit_afterFalse_reject c1 hst1 hc1read (by rw [hc1o]; exact hout)
              exact ⟨c', 2, by omega, .step hstep1 (.step hstep2 .zero), hhalt, hz⟩
          | true =>
              obtain ⟨c1, hstep1, hst1, hc1ih, hc1ic, hc1w, hc1o⟩ :=
                verifyPairSplit_scanX_true_step c hst hread1 hwst hoh hons
              have hc1read : c1.input.read = Γ.blank := by
                show c1.input.cells c1.input.head = _
                rw [hc1ic, hc1ih]; simpa using hsuf.2.2.1
              obtain ⟨c', hstep2, hhalt, hz⟩ :=
                verifyPairSplit_afterTrue_reject c1 hst1 (Or.inl hc1read) (by rw [hc1o]; exact hout)
              exact ⟨c', 2, by omega, .step hstep1 (.step hstep2 .zero), hhalt, hz⟩
      | cons b2 rest2 =>
          have hread1 : c.input.read = Γ.ofBool b1 := hasBoolSuffix_read_cons hsuf
          have hnext : c.input.cells (c.input.head + 1) = Γ.ofBool b2 := by
            exact hsuf.2.1 1 (by simp)
          cases b1 <;> cases b2
          · -- false false: consume `00`, recurse on rest2
            have hnone2 : unpair? rest2 = none := by
              simpa [unpair?] using hnone
            obtain ⟨c', hr2, hst', hc'ih, hc'ic, hc'0h, hc'0c, hc'1w, hc'2h, hc'2c, hc'o⟩ :=
              verifyPairSplit_bit_step false c hst hread1 hnext hwst hoh hons
            have hwst' : ∀ i, (c'.work i).head ≥ 1 ∧
                ∀ j, j ≥ 1 → (c'.work i).cells j ≠ Γ.start := by
              intro i
              match i with
              | ⟨0, _⟩ =>
                  refine ⟨by rw [hc'0h]; omega, ?_⟩
                  rw [hc'0c]; intro j hj
                  by_cases hjx : j = (c.work ⟨0, by omega⟩).head
                  · rw [hjx, Function.update_self]; decide
                  · rw [Function.update_of_ne hjx]; exact (hwst ⟨0, by omega⟩).2 j hj
              | ⟨1, _⟩ => rw [hc'1w]; exact hwst ⟨1, by omega⟩
              | ⟨2, _⟩ =>
                  refine ⟨by rw [hc'2h]; omega, ?_⟩
                  rw [hc'2c]; intro j hj
                  by_cases hjx : j = (c.work ⟨2, by omega⟩).head
                  · rw [hjx, Function.update_self]; decide
                  · rw [Function.update_of_ne hjx]; exact (hwst ⟨2, by omega⟩).2 j hj
            have hsuf' : hasBoolSuffix c'.input rest2 := by
              obtain ⟨_, hdata, hblank, hns⟩ := hsuf
              refine ⟨by rw [hc'ih]; omega, ?_, ?_, ?_⟩
              · intro i hi
                rw [hc'ic, hc'ih,
                  show c.input.head + 2 + i = c.input.head + (i + 2) from by omega]
                have := hdata (i + 2) (by simp only [List.length_cons]; omega)
                simpa using this
              · rw [hc'ic, hc'ih,
                  show c.input.head + 2 + rest2.length =
                    c.input.head + (rest2.length + 2) from by omega]
                simpa [List.length_cons] using hblank
              · intro j hj; rw [hc'ic]; exact hns j hj
            obtain ⟨c'', t, htb, hr'', hhalt'', hz''⟩ :=
              ih rest2.length (by simp only [List.length_cons] at hlen; omega) rest2 rfl c' hst'
                hnone2
                hsuf' hwst' (by rw [hc'o]; exact hout)
            exact ⟨c'', 2 + t, by simp only [List.length_cons] at hlen; omega,
              TM.reachesIn_trans _ hr2 hr'', hhalt'', hz''⟩
          · -- false true: separator → `unpair?` succeeds, contradicting `hnone`
            simp [unpair?] at hnone
          · -- true false: reject (`.splitAfterTrue` reads `0`)
            obtain ⟨c1, hstep1, hst1, hc1ih, hc1ic, hc1w, hc1o⟩ :=
              verifyPairSplit_scanX_true_step c hst hread1 hwst hoh hons
            have hc1read : c1.input.read = Γ.zero := by
              show c1.input.cells c1.input.head = _
              rw [hc1ic, hc1ih]; exact hnext
            obtain ⟨c', hstep2, hhalt, hz⟩ :=
              verifyPairSplit_afterTrue_reject c1 hst1 (Or.inr hc1read) (by rw [hc1o]; exact hout)
            exact ⟨c', 2, by omega,
              .step hstep1 (.step hstep2 .zero), hhalt, hz⟩
          · -- true true: consume `11`, recurse on rest2
            have hnone2 : unpair? rest2 = none := by
              simpa [unpair?] using hnone
            obtain ⟨c', hr2, hst', hc'ih, hc'ic, hc'0h, hc'0c, hc'1w, hc'2h, hc'2c, hc'o⟩ :=
              verifyPairSplit_bit_step true c hst hread1 hnext hwst hoh hons
            have hwst' : ∀ i, (c'.work i).head ≥ 1 ∧
                ∀ j, j ≥ 1 → (c'.work i).cells j ≠ Γ.start := by
              intro i
              match i with
              | ⟨0, _⟩ =>
                  refine ⟨by rw [hc'0h]; omega, ?_⟩
                  rw [hc'0c]; intro j hj
                  by_cases hjx : j = (c.work ⟨0, by omega⟩).head
                  · rw [hjx, Function.update_self]; decide
                  · rw [Function.update_of_ne hjx]; exact (hwst ⟨0, by omega⟩).2 j hj
              | ⟨1, _⟩ => rw [hc'1w]; exact hwst ⟨1, by omega⟩
              | ⟨2, _⟩ =>
                  refine ⟨by rw [hc'2h]; omega, ?_⟩
                  rw [hc'2c]; intro j hj
                  by_cases hjx : j = (c.work ⟨2, by omega⟩).head
                  · rw [hjx, Function.update_self]; decide
                  · rw [Function.update_of_ne hjx]; exact (hwst ⟨2, by omega⟩).2 j hj
            have hsuf' : hasBoolSuffix c'.input rest2 := by
              obtain ⟨_, hdata, hblank, hns⟩ := hsuf
              refine ⟨by rw [hc'ih]; omega, ?_, ?_, ?_⟩
              · intro i hi
                rw [hc'ic, hc'ih,
                  show c.input.head + 2 + i = c.input.head + (i + 2) from by omega]
                have := hdata (i + 2) (by simp only [List.length_cons]; omega)
                simpa using this
              · rw [hc'ic, hc'ih,
                  show c.input.head + 2 + rest2.length =
                    c.input.head + (rest2.length + 2) from by omega]
                simpa [List.length_cons] using hblank
              · intro j hj; rw [hc'ic]; exact hns j hj
            obtain ⟨c'', t, htb, hr'', hhalt'', hz''⟩ :=
              ih rest2.length (by simp only [List.length_cons] at hlen; omega) rest2 rfl c' hst'
                hnone2
                hsuf' hwst' (by rw [hc'o]; exact hout)
            exact ⟨c'', 2 + t, by simp only [List.length_cons] at hlen; omega,
              TM.reachesIn_trans _ hr2 hr'', hhalt'', hz''⟩

/-- **Reject (malformed input).** When `w` is not a valid `pair`, the split scan
rejects, halting with output `0`. -/
private theorem verifyPairSplit_reject_malformed (w : List Bool)
    (hw : unpair? w = none) :
    ∃ c' t,
      t ≤ 2 * w.length + 4 ∧
      verifyPairTM.reachesIn t (verifyPairTM.initCfg w) c' ∧
      verifyPairTM.halted c' ∧
      c'.output.cells 1 = Γ.zero := by
  obtain ⟨c1, hr1, hs1, hi1, hw01, hw11, hu2, hc2start, ho1⟩ :=
    verifyPairTM_init_steps w
  obtain ⟨hu2h, hu2one, hu2blank⟩ := hu2
  have hwst : ∀ i, (c1.work i).head ≥ 1 ∧ ∀ j, j ≥ 1 → (c1.work i).cells j ≠ Γ.start := by
    intro i
    match i with
    | ⟨0, _⟩ =>
        refine ⟨by rw [hw01]; simp [Tape.move, Tape.init], ?_⟩
        rw [hw01]; intro j hj; rw [Tape.move_cells]
        cases j with | zero => omega | succ k => simp [Tape.init]
    | ⟨1, _⟩ =>
        refine ⟨by rw [hw11]; simp [Tape.move, Tape.init], ?_⟩
        rw [hw11]; intro j hj; rw [Tape.move_cells]
        cases j with | zero => omega | succ k => simp [Tape.init]
    | ⟨2, _⟩ =>
        refine ⟨by rw [hu2h]; omega, ?_⟩
        intro j hj
        cases j with
        | zero => omega
        | succ k =>
            by_cases hk : k < 1
            · have : k = 0 := by omega
              subst this; rw [hu2one 0 (by omega)]; decide
            · rw [hu2blank k (by omega)]; decide
  obtain ⟨c', t, htb, hr', hhalt, hz⟩ :=
    verifyPairSplit_scan_reject w c1 hs1 hw
      (by rw [hi1]; exact initTape_move_right_hasBoolSuffix w) hwst ho1
  exact ⟨c', 2 + t, by omega, TM.reachesIn_trans _ hr1 hr', hhalt, hz⟩

/-- **Combine.** `verifyPairTM` decides `pairLang Witness` within the quadratic
budget `verifyPairTMTime`. -/
theorem verifyPairTM_decidesInTime :
    verifyPairTM.DecidesInTime (pairLang Witness) verifyPairTMTime := by
  intro w
  obtain ⟨c', t, ht, hreach, hhalt, hout⟩ : ∃ c' t,
      t ≤ verifyPairTMTime w.length ∧
      verifyPairTM.reachesIn t (verifyPairTM.initCfg w) c' ∧
      verifyPairTM.halted c' ∧
      c'.output.cells 1 = (if verifyPairSem w then Γ.one else Γ.zero) := by
    cases hunpair : unpair? w with
    | none =>
        obtain ⟨c', t, ht, hreach, hhalt, hzero⟩ := verifyPairSplit_reject_malformed w hunpair
        refine ⟨c', t, ?_, hreach, hhalt, ?_⟩
        · have hb : 2 * w.length + 4 ≤ verifyPairTMTime w.length := by
            unfold verifyPairTMTime
            nlinarith [Nat.zero_le ((w.length + 3) * (w.length + 3))]
          omega
        · rw [hzero]; simp [verifyPairSem, hunpair]
    | some zα =>
        obtain ⟨z, α⟩ := zα
        have hw : w = pair z α := eq_pair_of_unpair?_eq_some hunpair
        subst hw
        by_cases hlen : α.length ≤ z.length + 1
        · obtain ⟨c', t, ht, hreach, hhalt, hout⟩ := verifyPairSplit_eval_success z α hlen
          refine ⟨c', t, ?_, hreach, hhalt, ?_⟩
          · have hb : 4 * z.length + 2 * α.length + 12 + (2 * z.length + 1) ≤
                verifyPairTMTime (pair z α).length := by
              rw [pair_length]; unfold verifyPairTMTime
              nlinarith [Nat.zero_le
                ((2 * z.length + 2 + α.length + 3) * (2 * z.length + 2 + α.length + 3))]
            omega
          · rw [hout]
            have hvs : verifyPairSem (pair z α) = satEvalSemBits α z := by
              simp [verifyPairSem, hlen]
            rw [hvs]
        · push Not at hlen
          obtain ⟨c', t, ht, hreach, hhalt, hzero⟩ := verifyPairSplit_reject_long z α hlen
          refine ⟨c', t, ?_, hreach, hhalt, ?_⟩
          · have hb : 4 * z.length + 10 ≤ verifyPairTMTime (pair z α).length := by
              rw [pair_length]; unfold verifyPairTMTime
              nlinarith [Nat.zero_le
                ((2 * z.length + 2 + α.length + 3) * (2 * z.length + 2 + α.length + 3))]
            omega
          · rw [hzero]
            have hnle : ¬ (α.length ≤ z.length + 1) := by omega
            simp [verifyPairSem, hnle]
  refine ⟨c', t, ht, hreach, hhalt, ?_, ?_⟩
  · intro hmem
    simp [hout, (verifyPairSem_eq_true_iff_mem_pairLang w).mpr hmem]
  · intro hnmem
    have hb : verifyPairSem w = false := by
      rcases Bool.eq_false_or_eq_true (verifyPairSem w) with h | h
      · exact absurd ((verifyPairSem_eq_true_iff_mem_pairLang w).mp h) hnmem
      · exact h
    simp [hout, hb]

end VerifierTM

end SAT

end Complexity
