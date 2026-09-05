/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Internal.BodyLoop
public import Complexitylib.Models.TuringMachine.UTM.Internal.StepGlue

/-!
# Body correctness: the per-iteration theorem

The capstone gluing of the body correctness: from the body's start state,
under the standing invariant `SimInv`, one pass of the body machine reaches
`bodyDone` in `bodyIterTime α` steps and

* is an exact no-op when the interpreted machine `(decodeDesc α).toTM` is
  halted at `mc`, and
* re-establishes `SimInv` at `(decodeDesc α).toTM.step mc` otherwise.

The proof chains the phase lemmas of `BodyAssembly`/`BodyLoop`
(`hcPhase_halted`/`hcPhase_running` → `peekSeekPhase` → `matchLoop` →
`applyPhase`/`defaultTail`) and identifies the machine's decoded action with
the abstract table lookup via the `BodyLookup` correspondence
(`firstMatch_lookup`/`noMatch_lookup`, `value_slices`).

The side condition `TerminatedRegion` rules out the one machine/decoder
divergence: an entry region starting with an empty segment followed by junk
(see `matchLoop`).
-/


@[expose] public section

namespace Complexity

namespace TM.UTMBody

open BodyQ

-- ════════════════════════════════════════════════════════════════════════
-- Helpers
-- ════════════════════════════════════════════════════════════════════════

/-- `HoldsExact` only inspects the cells. -/
private theorem holdsExact_cells_congr {t' t : Tape} {l : List Γw}
    (he : t'.cells = t.cells) (h : t.HoldsExact l) : t'.HoldsExact l :=
  ⟨by rw [he]; exact h.1, fun i => by rw [he]; exact h.2 i⟩

/-- `StartInvariant` only inspects the cells. -/
private theorem wfCells_cells_congr {t' t : Tape} (he : t'.cells = t.cells)
    (h : t.StartInvariant) : t'.StartInvariant :=
  ⟨by rw [he]; exact h.1, fun j hj => by rw [he]; exact h.2 j hj⟩

private theorem takeField_fst_length_le (l : List Γw) :
    (takeField l).1.length ≤ l.length := by
  rcases takeField_structure l with hsp | ⟨hsp, -⟩
  · have := congrArg List.length hsp
    simp only [List.length_append, List.length_cons] at this
    omega
  · exact le_of_eq (congrArg List.length hsp)

private theorem qhaltField_length_le (l : List Γw) :
    (qhaltField l).length ≤ l.length :=
  le_trans (takeField_fst_length_le (takeField l).2) (takeField_rest_length l)

/-- `readBackWrite` (the machine's identity write) is `TMDesc.readback`. -/
private theorem readBackWrite_eq_readback (g : Γ) :
    readBackWrite g = TMDesc.readback g := by
  cases g <;> rfl

/-- The peek flag and the interpreter's `▷`-test decide the same
    sanitization. -/
private theorem sanitize_dir_eq {sim : Tape} (hwf : sim.StartInvariant) (flag : Bool)
    (hflag : flag = decide (sim.head = 0)) (d : Dir3) :
    (if flag then Dir3.right else d)
      = (if sim.read = Γ.start then Dir3.right else d) := by
  subst hflag
  by_cases h0 : sim.head = 0
  · rw [decide_eq_true h0, ite_eq_left rfl, ite_eq_left ((read_start_iff hwf).mpr h0)]
  · rw [decide_eq_false h0, ite_eq_right Bool.false_ne_true,
      ite_eq_right (fun hc => h0 ((read_start_iff hwf).mp hc))]

/-- **The default-move correspondence** (the crux of the no-match branch):
    the UTM's readback-write plus flag-sanitized move on the shadow tape
    shadows the simulated tape's read-sanitized move. -/
private theorem vshift_default_move {sim utm : Tape} (h : VShift sim utm)
    (hwf : sim.StartInvariant) (flag : Bool) (hflag : flag = decide (sim.head = 0)) :
    VShift (sim.move (if sim.read = Γ.start then Dir3.right else Dir3.stay))
      (utm.writeAndMove (readBackWrite utm.read).toΓ
        (if flag then Dir3.right else Dir3.stay)) := by
  rw [readBackWrite_eq_readback,
    writeAndMove_readback_eq_move (h.startInvariant hwf),
    sanitize_dir_eq hwf flag hflag Dir3.stay]
  exact h.move _ (fun h0 => by rw [ite_eq_left ((read_start_iff hwf).mpr h0)])

/-- The interpreted step in closed form, on a running configuration whose
    looked-up action is `a`. -/
private theorem toTM_step_running {d : TMDesc} {mc : Cfg 1 d.toTM.Q}
    {a : DescAct} (hh : mc.state ≠ d.toTM.qhalt)
    (ha : d.lookup mc.state.val mc.input.read ((mc.work 0).read)
      mc.output.read = a) :
    d.toTM.step mc = some
      { state := ⟨min a.q' (2 ^ d.w), Nat.lt_succ_of_le (Nat.min_le_right ..)⟩
        input := mc.input.move
          (if mc.input.read = Γ.start then Dir3.right else a.di)
        work := fun i => (mc.work i).writeAndMove a.ww.toΓ
          (if (mc.work i).read = Γ.start then Dir3.right else a.dw)
        output := mc.output.writeAndMove a.wo.toΓ
          (if mc.output.read = Γ.start then Dir3.right else a.dOut) } := by
  subst ha
  simp only [TM.step, ite_eq_right hh]
  rfl

-- ════════════════════════════════════════════════════════════════════════
-- The statement
-- ════════════════════════════════════════════════════════════════════════

/-- The side condition ruling out the machine/decoder divergence on an
    empty leading table segment followed by junk (see `matchLoop`). -/
def TerminatedRegion (α : List Bool) : Prop :=
  ∀ s rest, (takeField (takeField (groupPairs α)).2).2 = Γw.blank :: s :: rest →
    s = Γw.blank

/-- Time bound for one body iteration: quadratic in the description length,
    with generous constants (the match loop dominates). -/
def bodyIterTime (α : List Bool) : ℕ :=
  ((groupPairs α).length + 2) * (4 * (groupPairs α).length + 60)
    + 30 * (groupPairs α).length + 100

/-- **Per-iteration correctness of the body machine**: from `hc0` under
    `SimInv`, the body reaches `bodyDone` within `bodyIterTime α` steps,
    leaving the real input/output tapes untouched; if the interpreted
    machine is halted the pass is an exact no-op on every work tape, and
    otherwise `SimInv` is re-established at the stepped configuration. -/
theorem bodyIteration (α : List Bool) (mc : Cfg 1 (decodeDesc α).toTM.Q)
    (hterm : TerminatedRegion α)
    (c : Cfg 6 bodyTM.Q)
    (hst : c.state = BodyQ.hc0)
    (hinv : SimInv α mc c.input c.work c.output) :
    ∃ c' t, t ≤ bodyIterTime α ∧
      bodyTM.reachesIn t c c' ∧
      c'.state = BodyQ.bodyDone ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      match (decodeDesc α).toTM.step mc with
      | none => ∀ i, c'.work i = c.work i
      | some mc' => SimInv α mc' c'.input c'.work c'.output := by
  -- length bookkeeping
  have hF1L : (takeField (groupPairs α)).1.length ≤ (groupPairs α).length :=
    takeField_fst_length_le _
  have hqhL : (qhaltField (groupPairs α)).length ≤ (groupPairs α).length :=
    qhaltField_length_le _
  have hRL : (takeField (takeField (groupPairs α)).2).2.length
      ≤ (groupPairs α).length :=
    le_trans (takeField_rest_length _) (takeField_rest_length _)
  have hwL : (decodeDesc α).w ≤ (groupPairs α).length := by
    rw [decodeDesc_w]; exact hF1L
  by_cases hh : mc.state = (decodeDesc α).toTM.qhalt
  · -- ── halted: the body is an exact no-op ──────────────────────────────
    have hstep : (decodeDesc α).toTM.step mc = none := by
      simp [TM.step, hh]
    obtain ⟨c', t, ht, hreach, hst', hin', hwk', hout'⟩ :=
      hcPhase_halted c hst hinv hh
    refine ⟨c', t, ?_, hreach, hst', hin', hout', ?_⟩
    · obtain ⟨M, hM⟩ : ∃ M, bodyIterTime α
          = M + 30 * (groupPairs α).length + 100 := ⟨_, rfl⟩
      rw [hM]; omega
    · rw [hstep]
      exact hwk'
  · -- ── running: chase the phases ─────────────────────────────────────────
    -- the state clause must be the running disjunct
    obtain ⟨hq, hSt⟩ : mc.state.val < 2 ^ (decodeDesc α).w ∧
        (c.work stT).HoldsExact
          (bitsToSyms (Nat.toBits (decodeDesc α).w mc.state.val)) := by
      rcases hinv.state with h | ⟨hqh, -⟩
      · exact h
      · exact absurd hqh hh
    have hlenS : (bitsToSyms (Nat.toBits (decodeDesc α).w mc.state.val)).length
        = (decodeDesc α).w := by
      rw [bitsToSyms_length, Nat.length_toBits]
    -- sim reads from the honest flags
    have hsr0 : simRead (decide (mc.input.head = 0)) ((c.work vIn).read)
        = mc.input.read := simRead_flag_eq hinv.vin hinv.wf_in
    have hsr1 : simRead (decide ((mc.work 0).head = 0)) ((c.work vWk).read)
        = (mc.work 0).read := simRead_flag_eq hinv.vwk hinv.wf_wk
    have hsr2 : simRead (decide (mc.output.head = 0)) ((c.work vOut).read)
        = mc.output.read := simRead_flag_eq hinv.vout hinv.wf_out
    -- phase 1: the halt check falls through
    obtain ⟨c₁, t₁, ht₁, hr₁, hst₁, hin₁, hwk₁, hout₁⟩ :=
      hcPhase_running c hst hinv hh
    have hwork₁ : c₁.work = c.work := funext hwk₁
    have hinv₁ : SimInv α mc c₁.input c₁.work c₁.output := by
      rw [hin₁, hout₁, hwork₁]; exact hinv
    -- phase 2: peek the flags, seek to the entry region
    obtain ⟨c₂, t₂, ht₂, hr₂, hst₂, hwk₂, hdsT₂, hin₂, hout₂⟩ :=
      peekSeekPhase c₁ hst₁ hinv₁
    have hwk₂' : ∀ i, i ≠ dsT → c₂.work i = c.work i :=
      fun i hi => (hwk₂ i hi).trans (hwk₁ i)
    have hdsT₂' : c₂.work dsT = ⟨(takeField (groupPairs α)).1.length
        + (qhaltField (groupPairs α)).length + 3, (c.work dsT).cells⟩ := by
      rw [hdsT₂, hwork₁]
    -- phase 3: the match loop
    obtain ⟨hcase_some, hcase_none⟩ :=
      matchLoop (decide (mc.input.head = 0), decide ((mc.work 0).head = 0),
          decide (mc.output.head = 0))
        ((c.work vIn).read) ((c.work vWk).read) ((c.work vOut).read)
        (bitsToSyms (Nat.toBits (decodeDesc α).w mc.state.val))
        (fun s hs => bitsToSyms_ne_blank hs)
        ((takeField (takeField (groupPairs α)).2).2)
        ((takeField (groupPairs α)).1.length
          + (qhaltField (groupPairs α)).length + 3)
        c₂ hterm hst₂
        (fun j => by
          rw [hdsT₂']
          exact descLayout_entries hinv.desc j)
        (by rw [hdsT₂'])
        (by omega)
        (fun j hj => by
          rw [hdsT₂']
          exact (Tape.HoldsExact.startInvariant hinv.desc).2 j hj)
        (by rw [hwk₂' stT (by decide)]; exact hSt)
        (by rw [hwk₂' stT (by decide)]; exact hinv.state_head)
        (by rw [hwk₂' scT (by decide)]; exact hinv.scratch)
        (by rw [hwk₂' scT (by decide)]; exact hinv.scratch_head)
        (congrArg Tape.read (hwk₂' vIn (by decide)))
        (congrArg Tape.read (hwk₂' vWk (by decide)))
        (congrArg Tape.read (hwk₂' vOut (by decide)))
        (by rw [hwk₂' vIn (by decide)]; exact hinv.vin.read_ne_start hinv.wf_in)
        (by rw [hwk₂' vWk (by decide)]; exact hinv.vwk.read_ne_start hinv.wf_wk)
        (by rw [hwk₂' vOut (by decide)]; exact hinv.vout.read_ne_start hinv.wf_out)
        (by rw [hin₂, hin₁]; exact hinv.inp_read)
        (by rw [hout₂, hout₁]; exact hinv.out_read)
    cases hfind : machFind
        (bitsToSyms (Nat.toBits (decodeDesc α).w mc.state.val)).length
        (bitsToSyms (Nat.toBits (decodeDesc α).w mc.state.val))
        (keyCells (decide (mc.input.head = 0), decide ((mc.work 0).head = 0),
            decide (mc.output.head = 0))
          ((c.work vIn).read) ((c.work vWk).read) ((c.work vOut).read))
        ((takeField (takeField (groupPairs α)).2).2) with
    | some seg =>
      -- ── B1: a table entry matched ───────────────────────────────────────
      obtain ⟨c₃, t₃, ht₃, hr₃, hst₃, hscHold₃, hscHead₃, hstT₃, hdsCells₃,
          hdsHead₃lo, hdsHead₃hi, hvIn₃, hvWk₃, hvOut₃, hin₃, hout₃⟩ :=
        hcase_some seg hfind
      rw [hlenS] at hfind ht₃ hscHold₃ hscHead₃
      -- lookup correspondence
      obtain ⟨e, hpe, hmm', hlook⟩ :=
        firstMatch_lookup hq _ _ _ _ (decodeDesc α).qstart (decodeDesc α).qhalt
          hfind
      obtain ⟨-, hnb⟩ := machFind_matches _ _ _ _ _ hfind
      have hseglen : 2 * (decodeDesc α).w + 16 ≤ seg.length := hmm'.2.2
      obtain ⟨hvq', hvww, hvwo, hvdi, hvdw, hvdOut⟩ := value_slices hnb hpe
      have ha : (decodeDesc α).lookup mc.state.val mc.input.read
          ((mc.work 0).read) mc.output.read = e.act := by
        dsimp only at hlook
        rw [hsr0, hsr1, hsr2] at hlook
        exact hlook
      have hstep := toTM_step_running hh ha
      -- desc-tape cells through the match loop
      have hdsC₃ : (c₃.work dsT).cells = (c.work dsT).cells := by
        rw [hdsCells₃, hdsT₂']
      -- phase 4: apply the action
      obtain ⟨c₄, t₄, ht₄, hr₄, hst₄, hstHold₄, hstHead₄, hdsT₄, hscHold₄,
          hscHead₄, hvin₄, hvwk₄, hvout₄, hin₄, hout₄⟩ :=
        applyPhase (sim0 := mc.input) (sim1 := mc.work 0) (sim2 := mc.output)
          c₃
          ((seg.drop ((decodeDesc α).w + 6)).take ((decodeDesc α).w + 10))
          (bitsToSyms (Nat.toBits (decodeDesc α).w mc.state.val))
          ((decodeDesc α).w + 10 + 1) ((c₃.work dsT).head)
          (by omega) hdsHead₃lo
          (by rw [List.length_take, List.length_drop, hlenS]; omega)
          (fun s hs => bitsToSyms_ne_blank hs)
          hst₃
          (by rw [hvIn₃, hwk₂' vIn (by decide)]; exact hinv.vin)
          (by rw [hvWk₃, hwk₂' vWk (by decide)]; exact hinv.vwk)
          (by rw [hvOut₃, hwk₂' vOut (by decide)]; exact hinv.vout)
          hinv.wf_in hinv.wf_wk hinv.wf_out
          rfl rfl rfl
          (by rw [hstT₃, hwk₂' stT (by decide)]; exact hSt)
          (by rw [hstT₃, hwk₂' stT (by decide)]; exact hinv.state_head)
          hscHold₃ hscHead₃
          (wfCells_cells_congr hdsC₃ (Tape.HoldsExact.startInvariant hinv.desc))
          rfl
          (by rw [hin₃, hin₂, hin₁]; exact hinv.inp_read)
          (by rw [hout₃, hout₂, hout₁]; exact hinv.out_read)
      -- decode the copied action cells
      rw [hlenS] at ht₄ hstHold₄ hvin₄ hvwk₄ hvout₄
      dsimp only at hvin₄ hvwk₄ hvout₄
      have hbit : ∀ k j m, k < 10 → 1 + (decodeDesc α).w + k = j →
          2 * (decodeDesc α).w + 6 + k = m →
          cellBit ((c₃.work scT).cells j) = segBit seg m :=
        fun k j m hk hj hm =>
          hj ▸ hm ▸ scratch_cellBit_eq_segBit hk hseglen hscHold₃
      rw [hbit 4 _ (2 * (decodeDesc α).w + 10) (by omega) rfl (by omega),
        hbit 5 _ (2 * (decodeDesc α).w + 11) (by omega) rfl (by omega),
        hvdi, sanitize_dir_eq hinv.wf_in _ rfl e.act.di] at hvin₄
      rw [hbit 0 (1 + (decodeDesc α).w) (2 * (decodeDesc α).w + 6)
          (by omega) (by omega) (by omega),
        hbit 1 _ (2 * (decodeDesc α).w + 7) (by omega) rfl (by omega),
        hvww,
        hbit 6 _ (2 * (decodeDesc α).w + 12) (by omega) rfl (by omega),
        hbit 7 _ (2 * (decodeDesc α).w + 13) (by omega) rfl (by omega),
        hvdw, sanitize_dir_eq hinv.wf_wk _ rfl e.act.dw] at hvwk₄
      rw [hbit 2 _ (2 * (decodeDesc α).w + 8) (by omega) rfl (by omega),
        hbit 3 _ (2 * (decodeDesc α).w + 9) (by omega) rfl (by omega),
        hvwo,
        hbit 8 _ (2 * (decodeDesc α).w + 14) (by omega) rfl (by omega),
        hbit 9 _ (2 * (decodeDesc α).w + 15) (by omega) rfl (by omega),
        hvdOut, sanitize_dir_eq hinv.wf_out _ rfl e.act.dOut] at hvout₄
      -- assemble
      refine ⟨c₄, t₁ + t₂ + t₃ + t₄, ?_,
        reachesIn_trans _ (reachesIn_trans _ (reachesIn_trans _ hr₁ hr₂) hr₃)
          hr₄,
        hst₄, by rw [hin₄, hin₃, hin₂, hin₁],
        by rw [hout₄, hout₃, hout₂, hout₁], ?_⟩
      · -- time
        obtain ⟨M, hM3, hMeq⟩ : ∃ M, t₃ ≤ M ∧ bodyIterTime α
            = M + 30 * (groupPairs α).length + 100 :=
          ⟨_, le_trans ht₃ (Nat.mul_le_mul (by omega) (by omega)), rfl⟩
        rw [hMeq]
        omega
      · -- the invariant at the stepped configuration
        rw [hstep]
        have hminq : min e.act.q' (2 ^ (decodeDesc α).w) = e.act.q' :=
          Nat.min_eq_left (le_of_lt (parseEntry_q'_lt hpe))
        have hdsC₄ : (c₄.work dsT).cells = (c.work dsT).cells := by
          rw [hdsT₄]; exact hdsC₃
        refine ⟨hvin₄, hvwk₄, hvout₄,
          hinv.wf_in.move _, hinv.wf_wk.writeAndMove _ _,
          hinv.wf_out.writeAndMove _ _,
          Or.inl ⟨?_, ?_⟩, hstHead₄,
          holdsExact_cells_congr hdsC₄ hinv.desc, by rw [hdsT₄],
          hscHold₄, hscHead₄,
          by rw [hin₄, hin₃, hin₂, hin₁]; exact hinv.inp_read,
          by rw [hout₄, hout₃, hout₂, hout₁]; exact hinv.out_read⟩
        · exact lt_of_le_of_lt (Nat.min_le_left _ _) (parseEntry_q'_lt hpe)
        · show (c₄.work stT).HoldsExact (bitsToSyms (Nat.toBits (decodeDesc α).w
            (min e.act.q' (2 ^ (decodeDesc α).w))))
          rw [hminq, ← hvq', ← valueSlice_take seg (decodeDesc α).w]
          exact hstHold₄
    | none =>
      -- ── B2: no entry matched, the default transition fires ─────────────
      obtain ⟨c₃, t₃, ht₃, hr₃, hst₃, hvIn₃, hvWk₃, hvOut₃, hstCells₃,
          hstHead₃lo, hstHead₃hi, hdsCells₃, hdsHead₃lo, hdsHead₃hi,
          hsc0₃, hscns₃, hscHead₃lo, hscHead₃hi, hscBeyond₃, hin₃, hout₃⟩ :=
        hcase_none hfind
      rw [hlenS] at hfind ht₃ hstHead₃hi hscHead₃hi
      have ha : (decodeDesc α).lookup mc.state.val mc.input.read
          ((mc.work 0).read) mc.output.read
          = (decodeDesc α).defaultAct ((mc.work 0).read) mc.output.read := by
        have h' := noMatch_lookup hq _ _ _ _ (decodeDesc α).qstart
          (decodeDesc α).qhalt hfind
        dsimp only at h'
        rw [hsr0, hsr1, hsr2] at h'
        exact h'
      have hstep := toTM_step_running hh ha
      -- virtual tapes under the sanitized default moves
      have hvin' : VShift
          (mc.input.move (if mc.input.read = Γ.start then Dir3.right
            else Dir3.stay)) (c₃.work vIn) := by
        rw [hvIn₃, hwk₂' vIn (by decide)]
        exact vshift_default_move hinv.vin hinv.wf_in _ rfl
      have hvwk' : VShift
          ((mc.work 0).move (if (mc.work 0).read = Γ.start then Dir3.right
            else Dir3.stay)) (c₃.work vWk) := by
        rw [hvWk₃, hwk₂' vWk (by decide)]
        exact vshift_default_move hinv.vwk hinv.wf_wk _ rfl
      have hvout' : VShift
          (mc.output.move (if mc.output.read = Γ.start then Dir3.right
            else Dir3.stay)) (c₃.work vOut) := by
        rw [hvOut₃, hwk₂' vOut (by decide)]
        exact vshift_default_move hinv.vout hinv.wf_out _ rfl
      -- tape cells through the loop
      have hstC₃ : (c₃.work stT).cells = (c.work stT).cells := by
        rw [hstCells₃, hwk₂' stT (by decide)]
      have hdsC₃ : (c₃.work dsT).cells = (c.work dsT).cells := by
        rw [hdsCells₃, hdsT₂']
      -- phase 4: the default tail
      obtain ⟨c₄, t₄, ht₄, hr₄, hst₄, hstHold₄, hstHead₄, hdsT₄, hscHold₄,
          hscHead₄, hoth₄, hin₄, hout₄⟩ :=
        defaultTail c₃ ((c₃.work scT).cells)
          (bitsToSyms (Nat.toBits (decodeDesc α).w mc.state.val))
          ((c₃.work scT).head) ((c₃.work stT).head) ((c₃.work dsT).head)
          hstHead₃lo hdsHead₃lo hst₃
          hsc0₃ hscns₃
          (fun j hj => hscBeyond₃ j (by omega) (by omega))
          rfl rfl
          (holdsExact_cells_congr hstC₃ hSt)
          (fun s hs => bitsToSyms_ne_blank hs)
          rfl
          (holdsExact_cells_congr hdsC₃ hinv.desc)
          rfl
          (by rw [hin₃, hin₂, hin₁]; exact hinv.inp_read)
          (by rw [hout₃, hout₂, hout₁]; exact hinv.out_read)
          (fun i hiS hiD hiSc => by
            rcases i with ⟨iv, hv⟩
            rcases iv with _ | _ | _ | _ | _ | _ | n
            · exact hvin'.read_ne_start (hinv.wf_in.move _)
            · exact hvwk'.read_ne_start (hinv.wf_wk.move _)
            · exact hvout'.read_ne_start (hinv.wf_out.move _)
            · exact absurd rfl hiS
            · exact absurd rfl hiD
            · exact absurd rfl hiSc
            · exact absurd hv (by omega))
      rw [hlenS] at ht₄
      -- assemble
      refine ⟨c₄, t₁ + t₂ + t₃ + t₄, ?_,
        reachesIn_trans _ (reachesIn_trans _ (reachesIn_trans _ hr₁ hr₂) hr₃)
          hr₄,
        hst₄, by rw [hin₄, hin₃, hin₂, hin₁],
        by rw [hout₄, hout₃, hout₂, hout₁], ?_⟩
      · -- time
        obtain ⟨M, hM3, hMeq⟩ : ∃ M, t₃ ≤ M ∧ bodyIterTime α
            = M + 30 * (groupPairs α).length + 100 :=
          ⟨_, le_trans ht₃ (Nat.mul_le_mul (by omega) (by omega)), rfl⟩
        rw [hMeq]
        omega
      · -- the invariant at the (defaulted, halted) stepped configuration
        rw [hstep]
        have hdsC₄ : (c₄.work dsT).cells = (c.work dsT).cells := by
          rw [hdsT₄]; exact hdsC₃
        refine ⟨?_, ?_, ?_,
          hinv.wf_in.move _, hinv.wf_wk.writeAndMove _ _,
          hinv.wf_out.writeAndMove _ _,
          Or.inr ⟨rfl, hstHold₄⟩, hstHead₄,
          holdsExact_cells_congr hdsC₄ hinv.desc, by rw [hdsT₄],
          hscHold₄, hscHead₄,
          by rw [hin₄, hin₃, hin₂, hin₁]; exact hinv.inp_read,
          by rw [hout₄, hout₃, hout₂, hout₁]; exact hinv.out_read⟩
        · rw [hoth₄ vIn (by decide) (by decide) (by decide)]
          exact hvin'
        · rw [hoth₄ vWk (by decide) (by decide) (by decide)]
          show VShift ((mc.work 0).writeAndMove
            (TMDesc.readback ((mc.work 0).read)).toΓ
            (if (mc.work 0).read = Γ.start then Dir3.right else Dir3.stay))
            (c₃.work vWk)
          rw [writeAndMove_readback_eq_move hinv.wf_wk]
          exact hvwk'
        · rw [hoth₄ vOut (by decide) (by decide) (by decide)]
          show VShift (mc.output.writeAndMove
            (TMDesc.readback mc.output.read).toΓ
            (if mc.output.read = Γ.start then Dir3.right else Dir3.stay))
            (c₃.work vOut)
          rw [writeAndMove_readback_eq_move hinv.wf_out]
          exact hvout'

end TM.UTMBody

end Complexity
