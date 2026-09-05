/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Internal.BodyInternal
public import Complexitylib.Models.TuringMachine.UTM.Internal.VTape
public import Complexitylib.Models.TuringMachine.UTM.Internal.Desc

/-!
# Body machine: peek, default-move, and apply phases

Phase lemmas for the body machine's interaction with the three *virtual*
tapes (the `+1`-shift shadows of the simulated input/work/output tapes,
`VTape.lean`):

- `peek_correct` — the two-step peek captures the at-origin flags and
  restores all tapes exactly;
- `segCheck_default_step` / `segCheck_continue_step` — the no-match branch's
  sanitized default moves (trick 4) and the ordinary continue step;
- `appQ'_loop` — the overwrite copy of the new state from scratch onto the
  state tape (trick 2);
- `appAct_all` — the ten-step decode of the five 2-cell action groups
  (trick 6), transforming the three virtual tapes exactly as one sanitized
  simulated action.

`grpΓw_eq_decΓw` / `grpDir_eq_decDir` bridge the machine's 2-bit group
decoders to the description decoders in `Desc.lean`.
-/


public section

namespace Complexity

namespace TM.UTMBody

open BodyQ

-- ════════════════════════════════════════════════════════════════════════
-- Bridges to the description decoders
-- ════════════════════════════════════════════════════════════════════════

/-- The machine's 2-bit write-symbol decoder agrees with `decΓw`. -/
theorem grpΓw_eq_decΓw (b₀ b₁ : Bool) : grpΓw b₀ b₁ = decΓw [b₀, b₁] := by
  cases b₀ <;> cases b₁ <;> rfl

/-- The machine's 2-bit direction decoder agrees with `decDir`. -/
theorem grpDir_eq_decDir (b₀ b₁ : Bool) : grpDir b₀ b₁ = decDir [b₀, b₁] := by
  cases b₀ <;> cases b₁ <;> rfl

-- ════════════════════════════════════════════════════════════════════════
-- Tape helpers
-- ════════════════════════════════════════════════════════════════════════

/-- Writing back the read symbol is a no-op on the tape (at the origin the
    write itself is a structural no-op). -/
private theorem write_readBack_id {t : Tape} (h : t.head = 0 ∨ t.read ≠ Γ.start) :
    t.write (readBackWrite t.read).toΓ = t := by
  rcases h with h0 | hne
  · unfold Tape.write; rw [ite_eq_left h0]
  · rw [toΓ_readBackWrite_of_ne_start hne]
    unfold Tape.write
    by_cases h0 : t.head = 0
    · rw [ite_eq_left h0]
    · rw [ite_eq_right h0]
      have hupd : Function.update t.cells t.head t.read = t.cells :=
        Function.update_eq_self t.head t.cells
      rw [hupd]

private theorem writeAndMove_readBack_left {t : Tape} (h : t.read ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read).toΓ Dir3.left = ⟨t.head - 1, t.cells⟩ := by
  show (t.write _).move Dir3.left = _
  rw [write_readBack_id (Or.inr h)]
  rfl

private theorem writeAndMove_readBack_right {t : Tape}
    (h : t.head = 0 ∨ t.read ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read).toΓ Dir3.right = ⟨t.head + 1, t.cells⟩ := by
  show (t.write _).move Dir3.right = _
  rw [write_readBack_id h]
  rfl

private theorem writeAndMove_readBack_move {t : Tape} (h : t.read ≠ Γ.start)
    (d : Dir3) :
    t.writeAndMove (readBackWrite t.read).toΓ d = t.move d := by
  show (t.write _).move d = _
  rw [write_readBack_id (Or.inr h)]

-- ════════════════════════════════════════════════════════════════════════
-- Peek helpers
-- ════════════════════════════════════════════════════════════════════════

/-- The shadow's cell at index `sim.head` (one left of the shadow head) is
    `▷` exactly when the simulated head is at the origin. -/
private theorem vshift_cells_start_iff {sim utm : Tape} (h : VShift sim utm)
    (hwf : sim.StartInvariant) :
    utm.cells sim.head = Γ.start ↔ sim.head = 0 := by
  simp only [h.1]
  rcases sim.head with _ | (_ | q)
  · simp
  · simp
  · have hq := hwf.2 (q + 1) (by omega)
    simp [hq]

/-- The peek-left step: writing back and moving left from a shadow position
    lands the head at `sim.head` with cells preserved. -/
private theorem peek_leftstep {sim utm : Tape} (h : VShift sim utm)
    (hwf : sim.StartInvariant) :
    utm.writeAndMove (readBackWrite utm.read).toΓ
      (if utm.read = Γ.start then Dir3.right else Dir3.left)
      = ⟨sim.head, utm.cells⟩ := by
  have hr := h.read_ne_start hwf
  rw [ite_eq_right hr, writeAndMove_readBack_left hr, h.2, Nat.add_sub_cancel]

/-- The peek-right (return) step: from head `sim.head` the write-back is a
    no-op (also at the `▷` bounce) and the right move restores the shadow. -/
private theorem peek_return {sim utm : Tape} (h : VShift sim utm)
    (hwf : sim.StartInvariant) :
    (⟨sim.head, utm.cells⟩ : Tape).writeAndMove
      (readBackWrite ((⟨sim.head, utm.cells⟩ : Tape).read)).toΓ
      (if (⟨sim.head, utm.cells⟩ : Tape).read = Γ.start then Dir3.right
        else Dir3.right)
      = utm := by
  have hor : (⟨sim.head, utm.cells⟩ : Tape).head = 0 ∨
      (⟨sim.head, utm.cells⟩ : Tape).read ≠ Γ.start := by
    rcases Nat.eq_zero_or_pos sim.head with hz | hz
    · exact Or.inl hz
    · refine Or.inr fun hcon => ?_
      have := (vshift_cells_start_iff h hwf).mp hcon
      omega
  rw [ite_self, writeAndMove_readBack_right hor]
  show (⟨sim.head + 1, utm.cells⟩ : Tape) = utm
  rw [← h.2]

/-- `peek_return` with the peeked tape given by an equation (for use on
    opaque configurations). -/
private theorem peek_return' {sim utm t₁ : Tape} (h : VShift sim utm)
    (hwf : sim.StartInvariant) (ht : t₁ = ⟨sim.head, utm.cells⟩) :
    t₁.writeAndMove (readBackWrite t₁.read).toΓ
      (if t₁.read = Γ.start then Dir3.right else Dir3.right) = utm := by
  subst ht
  exact peek_return h hwf

/-- The flag the peek captures is exactly "simulated head at the origin". -/
private theorem peek_flag {sim utm : Tape} (h : VShift sim utm)
    (hwf : sim.StartInvariant) :
    decide ((⟨sim.head, utm.cells⟩ : Tape).read = Γ.start)
      = decide (sim.head = 0) := by
  refine decide_eq_decide.mpr ?_
  show utm.cells sim.head = Γ.start ↔ sim.head = 0
  exact vshift_cells_start_iff h hwf

/-- Read-parkedness for all six work tapes from the six individual facts. -/
private theorem read_ne_start_all {w : Fin 6 → Tape}
    (p0 : (w vIn).read ≠ Γ.start) (p1 : (w vWk).read ≠ Γ.start)
    (p2 : (w vOut).read ≠ Γ.start) (p3 : (w stT).read ≠ Γ.start)
    (p4 : (w dsT).read ≠ Γ.start) (p5 : (w scT).read ≠ Γ.start) :
    ∀ i, (w i).read ≠ Γ.start := by
  intro i
  fin_cases i
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5

-- ════════════════════════════════════════════════════════════════════════
-- The peek phase
-- ════════════════════════════════════════════════════════════════════════

/-- **The peek phase** (`peek1` → `peek2` → `seek1 f`): in two steps the
    body machine captures the at-origin flags of the three virtual tapes and
    restores every tape exactly. The flags are honest: the machine proceeds
    to `seek1 (decide (sim0.head = 0), decide (sim1.head = 0),
    decide (sim2.head = 0))`. -/
theorem peek_correct {c : Cfg 6 bodyTM.Q} {sim0 sim1 sim2 : Tape}
    (h0 : VShift sim0 (c.work vIn)) (h1 : VShift sim1 (c.work vWk))
    (h2 : VShift sim2 (c.work vOut))
    (hwf0 : sim0.StartInvariant) (hwf1 : sim1.StartInvariant) (hwf2 : sim2.StartInvariant)
    (hst : c.state = peek1)
    (hstT : (c.work stT).read ≠ Γ.start) (hdsT : (c.work dsT).read ≠ Γ.start)
    (hscT : (c.work scT).read ≠ Γ.start)
    (hin : c.input.read ≠ Γ.start) (hout : c.output.read ≠ Γ.start) :
    ∃ c', bodyTM.reachesIn 2 c c' ∧
      c'.state = seek1 (decide (sim0.head = 0), decide (sim1.head = 0),
        decide (sim2.head = 0)) ∧
      c'.work vIn = c.work vIn ∧ c'.work vWk = c.work vWk ∧
      c'.work vOut = c.work vOut ∧
      c'.work stT = c.work stT ∧ c'.work dsT = c.work dsT ∧
      c'.work scT = c.work scT ∧
      c'.input = c.input ∧ c'.output = c.output := by
  have hr0 := h0.read_ne_start hwf0
  have hr1 := h1.read_ne_start hwf1
  have hr2 := h2.read_ne_start hwf2
  have hoth := read_ne_start_all (w := c.work) hr0 hr1 hr2 hstT hdsT hscT
  -- step 1: all three virtual heads left
  obtain ⟨c₁, hc1, hs₁, hi₁, ho₁, hv₁0, hv₁1, hv₁2, hrest₁⟩ :
      ∃ c₁, bodyTM.step c = some c₁ ∧ c₁.state = peek2 ∧
        c₁.input = c.input ∧ c₁.output = c.output ∧
        c₁.work vIn = ⟨sim0.head, (c.work vIn).cells⟩ ∧
        c₁.work vWk = ⟨sim1.head, (c.work vWk).cells⟩ ∧
        c₁.work vOut = ⟨sim2.head, (c.work vOut).cells⟩ ∧
        ∀ i, i ≠ vIn → i ≠ vWk → i ≠ vOut → c₁.work i = c.work i := by
    refine ⟨_, step_act3 (by rw [hst]; exact fun h => nomatch h)
        (by rw [hst]
            exact arm_peek1 c.input.read (fun i => (c.work i).read) c.output.read),
      rfl, idle_input_id hin, idle_tape_id hout, ?_, ?_, ?_, ?_⟩
    · exact peek_leftstep h0 hwf0
    · exact peek_leftstep h1 hwf1
    · exact peek_leftstep h2 hwf2
    · intro i hi0 hi1 hi2
      show (if i = vIn then _ else _) = _
      rw [ite_eq_right hi0, ite_eq_right hi1, ite_eq_right hi2]
      exact idle_tape_id (hoth i)
  -- step 2: read the flags, all three virtual heads right
  obtain ⟨c₂, hc2, hs₂, hi₂, ho₂, hv₂0, hv₂1, hv₂2, hrest₂⟩ :
      ∃ c₂, bodyTM.step c₁ = some c₂ ∧
        c₂.state = seek1 (decide (sim0.head = 0), decide (sim1.head = 0),
          decide (sim2.head = 0)) ∧
        c₂.input = c.input ∧ c₂.output = c.output ∧
        c₂.work vIn = c.work vIn ∧ c₂.work vWk = c.work vWk ∧
        c₂.work vOut = c.work vOut ∧
        ∀ i, i ≠ vIn → i ≠ vWk → i ≠ vOut → c₂.work i = c₁.work i := by
    refine ⟨_, step_act3 (by rw [hs₁]; exact fun h => nomatch h)
        (by rw [hs₁]
            exact arm_peek2 c₁.input.read (fun i => (c₁.work i).read) c₁.output.read),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show seek1 _ = _
      refine congrArg seek1 ?_
      rw [hv₁0, hv₁1, hv₁2]
      simp only [Prod.mk.injEq]
      exact ⟨peek_flag h0 hwf0, peek_flag h1 hwf1, peek_flag h2 hwf2⟩
    · rw [hi₁]; exact idle_input_id hin
    · rw [ho₁]; exact idle_tape_id hout
    · exact peek_return' h0 hwf0 hv₁0
    · exact peek_return' h1 hwf1 hv₁1
    · exact peek_return' h2 hwf2 hv₁2
    · intro i hi0 hi1 hi2
      show (if i = vIn then _ else _) = _
      rw [ite_eq_right hi0, ite_eq_right hi1, ite_eq_right hi2]
      exact idle_tape_id (by rw [hrest₁ i hi0 hi1 hi2]; exact hoth i)
  refine ⟨c₂, .step hc1 (.step hc2 .zero), hs₂, hv₂0, hv₂1, hv₂2, ?_, ?_, ?_,
    hi₂, ho₂⟩
  · exact (hrest₂ stT (by decide) (by decide) (by decide)).trans
      (hrest₁ stT (by decide) (by decide) (by decide))
  · exact (hrest₂ dsT (by decide) (by decide) (by decide)).trans
      (hrest₁ dsT (by decide) (by decide) (by decide))
  · exact (hrest₂ scT (by decide) (by decide) (by decide)).trans
      (hrest₁ scT (by decide) (by decide) (by decide))

-- ════════════════════════════════════════════════════════════════════════
-- The segCheck branch
-- ════════════════════════════════════════════════════════════════════════

/-- **The no-match default step** (`segCheck f` reading `□` → `dfScr`,
    trick 4): one step applies the default action's sanitized moves to the
    three virtual tapes — right where the at-origin flag is set, stay
    otherwise — matching the interpreted machine's sanitized `stay`
    directions. All writes are read-backs; every other tape is preserved
    exactly. -/
theorem segCheck_default_step {c : Cfg 6 bodyTM.Q} {f : VFlags}
    {sim0 sim1 sim2 : Tape}
    (h0 : VShift sim0 (c.work vIn)) (h1 : VShift sim1 (c.work vWk))
    (h2 : VShift sim2 (c.work vOut))
    (hwf0 : sim0.StartInvariant) (hwf1 : sim1.StartInvariant) (hwf2 : sim2.StartInvariant)
    (hf0 : f.1 = decide (sim0.head = 0)) (hf1 : f.2.1 = decide (sim1.head = 0))
    (hf2 : f.2.2 = decide (sim2.head = 0))
    (hst : c.state = segCheck f)
    (hdc : (c.work dsT).read = Γ.blank)
    (hstT : (c.work stT).read ≠ Γ.start) (hscT : (c.work scT).read ≠ Γ.start)
    (hin : c.input.read ≠ Γ.start) (hout : c.output.read ≠ Γ.start) :
    ∃ c', bodyTM.reachesIn 1 c c' ∧ c'.state = dfScr ∧
      VShift (sim0.move (if f.1 then Dir3.right else Dir3.stay)) (c'.work vIn) ∧
      VShift (sim1.move (if f.2.1 then Dir3.right else Dir3.stay)) (c'.work vWk) ∧
      VShift (sim2.move (if f.2.2 then Dir3.right else Dir3.stay)) (c'.work vOut) ∧
      c'.work stT = c.work stT ∧ c'.work dsT = c.work dsT ∧
      c'.work scT = c.work scT ∧
      c'.input = c.input ∧ c'.output = c.output := by
  have hr0 := h0.read_ne_start hwf0
  have hr1 := h1.read_ne_start hwf1
  have hr2 := h2.read_ne_start hwf2
  have hdsT : (c.work dsT).read ≠ Γ.start := by
    rw [hdc]; exact fun h => nomatch h
  have hoth := read_ne_start_all (w := c.work) hr0 hr1 hr2 hstT hdsT hscT
  have harm := arm_segCheck c.input.read (fun i => (c.work i).read) c.output.read f
  rw [ite_eq_left hdc] at harm
  obtain ⟨c', hstep, hs, hi, ho, hv0, hv1, hv2, hrest⟩ :
      ∃ c', bodyTM.step c = some c' ∧ c'.state = dfScr ∧
        c'.input = c.input ∧ c'.output = c.output ∧
        c'.work vIn = (c.work vIn).move (if f.1 then Dir3.right else Dir3.stay) ∧
        c'.work vWk = (c.work vWk).move (if f.2.1 then Dir3.right else Dir3.stay) ∧
        c'.work vOut = (c.work vOut).move (if f.2.2 then Dir3.right else Dir3.stay) ∧
        ∀ i, i ≠ vIn → i ≠ vWk → i ≠ vOut → c'.work i = c.work i := by
    refine ⟨_, step_act3 (by rw [hst]; exact fun h => nomatch h)
        (by rw [hst]; exact harm),
      rfl, idle_input_id hin, idle_tape_id hout, ?_, ?_, ?_, ?_⟩
    · show (c.work vIn).writeAndMove (readBackWrite ((c.work vIn).read)).toΓ
        (if (c.work vIn).read = Γ.start then Dir3.right
          else if f.1 then Dir3.right else Dir3.stay) = _
      rw [ite_eq_right hr0]
      exact writeAndMove_readBack_move hr0 _
    · show (c.work vWk).writeAndMove (readBackWrite ((c.work vWk).read)).toΓ
        (if (c.work vWk).read = Γ.start then Dir3.right
          else if f.2.1 then Dir3.right else Dir3.stay) = _
      rw [ite_eq_right hr1]
      exact writeAndMove_readBack_move hr1 _
    · show (c.work vOut).writeAndMove (readBackWrite ((c.work vOut).read)).toΓ
        (if (c.work vOut).read = Γ.start then Dir3.right
          else if f.2.2 then Dir3.right else Dir3.stay) = _
      rw [ite_eq_right hr2]
      exact writeAndMove_readBack_move hr2 _
    · intro i hi0 hi1 hi2
      show (if i = vIn then _ else _) = _
      rw [ite_eq_right hi0, ite_eq_right hi1, ite_eq_right hi2]
      exact idle_tape_id (hoth i)
  refine ⟨c', .step hstep .zero, hs, ?_, ?_, ?_,
    hrest stT (by decide) (by decide) (by decide),
    hrest dsT (by decide) (by decide) (by decide),
    hrest scT (by decide) (by decide) (by decide), hi, ho⟩
  · rw [hv0]
    exact h0.move _ fun hz => by rw [hf0, decide_eq_true hz, ite_eq_left rfl]
  · rw [hv1]
    exact h1.move _ fun hz => by rw [hf1, decide_eq_true hz, ite_eq_left rfl]
  · rw [hv2]
    exact h2.move _ fun hz => by rw [hf2, decide_eq_true hz, ite_eq_left rfl]

/-- **The segCheck continue step** (`segCheck f` reading non-`□` → `mmScr f`):
    a pure control-state change — every tape is preserved exactly. -/
theorem segCheck_continue_step {c : Cfg 6 bodyTM.Q} {f : VFlags}
    (hst : c.state = segCheck f)
    (hdc : (c.work dsT).read ≠ Γ.blank)
    (hparked : ∀ i, (c.work i).read ≠ Γ.start)
    (hin : c.input.read ≠ Γ.start) (hout : c.output.read ≠ Γ.start) :
    ∃ c', bodyTM.reachesIn 1 c c' ∧ c'.state = mmScr f ∧
      (∀ i, c'.work i = c.work i) ∧ c'.input = c.input ∧ c'.output = c.output := by
  have harm := arm_segCheck c.input.read (fun i => (c.work i).read) c.output.read f
  rw [ite_eq_right hdc] at harm
  refine ⟨_, .step (step_mkAct (by rw [hst]; exact fun h => nomatch h)
      (by rw [hst]; exact harm)) .zero, rfl, ?_, idle_input_id hin,
    idle_tape_id hout⟩
  intro i
  exact idle_tape_id (hparked i)

-- ════════════════════════════════════════════════════════════════════════
-- The apply phase: state overwrite (trick 2)
-- ════════════════════════════════════════════════════════════════════════

/-- **The apply-phase state overwrite** (`appQ' f`, trick 2): with the state
    head at `a` (old cells `S`, blank at distance `n`) and the scratch head
    at `e` (cells `E`, `▷`-free), the machine copies `n` scratch symbols
    over the old state — reading the *old* state cell to know when to stop —
    then idles once on the `□` into `appAct f 0 none`. Total `n + 1` steps;
    the scratch tape and every other tape are exactly preserved. -/
theorem appQ'_loop {f : VFlags} (E : ℕ → Γ) (hEns : ∀ j, 1 ≤ j → E j ≠ Γ.start) :
    ∀ (n : ℕ) (S : ℕ → Γ), (∀ j, 1 ≤ j → S j ≠ Γ.start) →
      ∀ (a e : ℕ), 1 ≤ a → 1 ≤ e →
      (∀ j, j < n → S (a + j) ≠ Γ.blank) → S (a + n) = Γ.blank →
      ∀ c : Cfg 6 bodyTM.Q,
      c.state = appQ' f →
      (c.work stT).cells = S → (c.work stT).head = a →
      (c.work scT).cells = E → (c.work scT).head = e →
      c.input.read ≠ Γ.start → c.output.read ≠ Γ.start →
      (∀ i, i ≠ stT → i ≠ scT → (c.work i).read ≠ Γ.start) →
      ∃ c', bodyTM.reachesIn (n + 1) c c' ∧
        c'.state = appAct f 0 none ∧
        c'.work stT = ⟨a + n, fun j => if a ≤ j ∧ j < a + n then E (e + (j - a)) else S j⟩ ∧
        c'.work scT = ⟨e + n, E⟩ ∧
        c'.input = c.input ∧ c'.output = c.output ∧
        (∀ i, i ≠ stT → i ≠ scT → c'.work i = c.work i) := by
  intro n
  induction n with
  | zero =>
    intro S hSns a e ha he hnb hbl c hst hcS hheadS hcE hheadE hin hout hoth
    have hreads : (c.work stT).read = Γ.blank := by
      simp only [Tape.read, hheadS, hcS]
      simpa using hbl
    have harm := arm_appQ' c.input.read (fun i => (c.work i).read) c.output.read f
    rw [ite_eq_left hreads] at harm
    have hstep := step_mkAct (c := c)
      (by rw [hst]; exact fun hcon => nomatch hcon)
      (by rw [hst]; exact harm)
    refine ⟨_, .step hstep .zero, rfl, ?_, ?_, idle_input_id hin, idle_tape_id hout,
      fun i hi hi' => idle_tape_id (hoth i hi hi')⟩
    · show (c.work stT).writeAndMove _ _ = _
      rw [idle_tape_id (by rw [hreads]; exact fun h => nomatch h)]
      have hS : (fun j => if a ≤ j ∧ j < a + 0 then E (e + (j - a)) else S j) = S := by
        funext j
        rw [ite_eq_right (by omega)]
      rw [hS, ← hcS, show a + 0 = (c.work stT).head from by rw [hheadS]; omega]
    · show (c.work scT).writeAndMove _ _ = _
      rw [idle_tape_id (by
        simp only [Tape.read, hheadE, hcE]
        exact hEns e he)]
      rw [← hcE, show e + 0 = (c.work scT).head from by rw [hheadE]; omega]
  | succ n ih =>
    intro S hSns a e ha he hnb hbl c hst hcS hheadS hcE hheadE hin hout hoth
    have hreads : (c.work stT).read = S a := by
      simp [Tape.read, hheadS, hcS]
    have hreadnb : (c.work stT).read ≠ Γ.blank := by
      rw [hreads]
      simpa using hnb 0 (by omega)
    have hreads' : (c.work stT).read ≠ Γ.start := by
      rw [hreads]; exact hSns a ha
    have hreadsc : (c.work scT).read = E e := by
      simp [Tape.read, hheadE, hcE]
    have hreadsc' : (c.work scT).read ≠ Γ.start := by
      rw [hreadsc]; exact hEns e he
    have harm := arm_appQ' c.input.read (fun i => (c.work i).read) c.output.read f
    rw [ite_eq_right hreadnb] at harm
    have hstep := step_act2 (c := c)
      (by rw [hst]; exact fun hcon => nomatch hcon)
      (by rw [hst]; exact harm)
    have hEe : (readBackWrite ((c.work scT).read)).toΓ = E e := by
      rw [toΓ_readBackWrite_of_ne_start hreadsc', hreadsc]
    have hSupd : ∀ j, 1 ≤ j → Function.update S a (E e) j ≠ Γ.start := by
      intro j hj
      by_cases hje : j = a
      · subst hje; rw [Function.update_self]; exact hEns e he
      · rw [Function.update_of_ne hje]; exact hSns j hj
    obtain ⟨c', hreach, hst', hwtS', hwtE', hin', hout', hoth'⟩ :=
      ih (Function.update S a (E e)) hSupd (a + 1) (e + 1) (by omega) (by omega)
        (fun j hj => by
          rw [Function.update_of_ne (by omega)]
          have := hnb (j + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this)
        (by
          rw [Function.update_of_ne (by omega)]
          have : a + 1 + n = a + (n + 1) := by omega
          rw [this]; exact hbl)
        { state := appQ' f
          input := c.input.move (idleDir c.input.read)
          work := fun i =>
            if i = stT then
              (c.work i).writeAndMove (readBackWrite ((c.work scT).read)).toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.right)
            else if i = scT then
              (c.work i).writeAndMove (readBackWrite ((c.work scT).read)).toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.right)
            else (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
              (idleDir ((c.work i).read))
          output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
            (idleDir c.output.read) }
        rfl
        (by
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right hreads']
          show (((c.work stT).write _).move Dir3.right).cells = _
          have hw : (c.work stT).write (readBackWrite ((c.work scT).read)).toΓ
              = { c.work stT with
                  cells := Function.update (c.work stT).cells (c.work stT).head
                    (readBackWrite ((c.work scT).read)).toΓ } := by
            unfold Tape.write
            rw [ite_eq_right (by omega)]
          rw [hw]
          show Function.update (c.work stT).cells (c.work stT).head _ = _
          rw [hcS, hheadS, hEe])
        (by
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right hreads']
          simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hheadS])
        (by
          dsimp only
          rw [ite_eq_right (by decide : scT ≠ stT), ite_eq_left rfl, ite_eq_right hreadsc',
            tape_readBackWrite_preserves _ _ (Or.inr hreadsc'), hcE])
        (by
          dsimp only
          rw [ite_eq_right (by decide : scT ≠ stT), ite_eq_left rfl, ite_eq_right hreadsc']
          simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hheadE])
        (by dsimp only; rw [idle_input_id hin]; exact hin)
        (by dsimp only; rw [idle_tape_id hout]; exact hout)
        (fun i hi hi' => by
          dsimp only
          rw [ite_eq_right hi, ite_eq_right hi', idle_tape_id (hoth i hi hi')]
          exact hoth i hi hi')
    refine ⟨c', .step hstep hreach, hst', ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwtS']
      simp only [Tape.mk.injEq]
      refine ⟨by omega, ?_⟩
      funext j
      by_cases hj1 : a + 1 ≤ j ∧ j < a + 1 + n
      · rw [ite_eq_left hj1, ite_eq_left (by omega)]
        exact congrArg E (by omega)
      · rw [ite_eq_right hj1]
        by_cases hje : j = a
        · subst hje
          rw [Function.update_self, ite_eq_left (by omega)]
          exact congrArg E (by omega)
        · rw [Function.update_of_ne hje, ite_eq_right (by omega)]
    · rw [hwtE']
      exact congrArg (fun m => (⟨m, E⟩ : Tape)) (by omega)
    · rw [hin']; exact idle_input_id hin
    · rw [hout']; exact idle_tape_id hout
    · intro i hi hi'
      rw [hoth' i hi hi']
      show (if i = stT then _ else if i = scT then _ else _) = _
      rw [ite_eq_right hi, ite_eq_right hi']
      exact idle_tape_id (hoth i hi hi')

-- ════════════════════════════════════════════════════════════════════════
-- The apply phase: action groups (trick 6)
-- ════════════════════════════════════════════════════════════════════════

/-- One *write* action group (two steps): the none-step buffers the first
    bit from scratch, the some-step writes the decoded symbol (suppressed to
    `□` when the flag is set) on tape `t` and stays. The scratch head
    advances by two; everything else is preserved. -/
private theorem appAct_writeGroup {c : Cfg 6 bodyTM.Q} {f : VFlags} {g : Fin 5}
    {q'' : BodyQ} {t : Fin 6} {flag : Bool}
    (ht : t ≠ scT)
    (harm1 : ∀ iH wH oH, bodyδ (appAct f g none) iH wH oH
      = act1 (appAct f g (some (cellBit (wH scT)))) iH wH oH scT
          (readBackWrite (wH scT)) .right)
    (harm2 : ∀ (b₀ : Bool) (iH : Γ) (wH : Fin 6 → Γ) (oH : Γ),
      bodyδ (appAct f g (some b₀)) iH wH oH
      = act2 q'' iH wH oH scT (readBackWrite (wH scT)) .right
          t (if flag then Γw.blank else grpΓw b₀ (cellBit (wH scT))) .stay)
    (hst : c.state = appAct f g none)
    (hsc0 : (c.work scT).read ≠ Γ.start)
    (hsc1 : (c.work scT).cells ((c.work scT).head + 1) ≠ Γ.start)
    (htr : (c.work t).read ≠ Γ.start)
    (hoth : ∀ i, i ≠ scT → i ≠ t → (c.work i).read ≠ Γ.start)
    (hin : c.input.read ≠ Γ.start) (hout : c.output.read ≠ Γ.start) :
    ∃ c', bodyTM.reachesIn 2 c c' ∧ c'.state = q'' ∧
      c'.work t = (c.work t).write
        (if flag then Γw.blank
         else grpΓw (cellBit ((c.work scT).read))
           (cellBit ((c.work scT).cells ((c.work scT).head + 1)))).toΓ ∧
      c'.work scT = ⟨(c.work scT).head + 2, (c.work scT).cells⟩ ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      (∀ i, i ≠ scT → i ≠ t → c'.work i = c.work i) := by
  -- step 1: buffer the first bit, scratch right
  obtain ⟨c₁, hc1, hs₁, hi₁, ho₁, hsc₁, hoth₁⟩ :
      ∃ c₁, bodyTM.step c = some c₁ ∧
        c₁.state = appAct f g (some (cellBit ((c.work scT).read))) ∧
        c₁.input = c.input ∧ c₁.output = c.output ∧
        c₁.work scT = ⟨(c.work scT).head + 1, (c.work scT).cells⟩ ∧
        ∀ i, i ≠ scT → c₁.work i = c.work i := by
    refine ⟨_, step_act1 (by rw [hst]; exact fun h => nomatch h)
        (by rw [hst]
            exact harm1 c.input.read (fun i => (c.work i).read) c.output.read),
      rfl, idle_input_id hin, idle_tape_id hout, ?_, ?_⟩
    · show (c.work scT).writeAndMove (readBackWrite ((c.work scT).read)).toΓ
        (if (c.work scT).read = Γ.start then Dir3.right else Dir3.right) = _
      rw [ite_self]
      exact writeAndMove_readBack_right (Or.inr hsc0)
    · intro i hi
      show (if i = scT then _ else _) = _
      rw [ite_eq_right hi]
      refine idle_tape_id ?_
      by_cases hit : i = t
      · subst hit; exact htr
      · exact hoth i hi hit
  -- step 2: write the decoded symbol on tape t, scratch right
  have ht₁ : c₁.work t = c.work t := hoth₁ t ht
  obtain ⟨c₂, hc2, hs₂, hi₂, ho₂, htp₂, hsc₂, hoth₂⟩ :
      ∃ c₂, bodyTM.step c₁ = some c₂ ∧ c₂.state = q'' ∧
        c₂.input = c.input ∧ c₂.output = c.output ∧
        c₂.work t = (c.work t).write
          (if flag then Γw.blank
           else grpΓw (cellBit ((c.work scT).read))
             (cellBit ((c.work scT).cells ((c.work scT).head + 1)))).toΓ ∧
        c₂.work scT = ⟨(c.work scT).head + 2, (c.work scT).cells⟩ ∧
        ∀ i, i ≠ scT → i ≠ t → c₂.work i = c₁.work i := by
    refine ⟨_, step_act2 (by rw [hs₁]; exact fun h => nomatch h)
        (by rw [hs₁]
            exact harm2 (cellBit ((c.work scT).read)) c₁.input.read
              (fun i => (c₁.work i).read) c₁.output.read),
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hi₁]; exact idle_input_id hin
    · rw [ho₁]; exact idle_tape_id hout
    · show (if t = scT then _ else if t = t then _ else _) = _
      rw [ite_eq_right ht, ite_eq_left rfl, ht₁, hsc₁, ite_eq_right htr]
      rfl
    · show (c₁.work scT).writeAndMove (readBackWrite ((c₁.work scT).read)).toΓ
        (if (c₁.work scT).read = Γ.start then Dir3.right else Dir3.right) = _
      rw [hsc₁, ite_self]
      exact writeAndMove_readBack_right (Or.inr hsc1)
    · intro i hi hit
      show (if i = scT then _ else if i = t then _ else _) = _
      rw [ite_eq_right hi, ite_eq_right hit]
      exact idle_tape_id (by rw [hoth₁ i hi]; exact hoth i hi hit)
  exact ⟨c₂, .step hc1 (.step hc2 .zero), hs₂, htp₂, hsc₂, hi₂, ho₂,
    fun i hi hit => (hoth₂ i hi hit).trans (hoth₁ i hi)⟩

/-- One *move* action group (two steps): the none-step buffers the first
    bit, the some-step moves tape `t` by the decoded direction (forced right
    when the flag is set) with a read-back write. The scratch head advances
    by two; everything else is preserved. -/
private theorem appAct_moveGroup {c : Cfg 6 bodyTM.Q} {f : VFlags} {g : Fin 5}
    {q'' : BodyQ} {t : Fin 6} {flag : Bool}
    (ht : t ≠ scT)
    (harm1 : ∀ iH wH oH, bodyδ (appAct f g none) iH wH oH
      = act1 (appAct f g (some (cellBit (wH scT)))) iH wH oH scT
          (readBackWrite (wH scT)) .right)
    (harm2 : ∀ (b₀ : Bool) (iH : Γ) (wH : Fin 6 → Γ) (oH : Γ),
      bodyδ (appAct f g (some b₀)) iH wH oH
      = act2 q'' iH wH oH scT (readBackWrite (wH scT)) .right
          t (readBackWrite (wH t))
          (if flag then Dir3.right else grpDir b₀ (cellBit (wH scT))))
    (hst : c.state = appAct f g none)
    (hsc0 : (c.work scT).read ≠ Γ.start)
    (hsc1 : (c.work scT).cells ((c.work scT).head + 1) ≠ Γ.start)
    (htr : (c.work t).read ≠ Γ.start)
    (hoth : ∀ i, i ≠ scT → i ≠ t → (c.work i).read ≠ Γ.start)
    (hin : c.input.read ≠ Γ.start) (hout : c.output.read ≠ Γ.start) :
    ∃ c', bodyTM.reachesIn 2 c c' ∧ c'.state = q'' ∧
      c'.work t = (c.work t).move
        (if flag then Dir3.right
         else grpDir (cellBit ((c.work scT).read))
           (cellBit ((c.work scT).cells ((c.work scT).head + 1)))) ∧
      c'.work scT = ⟨(c.work scT).head + 2, (c.work scT).cells⟩ ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      (∀ i, i ≠ scT → i ≠ t → c'.work i = c.work i) := by
  -- step 1: buffer the first bit, scratch right
  obtain ⟨c₁, hc1, hs₁, hi₁, ho₁, hsc₁, hoth₁⟩ :
      ∃ c₁, bodyTM.step c = some c₁ ∧
        c₁.state = appAct f g (some (cellBit ((c.work scT).read))) ∧
        c₁.input = c.input ∧ c₁.output = c.output ∧
        c₁.work scT = ⟨(c.work scT).head + 1, (c.work scT).cells⟩ ∧
        ∀ i, i ≠ scT → c₁.work i = c.work i := by
    refine ⟨_, step_act1 (by rw [hst]; exact fun h => nomatch h)
        (by rw [hst]
            exact harm1 c.input.read (fun i => (c.work i).read) c.output.read),
      rfl, idle_input_id hin, idle_tape_id hout, ?_, ?_⟩
    · show (c.work scT).writeAndMove (readBackWrite ((c.work scT).read)).toΓ
        (if (c.work scT).read = Γ.start then Dir3.right else Dir3.right) = _
      rw [ite_self]
      exact writeAndMove_readBack_right (Or.inr hsc0)
    · intro i hi
      show (if i = scT then _ else _) = _
      rw [ite_eq_right hi]
      refine idle_tape_id ?_
      by_cases hit : i = t
      · subst hit; exact htr
      · exact hoth i hi hit
  -- step 2: move tape t by the decoded direction, scratch right
  have ht₁ : c₁.work t = c.work t := hoth₁ t ht
  obtain ⟨c₂, hc2, hs₂, hi₂, ho₂, htp₂, hsc₂, hoth₂⟩ :
      ∃ c₂, bodyTM.step c₁ = some c₂ ∧ c₂.state = q'' ∧
        c₂.input = c.input ∧ c₂.output = c.output ∧
        c₂.work t = (c.work t).move
          (if flag then Dir3.right
           else grpDir (cellBit ((c.work scT).read))
             (cellBit ((c.work scT).cells ((c.work scT).head + 1)))) ∧
        c₂.work scT = ⟨(c.work scT).head + 2, (c.work scT).cells⟩ ∧
        ∀ i, i ≠ scT → i ≠ t → c₂.work i = c₁.work i := by
    refine ⟨_, step_act2 (by rw [hs₁]; exact fun h => nomatch h)
        (by rw [hs₁]
            exact harm2 (cellBit ((c.work scT).read)) c₁.input.read
              (fun i => (c₁.work i).read) c₁.output.read),
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hi₁]; exact idle_input_id hin
    · rw [ho₁]; exact idle_tape_id hout
    · show (if t = scT then _ else if t = t then _ else _) = _
      rw [ite_eq_right ht, ite_eq_left rfl, ht₁, hsc₁, ite_eq_right htr]
      exact writeAndMove_readBack_move htr _
    · show (c₁.work scT).writeAndMove (readBackWrite ((c₁.work scT).read)).toΓ
        (if (c₁.work scT).read = Γ.start then Dir3.right else Dir3.right) = _
      rw [hsc₁, ite_self]
      exact writeAndMove_readBack_right (Or.inr hsc1)
    · intro i hi hit
      show (if i = scT then _ else if i = t then _ else _) = _
      rw [ite_eq_right hi, ite_eq_right hit]
      exact idle_tape_id (by rw [hoth₁ i hi]; exact hoth i hi hit)
  exact ⟨c₂, .step hc1 (.step hc2 .zero), hs₂, htp₂, hsc₂, hi₂, ho₂,
    fun i hi hit => (hoth₂ i hi hit).trans (hoth₁ i hi)⟩

/-- **The full apply-phase action decode** (`appAct f 0 none` → … → `clScr`,
    trick 6): ten steps consume the ten scratch action cells `E e .. E (e+9)`
    in five 2-cell groups — write `ww` on vWork (g0), write `wo` on vOut
    (g1), move vInput (g2), move vWork (g3), move vOut (g4) — each write
    suppressed to `□` and each move forced right where the corresponding
    at-origin flag is set, matching the interpreted machine's sanitized
    action exactly (note `sim.write` at the origin is itself a structural
    no-op, so the stated sim-side write is unconditional). The scratch tape
    ends at head `e + 10` with cells unchanged; the state, desc, input, and
    output tapes are preserved exactly. -/
theorem appAct_all {c : Cfg 6 bodyTM.Q} {f : VFlags} {sim0 sim1 sim2 : Tape}
    {E : ℕ → Γ} {e : ℕ}
    (h0 : VShift sim0 (c.work vIn)) (h1 : VShift sim1 (c.work vWk))
    (h2 : VShift sim2 (c.work vOut))
    (hwf0 : sim0.StartInvariant) (hwf1 : sim1.StartInvariant) (hwf2 : sim2.StartInvariant)
    (hf0 : f.1 = decide (sim0.head = 0)) (hf1 : f.2.1 = decide (sim1.head = 0))
    (hf2 : f.2.2 = decide (sim2.head = 0))
    (hst : c.state = appAct f 0 none)
    (hscC : (c.work scT).cells = E) (hscH : (c.work scT).head = e) (he : 1 ≤ e)
    (hEns : ∀ j, 1 ≤ j → E j ≠ Γ.start)
    (hstT : (c.work stT).read ≠ Γ.start) (hdsT : (c.work dsT).read ≠ Γ.start)
    (hin : c.input.read ≠ Γ.start) (hout : c.output.read ≠ Γ.start) :
    ∃ c', bodyTM.reachesIn 10 c c' ∧ c'.state = clScr ∧
      VShift (sim0.move
          (if f.1 then Dir3.right
            else grpDir (cellBit (E (e + 4))) (cellBit (E (e + 5)))))
        (c'.work vIn) ∧
      VShift (sim1.writeAndMove
          (grpΓw (cellBit (E e)) (cellBit (E (e + 1)))).toΓ
          (if f.2.1 then Dir3.right
            else grpDir (cellBit (E (e + 6))) (cellBit (E (e + 7)))))
        (c'.work vWk) ∧
      VShift (sim2.writeAndMove
          (grpΓw (cellBit (E (e + 2))) (cellBit (E (e + 3)))).toΓ
          (if f.2.2 then Dir3.right
            else grpDir (cellBit (E (e + 8))) (cellBit (E (e + 9)))))
        (c'.work vOut) ∧
      c'.work stT = c.work stT ∧ c'.work dsT = c.work dsT ∧
      c'.work scT = ⟨e + 10, E⟩ ∧
      c'.input = c.input ∧ c'.output = c.output := by
  have hr0 := h0.read_ne_start hwf0
  have hr1 := h1.read_ne_start hwf1
  have hr2 := h2.read_ne_start hwf2
  have hscR : (c.work scT).read = E e := by
    simp [Tape.read, hscH, hscC]
  have hscT0 : (c.work scT).read ≠ Γ.start := by
    rw [hscR]; exact hEns e he
  -- ── group 0: write ww on vWork ──
  obtain ⟨c₁, hre₁, hs₁, hv₁, hsc₁, hi₁, ho₁, hoth₁⟩ :=
    appAct_writeGroup (t := vWk) (flag := f.2.1) (by decide)
      (fun iH wH oH => arm_appAct_none iH wH oH f 0)
      (fun b₀ iH wH oH => arm_appAct0 iH wH oH f b₀)
      hst hscT0
      (by rw [hscC, hscH]; exact hEns (e + 1) (by omega))
      hr1
      (fun i _ _ => read_ne_start_all hr0 hr1 hr2 hstT hdsT hscT0 i)
      hin hout
  have hsc₁' : c₁.work scT = ⟨e + 2, E⟩ := by rw [hsc₁, hscH, hscC]
  have hv₁' : c₁.work vWk = (c.work vWk).write
      (if f.2.1 then Γw.blank
       else grpΓw (cellBit (E e)) (cellBit (E (e + 1)))).toΓ := by
    rw [hv₁, hscR, hscC, hscH]
  have h1w : VShift
      (sim1.write (grpΓw (cellBit (E e)) (cellBit (E (e + 1)))).toΓ)
      (c₁.work vWk) := by
    rw [hv₁']
    by_cases hz : sim1.head = 0
    · have hno : sim1.write (grpΓw (cellBit (E e)) (cellBit (E (e + 1)))).toΓ
          = sim1 := by
        unfold Tape.write
        rw [ite_eq_left hz]
      rw [hno, hf1, decide_eq_true hz, ite_eq_left rfl]
      exact h1.write_origin hz
    · rw [hf1, decide_eq_false hz, ite_eq_right Bool.false_ne_true]
      exact h1.write _ (by omega)
  have hwf1w : (sim1.write (grpΓw (cellBit (E e)) (cellBit (E (e + 1)))).toΓ).StartInvariant :=
    hwf1.write _
  have hr1w := h1w.read_ne_start hwf1w
  have hIn₁ : c₁.work vIn = c.work vIn := hoth₁ vIn (by decide) (by decide)
  have hOut₁ : c₁.work vOut = c.work vOut := hoth₁ vOut (by decide) (by decide)
  have hSt₁ : c₁.work stT = c.work stT := hoth₁ stT (by decide) (by decide)
  have hDs₁ : c₁.work dsT = c.work dsT := hoth₁ dsT (by decide) (by decide)
  -- ── group 1: write wo on vOut ──
  obtain ⟨c₂, hre₂, hs₂, hv₂, hsc₂, hi₂, ho₂, hoth₂⟩ :=
    appAct_writeGroup (t := vOut) (flag := f.2.2) (by decide)
      (fun iH wH oH => arm_appAct_none iH wH oH f 1)
      (fun b₀ iH wH oH => arm_appAct1 iH wH oH f b₀)
      hs₁
      (by rw [hsc₁']; exact hEns (e + 2) (by omega))
      (by rw [hsc₁']; exact hEns (e + 3) (by omega))
      (by rw [hOut₁]; exact hr2)
      (fun i _ _ => read_ne_start_all (by rw [hIn₁]; exact hr0) hr1w
        (by rw [hOut₁]; exact hr2) (by rw [hSt₁]; exact hstT)
        (by rw [hDs₁]; exact hdsT)
        (by rw [hsc₁']; exact hEns (e + 2) (by omega)) i)
      (by rw [hi₁]; exact hin) (by rw [ho₁]; exact hout)
  have hsc₂' : c₂.work scT = ⟨e + 4, E⟩ := by rw [hsc₂, hsc₁']
  have hv₂' : c₂.work vOut = (c.work vOut).write
      (if f.2.2 then Γw.blank
       else grpΓw (cellBit (E (e + 2))) (cellBit (E (e + 3)))).toΓ := by
    rw [hv₂, hOut₁, hsc₁']
    rfl
  have h2w : VShift
      (sim2.write (grpΓw (cellBit (E (e + 2))) (cellBit (E (e + 3)))).toΓ)
      (c₂.work vOut) := by
    rw [hv₂']
    by_cases hz : sim2.head = 0
    · have hno : sim2.write (grpΓw (cellBit (E (e + 2))) (cellBit (E (e + 3)))).toΓ
          = sim2 := by
        unfold Tape.write
        rw [ite_eq_left hz]
      rw [hno, hf2, decide_eq_true hz, ite_eq_left rfl]
      exact h2.write_origin hz
    · rw [hf2, decide_eq_false hz, ite_eq_right Bool.false_ne_true]
      exact h2.write _ (by omega)
  have hwf2w :
      (sim2.write (grpΓw (cellBit (E (e + 2))) (cellBit (E (e + 3)))).toΓ).StartInvariant :=
    hwf2.write _
  have hr2w := h2w.read_ne_start hwf2w
  have hIn₂ : c₂.work vIn = c.work vIn := (hoth₂ vIn (by decide) (by decide)).trans hIn₁
  have hWk₂ : c₂.work vWk = c₁.work vWk := hoth₂ vWk (by decide) (by decide)
  have hSt₂ : c₂.work stT = c.work stT := (hoth₂ stT (by decide) (by decide)).trans hSt₁
  have hDs₂ : c₂.work dsT = c.work dsT := (hoth₂ dsT (by decide) (by decide)).trans hDs₁
  have hi₂' : c₂.input = c.input := hi₂.trans hi₁
  have ho₂' : c₂.output = c.output := ho₂.trans ho₁
  -- ── group 2: move vInput ──
  obtain ⟨c₃, hre₃, hs₃, hv₃, hsc₃, hi₃, ho₃, hoth₃⟩ :=
    appAct_moveGroup (t := vIn) (flag := f.1) (by decide)
      (fun iH wH oH => arm_appAct_none iH wH oH f 2)
      (fun b₀ iH wH oH => arm_appAct2 iH wH oH f b₀)
      hs₂
      (by rw [hsc₂']; exact hEns (e + 4) (by omega))
      (by rw [hsc₂']; exact hEns (e + 5) (by omega))
      (by rw [hIn₂]; exact hr0)
      (fun i _ _ => read_ne_start_all (by rw [hIn₂]; exact hr0)
        (by rw [hWk₂]; exact hr1w) hr2w (by rw [hSt₂]; exact hstT)
        (by rw [hDs₂]; exact hdsT)
        (by rw [hsc₂']; exact hEns (e + 4) (by omega)) i)
      (by rw [hi₂']; exact hin) (by rw [ho₂']; exact hout)
  have hsc₃' : c₃.work scT = ⟨e + 6, E⟩ := by rw [hsc₃, hsc₂']
  have hv₃' : c₃.work vIn = (c.work vIn).move
      (if f.1 then Dir3.right
       else grpDir (cellBit (E (e + 4))) (cellBit (E (e + 5)))) := by
    rw [hv₃, hIn₂, hsc₂']
    rfl
  have h0m : VShift (sim0.move
      (if f.1 then Dir3.right
        else grpDir (cellBit (E (e + 4))) (cellBit (E (e + 5)))))
      (c₃.work vIn) := by
    rw [hv₃']
    exact h0.move _ fun hz => by rw [hf0, decide_eq_true hz, ite_eq_left rfl]
  have hwf0m : (sim0.move
      (if f.1 then Dir3.right
        else grpDir (cellBit (E (e + 4))) (cellBit (E (e + 5))))).StartInvariant :=
    hwf0.move _
  have hr0m := h0m.read_ne_start hwf0m
  have hWk₃ : c₃.work vWk = c₁.work vWk := (hoth₃ vWk (by decide) (by decide)).trans hWk₂
  have hOut₃ : c₃.work vOut = c₂.work vOut := hoth₃ vOut (by decide) (by decide)
  have hSt₃ : c₃.work stT = c.work stT := (hoth₃ stT (by decide) (by decide)).trans hSt₂
  have hDs₃ : c₃.work dsT = c.work dsT := (hoth₃ dsT (by decide) (by decide)).trans hDs₂
  have hi₃' : c₃.input = c.input := hi₃.trans hi₂'
  have ho₃' : c₃.output = c.output := ho₃.trans ho₂'
  -- ── group 3: move vWork ──
  obtain ⟨c₄, hre₄, hs₄, hv₄, hsc₄, hi₄, ho₄, hoth₄⟩ :=
    appAct_moveGroup (t := vWk) (flag := f.2.1) (by decide)
      (fun iH wH oH => arm_appAct_none iH wH oH f 3)
      (fun b₀ iH wH oH => arm_appAct3 iH wH oH f b₀)
      hs₃
      (by rw [hsc₃']; exact hEns (e + 6) (by omega))
      (by rw [hsc₃']; exact hEns (e + 7) (by omega))
      (by rw [hWk₃]; exact hr1w)
      (fun i _ _ => read_ne_start_all hr0m (by rw [hWk₃]; exact hr1w)
        (by rw [hOut₃]; exact hr2w) (by rw [hSt₃]; exact hstT)
        (by rw [hDs₃]; exact hdsT)
        (by rw [hsc₃']; exact hEns (e + 6) (by omega)) i)
      (by rw [hi₃']; exact hin) (by rw [ho₃']; exact hout)
  have hsc₄' : c₄.work scT = ⟨e + 8, E⟩ := by rw [hsc₄, hsc₃']
  have hv₄' : c₄.work vWk
      = ((c.work vWk).write (if f.2.1 then Γw.blank
          else grpΓw (cellBit (E e)) (cellBit (E (e + 1)))).toΓ).move
        (if f.2.1 then Dir3.right
          else grpDir (cellBit (E (e + 6))) (cellBit (E (e + 7)))) := by
    rw [hv₄, hWk₃, hv₁', hsc₃']
    rfl
  have h1m : VShift
      ((sim1.write (grpΓw (cellBit (E e)) (cellBit (E (e + 1)))).toΓ).move
        (if f.2.1 then Dir3.right
          else grpDir (cellBit (E (e + 6))) (cellBit (E (e + 7)))))
      (c₄.work vWk) := by
    rw [hv₄', ← hv₁']
    exact h1w.move _ fun hz => by
      rw [Tape.write_head] at hz
      rw [hf1, decide_eq_true hz, ite_eq_left rfl]
  have hwf1m : ((sim1.write (grpΓw (cellBit (E e)) (cellBit (E (e + 1)))).toΓ).move
      (if f.2.1 then Dir3.right
        else grpDir (cellBit (E (e + 6))) (cellBit (E (e + 7))))).StartInvariant :=
    hwf1w.move _
  have hr1m := h1m.read_ne_start hwf1m
  have hIn₄ : c₄.work vIn = c₃.work vIn := hoth₄ vIn (by decide) (by decide)
  have hOut₄ : c₄.work vOut = c₂.work vOut := (hoth₄ vOut (by decide) (by decide)).trans hOut₃
  have hSt₄ : c₄.work stT = c.work stT := (hoth₄ stT (by decide) (by decide)).trans hSt₃
  have hDs₄ : c₄.work dsT = c.work dsT := (hoth₄ dsT (by decide) (by decide)).trans hDs₃
  have hi₄' : c₄.input = c.input := hi₄.trans hi₃'
  have ho₄' : c₄.output = c.output := ho₄.trans ho₃'
  -- ── group 4: move vOut, exit to cleanup ──
  obtain ⟨c₅, hre₅, hs₅, hv₅, hsc₅, hi₅, ho₅, hoth₅⟩ :=
    appAct_moveGroup (t := vOut) (flag := f.2.2) (by decide)
      (fun iH wH oH => arm_appAct_none iH wH oH f 4)
      (fun b₀ iH wH oH => arm_appAct4 iH wH oH f b₀)
      hs₄
      (by rw [hsc₄']; exact hEns (e + 8) (by omega))
      (by rw [hsc₄']; exact hEns (e + 9) (by omega))
      (by rw [hOut₄]; exact hr2w)
      (fun i _ _ => read_ne_start_all (by rw [hIn₄]; exact hr0m) hr1m
        (by rw [hOut₄]; exact hr2w) (by rw [hSt₄]; exact hstT)
        (by rw [hDs₄]; exact hdsT)
        (by rw [hsc₄']; exact hEns (e + 8) (by omega)) i)
      (by rw [hi₄']; exact hin) (by rw [ho₄']; exact hout)
  have hsc₅' : c₅.work scT = ⟨e + 10, E⟩ := by rw [hsc₅, hsc₄']
  have hv₅' : c₅.work vOut
      = ((c.work vOut).write (if f.2.2 then Γw.blank
          else grpΓw (cellBit (E (e + 2))) (cellBit (E (e + 3)))).toΓ).move
        (if f.2.2 then Dir3.right
          else grpDir (cellBit (E (e + 8))) (cellBit (E (e + 9)))) := by
    rw [hv₅, hOut₄, hv₂', hsc₄']
    rfl
  have h2m : VShift
      ((sim2.write (grpΓw (cellBit (E (e + 2))) (cellBit (E (e + 3)))).toΓ).move
        (if f.2.2 then Dir3.right
          else grpDir (cellBit (E (e + 8))) (cellBit (E (e + 9)))))
      (c₅.work vOut) := by
    rw [hv₅', ← hv₂']
    exact h2w.move _ fun hz => by
      rw [Tape.write_head] at hz
      rw [hf2, decide_eq_true hz, ite_eq_left rfl]
  -- ── assembly ──
  refine ⟨c₅, ?_, hs₅, ?_, ?_, h2m, ?_, ?_, hsc₅',
    hi₅.trans hi₄', ho₅.trans ho₄'⟩
  · exact bodyTM.reachesIn_trans hre₁ (bodyTM.reachesIn_trans hre₂
      (bodyTM.reachesIn_trans hre₃ (bodyTM.reachesIn_trans hre₄ hre₅)))
  · rw [(hoth₅ vIn (by decide) (by decide)).trans hIn₄]
    exact h0m
  · rw [hoth₅ vWk (by decide) (by decide)]
    exact h1m
  · exact (hoth₅ stT (by decide) (by decide)).trans hSt₄
  · exact (hoth₅ dsT (by decide) (by decide)).trans hDs₄

end TM.UTMBody

end Complexity
