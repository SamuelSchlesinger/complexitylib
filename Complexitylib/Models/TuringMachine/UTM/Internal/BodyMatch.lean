/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Internal.BodyInternal

/-!
# Body machine: match-phase loop lemmas

Closed-form loop lemmas for the body machine's match phase (design appendix,
phases 0 and 3): the halt-check lockstep compare (`hc1`), the key-scan
state-field compare (`cmpQ`), the six key-symbol cells (`cmpS`), the
q'-field countdown copy (`copyQ'`, trick 1), and the ten action cells
(`copyAct`).

All lemmas follow the ghost-cell style of `BodyInternal.lean`: tape contents
are given as cell functions with `▷`-freeness hypotheses, every idle tape is
exactly preserved (`idle_tape_id` frames), and scratch extension is stated
as an update-on-an-interval of the ghost cells (as in `dfCopy_loop`).
-/


public section

namespace Complexity

namespace TM.UTMBody

open BodyQ

-- ════════════════════════════════════════════════════════════════════════
-- Step helpers
-- ════════════════════════════════════════════════════════════════════════

/-- One step whose arm is `idle q'` changes only the control state, provided
    every head reads a non-`▷` symbol. -/
theorem step_idle {c : Cfg 6 bodyTM.Q} (hne : c.state ≠ bodyDone) {q' : BodyQ}
    (h : bodyδ c.state c.input.read (fun i => (c.work i).read) c.output.read
      = idle q' c.input.read (fun i => (c.work i).read) c.output.read)
    (hin : c.input.read ≠ Γ.start) (hout : c.output.read ≠ Γ.start)
    (hwk : ∀ i, (c.work i).read ≠ Γ.start) :
    bodyTM.step c = some { c with state := q' } := by
  rw [step_mkAct hne h]
  refine congrArg some ?_
  refine Cfg.ext ?_ ?_ ?_ ?_
  · rfl
  · exact idle_input_id hin
  · exact funext fun i => idle_tape_id (hwk i)
  · exact idle_tape_id hout

/-- Writing back a non-`▷` read leaves the cells unchanged (write-only form
    of `tape_readBackWrite_preserves`). -/
theorem write_readBack_cells {t : Tape} (h : t.read ≠ Γ.start) :
    (t.write (readBackWrite t.read).toΓ).cells = t.cells := by
  have hp := tape_readBackWrite_preserves t Dir3.stay (Or.inr h)
  simpa [Tape.writeAndMove, Tape.move] using hp

-- ════════════════════════════════════════════════════════════════════════
-- Generic lockstep compare loop
-- ════════════════════════════════════════════════════════════════════════

/-- **Generic lockstep compare loop** for any state whose transition, on
    agreeing non-`□` state/desc reads, steps both the state and desc heads
    right and stays in `cur` (the shape shared by `hc1` and `cmpQ f`):
    while the state tape (ghost cells `S`, head from `a`) and the desc tape
    (ghost cells `W`, head from `b`) agree on `n` non-`□` symbols, the
    machine advances both heads `n` cells in `n` steps. All cells and every
    other tape are exactly preserved. -/
theorem lockstep_agree_loop {cur : BodyQ} (hcur : cur ≠ bodyDone)
    (hδ : ∀ iH wH oH, wH stT ≠ Γ.blank → wH dsT ≠ Γ.blank → wH stT = wH dsT →
      bodyδ cur iH wH oH
        = act2 cur iH wH oH stT (readBackWrite (wH stT)) .right
            dsT (readBackWrite (wH dsT)) .right)
    (S W : ℕ → Γ) (hSns : ∀ j, 1 ≤ j → S j ≠ Γ.start)
    (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start) :
    ∀ (n a b : ℕ), 1 ≤ a → 1 ≤ b →
      (∀ j, j < n → S (a + j) = W (b + j) ∧ S (a + j) ≠ Γ.blank) →
      ∀ c : Cfg 6 bodyTM.Q,
      c.state = cur →
      (c.work stT).cells = S → (c.work stT).head = a →
      (c.work dsT).cells = W → (c.work dsT).head = b →
      c.input.read ≠ Γ.start → c.output.read ≠ Γ.start →
      (∀ i, i ≠ stT → i ≠ dsT → (c.work i).read ≠ Γ.start) →
      ∃ c', bodyTM.reachesIn n c c' ∧
        c'.state = cur ∧
        c'.work stT = ⟨a + n, S⟩ ∧
        c'.work dsT = ⟨b + n, W⟩ ∧
        c'.input = c.input ∧ c'.output = c.output ∧
        (∀ i, i ≠ stT → i ≠ dsT → c'.work i = c.work i) := by
  intro n
  induction n with
  | zero =>
    intro a b ha hb hagree c hst hcS hheadS hcW hheadW hin hout hoth
    exact ⟨c, .zero, hst,
      by rw [← hcS, show a + 0 = (c.work stT).head from by omega],
      by rw [← hcW, show b + 0 = (c.work dsT).head from by omega],
      rfl, rfl, fun _ _ _ => rfl⟩
  | succ n ih =>
    intro a b ha hb hagree c hst hcS hheadS hcW hheadW hin hout hoth
    have hreadS : (c.work stT).read = S a := by simp [Tape.read, hheadS, hcS]
    have hreadW : (c.work dsT).read = W b := by simp [Tape.read, hheadW, hcW]
    have h0 := hagree 0 (by omega)
    rw [Nat.add_zero, Nat.add_zero] at h0
    have hSnb : (c.work stT).read ≠ Γ.blank := by rw [hreadS]; exact h0.2
    have hWnb : (c.work dsT).read ≠ Γ.blank := by
      rw [hreadW, ← h0.1]; exact h0.2
    have heqSW : (c.work stT).read = (c.work dsT).read := by
      rw [hreadS, hreadW]; exact h0.1
    have hreadS' : (c.work stT).read ≠ Γ.start := by
      rw [hreadS]; exact hSns a ha
    have hreadW' : (c.work dsT).read ≠ Γ.start := by
      rw [hreadW]; exact hWns b hb
    have harm := hδ c.input.read (fun i => (c.work i).read) c.output.read
      hSnb hWnb heqSW
    have hstep := step_act2 (by rw [hst]; exact hcur) (by rw [hst]; exact harm)
    obtain ⟨c', hreach, hst', hwtS', hwtD', hin', hout', hoth'⟩ :=
      ih (a + 1) (b + 1) (by omega) (by omega)
        (fun j hj => by
          have h := hagree (j + 1) (by omega)
          have e1 : a + (j + 1) = a + 1 + j := by omega
          have e2 : b + (j + 1) = b + 1 + j := by omega
          rw [e1, e2] at h
          exact h)
        { state := cur
          input := c.input.move (idleDir c.input.read)
          work := fun i =>
            if i = stT then
              (c.work i).writeAndMove (readBackWrite ((c.work stT).read)).toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.right)
            else if i = dsT then
              (c.work i).writeAndMove (readBackWrite ((c.work dsT).read)).toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.right)
            else (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
              (idleDir ((c.work i).read))
          output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
            (idleDir c.output.read) }
        rfl
        (by
          dsimp only
          rw [ite_eq_left rfl,
            tape_readBackWrite_preserves _ _ (Or.inr hreadS'), hcS])
        (by
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right hreadS']
          simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hheadS])
        (by
          dsimp only
          rw [ite_eq_right (by decide : dsT ≠ stT), ite_eq_left rfl,
            tape_readBackWrite_preserves _ _ (Or.inr hreadW'), hcW])
        (by
          dsimp only
          rw [ite_eq_right (by decide : dsT ≠ stT), ite_eq_left rfl, ite_eq_right hreadW']
          simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hheadW])
        (by dsimp only; rw [idle_input_id hin]; exact hin)
        (by dsimp only; rw [idle_tape_id hout]; exact hout)
        (fun i hi hi' => by
          dsimp only
          rw [ite_eq_right hi, ite_eq_right hi', idle_tape_id (hoth i hi hi')]
          exact hoth i hi hi')
    refine ⟨c', .step hstep hreach, hst', ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwtS']
      exact congrArg (fun m => (⟨m, S⟩ : Tape)) (by omega)
    · rw [hwtD']
      exact congrArg (fun m => (⟨m, W⟩ : Tape)) (by omega)
    · rw [hin']; exact idle_input_id hin
    · rw [hout']; exact idle_tape_id hout
    · intro i hi hi'
      rw [hoth' i hi hi']
      show (if i = stT then _ else if i = dsT then _ else _) = _
      rw [ite_eq_right hi, ite_eq_right hi']
      exact idle_tape_id (hoth i hi hi')

-- ════════════════════════════════════════════════════════════════════════
-- 1. Halt check: hc1 lockstep compare
-- ════════════════════════════════════════════════════════════════════════

/-- **Halt-check compare, match case**: from `hc1` with the state tape
    (ghost `S`, head `a`) and desc tape (ghost `W`, head `b`) agreeing on
    `n` non-`□` symbols and then both hitting `□` simultaneously, reach
    `haltRewS` in `n + 1` steps with heads at `a + n` and `b + n`. All
    cells and every other tape are exactly preserved. -/
theorem hc1_match_loop (S W : ℕ → Γ)
    (hSns : ∀ j, 1 ≤ j → S j ≠ Γ.start) (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start)
    (n a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hagree : ∀ j, j < n → S (a + j) = W (b + j) ∧ S (a + j) ≠ Γ.blank)
    (hSbl : S (a + n) = Γ.blank) (hWbl : W (b + n) = Γ.blank)
    (c : Cfg 6 bodyTM.Q)
    (hst : c.state = hc1)
    (hcS : (c.work stT).cells = S) (hheadS : (c.work stT).head = a)
    (hcW : (c.work dsT).cells = W) (hheadW : (c.work dsT).head = b)
    (hin : c.input.read ≠ Γ.start) (hout : c.output.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ stT → i ≠ dsT → (c.work i).read ≠ Γ.start) :
    ∃ c', bodyTM.reachesIn (n + 1) c c' ∧
      c'.state = haltRewS ∧
      c'.work stT = ⟨a + n, S⟩ ∧
      c'.work dsT = ⟨b + n, W⟩ ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      (∀ i, i ≠ stT → i ≠ dsT → c'.work i = c.work i) := by
  obtain ⟨c₁, hreach₁, hst₁, hwtS₁, hwtD₁, hin₁, hout₁, hoth₁⟩ :=
    lockstep_agree_loop (cur := hc1) (fun hcon => nomatch hcon)
      (fun iH wH oH hs hd he => by
        have h1 : ¬(wH stT = Γ.blank ∧ wH dsT = Γ.blank) := fun hcon => hs hcon.1
        rw [arm_hc1 iH wH oH, ite_eq_right h1, ite_eq_left ⟨hs, hd, he⟩])
      S W hSns hWns n a b ha hb hagree c hst hcS hheadS hcW hheadW hin hout hoth
  have hreadS₁ : (c₁.work stT).read = Γ.blank := by
    rw [hwtS₁]; exact hSbl
  have hreadW₁ : (c₁.work dsT).read = Γ.blank := by
    rw [hwtD₁]; exact hWbl
  have harm := arm_hc1 c₁.input.read (fun i => (c₁.work i).read) c₁.output.read
  rw [ite_eq_left ⟨hreadS₁, hreadW₁⟩] at harm
  have hwk₁ : ∀ i, (c₁.work i).read ≠ Γ.start := by
    intro i
    by_cases hiS : i = stT
    · subst hiS; rw [hreadS₁]; simp
    · by_cases hiD : i = dsT
      · subst hiD; rw [hreadW₁]; simp
      · rw [hoth₁ i hiS hiD]; exact hoth i hiS hiD
  have hstep := step_idle (by rw [hst₁]; exact fun hcon => nomatch hcon)
    (by rw [hst₁]; exact harm)
    (by rw [hin₁]; exact hin) (by rw [hout₁]; exact hout) hwk₁
  exact ⟨_, reachesIn_trans _ hreach₁ (.step hstep .zero), rfl,
    hwtS₁, hwtD₁, hin₁, hout₁, hoth₁⟩

/-- **Halt-check compare, mismatch case**: same lockstep compare as
    `hc1_match_loop`, but at offset `n` the two tapes disagree for the first
    time (not both `□`, and not both-non-`□`-and-equal): reach `preRewS` in
    `n + 1` steps with heads at `a + n` and `b + n`. All cells and every
    other tape are exactly preserved. -/
theorem hc1_mismatch_loop (S W : ℕ → Γ)
    (hSns : ∀ j, 1 ≤ j → S j ≠ Γ.start) (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start)
    (n a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hagree : ∀ j, j < n → S (a + j) = W (b + j) ∧ S (a + j) ≠ Γ.blank)
    (hmm1 : ¬(S (a + n) = Γ.blank ∧ W (b + n) = Γ.blank))
    (hmm2 : ¬(S (a + n) ≠ Γ.blank ∧ W (b + n) ≠ Γ.blank ∧ S (a + n) = W (b + n)))
    (c : Cfg 6 bodyTM.Q)
    (hst : c.state = hc1)
    (hcS : (c.work stT).cells = S) (hheadS : (c.work stT).head = a)
    (hcW : (c.work dsT).cells = W) (hheadW : (c.work dsT).head = b)
    (hin : c.input.read ≠ Γ.start) (hout : c.output.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ stT → i ≠ dsT → (c.work i).read ≠ Γ.start) :
    ∃ c', bodyTM.reachesIn (n + 1) c c' ∧
      c'.state = preRewS ∧
      c'.work stT = ⟨a + n, S⟩ ∧
      c'.work dsT = ⟨b + n, W⟩ ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      (∀ i, i ≠ stT → i ≠ dsT → c'.work i = c.work i) := by
  obtain ⟨c₁, hreach₁, hst₁, hwtS₁, hwtD₁, hin₁, hout₁, hoth₁⟩ :=
    lockstep_agree_loop (cur := hc1) (fun hcon => nomatch hcon)
      (fun iH wH oH hs hd he => by
        have h1 : ¬(wH stT = Γ.blank ∧ wH dsT = Γ.blank) := fun hcon => hs hcon.1
        rw [arm_hc1 iH wH oH, ite_eq_right h1, ite_eq_left ⟨hs, hd, he⟩])
      S W hSns hWns n a b ha hb hagree c hst hcS hheadS hcW hheadW hin hout hoth
  have hreadS₁ : (c₁.work stT).read = S (a + n) := by rw [hwtS₁]; rfl
  have hreadW₁ : (c₁.work dsT).read = W (b + n) := by rw [hwtD₁]; rfl
  have hc1' : ¬((c₁.work stT).read = Γ.blank ∧ (c₁.work dsT).read = Γ.blank) := by
    rw [hreadS₁, hreadW₁]; exact hmm1
  have hc2' : ¬((c₁.work stT).read ≠ Γ.blank ∧ (c₁.work dsT).read ≠ Γ.blank ∧
      (c₁.work stT).read = (c₁.work dsT).read) := by
    rw [hreadS₁, hreadW₁]; exact hmm2
  have harm := arm_hc1 c₁.input.read (fun i => (c₁.work i).read) c₁.output.read
  rw [ite_eq_right hc1', ite_eq_right hc2'] at harm
  have hwk₁ : ∀ i, (c₁.work i).read ≠ Γ.start := by
    intro i
    by_cases hiS : i = stT
    · subst hiS; rw [hreadS₁]; exact hSns (a + n) (by omega)
    · by_cases hiD : i = dsT
      · subst hiD; rw [hreadW₁]; exact hWns (b + n) (by omega)
      · rw [hoth₁ i hiS hiD]; exact hoth i hiS hiD
  have hstep := step_idle (by rw [hst₁]; exact fun hcon => nomatch hcon)
    (by rw [hst₁]; exact harm)
    (by rw [hin₁]; exact hin) (by rw [hout₁]; exact hout) hwk₁
  exact ⟨_, reachesIn_trans _ hreach₁ (.step hstep .zero), rfl,
    hwtS₁, hwtD₁, hin₁, hout₁, hoth₁⟩

-- ════════════════════════════════════════════════════════════════════════
-- 2. Key scan: cmpQ lockstep compare
-- ════════════════════════════════════════════════════════════════════════

/-- **Key-field compare, match case**: from `cmpQ f` with the state tape
    (ghost `S`, head `a`) and desc tape (ghost `W`, head `b`) agreeing on
    `n` non-`□` symbols, and the state tape hitting `□` at offset `n` (the
    state's key part is consumed — the exit fires regardless of the desc
    symbol), reach `cmpS f 0` in `n + 1` steps with heads at `a + n` and
    `b + n` (the exit step moves neither head). All cells and every other
    tape are exactly preserved. -/
theorem cmpQ_match_loop (f : VFlags) (S W : ℕ → Γ)
    (hSns : ∀ j, 1 ≤ j → S j ≠ Γ.start) (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start)
    (n a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hagree : ∀ j, j < n → S (a + j) = W (b + j) ∧ S (a + j) ≠ Γ.blank)
    (hSbl : S (a + n) = Γ.blank)
    (c : Cfg 6 bodyTM.Q)
    (hst : c.state = cmpQ f)
    (hcS : (c.work stT).cells = S) (hheadS : (c.work stT).head = a)
    (hcW : (c.work dsT).cells = W) (hheadW : (c.work dsT).head = b)
    (hin : c.input.read ≠ Γ.start) (hout : c.output.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ stT → i ≠ dsT → (c.work i).read ≠ Γ.start) :
    ∃ c', bodyTM.reachesIn (n + 1) c c' ∧
      c'.state = cmpS f 0 ∧
      c'.work stT = ⟨a + n, S⟩ ∧
      c'.work dsT = ⟨b + n, W⟩ ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      (∀ i, i ≠ stT → i ≠ dsT → c'.work i = c.work i) := by
  obtain ⟨c₁, hreach₁, hst₁, hwtS₁, hwtD₁, hin₁, hout₁, hoth₁⟩ :=
    lockstep_agree_loop (cur := cmpQ f) (fun hcon => nomatch hcon)
      (fun iH wH oH hs hd he => by
        rw [arm_cmpQ iH wH oH f, ite_eq_right hs, ite_eq_left ⟨hd, he⟩])
      S W hSns hWns n a b ha hb hagree c hst hcS hheadS hcW hheadW hin hout hoth
  have hreadS₁ : (c₁.work stT).read = Γ.blank := by rw [hwtS₁]; exact hSbl
  have hreadW₁ : (c₁.work dsT).read = W (b + n) := by rw [hwtD₁]; rfl
  have harm := arm_cmpQ c₁.input.read (fun i => (c₁.work i).read) c₁.output.read f
  rw [ite_eq_left hreadS₁] at harm
  have hwk₁ : ∀ i, (c₁.work i).read ≠ Γ.start := by
    intro i
    by_cases hiS : i = stT
    · subst hiS; rw [hreadS₁]; simp
    · by_cases hiD : i = dsT
      · subst hiD; rw [hreadW₁]; exact hWns (b + n) (by omega)
      · rw [hoth₁ i hiS hiD]; exact hoth i hiS hiD
  have hstep := step_idle (by rw [hst₁]; exact fun hcon => nomatch hcon)
    (by rw [hst₁]; exact harm)
    (by rw [hin₁]; exact hin) (by rw [hout₁]; exact hout) hwk₁
  exact ⟨_, reachesIn_trans _ hreach₁ (.step hstep .zero), rfl,
    hwtS₁, hwtD₁, hin₁, hout₁, hoth₁⟩

/-- **Key-field compare, mismatch case**: same lockstep compare as
    `cmpQ_match_loop`, but at offset `n` the state symbol is non-`□` and
    fails to match the desc symbol (desc `□` or different): reach
    `skipSeg f` in `n + 1` steps with heads at `a + n` and `b + n` (the
    exit step moves neither head). All cells and every other tape are
    exactly preserved. -/
theorem cmpQ_mismatch_loop (f : VFlags) (S W : ℕ → Γ)
    (hSns : ∀ j, 1 ≤ j → S j ≠ Γ.start) (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start)
    (n a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hagree : ∀ j, j < n → S (a + j) = W (b + j) ∧ S (a + j) ≠ Γ.blank)
    (hSnb : S (a + n) ≠ Γ.blank)
    (hmm : ¬(W (b + n) ≠ Γ.blank ∧ S (a + n) = W (b + n)))
    (c : Cfg 6 bodyTM.Q)
    (hst : c.state = cmpQ f)
    (hcS : (c.work stT).cells = S) (hheadS : (c.work stT).head = a)
    (hcW : (c.work dsT).cells = W) (hheadW : (c.work dsT).head = b)
    (hin : c.input.read ≠ Γ.start) (hout : c.output.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ stT → i ≠ dsT → (c.work i).read ≠ Γ.start) :
    ∃ c', bodyTM.reachesIn (n + 1) c c' ∧
      c'.state = skipSeg f ∧
      c'.work stT = ⟨a + n, S⟩ ∧
      c'.work dsT = ⟨b + n, W⟩ ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      (∀ i, i ≠ stT → i ≠ dsT → c'.work i = c.work i) := by
  obtain ⟨c₁, hreach₁, hst₁, hwtS₁, hwtD₁, hin₁, hout₁, hoth₁⟩ :=
    lockstep_agree_loop (cur := cmpQ f) (fun hcon => nomatch hcon)
      (fun iH wH oH hs hd he => by
        rw [arm_cmpQ iH wH oH f, ite_eq_right hs, ite_eq_left ⟨hd, he⟩])
      S W hSns hWns n a b ha hb hagree c hst hcS hheadS hcW hheadW hin hout hoth
  have hreadS₁ : (c₁.work stT).read = S (a + n) := by rw [hwtS₁]; rfl
  have hreadW₁ : (c₁.work dsT).read = W (b + n) := by rw [hwtD₁]; rfl
  have hc1' : ¬((c₁.work stT).read = Γ.blank) := by rw [hreadS₁]; exact hSnb
  have hc2' : ¬((c₁.work dsT).read ≠ Γ.blank ∧
      (c₁.work stT).read = (c₁.work dsT).read) := by
    rw [hreadS₁, hreadW₁]; exact hmm
  have harm := arm_cmpQ c₁.input.read (fun i => (c₁.work i).read) c₁.output.read f
  rw [ite_eq_right hc1', ite_eq_right hc2'] at harm
  have hwk₁ : ∀ i, (c₁.work i).read ≠ Γ.start := by
    intro i
    by_cases hiS : i = stT
    · subst hiS; rw [hreadS₁]; exact hSns (a + n) (by omega)
    · by_cases hiD : i = dsT
      · subst hiD; rw [hreadW₁]; exact hWns (b + n) (by omega)
      · rw [hoth₁ i hiS hiD]; exact hoth i hiS hiD
  have hstep := step_idle (by rw [hst₁]; exact fun hcon => nomatch hcon)
    (by rw [hst₁]; exact harm)
    (by rw [hin₁]; exact hin) (by rw [hout₁]; exact hout) hwk₁
  exact ⟨_, reachesIn_trans _ hreach₁ (.step hstep .zero), rfl,
    hwtS₁, hwtD₁, hin₁, hout₁, hoth₁⟩

-- ════════════════════════════════════════════════════════════════════════
-- 3. Key scan: cmpS — the six key-symbol cells
-- ════════════════════════════════════════════════════════════════════════

/-- **Key-symbol compare, match case**: from `cmpS f idx` with the desc
    tape (ghost `W`, head `b`) holding the expected `keyCell` symbols
    (all non-`□`) at offsets `0..k` (`idx.val + k = 5`), reach `copyQ' f`
    in `k + 1` steps with the desc head at `b + k + 1`. The three virtual
    tapes are stationary, so their live reads `v0`/`v1`/`v2` stay valid
    throughout. On the final step the state head (ghost `V`, head `a`)
    takes trick 1's pre-step one cell left. All cells and every other tape
    are exactly preserved. -/
theorem cmpS_match_loop (f : VFlags) (v0 v1 v2 : Γ) (W V : ℕ → Γ)
    (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start) (hVns : ∀ j, 1 ≤ j → V j ≠ Γ.start) :
    ∀ (k : ℕ) (idx : Fin 6), idx.val + k = 5 →
      ∀ (a b : ℕ), 1 ≤ a → 1 ≤ b →
      (∀ j, j ≤ k → ∀ (hj6 : idx.val + j < 6),
        W (b + j) = keyCell f v0 v1 v2 ⟨idx.val + j, hj6⟩ ∧ W (b + j) ≠ Γ.blank) →
      ∀ c : Cfg 6 bodyTM.Q,
      c.state = cmpS f idx →
      (c.work vIn).read = v0 → (c.work vWk).read = v1 → (c.work vOut).read = v2 →
      (c.work stT).cells = V → (c.work stT).head = a →
      (c.work dsT).cells = W → (c.work dsT).head = b →
      c.input.read ≠ Γ.start → c.output.read ≠ Γ.start →
      (∀ i, i ≠ stT → i ≠ dsT → (c.work i).read ≠ Γ.start) →
      ∃ c', bodyTM.reachesIn (k + 1) c c' ∧
        c'.state = copyQ' f ∧
        c'.work stT = ⟨a - 1, V⟩ ∧
        c'.work dsT = ⟨b + k + 1, W⟩ ∧
        c'.input = c.input ∧ c'.output = c.output ∧
        (∀ i, i ≠ stT → i ≠ dsT → c'.work i = c.work i) := by
  intro k
  induction k with
  | zero =>
    intro idx hk a b ha hb hkey c hst hv0 hv1 hv2 hcV hheadV hcW hheadW hin hout hoth
    have hreadW : (c.work dsT).read = W b := by simp [Tape.read, hheadW, hcW]
    have hreadW' : (c.work dsT).read ≠ Γ.start := by rw [hreadW]; exact hWns b hb
    have hreadS' : (c.work stT).read ≠ Γ.start := by
      simp only [Tape.read, hheadV, hcV]; exact hVns a ha
    have h0 : W b = keyCell f v0 v1 v2 idx ∧ W b ≠ Γ.blank :=
      hkey 0 (by omega) (by omega)
    have hcond : (c.work dsT).read
        = keyCell f (c.work vIn).read (c.work vWk).read (c.work vOut).read idx ∧
        (c.work dsT).read ≠ Γ.blank := by
      rw [hv0, hv1, hv2, hreadW]; exact h0
    have harm := arm_cmpS c.input.read (fun i => (c.work i).read) c.output.read f idx
    rw [ite_eq_left hcond, dite_eq_right (show ¬idx.val < 5 by omega)] at harm
    have hstep := step_act2 (by rw [hst]; exact fun hcon => nomatch hcon)
      (by rw [hst]; exact harm)
    refine ⟨_, .step hstep .zero, rfl, ?_, ?_, idle_input_id hin, idle_tape_id hout, ?_⟩
    · show (c.work stT).writeAndMove _ _ = (⟨a - 1, V⟩ : Tape)
      rw [ite_eq_right hreadS']
      simp only [Tape.writeAndMove, Tape.move, Tape.mk.injEq, Tape.write_head]
      exact ⟨by omega, by rw [write_readBack_cells hreadS', hcV]⟩
    · show (c.work dsT).writeAndMove _ _ = (⟨b + 0 + 1, W⟩ : Tape)
      rw [ite_eq_right hreadW']
      simp only [Tape.writeAndMove, Tape.move, Tape.mk.injEq, Tape.write_head]
      exact ⟨by omega, by rw [write_readBack_cells hreadW', hcW]⟩
    · intro i hiS hiD
      show (if i = dsT then _ else if i = stT then _ else _) = _
      rw [ite_eq_right hiD, ite_eq_right hiS]
      exact idle_tape_id (hoth i hiS hiD)
  | succ k ih =>
    intro idx hk a b ha hb hkey c hst hv0 hv1 hv2 hcV hheadV hcW hheadW hin hout hoth
    have hreadW : (c.work dsT).read = W b := by simp [Tape.read, hheadW, hcW]
    have hreadW' : (c.work dsT).read ≠ Γ.start := by rw [hreadW]; exact hWns b hb
    have hreadS' : (c.work stT).read ≠ Γ.start := by
      simp only [Tape.read, hheadV, hcV]; exact hVns a ha
    have h0 : W b = keyCell f v0 v1 v2 idx ∧ W b ≠ Γ.blank :=
      hkey 0 (by omega) (by omega)
    have hcond : (c.work dsT).read
        = keyCell f (c.work vIn).read (c.work vWk).read (c.work vOut).read idx ∧
        (c.work dsT).read ≠ Γ.blank := by
      rw [hv0, hv1, hv2, hreadW]; exact h0
    have harm := arm_cmpS c.input.read (fun i => (c.work i).read) c.output.read f idx
    rw [ite_eq_left hcond, dite_eq_left (show idx.val < 5 by omega)] at harm
    have hstep := step_act1 (by rw [hst]; exact fun hcon => nomatch hcon)
      (by rw [hst]; exact harm)
    obtain ⟨c', hreach, hst', hwtS', hwtD', hin', hout', hoth'⟩ :=
      ih ⟨idx.val + 1, by omega⟩ (by show idx.val + 1 + k = 5; omega)
        a (b + 1) ha (by omega)
        (fun j hj hj6 => by
          have e2 : b + (j + 1) = b + 1 + j := by omega
          have h := hkey (j + 1) (by omega) (by show idx.val + (j + 1) < 6; omega)
          rw [e2] at h
          refine ⟨?_, h.2⟩
          rw [h.1]
          exact congrArg (keyCell f v0 v1 v2)
            (Fin.ext (show idx.val + (j + 1) = idx.val + 1 + j by omega)))
        { state := cmpS f ⟨idx.val + 1, by omega⟩
          input := c.input.move (idleDir c.input.read)
          work := fun i =>
            if i = dsT then
              (c.work i).writeAndMove (readBackWrite ((c.work dsT).read)).toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.right)
            else (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
              (idleDir ((c.work i).read))
          output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
            (idleDir c.output.read) }
        rfl
        (by dsimp only
            rw [ite_eq_right (by decide : vIn ≠ dsT),
              idle_tape_id (hoth vIn (by decide) (by decide)), hv0])
        (by dsimp only
            rw [ite_eq_right (by decide : vWk ≠ dsT),
              idle_tape_id (hoth vWk (by decide) (by decide)), hv1])
        (by dsimp only
            rw [ite_eq_right (by decide : vOut ≠ dsT),
              idle_tape_id (hoth vOut (by decide) (by decide)), hv2])
        (by dsimp only
            rw [ite_eq_right (by decide : stT ≠ dsT), idle_tape_id hreadS', hcV])
        (by dsimp only
            rw [ite_eq_right (by decide : stT ≠ dsT), idle_tape_id hreadS', hheadV])
        (by dsimp only
            rw [ite_eq_left rfl, tape_readBackWrite_preserves _ _ (Or.inr hreadW'), hcW])
        (by dsimp only
            rw [ite_eq_left rfl, ite_eq_right hreadW']
            simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hheadW])
        (by dsimp only; rw [idle_input_id hin]; exact hin)
        (by dsimp only; rw [idle_tape_id hout]; exact hout)
        (fun i hiS hiD => by
          dsimp only
          rw [ite_eq_right hiD, idle_tape_id (hoth i hiS hiD)]
          exact hoth i hiS hiD)
    refine ⟨c', .step hstep hreach, hst', hwtS', ?_, ?_, ?_, ?_⟩
    · rw [hwtD']
      exact congrArg (fun m => (⟨m, W⟩ : Tape)) (by omega)
    · rw [hin']; exact idle_input_id hin
    · rw [hout']; exact idle_tape_id hout
    · intro i hiS hiD
      rw [hoth' i hiS hiD]
      show (if i = dsT then _ else _) = _
      rw [ite_eq_right hiD]
      exact idle_tape_id (hoth i hiS hiD)

/-- **Key-symbol compare, mismatch case**: from `cmpS f idx` with the desc
    tape (ghost `W`, head `b`) matching the expected `keyCell` symbols at
    offsets `< n` but failing at offset `n` (`idx.val + n ≤ 5`; the cell
    differs from the expected symbol or is `□`), reach `skipSeg f` in
    `n + 1` steps with the desc head at `b + n`. The state head does not
    move. All cells and every other tape are exactly preserved. -/
theorem cmpS_mismatch_loop (f : VFlags) (v0 v1 v2 : Γ) (W : ℕ → Γ)
    (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start) :
    ∀ (n : ℕ) (idx : Fin 6), idx.val + n ≤ 5 →
      ∀ (b : ℕ), 1 ≤ b →
      (∀ j, j < n → ∀ (hj6 : idx.val + j < 6),
        W (b + j) = keyCell f v0 v1 v2 ⟨idx.val + j, hj6⟩ ∧ W (b + j) ≠ Γ.blank) →
      (∀ (hn6 : idx.val + n < 6),
        ¬(W (b + n) = keyCell f v0 v1 v2 ⟨idx.val + n, hn6⟩ ∧ W (b + n) ≠ Γ.blank)) →
      ∀ c : Cfg 6 bodyTM.Q,
      c.state = cmpS f idx →
      (c.work vIn).read = v0 → (c.work vWk).read = v1 → (c.work vOut).read = v2 →
      (c.work dsT).cells = W → (c.work dsT).head = b →
      c.input.read ≠ Γ.start → c.output.read ≠ Γ.start →
      (∀ i, i ≠ dsT → (c.work i).read ≠ Γ.start) →
      ∃ c', bodyTM.reachesIn (n + 1) c c' ∧
        c'.state = skipSeg f ∧
        c'.work dsT = ⟨b + n, W⟩ ∧
        c'.input = c.input ∧ c'.output = c.output ∧
        (∀ i, i ≠ dsT → c'.work i = c.work i) := by
  intro n
  induction n with
  | zero =>
    intro idx hn b hb hkey hMM c hst hv0 hv1 hv2 hcW hheadW hin hout hoth
    have hreadW : (c.work dsT).read = W b := by simp [Tape.read, hheadW, hcW]
    have hreadW' : (c.work dsT).read ≠ Γ.start := by rw [hreadW]; exact hWns b hb
    have hMM' : ¬(W b = keyCell f v0 v1 v2 idx ∧ W b ≠ Γ.blank) := hMM (by omega)
    have hcond : ¬((c.work dsT).read
        = keyCell f (c.work vIn).read (c.work vWk).read (c.work vOut).read idx ∧
        (c.work dsT).read ≠ Γ.blank) := by
      rw [hv0, hv1, hv2, hreadW]; exact hMM'
    have harm := arm_cmpS c.input.read (fun i => (c.work i).read) c.output.read f idx
    rw [ite_eq_right hcond] at harm
    have hwk : ∀ i, (c.work i).read ≠ Γ.start := by
      intro i
      by_cases hiD : i = dsT
      · subst hiD; exact hreadW'
      · exact hoth i hiD
    have hstep := step_idle (by rw [hst]; exact fun hcon => nomatch hcon)
      (by rw [hst]; exact harm) hin hout hwk
    exact ⟨_, .step hstep .zero, rfl,
      by rw [← hcW, show b + 0 = (c.work dsT).head from by omega],
      rfl, rfl, fun _ _ => rfl⟩
  | succ n ih =>
    intro idx hn b hb hkey hMM c hst hv0 hv1 hv2 hcW hheadW hin hout hoth
    have hreadW : (c.work dsT).read = W b := by simp [Tape.read, hheadW, hcW]
    have hreadW' : (c.work dsT).read ≠ Γ.start := by rw [hreadW]; exact hWns b hb
    have h0 : W b = keyCell f v0 v1 v2 idx ∧ W b ≠ Γ.blank :=
      hkey 0 (by omega) (by omega)
    have hcond : (c.work dsT).read
        = keyCell f (c.work vIn).read (c.work vWk).read (c.work vOut).read idx ∧
        (c.work dsT).read ≠ Γ.blank := by
      rw [hv0, hv1, hv2, hreadW]; exact h0
    have harm := arm_cmpS c.input.read (fun i => (c.work i).read) c.output.read f idx
    rw [ite_eq_left hcond, dite_eq_left (show idx.val < 5 by omega)] at harm
    have hstep := step_act1 (by rw [hst]; exact fun hcon => nomatch hcon)
      (by rw [hst]; exact harm)
    obtain ⟨c', hreach, hst', hwtD', hin', hout', hoth'⟩ :=
      ih ⟨idx.val + 1, by omega⟩ (by show idx.val + 1 + n ≤ 5; omega)
        (b + 1) (by omega)
        (fun j hj hj6 => by
          have e2 : b + (j + 1) = b + 1 + j := by omega
          have h := hkey (j + 1) (by omega) (by show idx.val + (j + 1) < 6; omega)
          rw [e2] at h
          refine ⟨?_, h.2⟩
          rw [h.1]
          exact congrArg (keyCell f v0 v1 v2)
            (Fin.ext (show idx.val + (j + 1) = idx.val + 1 + j by omega)))
        (fun hn6 => by
          have e2 : b + 1 + n = b + (n + 1) := by omega
          rw [e2]
          intro hcon
          refine hMM (by omega) ⟨?_, hcon.2⟩
          rw [hcon.1]
          exact congrArg (keyCell f v0 v1 v2)
            (Fin.ext (show idx.val + 1 + n = idx.val + (n + 1) by omega)))
        { state := cmpS f ⟨idx.val + 1, by omega⟩
          input := c.input.move (idleDir c.input.read)
          work := fun i =>
            if i = dsT then
              (c.work i).writeAndMove (readBackWrite ((c.work dsT).read)).toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.right)
            else (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
              (idleDir ((c.work i).read))
          output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
            (idleDir c.output.read) }
        rfl
        (by dsimp only
            rw [ite_eq_right (by decide : vIn ≠ dsT),
              idle_tape_id (hoth vIn (by decide)), hv0])
        (by dsimp only
            rw [ite_eq_right (by decide : vWk ≠ dsT),
              idle_tape_id (hoth vWk (by decide)), hv1])
        (by dsimp only
            rw [ite_eq_right (by decide : vOut ≠ dsT),
              idle_tape_id (hoth vOut (by decide)), hv2])
        (by dsimp only
            rw [ite_eq_left rfl, tape_readBackWrite_preserves _ _ (Or.inr hreadW'), hcW])
        (by dsimp only
            rw [ite_eq_left rfl, ite_eq_right hreadW']
            simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hheadW])
        (by dsimp only; rw [idle_input_id hin]; exact hin)
        (by dsimp only; rw [idle_tape_id hout]; exact hout)
        (fun i hiD => by
          dsimp only
          rw [ite_eq_right hiD, idle_tape_id (hoth i hiD)]
          exact hoth i hiD)
    refine ⟨c', .step hstep hreach, hst', ?_, ?_, ?_, ?_⟩
    · rw [hwtD']
      exact congrArg (fun m => (⟨m, W⟩ : Tape)) (by omega)
    · rw [hin']; exact idle_input_id hin
    · rw [hout']; exact idle_tape_id hout
    · intro i hiD
      rw [hoth' i hiD]
      show (if i = dsT then _ else _) = _
      rw [ite_eq_right hiD]
      exact idle_tape_id (hoth i hiD)

-- ════════════════════════════════════════════════════════════════════════
-- 4. Value copy: copyQ' — trick 1's countdown copy
-- ════════════════════════════════════════════════════════════════════════

/-- **q'-field copy, clean case** (trick 1): from `copyQ' f` with the state
    tape (ghost `S`, `▷` at cell 0 only, head counting down from `s`), the
    desc tape (ghost `W`, head `b`) holding `s` non-`□` cells, and the
    scratch tape (ghost `E`, frontier `e`), copy the `s` desc cells to
    scratch cells `e..e+s-1` while the state head walks left; when it hits
    `▷` the forced bounce lands it at cell 1 and the machine enters
    `copyAct f 0` — `s + 1` steps in total. State and desc cells and every
    other tape are exactly preserved. -/
theorem copyQ'_copy_loop (f : VFlags) (S W : ℕ → Γ)
    (hS0 : S 0 = Γ.start) (hSns : ∀ j, 1 ≤ j → S j ≠ Γ.start)
    (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start) :
    ∀ (s : ℕ) (E : ℕ → Γ), (∀ j, 1 ≤ j → E j ≠ Γ.start) →
      ∀ (b e : ℕ), 1 ≤ b → 1 ≤ e →
      (∀ j, j < s → W (b + j) ≠ Γ.blank) →
      ∀ c : Cfg 6 bodyTM.Q,
      c.state = copyQ' f →
      (c.work stT).cells = S → (c.work stT).head = s →
      (c.work dsT).cells = W → (c.work dsT).head = b →
      (c.work scT).cells = E → (c.work scT).head = e →
      c.input.read ≠ Γ.start → c.output.read ≠ Γ.start →
      (∀ i, i ≠ stT → i ≠ dsT → i ≠ scT → (c.work i).read ≠ Γ.start) →
      ∃ c', bodyTM.reachesIn (s + 1) c c' ∧
        c'.state = copyAct f 0 ∧
        c'.work stT = ⟨1, S⟩ ∧
        c'.work dsT = ⟨b + s, W⟩ ∧
        c'.work scT = ⟨e + s, fun j => if e ≤ j ∧ j < e + s then W (b + (j - e)) else E j⟩ ∧
        c'.input = c.input ∧ c'.output = c.output ∧
        (∀ i, i ≠ stT → i ≠ dsT → i ≠ scT → c'.work i = c.work i) := by
  intro s
  induction s with
  | zero =>
    intro E hE b e hb he hnb c hst hcS hheadS hcW hheadW hcE hheadE hin hout hoth
    have hreadS : (c.work stT).read = Γ.start := by
      simp [Tape.read, hheadS, hcS, hS0]
    have hreadW' : (c.work dsT).read ≠ Γ.start := by
      simp only [Tape.read, hheadW, hcW]; exact hWns b hb
    have hreadE' : (c.work scT).read ≠ Γ.start := by
      simp only [Tape.read, hheadE, hcE]; exact hE e he
    have harm := arm_copyQ' c.input.read (fun i => (c.work i).read) c.output.read f
    rw [ite_eq_left hreadS] at harm
    have hstep := step_act1 (by rw [hst]; exact fun hcon => nomatch hcon)
      (by rw [hst]; exact harm)
    refine ⟨_, .step hstep .zero, rfl, ?_, ?_, ?_,
      idle_input_id hin, idle_tape_id hout, ?_⟩
    · show (c.work stT).writeAndMove _ _ = (⟨1, S⟩ : Tape)
      rw [ite_eq_left hreadS]
      have hwr : (c.work stT).write (readBackWrite ((c.work stT).read)).toΓ
          = c.work stT := by
        unfold Tape.write
        rw [ite_eq_left hheadS]
      show ((c.work stT).write _).move .right = _
      rw [hwr]
      simp only [Tape.move, Tape.mk.injEq]
      exact ⟨by omega, hcS⟩
    · show (c.work dsT).writeAndMove _ _ = (⟨b + 0, W⟩ : Tape)
      rw [idle_tape_id hreadW', ← hcW,
        show b + 0 = (c.work dsT).head from by omega]
    · show (c.work scT).writeAndMove _ _ = _
      rw [idle_tape_id hreadE']
      have hEmpty : (fun j => if e ≤ j ∧ j < e + 0 then W (b + (j - e)) else E j)
          = E := by
        funext j; rw [ite_eq_right (by omega)]
      rw [hEmpty, ← hcE, show e + 0 = (c.work scT).head from by omega]
    · intro i hiS hiD hiE
      show (if i = stT then _ else _) = _
      rw [ite_eq_right hiS]
      exact idle_tape_id (hoth i hiS hiD hiE)
  | succ s ih =>
    intro E hE b e hb he hnb c hst hcS hheadS hcW hheadW hcE hheadE hin hout hoth
    have hreadS : (c.work stT).read = S (s + 1) := by
      simp [Tape.read, hheadS, hcS]
    have hreadS' : (c.work stT).read ≠ Γ.start := by
      rw [hreadS]; exact hSns (s + 1) (by omega)
    have hreadW : (c.work dsT).read = W b := by simp [Tape.read, hheadW, hcW]
    have hreadW' : (c.work dsT).read ≠ Γ.start := by rw [hreadW]; exact hWns b hb
    have hreadWnb : (c.work dsT).read ≠ Γ.blank := by
      rw [hreadW]
      exact (show W b ≠ Γ.blank from hnb 0 (by omega))
    have hreadE' : (c.work scT).read ≠ Γ.start := by
      simp only [Tape.read, hheadE, hcE]; exact hE e he
    have hWb : (readBackWrite ((c.work dsT).read)).toΓ = W b := by
      rw [toΓ_readBackWrite_of_ne_start hreadW', hreadW]
    have harm := arm_copyQ' c.input.read (fun i => (c.work i).read) c.output.read f
    rw [ite_eq_right hreadS', ite_eq_right hreadWnb] at harm
    have hstep := step_act3 (by rw [hst]; exact fun hcon => nomatch hcon)
      (by rw [hst]; exact harm)
    have hEupd : ∀ j, 1 ≤ j → Function.update E e (W b) j ≠ Γ.start := by
      intro j hj
      by_cases hje : j = e
      · subst hje; rw [Function.update_self]; exact hWns b hb
      · rw [Function.update_of_ne hje]; exact hE j hj
    obtain ⟨c', hreach, hst', hwtS', hwtD', hwtE', hin', hout', hoth'⟩ :=
      ih (Function.update E e (W b)) hEupd (b + 1) (e + 1) (by omega) (by omega)
        (fun j hj => by
          have h := hnb (j + 1) (by omega)
          have e2 : b + (j + 1) = b + 1 + j := by omega
          rw [e2] at h
          exact h)
        { state := copyQ' f
          input := c.input.move (idleDir c.input.read)
          work := fun i =>
            if i = scT then
              (c.work i).writeAndMove (readBackWrite ((c.work dsT).read)).toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.right)
            else if i = dsT then
              (c.work i).writeAndMove (readBackWrite ((c.work dsT).read)).toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.right)
            else if i = stT then
              (c.work i).writeAndMove (readBackWrite ((c.work stT).read)).toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.left)
            else (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
              (idleDir ((c.work i).read))
          output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
            (idleDir c.output.read) }
        rfl
        (by dsimp only
            rw [ite_eq_right (by decide : stT ≠ scT), ite_eq_right (by decide : stT ≠ dsT),
              ite_eq_left rfl, tape_readBackWrite_preserves _ _ (Or.inr hreadS'), hcS])
        (by dsimp only
            rw [ite_eq_right (by decide : stT ≠ scT), ite_eq_right (by decide : stT ≠ dsT),
              ite_eq_left rfl, ite_eq_right hreadS']
            simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hheadS]
            omega)
        (by dsimp only
            rw [ite_eq_right (by decide : dsT ≠ scT), ite_eq_left rfl,
              tape_readBackWrite_preserves _ _ (Or.inr hreadW'), hcW])
        (by dsimp only
            rw [ite_eq_right (by decide : dsT ≠ scT), ite_eq_left rfl, ite_eq_right hreadW']
            simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hheadW])
        (by dsimp only
            rw [ite_eq_left rfl, ite_eq_right hreadE']
            show (((c.work scT).write _).move Dir3.right).cells = _
            have hw : (c.work scT).write (readBackWrite ((c.work dsT).read)).toΓ
                = { c.work scT with
                    cells := Function.update (c.work scT).cells (c.work scT).head
                      (readBackWrite ((c.work dsT).read)).toΓ } := by
              unfold Tape.write
              rw [ite_eq_right (by omega)]
            rw [hw]
            show Function.update (c.work scT).cells (c.work scT).head _ = _
            rw [hcE, hheadE, hWb])
        (by dsimp only
            rw [ite_eq_left rfl, ite_eq_right hreadE']
            simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hheadE])
        (by dsimp only; rw [idle_input_id hin]; exact hin)
        (by dsimp only; rw [idle_tape_id hout]; exact hout)
        (fun i hiS hiD hiE => by
          dsimp only
          rw [ite_eq_right hiE, ite_eq_right hiD, ite_eq_right hiS,
            idle_tape_id (hoth i hiS hiD hiE)]
          exact hoth i hiS hiD hiE)
    refine ⟨c', .step hstep hreach, hst', hwtS', ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwtD']
      exact congrArg (fun m => (⟨m, W⟩ : Tape)) (by omega)
    · rw [hwtE']
      simp only [Tape.mk.injEq]
      refine ⟨by omega, ?_⟩
      funext j
      by_cases hj1 : e + 1 ≤ j ∧ j < e + 1 + s
      · rw [ite_eq_left hj1, ite_eq_left (by omega)]
        exact congrArg W (by omega)
      · rw [ite_eq_right hj1]
        by_cases hje : j = e
        · subst hje
          rw [Function.update_self, ite_eq_left (by omega)]
          exact congrArg W (by omega)
        · rw [Function.update_of_ne hje, ite_eq_right (by omega)]
    · rw [hin']; exact idle_input_id hin
    · rw [hout']; exact idle_tape_id hout
    · intro i hiS hiD hiE
      rw [hoth' i hiS hiD hiE]
      show (if i = scT then _ else if i = dsT then _ else if i = stT then _ else _) = _
      rw [ite_eq_right hiE, ite_eq_right hiD, ite_eq_right hiS]
      exact idle_tape_id (hoth i hiS hiD hiE)

/-- **q'-field copy, early-`□` case**: from `copyQ' f` counting down from
    state head `s`, the desc tape hits `□` after only `n < s` copied cells:
    the machine exits to `skipSeg f` in `n + 1` steps (the `□`-exit step is
    an idle transition) with the state head at `s - n`, the desc head at
    `b + n` (on the `□`), and scratch extended by the `n` copied cells.
    State and desc cells and every other tape are exactly preserved. -/
theorem copyQ'_blank_loop (f : VFlags) (S W : ℕ → Γ)
    (hSns : ∀ j, 1 ≤ j → S j ≠ Γ.start)
    (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start) :
    ∀ (n : ℕ) (E : ℕ → Γ), (∀ j, 1 ≤ j → E j ≠ Γ.start) →
      ∀ (s b e : ℕ), n < s → 1 ≤ b → 1 ≤ e →
      (∀ j, j < n → W (b + j) ≠ Γ.blank) → W (b + n) = Γ.blank →
      ∀ c : Cfg 6 bodyTM.Q,
      c.state = copyQ' f →
      (c.work stT).cells = S → (c.work stT).head = s →
      (c.work dsT).cells = W → (c.work dsT).head = b →
      (c.work scT).cells = E → (c.work scT).head = e →
      c.input.read ≠ Γ.start → c.output.read ≠ Γ.start →
      (∀ i, i ≠ stT → i ≠ dsT → i ≠ scT → (c.work i).read ≠ Γ.start) →
      ∃ c', bodyTM.reachesIn (n + 1) c c' ∧
        c'.state = skipSeg f ∧
        c'.work stT = ⟨s - n, S⟩ ∧
        c'.work dsT = ⟨b + n, W⟩ ∧
        c'.work scT = ⟨e + n, fun j => if e ≤ j ∧ j < e + n then W (b + (j - e)) else E j⟩ ∧
        c'.input = c.input ∧ c'.output = c.output ∧
        (∀ i, i ≠ stT → i ≠ dsT → i ≠ scT → c'.work i = c.work i) := by
  intro n
  induction n with
  | zero =>
    intro E hE s b e hns hb he hnb hbl c hst hcS hheadS hcW hheadW hcE hheadE
      hin hout hoth
    have hreadS : (c.work stT).read = S s := by simp [Tape.read, hheadS, hcS]
    have hreadS' : (c.work stT).read ≠ Γ.start := by
      rw [hreadS]; exact hSns s (by omega)
    have hreadWbl : (c.work dsT).read = Γ.blank := by
      simp only [Tape.read, hheadW, hcW]
      exact (show W b = Γ.blank from hbl)
    have hreadE' : (c.work scT).read ≠ Γ.start := by
      simp only [Tape.read, hheadE, hcE]; exact hE e he
    have harm := arm_copyQ' c.input.read (fun i => (c.work i).read) c.output.read f
    rw [ite_eq_right hreadS', ite_eq_left hreadWbl] at harm
    have hwk : ∀ i, (c.work i).read ≠ Γ.start := by
      intro i
      by_cases hiS : i = stT
      · subst hiS; exact hreadS'
      · by_cases hiD : i = dsT
        · subst hiD; rw [hreadWbl]; simp
        · by_cases hiE : i = scT
          · subst hiE; exact hreadE'
          · exact hoth i hiS hiD hiE
    have hstep := step_idle (by rw [hst]; exact fun hcon => nomatch hcon)
      (by rw [hst]; exact harm) hin hout hwk
    refine ⟨_, .step hstep .zero, rfl, ?_, ?_, ?_, rfl, rfl, fun _ _ _ _ => rfl⟩
    · rw [← hcS, show s - 0 = (c.work stT).head from by omega]
    · rw [← hcW, show b + 0 = (c.work dsT).head from by omega]
    · have hEmpty : (fun j => if e ≤ j ∧ j < e + 0 then W (b + (j - e)) else E j)
          = E := by
        funext j; rw [ite_eq_right (by omega)]
      rw [hEmpty, ← hcE, show e + 0 = (c.work scT).head from by omega]
  | succ n ih =>
    intro E hE s b e hns hb he hnb hbl c hst hcS hheadS hcW hheadW hcE hheadE
      hin hout hoth
    have hreadS : (c.work stT).read = S s := by simp [Tape.read, hheadS, hcS]
    have hreadS' : (c.work stT).read ≠ Γ.start := by
      rw [hreadS]; exact hSns s (by omega)
    have hreadW : (c.work dsT).read = W b := by simp [Tape.read, hheadW, hcW]
    have hreadW' : (c.work dsT).read ≠ Γ.start := by rw [hreadW]; exact hWns b hb
    have hreadWnb : (c.work dsT).read ≠ Γ.blank := by
      rw [hreadW]
      exact (show W b ≠ Γ.blank from hnb 0 (by omega))
    have hreadE' : (c.work scT).read ≠ Γ.start := by
      simp only [Tape.read, hheadE, hcE]; exact hE e he
    have hWb : (readBackWrite ((c.work dsT).read)).toΓ = W b := by
      rw [toΓ_readBackWrite_of_ne_start hreadW', hreadW]
    have harm := arm_copyQ' c.input.read (fun i => (c.work i).read) c.output.read f
    rw [ite_eq_right hreadS', ite_eq_right hreadWnb] at harm
    have hstep := step_act3 (by rw [hst]; exact fun hcon => nomatch hcon)
      (by rw [hst]; exact harm)
    have hEupd : ∀ j, 1 ≤ j → Function.update E e (W b) j ≠ Γ.start := by
      intro j hj
      by_cases hje : j = e
      · subst hje; rw [Function.update_self]; exact hWns b hb
      · rw [Function.update_of_ne hje]; exact hE j hj
    obtain ⟨c', hreach, hst', hwtS', hwtD', hwtE', hin', hout', hoth'⟩ :=
      ih (Function.update E e (W b)) hEupd (s - 1) (b + 1) (e + 1)
        (by omega) (by omega) (by omega)
        (fun j hj => by
          have h := hnb (j + 1) (by omega)
          have e2 : b + (j + 1) = b + 1 + j := by omega
          rw [e2] at h
          exact h)
        (by
          have e2 : b + 1 + n = b + (n + 1) := by omega
          rw [e2]
          exact hbl)
        { state := copyQ' f
          input := c.input.move (idleDir c.input.read)
          work := fun i =>
            if i = scT then
              (c.work i).writeAndMove (readBackWrite ((c.work dsT).read)).toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.right)
            else if i = dsT then
              (c.work i).writeAndMove (readBackWrite ((c.work dsT).read)).toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.right)
            else if i = stT then
              (c.work i).writeAndMove (readBackWrite ((c.work stT).read)).toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.left)
            else (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
              (idleDir ((c.work i).read))
          output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
            (idleDir c.output.read) }
        rfl
        (by dsimp only
            rw [ite_eq_right (by decide : stT ≠ scT), ite_eq_right (by decide : stT ≠ dsT),
              ite_eq_left rfl, tape_readBackWrite_preserves _ _ (Or.inr hreadS'), hcS])
        (by dsimp only
            rw [ite_eq_right (by decide : stT ≠ scT), ite_eq_right (by decide : stT ≠ dsT),
              ite_eq_left rfl, ite_eq_right hreadS']
            simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hheadS])
        (by dsimp only
            rw [ite_eq_right (by decide : dsT ≠ scT), ite_eq_left rfl,
              tape_readBackWrite_preserves _ _ (Or.inr hreadW'), hcW])
        (by dsimp only
            rw [ite_eq_right (by decide : dsT ≠ scT), ite_eq_left rfl, ite_eq_right hreadW']
            simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hheadW])
        (by dsimp only
            rw [ite_eq_left rfl, ite_eq_right hreadE']
            show (((c.work scT).write _).move Dir3.right).cells = _
            have hw : (c.work scT).write (readBackWrite ((c.work dsT).read)).toΓ
                = { c.work scT with
                    cells := Function.update (c.work scT).cells (c.work scT).head
                      (readBackWrite ((c.work dsT).read)).toΓ } := by
              unfold Tape.write
              rw [ite_eq_right (by omega)]
            rw [hw]
            show Function.update (c.work scT).cells (c.work scT).head _ = _
            rw [hcE, hheadE, hWb])
        (by dsimp only
            rw [ite_eq_left rfl, ite_eq_right hreadE']
            simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hheadE])
        (by dsimp only; rw [idle_input_id hin]; exact hin)
        (by dsimp only; rw [idle_tape_id hout]; exact hout)
        (fun i hiS hiD hiE => by
          dsimp only
          rw [ite_eq_right hiE, ite_eq_right hiD, ite_eq_right hiS,
            idle_tape_id (hoth i hiS hiD hiE)]
          exact hoth i hiS hiD hiE)
    refine ⟨c', .step hstep hreach, hst', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwtS']
      exact congrArg (fun m => (⟨m, S⟩ : Tape)) (by omega)
    · rw [hwtD']
      exact congrArg (fun m => (⟨m, W⟩ : Tape)) (by omega)
    · rw [hwtE']
      simp only [Tape.mk.injEq]
      refine ⟨by omega, ?_⟩
      funext j
      by_cases hj1 : e + 1 ≤ j ∧ j < e + 1 + n
      · rw [ite_eq_left hj1, ite_eq_left (by omega)]
        exact congrArg W (by omega)
      · rw [ite_eq_right hj1]
        by_cases hje : j = e
        · subst hje
          rw [Function.update_self, ite_eq_left (by omega)]
          exact congrArg W (by omega)
        · rw [Function.update_of_ne hje, ite_eq_right (by omega)]
    · rw [hin']; exact idle_input_id hin
    · rw [hout']; exact idle_tape_id hout
    · intro i hiS hiD hiE
      rw [hoth' i hiS hiD hiE]
      show (if i = scT then _ else if i = dsT then _ else if i = stT then _ else _) = _
      rw [ite_eq_right hiE, ite_eq_right hiD, ite_eq_right hiS]
      exact idle_tape_id (hoth i hiS hiD hiE)

-- ════════════════════════════════════════════════════════════════════════
-- 5. Value copy: copyAct — the ten action cells
-- ════════════════════════════════════════════════════════════════════════

/-- **Action-cell copy, clean case**: from `copyAct f j` with the desc tape
    (ghost `W`, head `b`) holding `k + 1` non-`□` cells
    (`j.val + k = 9`, so `k + 1 = 10 - j.val`) and the scratch tape (ghost
    `E`, frontier `e`), copy the remaining action cells to scratch cells
    `e..e+k` and enter `appRewScr f` in `k + 1` steps, with the desc head
    at `b + k + 1` and the scratch frontier at `e + k + 1`. Desc cells and
    every other tape are exactly preserved. -/
theorem copyAct_copy_loop (f : VFlags) (W : ℕ → Γ)
    (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start) :
    ∀ (k : ℕ) (j : Fin 10), j.val + k = 9 →
      ∀ (E : ℕ → Γ), (∀ i, 1 ≤ i → E i ≠ Γ.start) →
      ∀ (b e : ℕ), 1 ≤ b → 1 ≤ e →
      (∀ i, i ≤ k → W (b + i) ≠ Γ.blank) →
      ∀ c : Cfg 6 bodyTM.Q,
      c.state = copyAct f j →
      (c.work dsT).cells = W → (c.work dsT).head = b →
      (c.work scT).cells = E → (c.work scT).head = e →
      c.input.read ≠ Γ.start → c.output.read ≠ Γ.start →
      (∀ i, i ≠ dsT → i ≠ scT → (c.work i).read ≠ Γ.start) →
      ∃ c', bodyTM.reachesIn (k + 1) c c' ∧
        c'.state = appRewScr f ∧
        c'.work dsT = ⟨b + k + 1, W⟩ ∧
        c'.work scT = ⟨e + k + 1,
          fun i => if e ≤ i ∧ i < e + k + 1 then W (b + (i - e)) else E i⟩ ∧
        c'.input = c.input ∧ c'.output = c.output ∧
        (∀ i, i ≠ dsT → i ≠ scT → c'.work i = c.work i) := by
  intro k
  induction k with
  | zero =>
    intro j hk E hE b e hb he hnb c hst hcW hheadW hcE hheadE hin hout hoth
    have hreadW : (c.work dsT).read = W b := by simp [Tape.read, hheadW, hcW]
    have hreadW' : (c.work dsT).read ≠ Γ.start := by rw [hreadW]; exact hWns b hb
    have hreadWnb : (c.work dsT).read ≠ Γ.blank := by
      rw [hreadW]
      exact (show W b ≠ Γ.blank from hnb 0 (by omega))
    have hreadE' : (c.work scT).read ≠ Γ.start := by
      simp only [Tape.read, hheadE, hcE]; exact hE e he
    have hWb : (readBackWrite ((c.work dsT).read)).toΓ = W b := by
      rw [toΓ_readBackWrite_of_ne_start hreadW', hreadW]
    have harm := arm_copyAct c.input.read (fun i => (c.work i).read) c.output.read f j
    rw [ite_eq_right hreadWnb, dite_eq_right (show ¬j.val < 9 by omega)] at harm
    have hstep := step_act2 (by rw [hst]; exact fun hcon => nomatch hcon)
      (by rw [hst]; exact harm)
    refine ⟨_, .step hstep .zero, rfl, ?_, ?_,
      idle_input_id hin, idle_tape_id hout, ?_⟩
    · show (c.work dsT).writeAndMove _ _ = (⟨b + 0 + 1, W⟩ : Tape)
      rw [ite_eq_right hreadW']
      simp only [Tape.writeAndMove, Tape.move, Tape.mk.injEq, Tape.write_head]
      exact ⟨by omega, by rw [write_readBack_cells hreadW', hcW]⟩
    · show (c.work scT).writeAndMove _ _ = _
      rw [ite_eq_right hreadE']
      show ((c.work scT).write _).move .right = _
      have hw : (c.work scT).write (readBackWrite ((c.work dsT).read)).toΓ
          = { c.work scT with
              cells := Function.update (c.work scT).cells (c.work scT).head
                (readBackWrite ((c.work dsT).read)).toΓ } := by
        unfold Tape.write
        rw [ite_eq_right (by omega)]
      rw [hw]
      simp only [Tape.move, Tape.mk.injEq]
      refine ⟨by omega, ?_⟩
      show Function.update (c.work scT).cells (c.work scT).head _ = _
      rw [hcE, hheadE, hWb]
      funext i
      by_cases hie : i = e
      · subst hie
        rw [Function.update_self, ite_eq_left (by omega)]
        exact congrArg W (by omega)
      · rw [Function.update_of_ne hie, ite_eq_right (by omega)]
    · intro i hiD hiE
      show (if i = scT then _ else if i = dsT then _ else _) = _
      rw [ite_eq_right hiE, ite_eq_right hiD]
      exact idle_tape_id (hoth i hiD hiE)
  | succ k ih =>
    intro j hk E hE b e hb he hnb c hst hcW hheadW hcE hheadE hin hout hoth
    have hreadW : (c.work dsT).read = W b := by simp [Tape.read, hheadW, hcW]
    have hreadW' : (c.work dsT).read ≠ Γ.start := by rw [hreadW]; exact hWns b hb
    have hreadWnb : (c.work dsT).read ≠ Γ.blank := by
      rw [hreadW]
      exact (show W b ≠ Γ.blank from hnb 0 (by omega))
    have hreadE' : (c.work scT).read ≠ Γ.start := by
      simp only [Tape.read, hheadE, hcE]; exact hE e he
    have hWb : (readBackWrite ((c.work dsT).read)).toΓ = W b := by
      rw [toΓ_readBackWrite_of_ne_start hreadW', hreadW]
    have harm := arm_copyAct c.input.read (fun i => (c.work i).read) c.output.read f j
    rw [ite_eq_right hreadWnb, dite_eq_left (show j.val < 9 by omega)] at harm
    have hstep := step_act2 (by rw [hst]; exact fun hcon => nomatch hcon)
      (by rw [hst]; exact harm)
    have hEupd : ∀ i, 1 ≤ i → Function.update E e (W b) i ≠ Γ.start := by
      intro i hi
      by_cases hie : i = e
      · subst hie; rw [Function.update_self]; exact hWns b hb
      · rw [Function.update_of_ne hie]; exact hE i hi
    obtain ⟨c', hreach, hst', hwtD', hwtE', hin', hout', hoth'⟩ :=
      ih ⟨j.val + 1, by omega⟩ (by show j.val + 1 + k = 9; omega)
        (Function.update E e (W b)) hEupd (b + 1) (e + 1) (by omega) (by omega)
        (fun i hi => by
          have h := hnb (i + 1) (by omega)
          have e2 : b + (i + 1) = b + 1 + i := by omega
          rw [e2] at h
          exact h)
        { state := copyAct f ⟨j.val + 1, by omega⟩
          input := c.input.move (idleDir c.input.read)
          work := fun i =>
            if i = scT then
              (c.work i).writeAndMove (readBackWrite ((c.work dsT).read)).toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.right)
            else if i = dsT then
              (c.work i).writeAndMove (readBackWrite ((c.work dsT).read)).toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.right)
            else (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
              (idleDir ((c.work i).read))
          output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
            (idleDir c.output.read) }
        rfl
        (by dsimp only
            rw [ite_eq_right (by decide : dsT ≠ scT), ite_eq_left rfl,
              tape_readBackWrite_preserves _ _ (Or.inr hreadW'), hcW])
        (by dsimp only
            rw [ite_eq_right (by decide : dsT ≠ scT), ite_eq_left rfl, ite_eq_right hreadW']
            simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hheadW])
        (by dsimp only
            rw [ite_eq_left rfl, ite_eq_right hreadE']
            show (((c.work scT).write _).move Dir3.right).cells = _
            have hw : (c.work scT).write (readBackWrite ((c.work dsT).read)).toΓ
                = { c.work scT with
                    cells := Function.update (c.work scT).cells (c.work scT).head
                      (readBackWrite ((c.work dsT).read)).toΓ } := by
              unfold Tape.write
              rw [ite_eq_right (by omega)]
            rw [hw]
            show Function.update (c.work scT).cells (c.work scT).head _ = _
            rw [hcE, hheadE, hWb])
        (by dsimp only
            rw [ite_eq_left rfl, ite_eq_right hreadE']
            simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hheadE])
        (by dsimp only; rw [idle_input_id hin]; exact hin)
        (by dsimp only; rw [idle_tape_id hout]; exact hout)
        (fun i hiD hiE => by
          dsimp only
          rw [ite_eq_right hiE, ite_eq_right hiD, idle_tape_id (hoth i hiD hiE)]
          exact hoth i hiD hiE)
    refine ⟨c', .step hstep hreach, hst', ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwtD']
      exact congrArg (fun m => (⟨m, W⟩ : Tape)) (by omega)
    · rw [hwtE']
      simp only [Tape.mk.injEq]
      refine ⟨by omega, ?_⟩
      funext i
      by_cases hi1 : e + 1 ≤ i ∧ i < e + 1 + k + 1
      · rw [ite_eq_left hi1, ite_eq_left (by omega)]
        exact congrArg W (by omega)
      · rw [ite_eq_right hi1]
        by_cases hie : i = e
        · subst hie
          rw [Function.update_self, ite_eq_left (by omega)]
          exact congrArg W (by omega)
        · rw [Function.update_of_ne hie, ite_eq_right (by omega)]
    · rw [hin']; exact idle_input_id hin
    · rw [hout']; exact idle_tape_id hout
    · intro i hiD hiE
      rw [hoth' i hiD hiE]
      show (if i = scT then _ else if i = dsT then _ else _) = _
      rw [ite_eq_right hiE, ite_eq_right hiD]
      exact idle_tape_id (hoth i hiD hiE)

/-- **Action-cell copy, early-`□` case**: from `copyAct f j`, the desc tape
    hits `□` at offset `n` (`j.val + n ≤ 9`) after `n` copied cells: the
    machine exits to `skipSeg f` in `n + 1` steps (the `□`-exit step is an
    idle transition) with the desc head at `b + n` (on the `□`) and scratch
    extended by the `n` copied cells. Desc cells and every other tape are
    exactly preserved. -/
theorem copyAct_blank_loop (f : VFlags) (W : ℕ → Γ)
    (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start) :
    ∀ (n : ℕ) (j : Fin 10), j.val + n ≤ 9 →
      ∀ (E : ℕ → Γ), (∀ i, 1 ≤ i → E i ≠ Γ.start) →
      ∀ (b e : ℕ), 1 ≤ b → 1 ≤ e →
      (∀ i, i < n → W (b + i) ≠ Γ.blank) → W (b + n) = Γ.blank →
      ∀ c : Cfg 6 bodyTM.Q,
      c.state = copyAct f j →
      (c.work dsT).cells = W → (c.work dsT).head = b →
      (c.work scT).cells = E → (c.work scT).head = e →
      c.input.read ≠ Γ.start → c.output.read ≠ Γ.start →
      (∀ i, i ≠ dsT → i ≠ scT → (c.work i).read ≠ Γ.start) →
      ∃ c', bodyTM.reachesIn (n + 1) c c' ∧
        c'.state = skipSeg f ∧
        c'.work dsT = ⟨b + n, W⟩ ∧
        c'.work scT = ⟨e + n,
          fun i => if e ≤ i ∧ i < e + n then W (b + (i - e)) else E i⟩ ∧
        c'.input = c.input ∧ c'.output = c.output ∧
        (∀ i, i ≠ dsT → i ≠ scT → c'.work i = c.work i) := by
  intro n
  induction n with
  | zero =>
    intro j hn E hE b e hb he hnb hbl c hst hcW hheadW hcE hheadE hin hout hoth
    have hreadWbl : (c.work dsT).read = Γ.blank := by
      simp only [Tape.read, hheadW, hcW]
      exact (show W b = Γ.blank from hbl)
    have hreadE' : (c.work scT).read ≠ Γ.start := by
      simp only [Tape.read, hheadE, hcE]; exact hE e he
    have harm := arm_copyAct c.input.read (fun i => (c.work i).read) c.output.read f j
    rw [ite_eq_left hreadWbl] at harm
    have hwk : ∀ i, (c.work i).read ≠ Γ.start := by
      intro i
      by_cases hiD : i = dsT
      · subst hiD; rw [hreadWbl]; simp
      · by_cases hiE : i = scT
        · subst hiE; exact hreadE'
        · exact hoth i hiD hiE
    have hstep := step_idle (by rw [hst]; exact fun hcon => nomatch hcon)
      (by rw [hst]; exact harm) hin hout hwk
    refine ⟨_, .step hstep .zero, rfl, ?_, ?_, rfl, rfl, fun _ _ _ => rfl⟩
    · rw [← hcW, show b + 0 = (c.work dsT).head from by omega]
    · have hEmpty : (fun i => if e ≤ i ∧ i < e + 0 then W (b + (i - e)) else E i)
          = E := by
        funext i; rw [ite_eq_right (by omega)]
      rw [hEmpty, ← hcE, show e + 0 = (c.work scT).head from by omega]
  | succ n ih =>
    intro j hn E hE b e hb he hnb hbl c hst hcW hheadW hcE hheadE hin hout hoth
    have hreadW : (c.work dsT).read = W b := by simp [Tape.read, hheadW, hcW]
    have hreadW' : (c.work dsT).read ≠ Γ.start := by rw [hreadW]; exact hWns b hb
    have hreadWnb : (c.work dsT).read ≠ Γ.blank := by
      rw [hreadW]
      exact (show W b ≠ Γ.blank from hnb 0 (by omega))
    have hreadE' : (c.work scT).read ≠ Γ.start := by
      simp only [Tape.read, hheadE, hcE]; exact hE e he
    have hWb : (readBackWrite ((c.work dsT).read)).toΓ = W b := by
      rw [toΓ_readBackWrite_of_ne_start hreadW', hreadW]
    have harm := arm_copyAct c.input.read (fun i => (c.work i).read) c.output.read f j
    rw [ite_eq_right hreadWnb, dite_eq_left (show j.val < 9 by omega)] at harm
    have hstep := step_act2 (by rw [hst]; exact fun hcon => nomatch hcon)
      (by rw [hst]; exact harm)
    have hEupd : ∀ i, 1 ≤ i → Function.update E e (W b) i ≠ Γ.start := by
      intro i hi
      by_cases hie : i = e
      · subst hie; rw [Function.update_self]; exact hWns b hb
      · rw [Function.update_of_ne hie]; exact hE i hi
    obtain ⟨c', hreach, hst', hwtD', hwtE', hin', hout', hoth'⟩ :=
      ih ⟨j.val + 1, by omega⟩ (by show j.val + 1 + n ≤ 9; omega)
        (Function.update E e (W b)) hEupd (b + 1) (e + 1) (by omega) (by omega)
        (fun i hi => by
          have h := hnb (i + 1) (by omega)
          have e2 : b + (i + 1) = b + 1 + i := by omega
          rw [e2] at h
          exact h)
        (by
          have e2 : b + 1 + n = b + (n + 1) := by omega
          rw [e2]
          exact hbl)
        { state := copyAct f ⟨j.val + 1, by omega⟩
          input := c.input.move (idleDir c.input.read)
          work := fun i =>
            if i = scT then
              (c.work i).writeAndMove (readBackWrite ((c.work dsT).read)).toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.right)
            else if i = dsT then
              (c.work i).writeAndMove (readBackWrite ((c.work dsT).read)).toΓ
                (if (c.work i).read = Γ.start then Dir3.right else Dir3.right)
            else (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
              (idleDir ((c.work i).read))
          output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
            (idleDir c.output.read) }
        rfl
        (by dsimp only
            rw [ite_eq_right (by decide : dsT ≠ scT), ite_eq_left rfl,
              tape_readBackWrite_preserves _ _ (Or.inr hreadW'), hcW])
        (by dsimp only
            rw [ite_eq_right (by decide : dsT ≠ scT), ite_eq_left rfl, ite_eq_right hreadW']
            simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hheadW])
        (by dsimp only
            rw [ite_eq_left rfl, ite_eq_right hreadE']
            show (((c.work scT).write _).move Dir3.right).cells = _
            have hw : (c.work scT).write (readBackWrite ((c.work dsT).read)).toΓ
                = { c.work scT with
                    cells := Function.update (c.work scT).cells (c.work scT).head
                      (readBackWrite ((c.work dsT).read)).toΓ } := by
              unfold Tape.write
              rw [ite_eq_right (by omega)]
            rw [hw]
            show Function.update (c.work scT).cells (c.work scT).head _ = _
            rw [hcE, hheadE, hWb])
        (by dsimp only
            rw [ite_eq_left rfl, ite_eq_right hreadE']
            simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hheadE])
        (by dsimp only; rw [idle_input_id hin]; exact hin)
        (by dsimp only; rw [idle_tape_id hout]; exact hout)
        (fun i hiD hiE => by
          dsimp only
          rw [ite_eq_right hiE, ite_eq_right hiD, idle_tape_id (hoth i hiD hiE)]
          exact hoth i hiD hiE)
    refine ⟨c', .step hstep hreach, hst', ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwtD']
      exact congrArg (fun m => (⟨m, W⟩ : Tape)) (by omega)
    · rw [hwtE']
      simp only [Tape.mk.injEq]
      refine ⟨by omega, ?_⟩
      funext i
      by_cases hi1 : e + 1 ≤ i ∧ i < e + 1 + n
      · rw [ite_eq_left hi1, ite_eq_left (by omega)]
        exact congrArg W (by omega)
      · rw [ite_eq_right hi1]
        by_cases hie : i = e
        · subst hie
          rw [Function.update_self, ite_eq_left (by omega)]
          exact congrArg W (by omega)
        · rw [Function.update_of_ne hie, ite_eq_right (by omega)]
    · rw [hin']; exact idle_input_id hin
    · rw [hout']; exact idle_tape_id hout
    · intro i hiD hiE
      rw [hoth' i hiD hiE]
      show (if i = scT then _ else if i = dsT then _ else _) = _
      rw [ite_eq_right hiE, ite_eq_right hiD]
      exact idle_tape_id (hoth i hiD hiE)

end TM.UTMBody

end Complexity
