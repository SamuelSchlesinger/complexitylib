/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.Pairing
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import Complexitylib.Models.TuringMachine.Trace
public import Complexitylib.Models.TuringMachine.Subroutines.PairSplit.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.Ring.RingNF

/-!
# Pair-splitting machine — proof internals

This file proves the stepwise decoding and exact-time correctness facts for
`pairSplitCoreTM`. Stable statements are re-exposed by
`Complexitylib.Models.TuringMachine.Subroutines.PairSplit`.
-/


public section

namespace Complexity

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Front-half decoding: local step lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- In `.scanX`, reading the first `false` copy advances to `.afterFalse`
without changing either work tape. -/
private theorem pairSplit_scanX_false_step {k : ℕ} (xIdx yIdx : Fin k)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .scanX) (hiread : c.input.read = Γ.zero)
    (hxh : (c.work xIdx).head ≥ 1)
    (hxns : ∀ j, j ≥ 1 → (c.work xIdx).cells j ≠ Γ.start)
    (hyh : (c.work yIdx).head ≥ 1)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairSplitCoreTM xIdx yIdx).step c = some c' ∧
      c'.state = .afterFalse ∧
      c'.input.head = c.input.head + 1 ∧
      c'.input.cells = c.input.cells ∧
      c'.work xIdx = c.work xIdx ∧
      c'.work yIdx = c.work yIdx := by
  simp only [TM.step, hst, pairSplitCoreTM, ite_eq_left hiread]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [Tape.move]
  · simpa using (Tape.move_cells c.input Dir3.right)
  · exact tape_writeAndMove_stable (c.work xIdx) hxh hxns
  · exact tape_writeAndMove_stable (c.work yIdx) hyh hyns

/-- In `.scanX`, reading the first `true` copy advances to `.writeTrue`
without changing either work tape. -/
private theorem pairSplit_scanX_true_step {k : ℕ} (xIdx yIdx : Fin k)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .scanX) (hiread : c.input.read = Γ.one)
    (hxh : (c.work xIdx).head ≥ 1)
    (hxns : ∀ j, j ≥ 1 → (c.work xIdx).cells j ≠ Γ.start)
    (hyh : (c.work yIdx).head ≥ 1)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairSplitCoreTM xIdx yIdx).step c = some c' ∧
      c'.state = .writeTrue ∧
      c'.input.head = c.input.head + 1 ∧
      c'.input.cells = c.input.cells ∧
      c'.work xIdx = c.work xIdx ∧
      c'.work yIdx = c.work yIdx := by
  have hne_zero : c.input.read ≠ Γ.zero := by
    rw [hiread]
    decide
  simp only [TM.step, hst, pairSplitCoreTM, ite_eq_right hne_zero, ite_eq_left hiread]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [Tape.move]
  · simpa using (Tape.move_cells c.input Dir3.right)
  · exact tape_writeAndMove_stable (c.work xIdx) hxh hxns
  · exact tape_writeAndMove_stable (c.work yIdx) hyh hyns

/-- In `.afterFalse`, reading the second `false` writes `false` to `xIdx`
and returns to `.scanX`. -/
private theorem pairSplit_afterFalse_zero_step {k : ℕ} (xIdx yIdx : Fin k)
    (hne : xIdx ≠ yIdx)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .afterFalse) (hiread : c.input.read = Γ.zero)
    (hxh : (c.work xIdx).head ≥ 1)
    (hyh : (c.work yIdx).head ≥ 1)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairSplitCoreTM xIdx yIdx).step c = some c' ∧
      c'.state = .scanX ∧
      c'.input.head = c.input.head + 1 ∧
      c'.input.cells = c.input.cells ∧
      (c'.work xIdx).head = (c.work xIdx).head + 1 ∧
      (c'.work xIdx).cells =
        Function.update (c.work xIdx).cells (c.work xIdx).head Γ.zero ∧
      c'.work yIdx = c.work yIdx := by
  simp only [TM.step, hst, pairSplitCoreTM, ite_eq_left hiread]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Tape.move]
  · simpa using (Tape.move_cells c.input Dir3.right)
  · dsimp only []
    simp [Tape.writeAndMove, Tape.write, Tape.move,
      show (c.work xIdx).head ≠ 0 from by omega]
  · dsimp only []
    simp [Tape.writeAndMove, Tape.move_cells, Tape.write,
      show (c.work xIdx).head ≠ 0 from by omega]
  · dsimp only []
    simp only [ite_eq_right (Ne.symm hne)]
    exact tape_writeAndMove_stable (c.work yIdx) hyh hyns

/-- In `.afterFalse`, reading `true` recognizes the separator and enters
`.copyY`, leaving both work tapes unchanged. -/
private theorem pairSplit_afterFalse_sep_step {k : ℕ} (xIdx yIdx : Fin k)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .afterFalse) (hiread : c.input.read = Γ.one)
    (hxh : (c.work xIdx).head ≥ 1)
    (hxns : ∀ j, j ≥ 1 → (c.work xIdx).cells j ≠ Γ.start)
    (hyh : (c.work yIdx).head ≥ 1)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairSplitCoreTM xIdx yIdx).step c = some c' ∧
      c'.state = .copyY ∧
      c'.input.head = c.input.head + 1 ∧
      c'.input.cells = c.input.cells ∧
      c'.work xIdx = c.work xIdx ∧
      c'.work yIdx = c.work yIdx := by
  have hne_zero : c.input.read ≠ Γ.zero := by
    rw [hiread]
    decide
  simp only [TM.step, hst, pairSplitCoreTM, ite_eq_right hne_zero, ite_eq_left hiread]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [Tape.move]
  · simpa using (Tape.move_cells c.input Dir3.right)
  · exact tape_writeAndMove_stable (c.work xIdx) hxh hxns
  · exact tape_writeAndMove_stable (c.work yIdx) hyh hyns

/-- In `.writeTrue`, reading the second `true` writes `true` to `xIdx`
and returns to `.scanX`. -/
private theorem pairSplit_writeTrue_step {k : ℕ} (xIdx yIdx : Fin k)
    (hne : xIdx ≠ yIdx)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .writeTrue) (hiread : c.input.read = Γ.one)
    (hxh : (c.work xIdx).head ≥ 1)
    (hyh : (c.work yIdx).head ≥ 1)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairSplitCoreTM xIdx yIdx).step c = some c' ∧
      c'.state = .scanX ∧
      c'.input.head = c.input.head + 1 ∧
      c'.input.cells = c.input.cells ∧
      (c'.work xIdx).head = (c.work xIdx).head + 1 ∧
      (c'.work xIdx).cells =
        Function.update (c.work xIdx).cells (c.work xIdx).head Γ.one ∧
      c'.work yIdx = c.work yIdx := by
  simp only [TM.step, hst, pairSplitCoreTM, ite_eq_left hiread]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Tape.move]
  · simpa using (Tape.move_cells c.input Dir3.right)
  · dsimp only []
    simp [Tape.writeAndMove, Tape.write, Tape.move,
      show (c.work xIdx).head ≠ 0 from by omega]
  · dsimp only []
    simp [Tape.writeAndMove, Tape.move_cells, Tape.write,
      show (c.work xIdx).head ≠ 0 from by omega]
  · dsimp only []
    simp only [ite_eq_right (Ne.symm hne)]
    exact tape_writeAndMove_stable (c.work yIdx) hyh hyns

/-- Two-step decoding of a doubled `false` bit. -/
private theorem pairSplit_false_bit_step {k : ℕ} (xIdx yIdx : Fin k)
    (hne : xIdx ≠ yIdx)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .scanX)
    (hread0 : c.input.read = Γ.zero)
    (hnext0 : c.input.cells (c.input.head + 1) = Γ.zero)
    (hxh : (c.work xIdx).head ≥ 1)
    (hxns : ∀ j, j ≥ 1 → (c.work xIdx).cells j ≠ Γ.start)
    (hyh : (c.work yIdx).head ≥ 1)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairSplitCoreTM xIdx yIdx).reachesIn 2 c c' ∧
      c'.state = .scanX ∧
      c'.input.head = c.input.head + 2 ∧
      c'.input.cells = c.input.cells ∧
      (c'.work xIdx).head = (c.work xIdx).head + 1 ∧
      (c'.work xIdx).cells =
        Function.update (c.work xIdx).cells (c.work xIdx).head Γ.zero ∧
      c'.work yIdx = c.work yIdx := by
  obtain ⟨c1, hstep1, hst1, hc1_ih, hc1_ic, hc1_xw, hc1_yw⟩ :=
    pairSplit_scanX_false_step xIdx yIdx c hst hread0 hxh hxns hyh hyns
  have hc1_read : c1.input.read = Γ.zero := by
    show c1.input.cells c1.input.head = Γ.zero
    rw [hc1_ic, hc1_ih]
    exact hnext0
  have hc1_xh : (c1.work xIdx).head ≥ 1 := by rw [hc1_xw]; exact hxh
  have hc1_yh : (c1.work yIdx).head ≥ 1 := by rw [hc1_yw]; exact hyh
  have hc1_yns : ∀ j, j ≥ 1 → (c1.work yIdx).cells j ≠ Γ.start := by
    intro j hj
    rw [hc1_yw]
    exact hyns j hj
  obtain ⟨c2, hstep2, hst2, hc2_ih, hc2_ic, hc2_xh, hc2_xc, hc2_yw⟩ :=
    pairSplit_afterFalse_zero_step xIdx yIdx hne c1 hst1 hc1_read hc1_xh hc1_yh hc1_yns
  refine ⟨c2, .step hstep1 (.step hstep2 .zero), hst2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc2_ih, hc1_ih]
  · rw [hc2_ic, hc1_ic]
  · rw [hc2_xh, hc1_xw]
  · rw [hc2_xc, hc1_xw]
  · rw [hc2_yw, hc1_yw]

/-- Two-step decoding of a doubled `true` bit. -/
private theorem pairSplit_true_bit_step {k : ℕ} (xIdx yIdx : Fin k)
    (hne : xIdx ≠ yIdx)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .scanX)
    (hread1 : c.input.read = Γ.one)
    (hnext1 : c.input.cells (c.input.head + 1) = Γ.one)
    (hxh : (c.work xIdx).head ≥ 1)
    (hxns : ∀ j, j ≥ 1 → (c.work xIdx).cells j ≠ Γ.start)
    (hyh : (c.work yIdx).head ≥ 1)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairSplitCoreTM xIdx yIdx).reachesIn 2 c c' ∧
      c'.state = .scanX ∧
      c'.input.head = c.input.head + 2 ∧
      c'.input.cells = c.input.cells ∧
      (c'.work xIdx).head = (c.work xIdx).head + 1 ∧
      (c'.work xIdx).cells =
        Function.update (c.work xIdx).cells (c.work xIdx).head Γ.one ∧
      c'.work yIdx = c.work yIdx := by
  obtain ⟨c1, hstep1, hst1, hc1_ih, hc1_ic, hc1_xw, hc1_yw⟩ :=
    pairSplit_scanX_true_step xIdx yIdx c hst hread1 hxh hxns hyh hyns
  have hc1_read : c1.input.read = Γ.one := by
    show c1.input.cells c1.input.head = Γ.one
    rw [hc1_ic, hc1_ih]
    exact hnext1
  have hc1_xh : (c1.work xIdx).head ≥ 1 := by rw [hc1_xw]; exact hxh
  have hc1_yh : (c1.work yIdx).head ≥ 1 := by rw [hc1_yw]; exact hyh
  have hc1_yns : ∀ j, j ≥ 1 → (c1.work yIdx).cells j ≠ Γ.start := by
    intro j hj
    rw [hc1_yw]
    exact hyns j hj
  obtain ⟨c2, hstep2, hst2, hc2_ih, hc2_ic, hc2_xh, hc2_xc, hc2_yw⟩ :=
    pairSplit_writeTrue_step xIdx yIdx hne c1 hst1 hc1_read hc1_xh hc1_yh hc1_yns
  refine ⟨c2, .step hstep1 (.step hstep2 .zero), hst2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc2_ih, hc1_ih]
  · rw [hc2_ic, hc1_ic]
  · rw [hc2_xh, hc1_xw]
  · rw [hc2_xc, hc1_xw]
  · rw [hc2_yw, hc1_yw]

/-- Two-step recognition of the separator `01`, transitioning from the
front-half decoder into `.copyY`. -/
private theorem pairSplit_separator_step {k : ℕ} (xIdx yIdx : Fin k)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .scanX)
    (hread0 : c.input.read = Γ.zero)
    (hnext1 : c.input.cells (c.input.head + 1) = Γ.one)
    (hxh : (c.work xIdx).head ≥ 1)
    (hxns : ∀ j, j ≥ 1 → (c.work xIdx).cells j ≠ Γ.start)
    (hyh : (c.work yIdx).head ≥ 1)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairSplitCoreTM xIdx yIdx).reachesIn 2 c c' ∧
      c'.state = .copyY ∧
      c'.input.head = c.input.head + 2 ∧
      c'.input.cells = c.input.cells ∧
      c'.work xIdx = c.work xIdx ∧
      c'.work yIdx = c.work yIdx := by
  obtain ⟨c1, hstep1, hst1, hc1_ih, hc1_ic, hc1_xw, hc1_yw⟩ :=
    pairSplit_scanX_false_step xIdx yIdx c hst hread0 hxh hxns hyh hyns
  have hc1_read : c1.input.read = Γ.one := by
    show c1.input.cells c1.input.head = Γ.one
    rw [hc1_ic, hc1_ih]
    exact hnext1
  have hc1_xh : (c1.work xIdx).head ≥ 1 := by rw [hc1_xw]; exact hxh
  have hc1_yh : (c1.work yIdx).head ≥ 1 := by rw [hc1_yw]; exact hyh
  have hc1_xns : ∀ j, j ≥ 1 → (c1.work xIdx).cells j ≠ Γ.start := by
    intro j hj
    rw [hc1_xw]
    exact hxns j hj
  have hc1_yns : ∀ j, j ≥ 1 → (c1.work yIdx).cells j ≠ Γ.start := by
    intro j hj
    rw [hc1_yw]
    exact hyns j hj
  obtain ⟨c2, hstep2, hst2, hc2_ih, hc2_ic, hc2_xw, hc2_yw⟩ :=
    pairSplit_afterFalse_sep_step xIdx yIdx c1 hst1 hc1_read hc1_xh hc1_xns hc1_yh hc1_yns
  refine ⟨c2, .step hstep1 (.step hstep2 .zero), hst2, ?_, ?_, ?_, ?_⟩
  · rw [hc2_ih, hc1_ih]
  · rw [hc2_ic, hc1_ic]
  · rw [hc2_xw, hc1_xw]
  · rw [hc2_yw, hc1_yw]

-- ════════════════════════════════════════════════════════════════════════
-- Front-half decoding loop
-- ════════════════════════════════════════════════════════════════════════

/-- Decode a doubled-bit prefix into `xIdx`. Starting in `.scanX` on an input
segment encoding `bits`, the machine consumes `2 * |bits|` input cells,
writes `bits` to `xIdx`, and returns to `.scanX`, leaving `yIdx` unchanged. -/
private theorem pairSplit_scanX_loop {k : ℕ} (xIdx yIdx : Fin k)
    (hne : xIdx ≠ yIdx) :
    ∀ (bits : List Bool) (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q),
      c.state = .scanX →
      c.input.head ≥ 1 →
      c.input.cells 0 = Γ.start →
      (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
      (∀ i, (h : i < bits.length) →
        c.input.cells (c.input.head + 2 * i) = Γ.ofBool (bits[i]'h) ∧
        c.input.cells (c.input.head + (2 * i + 1)) = Γ.ofBool (bits[i]'h)) →
      (c.work xIdx).head ≥ 1 →
      (c.work xIdx).cells 0 = Γ.start →
      (∀ j, j ≥ 1 → (c.work xIdx).cells j ≠ Γ.start) →
      (c.work yIdx).head ≥ 1 →
      (∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) →
      ∃ c',
        (pairSplitCoreTM xIdx yIdx).reachesIn (2 * bits.length) c c' ∧
        c'.state = .scanX ∧
        c'.input.head = c.input.head + 2 * bits.length ∧
        c'.input.cells = c.input.cells ∧
        (c'.work xIdx).head = (c.work xIdx).head + bits.length ∧
        (c'.work xIdx).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (c'.work xIdx).cells j ≠ Γ.start) ∧
        (∀ j, j < (c.work xIdx).head → (c'.work xIdx).cells j = (c.work xIdx).cells j) ∧
        (∀ j, j ≥ (c.work xIdx).head + bits.length →
            (c'.work xIdx).cells j = (c.work xIdx).cells j) ∧
        (∀ i, (h : i < bits.length) →
            (c'.work xIdx).cells ((c.work xIdx).head + i) = Γ.ofBool (bits[i]'h)) ∧
        c'.work yIdx = c.work yIdx := by
  intro bits
  induction bits with
  | nil =>
      intro c hst _ _ _ _ _ hxc0 hxns _ _
      refine ⟨c, by simpa using (TM.reachesIn.zero (tm := pairSplitCoreTM xIdx yIdx) (c := c)),
        hst, by simp, rfl, by simp, hxc0, hxns, ?_, ?_, ?_, rfl⟩
      · intro j _; rfl
      · intro j _; rfl
      · intro i h
        cases h
  | cons b bs ih =>
      intro c hst hih hic0 hins hbits hxh hxc0 hxns hyh hyns
      have hbits0 := hbits 0 (by simp)
      cases b with
      | false =>
          have hread0 : c.input.read = Γ.zero := by
            show c.input.cells c.input.head = Γ.zero
            simpa [Γ.ofBool] using hbits0.1
          have hnext0 : c.input.cells (c.input.head + 1) = Γ.zero := by
            simpa [Γ.ofBool] using hbits0.2
          obtain ⟨c1, hreach1, hst1, hc1_ih, hc1_ic, hc1_xh, hc1_xc, hc1_yw⟩ :=
            pairSplit_false_bit_step xIdx yIdx hne c hst hread0 hnext0 hxh hxns hyh hyns
          have hc1_ih_ge : c1.input.head ≥ 1 := by rw [hc1_ih]; omega
          have hc1_ic0 : c1.input.cells 0 = Γ.start := by rw [hc1_ic]; exact hic0
          have hc1_ins : ∀ j, j ≥ 1 → c1.input.cells j ≠ Γ.start := by
            intro j hj
            rw [hc1_ic]
            exact hins j hj
          have hc1_hbits : ∀ i, (h : i < bs.length) →
              c1.input.cells (c1.input.head + 2 * i) = Γ.ofBool (bs[i]'h) ∧
              c1.input.cells (c1.input.head + (2 * i + 1)) = Γ.ofBool (bs[i]'h) := by
            intro i hi
            have horig := hbits (i + 1) (by simpa using hi)
            constructor
            · rw [hc1_ic, hc1_ih]
              have hshift : c.input.head + 2 + 2 * i = c.input.head + 2 * (i + 1) := by ring
              simpa [hshift] using horig.1
            · rw [hc1_ic, hc1_ih]
              have hshift :
                  c.input.head + 2 + (2 * i + 1) = c.input.head + (2 * (i + 1) + 1) := by ring
              simpa [hshift] using horig.2
          have hc1_xh_ge : (c1.work xIdx).head ≥ 1 := by rw [hc1_xh]; omega
          have hc1_xc0 : (c1.work xIdx).cells 0 = Γ.start := by
            rw [hc1_xc, Function.update_of_ne (by omega)]
            exact hxc0
          have hc1_xns : ∀ j, j ≥ 1 → (c1.work xIdx).cells j ≠ Γ.start := by
            intro j hj
            rw [hc1_xc]
            by_cases hjx : j = (c.work xIdx).head
            · rw [hjx, Function.update_self]
              exact Γ.ofBool_ne_start false
            · rw [Function.update_of_ne hjx]
              exact hxns j hj
          have hc1_yh : (c1.work yIdx).head ≥ 1 := by rw [hc1_yw]; exact hyh
          have hc1_yns : ∀ j, j ≥ 1 → (c1.work yIdx).cells j ≠ Γ.start := by
            intro j hj
            rw [hc1_yw]
            exact hyns j hj
          obtain ⟨c', hreach, hst', hc_ih, hc_ic, hc_xh, hc_xc0, hc_xns,
                  hc_below, hc_above, hc_data, hc_yw⟩ :=
            ih c1 hst1 hc1_ih_ge hc1_ic0 hc1_ins hc1_hbits hc1_xh_ge hc1_xc0 hc1_xns hc1_yh hc1_yns
          have hreach_total :
              (pairSplitCoreTM xIdx yIdx).reachesIn (2 * (List.length (false :: bs))) c c' := by
            have htot : (pairSplitCoreTM xIdx yIdx).reachesIn (2 + 2 * bs.length) c c' :=
              reachesIn_trans _ hreach1 hreach
            have heq : 2 * (List.length (false :: bs)) = 2 + 2 * bs.length := by
              simp
              omega
            rw [heq]
            exact htot
          refine ⟨c', hreach_total, hst', ?_, ?_, ?_, hc_xc0, hc_xns, ?_, ?_, ?_, ?_⟩
          · rw [hc_ih, hc1_ih]
            simp
            omega
          · rw [hc_ic, hc1_ic]
          · rw [hc_xh, hc1_xh]
            simp
            omega
          · intro j hj
            have hj1 : j < (c1.work xIdx).head := by rw [hc1_xh]; omega
            rw [hc_below j hj1, hc1_xc, Function.update_of_ne (Nat.ne_of_lt hj)]
          · intro j hj
            have hj' : j ≥ (c.work xIdx).head + (bs.length + 1) := by
              simpa using hj
            have hj1 : j ≥ (c1.work xIdx).head + bs.length := by
              rw [hc1_xh]
              omega
            rw [hc_above j hj1, hc1_xc, Function.update_of_ne (by omega)]
          · intro i hi
            cases i with
            | zero =>
                have hp0 : (c.work xIdx).head + 0 = (c.work xIdx).head := by omega
                rw [hp0]
                have hj1 : (c.work xIdx).head < (c1.work xIdx).head := by rw [hc1_xh]; omega
                rw [hc_below _ hj1, hc1_xc, Function.update_self]
                rfl
            | succ i =>
                have hi' : i < bs.length := by simpa using hi
                have hdata' := hc_data i hi'
                have hpos : (c.work xIdx).head + (i + 1) = (c1.work xIdx).head + i := by
                  rw [hc1_xh]
                  omega
                rw [hpos, hdata']
                rfl
          · rw [hc_yw, hc1_yw]
      | true =>
          have hread1 : c.input.read = Γ.one := by
            show c.input.cells c.input.head = Γ.one
            simpa [Γ.ofBool] using hbits0.1
          have hnext1 : c.input.cells (c.input.head + 1) = Γ.one := by
            simpa [Γ.ofBool] using hbits0.2
          obtain ⟨c1, hreach1, hst1, hc1_ih, hc1_ic, hc1_xh, hc1_xc, hc1_yw⟩ :=
            pairSplit_true_bit_step xIdx yIdx hne c hst hread1 hnext1 hxh hxns hyh hyns
          have hc1_ih_ge : c1.input.head ≥ 1 := by rw [hc1_ih]; omega
          have hc1_ic0 : c1.input.cells 0 = Γ.start := by rw [hc1_ic]; exact hic0
          have hc1_ins : ∀ j, j ≥ 1 → c1.input.cells j ≠ Γ.start := by
            intro j hj
            rw [hc1_ic]
            exact hins j hj
          have hc1_hbits : ∀ i, (h : i < bs.length) →
              c1.input.cells (c1.input.head + 2 * i) = Γ.ofBool (bs[i]'h) ∧
              c1.input.cells (c1.input.head + (2 * i + 1)) = Γ.ofBool (bs[i]'h) := by
            intro i hi
            have horig := hbits (i + 1) (by simpa using hi)
            constructor
            · rw [hc1_ic, hc1_ih]
              have hshift : c.input.head + 2 + 2 * i = c.input.head + 2 * (i + 1) := by ring
              simpa [hshift] using horig.1
            · rw [hc1_ic, hc1_ih]
              have hshift :
                  c.input.head + 2 + (2 * i + 1) = c.input.head + (2 * (i + 1) + 1) := by ring
              simpa [hshift] using horig.2
          have hc1_xh_ge : (c1.work xIdx).head ≥ 1 := by rw [hc1_xh]; omega
          have hc1_xc0 : (c1.work xIdx).cells 0 = Γ.start := by
            rw [hc1_xc, Function.update_of_ne (by omega)]
            exact hxc0
          have hc1_xns : ∀ j, j ≥ 1 → (c1.work xIdx).cells j ≠ Γ.start := by
            intro j hj
            rw [hc1_xc]
            by_cases hjx : j = (c.work xIdx).head
            · rw [hjx, Function.update_self]
              exact Γ.ofBool_ne_start true
            · rw [Function.update_of_ne hjx]
              exact hxns j hj
          have hc1_yh : (c1.work yIdx).head ≥ 1 := by rw [hc1_yw]; exact hyh
          have hc1_yns : ∀ j, j ≥ 1 → (c1.work yIdx).cells j ≠ Γ.start := by
            intro j hj
            rw [hc1_yw]
            exact hyns j hj
          obtain ⟨c', hreach, hst', hc_ih, hc_ic, hc_xh, hc_xc0, hc_xns,
                  hc_below, hc_above, hc_data, hc_yw⟩ :=
            ih c1 hst1 hc1_ih_ge hc1_ic0 hc1_ins hc1_hbits hc1_xh_ge hc1_xc0 hc1_xns hc1_yh hc1_yns
          have hreach_total :
              (pairSplitCoreTM xIdx yIdx).reachesIn (2 * (List.length (true :: bs))) c c' := by
            have htot : (pairSplitCoreTM xIdx yIdx).reachesIn (2 + 2 * bs.length) c c' :=
              reachesIn_trans _ hreach1 hreach
            have heq : 2 * (List.length (true :: bs)) = 2 + 2 * bs.length := by
              simp
              omega
            rw [heq]
            exact htot
          refine ⟨c', hreach_total, hst', ?_, ?_, ?_, hc_xc0, hc_xns, ?_, ?_, ?_, ?_⟩
          · rw [hc_ih, hc1_ih]
            simp
            omega
          · rw [hc_ic, hc1_ic]
          · rw [hc_xh, hc1_xh]
            simp
            omega
          · intro j hj
            have hj1 : j < (c1.work xIdx).head := by rw [hc1_xh]; omega
            rw [hc_below j hj1, hc1_xc, Function.update_of_ne (Nat.ne_of_lt hj)]
          · intro j hj
            have hj' : j ≥ (c.work xIdx).head + (bs.length + 1) := by
              simpa using hj
            have hj1 : j ≥ (c1.work xIdx).head + bs.length := by
              rw [hc1_xh]
              omega
            rw [hc_above j hj1, hc1_xc, Function.update_of_ne (by omega)]
          · intro i hi
            cases i with
            | zero =>
                have hp0 : (c.work xIdx).head + 0 = (c.work xIdx).head := by omega
                rw [hp0]
                have hj1 : (c.work xIdx).head < (c1.work xIdx).head := by rw [hc1_xh]; omega
                rw [hc_below _ hj1, hc1_xc, Function.update_self]
                rfl
            | succ i =>
                have hi' : i < bs.length := by simpa using hi
                have hdata' := hc_data i hi'
                have hpos : (c.work xIdx).head + (i + 1) = (c1.work xIdx).head + i := by
                  rw [hc1_xh]
                  omega
                rw [hpos, hdata']
                rfl
          · rw [hc_yw, hc1_yw]

/-- In `.copyY`, reading blank halts immediately with every tracked tape
stable. -/
private theorem pairSplit_copyY_halt_step {k : ℕ} (xIdx yIdx : Fin k)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .copyY) (hiread : c.input.read = Γ.blank)
    (hxread : (c.work xIdx).read = Γ.blank)
    (hyread : (c.work yIdx).read = Γ.blank) :
    ∃ c', (pairSplitCoreTM xIdx yIdx).step c = some c' ∧
      c'.state = .done ∧
      c'.input = c.input ∧
      c'.work xIdx = c.work xIdx ∧
      c'.work yIdx = c.work yIdx := by
  simp only [TM.step, hst, pairSplitCoreTM, ite_eq_left hiread, pairSplitIdle]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · simp [hiread, idleDir, Tape.move]
  · have hxread_ns : (c.work xIdx).read ≠ Γ.start := by simp [hxread]
    simpa [transitionTape, readBackWrite, hxread] using
      (transitionTape_eq_self hxread_ns)
  · have hyread_ns : (c.work yIdx).read ≠ Γ.start := by simp [hyread]
    simpa [transitionTape, readBackWrite, hyread] using
      (transitionTape_eq_self hyread_ns)

/-- In `.copyY`, reading a data bit copies that bit to `yIdx`, advancing
both the input head and `yIdx`, while leaving `xIdx` unchanged. -/
private theorem pairSplit_copyY_cont_step {k : ℕ} (xIdx yIdx : Fin k)
    (hne : xIdx ≠ yIdx)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .copyY) (hiread_nb : c.input.read ≠ Γ.blank)
    (hiread_ns : c.input.read ≠ Γ.start)
    (hxh : (c.work xIdx).head ≥ 1)
    (hxns : ∀ j, j ≥ 1 → (c.work xIdx).cells j ≠ Γ.start)
    (hyh : (c.work yIdx).head ≥ 1) :
    ∃ c', (pairSplitCoreTM xIdx yIdx).step c = some c' ∧
      c'.state = .copyY ∧
      c'.input.head = c.input.head + 1 ∧
      c'.input.cells = c.input.cells ∧
      c'.work xIdx = c.work xIdx ∧
      (c'.work yIdx).head = (c.work yIdx).head + 1 ∧
      (c'.work yIdx).cells =
        Function.update (c.work yIdx).cells (c.work yIdx).head c.input.read := by
  simp only [TM.step, hst, pairSplitCoreTM, ite_eq_right hiread_nb]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Tape.move]
  ·
    simpa using (Tape.move_cells c.input Dir3.right)
  · simp only [ite_eq_right hne]
    exact tape_writeAndMove_stable (c.work xIdx) hxh hxns
  · dsimp only []
    simp only [↓reduceIte]
    simp only [Tape.writeAndMove, Tape.move, Tape.write_head]
  · have hwrite :
        (match c.input.read with
          | .zero => Γw.zero
          | .one => Γw.one
          | .blank => Γw.blank
          | .start => Γw.blank).toΓ = c.input.read := by
        cases hread : c.input.read with
        | zero => rfl
        | one => rfl
        | blank => exact (hiread_nb hread).elim
        | start => exact (hiread_ns hread).elim
    dsimp only []
    simp only [↓reduceIte]
    unfold Tape.writeAndMove
    rw [Tape.move_cells]
    unfold Tape.write
    rw [ite_eq_right (show (c.work yIdx).head ≠ 0 from by omega)]
    change Function.update (c.work yIdx).cells (c.work yIdx).head _ =
      Function.update (c.work yIdx).cells (c.work yIdx).head _
    exact congrArg (Function.update (c.work yIdx).cells (c.work yIdx).head) hwrite

/-- Linear `copyY` loop. Starting in `.copyY`, if the next `m` input cells are
data bits, then after `m` steps those cells have been copied to `yIdx`, the
input and `yIdx` heads have each advanced by `m`, and `xIdx` is unchanged. -/
private theorem pairSplit_copyY_loop {k : ℕ} (xIdx yIdx : Fin k)
    (hne : xIdx ≠ yIdx) :
    ∀ (m : ℕ) (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q),
      c.state = .copyY →
      c.input.head ≥ 1 →
      c.input.cells 0 = Γ.start →
      (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
      (∀ i, i < m → c.input.cells (c.input.head + i) ≠ Γ.blank ∧
                      c.input.cells (c.input.head + i) ≠ Γ.start) →
      (c.work xIdx).head ≥ 1 →
      (∀ j, j ≥ 1 → (c.work xIdx).cells j ≠ Γ.start) →
      (c.work yIdx).head ≥ 1 →
      (c.work yIdx).cells 0 = Γ.start →
      (∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) →
      ∃ c',
        (pairSplitCoreTM xIdx yIdx).reachesIn m c c' ∧
        c'.state = .copyY ∧
        c'.input.head = c.input.head + m ∧
        c'.input.cells = c.input.cells ∧
        c'.work xIdx = c.work xIdx ∧
        (c'.work yIdx).head = (c.work yIdx).head + m ∧
        (c'.work yIdx).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (c'.work yIdx).cells j ≠ Γ.start) ∧
        (∀ j, j < (c.work yIdx).head → (c'.work yIdx).cells j = (c.work yIdx).cells j) ∧
        (∀ j, j ≥ (c.work yIdx).head + m →
            (c'.work yIdx).cells j = (c.work yIdx).cells j) ∧
        (∀ i, i < m →
            (c'.work yIdx).cells ((c.work yIdx).head + i) =
              c.input.cells (c.input.head + i)) := by
  intro m
  induction m with
  | zero =>
      intro c hst hih hic0 hins hdata hxh hxns hyh hyc0 hyns
      refine ⟨c, .zero, hst, by omega, rfl, rfl, by omega, hyc0, hyns, ?_, ?_, ?_⟩
      · intro j _; rfl
      · intro j _; rfl
      · intro i hi; exact absurd hi (by omega)
  | succ m ih =>
      intro c hst hih hic0 hins hdata hxh hxns hyh hyc0 hyns
      have hiread_nb : c.input.read ≠ Γ.blank := (hdata 0 (by omega)).1
      have hiread_ns : c.input.read ≠ Γ.start := (hdata 0 (by omega)).2
      obtain ⟨c1, hstep1, hst1, hih1, hic1, hxw1, hyh1, hyc1⟩ :=
        pairSplit_copyY_cont_step xIdx yIdx hne c hst hiread_nb hiread_ns
          hxh hxns hyh
      have hih1_ge : c1.input.head ≥ 1 := by rw [hih1]; omega
      have hic01 : c1.input.cells 0 = Γ.start := by rw [hic1]; exact hic0
      have hins1 : ∀ j, j ≥ 1 → c1.input.cells j ≠ Γ.start := by
        intro j hj
        rw [hic1]
        exact hins j hj
      have hxh1 : (c1.work xIdx).head ≥ 1 := by rw [hxw1]; exact hxh
      have hxns1 : ∀ j, j ≥ 1 → (c1.work xIdx).cells j ≠ Γ.start := by
        intro j hj
        rw [hxw1]
        exact hxns j hj
      have hyh1_ge : (c1.work yIdx).head ≥ 1 := by rw [hyh1]; omega
      have hyc01 : (c1.work yIdx).cells 0 = Γ.start := by
        rw [hyc1, Function.update_of_ne (by omega)]
        exact hyc0
      have hyns1 : ∀ j, j ≥ 1 → (c1.work yIdx).cells j ≠ Γ.start := by
        intro j hj
        rw [hyc1]
        by_cases hj1 : j = (c.work yIdx).head
        · rw [hj1, Function.update_self]
          exact hiread_ns
        · rw [Function.update_of_ne hj1]
          exact hyns j hj
      have hdata1 : ∀ i, i < m →
          c1.input.cells (c1.input.head + i) ≠ Γ.blank ∧
          c1.input.cells (c1.input.head + i) ≠ Γ.start := by
        intro i hi
        have hshift : c1.input.head + i = c.input.head + (i + 1) := by
          rw [hih1]
          omega
        rw [hic1, hshift]
        exact hdata (i + 1) (by omega)
      obtain ⟨c', hreach, hst', hc_ih, hc_ic, hc_xw, hc_yh, hc_yc0, hc_yns,
              hc_below, hc_above, hc_data⟩ :=
        ih c1 hst1 hih1_ge hic01 hins1 hdata1 hxh1 hxns1 hyh1_ge hyc01 hyns1
      have hreach_total : (pairSplitCoreTM xIdx yIdx).reachesIn (m + 1) c c' := by
        have h1 : (pairSplitCoreTM xIdx yIdx).reachesIn 1 c c1 := .step hstep1 .zero
        have htot : (pairSplitCoreTM xIdx yIdx).reachesIn (1 + m) c c' :=
          reachesIn_trans _ h1 hreach
        have heq : m + 1 = 1 + m := by ring
        rw [heq]
        exact htot
      refine ⟨c', hreach_total, hst', ?_, ?_, ?_, ?_, hc_yc0, hc_yns, ?_, ?_, ?_⟩
      · rw [hc_ih, hih1]
        omega
      · rw [hc_ic, hic1]
      · rw [hc_xw, hxw1]
      · rw [hc_yh, hyh1]
        omega
      · intro j hj
        have hj1 : j < (c1.work yIdx).head := by rw [hyh1]; omega
        rw [hc_below j hj1, hyc1, Function.update_of_ne (by omega)]
      · intro j hj
        have hj1 : j ≥ (c1.work yIdx).head + m := by rw [hyh1]; omega
        rw [hc_above j hj1, hyc1, Function.update_of_ne (by omega)]
      · intro i hi
        by_cases hi0 : i = 0
        · subst hi0
          have hp0 : (c.work yIdx).head + 0 = (c.work yIdx).head := by omega
          rw [hp0]
          have hj1 : (c.work yIdx).head < (c1.work yIdx).head := by rw [hyh1]; omega
          rw [hc_below _ hj1, hyc1, Function.update_self]
          have hzero : c.input.head + 0 = c.input.head := by omega
          rw [hzero]
          rfl
        · have hi_pred : i - 1 < m := by omega
          have hdata' := hc_data (i - 1) hi_pred
          have hp : (c.work yIdx).head + i = (c1.work yIdx).head + (i - 1) := by
            rw [hyh1]
            omega
          have hq : c.input.head + i = c1.input.head + (i - 1) := by
            rw [hih1]
            omega
          rw [hp, hdata', hic1, hq]

/-- Exact suffix-copy theorem for `.copyY`: when the input head is positioned
at a segment encoding `y`, followed by blank, and `yIdx` is the empty started
tape, the machine copies `y` to `yIdx` and halts in `|y| + 1` steps. `xIdx`
is preserved provided its head is already sitting on blank. -/
private theorem pairSplit_copyY_from_input_segment {k : ℕ}
    (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx) (y : List Bool)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .copyY)
    (hih : c.input.head ≥ 1)
    (hic0 : c.input.cells 0 = Γ.start)
    (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hbits : ∀ i, (h : i < y.length) →
      c.input.cells (c.input.head + i) = Γ.ofBool (y[i]'h))
    (hblank : c.input.cells (c.input.head + y.length) = Γ.blank)
    (hxh : (c.work xIdx).head ≥ 1)
    (hxns : ∀ j, j ≥ 1 → (c.work xIdx).cells j ≠ Γ.start)
    (hxread : (c.work xIdx).read = Γ.blank)
    (hyw : c.work yIdx = (Tape.init []).move Dir3.right) :
    ∃ c',
      (pairSplitCoreTM xIdx yIdx).reachesIn (y.length + 1) c c' ∧
      (pairSplitCoreTM xIdx yIdx).halted c' ∧
      c'.input.head = c.input.head + y.length ∧
      c'.input.cells = c.input.cells ∧
      c'.work xIdx = c.work xIdx ∧
      (c'.work yIdx).head = 1 + y.length ∧
      (c'.work yIdx).cells 0 = Γ.start ∧
      (∀ i, (h : i < y.length) →
        (c'.work yIdx).cells (i + 1) = Γ.ofBool (y[i]'h)) ∧
      (∀ i, y.length ≤ i → (c'.work yIdx).cells (i + 1) = Γ.blank) := by
  have hyh : (c.work yIdx).head = 1 := by
    rw [hyw]
    rfl
  have hyh_ge : (c.work yIdx).head ≥ 1 := by rw [hyh]
  have hyc0 : (c.work yIdx).cells 0 = Γ.start := by
    rw [hyw, Tape.move_cells]
    rfl
  have hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start := by
    intro j hj
    rw [hyw, Tape.move_cells]
    exact Tape.init_nil_move_right_cells_ne_start j hj
  have hdata : ∀ i, i < y.length →
      c.input.cells (c.input.head + i) ≠ Γ.blank ∧
      c.input.cells (c.input.head + i) ≠ Γ.start := by
    intro i hi
    rw [hbits i hi]
    exact ⟨Γ.ofBool_ne_blank _, Γ.ofBool_ne_start _⟩
  obtain ⟨c1, hreach, hst1, hc1_ih, hc1_ic, hc1_xw, hc1_yh, hc1_yc0, hc1_yns,
          hc1_below, hc1_above, hc1_data⟩ :=
    pairSplit_copyY_loop xIdx yIdx hne y.length c hst hih hic0 hins hdata
      hxh hxns hyh_ge hyc0 hyns
  have hc1_ih_val : c1.input.head = c.input.head + y.length := hc1_ih
  have hc1_yh_val : (c1.work yIdx).head = 1 + y.length := by
    rw [hc1_yh, hyh]
  have hc1_yread : (c1.work yIdx).read = Γ.blank := by
    show (c1.work yIdx).cells ((c1.work yIdx).head) = Γ.blank
    rw [hc1_yh_val]
    have habove : 1 + y.length ≥ (c.work yIdx).head + y.length := by
      rw [hyh]
    rw [hc1_above (1 + y.length) habove, hyw, Tape.move_cells]
    simp [Nat.add_comm]
  have hc1_xread : (c1.work xIdx).read = Γ.blank := by
    rw [hc1_xw]
    exact hxread
  have hc1_iread : c1.input.read = Γ.blank := by
    show c1.input.cells c1.input.head = Γ.blank
    rw [hc1_ic, hc1_ih_val]
    exact hblank
  obtain ⟨c2, hstep2, hhalt, hc2_inp, hc2_xw, hc2_yw⟩ :=
    pairSplit_copyY_halt_step xIdx yIdx c1 hst1 hc1_iread hc1_xread hc1_yread
  have hreach_total : (pairSplitCoreTM xIdx yIdx).reachesIn (y.length + 1) c c2 := by
    exact reachesIn_trans _ hreach (.step hstep2 .zero)
  refine ⟨c2, hreach_total, hhalt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc2_inp, hc1_ih_val]
  · rw [hc2_inp, hc1_ic]
  · rw [hc2_xw, hc1_xw]
  · rw [hc2_yw, hc1_yh_val]
  · rw [hc2_yw]
    exact hc1_yc0
  · intro i hi
    rw [hc2_yw]
    have hpos : i + 1 = (c.work yIdx).head + i := by rw [hyh]; omega
    rw [hpos, hc1_data i hi, hbits i hi]
  · intro i hi
    rw [hc2_yw]
    have habove : i + 1 ≥ (c.work yIdx).head + y.length := by rw [hyh]; omega
    rw [hc1_above (i + 1) habove, hyw, Tape.move_cells]
    exact Tape.init_nil_cells_succ i

/-- Core correctness for valid started inputs. Beginning in `.scanX` with
`pair x y` on the input tape and empty started work tapes, `pairSplitCoreTM`
halts after decoding the doubled `x` prefix onto `xIdx` and copying the
suffix `y` onto `yIdx`. The two work heads finish just past the strings they
wrote. -/
theorem pairSplitCoreTM_from_scanX_initTape_move_right_internal
    {k : ℕ} (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .scanX)
    (hinp : c.input = (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right)
    (hxw : c.work xIdx = (Tape.init []).move Dir3.right)
    (hyw : c.work yIdx = (Tape.init []).move Dir3.right) :
    ∃ c',
      (pairSplitCoreTM xIdx yIdx).reachesIn (2 * x.length + y.length + 3) c c' ∧
      (pairSplitCoreTM xIdx yIdx).halted c' ∧
      c'.input.head = (pair x y).length + 1 ∧
      c'.input.cells = (Tape.init ((pair x y).map Γ.ofBool)).cells ∧
      (c'.work xIdx).head = 1 + x.length ∧
      (c'.work xIdx).cells 0 = Γ.start ∧
      (∀ i, (h : i < x.length) →
        (c'.work xIdx).cells (i + 1) = Γ.ofBool (x[i]'h)) ∧
      (∀ i, x.length ≤ i → (c'.work xIdx).cells (i + 1) = Γ.blank) ∧
      (c'.work yIdx).head = 1 + y.length ∧
      (c'.work yIdx).cells 0 = Γ.start ∧
      (∀ i, (h : i < y.length) →
        (c'.work yIdx).cells (i + 1) = Γ.ofBool (y[i]'h)) ∧
      (∀ i, y.length ≤ i → (c'.work yIdx).cells (i + 1) = Γ.blank) := by
  have hc_ih : c.input.head = 1 := by
    rw [hinp]
    rfl
  have hc_ic : c.input.cells = (Tape.init ((pair x y).map Γ.ofBool)).cells := by
    rw [hinp]
    exact Tape.move_cells _ _
  have hc_ih_ge : c.input.head ≥ 1 := by
    rw [hc_ih]
  have hc_ic0 : c.input.cells 0 = Γ.start := by
    rw [hc_ic]
    rfl
  have hc_ins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start := by
    intro j hj
    rw [hc_ic]
    exact Tape.init_ofBool_cells_ne_start (pair x y) j hj
  have hc_hbits : ∀ i, (h : i < x.length) →
      c.input.cells (c.input.head + 2 * i) = Γ.ofBool (x[i]'h) ∧
      c.input.cells (c.input.head + (2 * i + 1)) = Γ.ofBool (x[i]'h) := by
    intro i hi
    constructor
    · have hpair :
          (pair x y)[2 * i]'(by rw [pair_length]; omega) = x[i]'hi :=
        pair_getElem_left_first x y i hi
      have hcell :
          (Tape.init ((pair x y).map Γ.ofBool)).cells (2 * i + 1) =
            Γ.ofBool ((pair x y)[2 * i]'(by rw [pair_length]; omega)) :=
        Tape.init_ofBool_cells_lt (pair x y) (2 * i) (by rw [pair_length]; omega)
      rw [show c.input.head + 2 * i = 2 * i + 1 by rw [hc_ih]; omega, hc_ic]
      simpa [hpair] using hcell
    · have hpair :
          (pair x y)[2 * i + 1]'(by rw [pair_length]; omega) = x[i]'hi :=
        pair_getElem_left_second x y i hi
      have hcell :
          (Tape.init ((pair x y).map Γ.ofBool)).cells (2 * i + 2) =
            Γ.ofBool ((pair x y)[2 * i + 1]'(by rw [pair_length]; omega)) := by
        simpa using
          Tape.init_ofBool_cells_lt (pair x y) (2 * i + 1) (by rw [pair_length]; omega)
      rw [show c.input.head + (2 * i + 1) = 2 * i + 2 by rw [hc_ih]; omega, hc_ic]
      simpa [hpair] using hcell
  have hxh_eq : (c.work xIdx).head = 1 := by
    rw [hxw]
    rfl
  have hxh : (c.work xIdx).head ≥ 1 := by
    rw [hxh_eq]
  have hxc0 : (c.work xIdx).cells 0 = Γ.start := by
    rw [hxw, Tape.move_cells]
    rfl
  have hxns : ∀ j, j ≥ 1 → (c.work xIdx).cells j ≠ Γ.start := by
    intro j hj
    rw [hxw]
    exact Tape.init_nil_move_right_cells_ne_start j hj
  have hyh_eq : (c.work yIdx).head = 1 := by
    rw [hyw]
    rfl
  have hyh : (c.work yIdx).head ≥ 1 := by
    rw [hyh_eq]
  have hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start := by
    intro j hj
    rw [hyw]
    exact Tape.init_nil_move_right_cells_ne_start j hj
  obtain ⟨c1, hreach_x, hc1_state, hc1_ih, hc1_ic, hc1_xh, hc1_xc0, hc1_xns,
          hc1_below, hc1_above, hc1_data, hc1_yw⟩ :=
    pairSplit_scanX_loop xIdx yIdx hne x c hst hc_ih_ge hc_ic0 hc_ins hc_hbits
      hxh hxc0 hxns hyh hyns
  have hc1_ih_val : c1.input.head = 1 + 2 * x.length := by
    rw [hc1_ih, hc_ih]
  have hc1_icells : c1.input.cells = (Tape.init ((pair x y).map Γ.ofBool)).cells := by
    rw [hc1_ic, hc_ic]
  have hc1_read0 : c1.input.read = Γ.zero := by
    show c1.input.cells c1.input.head = Γ.zero
    rw [hc1_icells, hc1_ih_val]
    have hcell :
        (Tape.init ((pair x y).map Γ.ofBool)).cells (2 * x.length + 1) =
          Γ.ofBool ((pair x y)[2 * x.length]'(by rw [pair_length]; omega)) :=
      Tape.init_ofBool_cells_lt (pair x y) (2 * x.length) (by rw [pair_length]; omega)
    rw [pair_getElem_sep_zero x y] at hcell
    simpa [Γ.ofBool, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcell
  have hc1_next1 : c1.input.cells (c1.input.head + 1) = Γ.one := by
    rw [hc1_icells, hc1_ih_val]
    have hcell :
        (Tape.init ((pair x y).map Γ.ofBool)).cells (2 * x.length + 2) =
          Γ.ofBool ((pair x y)[2 * x.length + 1]'(by rw [pair_length]; omega)) := by
      simpa using
        Tape.init_ofBool_cells_lt (pair x y) (2 * x.length + 1) (by rw [pair_length]; omega)
    rw [pair_getElem_sep_one x y] at hcell
    have hpos : 1 + 2 * x.length + 1 = 2 * x.length + 2 := by omega
    rw [hpos]
    simpa [Γ.ofBool] using hcell
  have hc1_xh_val : (c1.work xIdx).head = 1 + x.length := by
    rw [hc1_xh, hxh_eq]
  obtain ⟨c2, hreach_sep, hc2_state, hc2_ih, hc2_ic, hc2_xw, hc2_yw⟩ :=
    pairSplit_separator_step xIdx yIdx c1 hc1_state hc1_read0 hc1_next1
      (by rw [hc1_xh_val]; omega) hc1_xns (by rw [hc1_yw, hyh_eq])
      (by
        intro j hj
        rw [hc1_yw, hyw]
        exact Tape.init_nil_move_right_cells_ne_start j hj)
  have hreach_sep_total : (pairSplitCoreTM xIdx yIdx).reachesIn (2 * x.length + 2) c c2 := by
    simpa using reachesIn_trans _ hreach_x hreach_sep
  have hc2_ih_val : c2.input.head = 1 + 2 * x.length + 2 := by
    rw [hc2_ih, hc1_ih_val]
  have hc2_icells : c2.input.cells = (Tape.init ((pair x y).map Γ.ofBool)).cells := by
    rw [hc2_ic, hc1_icells]
  have hc2_ih_ge : c2.input.head ≥ 1 := by
    rw [hc2_ih_val]
    omega
  have hc2_ic0 : c2.input.cells 0 = Γ.start := by
    rw [hc2_icells]
    rfl
  have hc2_ins : ∀ j, j ≥ 1 → c2.input.cells j ≠ Γ.start := by
    intro j hj
    rw [hc2_icells]
    exact Tape.init_ofBool_cells_ne_start (pair x y) j hj
  have hc2_ybits : ∀ i, (h : i < y.length) →
      c2.input.cells (c2.input.head + i) = Γ.ofBool (y[i]'h) := by
    intro i hi
    rw [hc2_icells, hc2_ih_val]
    have hcell :=
      Tape.init_ofBool_cells_lt (pair x y) (2 * x.length + 2 + i) (by rw [pair_length]; omega)
    rw [pair_getElem_right x y i hi] at hcell
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcell
  have hc2_blank : c2.input.cells (c2.input.head + y.length) = Γ.blank := by
    rw [hc2_icells, hc2_ih_val]
    simpa [pair_length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Tape.init_ofBool_cells_ge (pair x y) ((pair x y).length) (le_rfl)
  have hc2_xh_ge : (c2.work xIdx).head ≥ 1 := by
    rw [hc2_xw, hc1_xh_val]
    omega
  have hc2_xns : ∀ j, j ≥ 1 → (c2.work xIdx).cells j ≠ Γ.start := by
    intro j hj
    rw [hc2_xw]
    exact hc1_xns j hj
  have hc2_xread : (c2.work xIdx).read = Γ.blank := by
    show (c2.work xIdx).cells ((c2.work xIdx).head) = Γ.blank
    rw [hc2_xw, hc1_xh_val]
    have habove : 1 + x.length ≥ (c.work xIdx).head + x.length := by
      rw [hxh_eq]
    rw [hc1_above (1 + x.length) habove, hxw, Tape.move_cells]
    simp [Nat.add_comm]
  have hc2_yw_init : c2.work yIdx = (Tape.init []).move Dir3.right := by
    rw [hc2_yw, hc1_yw]
    exact hyw
  obtain ⟨c3, hreach_y, hhalt, hc3_ih, hc3_ic, hc3_xw, hc3_yh, hc3_yc0, hc3_ydata, hc3_ytail⟩ :=
    pairSplit_copyY_from_input_segment xIdx yIdx hne y c2 hc2_state hc2_ih_ge hc2_ic0 hc2_ins
      hc2_ybits hc2_blank hc2_xh_ge hc2_xns hc2_xread hc2_yw_init
  have hreach_total : (pairSplitCoreTM xIdx yIdx).reachesIn (2 * x.length + y.length + 3) c c3 := by
    have htot :
        (pairSplitCoreTM xIdx yIdx).reachesIn (y.length + (1 + (2 + 2 * x.length))) c c3 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        reachesIn_trans _ hreach_sep_total hreach_y
    have heq : y.length + (1 + (2 + 2 * x.length)) = 2 * x.length + y.length + 3 := by
      omega
    simpa [heq] using htot
  refine ⟨c3, hreach_total, hhalt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc3_ih]
    rw [hc2_ih_val, pair_length]
    omega
  · rw [hc3_ic, hc2_icells]
  · rw [hc3_xw, hc2_xw, hc1_xh_val]
  · rw [hc3_xw, hc2_xw]
    exact hc1_xc0
  · intro i hi
    rw [hc3_xw, hc2_xw]
    have hpos : i + 1 = (c.work xIdx).head + i := by
      rw [hxh_eq]
      omega
    rw [hpos, hc1_data i hi]
  · intro i hi
    rw [hc3_xw, hc2_xw]
    have habove : i + 1 ≥ (c.work xIdx).head + x.length := by
      rw [hxh_eq]
      omega
    rw [hc1_above (i + 1) habove, hxw, Tape.move_cells]
    exact Tape.init_nil_cells_succ i
  · rw [hc3_yh]
  · exact hc3_yc0
  · exact hc3_ydata
  · exact hc3_ytail

/-- Variant of the init step for phase composition: if the input tape and the
two tracked work tapes are already positioned past `▷`, the `.init` state
advances to `.scanX` without changing those tapes. -/
theorem pairSplit_init_step_all_started_internal {k : ℕ} (xIdx yIdx : Fin k)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .init)
    (hinp : c.input.read ≠ Γ.start)
    (hx : (c.work xIdx).read ≠ Γ.start)
    (hy : (c.work yIdx).read ≠ Γ.start) :
    ∃ c', (pairSplitCoreTM xIdx yIdx).step c = some c' ∧
      c'.state = .scanX ∧
      c'.input = c.input ∧
      c'.work xIdx = c.work xIdx ∧
      c'.work yIdx = c.work yIdx := by
  simp only [TM.step, hst, pairSplitCoreTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · exact transitionInput_eq_self hinp
  · show (c.work xIdx).writeAndMove (readBackWrite (c.work xIdx).read)
        (idleDir (c.work xIdx).read) = c.work xIdx
    exact transitionTape_eq_self hx
  · show (c.work yIdx).writeAndMove (readBackWrite (c.work yIdx).read)
        (idleDir (c.work yIdx).read) = c.work yIdx
    exact transitionTape_eq_self hy

/-- Starting from `.init` with `pair x y` already on a started input tape and
empty started work tapes, `pairSplitCoreTM` halts within `pairSplitCoreTime`,
leaving `xIdx` holding `x` and `yIdx` holding `y`, with both heads just past
the written strings. -/
theorem pairSplitCoreTM_from_init_initTape_move_right_internal
    {k : ℕ} (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .init)
    (hinp : c.input = (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right)
    (hxw : c.work xIdx = (Tape.init []).move Dir3.right)
    (hyw : c.work yIdx = (Tape.init []).move Dir3.right) :
    ∃ c',
      (pairSplitCoreTM xIdx yIdx).reachesIn (pairSplitCoreTime x.length y.length) c c' ∧
      (pairSplitCoreTM xIdx yIdx).halted c' ∧
      c'.input.head = (pair x y).length + 1 ∧
      c'.input.cells = (Tape.init ((pair x y).map Γ.ofBool)).cells ∧
      (c'.work xIdx).head = 1 + x.length ∧
      (c'.work xIdx).cells 0 = Γ.start ∧
      (∀ i, (h : i < x.length) →
        (c'.work xIdx).cells (i + 1) = Γ.ofBool (x[i]'h)) ∧
      (∀ i, x.length ≤ i → (c'.work xIdx).cells (i + 1) = Γ.blank) ∧
      (c'.work yIdx).head = 1 + y.length ∧
      (c'.work yIdx).cells 0 = Γ.start ∧
      (∀ i, (h : i < y.length) →
        (c'.work yIdx).cells (i + 1) = Γ.ofBool (y[i]'h)) ∧
      (∀ i, y.length ≤ i → (c'.work yIdx).cells (i + 1) = Γ.blank) := by
  have hinp_read : c.input.read ≠ Γ.start := by
    rw [hinp]
    show ((Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right).read ≠ Γ.start
    simp [Tape.read, Tape.move]
    exact Tape.init_ofBool_cells_ne_start (pair x y) 1 (by omega)
  have hx_read : (c.work xIdx).read ≠ Γ.start := by
    rw [hxw]
    show ((Tape.init []).move Dir3.right).read ≠ Γ.start
    simp [Tape.read, Tape.move]
  have hy_read : (c.work yIdx).read ≠ Γ.start := by
    rw [hyw]
    show ((Tape.init []).move Dir3.right).read ≠ Γ.start
    simp [Tape.read, Tape.move]
  obtain ⟨c1, hstep_init, hc1_state, hc1_inp, hc1_xw, hc1_yw⟩ :=
    pairSplit_init_step_all_started_internal xIdx yIdx c hst hinp_read hx_read hy_read
  obtain ⟨c2, hreach_core, hhalt, hc2_ih, hc2_ic, hc2_xh, hc2_xc0, hc2_xdata,
          hc2_xtail, hc2_yh, hc2_yc0, hc2_ydata, hc2_ytail⟩ :=
    pairSplitCoreTM_from_scanX_initTape_move_right_internal xIdx yIdx hne x y c1 hc1_state
      (by rw [hc1_inp]; exact hinp) (by rw [hc1_xw]; exact hxw) (by rw [hc1_yw]; exact hyw)
  refine ⟨c2, ?_, hhalt, hc2_ih, hc2_ic, hc2_xh, hc2_xc0, hc2_xdata, hc2_xtail,
    hc2_yh, hc2_yc0, hc2_ydata, hc2_ytail⟩
  have htot : (pairSplitCoreTM xIdx yIdx).reachesIn (1 + (2 * x.length + y.length + 3)) c c2 := by
    exact reachesIn_trans _ (.step hstep_init .zero) hreach_core
  have heq : 1 + (2 * x.length + y.length + 3) = pairSplitCoreTime x.length y.length := by
    simp [pairSplitCoreTime]
    omega
  simpa [heq] using htot

-- ════════════════════════════════════════════════
-- Stable frame facts
-- ════════════════════════════════════════════════

/-- One lifted pair-split step preserves an output tape whose head is off the
left-end marker. -/
private theorem pairSplitCoreTM_toNTM_trace_one_preserves_output
    {k : ℕ} (xIdx yIdx : Fin k) (choice : Bool)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hread : c.output.read ≠ Γ.start) :
    (((pairSplitCoreTM xIdx yIdx).toNTM).trace 1
      (fun _ => choice) c).output = c.output := by
  have hpres := transitionTape_eq_self hread
  by_cases hhalt : c.state = PairSplitPhase.done
  · simp [NTM.trace, TM.toNTM, pairSplitCoreTM, hhalt]
  · cases hstate : c.state
    ·
      simpa [NTM.trace, TM.toNTM, pairSplitCoreTM, pairSplitIdle, transitionTape,
        hstate]
        using hpres
    ·
      by_cases hzero : c.input.read = Γ.zero
      · simpa [NTM.trace, TM.toNTM, pairSplitCoreTM, pairSplitIdle, transitionTape,
          hstate, hzero]
          using hpres
      · by_cases hone : c.input.read = Γ.one <;>
          simpa [NTM.trace, TM.toNTM, pairSplitCoreTM, pairSplitIdle,
            transitionTape, hstate, hzero, hone] using hpres
    ·
      by_cases hzero : c.input.read = Γ.zero
      · simpa [NTM.trace, TM.toNTM, pairSplitCoreTM, pairSplitIdle, transitionTape,
          hstate, hzero]
          using hpres
      · by_cases hone : c.input.read = Γ.one <;>
          simpa [NTM.trace, TM.toNTM, pairSplitCoreTM, pairSplitIdle,
            transitionTape, hstate, hzero, hone] using hpres
    ·
      by_cases hone : c.input.read = Γ.one <;>
        simpa [NTM.trace, TM.toNTM, pairSplitCoreTM, pairSplitIdle,
          transitionTape, hstate, hone]
          using hpres
    ·
      by_cases hblank : c.input.read = Γ.blank <;>
        simpa [NTM.trace, TM.toNTM, pairSplitCoreTM, pairSplitIdle,
          transitionTape, hstate, hblank]
          using hpres
    · exact (hhalt hstate).elim

/-- One lifted pair-split step preserves every off-start work tape other than
the two destination tapes. -/
private theorem pairSplitCoreTM_toNTM_trace_one_preserves_other_work
    {k : ℕ} (xIdx yIdx otherIdx : Fin k) (choice : Bool)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hx : otherIdx ≠ xIdx) (hy : otherIdx ≠ yIdx)
    (hread : (c.work otherIdx).read ≠ Γ.start) :
    (((pairSplitCoreTM xIdx yIdx).toNTM).trace 1
      (fun _ => choice) c).work otherIdx = c.work otherIdx := by
  have hpres := transitionTape_eq_self hread
  by_cases hhalt : c.state = PairSplitPhase.done
  · simp [NTM.trace, TM.toNTM, pairSplitCoreTM, hhalt]
  · cases hstate : c.state
    ·
      simpa [NTM.trace, TM.toNTM, pairSplitCoreTM, pairSplitIdle, transitionTape,
        hstate, hx, hy]
        using hpres
    ·
      by_cases hzero : c.input.read = Γ.zero
      · simpa [NTM.trace, TM.toNTM, pairSplitCoreTM, pairSplitIdle,
          transitionTape, hstate, hzero, hx, hy] using hpres
      · by_cases hone : c.input.read = Γ.one <;>
          simpa [NTM.trace, TM.toNTM, pairSplitCoreTM, pairSplitIdle,
            transitionTape, hstate, hzero, hone, hx, hy] using hpres
    ·
      by_cases hzero : c.input.read = Γ.zero
      · simpa [NTM.trace, TM.toNTM, pairSplitCoreTM, pairSplitIdle,
          transitionTape, hstate, hzero, hx, hy] using hpres
      · by_cases hone : c.input.read = Γ.one <;>
          simpa [NTM.trace, TM.toNTM, pairSplitCoreTM, pairSplitIdle,
            transitionTape, hstate, hzero, hone, hx, hy] using hpres
    ·
      by_cases hone : c.input.read = Γ.one <;>
        simpa [NTM.trace, TM.toNTM, pairSplitCoreTM, pairSplitIdle,
          transitionTape, hstate, hone, hx, hy] using hpres
    ·
      by_cases hblank : c.input.read = Γ.blank <;>
        simpa [NTM.trace, TM.toNTM, pairSplitCoreTM, pairSplitIdle,
          transitionTape, hstate, hblank, hx, hy] using hpres
    · exact (hhalt hstate).elim

/-- Every lifted pair-split trace preserves an off-start output tape. -/
theorem pairSplitCoreTM_toNTM_trace_preserves_output_internal
    {k : ℕ} (xIdx yIdx : Fin k) (T : ℕ) (choices : Fin T → Bool)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hread : c.output.read ≠ Γ.start) :
    (((pairSplitCoreTM xIdx yIdx).toNTM).trace T choices c).output = c.output := by
  apply ((pairSplitCoreTM xIdx yIdx).toNTM).trace_invariant T choices c
    (fun _ current => current.output = c.output) rfl
  intro time htime current hcurrent
  have hreadCurrent : current.output.read ≠ Γ.start := by
    rw [hcurrent]
    exact hread
  exact (pairSplitCoreTM_toNTM_trace_one_preserves_output xIdx yIdx
    (choices ⟨time, htime⟩) current hreadCurrent).trans hcurrent

/-- Every lifted pair-split trace preserves an off-start work tape other than
the two destination tapes. -/
theorem pairSplitCoreTM_toNTM_trace_preserves_other_work_internal
    {k : ℕ} (xIdx yIdx otherIdx : Fin k) (T : ℕ) (choices : Fin T → Bool)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hx : otherIdx ≠ xIdx) (hy : otherIdx ≠ yIdx)
    (hread : (c.work otherIdx).read ≠ Γ.start) :
    (((pairSplitCoreTM xIdx yIdx).toNTM).trace T choices c).work otherIdx =
      c.work otherIdx := by
  apply ((pairSplitCoreTM xIdx yIdx).toNTM).trace_invariant T choices c
    (fun _ current => current.work otherIdx = c.work otherIdx) rfl
  intro time htime current hcurrent
  have hreadCurrent : (current.work otherIdx).read ≠ Γ.start := by
    rw [hcurrent]
    exact hread
  exact (pairSplitCoreTM_toNTM_trace_one_preserves_other_work xIdx yIdx
    otherIdx (choices ⟨time, htime⟩) current hx hy hreadCurrent).trans
      hcurrent

-- ════════════════════════════════════════════════
-- Exact endpoint from the genuine initial configuration
-- ════════════════════════════════════════════════

/-- Exact pair-split correctness from the machine's genuine initial
configuration. In addition to decoding the target tapes, the theorem frames
the output and every unrelated work tape as started and blank. -/
theorem pairSplitCoreTM_from_initCfg_internal
    {k : ℕ} (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx) (x y : List Bool) :
    ∃ c',
      (pairSplitCoreTM xIdx yIdx).reachesIn
        (pairSplitCoreTime x.length y.length)
        ((pairSplitCoreTM xIdx yIdx).initCfg (pair x y)) c' ∧
      (pairSplitCoreTM xIdx yIdx).halted c' ∧
      c'.input.head = (pair x y).length + 1 ∧
      c'.input.cells = (Tape.init ((pair x y).map Γ.ofBool)).cells ∧
      (c'.work xIdx).head = 1 + x.length ∧
      (c'.work xIdx).cells 0 = Γ.start ∧
      (∀ i, (h : i < x.length) →
        (c'.work xIdx).cells (i + 1) = Γ.ofBool (x[i]'h)) ∧
      (∀ i, x.length ≤ i → (c'.work xIdx).cells (i + 1) = Γ.blank) ∧
      (c'.work yIdx).head = 1 + y.length ∧
      (c'.work yIdx).cells 0 = Γ.start ∧
      (∀ i, (h : i < y.length) →
        (c'.work yIdx).cells (i + 1) = Γ.ofBool (y[i]'h)) ∧
      (∀ i, y.length ≤ i → (c'.work yIdx).cells (i + 1) = Γ.blank) ∧
      (∀ i, i ≠ xIdx → i ≠ yIdx →
        c'.work i = (Tape.init []).move Dir3.right) ∧
      c'.output = (Tape.init []).move Dir3.right := by
  let c1 : Cfg k (pairSplitCoreTM xIdx yIdx).Q :=
    { state := .scanX
      input := (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right
      work := fun _ => (Tape.init []).move Dir3.right
      output := (Tape.init []).move Dir3.right }
  have hstep_init :
      (pairSplitCoreTM xIdx yIdx).step
        ((pairSplitCoreTM xIdx yIdx).initCfg (pair x y)) = some c1 := by
    simp [TM.step, pairSplitCoreTM, c1, Tape.read, Tape.init, readBackWrite,
      idleDir, Tape.writeAndMove, Tape.write, Tape.move]
  obtain ⟨c2, hreach_core, hhalt, hc2_ih, hc2_ic, hc2_xh, hc2_xc0, hc2_xdata,
      hc2_xtail, hc2_yh, hc2_yc0, hc2_ydata, hc2_ytail⟩ :=
    pairSplitCoreTM_from_scanX_initTape_move_right_internal xIdx yIdx hne x y c1
      rfl rfl rfl rfl
  have hreach :
      (pairSplitCoreTM xIdx yIdx).reachesIn
        (pairSplitCoreTime x.length y.length)
        ((pairSplitCoreTM xIdx yIdx).initCfg (pair x y)) c2 := by
    have htotal :
        (pairSplitCoreTM xIdx yIdx).reachesIn
          (1 + (2 * x.length + y.length + 3))
          ((pairSplitCoreTM xIdx yIdx).initCfg (pair x y)) c2 :=
      reachesIn_trans _ (.step hstep_init .zero) hreach_core
    have heq : 1 + (2 * x.length + y.length + 3) =
        pairSplitCoreTime x.length y.length := by
      simp [pairSplitCoreTime]
      omega
    simpa [heq] using htotal
  have htrace :
      ((pairSplitCoreTM xIdx yIdx).toNTM).trace
        (2 * x.length + y.length + 3) (fun _ => false) c1 = c2 :=
    (pairSplitCoreTM xIdx yIdx).toNTM_trace_of_reachesIn
      hreach_core hhalt le_rfl (fun _ => false)
  have hother : ∀ i, i ≠ xIdx → i ≠ yIdx →
      c2.work i = (Tape.init []).move Dir3.right := by
    intro i hix hiy
    rw [← htrace]
    simpa [c1] using
      pairSplitCoreTM_toNTM_trace_preserves_other_work_internal
        xIdx yIdx i (2 * x.length + y.length + 3) (fun _ => false) c1
          hix hiy (by simp [c1])
  have hout : c2.output = (Tape.init []).move Dir3.right := by
    rw [← htrace]
    simpa [c1] using
      pairSplitCoreTM_toNTM_trace_preserves_output_internal
        xIdx yIdx (2 * x.length + y.length + 3) (fun _ => false) c1
          (by simp [c1])
  exact ⟨c2, hreach, hhalt, hc2_ih, hc2_ic, hc2_xh, hc2_xc0, hc2_xdata,
    hc2_xtail, hc2_yh, hc2_yc0, hc2_ydata, hc2_ytail, hother, hout⟩

end TM

end Complexity
