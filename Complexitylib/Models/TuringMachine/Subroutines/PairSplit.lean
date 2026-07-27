/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Hoare.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.PairSplit.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.PairSplit.Internal
public import Complexitylib.Models.TuringMachine.Tape.Encoding

/-!
# Split a paired input onto work tapes

`pairSplitCoreTM` is the deterministic machine-level inverse of the neutral
`pair` codec. On a canonical input `pair x y`, it writes `x` and `y` as
canonical binary prefixes on two distinct work tapes in exact time
`2 * |x| + |y| + 4`.

This is intentionally a canonical-pair primitive, not a total recognizer for
the image of `pair`: malformed inputs may share its halting state. A client
requiring rejecting semantics for arbitrary outer strings must use a parser
with a distinct failure result.

## Main results

- `pairSplitCoreTM_reachesIn_initCfg` — exact initialized endpoint with frames.
- `pairSplitCoreTM_from_init_initTape_move_right` — exact endpoint semantics.
- `pairSplitCoreTM_hoareTime_prefix_marker_frame` — binary prefixes, left markers,
  and preserved frames.
- `pairSplitCoreTM_hoareTime_prefix_frame` — compatibility binary-prefix
  specification with frames.
- `pairSplitCoreTM_hoareTime_prefix` — compact binary-prefix specification.
- `pairSplitCoreTM_hoareTime_frame` and `pairSplitCoreTM_hoareTime` — compatible
  `HasOutput` specifications.
-/

@[expose] public section

namespace Complexity

namespace TM

/-- On a canonical pair, the splitter's exact time is the encoded input
length plus two steps. -/
@[simp] theorem pairSplitCoreTime_eq_pair_length (x y : List Bool) :
    pairSplitCoreTime x.length y.length = (pair x y).length + 2 := by
  simp [pairSplitCoreTime, pair_length]
  omega

/-- Exact pair-split correctness from the genuine machine initialization.
The target work tapes contain the decoded components, while every unrelated
work tape and the output are the canonical started blank tape. -/
theorem pairSplitCoreTM_reachesIn_initCfg
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
      c'.output = (Tape.init []).move Dir3.right :=
  pairSplitCoreTM_from_initCfg_internal xIdx yIdx hne x y

/-- Core correctness from the already-started `.scanX` phase. This preserves
the theorem name formerly exposed from the NP-internal implementation. -/
theorem pairSplitCoreTM_from_scanX_initTape_move_right
    {k : ℕ} (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .scanX)
    (hinp : c.input = (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right)
    (hxw : c.work xIdx = (Tape.init []).move Dir3.right)
    (hyw : c.work yIdx = (Tape.init []).move Dir3.right) :
    ∃ c',
      (pairSplitCoreTM xIdx yIdx).reachesIn
        (2 * x.length + y.length + 3) c c' ∧
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
      (∀ i, y.length ≤ i → (c'.work yIdx).cells (i + 1) = Γ.blank) :=
  pairSplitCoreTM_from_scanX_initTape_move_right_internal
    xIdx yIdx hne x y c hst hinp hxw hyw

/-- One phase-composition step from `.init` to `.scanX`, preserving the
already-started input and target work tapes. -/
theorem pairSplit_init_step_all_started {k : ℕ} (xIdx yIdx : Fin k)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .init)
    (hinp : c.input.read ≠ Γ.start)
    (hx : (c.work xIdx).read ≠ Γ.start)
    (hy : (c.work yIdx).read ≠ Γ.start) :
    ∃ c', (pairSplitCoreTM xIdx yIdx).step c = some c' ∧
      c'.state = .scanX ∧
      c'.input = c.input ∧
      c'.work xIdx = c.work xIdx ∧
      c'.work yIdx = c.work yIdx :=
  pairSplit_init_step_all_started_internal xIdx yIdx c hst hinp hx hy

/-- Starting from `.init` with a canonical pair and two empty started work
tapes, `pairSplitCoreTM` halts in its exact advertised time. The two target
tapes contain the decoded components and finish immediately after them. -/
theorem pairSplitCoreTM_from_init_initTape_move_right
    {k : ℕ} (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .init)
    (hinp : c.input = (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right)
    (hxw : c.work xIdx = (Tape.init []).move Dir3.right)
    (hyw : c.work yIdx = (Tape.init []).move Dir3.right) :
    ∃ c',
      (pairSplitCoreTM xIdx yIdx).reachesIn
        (pairSplitCoreTime x.length y.length) c c' ∧
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
      (∀ i, y.length ≤ i → (c'.work yIdx).cells (i + 1) = Γ.blank) :=
  pairSplitCoreTM_from_init_initTape_move_right_internal xIdx yIdx hne x y c
    hst hinp hxw hyw

/-- Marker-aware frame-preserving specification. The decoded components are
canonical binary prefixes with their left markers intact, and the splitter
preserves an arbitrary off-start output tape and every arbitrary off-start work
tape outside the two targets. -/
theorem pairSplitCoreTM_hoareTime_prefix_marker_frame
    {k : ℕ} (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool) (frameWork : Fin k → Tape) (frameOutput : Tape)
    (hframeWork : ∀ i, i ≠ xIdx → i ≠ yIdx →
      (frameWork i).read ≠ Γ.start)
    (hframeOutput : frameOutput.read ≠ Γ.start) :
    (pairSplitCoreTM xIdx yIdx).HoareTime
      (fun inp work out =>
        inp = (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right ∧
        work xIdx = (Tape.init []).move Dir3.right ∧
        work yIdx = (Tape.init []).move Dir3.right ∧
        (∀ i, i ≠ xIdx → i ≠ yIdx → work i = frameWork i) ∧
        out = frameOutput)
      (fun inp work out =>
        inp.head = (pair x y).length + 1 ∧
        inp.cells = (Tape.init ((pair x y).map Γ.ofBool)).cells ∧
        (work xIdx).cells 0 = Γ.start ∧
        (work xIdx).HasBinaryPrefix x ∧
        (work yIdx).cells 0 = Γ.start ∧
        (work yIdx).HasBinaryPrefix y ∧
        (∀ i, i ≠ xIdx → i ≠ yIdx → work i = frameWork i) ∧
        out = frameOutput)
      (pairSplitCoreTime x.length y.length) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hxw, hyw, hwork, hout⟩
  let c : Cfg k (pairSplitCoreTM xIdx yIdx).Q :=
    { state := (pairSplitCoreTM xIdx yIdx).qstart
      input := inp
      work := work
      output := out }
  obtain ⟨c', hreach, hhalt, hinputHead, hinputCells,
      hxHead, hxStart, hxData, hxTail, hyHead, hyStart, hyData, hyTail⟩ :=
    pairSplitCoreTM_from_init_initTape_move_right_internal xIdx yIdx hne x y c
      rfl hinp hxw hyw
  have htrace :
      ((pairSplitCoreTM xIdx yIdx).toNTM).trace
        (pairSplitCoreTime x.length y.length) (fun _ => false) c = c' :=
    (pairSplitCoreTM xIdx yIdx).toNTM_trace_of_reachesIn
      hreach hhalt le_rfl (fun _ => false)
  have hother : ∀ i, i ≠ xIdx → i ≠ yIdx → c'.work i = frameWork i := by
    intro i hix hiy
    have hread : (c.work i).read ≠ Γ.start := by
      change (work i).read ≠ Γ.start
      rw [hwork i hix hiy]
      exact hframeWork i hix hiy
    have hpres := pairSplitCoreTM_toNTM_trace_preserves_other_work_internal
      xIdx yIdx i (pairSplitCoreTime x.length y.length) (fun _ => false) c
        hix hiy hread
    rw [htrace] at hpres
    exact hpres.trans (hwork i hix hiy)
  have hout' : c'.output = frameOutput := by
    have hread : c.output.read ≠ Γ.start := by
      change out.read ≠ Γ.start
      rw [hout]
      exact hframeOutput
    have hpres := pairSplitCoreTM_toNTM_trace_preserves_output_internal
      xIdx yIdx (pairSplitCoreTime x.length y.length) (fun _ => false) c hread
    rw [htrace] at hpres
    exact hpres.trans hout
  refine ⟨c', pairSplitCoreTime x.length y.length, le_rfl, hreach, hhalt,
    hinputHead, hinputCells, hxStart, ?_, hyStart, ?_, hother, hout'⟩
  · exact ⟨by simpa [Nat.add_comm] using hxHead, hxData, hxTail⟩
  · exact ⟨by simpa [Nat.add_comm] using hyHead, hyData, hyTail⟩

/-- Frame-preserving compositional specification. The decoded components are
canonical binary prefixes, and the splitter preserves an arbitrary off-start
output tape and every arbitrary off-start work tape outside the two targets. -/
theorem pairSplitCoreTM_hoareTime_prefix_frame
    {k : ℕ} (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool) (frameWork : Fin k → Tape) (frameOutput : Tape)
    (hframeWork : ∀ i, i ≠ xIdx → i ≠ yIdx →
      (frameWork i).read ≠ Γ.start)
    (hframeOutput : frameOutput.read ≠ Γ.start) :
    (pairSplitCoreTM xIdx yIdx).HoareTime
      (fun inp work out =>
        inp = (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right ∧
        work xIdx = (Tape.init []).move Dir3.right ∧
        work yIdx = (Tape.init []).move Dir3.right ∧
        (∀ i, i ≠ xIdx → i ≠ yIdx → work i = frameWork i) ∧
        out = frameOutput)
      (fun inp work out =>
        inp.head = (pair x y).length + 1 ∧
        inp.cells = (Tape.init ((pair x y).map Γ.ofBool)).cells ∧
        (work xIdx).HasBinaryPrefix x ∧
        (work yIdx).HasBinaryPrefix y ∧
        (∀ i, i ≠ xIdx → i ≠ yIdx → work i = frameWork i) ∧
        out = frameOutput)
      (pairSplitCoreTime x.length y.length) := by
  refine (pairSplitCoreTM_hoareTime_prefix_marker_frame xIdx yIdx hne x y
    frameWork frameOutput hframeWork hframeOutput).strengthen_post ?_
  intro inp work out hpost
  rcases hpost with
    ⟨hinputHead, hinputCells, -, hxPrefix, -, hyPrefix, hwork, hout⟩
  exact ⟨hinputHead, hinputCells, hxPrefix, hyPrefix, hwork, hout⟩

/-- Frame-preserving compositional specification exposing the decoded heads
and `HasOutput` facts. The prefix-strengthened form is
`pairSplitCoreTM_hoareTime_prefix_frame`. -/
theorem pairSplitCoreTM_hoareTime_frame
    {k : ℕ} (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool) (frameWork : Fin k → Tape) (frameOutput : Tape)
    (hframeWork : ∀ i, i ≠ xIdx → i ≠ yIdx →
      (frameWork i).read ≠ Γ.start)
    (hframeOutput : frameOutput.read ≠ Γ.start) :
    (pairSplitCoreTM xIdx yIdx).HoareTime
      (fun inp work out =>
        inp = (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right ∧
        work xIdx = (Tape.init []).move Dir3.right ∧
        work yIdx = (Tape.init []).move Dir3.right ∧
        (∀ i, i ≠ xIdx → i ≠ yIdx → work i = frameWork i) ∧
        out = frameOutput)
      (fun inp work out =>
        inp.head = (pair x y).length + 1 ∧
        inp.cells = (Tape.init ((pair x y).map Γ.ofBool)).cells ∧
        (work xIdx).head = 1 + x.length ∧
        (work xIdx).HasOutput x ∧
        (work yIdx).head = 1 + y.length ∧
        (work yIdx).HasOutput y ∧
        (∀ i, i ≠ xIdx → i ≠ yIdx → work i = frameWork i) ∧
        out = frameOutput)
      (pairSplitCoreTime x.length y.length) := by
  refine (pairSplitCoreTM_hoareTime_prefix_frame xIdx yIdx hne x y
    frameWork frameOutput hframeWork hframeOutput).strengthen_post ?_
  intro inp work out hpost
  rcases hpost with
    ⟨hinputHead, hinputCells, hxPrefix, hyPrefix, hwork, hout⟩
  refine ⟨hinputHead, hinputCells, ?_, ?_, ?_, ?_, hwork, hout⟩
  · simpa [Nat.add_comm] using hxPrefix.1
  · exact ⟨hxPrefix.2.1, hxPrefix.2.2 x.length le_rfl⟩
  · simpa [Nat.add_comm] using hyPrefix.1
  · exact ⟨hyPrefix.2.1, hyPrefix.2.2 y.length le_rfl⟩

/-- Compositional canonical-pair specification. The target work tapes begin
empty at cell `1`; on exit they are canonical binary prefixes for the two
decoded strings. This compact theorem makes no claim about unrelated work
tapes or the output; use `pairSplitCoreTM_hoareTime_prefix_frame` when those
frames must be preserved. -/
theorem pairSplitCoreTM_hoareTime_prefix
    {k : ℕ} (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool) :
    (pairSplitCoreTM xIdx yIdx).HoareTime
      (fun inp work _ =>
        inp = (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right ∧
        work xIdx = (Tape.init []).move Dir3.right ∧
        work yIdx = (Tape.init []).move Dir3.right)
      (fun inp work _ =>
        inp.head = (pair x y).length + 1 ∧
        inp.cells = (Tape.init ((pair x y).map Γ.ofBool)).cells ∧
        (work xIdx).HasBinaryPrefix x ∧
        (work yIdx).HasBinaryPrefix y)
      (pairSplitCoreTime x.length y.length) := by
  intro inp work out hpre
  obtain ⟨hinp, hxw, hyw⟩ := hpre
  let c : Cfg k (pairSplitCoreTM xIdx yIdx).Q :=
    { state := (pairSplitCoreTM xIdx yIdx).qstart
      input := inp
      work := work
      output := out }
  obtain ⟨c', hreach, hhalt, hinputHead, hinputCells,
      hxHead, -, hxData, hxTail, hyHead, -, hyData, hyTail⟩ :=
    pairSplitCoreTM_from_init_initTape_move_right_internal xIdx yIdx hne x y c
      rfl hinp hxw hyw
  refine ⟨c', pairSplitCoreTime x.length y.length, le_rfl, hreach, hhalt,
    hinputHead, hinputCells, ?_, ?_⟩
  · exact ⟨by simpa [Nat.add_comm] using hxHead, hxData, hxTail⟩
  · exact ⟨by simpa [Nat.add_comm] using hyHead, hyData, hyTail⟩

/-- Compact canonical-pair specification exposing the decoded heads and
`HasOutput` facts. The prefix-strengthened form is
`pairSplitCoreTM_hoareTime_prefix`. -/
theorem pairSplitCoreTM_hoareTime
    {k : ℕ} (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool) :
    (pairSplitCoreTM xIdx yIdx).HoareTime
      (fun inp work _ =>
        inp = (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right ∧
        work xIdx = (Tape.init []).move Dir3.right ∧
        work yIdx = (Tape.init []).move Dir3.right)
      (fun inp work _ =>
        inp.head = (pair x y).length + 1 ∧
        inp.cells = (Tape.init ((pair x y).map Γ.ofBool)).cells ∧
        (work xIdx).head = 1 + x.length ∧
        (work xIdx).HasOutput x ∧
        (work yIdx).head = 1 + y.length ∧
        (work yIdx).HasOutput y)
      (pairSplitCoreTime x.length y.length) := by
  refine (pairSplitCoreTM_hoareTime_prefix xIdx yIdx hne x y).strengthen_post ?_
  intro inp work out hpost
  rcases hpost with ⟨hinputHead, hinputCells, hxPrefix, hyPrefix⟩
  refine ⟨hinputHead, hinputCells, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.add_comm] using hxPrefix.1
  · exact ⟨hxPrefix.2.1, hxPrefix.2.2 x.length le_rfl⟩
  · simpa [Nat.add_comm] using hyPrefix.1
  · exact ⟨hyPrefix.2.1, hyPrefix.2.2 y.length le_rfl⟩

end TM

end Complexity
