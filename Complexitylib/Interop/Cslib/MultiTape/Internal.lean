/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Cslib.MultiTape.Defs
import Complexitylib.Models.TuringMachine.Internal
import Complexitylib.Models.TuringMachine.Frame

/-!
# Proofs for the CSLib multi-tape simulation

Two layers of proof support `Complexitylib.Interop.Cslib.MultiTape`.

- **Generic CSLib facts** (namespace `Complexity.MultiTape`): one step of a
  running configuration field by field, the input-head arithmetic, and a
  space bound of `k (t + 1)` cells.
- **The simulation** (namespace `Complexity.TM`): `MultiTapeSim` relates our
  configuration to a simulator configuration. `TapeSim` covers each one-sided
  tape with its data and marker tapes, and `ZoneOK` with `inputAction_spec`
  covers the input head. One simulator step follows each of our steps
  (`MultiTapeSim.step`). After our machine halts, the rewind phase
  (`Rewinding.run`) emits the verdict, and `toMultiTape_computesFun`
  assembles the time and space bounds.
-/


public section

namespace Complexity

open Turing

namespace MultiTape

variable {k : ℕ} {S Q : Type*} {input : List S}

/-- The effect of an optional write on a CSLib work tape. -/
@[expose] def applyWrite (cells : ℤ → Option S) (pos : ℤ) : Option (Option S) → ℤ → Option S
  | none => cells
  | some s => Function.update cells pos s

@[simp] theorem applyWrite_none (cells : ℤ → Option S) (pos : ℤ) :
    applyWrite cells pos none = cells := rfl

/-- One step from a running configuration, field by field. -/
theorem step_of_state_eq_some (M : MultiTapeTM k S Q) {d : Turing.Cfg k S Q input}
    {q : Q} (h : d.state = some q) :
    M.step d =
      { state := (M.tr q d.inputSymbol d.workTapeSymbols).state
        inputPos := moveInputPos d.inputPos (M.tr q d.inputSymbol d.workTapeSymbols).inputTape
        workTapes := fun i => applyWrite (d.workTapes i) (d.workTapePos i)
          ((M.tr q d.inputSymbol d.workTapeSymbols).workTapes i).1
        workTapePos := fun i =>
          d.workTapePos i + ((M.tr q d.inputSymbol d.workTapeSymbols).workTapes i).2
        output := d.output ++ (M.tr q d.inputSymbol d.workTapeSymbols).output.toList } := by
  obtain ⟨state, inputPos, workTapes, workTapePos, output⟩ := d
  cases h
  rfl

/-- The position reached by an input-head move. -/
theorem moveInputPos_val {m : ℕ} (p : Fin (m + 2)) (s : SignType) :
    (moveInputPos p s : ℕ) = min ((p : ℤ) + (s : ℤ)).toNat (m + 1) := by
  unfold moveInputPos
  dsimp only
  split <;> simp <;> omega

/-- The input symbol is blank exactly at the two boundary positions. -/
theorem inputSymbol_eq_none_iff (d : Turing.Cfg k S Q input) :
    d.inputSymbol = none ↔ (d.inputPos : ℕ) = 0 ∨ (d.inputPos : ℕ) = input.length + 1 := by
  unfold Cfg.inputSymbol
  split_ifs with h1 h2
  · simp [h1]
  · simp [h2]
  · simp only [false_iff, not_or]
    exact ⟨fun h => h1 (Fin.ext h), h2⟩

/-- Inside the input, the input symbol is the corresponding input letter. -/
theorem inputSymbol_of_lt (d : Turing.Cfg k S Q input) {p : ℕ}
    (hpos : (d.inputPos : ℕ) = p + 1) (hp : p < input.length) :
    d.inputSymbol = some input[p] :=
  inputSymbolInner p (by omega) hp

/-- Each work head visits at most `t + 1` cells in `t` steps, so a machine with
`k` work tapes uses at most `k * (t + 1)` cells. -/
theorem spaceUsed_le (M : MultiTapeTM k S Q) (d : Turing.Cfg k S Q input) (t : ℕ) :
    M.spaceUsed d t ≤ k * (t + 1) := by
  unfold MultiTapeTM.spaceUsed
  calc ∑ i, M.spaceUsedByTape d t i ≤ ∑ _i : Fin k, (t + 1) :=
        Finset.sum_le_sum fun i _ => by
          unfold MultiTapeTM.spaceUsedByTape MultiTapeTM.visitedByTapeHead
          exact Finset.card_image_le.trans (by simp)
    _ = k * (t + 1) := by simp

end MultiTape

namespace TM

open MultiTape

variable {n : ℕ}

@[simp] theorem Γ.ofCell_toCell (w : Γw) : Γ.ofCell w.toCell = w.toΓ := by
  cases w <;> rfl

/-- The marker tape of a simulated tape: a `1` at position 0 and blank
elsewhere. -/
def markTape : ℤ → Option Bool := fun p => if p = 0 then some true else none

/-- The data tape at `pos` with cells `cells` and the marker tape at `mpos` with
cells `marks` simulate our one-sided tape `t`: both heads at `t`'s head, data
cells `1, 2, …` equal to `t`'s (CSLib blank read as `□`), the marker tape
unchanged, and `▷` only in cell 0 of `t`. -/
structure TapeSim (t : Tape) (pos mpos : ℤ) (cells marks : ℤ → Option Bool) : Prop where
  pos : pos = t.head
  mpos : mpos = t.head
  cells : ∀ p : ℕ, 1 ≤ p → Γ.ofCell (cells p) = t.cells p
  marks : marks = markTape
  inv : t.StartInvariant

theorem TapeSim.atStart {t : Tape} {pos mpos : ℤ} {cells marks : ℤ → Option Bool}
    (h : TapeSim t pos mpos cells marks) :
    decide (marks mpos = some true) = decide (t.head = 0) := by
  rw [h.marks, h.mpos]
  by_cases h0 : t.head = 0 <;> simp [markTape, h0]

theorem TapeSim.read {t : Tape} {pos mpos : ℤ} {cells marks : ℤ → Option Bool}
    (h : TapeSim t pos mpos cells marks) :
    (if marks mpos = some true then Γ.start else Γ.ofCell (cells pos)) = t.read := by
  rw [h.marks, h.mpos, h.pos]
  by_cases h0 : t.head = 0
  · simp [markTape, h0, Tape.read, h.inv.1]
  · simp only [markTape, Nat.cast_eq_zero, h0, ite_false, reduceCtorEq]
    exact h.cells _ (by omega)

/-- `oneSidedWrite` and `oneSidedMove` simulate one write-and-move. -/
theorem TapeSim.writeAndMove {t : Tape} {pos mpos : ℤ} {cells marks : ℤ → Option Bool}
    (h : TapeSim t pos mpos cells marks) (w : Γw) (d : Dir3) :
    TapeSim (t.writeAndMove w d) (pos + oneSidedMove (decide (t.head = 0)) d)
      (mpos + oneSidedMove (decide (t.head = 0)) d)
      (applyWrite cells pos (oneSidedWrite (decide (t.head = 0)) w)) marks := by
  by_cases h0 : t.head = 0
  · have hw : t.write w.toΓ = t := by simp [Tape.write, h0]
    refine ⟨?_, ?_, fun p hp => ?_, h.marks, h.inv.writeAndMove w d⟩
    · unfold Tape.writeAndMove
      rw [hw, h.pos]
      cases d <;> simp [oneSidedMove, Tape.move, Dir3.toSign, h0]
    · unfold Tape.writeAndMove
      rw [hw, h.mpos]
      cases d <;> simp [oneSidedMove, Tape.move, Dir3.toSign, h0]
    · unfold Tape.writeAndMove
      rw [hw, Tape.move_cells]
      simpa [h0, oneSidedWrite, applyWrite] using h.cells p hp
  · refine ⟨?_, ?_, fun p hp => ?_, h.marks, h.inv.writeAndMove w d⟩
    · rw [h.pos]
      cases d <;> simp [oneSidedMove, Tape.move, Tape.write, h0, Dir3.toSign]
      omega
    · rw [h.mpos]
      cases d <;> simp [oneSidedMove, Tape.move, Tape.write, h0, Dir3.toSign]
      omega
    · unfold Tape.writeAndMove
      rw [Tape.move_cells]
      simp only [h0, decide_false, oneSidedWrite, Bool.false_eq_true, ite_false, applyWrite,
        Tape.write]
      by_cases hp' : p = t.head
      · subst hp'; simp [h.pos]
      · rw [Function.update_of_ne (by rw [h.pos]; exact_mod_cast hp'),
          Function.update_of_ne hp', h.cells p hp]

/-- Moving both heads, other than left from cell 0, keeps a tape simulated. -/
theorem TapeSim.move {t : Tape} {pos mpos : ℤ} {cells marks : ℤ → Option Bool}
    (h : TapeSim t pos mpos cells marks) (d : Dir3) (hd : d = Dir3.left → t.head ≠ 0) :
    TapeSim (t.move d) (pos + d.toSign) (mpos + d.toSign) cells marks := by
  refine ⟨?_, ?_, fun p hp => by rw [Tape.move_cells]; exact h.cells p hp, h.marks,
    h.inv.move d⟩
  · rw [h.pos]
    cases d <;> simp [Tape.move, Dir3.toSign] at hd ⊢
    omega
  · rw [h.mpos]
    cases d <;> simp [Tape.move, Dir3.toSign] at hd ⊢
    omega

/-- The zone flag is consistent with the input head position `h` on an input
of length `N`. -/
def ZoneOK (N h : ℕ) : InputZone → Prop
  | .left => h = 0
  | .inner => 1 ≤ h
  | .probe => h ≤ N

/-- The resolved zone says exactly whether the head is on `▷`. -/
theorem atLeft_eq {N h pos : ℕ} {z : InputZone} {sym : Option Bool}
    (hz : ZoneOK N h z) (hpos : pos = min h (N + 1))
    (hsym : sym = none ↔ pos = 0 ∨ pos = N + 1) :
    z.atLeft sym = decide (h = 0) := by
  cases z <;> simp only [ZoneOK, InputZone.atLeft] at hz ⊢
  · simp [hz]
  · simp; omega
  · rw [Bool.eq_iff_iff, Option.isNone_iff_eq_none, hsym, decide_eq_true_iff]; omega

/-- The input bookkeeping of `inputAction` tracks one input-head move. Here
`pos` is CSLib's clamped input head, `o` the overshoot counter, `sym` the input
symbol, and `ov` the counter tape's symbol. -/
theorem inputAction_spec {N : ℕ} {t : Tape} {z : InputZone} {pos : Fin (N + 2)}
    {sym ov : Option Bool} {o : ℤ} (d : Dir3) (hz : ZoneOK N t.head z)
    (hpos : (pos : ℕ) = min t.head (N + 1))
    (hsym : sym = none ↔ (pos : ℕ) = 0 ∨ (pos : ℕ) = N + 1)
    (ho : o = ((t.head - (N + 1) : ℕ) : ℤ))
    (hov : ov = some true ↔ t.head ≤ N + 1) :
    ZoneOK N (t.move d).head (inputAction (z.atLeft sym) sym ov d).2.2 ∧
    (moveInputPos pos (inputAction (z.atLeft sym) sym ov d).1 : ℕ) =
      min (t.move d).head (N + 1) ∧
    o + ((inputAction (z.atLeft sym) sym ov d).2.1 : ℤ) =
      (((t.move d).head - (N + 1) : ℕ) : ℤ) := by
  rw [atLeft_eq hz hpos hsym]
  clear hz
  have hlt := pos.isLt
  have hs : sym.isNone = decide ((pos : ℕ) = 0 ∨ (pos : ℕ) = N + 1) := by
    rw [Bool.eq_iff_iff, Option.isNone_iff_eq_none, hsym, decide_eq_true_iff]
  have hv : decide (ov ≠ some true) = decide (N + 1 < t.head) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, ne_eq, hov]; omega
  rw [moveInputPos_val]
  generalize (pos : ℕ) = p at *
  cases d <;> by_cases h0 : t.head = 0 <;>
    simp [inputAction, Tape.move, h0, hs, hv] <;>
    (try split_ifs) <;>
    (try simp only [ZoneOK, SignType.coe_zero, SignType.coe_one, SignType.coe_neg_one,
      true_and]) <;>
    omega

@[simp] theorem tapeLayout_dataIdx {α : Type*} (u v : Fin (n + 1) → α) (w : α)
    (i : Fin (n + 1)) : tapeLayout u v w (dataIdx i) = u i := by
  simp only [tapeLayout, dataIdx, Fin.append_left]

@[simp] theorem tapeLayout_markIdx {α : Type*} (u v : Fin (n + 1) → α) (w : α)
    (i : Fin (n + 1)) : tapeLayout u v w (markIdx i) = v i := by
  simp only [tapeLayout, markIdx, Fin.append_left, Fin.append_right]

@[simp] theorem tapeLayout_overIdx {α : Type*} (u v : Fin (n + 1) → α) (w : α) :
    tapeLayout u v w (overIdx (n := n)) = w := by
  simp only [tapeLayout, overIdx, Fin.append_right]
  rfl

/-- Our read-write tapes in the simulator's order: work tapes, then the
output tape. -/
def simTape {Q : Type} (c : Cfg n Q) : Fin (n + 1) → Tape :=
  Fin.lastCases c.output c.work

@[simp] theorem simTape_castSucc {Q : Type} (c : Cfg n Q) (j : Fin n) :
    simTape c j.castSucc = c.work j := by
  simp [simTape]

@[simp] theorem simTape_last {Q : Type} (c : Cfg n Q) : simTape c (Fin.last n) = c.output := by
  simp [simTape]

variable (tm : TM n)

/-- The simulator's configurations on input `x`. -/
abbrev SimCfg (x : List Bool) := Turing.Cfg (simTapes n) Bool (MultiTapeState tm.Q) x

/-- The simulator configuration `d`, with zone flag `z`, simulates our
configuration `c` on input `x`. -/
structure MultiTapeSim (x : List Bool) (c : Cfg n tm.Q) (z : InputZone) (d : tm.SimCfg x) :
    Prop where
  state : d.state = some (.run c.state z)
  zone : ZoneOK x.length c.input.head z
  inputCells : c.input.cells = (Tape.init (x.map Γ.ofBool)).cells
  inputPos : (d.inputPos : ℕ) = min c.input.head (x.length + 1)
  overPos : d.workTapePos overIdx = ((c.input.head - (x.length + 1) : ℕ) : ℤ)
  overCells : d.workTapes overIdx = markTape
  tapes : ∀ i, TapeSim (simTape c i) (d.workTapePos (dataIdx i)) (d.workTapePos (markIdx i))
    (d.workTapes (dataIdx i)) (d.workTapes (markIdx i))
  output : d.output = []

variable {tm}

theorem MultiTapeSim.inputSymbol_eq_none_iff {x : List Bool} {c : Cfg n tm.Q}
    {z : InputZone} {d : tm.SimCfg x} (_h : MultiTapeSim tm x c z d) :
    d.inputSymbol = none ↔ (d.inputPos : ℕ) = 0 ∨ (d.inputPos : ℕ) = x.length + 1 :=
  MultiTape.inputSymbol_eq_none_iff d

/-- The simulator reads our input symbol. -/
theorem MultiTapeSim.readIn {x : List Bool} {c : Cfg n tm.Q} {z : InputZone}
    {d : tm.SimCfg x} (h : MultiTapeSim tm x c z d) :
    (if z.atLeft d.inputSymbol then Γ.start else Γ.ofCell d.inputSymbol) = c.input.read := by
  rw [atLeft_eq h.zone h.inputPos h.inputSymbol_eq_none_iff, Tape.read, h.inputCells]
  by_cases h0 : c.input.head = 0
  · simp [h0]
  · simp only [h0, decide_false, Bool.false_eq_true, ite_false]
    obtain ⟨p, hp⟩ : ∃ p, c.input.head = p + 1 := ⟨c.input.head - 1, by omega⟩
    rw [hp]
    by_cases hlt : p < x.length
    · rw [inputSymbol_of_lt d (p := p) (by rw [h.inputPos]; omega) hlt,
        Tape.init_ofBool_cells_lt x p hlt]
      rfl
    · rw [(h.inputSymbol_eq_none_iff).2 (by rw [h.inputPos]; omega),
        Tape.init_ofBool_cells_ge x p (by omega)]
      rfl

/-- The overshoot counter reads `1` exactly when the input head is at most one
cell past the input. -/
theorem MultiTapeSim.readOver {x : List Bool} {c : Cfg n tm.Q} {z : InputZone}
    {d : tm.SimCfg x} (h : MultiTapeSim tm x c z d) :
    d.workTapeSymbols overIdx = some true ↔ c.input.head ≤ x.length + 1 := by
  simp only [Cfg.workTapeSymbols, h.overCells, h.overPos, markTape]
  split_ifs with h0 <;> simp <;> omega

theorem MultiTapeSim.simRead {x : List Bool} {c : Cfg n tm.Q} {z : InputZone}
    {d : tm.SimCfg x} (h : MultiTapeSim tm x c z d) (i : Fin (n + 1)) :
    simRead d.workTapeSymbols i = (simTape c i).read :=
  (h.tapes i).read

theorem MultiTapeSim.atStart {x : List Bool} {c : Cfg n tm.Q} {z : InputZone}
    {d : tm.SimCfg x} (h : MultiTapeSim tm x c z d) (i : Fin (n + 1)) :
    decide (d.workTapeSymbols (markIdx i) = some true) = decide ((simTape c i).head = 0) :=
  (h.tapes i).atStart

/-- One step of our machine is one step of the simulator. -/
theorem MultiTapeSim.step {x : List Bool} {c c' : Cfg n tm.Q} {z : InputZone}
    {d : tm.SimCfg x} (h : MultiTapeSim tm x c z d) (hstep : tm.step c = some c') :
    ∃ z', MultiTapeSim tm x c' z' (tm.toMultiTape.step d) := by
  have hq : c.state ≠ tm.qhalt := state_ne_qhalt_of_step hstep
  have hin := h.readIn
  have hr := h.simRead
  have hat := h.atStart
  rw [step_of_state_eq_some _ h.state]
  simp only [toMultiTape, toMultiTapeTr, hq, ite_false, hin, hr, hat, simTape_castSucc,
    simTape_last]
  simp only [TM.step, hq, ite_false, Option.some.injEq] at hstep
  subst hstep
  set o := tm.δ c.state c.input.read (fun i => (c.work i).read) c.output.read
  have hspec := inputAction_spec (t := c.input) (pos := d.inputPos) (sym := d.inputSymbol)
    (ov := d.workTapeSymbols overIdx) (o := d.workTapePos overIdx) o.2.2.2.1
    h.zone h.inputPos h.inputSymbol_eq_none_iff h.overPos h.readOver
  refine ⟨_, rfl, hspec.1, by simp [Tape.move_cells, h.inputCells], hspec.2.1, ?_, ?_, ?_, ?_⟩
  · simpa using hspec.2.2
  · simp [applyWrite, h.overCells]
  · intro i
    induction i using Fin.lastCases with
    | last => simpa [simTape] using (h.tapes (Fin.last n)).writeAndMove o.2.2.1 o.2.2.2.2.2
    | cast j =>
      simpa [simTape] using (h.tapes j.castSucc).writeAndMove (o.2.1 j) (o.2.2.2.2.1 j)
  · simp [h.output]

/-- A freshly marked marker tape. -/
theorem applyWrite_markTape :
    applyWrite (fun _ => none) 0 (some (some true)) = markTape := by
  funext p
  simp [applyWrite, markTape, Function.update_apply]

variable (tm) in
/-- After its marking step, the simulator simulates our initial configuration. -/
theorem multiTapeSim_init (x : List Bool) :
    MultiTapeSim tm x (tm.initCfg x) .left (tm.toMultiTape.step (tm.toMultiTape.initCfg x)) := by
  rw [step_of_state_eq_some _ (q := .init) rfl]
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, fun i => ?_, rfl⟩
  · simp [toMultiTape, toMultiTapeTr, moveInputPos_val]
  · simp [toMultiTape, toMultiTapeTr]
  · simpa [toMultiTape, toMultiTapeTr] using applyWrite_markTape
  · induction i using Fin.lastCases <;>
      refine ⟨by simp [toMultiTape, toMultiTapeTr], by simp [toMultiTape, toMultiTapeTr],
        fun p hp => ?_, by simpa [toMultiTape, toMultiTapeTr] using applyWrite_markTape,
        by simpa using Tape.StartInvariant.init_nil⟩ <;>
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩ <;>
      simp [toMultiTape, toMultiTapeTr, Γ.ofCell]

/-- A run of our machine is a run of the simulator of the same length. -/
theorem MultiTapeSim.reachesIn {x : List Bool} {t : ℕ} {c c' : Cfg n tm.Q}
    (hreach : tm.reachesIn t c c') {z : InputZone} {d : tm.SimCfg x}
    (h : MultiTapeSim tm x c z d) :
    ∃ z', MultiTapeSim tm x c' z' (tm.toMultiTape.runFrom d t) := by
  induction hreach generalizing z d with
  | zero => exact ⟨z, by simpa [MultiTapeTM.runFrom] using h⟩
  | step hstep _ ih =>
    obtain ⟨z'', h''⟩ := h.step hstep
    obtain ⟨z', h'⟩ := ih h''
    exact ⟨z', by
      rw [MultiTapeTM.runFrom, Function.iterate_succ_apply]
      exact h'⟩

variable (tm) in
/-- The simulator is rewinding its copy `t` of our output tape. -/
structure Rewinding (x : List Bool) (t : Tape) (d : tm.SimCfg x) : Prop where
  state : d.state = some .rewind
  out : TapeSim t (d.workTapePos (dataIdx (Fin.last n))) (d.workTapePos (markIdx (Fin.last n)))
    (d.workTapes (dataIdx (Fin.last n))) (d.workTapes (markIdx (Fin.last n)))
  output : d.output = []

variable (tm) in
/-- The simulator is about to read the verdict in cell 1 of its copy `t` of our
output tape. -/
structure AtVerdict (x : List Bool) (t : Tape) (d : tm.SimCfg x) : Prop where
  state : d.state = some .verdict
  out : TapeSim t (d.workTapePos (dataIdx (Fin.last n))) (d.workTapePos (markIdx (Fin.last n)))
    (d.workTapes (dataIdx (Fin.last n))) (d.workTapes (markIdx (Fin.last n)))
  head : t.head = 1
  output : d.output = []

/-- Once our machine halts, the simulator starts rewinding. -/
theorem MultiTapeSim.halt {x : List Bool} {c : Cfg n tm.Q} {z : InputZone}
    {d : tm.SimCfg x} (h : MultiTapeSim tm x c z d) (hc : c.state = tm.qhalt) :
    Rewinding tm x c.output (tm.toMultiTape.step d) := by
  rw [step_of_state_eq_some _ h.state]
  refine ⟨?_, ?_, ?_⟩
  · simp [toMultiTape, toMultiTapeTr, hc]
  · simpa [toMultiTape, toMultiTapeTr, hc, applyWrite] using h.tapes (Fin.last n)
  · simp [toMultiTape, toMultiTapeTr, hc, h.output]

theorem Rewinding.step_of_ne_zero {x : List Bool} {t : Tape} {d : tm.SimCfg x}
    (h : Rewinding tm x t d) (h0 : t.head ≠ 0) :
    Rewinding tm x (t.move .left) (tm.toMultiTape.step d) := by
  have hat : d.workTapeSymbols (markIdx (Fin.last n)) ≠ some true := fun h' =>
    h0 ((decide_eq_decide.mp h.out.atStart).1 h')
  rw [step_of_state_eq_some _ h.state]
  refine ⟨?_, ?_, ?_⟩
  · simp [toMultiTape, toMultiTapeTr, hat]
  · simpa [toMultiTape, toMultiTapeTr, hat, applyWrite, Dir3.toSign] using
      h.out.move .left (fun _ => h0)
  · simp [toMultiTape, toMultiTapeTr, h.output]

theorem Rewinding.step_of_eq_zero {x : List Bool} {t : Tape} {d : tm.SimCfg x}
    (h : Rewinding tm x t d) (h0 : t.head = 0) :
    AtVerdict tm x (t.move .right) (tm.toMultiTape.step d) := by
  have hat : d.workTapeSymbols (markIdx (Fin.last n)) = some true :=
    (decide_eq_decide.mp h.out.atStart).2 h0
  rw [step_of_state_eq_some _ h.state]
  refine ⟨?_, ?_, by simp [Tape.move, h0], ?_⟩
  · simp [toMultiTape, toMultiTapeTr, hat]
  · simpa [toMultiTape, toMultiTapeTr, hat, applyWrite, Dir3.toSign] using
      h.out.move .right (by simp)
  · simp [toMultiTape, toMultiTapeTr, h.output]

theorem AtVerdict.step {x : List Bool} {t : Tape} {d : tm.SimCfg x}
    (h : AtVerdict tm x t d) :
    (tm.toMultiTape.step d).state = none ∧
      (tm.toMultiTape.step d).output = [decide (t.cells 1 = Γ.one)] := by
  have hr : simRead d.workTapeSymbols (Fin.last n) = t.cells 1 :=
    h.out.read.trans (by rw [Tape.read, h.head])
  rw [step_of_state_eq_some _ h.state]
  refine ⟨rfl, ?_⟩
  simp only [toMultiTape, toMultiTapeTr, hr, h.output, List.nil_append]
  rfl

/-- The rewind phase from output-head position `m` halts after `m + 2` more
steps, emitting the verdict in output cell 1. -/
theorem Rewinding.run {x : List Bool} :
    ∀ (m : ℕ) {t : Tape} {d : tm.SimCfg x}, Rewinding tm x t d → t.head = m →
      (tm.toMultiTape.runFrom d (m + 2)).state = none ∧
      (tm.toMultiTape.runFrom d (m + 2)).output = [decide (t.cells 1 = Γ.one)]
  | 0, t, d, h, hm => by
    simp only [MultiTapeTM.runFrom, Function.iterate_succ_apply, Function.iterate_zero,
      id_eq]
    simpa [Tape.move_cells] using (h.step_of_eq_zero hm).step
  | m + 1, t, d, h, hm => by
    rw [show m + 1 + 2 = m + 2 + 1 by omega, MultiTapeTM.runFrom,
      Function.iterate_succ_apply, ← MultiTapeTM.runFrom]
    simpa [Tape.move_cells] using
      Rewinding.run m (h.step_of_ne_zero (by omega)) (by simp [Tape.move, hm])

/-- A decider takes at least one step on every input length: the verdict cell
starts blank. -/
theorem DecidesInTime.one_le {L : Language} {f : ℕ → ℕ} (h : tm.DecidesInTime L f)
    (m : ℕ) : 1 ≤ f m := by
  obtain ⟨c', t, ht, hreach, -, hyes, hno⟩ := h (List.replicate m false)
  rw [List.length_replicate] at ht
  rcases t with _ | t
  · rw [reachesIn_zero_iff] at hreach
    subst hreach
    by_cases hx : List.replicate m false ∈ L
    · exact absurd (hyes hx) (by simp [Tape.init])
    · exact absurd (hno hx) (by simp [Tape.init])
  · omega

/-- CSLib's encoding of a Boolean verdict as a one-bit output. -/
@[expose] def verdictEmb : Bool ↪ List Bool :=
  ⟨fun b => [b], by intro a b h; simpa using h⟩

variable (tm) in
/-- **The simulator decides what `tm` decides**, within time `2 f + 4` and
space `(2n + 3) (2 f + 5)` when `tm` decides within time `f`. -/
theorem toMultiTape_computesFun {L : Language} {f : ℕ → ℕ} (hdec : tm.DecidesInTime L f) :
    tm.toMultiTape.ComputesFunInTimeAndSpace (Function.Embedding.refl _) verdictEmb
      (MultiTapeTM.indicator L) (fun x => 2 * f x.length + 4)
      (fun x => simTapes n * (2 * f x.length + 5)) := by
  intro x
  obtain ⟨c', t, ht, hreach, hhalt, hyes, hno⟩ := hdec x
  have hp : c'.output.head ≤ t := (head_le_of_reachesIn tm hreach).2.1
  obtain ⟨z, hsim⟩ := (multiTapeSim_init tm x).reachesIn hreach
  have hrun := (hsim.halt hhalt).run c'.output.head rfl
  have hsplit : tm.toMultiTape.runFrom (tm.toMultiTape.initCfg x)
      (1 + t + 1 + (c'.output.head + 2)) =
      tm.toMultiTape.runFrom (tm.toMultiTape.step (tm.toMultiTape.runFrom
        (tm.toMultiTape.step (tm.toMultiTape.initCfg x)) t)) (c'.output.head + 2) := by
    simp only [MultiTapeTM.runFrom]
    have e : ∀ y : tm.SimCfg x, tm.toMultiTape.step y = tm.toMultiTape.step^[1] y :=
      fun _ => rfl
    rw [e (tm.toMultiTape.initCfg x), e (tm.toMultiTape.step^[t] _),
      ← Function.iterate_add_apply, ← Function.iterate_add_apply,
      ← Function.iterate_add_apply]
    congr 1
    omega
  refine ⟨1 + t + 1 + (c'.output.head + 2), by dsimp only; omega,
    tm.toMultiTape.spaceUsed (tm.toMultiTape.initCfg x) (1 + t + 1 + (c'.output.head + 2)),
    (MultiTape.spaceUsed_le _ _ _).trans (Nat.mul_le_mul_left (simTapes n)
      (show 1 + t + 1 + (c'.output.head + 2) + 1 ≤ 2 * f x.length + 5 by omega)), ?_⟩
  change tm.toMultiTape.ComputesInTimeAndSpace x (verdictEmb (MultiTapeTM.indicator L x)) _ _
  refine ⟨by rw [hsplit]; exact hrun.1, ?_, rfl⟩
  rw [hsplit, hrun.2]
  simp only [verdictEmb, MultiTapeTM.indicator]
  by_cases hx : x ∈ L
  · simp [hyes hx, hx]
  · simp [hno hx, hx]

end TM

end Complexity
