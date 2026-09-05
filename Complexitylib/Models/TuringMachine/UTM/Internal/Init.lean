/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Internal.Desc
public import Complexitylib.Models.TuringMachine.UTM.Internal.VTape
public import Complexitylib.Models.TuringMachine.Hoare.Defs
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import Complexitylib.Encoding.Pairing
public import Mathlib.Algebra.Order.Sub.Basic

/-!
# UTM initialization machine

`initTM : TM 6` is the first phase of the universal Turing machine
(`docs/UTM-design.md`). On input `pair α x` it:

1. **parses the α-region** of the input (α's bits doubled, terminated by the
   separator `01`), translating each 2-bit group into one desc symbol
   (`symOfPair`) written onto the desc tape (work tape 4);
2. **copies `x`** onto the virtual input tape (work tape 0) shifted one cell
   right (the +1-shift representation: work-0 cell 1 stays `□`, `x[i]` goes
   to cell `i + 2`);
3. **copies the first desc field** (the `qstart` field, i.e. the symbols
   before the first `□`) onto the state tape (work tape 3);
4. **parks** all work-tape heads at cell 1 and halts, leaving the output
   tape untouched.

The specification is `initTM_hoareTime`. Malformed inputs (a `10` cell pair
or a blank in the middle of a 2-cell group in the α-region) make the machine
halt immediately; the specification only covers well-formed inputs.
-/


@[expose] public section

namespace Complexity

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- State type
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `initTM`.

* `start` — the forced first step (every head bounces off `▷` to cell 1);
* `readFst pending` — phase 1, at the first cell of a 2-cell input group;
  `pending` holds an α-bit waiting for its partner (desc symbols are built
  from *two* α-bits);
* `readSnd fst pending` — phase 1, at the second cell of a 2-cell group whose
  first cell held the bit `fst`;
* `copyX` — phase 2, copying `x` to work tape 0 (shifted);
* `rewindDesc` — phase 3, rewinding the desc tape (work 4) to cell 1;
* `copyField` — phase 3, copying the `qstart` field of the desc tape onto
  the state tape (work 3);
* `rewindDesc2`, `rewindState`, `rewindV0` — final rewinds of work tapes
  4, 3, 0;
* `done` — halt. -/
inductive InitQ where
  | start
  | readFst (pending : Option Bool)
  | readSnd (fst : Bool) (pending : Option Bool)
  | copyX
  | rewindDesc
  | copyField
  | rewindDesc2
  | rewindState
  | rewindV0
  | done
  deriving DecidableEq

instance : Fintype InitQ where
  elems := {.start, .readFst none, .readFst (some false), .readFst (some true),
    .readSnd false none, .readSnd false (some false), .readSnd false (some true),
    .readSnd true none, .readSnd true (some false), .readSnd true (some true),
    .copyX, .rewindDesc, .copyField, .rewindDesc2, .rewindState, .rewindV0, .done}
  complete := fun q => by
    match q with
    | .start | .copyX | .rewindDesc | .copyField | .rewindDesc2
    | .rewindState | .rewindV0 | .done => simp
    | .readFst none | .readFst (some false) | .readFst (some true) => simp
    | .readSnd false none | .readSnd false (some false) | .readSnd false (some true)
    | .readSnd true none | .readSnd true (some false) | .readSnd true (some true) => simp

-- ════════════════════════════════════════════════════════════════════════
-- The machine
-- ════════════════════════════════════════════════════════════════════════

/-- One step of a work-tape rewind: move the head of work tape `idx` left
    until it reads `▷`, then bounce right to cell 1 and enter `qnext`.
    All other tapes idle. -/
def rewindStep (idx : Fin 6) (qloop qnext : InitQ)
    (iHead : Γ) (wHeads : Fin 6 → Γ) (oHead : Γ) :
    InitQ × (Fin 6 → Γw) × Γw × Dir3 × (Fin 6 → Dir3) × Dir3 :=
  if wHeads idx = Γ.start then
    (qnext, fun i => readBackWrite (wHeads i), readBackWrite oHead,
     idleDir iHead, fun i => if i = idx then Dir3.right else idleDir (wHeads i),
     idleDir oHead)
  else
    (qloop, fun i => readBackWrite (wHeads i), readBackWrite oHead,
     idleDir iHead, fun i => if i = idx then Dir3.left else idleDir (wHeads i),
     idleDir oHead)

/-- The UTM initialization machine. See the module docstring and
    `docs/UTM-design.md` for the phase structure. -/
def initTM : TM 6 where
  Q := InitQ
  qstart := .start
  qhalt := .done
  δ := fun q iHead wHeads oHead =>
    match q with
    | .start =>
        (.readFst none, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .readFst pending =>
        match iHead with
        | .zero =>
            (.readSnd false pending, fun i => readBackWrite (wHeads i),
             readBackWrite oHead, Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | .one =>
            (.readSnd true pending, fun i => readBackWrite (wHeads i),
             readBackWrite oHead, Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | .blank =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             Dir3.stay, fun i => idleDir (wHeads i), idleDir oHead)
        | .start =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
    | .readSnd fst pending =>
        match iHead, fst with
        | .zero, false =>
            -- α-bit `false`
            match pending with
            | none =>
                (.readFst (some false), fun i => readBackWrite (wHeads i),
                 readBackWrite oHead, Dir3.right,
                 fun i => idleDir (wHeads i), idleDir oHead)
            | some b₁ =>
                (.readFst none,
                 fun i => if i = 4 then symOfPair b₁ false else readBackWrite (wHeads i),
                 readBackWrite oHead, Dir3.right,
                 fun i => if i = 4 then Dir3.right else idleDir (wHeads i), idleDir oHead)
        | .one, true =>
            -- α-bit `true`
            match pending with
            | none =>
                (.readFst (some true), fun i => readBackWrite (wHeads i),
                 readBackWrite oHead, Dir3.right,
                 fun i => idleDir (wHeads i), idleDir oHead)
            | some b₁ =>
                (.readFst none,
                 fun i => if i = 4 then symOfPair b₁ true else readBackWrite (wHeads i),
                 readBackWrite oHead, Dir3.right,
                 fun i => if i = 4 then Dir3.right else idleDir (wHeads i), idleDir oHead)
        | .one, false =>
            -- separator `01`: enter phase 2, advancing work 0 from cell 1 to 2
            (.copyX, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             Dir3.right, fun i => if i = 0 then Dir3.right else idleDir (wHeads i),
             idleDir oHead)
        | .zero, true =>
            -- `10`: malformed
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             Dir3.stay, fun i => idleDir (wHeads i), idleDir oHead)
        | .blank, _ =>
            -- blank mid-group: malformed
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             Dir3.stay, fun i => idleDir (wHeads i), idleDir oHead)
        | .start, _ =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
    | .copyX =>
        match iHead with
        | .zero =>
            (.copyX, fun i => if i = 0 then Γw.zero else readBackWrite (wHeads i),
             readBackWrite oHead, Dir3.right,
             fun i => if i = 0 then Dir3.right else idleDir (wHeads i), idleDir oHead)
        | .one =>
            (.copyX, fun i => if i = 0 then Γw.one else readBackWrite (wHeads i),
             readBackWrite oHead, Dir3.right,
             fun i => if i = 0 then Dir3.right else idleDir (wHeads i), idleDir oHead)
        | .blank =>
            (.rewindDesc, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             Dir3.stay, fun i => idleDir (wHeads i), idleDir oHead)
        | .start =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
    | .rewindDesc => rewindStep 4 .rewindDesc .copyField iHead wHeads oHead
    | .copyField =>
        match wHeads 4 with
        | .zero =>
            (.copyField, fun i => if i = 3 then Γw.zero else readBackWrite (wHeads i),
             readBackWrite oHead, idleDir iHead,
             fun i => if i = 3 then Dir3.right else if i = 4 then Dir3.right
                      else idleDir (wHeads i),
             idleDir oHead)
        | .one =>
            (.copyField, fun i => if i = 3 then Γw.one else readBackWrite (wHeads i),
             readBackWrite oHead, idleDir iHead,
             fun i => if i = 3 then Dir3.right else if i = 4 then Dir3.right
                      else idleDir (wHeads i),
             idleDir oHead)
        | .blank =>
            (.rewindDesc2, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
        | .start =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .rewindDesc2 => rewindStep 4 .rewindDesc2 .rewindState iHead wHeads oHead
    | .rewindState => rewindStep 3 .rewindState .rewindV0 iHead wHeads oHead
    | .rewindV0 => rewindStep 0 .rewindV0 .done iHead wHeads oHead
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro q iHead wHeads oHead
    have hrw : ∀ (idx : Fin 6) (qloop qnext : InitQ),
        let (_, _, _, inDir, workDirs, outDir) :=
          rewindStep idx qloop qnext iHead wHeads oHead
        (iHead = Γ.start → inDir = Dir3.right) ∧
        (∀ i, wHeads i = Γ.start → workDirs i = Dir3.right) ∧
        (oHead = Γ.start → outDir = Dir3.right) := by
      intro idx qloop qnext
      by_cases hs : wHeads idx = Γ.start
      · simp only [rewindStep, hs, ↓reduceIte]
        refine ⟨idleDir_right_of_start, fun i hwi => ?_, idleDir_right_of_start⟩
        split
        · rfl
        · exact idleDir_right_of_start hwi
      · simp only [rewindStep, hs, ↓reduceIte]
        refine ⟨idleDir_right_of_start, fun i hwi => ?_, idleDir_right_of_start⟩
        split
        · next heq => subst heq; exact absurd hwi hs
        · exact idleDir_right_of_start hwi
    match q with
    | .start =>
        exact ⟨idleDir_right_of_start, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
    | .readFst p =>
        cases iHead with
        | zero => exact ⟨fun _ => rfl, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
        | one => exact ⟨fun _ => rfl, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
        | blank => exact ⟨nofun, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
        | start => exact ⟨fun _ => rfl, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
    | .readSnd f p =>
        match iHead, f with
        | .zero, false =>
            match p with
            | none =>
                exact ⟨fun _ => rfl, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
            | some b₁ =>
                refine ⟨fun _ => rfl, fun i hwi => ?_, idleDir_right_of_start⟩
                dsimp only; split
                · rfl
                · exact idleDir_right_of_start hwi
        | .one, true =>
            match p with
            | none =>
                exact ⟨fun _ => rfl, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
            | some b₁ =>
                refine ⟨fun _ => rfl, fun i hwi => ?_, idleDir_right_of_start⟩
                dsimp only; split
                · rfl
                · exact idleDir_right_of_start hwi
        | .one, false =>
            refine ⟨fun _ => rfl, fun i hwi => ?_, idleDir_right_of_start⟩
            dsimp only; split
            · rfl
            · exact idleDir_right_of_start hwi
        | .zero, true =>
            exact ⟨nofun, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
        | .blank, _ =>
            exact ⟨nofun, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
        | .start, _ =>
            exact ⟨fun _ => rfl, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
    | .copyX =>
        cases iHead with
        | zero =>
            refine ⟨fun _ => rfl, fun i hwi => ?_, idleDir_right_of_start⟩
            dsimp only; split
            · rfl
            · exact idleDir_right_of_start hwi
        | one =>
            refine ⟨fun _ => rfl, fun i hwi => ?_, idleDir_right_of_start⟩
            dsimp only; split
            · rfl
            · exact idleDir_right_of_start hwi
        | blank => exact ⟨nofun, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
        | start => exact ⟨fun _ => rfl, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
    | .copyField =>
        cases hw4 : wHeads 4 with
        | zero =>
            refine ⟨idleDir_right_of_start, fun i hwi => ?_, idleDir_right_of_start⟩
            dsimp only; split
            · rfl
            · split
              · rfl
              · exact idleDir_right_of_start hwi
        | one =>
            refine ⟨idleDir_right_of_start, fun i hwi => ?_, idleDir_right_of_start⟩
            dsimp only; split
            · rfl
            · split
              · rfl
              · exact idleDir_right_of_start hwi
        | blank =>
            exact ⟨idleDir_right_of_start, fun i => idleDir_right_of_start,
                   idleDir_right_of_start⟩
        | start =>
            exact ⟨idleDir_right_of_start, fun i => idleDir_right_of_start,
                   idleDir_right_of_start⟩
    | .rewindDesc => exact hrw 4 .rewindDesc .copyField
    | .rewindDesc2 => exact hrw 4 .rewindDesc2 .rewindState
    | .rewindState => exact hrw 3 .rewindState .rewindV0
    | .rewindV0 => exact hrw 0 .rewindV0 .done
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- Tape helpers
-- ════════════════════════════════════════════════════════════════════════

/-- An idle tape (readback write, idle direction) is unchanged, provided it
    is not reading `▷` and its head is off cell 0. -/
private theorem tape_idle_preserve (t : Tape) (hns : t.read ≠ Γ.start)
    (hh : 1 ≤ t.head) :
    t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read) = t := by
  simp only [Tape.writeAndMove, idleDir, hns, ↓reduceIte, Tape.move, Tape.write]
  split
  · omega
  · simp only [Tape.read] at hns ⊢
    rw [toΓ_readBackWrite_of_ne_start hns, Function.update_eq_self]

/-- `HoldsExact` depends only on the cells. -/
private theorem holdsExact_of_cells_eq {t t' : Tape} {l : List Γw}
    (h : t.HoldsExact l) (he : t'.cells = t.cells) : t'.HoldsExact l :=
  ⟨by rw [he]; exact h.1, fun i => by rw [he]; exact h.2 i⟩

/-- Writing a symbol at the frontier of a `HoldsExact` tape and moving right
    appends the symbol and keeps the head at the (new) frontier. -/
private theorem holdsExact_push {t : Tape} {l : List Γw} (h : t.HoldsExact l)
    (hh : t.head = l.length + 1) (s : Γw) :
    ((t.write s.toΓ).move .right).HoldsExact (l ++ [s]) ∧
    ((t.write s.toΓ).move .right).head = (l ++ [s]).length + 1 := by
  have hw : t.write s.toΓ = { t with cells := Function.update t.cells t.head s.toΓ } := by
    rw [Tape.write, ite_eq_right (by omega)]
  refine ⟨⟨?_, fun i => ?_⟩, ?_⟩
  · show (Tape.move _ .right).cells 0 = Γ.start
    rw [Tape.move_cells, hw]
    dsimp only
    rw [Function.update_of_ne (by omega)]
    exact h.1
  · show (Tape.move _ .right).cells (i + 1) = _
    rw [Tape.move_cells, hw]
    dsimp only
    by_cases hi : i = l.length
    · subst hi
      rw [show l.length + 1 = t.head from hh.symm, Function.update_self]
      rw [dite_eq_left (by simp)]
      simp
    · rw [Function.update_of_ne (by omega)]
      rw [h.2 i]
      by_cases hlt : i < l.length
      · rw [dite_eq_left hlt, dite_eq_left (by simp; omega)]
        rw [List.getElem_append_left hlt]
      · rw [dite_eq_right hlt, dite_eq_right (by simp; omega)]
  · simp [Tape.move, Tape.write_head, hh]

private theorem bitSym_toΓ (b : Bool) : (bitSym b).toΓ = Γ.ofBool b := by
  cases b <;> rfl

/-- The first field of a symbol string is no longer than the string. -/
private theorem takeField_fst_length : ∀ l : List Γw, (takeField l).1.length ≤ l.length
  | [] => le_refl _
  | .blank :: rest => by simp [takeField]
  | .zero :: rest => by
      simpa [takeField] using takeField_fst_length rest
  | .one :: rest => by
      simpa [takeField] using takeField_fst_length rest

/-- Doubling every bit doubles the length. -/
private theorem dbl_length : ∀ l : List Bool, (l.flatMap fun b => [b, b]).length = 2 * l.length
  | [] => rfl
  | b :: rest => by
      simp only [List.flatMap_cons, List.length_append, dbl_length rest, List.length_cons,
        List.length_nil]
      omega

-- ════════════════════════════════════════════════════════════════════════
-- Input-suffix tracking
-- ════════════════════════════════════════════════════════════════════════

/-- The input tape holds the bits `l` (as `Γ.ofBool` symbols) from cell `k`
    on, followed by blanks. -/
private def InpSfx (t : Tape) (k : ℕ) (l : List Bool) : Prop :=
  ∀ j : ℕ, t.cells (k + j) = ((l[j]?).map Γ.ofBool).getD Γ.blank

private theorem inpSfx_head {t : Tape} {k : ℕ} {b : Bool} {l : List Bool}
    (h : InpSfx t k (b :: l)) : t.cells k = Γ.ofBool b := by
  have := h 0; simpa using this

private theorem inpSfx_tail {t : Tape} {k : ℕ} {b : Bool} {l : List Bool}
    (h : InpSfx t k (b :: l)) : InpSfx t (k + 1) l := by
  intro j
  have := h (j + 1)
  rw [show k + (j + 1) = k + 1 + j by omega] at this
  simpa using this

private theorem inpSfx_nil {t : Tape} {k : ℕ} (h : InpSfx t k []) :
    t.cells k = Γ.blank := by
  have := h 0; simpa using this

private theorem inpSfx_of_cells_eq {t t' : Tape} {k : ℕ} {l : List Bool}
    (h : InpSfx t k l) (he : t'.cells = t.cells) : InpSfx t' k l := by
  intro j; rw [he]; exact h j

private theorem inpSfx_congr {t : Tape} {k k' : ℕ} {l : List Bool}
    (h : InpSfx t k l) (hk : k' = k) : InpSfx t k' l := hk ▸ h

private theorem inpSfx_initTape (l : List Bool) :
    InpSfx (Tape.init (l.map Γ.ofBool)) 1 l := by
  intro j
  show (if 1 + j = 0 then Γ.start else ((l.map Γ.ofBool)[1 + j - 1]?).getD Γ.blank) = _
  rw [ite_eq_right (by omega), show 1 + j - 1 = j by omega, List.getElem?_map]

-- ════════════════════════════════════════════════════════════════════════
-- Single-step lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- The first step: every head bounces off `▷` from cell 0 to cell 1. -/
private theorem step_start {c : Cfg 6 initTM.Q}
    (hst : c.state = InitQ.start)
    (hih : c.input.head = 0) (hic : c.input.cells 0 = Γ.start)
    (hwh : ∀ i, (c.work i).head = 0) (hwc : ∀ i, (c.work i).cells 0 = Γ.start)
    (hoh : c.output.head = 0) (hoc : c.output.cells 0 = Γ.start) :
    ∃ c', initTM.step c = some c' ∧
      c'.state = InitQ.readFst none ∧
      c'.input.cells = c.input.cells ∧ c'.input.head = 1 ∧
      (∀ i, (c'.work i).cells = (c.work i).cells ∧ (c'.work i).head = 1) ∧
      c'.output.cells = c.output.cells ∧ c'.output.head = 1 := by
  have hir : c.input.read = Γ.start := by rw [Tape.read, hih]; exact hic
  have hwr : ∀ i, (c.work i).read = Γ.start := fun i => by
    rw [Tape.read, hwh i]; exact hwc i
  have hor : c.output.read = Γ.start := by rw [Tape.read, hoh]; exact hoc
  simp only [TM.step, hst, initTM, reduceCtorEq, ↓reduceIte]
  refine ⟨_, rfl, rfl, Tape.move_cells _ _, by simp [Tape.move, idleDir, hir, hih],
    ?_, ?_, ?_⟩
  · intro i
    refine ⟨tape_readBackWrite_preserves _ _ (Or.inl (hwh i)), ?_⟩
    simp [Tape.writeAndMove, Tape.move, idleDir, hwr i, Tape.write_head, hwh i]
  · exact tape_readBackWrite_preserves _ _ (Or.inl hoh)
  · simp [Tape.writeAndMove, Tape.move, idleDir, hor, Tape.write_head, hoh]

/-- The started entry step: in state `.start` with every head already parked
    at a cell ≥ 1 not reading `▷`, one step moves to `readFst none` leaving
    every tape untouched. Used when `initTM` runs mid-sequence, where the
    tapes arrive already bounced off `▷`. -/
private theorem step_start_started {c : Cfg 6 initTM.Q}
    (hst : c.state = InitQ.start)
    (hir : c.input.read ≠ Γ.start)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (ho : c.output.read ≠ Γ.start) (hoh : 1 ≤ c.output.head) :
    ∃ c', initTM.step c = some c' ∧
      c'.state = InitQ.readFst none ∧
      c'.input = c.input ∧ c'.work = c.work ∧ c'.output = c.output := by
  simp only [TM.step, hst, initTM, reduceCtorEq, ↓reduceIte]
  refine ⟨_, rfl, rfl, ?_, ?_, tape_idle_preserve _ ho hoh⟩
  · simp [Tape.move, idleDir, hir]
  · funext i
    exact tape_idle_preserve _ (hw i).1 (hw i).2

/-- Phase 1: the first cell of a 2-cell group holds the bit `b`. -/
private theorem step_readFst {c : Cfg 6 initTM.Q} {b : Bool} {p : Option Bool}
    (hst : c.state = InitQ.readFst p)
    (hread : c.input.read = Γ.ofBool b)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (ho : c.output.read ≠ Γ.start) (hoh : 1 ≤ c.output.head) :
    ∃ c', initTM.step c = some c' ∧
      c'.state = InitQ.readSnd b p ∧
      c'.input.cells = c.input.cells ∧
      c'.input.head = c.input.head + 1 ∧
      c'.work = c.work ∧
      c'.output = c.output := by
  cases b
  all_goals
    simp only [Γ.ofBool] at hread
    simp only [TM.step, hst, initTM, reduceCtorEq, ↓reduceIte, hread]
    refine ⟨_, rfl, rfl, Tape.move_cells _ _, by simp [Tape.move], ?_,
      tape_idle_preserve _ ho hoh⟩
    funext i
    exact tape_idle_preserve _ (hw i).1 (hw i).2

/-- Phase 1: second cell of a group confirming the bit `b`, no pending bit. -/
private theorem step_readSnd_nopend {c : Cfg 6 initTM.Q} {b : Bool}
    (hst : c.state = InitQ.readSnd b none)
    (hread : c.input.read = Γ.ofBool b)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (ho : c.output.read ≠ Γ.start) (hoh : 1 ≤ c.output.head) :
    ∃ c', initTM.step c = some c' ∧
      c'.state = InitQ.readFst (some b) ∧
      c'.input.cells = c.input.cells ∧
      c'.input.head = c.input.head + 1 ∧
      c'.work = c.work ∧
      c'.output = c.output := by
  cases b
  all_goals
    simp only [Γ.ofBool] at hread
    simp only [TM.step, hst, initTM, reduceCtorEq, ↓reduceIte, hread]
    refine ⟨_, rfl, rfl, Tape.move_cells _ _, by simp [Tape.move], ?_,
      tape_idle_preserve _ ho hoh⟩
    funext i
    exact tape_idle_preserve _ (hw i).1 (hw i).2

/-- Phase 1: second cell of a group confirming the bit `b`, with a pending
    bit `b₁` — emit `symOfPair b₁ b` onto the desc tape (work 4). -/
private theorem step_readSnd_emit {c : Cfg 6 initTM.Q} {b b₁ : Bool}
    (hst : c.state = InitQ.readSnd b (some b₁))
    (hread : c.input.read = Γ.ofBool b)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (ho : c.output.read ≠ Γ.start) (hoh : 1 ≤ c.output.head) :
    ∃ c', initTM.step c = some c' ∧
      c'.state = InitQ.readFst none ∧
      c'.input.cells = c.input.cells ∧
      c'.input.head = c.input.head + 1 ∧
      (∀ i, i ≠ (4 : Fin 6) → c'.work i = c.work i) ∧
      c'.work 4 = ((c.work 4).write (symOfPair b₁ b).toΓ).move .right ∧
      c'.output = c.output := by
  cases b
  all_goals
    simp only [Γ.ofBool] at hread
    simp only [TM.step, hst, initTM, reduceCtorEq, ↓reduceIte, hread]
    refine ⟨_, rfl, rfl, Tape.move_cells _ _, by simp [Tape.move], ?_, ?_,
      tape_idle_preserve _ ho hoh⟩
    · intro i hi
      simp only [hi, ↓reduceIte]
      exact tape_idle_preserve _ (hw i).1 (hw i).2
    · simp only [↓reduceIte]

/-- Phase 1 → 2: the separator `01` — enter `copyX`, advancing work tape 0
    (from cell 1 to cell 2). A pending α-bit (odd `|α|`) is dropped. -/
private theorem step_readSnd_sep {c : Cfg 6 initTM.Q} {p : Option Bool}
    (hst : c.state = InitQ.readSnd false p)
    (hread : c.input.read = Γ.one)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (ho : c.output.read ≠ Γ.start) (hoh : 1 ≤ c.output.head) :
    ∃ c', initTM.step c = some c' ∧
      c'.state = InitQ.copyX ∧
      c'.input.cells = c.input.cells ∧
      c'.input.head = c.input.head + 1 ∧
      (∀ i, i ≠ (0 : Fin 6) → c'.work i = c.work i) ∧
      (c'.work 0).cells = (c.work 0).cells ∧
      (c'.work 0).head = (c.work 0).head + 1 ∧
      c'.output = c.output := by
  simp only [TM.step, hst, initTM, reduceCtorEq, ↓reduceIte, hread]
  refine ⟨_, rfl, rfl, Tape.move_cells _ _, by simp [Tape.move], ?_, ?_, ?_,
    tape_idle_preserve _ ho hoh⟩
  · intro i hi
    simp only [hi, ↓reduceIte]
    exact tape_idle_preserve _ (hw i).1 (hw i).2
  · simp only [↓reduceIte]
    exact tape_readBackWrite_preserves _ _ (Or.inr (hw 0).1)
  · simp only [↓reduceIte, Tape.writeAndMove, Tape.move, Tape.write_head]

/-- Phase 2: copy one bit of `x` onto work tape 0. -/
private theorem step_copyX_bit {c : Cfg 6 initTM.Q} {b : Bool}
    (hst : c.state = InitQ.copyX)
    (hread : c.input.read = Γ.ofBool b)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (ho : c.output.read ≠ Γ.start) (hoh : 1 ≤ c.output.head) :
    ∃ c', initTM.step c = some c' ∧
      c'.state = InitQ.copyX ∧
      c'.input.cells = c.input.cells ∧
      c'.input.head = c.input.head + 1 ∧
      (∀ i, i ≠ (0 : Fin 6) → c'.work i = c.work i) ∧
      c'.work 0 = ((c.work 0).write (bitSym b).toΓ).move .right ∧
      c'.output = c.output := by
  cases b
  all_goals
    simp only [Γ.ofBool] at hread
    simp only [TM.step, hst, initTM, reduceCtorEq, ↓reduceIte, hread]
    refine ⟨_, rfl, rfl, Tape.move_cells _ _, by simp [Tape.move], ?_, ?_,
      tape_idle_preserve _ ho hoh⟩
    · intro i hi
      simp only [hi, ↓reduceIte]
      exact tape_idle_preserve _ (hw i).1 (hw i).2
    · simp only [↓reduceIte]
      rfl

/-- Phase 2 → 3: `x` is exhausted (input reads blank) — start rewinding the
    desc tape. -/
private theorem step_copyX_blank {c : Cfg 6 initTM.Q}
    (hst : c.state = InitQ.copyX)
    (hread : c.input.read = Γ.blank)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (ho : c.output.read ≠ Γ.start) (hoh : 1 ≤ c.output.head) :
    ∃ c', initTM.step c = some c' ∧
      c'.state = InitQ.rewindDesc ∧
      c'.input = c.input ∧ c'.work = c.work ∧ c'.output = c.output := by
  simp only [TM.step, hst, initTM, reduceCtorEq, ↓reduceIte, hread]
  refine ⟨_, rfl, rfl, rfl, ?_, tape_idle_preserve _ ho hoh⟩
  funext i
  exact tape_idle_preserve _ (hw i).1 (hw i).2

/-- Phase 3: copy one field symbol (`0` or `1`) from the desc tape onto the
    state tape (work 3); both heads advance. -/
private theorem step_copyField_bit {c : Cfg 6 initTM.Q} {s : Γw}
    (hs : s = Γw.zero ∨ s = Γw.one)
    (hst : c.state = InitQ.copyField)
    (hread : (c.work 4).read = s.toΓ)
    (hi : c.input.read ≠ Γ.start)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (ho : c.output.read ≠ Γ.start) (hoh : 1 ≤ c.output.head) :
    ∃ c', initTM.step c = some c' ∧
      c'.state = InitQ.copyField ∧
      c'.input = c.input ∧
      (∀ i, i ≠ (3 : Fin 6) → i ≠ 4 → c'.work i = c.work i) ∧
      c'.work 3 = ((c.work 3).write s.toΓ).move .right ∧
      (c'.work 4).cells = (c.work 4).cells ∧
      (c'.work 4).head = (c.work 4).head + 1 ∧
      c'.output = c.output := by
  rcases hs with rfl | rfl
  all_goals
    simp only [Γw.toΓ] at hread
    simp only [TM.step, hst, initTM, reduceCtorEq, ↓reduceIte, hread]
    refine ⟨_, rfl, rfl, by simp [Tape.move, idleDir, hi], ?_, ?_, ?_, ?_,
      tape_idle_preserve _ ho hoh⟩
    · intro i hi3 hi4
      simp only [hi3, hi4, ↓reduceIte]
      exact tape_idle_preserve _ (hw i).1 (hw i).2
    · simp only [↓reduceIte]
    · simp only [show (4 : Fin 6) ≠ 3 by decide, ↓reduceIte]
      exact tape_readBackWrite_preserves _ _ (Or.inr (hw 4).1)
    · simp only [show (4 : Fin 6) ≠ 3 by decide, ↓reduceIte, Tape.writeAndMove,
        Tape.move, Tape.write_head]

/-- Phase 3: the desc tape reads `□` — the field is over (the `□` is not
    copied); start the second desc rewind. -/
private theorem step_copyField_blank {c : Cfg 6 initTM.Q}
    (hst : c.state = InitQ.copyField)
    (hread : (c.work 4).read = Γ.blank)
    (hi : c.input.read ≠ Γ.start)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (ho : c.output.read ≠ Γ.start) (hoh : 1 ≤ c.output.head) :
    ∃ c', initTM.step c = some c' ∧
      c'.state = InitQ.rewindDesc2 ∧
      c'.input = c.input ∧ c'.work = c.work ∧ c'.output = c.output := by
  simp only [TM.step, hst, initTM, reduceCtorEq, ↓reduceIte, hread]
  refine ⟨_, rfl, rfl, by simp [Tape.move, idleDir, hi], ?_,
    tape_idle_preserve _ ho hoh⟩
  funext i
  exact tape_idle_preserve _ (hw i).1 (hw i).2

-- ════════════════════════════════════════════════════════════════════════
-- Rewind loop
-- ════════════════════════════════════════════════════════════════════════

/-- Generic rewind loop for the four rewind states: from a rewind state with
    the head of work tape `idx` at `h`, reach `qnext` with that head at cell
    1 in `h + 1` steps, preserving all tape contents. -/
private theorem rewind_loop {idx : Fin 6} {qloop qnext : InitQ}
    (hδ : ∀ iH wH oH, initTM.δ qloop iH wH oH = rewindStep idx qloop qnext iH wH oH)
    (hqne : qloop ≠ initTM.qhalt) :
    ∀ (h : ℕ) (c : Cfg 6 initTM.Q),
      c.state = qloop →
      (c.work idx).head = h →
      (c.work idx).cells 0 = Γ.start →
      (∀ j, 1 ≤ j → (c.work idx).cells j ≠ Γ.start) →
      c.input.read ≠ Γ.start →
      (∀ i, i ≠ idx → (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head) →
      c.output.read ≠ Γ.start → 1 ≤ c.output.head →
      ∃ c', initTM.reachesIn (h + 1) c c' ∧
        c'.state = qnext ∧
        (c'.work idx).head = 1 ∧
        (c'.work idx).cells = (c.work idx).cells ∧
        (∀ i, i ≠ idx → c'.work i = c.work i) ∧
        c'.input = c.input ∧
        c'.output = c.output := by
  intro h
  induction h with
  | zero =>
    intro c hst hh hc0 hns hi hwo ho hoh
    have hne' : ¬(c.state = initTM.qhalt) := by rw [hst]; exact hqne
    have hread : (c.work idx).read = Γ.start := by rw [Tape.read, hh]; exact hc0
    obtain ⟨c₁, hstep, hst₁, hhd₁, hcl₁, hfr₁, hin₁, hout₁⟩ :
        ∃ c₁, initTM.step c = some c₁ ∧ c₁.state = qnext ∧
          (c₁.work idx).head = 1 ∧ (c₁.work idx).cells = (c.work idx).cells ∧
          (∀ i, i ≠ idx → c₁.work i = c.work i) ∧
          c₁.input = c.input ∧ c₁.output = c.output := by
      simp only [TM.step, hst, hδ, rewindStep, hread, ↓reduceIte]
      rw [ite_eq_right hne']
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, by simp [Tape.move, idleDir, hi],
        tape_idle_preserve _ ho hoh⟩
      · simp only [↓reduceIte, Tape.writeAndMove, Tape.move, Tape.write_head, hh]
      · simp only [↓reduceIte]
        exact tape_readBackWrite_preserves _ _ (Or.inl hh)
      · intro i hi'
        simp only [hi', ↓reduceIte]
        exact tape_idle_preserve _ (hwo i hi').1 (hwo i hi').2
    exact ⟨c₁, .step hstep .zero, hst₁, hhd₁, hcl₁, hfr₁, hin₁, hout₁⟩
  | succ h ih =>
    intro c hst hh hc0 hns hi hwo ho hoh
    have hne' : ¬(c.state = initTM.qhalt) := by rw [hst]; exact hqne
    have hread : (c.work idx).read ≠ Γ.start := by
      rw [Tape.read, hh]; exact hns (h + 1) (by omega)
    obtain ⟨c₁, hstep, hst₁, hhd₁, hcl₁, hfr₁, hin₁, hout₁⟩ :
        ∃ c₁, initTM.step c = some c₁ ∧ c₁.state = qloop ∧
          (c₁.work idx).head = h ∧ (c₁.work idx).cells = (c.work idx).cells ∧
          (∀ i, i ≠ idx → c₁.work i = c.work i) ∧
          c₁.input = c.input ∧ c₁.output = c.output := by
      simp only [TM.step, hst, hδ, rewindStep, hread, ↓reduceIte]
      rw [ite_eq_right hne']
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, by simp [Tape.move, idleDir, hi],
        tape_idle_preserve _ ho hoh⟩
      · simp only [↓reduceIte, Tape.writeAndMove, Tape.move, Tape.write_head, hh]
        omega
      · simp only [↓reduceIte]
        exact tape_readBackWrite_preserves _ _ (Or.inr hread)
      · intro i hi'
        simp only [hi', ↓reduceIte]
        exact tape_idle_preserve _ (hwo i hi').1 (hwo i hi').2
    obtain ⟨c', hreach, hst', hhd', hcl', hfr', hin', hout'⟩ :=
      ih c₁ hst₁ hhd₁ (by rw [hcl₁]; exact hc0) (fun j hj => by rw [hcl₁]; exact hns j hj)
        (by rw [hin₁]; exact hi)
        (fun i hi' => by rw [hfr₁ i hi']; exact hwo i hi')
        (by rw [hout₁]; exact ho) (by rw [hout₁]; exact hoh)
    exact ⟨c', .step hstep hreach, hst', hhd', by rw [hcl', hcl₁],
      fun i hi' => by rw [hfr' i hi', hfr₁ i hi'], by rw [hin', hin₁],
      by rw [hout', hout₁]⟩

-- ════════════════════════════════════════════════════════════════════════
-- Phase 1 loop: parse the α-region
-- ════════════════════════════════════════════════════════════════════════

/-- All-tape side conditions from the desc-tape frontier shape. -/
private theorem hw_of_frontier {c : Cfg 6 initTM.Q} {acc : List Γw}
    (hh4 : (c.work 4).HoldsExact acc) (hd4 : (c.work 4).head = acc.length + 1)
    (hwo : ∀ i, i ≠ (4 : Fin 6) → (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head) :
    ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head := by
  intro i
  by_cases h4 : i = (4 : Fin 6)
  · subst h4
    constructor
    · rw [Tape.read, hd4, Tape.HoldsExact.cells_ge hh4 (le_refl acc.length)]
      simp
    · rw [hd4]; omega
  · exact hwo i h4

/-- **Phase-1 loop**: starting at the first cell of the remaining α-region in
    state `readFst none`, consume all of `αs` (two input cells per α-bit),
    emitting `groupPairs αs` onto the desc tape (work 4). Ends in a `readFst`
    state (with a pending bit iff `|αs|` is odd) at the separator. -/
private theorem phase1_loop (x : List Bool) :
    ∀ (αs : List Bool) (acc : List Γw) (k : ℕ) (c : Cfg 6 initTM.Q),
      c.state = InitQ.readFst none →
      1 ≤ k →
      c.input.head = k →
      InpSfx c.input k ((αs.flatMap fun b => [b, b]) ++ false :: true :: x) →
      (c.work 4).HoldsExact acc →
      (c.work 4).head = acc.length + 1 →
      (∀ i, i ≠ (4 : Fin 6) → (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head) →
      c.output.read ≠ Γ.start → 1 ≤ c.output.head →
      ∃ (c' : Cfg 6 initTM.Q) (p : Option Bool),
        initTM.reachesIn (2 * αs.length) c c' ∧
        c'.state = InitQ.readFst p ∧
        c'.input.head = k + 2 * αs.length ∧
        c'.input.cells = c.input.cells ∧
        InpSfx c'.input (k + 2 * αs.length) (false :: true :: x) ∧
        (c'.work 4).HoldsExact (acc ++ groupPairs αs) ∧
        (c'.work 4).head = (acc ++ groupPairs αs).length + 1 ∧
        (∀ i, i ≠ (4 : Fin 6) → c'.work i = c.work i) ∧
        c'.output = c.output
  | [] => by
    intro acc k c hst hk hih hsfx hh4 hd4 hwo ho hoh
    exact ⟨c, none, .zero, hst, by simpa using hih, rfl,
      by simpa using hsfx, by simpa [groupPairs] using hh4,
      by simpa [groupPairs] using hd4, fun i _ => rfl, rfl⟩
  | [b] => by
    intro acc k c hst hk hih hsfx hh4 hd4 hwo ho hoh
    simp only [List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
      List.append_nil] at hsfx
    have hwAll := hw_of_frontier hh4 hd4 hwo
    -- step 1: read the first copy of b
    have hread₁ : c.input.read = Γ.ofBool b := by
      rw [Tape.read, hih]; exact inpSfx_head hsfx
    obtain ⟨c₁, hs₁, hst₁, hcl₁, hih₁, hwk₁, hout₁⟩ :=
      step_readFst (p := none) hst hread₁ hwAll ho hoh
    have hih₁' : c₁.input.head = k + 1 := by rw [hih₁, hih]
    have hsfx₁ := inpSfx_of_cells_eq (inpSfx_tail hsfx) hcl₁
    -- step 2: read the second copy of b, record it as pending
    have hread₂ : c₁.input.read = Γ.ofBool b := by
      rw [Tape.read, hih₁']; exact inpSfx_head hsfx₁
    obtain ⟨c₂, hs₂, hst₂, hcl₂, hih₂, hwk₂, hout₂⟩ :=
      step_readSnd_nopend hst₁ hread₂ (by rw [hwk₁]; exact hwAll)
        (by rw [hout₁]; exact ho) (by rw [hout₁]; exact hoh)
    have hgpb : groupPairs [b] = [] := rfl
    have hwork4 : c₂.work 4 = c.work 4 := by rw [hwk₂, hwk₁]
    refine ⟨c₂, some b, .step hs₁ (.step hs₂ .zero), hst₂, ?_, by rw [hcl₂, hcl₁],
      ?_, ?_, ?_, fun i _ => by rw [hwk₂, hwk₁], by rw [hout₂, hout₁]⟩
    · rw [hih₂, hih₁']
      simp only [List.length_cons, List.length_nil]
    · exact inpSfx_congr (inpSfx_of_cells_eq (inpSfx_tail hsfx₁) hcl₂)
        (by simp only [List.length_cons, List.length_nil])
    · rw [hgpb, List.append_nil, hwork4]; exact hh4
    · rw [hgpb, List.append_nil, hwork4]; exact hd4
  | b₀ :: b₁ :: rest => by
    intro acc k c hst hk hih hsfx hh4 hd4 hwo ho hoh
    simp only [List.flatMap_cons, List.cons_append, List.nil_append] at hsfx
    have hwAll := hw_of_frontier hh4 hd4 hwo
    -- step 1: first copy of b₀
    have hread₁ : c.input.read = Γ.ofBool b₀ := by
      rw [Tape.read, hih]; exact inpSfx_head hsfx
    obtain ⟨c₁, hs₁, hst₁, hcl₁, hih₁, hwk₁, hout₁⟩ :=
      step_readFst (p := none) hst hread₁ hwAll ho hoh
    have hih₁' : c₁.input.head = k + 1 := by rw [hih₁, hih]
    have hsfx₁ := inpSfx_of_cells_eq (inpSfx_tail hsfx) hcl₁
    -- step 2: second copy of b₀, record as pending
    have hread₂ : c₁.input.read = Γ.ofBool b₀ := by
      rw [Tape.read, hih₁']; exact inpSfx_head hsfx₁
    obtain ⟨c₂, hs₂, hst₂, hcl₂, hih₂, hwk₂, hout₂⟩ :=
      step_readSnd_nopend hst₁ hread₂ (by rw [hwk₁]; exact hwAll)
        (by rw [hout₁]; exact ho) (by rw [hout₁]; exact hoh)
    have hih₂' : c₂.input.head = k + 2 := by rw [hih₂, hih₁']
    have hsfx₂ := inpSfx_congr (inpSfx_of_cells_eq (inpSfx_tail hsfx₁) hcl₂)
      (show k + 2 = k + 1 + 1 by omega)
    -- step 3: first copy of b₁
    have hread₃ : c₂.input.read = Γ.ofBool b₁ := by
      rw [Tape.read, hih₂']; exact inpSfx_head hsfx₂
    obtain ⟨c₃, hs₃, hst₃, hcl₃, hih₃, hwk₃, hout₃⟩ :=
      step_readFst (p := some b₀) hst₂ hread₃ (by rw [hwk₂, hwk₁]; exact hwAll)
        (by rw [hout₂, hout₁]; exact ho) (by rw [hout₂, hout₁]; exact hoh)
    have hih₃' : c₃.input.head = k + 3 := by rw [hih₃, hih₂']
    have hsfx₃ := inpSfx_congr (inpSfx_of_cells_eq (inpSfx_tail hsfx₂) hcl₃)
      (show k + 3 = k + 2 + 1 by omega)
    -- step 4: second copy of b₁ — emit symOfPair b₀ b₁ onto the desc tape
    have hread₄ : c₃.input.read = Γ.ofBool b₁ := by
      rw [Tape.read, hih₃']; exact inpSfx_head hsfx₃
    obtain ⟨c₄, hs₄, hst₄, hcl₄, hih₄, hfr₄, hw44, hout₄⟩ :=
      step_readSnd_emit hst₃ hread₄ (by rw [hwk₃, hwk₂, hwk₁]; exact hwAll)
        (by rw [hout₃, hout₂, hout₁]; exact ho)
        (by rw [hout₃, hout₂, hout₁]; exact hoh)
    have hih₄' : c₄.input.head = k + 4 := by rw [hih₄, hih₃']
    have hsfx₄ := inpSfx_congr (inpSfx_of_cells_eq (inpSfx_tail hsfx₃) hcl₄)
      (show k + 4 = k + 3 + 1 by omega)
    -- the desc tape gained one symbol
    have hwork4₃ : c₃.work 4 = c.work 4 := by rw [hwk₃, hwk₂, hwk₁]
    have hpush := holdsExact_push hh4 hd4 (symOfPair b₀ b₁)
    have hh4' : (c₄.work 4).HoldsExact (acc ++ [symOfPair b₀ b₁]) := by
      rw [hw44, hwork4₃]; exact hpush.1
    have hd4' : (c₄.work 4).head = (acc ++ [symOfPair b₀ b₁]).length + 1 := by
      rw [hw44, hwork4₃]; exact hpush.2
    -- recurse on the remaining α-bits
    obtain ⟨c', p, hreach, hst', hih', hcl', hsfx', hh4'', hd4'', hfr', hout'⟩ :=
      phase1_loop x rest (acc ++ [symOfPair b₀ b₁]) (k + 4) c₄ hst₄ (by omega) hih₄' hsfx₄
        hh4' hd4'
        (fun i hi => by rw [hfr₄ i hi, hwk₃, hwk₂, hwk₁]; exact hwo i hi)
        (by rw [hout₄, hout₃, hout₂, hout₁]; exact ho)
        (by rw [hout₄, hout₃, hout₂, hout₁]; exact hoh)
    have hgp : acc ++ groupPairs (b₀ :: b₁ :: rest)
        = (acc ++ [symOfPair b₀ b₁]) ++ groupPairs rest := by
      show acc ++ (symOfPair b₀ b₁ :: groupPairs rest) = _
      simp
    refine ⟨c', p, ?_, hst', ?_, by rw [hcl', hcl₄, hcl₃, hcl₂, hcl₁], ?_, ?_, ?_,
      ?_, by rw [hout', hout₄, hout₃, hout₂, hout₁]⟩
    · rw [show 2 * (b₀ :: b₁ :: rest).length = 2 * rest.length + 1 + 1 + 1 + 1 by
        simp only [List.length_cons]; omega]
      exact .step hs₁ (.step hs₂ (.step hs₃ (.step hs₄ hreach)))
    · rw [hih']
      simp only [List.length_cons]
      omega
    · exact inpSfx_congr hsfx' (by simp only [List.length_cons]; omega)
    · rw [hgp]; exact hh4''
    · rw [hgp]; exact hd4''
    · intro i hi
      rw [hfr' i hi, hfr₄ i hi, hwk₃, hwk₂, hwk₁]

-- ════════════════════════════════════════════════════════════════════════
-- Phase 1 → 2: the separator
-- ════════════════════════════════════════════════════════════════════════

/-- Consume the separator `01` (2 steps), entering `copyX` with work tape 0
    advanced by one cell. A pending α-bit is dropped. -/
private theorem phase1_sep {x : List Bool} {p : Option Bool} {k : ℕ}
    {c : Cfg 6 initTM.Q}
    (hst : c.state = InitQ.readFst p)
    (hih : c.input.head = k)
    (hsfx : InpSfx c.input k (false :: true :: x))
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (ho : c.output.read ≠ Γ.start) (hoh : 1 ≤ c.output.head) :
    ∃ c', initTM.reachesIn 2 c c' ∧
      c'.state = InitQ.copyX ∧
      c'.input.head = k + 2 ∧
      c'.input.cells = c.input.cells ∧
      InpSfx c'.input (k + 2) x ∧
      (∀ i, i ≠ (0 : Fin 6) → c'.work i = c.work i) ∧
      (c'.work 0).cells = (c.work 0).cells ∧
      (c'.work 0).head = (c.work 0).head + 1 ∧
      c'.output = c.output := by
  -- step 1: read the 0
  have hread₁ : c.input.read = Γ.ofBool false := by
    rw [Tape.read, hih]; exact inpSfx_head hsfx
  obtain ⟨c₁, hs₁, hst₁, hcl₁, hih₁, hwk₁, hout₁⟩ := step_readFst hst hread₁ hw ho hoh
  have hih₁' : c₁.input.head = k + 1 := by rw [hih₁, hih]
  have hsfx₁ := inpSfx_of_cells_eq (inpSfx_tail hsfx) hcl₁
  -- step 2: read the 1 — the separator is complete
  have hread₂ : c₁.input.read = Γ.one := by
    rw [Tape.read, hih₁']; exact inpSfx_head hsfx₁
  obtain ⟨c₂, hs₂, hst₂, hcl₂, hih₂, hfr₂, hw0c, hw0h, hout₂⟩ :=
    step_readSnd_sep hst₁ hread₂ (by rw [hwk₁]; exact hw)
      (by rw [hout₁]; exact ho) (by rw [hout₁]; exact hoh)
  refine ⟨c₂, .step hs₁ (.step hs₂ .zero), hst₂, by rw [hih₂, hih₁'],
    by rw [hcl₂, hcl₁],
    inpSfx_congr (inpSfx_of_cells_eq (inpSfx_tail hsfx₁) hcl₂) (by omega),
    fun i hi => by rw [hfr₂ i hi, hwk₁], by rw [hw0c, hwk₁], by rw [hw0h, hwk₁],
    by rw [hout₂, hout₁]⟩

-- ════════════════════════════════════════════════════════════════════════
-- Phase 2 loop: copy x (shifted)
-- ════════════════════════════════════════════════════════════════════════

/-- **Phase-2 loop**: copy the remaining bits `xs` of `x` onto work tape 0
    (already-copied prefix `acc`, `□` shadow at cell 1), then detect the end
    of the input (blank) and enter `rewindDesc`. -/
private theorem phase2_loop :
    ∀ (xs : List Bool) (acc : List Γw) (k : ℕ) (c : Cfg 6 initTM.Q),
      c.state = InitQ.copyX →
      c.input.head = k →
      InpSfx c.input k xs →
      (c.work 0).HoldsExact (Γw.blank :: acc) →
      (c.work 0).head = acc.length + 2 →
      (∀ i, i ≠ (0 : Fin 6) → (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head) →
      c.output.read ≠ Γ.start → 1 ≤ c.output.head →
      ∃ c', initTM.reachesIn (xs.length + 1) c c' ∧
        c'.state = InitQ.rewindDesc ∧
        c'.input.head = k + xs.length ∧
        c'.input.cells = c.input.cells ∧
        (c'.work 0).HoldsExact (Γw.blank :: (acc ++ bitsToSyms xs)) ∧
        (c'.work 0).head = (acc ++ bitsToSyms xs).length + 2 ∧
        (∀ i, i ≠ (0 : Fin 6) → c'.work i = c.work i) ∧
        c'.output = c.output
  | [] => by
    intro acc k c hst hih hsfx hh0 hd0 hwo ho hoh
    have hw0read : (c.work 0).read = Γ.blank := by
      rw [Tape.read, hd0]
      exact Tape.HoldsExact.cells_ge hh0 (by simp)
    have hwAll : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head := by
      intro i
      by_cases h0 : i = (0 : Fin 6)
      · subst h0
        exact ⟨by rw [hw0read]; simp, by rw [hd0]; omega⟩
      · exact hwo i h0
    have hread : c.input.read = Γ.blank := by
      rw [Tape.read, hih]; exact inpSfx_nil hsfx
    obtain ⟨c₁, hs₁, hst₁, hin₁, hwk₁, hout₁⟩ := step_copyX_blank hst hread hwAll ho hoh
    refine ⟨c₁, .step hs₁ .zero, hst₁, by rw [hin₁, hih]; simp, by rw [hin₁],
      ?_, ?_, fun i _ => by rw [hwk₁], by rw [hout₁]⟩
    · rw [show acc ++ bitsToSyms [] = acc by simp [bitsToSyms], hwk₁]
      exact hh0
    · rw [show acc ++ bitsToSyms [] = acc by simp [bitsToSyms], hwk₁]
      exact hd0
  | b :: xs => by
    intro acc k c hst hih hsfx hh0 hd0 hwo ho hoh
    have hw0read : (c.work 0).read = Γ.blank := by
      rw [Tape.read, hd0]
      exact Tape.HoldsExact.cells_ge hh0 (by simp)
    have hwAll : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head := by
      intro i
      by_cases h0 : i = (0 : Fin 6)
      · subst h0
        exact ⟨by rw [hw0read]; simp, by rw [hd0]; omega⟩
      · exact hwo i h0
    have hread : c.input.read = Γ.ofBool b := by
      rw [Tape.read, hih]; exact inpSfx_head hsfx
    obtain ⟨c₁, hs₁, hst₁, hcl₁, hih₁, hfr₁, hw0₁, hout₁⟩ :=
      step_copyX_bit hst hread hwAll ho hoh
    -- work tape 0 gained one symbol
    have hpush := holdsExact_push hh0 (by rw [hd0]; simp) (bitSym b)
    have hh0₁ : (c₁.work 0).HoldsExact (Γw.blank :: (acc ++ [bitSym b])) := by
      rw [hw0₁]
      simpa using hpush.1
    have hd0₁ : (c₁.work 0).head = (acc ++ [bitSym b]).length + 2 := by
      rw [hw0₁]
      have := hpush.2
      simp only [List.cons_append, List.length_cons] at this ⊢
      omega
    -- recurse
    obtain ⟨c', hreach, hst', hih', hcl', hh0', hd0', hfr', hout'⟩ :=
      phase2_loop xs (acc ++ [bitSym b]) (k + 1) c₁ hst₁ (by rw [hih₁, hih])
        (inpSfx_of_cells_eq (inpSfx_tail hsfx) hcl₁) hh0₁ hd0₁
        (fun i hi => by rw [hfr₁ i hi]; exact hwo i hi)
        (by rw [hout₁]; exact ho) (by rw [hout₁]; exact hoh)
    have hbs : acc ++ bitsToSyms (b :: xs) = (acc ++ [bitSym b]) ++ bitsToSyms xs := by
      simp [bitsToSyms]
    refine ⟨c', .step hs₁ hreach, hst', ?_, by rw [hcl', hcl₁], ?_, ?_,
      fun i hi => by rw [hfr' i hi, hfr₁ i hi], by rw [hout', hout₁]⟩
    · rw [hih']
      simp only [List.length_cons]
      omega
    · rw [hbs]; exact hh0'
    · rw [hbs]; exact hd0'

-- ════════════════════════════════════════════════════════════════════════
-- Phase 3 loop: copy the qstart field onto the state tape
-- ════════════════════════════════════════════════════════════════════════

/-- **Field-copy loop**: with the desc tape (work 4) at position `p + 1` and
    holding the symbol suffix `rest` from there on, copy the symbols before
    the first blank cell — exactly `(takeField rest).1` — onto the state
    tape (work 3), then enter `rewindDesc2`. The terminating blank cell is
    read but not copied. -/
private theorem copyField_loop :
    ∀ (rest facc : List Γw) (p : ℕ) (c : Cfg 6 initTM.Q),
      c.state = InitQ.copyField →
      (c.work 4).head = p + 1 →
      (∀ j : ℕ, (c.work 4).cells (p + 1 + j)
        = if h : j < rest.length then (rest[j]).toΓ else Γ.blank) →
      (c.work 3).HoldsExact facc →
      (c.work 3).head = facc.length + 1 →
      c.input.read ≠ Γ.start →
      (∀ i, i ≠ (3 : Fin 6) → i ≠ (4 : Fin 6) →
        (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head) →
      c.output.read ≠ Γ.start → 1 ≤ c.output.head →
      ∃ c', initTM.reachesIn ((takeField rest).1.length + 1) c c' ∧
        c'.state = InitQ.rewindDesc2 ∧
        c'.input = c.input ∧
        (c'.work 4).cells = (c.work 4).cells ∧
        (c'.work 4).head = p + 1 + (takeField rest).1.length ∧
        (c'.work 3).HoldsExact (facc ++ (takeField rest).1) ∧
        (c'.work 3).head = (facc ++ (takeField rest).1).length + 1 ∧
        (∀ i, i ≠ (3 : Fin 6) → i ≠ (4 : Fin 6) → c'.work i = c.work i) ∧
        c'.output = c.output
  | [] => by
    intro facc p c hst hhd4 hcells hh3 hd3 hi hwo ho hoh
    have hread4 : (c.work 4).read = Γ.blank := by
      rw [Tape.read, hhd4]
      simpa using hcells 0
    have hw3read : (c.work 3).read = Γ.blank := by
      rw [Tape.read, hd3]
      exact Tape.HoldsExact.cells_ge hh3 (le_refl _)
    have hwAll : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head := by
      intro i
      by_cases h3 : i = (3 : Fin 6)
      · subst h3
        exact ⟨by rw [hw3read]; simp, by rw [hd3]; omega⟩
      · by_cases h4 : i = (4 : Fin 6)
        · subst h4
          exact ⟨by rw [hread4]; simp, by rw [hhd4]; omega⟩
        · exact hwo i h3 h4
    obtain ⟨c₁, hs₁, hst₁, hin₁, hwk₁, hout₁⟩ :=
      step_copyField_blank hst hread4 hi hwAll ho hoh
    refine ⟨c₁, .step hs₁ .zero, hst₁, hin₁, by rw [hwk₁], ?_, ?_, ?_,
      fun i h3 h4 => by rw [hwk₁], by rw [hout₁]⟩
    · rw [hwk₁, hhd4]
      simp [takeField]
    · rw [hwk₁]
      simpa [takeField] using hh3
    · rw [hwk₁]
      simpa [takeField] using hd3
  | .blank :: r => by
    intro facc p c hst hhd4 hcells hh3 hd3 hi hwo ho hoh
    have hread4 : (c.work 4).read = Γ.blank := by
      rw [Tape.read, hhd4]
      simpa using hcells 0
    have hw3read : (c.work 3).read = Γ.blank := by
      rw [Tape.read, hd3]
      exact Tape.HoldsExact.cells_ge hh3 (le_refl _)
    have hwAll : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head := by
      intro i
      by_cases h3 : i = (3 : Fin 6)
      · subst h3
        exact ⟨by rw [hw3read]; simp, by rw [hd3]; omega⟩
      · by_cases h4 : i = (4 : Fin 6)
        · subst h4
          exact ⟨by rw [hread4]; simp, by rw [hhd4]; omega⟩
        · exact hwo i h3 h4
    obtain ⟨c₁, hs₁, hst₁, hin₁, hwk₁, hout₁⟩ :=
      step_copyField_blank hst hread4 hi hwAll ho hoh
    refine ⟨c₁, .step hs₁ .zero, hst₁, hin₁, by rw [hwk₁], ?_, ?_, ?_,
      fun i h3 h4 => by rw [hwk₁], by rw [hout₁]⟩
    · rw [hwk₁, hhd4]
      simp [takeField]
    · rw [hwk₁]
      simpa [takeField] using hh3
    · rw [hwk₁]
      simpa [takeField] using hd3
  | .zero :: r => by
    intro facc p c hst hhd4 hcells hh3 hd3 hi hwo ho hoh
    have hread4 : (c.work 4).read = Γ.zero := by
      rw [Tape.read, hhd4]
      simpa using hcells 0
    have hw3read : (c.work 3).read = Γ.blank := by
      rw [Tape.read, hd3]
      exact Tape.HoldsExact.cells_ge hh3 (le_refl _)
    have hwAll : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head := by
      intro i
      by_cases h3 : i = (3 : Fin 6)
      · subst h3
        exact ⟨by rw [hw3read]; simp, by rw [hd3]; omega⟩
      · by_cases h4 : i = (4 : Fin 6)
        · subst h4
          exact ⟨by rw [hread4]; simp, by rw [hhd4]; omega⟩
        · exact hwo i h3 h4
    obtain ⟨c₁, hs₁, hst₁, hin₁, hfr₁, hw3₁, hw4c₁, hw4h₁, hout₁⟩ :=
      step_copyField_bit (Or.inl rfl) hst hread4 hi hwAll ho hoh
    have hpush := holdsExact_push hh3 hd3 Γw.zero
    have hh3₁ : (c₁.work 3).HoldsExact (facc ++ [Γw.zero]) := by
      rw [hw3₁]; exact hpush.1
    have hd3₁ : (c₁.work 3).head = (facc ++ [Γw.zero]).length + 1 := by
      rw [hw3₁]; exact hpush.2
    have hhd4₁ : (c₁.work 4).head = p + 1 + 1 := by rw [hw4h₁, hhd4]
    have hcells₁ : ∀ j : ℕ, (c₁.work 4).cells (p + 1 + 1 + j)
        = if h : j < r.length then (r[j]).toΓ else Γ.blank := by
      intro j
      rw [hw4c₁]
      have h := hcells (j + 1)
      rw [show p + 1 + (j + 1) = p + 1 + 1 + j by omega] at h
      simp only [List.length_cons] at h
      rw [h]
      by_cases hj : j < r.length
      · rw [dite_eq_left (by omega), dite_eq_left hj]
        simp
      · rw [dite_eq_right (by omega), dite_eq_right hj]
    obtain ⟨c', hreach, hst', hin', hw4c', hw4h', hh3', hd3', hfr', hout'⟩ :=
      copyField_loop r (facc ++ [Γw.zero]) (p + 1) c₁ hst₁ hhd4₁ hcells₁ hh3₁ hd3₁
        (by rw [hin₁]; exact hi)
        (fun i h3 h4 => by rw [hfr₁ i h3 h4]; exact hwo i h3 h4)
        (by rw [hout₁]; exact ho) (by rw [hout₁]; exact hoh)
    have htf1 : (takeField (Γw.zero :: r)).1 = Γw.zero :: (takeField r).1 := by
      simp [takeField]
    have happ : facc ++ (takeField (Γw.zero :: r)).1
        = (facc ++ [Γw.zero]) ++ (takeField r).1 := by
      rw [htf1]; simp
    refine ⟨c', ?_, hst', by rw [hin', hin₁], by rw [hw4c', hw4c₁], ?_, ?_, ?_, ?_,
      by rw [hout', hout₁]⟩
    · rw [show (takeField (Γw.zero :: r)).1.length + 1
          = ((takeField r).1.length + 1) + 1 by rw [htf1]; simp]
      exact .step hs₁ hreach
    · rw [hw4h', htf1]
      simp only [List.length_cons]
      omega
    · rw [happ]; exact hh3'
    · rw [happ]; exact hd3'
    · intro i h3 h4
      rw [hfr' i h3 h4, hfr₁ i h3 h4]
  | .one :: r => by
    intro facc p c hst hhd4 hcells hh3 hd3 hi hwo ho hoh
    have hread4 : (c.work 4).read = Γ.one := by
      rw [Tape.read, hhd4]
      simpa using hcells 0
    have hw3read : (c.work 3).read = Γ.blank := by
      rw [Tape.read, hd3]
      exact Tape.HoldsExact.cells_ge hh3 (le_refl _)
    have hwAll : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head := by
      intro i
      by_cases h3 : i = (3 : Fin 6)
      · subst h3
        exact ⟨by rw [hw3read]; simp, by rw [hd3]; omega⟩
      · by_cases h4 : i = (4 : Fin 6)
        · subst h4
          exact ⟨by rw [hread4]; simp, by rw [hhd4]; omega⟩
        · exact hwo i h3 h4
    obtain ⟨c₁, hs₁, hst₁, hin₁, hfr₁, hw3₁, hw4c₁, hw4h₁, hout₁⟩ :=
      step_copyField_bit (Or.inr rfl) hst hread4 hi hwAll ho hoh
    have hpush := holdsExact_push hh3 hd3 Γw.one
    have hh3₁ : (c₁.work 3).HoldsExact (facc ++ [Γw.one]) := by
      rw [hw3₁]; exact hpush.1
    have hd3₁ : (c₁.work 3).head = (facc ++ [Γw.one]).length + 1 := by
      rw [hw3₁]; exact hpush.2
    have hhd4₁ : (c₁.work 4).head = p + 1 + 1 := by rw [hw4h₁, hhd4]
    have hcells₁ : ∀ j : ℕ, (c₁.work 4).cells (p + 1 + 1 + j)
        = if h : j < r.length then (r[j]).toΓ else Γ.blank := by
      intro j
      rw [hw4c₁]
      have h := hcells (j + 1)
      rw [show p + 1 + (j + 1) = p + 1 + 1 + j by omega] at h
      simp only [List.length_cons] at h
      rw [h]
      by_cases hj : j < r.length
      · rw [dite_eq_left (by omega), dite_eq_left hj]
        simp
      · rw [dite_eq_right (by omega), dite_eq_right hj]
    obtain ⟨c', hreach, hst', hin', hw4c', hw4h', hh3', hd3', hfr', hout'⟩ :=
      copyField_loop r (facc ++ [Γw.one]) (p + 1) c₁ hst₁ hhd4₁ hcells₁ hh3₁ hd3₁
        (by rw [hin₁]; exact hi)
        (fun i h3 h4 => by rw [hfr₁ i h3 h4]; exact hwo i h3 h4)
        (by rw [hout₁]; exact ho) (by rw [hout₁]; exact hoh)
    have htf1 : (takeField (Γw.one :: r)).1 = Γw.one :: (takeField r).1 := by
      simp [takeField]
    have happ : facc ++ (takeField (Γw.one :: r)).1
        = (facc ++ [Γw.one]) ++ (takeField r).1 := by
      rw [htf1]; simp
    refine ⟨c', ?_, hst', by rw [hin', hin₁], by rw [hw4c', hw4c₁], ?_, ?_, ?_, ?_,
      by rw [hout', hout₁]⟩
    · rw [show (takeField (Γw.one :: r)).1.length + 1
          = ((takeField r).1.length + 1) + 1 by rw [htf1]; simp]
      exact .step hs₁ hreach
    · rw [hw4h', htf1]
      simp only [List.length_cons]
      omega
    · rw [happ]; exact hh3'
    · rw [happ]; exact hd3'
    · intro i h3 h4
      rw [hfr' i h3 h4, hfr₁ i h3 h4]

-- ════════════════════════════════════════════════════════════════════════
-- Postcondition conversions
-- ════════════════════════════════════════════════════════════════════════

/-- An all-blank tape also holds the single symbol `□` exactly. -/
private theorem holdsExact_blank_singleton {t : Tape} (h : t.HoldsExact []) :
    t.HoldsExact [Γw.blank] := by
  refine ⟨h.1, fun i => ?_⟩
  rw [Tape.HoldsExact.cells_ge h (Nat.zero_le i)]
  by_cases hi : i < 1
  · rw [dite_eq_left (show i < [Γw.blank].length by simpa using hi)]
    obtain rfl : i = 0 := by omega
    rfl
  · rw [dite_eq_right (show ¬i < [Γw.blank].length by simpa using hi)]

/-- The exact-contents view of the shifted `x` tape is the `VShift` shadow of
    `Tape.init (x.map Γ.ofBool)` (see `VShift.init`). -/
private theorem holdsExact_shift_cells {t : Tape} {x : List Bool}
    (h : t.HoldsExact (Γw.blank :: bitsToSyms x)) :
    t.cells = fun k => if k = 0 then Γ.start else if k = 1 then Γ.blank
      else ((x.map Γ.ofBool)[k - 2]?).getD Γ.blank := by
  funext k
  by_cases hk0 : k = 0
  · subst hk0
    simpa using h.1
  · by_cases hk1 : k = 1
    · subst hk1
      have := Tape.HoldsExact.cells_lt h (i := 0) (by simp)
      simpa using this
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
      simp only [show m + 2 ≠ 0 by omega, ite_false, show m + 2 ≠ 1 by omega,
        show m + 2 - 2 = m by omega]
      rw [show m + 2 = m + 1 + 1 by omega, h.2 (m + 1)]
      simp only [List.length_cons, bitsToSyms_length]
      by_cases hm : m < x.length
      · rw [dite_eq_left (by omega), List.getElem_cons_succ, List.getElem?_map,
          List.getElem?_eq_getElem hm]
        simp only [bitsToSyms, List.getElem_map, Option.map_some, Option.getD_some]
        exact bitSym_toΓ _
      · rw [dite_eq_right (by omega), List.getElem?_map,
          List.getElem?_eq_none (by omega)]
        rfl

-- ════════════════════════════════════════════════════════════════════════
-- Main theorem
-- ════════════════════════════════════════════════════════════════════════

/-- **Bounced core of `initTM`.** From a configuration in state
    `readFst none` with the input head at cell 1 over the cells of
    `Tape.init ((pair α x).map Γ.ofBool)`, all six work-tape heads at cell 1
    over blank cells, and the output head at cell 1 over blank cells, the
    machine halts within `4·|pair α x| + 4·|groupPairs α| + 23` steps in the
    `initTM` postcondition. Both `initTM_hoareTime` (one bouncing step from
    fresh tapes) and `initTM_hoareTime_started` (one idle step from started
    tapes) land in this configuration after their first step. -/
private theorem initTM_hoareTime_core (α x : List Bool) {c₁ : Cfg 6 initTM.Q}
    (hst₁ : c₁.state = InitQ.readFst none)
    (hcl₁ : c₁.input.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells)
    (hih₁ : c₁.input.head = 1)
    (hwcells₁ : ∀ i, (c₁.work i).cells = (Tape.init []).cells)
    (hwhead₁ : ∀ i, (c₁.work i).head = 1)
    (hocl₁' : c₁.output.cells = (Tape.init []).cells)
    (hoh₁ : c₁.output.head = 1) :
    ∃ (c' : Cfg 6 initTM.Q) (t : ℕ),
      t ≤ 4 * (pair α x).length + 4 * (groupPairs α).length + 23 ∧
      initTM.reachesIn t c₁ c' ∧ initTM.halted c' ∧
      c'.input.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧
      (c'.work 0).cells = (fun k => if k = 0 then Γ.start else if k = 1 then Γ.blank
        else (((x.map Γ.ofBool))[k - 2]?).getD Γ.blank) ∧ (c'.work 0).head = 1 ∧
      (c'.work 1).HoldsExact [] ∧ (c'.work 1).head = 1 ∧
      (c'.work 2).HoldsExact [] ∧ (c'.work 2).head = 1 ∧
      (c'.work 3).HoldsExact (takeField (groupPairs α)).1 ∧ (c'.work 3).head = 1 ∧
      (c'.work 4).HoldsExact (groupPairs α) ∧ (c'.work 4).head = 1 ∧
      (c'.work 5).HoldsExact [] ∧ (c'.work 5).head = 1 ∧
      c'.output.cells = (Tape.init []).cells ∧ c'.output.head = 1 := by
  have hP : pair α x = (α.flatMap fun b => [b, b]) ++ false :: true :: x := by
    simp [pair, delimit]
  have hwf := Tape.StartInvariant.init_ofBool (pair α x)
  have hblank1 : (Tape.init []).cells 1 = Γ.blank := Tape.init_nil_cells_succ 0
  have hwo₁ : ∀ i, (c₁.work i).read ≠ Γ.start ∧ 1 ≤ (c₁.work i).head := by
    intro i
    refine ⟨?_, (hwhead₁ i).ge⟩
    rw [Tape.read, hwhead₁ i, hwcells₁ i, hblank1]
    simp
  have ho₁ : c₁.output.read ≠ Γ.start := by
    rw [Tape.read, hoh₁, hocl₁', hblank1]
    simp
  have hoh₁' : 1 ≤ c₁.output.head := hoh₁.ge
  -- ── phase 1: parse the α-region onto the desc tape ──
  have hsfx₁ : InpSfx c₁.input 1 (pair α x) :=
    inpSfx_of_cells_eq (inpSfx_initTape (pair α x)) hcl₁
  have hh4₁ : (c₁.work 4).HoldsExact [] :=
    holdsExact_of_cells_eq Tape.HoldsExact.init_nil (hwcells₁ 4)
  obtain ⟨c₂, p₂, hreach₂, hst₂, hih₂, hcl₂, hsfx₂, hh4₂, hd4₂, hfr₂, hout₂⟩ :=
    phase1_loop x α [] 1 c₁ hst₁ (le_refl 1) hih₁
      (by rw [← hP]; exact hsfx₁) hh4₁ (by rw [hwhead₁ 4]; rfl)
      (fun i _ => hwo₁ i) ho₁ hoh₁'
  simp only [List.nil_append] at hh4₂ hd4₂
  -- ── the separator ──
  have hwAll₂ : ∀ i, (c₂.work i).read ≠ Γ.start ∧ 1 ≤ (c₂.work i).head :=
    hw_of_frontier hh4₂ hd4₂ (fun i hi => by rw [hfr₂ i hi]; exact hwo₁ i)
  obtain ⟨c₃, hreach₃, hst₃, hih₃, hcl₃, hsfx₃, hfr₃, h0c₃, h0h₃, hout₃⟩ :=
    phase1_sep hst₂ hih₂ hsfx₂ hwAll₂ (by rw [hout₂]; exact ho₁)
      (by rw [hout₂]; exact hoh₁')
  -- ── phase 2: copy x (shifted) onto work tape 0 ──
  have hh0₃ : (c₃.work 0).HoldsExact (Γw.blank :: []) := by
    apply holdsExact_blank_singleton
    apply holdsExact_of_cells_eq Tape.HoldsExact.init_nil
    rw [h0c₃, hfr₂ 0 (by decide), hwcells₁ 0]
  have hd0₃ : (c₃.work 0).head = ([] : List Γw).length + 2 := by
    rw [h0h₃, hfr₂ 0 (by decide), hwhead₁ 0]
    simp
  obtain ⟨c₄, hreach₄, hst₄, hih₄, hcl₄, hh0₄, hd0₄, hfr₄, hout₄⟩ :=
    phase2_loop x [] (1 + 2 * α.length + 2) c₃ hst₃ hih₃ hsfx₃ hh0₃ hd0₃
      (fun i hi => by rw [hfr₃ i hi]; exact hwAll₂ i)
      (by rw [hout₃, hout₂]; exact ho₁) (by rw [hout₃, hout₂]; exact hoh₁')
  simp only [List.nil_append] at hh0₄ hd0₄
  rw [bitsToSyms_length] at hd0₄
  have hclx₄ : c₄.input.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells := by
    rw [hcl₄, hcl₃, hcl₂, hcl₁]
  have hi₄ : c₄.input.read ≠ Γ.start := by
    rw [Tape.read, hclx₄]
    exact hwf.2 _ (by rw [hih₄]; omega)
  have hw4₄ : c₄.work 4 = c₂.work 4 := by
    rw [hfr₄ 4 (by decide), hfr₃ 4 (by decide)]
  have hh4₄ : (c₄.work 4).HoldsExact (groupPairs α) := by rw [hw4₄]; exact hh4₂
  have hd4₄ : (c₄.work 4).head = (groupPairs α).length + 1 := by rw [hw4₄]; exact hd4₂
  have hu₄ : ∀ i : Fin 6, i ≠ 0 → i ≠ 4 → c₄.work i = c₁.work i := by
    intro i h0 h4
    rw [hfr₄ i h0, hfr₃ i h0, hfr₂ i h4]
  have h0read₄ : (c₄.work 0).read = Γ.blank := by
    rw [Tape.read, hd0₄]
    exact Tape.HoldsExact.cells_ge hh0₄ (by simp)
  have hout₄' : c₄.output = c₁.output := by rw [hout₄, hout₃, hout₂]
  have hwo₄ : ∀ i : Fin 6, i ≠ 4 → (c₄.work i).read ≠ Γ.start ∧ 1 ≤ (c₄.work i).head := by
    intro i h4
    by_cases h0 : i = 0
    · subst h0
      exact ⟨by rw [h0read₄]; simp, by rw [hd0₄]; omega⟩
    · rw [hu₄ i h0 h4]
      exact hwo₁ i
  -- ── rewind the desc tape ──
  obtain ⟨c₅, hreach₅, hst₅, hd4₅, hcl4₅, hfr₅, hin₅, hout₅⟩ :=
    rewind_loop (idx := 4) (qloop := .rewindDesc) (qnext := .copyField)
      (fun _ _ _ => rfl) nofun
      ((groupPairs α).length + 1) c₄ hst₄ hd4₄
      (Tape.HoldsExact.startInvariant hh4₄).1
      (fun j hj => (Tape.HoldsExact.startInvariant hh4₄).2 j hj)
      hi₄ hwo₄
      (by rw [hout₄']; exact ho₁) (by rw [hout₄']; exact hoh₁')
  -- ── copy the qstart field onto the state tape ──
  have hh4₅ : (c₅.work 4).HoldsExact (groupPairs α) := holdsExact_of_cells_eq hh4₄ hcl4₅
  have hh3₅ : (c₅.work 3).HoldsExact [] := by
    rw [hfr₅ 3 (by decide), hu₄ 3 (by decide) (by decide)]
    exact holdsExact_of_cells_eq Tape.HoldsExact.init_nil (hwcells₁ 3)
  have hd3₅ : (c₅.work 3).head = ([] : List Γw).length + 1 := by
    rw [hfr₅ 3 (by decide), hu₄ 3 (by decide) (by decide), hwhead₁ 3]
    simp
  have hwo₅ : ∀ i : Fin 6, i ≠ 3 → i ≠ 4 →
      (c₅.work i).read ≠ Γ.start ∧ 1 ≤ (c₅.work i).head := by
    intro i h3 h4
    rw [hfr₅ i h4]
    exact hwo₄ i h4
  obtain ⟨c₆, hreach₆, hst₆, hin₆, hcl4₆, hd4₆, hh3₆, hd3₆, hfr₆, hout₆⟩ :=
    copyField_loop (groupPairs α) [] 0 c₅ hst₅ (by rw [hd4₅])
      (fun j => by rw [show 0 + 1 + j = j + 1 by omega]; exact hh4₅.2 j)
      hh3₅ hd3₅ (by rw [hin₅]; exact hi₄) hwo₅
      (by rw [hout₅, hout₄']; exact ho₁) (by rw [hout₅, hout₄']; exact hoh₁')
  simp only [List.nil_append] at hh3₆ hd3₆
  -- ── rewind the desc tape again ──
  have hh4₆ : (c₆.work 4).HoldsExact (groupPairs α) := holdsExact_of_cells_eq hh4₅ hcl4₆
  have hd4₆' : (c₆.work 4).head = (takeField (groupPairs α)).1.length + 1 := by
    rw [hd4₆]; omega
  have hwo₆ : ∀ i : Fin 6, i ≠ 4 →
      (c₆.work i).read ≠ Γ.start ∧ 1 ≤ (c₆.work i).head := by
    intro i h4
    by_cases h3 : i = 3
    · subst h3
      refine ⟨?_, by rw [hd3₆]; omega⟩
      rw [Tape.read, hd3₆, Tape.HoldsExact.cells_ge hh3₆ (le_refl _)]
      simp
    · rw [hfr₆ i h3 h4]
      exact hwo₅ i h3 h4
  obtain ⟨c₇, hreach₇, hst₇, hd4₇, hcl4₇, hfr₇, hin₇, hout₇⟩ :=
    rewind_loop (idx := 4) (qloop := .rewindDesc2) (qnext := .rewindState)
      (fun _ _ _ => rfl) nofun
      ((takeField (groupPairs α)).1.length + 1) c₆ hst₆ hd4₆'
      (Tape.HoldsExact.startInvariant hh4₆).1
      (fun j hj => (Tape.HoldsExact.startInvariant hh4₆).2 j hj)
      (by rw [hin₆, hin₅]; exact hi₄) hwo₆
      (by rw [hout₆, hout₅, hout₄']; exact ho₁)
      (by rw [hout₆, hout₅, hout₄']; exact hoh₁')
  -- ── rewind the state tape ──
  have hh3₇ : (c₇.work 3).HoldsExact (takeField (groupPairs α)).1 := by
    rw [hfr₇ 3 (by decide)]; exact hh3₆
  have hd3₇ : (c₇.work 3).head = (takeField (groupPairs α)).1.length + 1 := by
    rw [hfr₇ 3 (by decide)]; exact hd3₆
  have hh4₇ : (c₇.work 4).HoldsExact (groupPairs α) := holdsExact_of_cells_eq hh4₆ hcl4₇
  have hwo₇ : ∀ i : Fin 6, i ≠ 3 →
      (c₇.work i).read ≠ Γ.start ∧ 1 ≤ (c₇.work i).head := by
    intro i h3
    by_cases h4 : i = 4
    · subst h4
      refine ⟨?_, by rw [hd4₇]⟩
      rw [Tape.read, hd4₇]
      exact (Tape.HoldsExact.startInvariant hh4₇).2 1 (le_refl 1)
    · rw [hfr₇ i h4]
      exact hwo₆ i h4
  obtain ⟨c₈, hreach₈, hst₈, hd3₈, hcl3₈, hfr₈, hin₈, hout₈⟩ :=
    rewind_loop (idx := 3) (qloop := .rewindState) (qnext := .rewindV0)
      (fun _ _ _ => rfl) nofun
      ((takeField (groupPairs α)).1.length + 1) c₇ hst₇ hd3₇
      (Tape.HoldsExact.startInvariant hh3₇).1
      (fun j hj => (Tape.HoldsExact.startInvariant hh3₇).2 j hj)
      (by rw [hin₇, hin₆, hin₅]; exact hi₄) hwo₇
      (by rw [hout₇, hout₆, hout₅, hout₄']; exact ho₁)
      (by rw [hout₇, hout₆, hout₅, hout₄']; exact hoh₁')
  -- ── rewind the virtual input tape ──
  have hw0₈ : c₈.work 0 = c₄.work 0 := by
    rw [hfr₈ 0 (by decide), hfr₇ 0 (by decide), hfr₆ 0 (by decide) (by decide),
      hfr₅ 0 (by decide)]
  have hh0₈ : (c₈.work 0).HoldsExact (Γw.blank :: bitsToSyms x) := by
    rw [hw0₈]; exact hh0₄
  have hd0₈ : (c₈.work 0).head = x.length + 2 := by rw [hw0₈]; exact hd0₄
  have hh3₈ : (c₈.work 3).HoldsExact (takeField (groupPairs α)).1 :=
    holdsExact_of_cells_eq hh3₇ hcl3₈
  have hwo₈ : ∀ i : Fin 6, i ≠ 0 →
      (c₈.work i).read ≠ Γ.start ∧ 1 ≤ (c₈.work i).head := by
    intro i h0
    by_cases h3 : i = 3
    · subst h3
      refine ⟨?_, by rw [hd3₈]⟩
      rw [Tape.read, hd3₈]
      exact (Tape.HoldsExact.startInvariant hh3₈).2 1 (le_refl 1)
    · rw [hfr₈ i h3]
      exact hwo₇ i h3
  obtain ⟨c₉, hreach₉, hst₉, hd0₉, hcl0₉, hfr₉, hin₉, hout₉⟩ :=
    rewind_loop (idx := 0) (qloop := .rewindV0) (qnext := .done)
      (fun _ _ _ => rfl) nofun
      (x.length + 2) c₈ hst₈ hd0₈
      (Tape.HoldsExact.startInvariant hh0₈).1
      (fun j hj => (Tape.HoldsExact.startInvariant hh0₈).2 j hj)
      (by rw [hin₈, hin₇, hin₆, hin₅]; exact hi₄) hwo₈
      (by rw [hout₈, hout₇, hout₆, hout₅, hout₄']; exact ho₁)
      (by rw [hout₈, hout₇, hout₆, hout₅, hout₄']; exact hoh₁')
  -- ── assemble ──
  have R₂ := hreach₂
  have R₃ := reachesIn_trans initTM R₂ hreach₃
  have R₄ := reachesIn_trans initTM R₃ hreach₄
  have R₅ := reachesIn_trans initTM R₄ hreach₅
  have R₆ := reachesIn_trans initTM R₅ hreach₆
  have R₇ := reachesIn_trans initTM R₆ hreach₇
  have R₈ := reachesIn_trans initTM R₇ hreach₈
  have R₉ := reachesIn_trans initTM R₈ hreach₉
  have hu₉ : ∀ i : Fin 6, i ≠ 0 → i ≠ 3 → i ≠ 4 → c₉.work i = c₁.work i := by
    intro i h0 h3 h4
    rw [hfr₉ i h0, hfr₈ i h3, hfr₇ i h4, hfr₆ i h3 h4, hfr₅ i h4, hu₄ i h0 h4]
  have h0cells₉ : (c₉.work 0).cells = (c₄.work 0).cells := by
    rw [hcl0₉, hw0₈]
  refine ⟨c₉, _, ?_, R₉, hst₉, ?_, ?_, hd0₉, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · -- time bound
    have hplen := pair_length α x
    have hF := takeField_fst_length (groupPairs α)
    omega
  · -- input cells untouched
    rw [hin₉, hin₈, hin₇, hin₆, hin₅]
    exact hclx₄
  · -- work 0: the VShift shadow of x
    exact holdsExact_shift_cells (holdsExact_of_cells_eq hh0₄ h0cells₉)
  · -- work 1
    rw [hu₉ 1 (by decide) (by decide) (by decide)]
    exact holdsExact_of_cells_eq Tape.HoldsExact.init_nil (hwcells₁ 1)
  · rw [hu₉ 1 (by decide) (by decide) (by decide)]
    exact hwhead₁ 1
  · -- work 2
    rw [hu₉ 2 (by decide) (by decide) (by decide)]
    exact holdsExact_of_cells_eq Tape.HoldsExact.init_nil (hwcells₁ 2)
  · rw [hu₉ 2 (by decide) (by decide) (by decide)]
    exact hwhead₁ 2
  · -- work 3: the qstart field
    rw [hfr₉ 3 (by decide)]
    exact hh3₈
  · rw [hfr₉ 3 (by decide)]
    exact hd3₈
  · -- work 4: the translated description
    rw [hfr₉ 4 (by decide), hfr₈ 4 (by decide)]
    exact hh4₇
  · rw [hfr₉ 4 (by decide), hfr₈ 4 (by decide)]
    exact hd4₇
  · -- work 5
    rw [hu₉ 5 (by decide) (by decide) (by decide)]
    exact holdsExact_of_cells_eq Tape.HoldsExact.init_nil (hwcells₁ 5)
  · rw [hu₉ 5 (by decide) (by decide) (by decide)]
    exact hwhead₁ 5
  · -- output untouched
    rw [hout₉, hout₈, hout₇, hout₆, hout₅, hout₄']
    exact hocl₁'
  · rw [hout₉, hout₈, hout₇, hout₆, hout₅, hout₄']
    exact hoh₁

/-- **`initTM` specification.** Started on input `pair α x` with all work
    tapes and the output tape empty, `initTM` halts within
    `4·|pair α x| + 4·|groupPairs α| + 24` steps having:

    * left the input tape cells untouched;
    * copied `x` onto the virtual input tape (work 0) in the +1-shift
      representation (the `VShift` shadow of `Tape.init (x.map Γ.ofBool)`);
    * translated α onto the desc tape (work 4): `groupPairs α`;
    * copied the qstart field `(takeField (groupPairs α)).1` onto the state
      tape (work 3);
    * left work tapes 1, 2, 5 and the output tape blank;
    * parked every work-tape head and the output head at cell 1. -/
theorem initTM_hoareTime (α x : List Bool) :
    initTM.HoareTime
      (fun inp work out =>
        inp = Tape.init ((pair α x).map Γ.ofBool) ∧
        (∀ i : Fin 6, work i = Tape.init []) ∧
        out = Tape.init [])
      (fun inp work out =>
        inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧
        (work 0).cells = (fun k => if k = 0 then Γ.start else if k = 1 then Γ.blank
          else (((x.map Γ.ofBool))[k - 2]?).getD Γ.blank) ∧ (work 0).head = 1 ∧
        (work 1).HoldsExact [] ∧ (work 1).head = 1 ∧
        (work 2).HoldsExact [] ∧ (work 2).head = 1 ∧
        (work 3).HoldsExact (takeField (groupPairs α)).1 ∧ (work 3).head = 1 ∧
        (work 4).HoldsExact (groupPairs α) ∧ (work 4).head = 1 ∧
        (work 5).HoldsExact [] ∧ (work 5).head = 1 ∧
        out.cells = (Tape.init []).cells ∧ out.head = 1)
      (4 * (pair α x).length + 4 * (groupPairs α).length + 24) := by
  intro inp work out ⟨hinp, hwork, hout⟩
  subst hinp
  subst hout
  -- ── step 1: bounce all heads off ▷ ──
  obtain ⟨c₁, hs₁, hst₁, hcl₁, hih₁, hwk₁, hocl₁, hoh₁⟩ :=
    step_start
      (c := { state := initTM.qstart
              input := Tape.init ((pair α x).map Γ.ofBool)
              work := work
              output := Tape.init [] })
      rfl rfl (by simp [Tape.init])
      (fun i => by show (work i).head = 0; rw [hwork i]; rfl)
      (fun i => by show (work i).cells 0 = Γ.start; rw [hwork i]; simp [Tape.init])
      rfl (by simp [Tape.init])
  -- ── the bounced core ──
  obtain ⟨c', t, hle, hreach, hhalt, hpost⟩ :=
    initTM_hoareTime_core α x hst₁ hcl₁ hih₁
      (fun i => ((hwk₁ i).1).trans (congrArg Tape.cells (hwork i)))
      (fun i => (hwk₁ i).2) hocl₁ hoh₁
  exact ⟨c', t + 1, by omega, .step hs₁ hreach, hhalt, hpost⟩

/-- **`initTM` specification, started form.** Identical postcondition and
    time bound to `initTM_hoareTime`, but the tapes arrive already bounced
    off `▷`: the input head is parked at cell 1 over the same cells, every
    work tape is `(Tape.init []).move Dir3.right` (blank cells, head 1), and
    the output tape is blank with head 1. This is the form in which a lifted
    `initTM` receives its tapes when it runs mid-sequence rather than as the
    first phase of a machine. -/
theorem initTM_hoareTime_started (α x : List Bool) :
    initTM.HoareTime
      (fun inp work out =>
        inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧ inp.head = 1 ∧
        (∀ i : Fin 6, work i = (Tape.init []).move Dir3.right) ∧
        out.cells = (Tape.init []).cells ∧ out.head = 1)
      (fun inp work out =>
        inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧
        (work 0).cells = (fun k => if k = 0 then Γ.start else if k = 1 then Γ.blank
          else (((x.map Γ.ofBool))[k - 2]?).getD Γ.blank) ∧ (work 0).head = 1 ∧
        (work 1).HoldsExact [] ∧ (work 1).head = 1 ∧
        (work 2).HoldsExact [] ∧ (work 2).head = 1 ∧
        (work 3).HoldsExact (takeField (groupPairs α)).1 ∧ (work 3).head = 1 ∧
        (work 4).HoldsExact (groupPairs α) ∧ (work 4).head = 1 ∧
        (work 5).HoldsExact [] ∧ (work 5).head = 1 ∧
        out.cells = (Tape.init []).cells ∧ out.head = 1)
      (4 * (pair α x).length + 4 * (groupPairs α).length + 24) := by
  intro inp work out ⟨hic, hih, hwork, hoc, hoh⟩
  have hwf := Tape.StartInvariant.init_ofBool (pair α x)
  have hblank1 : (Tape.init []).cells 1 = Γ.blank := Tape.init_nil_cells_succ 0
  -- ── step 1: an idle step — every head already sits at cell 1 ──
  obtain ⟨c₁, hs₁, hst₁, hin₁, hw₁, hout₁⟩ :=
    step_start_started
      (c := { state := initTM.qstart, input := inp, work := work, output := out })
      rfl
      (by show inp.read ≠ Γ.start
          rw [Tape.read, hih, hic]
          exact hwf.2 1 le_rfl)
      (fun i => by
        show (work i).read ≠ Γ.start ∧ 1 ≤ (work i).head
        rw [hwork i]
        refine ⟨?_, le_rfl⟩
        show ((Tape.init []).move Dir3.right).cells 1 ≠ Γ.start
        rw [Tape.move_cells, hblank1]
        simp)
      (by show out.read ≠ Γ.start
          rw [Tape.read, hoh, hoc, hblank1]
          simp)
      hoh.ge
  have hin₁' : c₁.input = inp := hin₁
  have hw₁' : c₁.work = work := hw₁
  have hout₁' : c₁.output = out := hout₁
  -- ── the bounced core ──
  obtain ⟨c', t, hle, hreach, hhalt, hpost⟩ :=
    initTM_hoareTime_core α x hst₁
      (by rw [hin₁']; exact hic) (by rw [hin₁']; exact hih)
      (fun i => by rw [hw₁', hwork i, Tape.move_cells])
      (fun i => by rw [hw₁', hwork i]; rfl)
      (by rw [hout₁']; exact hoc) (by rw [hout₁']; exact hoh)
  exact ⟨c', t + 1, by omega, .step hs₁ hreach, hhalt, hpost⟩

end TM

end Complexity
