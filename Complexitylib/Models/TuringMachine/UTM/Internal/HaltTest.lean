/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Hoare.Defs
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import Complexitylib.Models.TuringMachine.UTM.Internal.VTape
public import Complexitylib.Models.TuringMachine.UTM.Internal.Desc
public import Mathlib.Algebra.Order.Sub.Basic

/-!
# The UTM halt test machine

`haltTestTM : TM 6` compares the state tape (work tape 3) against the
description's second field (the `qhalt` field of the desc tape, work tape 4)
and writes the verdict to output cell 1: `Γ.one` on match, `Γ.zero` on
mismatch. Both tape heads are rewound to cell 1 before halting.

Phases (from `qstart = .skip`):

* **A (skip)** — move the desc head right past the first field and its
  separator (`□`), landing on the first cell of the `qhalt` field;
* **B (compare)** — lockstep compare of state head vs desc head: both `□`
  simultaneously ⇒ match; any difference ⇒ mismatch;
* **C (verdict)** — one step: write `Γ.one`/`Γ.zero` at output cell 1
  (output head stays at 1);
* **D (rewind)** — rewind the state head to cell 1, then the desc head to
  cell 1, then halt.

The machine writes `readBackWrite` on every work tape at every step, so no
work-tape cell is ever changed; tapes 3 and 4 are restored *exactly* (same
head, same cells), and all other tapes are untouched.

## Main results

- `TM.haltTestTM_hoareTime` — full HoareTime specification with ghost
  initial tapes, verdict `Γ.one` iff `stSyms = (takeField (takeField dSyms).2).1`,
  in time `2·|dSyms| + 2·|stSyms| + 12`.

`takeField` connection: the desc tape holds `dSyms` (`Tape.HoldsExact`);
cells beyond the content read `Γ.blank`, indistinguishable from an
in-content `Γw.blank` — and `takeField` semantics agrees, by design. The
`stSyms` blank-freeness hypothesis is required: a `□` inside `stSyms` would
truncate the machine's comparison at that point while `stSyms` as a list
extends beyond it (and `takeField` fields are always blank-free). The UTM
state tape holds bit symbols only, so this is no restriction in use.
-/


public section

namespace Complexity

-- ════════════════════════════════════════════════════════════════════════
-- takeField structural lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- The first field produced by `takeField` is blank-free. -/
theorem takeField_fst_ne_blank : ∀ (l : List Γw), ∀ s ∈ (takeField l).1, s ≠ Γw.blank
  | [] => by simp [takeField]
  | .blank :: _ => by simp [takeField]
  | .zero :: rest => by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · simp
    · exact takeField_fst_ne_blank rest s hs
  | .one :: rest => by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · simp
    · exact takeField_fst_ne_blank rest s hs

/-- `takeField` decomposition: either the input splits as
    `field ++ □ :: rest`, or it contains no separator and the field is the
    whole input. -/
theorem takeField_structure : ∀ (l : List Γw),
    l = (takeField l).1 ++ Γw.blank :: (takeField l).2 ∨
    ((takeField l).1 = l ∧ (takeField l).2 = [])
  | [] => Or.inr ⟨rfl, rfl⟩
  | .blank :: _ => Or.inl rfl
  | .zero :: rest => by
    rcases takeField_structure rest with h | ⟨h1, h2⟩
    · exact Or.inl (by simpa [takeField] using h)
    · exact Or.inr ⟨by simp [takeField, h1], by simpa [takeField] using h2⟩
  | .one :: rest => by
    rcases takeField_structure rest with h | ⟨h1, h2⟩
    · exact Or.inl (by simpa [takeField] using h)
    · exact Or.inr ⟨by simp [takeField, h1], by simpa [takeField] using h2⟩

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Γw.toΓ helper lemmas
-- ════════════════════════════════════════════════════════════════════════

private theorem toΓ_ne_blank {s : Γw} (h : s ≠ Γw.blank) : s.toΓ ≠ Γ.blank := by
  cases s <;> simp_all [Γw.toΓ]

private theorem toΓ_inj {a b : Γw} (h : a.toΓ = b.toΓ) : a = b := by
  cases a <;> cases b <;> simp_all [Γw.toΓ]

-- ════════════════════════════════════════════════════════════════════════
-- The machine
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `haltTestTM`. -/
inductive HaltTestPhase where
  | skip | compare | writeOne | writeZero | rewindSt | rewindD | done
  deriving DecidableEq

instance : Fintype HaltTestPhase where
  elems := {.skip, .compare, .writeOne, .writeZero, .rewindSt, .rewindD, .done}
  complete := fun x => by cases x <;> simp

/-- The UTM halt test: skip the first desc field, compare the state tape
    (work tape 3) with the second desc field (work tape 4), write the
    verdict to output cell 1, rewind both heads to cell 1, halt. -/
def haltTestTM : TM 6 where
  Q := HaltTestPhase
  qstart := .skip
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .skip =>
      ((if wHeads 4 = Γ.blank then HaltTestPhase.compare else .skip),
       fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead,
       fun i => if i = 4 then Dir3.right else idleDir (wHeads i),
       idleDir oHead)
    | .compare =>
      if wHeads 3 = Γ.blank ∧ wHeads 4 = Γ.blank then
        (HaltTestPhase.writeOne, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else if wHeads 3 = wHeads 4 then
        (HaltTestPhase.compare, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = 3 then Dir3.right else if i = 4 then Dir3.right
                  else idleDir (wHeads i),
         idleDir oHead)
      else
        (HaltTestPhase.writeZero, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .writeOne =>
      (HaltTestPhase.rewindSt, fun i => readBackWrite (wHeads i), Γw.one,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .writeZero =>
      (HaltTestPhase.rewindSt, fun i => readBackWrite (wHeads i), Γw.zero,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .rewindSt =>
      ((if wHeads 3 = Γ.start then HaltTestPhase.rewindD else .rewindSt),
       fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead,
       fun i => if i = 3 then (if wHeads 3 = Γ.start then Dir3.right else Dir3.left)
                else idleDir (wHeads i),
       idleDir oHead)
    | .rewindD =>
      ((if wHeads 4 = Γ.start then HaltTestPhase.done else .rewindD),
       fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead,
       fun i => if i = 4 then (if wHeads 4 = Γ.start then Dir3.right else Dir3.left)
                else idleDir (wHeads i),
       idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .skip =>
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi; dsimp only []; split
      · rfl
      · exact idleDir_right_of_start hwi
    | .compare =>
      dsimp only []; split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      · split
        · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
          intro i hwi; dsimp only []; split
          · rfl
          · split
            · rfl
            · exact idleDir_right_of_start hwi
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                 idleDir_right_of_start⟩
    | .writeOne =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .writeZero =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .rewindSt =>
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi; dsimp only []; split
      · rename_i heq; subst heq; rw [ite_eq_left hwi]
      · exact idleDir_right_of_start hwi
    | .rewindD =>
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi; dsimp only []; split
      · rename_i heq; subst heq; rw [ite_eq_left hwi]
      · exact idleDir_right_of_start hwi
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- Idle-tape helpers
-- ════════════════════════════════════════════════════════════════════════

/-- A tape whose head is not on `▷` is fixed by an idle step, regardless of
    head position. -/
private theorem tape_idle_fix (t : Tape) (hne : t.read ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read) = t := by
  rw [toΓ_readBackWrite_of_ne_start hne]
  show (t.write t.read).move (idleDir t.read) = t
  simp only [idleDir, hne, ↓reduceIte]
  show (t.write (t.cells t.head)).move .stay = t
  simp only [Tape.write, Tape.move]
  split
  · rfl
  · simp only [Function.update_eq_self]

/-- The input tape is fixed by an idle move when not reading `▷`. -/
private theorem input_idle_fix (t : Tape) (hne : t.read ≠ Γ.start) :
    t.move (idleDir t.read) = t := by
  simp only [idleDir, hne, ↓reduceIte, Tape.move]

/-- Two tapes with the same head and cells are equal. -/
private theorem tape_eq_of_parts {t t' : Tape} (hh : t.head = t'.head)
    (hc : t.cells = t'.cells) : t = t' := by
  cases t; cases t'; simp_all

-- ════════════════════════════════════════════════════════════════════════
-- HoldsExact + takeField: cell layout of the first two fields
-- ════════════════════════════════════════════════════════════════════════

private theorem getElem_append_cons_self {α : Type _} {l₁ l₂ : List α} {a : α}
    {h : l₁.length < (l₁ ++ a :: l₂).length} :
    (l₁ ++ a :: l₂)[l₁.length]'h = a := by
  rw [List.getElem_append_right (Nat.le_refl _)]
  simp

private theorem getElem_append_cons_right {α : Type _} {l₁ l₂ : List α} {a : α} {k : ℕ}
    (hk : k < l₂.length) {h : l₁.length + 1 + k < (l₁ ++ a :: l₂).length} :
    (l₁ ++ a :: l₂)[l₁.length + 1 + k]'h = l₂[k] := by
  rw [List.getElem_append_right (by omega)]
  simp only [show l₁.length + 1 + k - l₁.length = k + 1 by omega,
    List.getElem_cons_succ]

/-- The first two fields of `l` sit inside `l` in one of three shapes:
    both separators present, only the first separator present, or no
    separator at all. -/
private theorem two_fields_decomp (l : List Γw) :
    (∃ tail, l = (takeField l).1 ++ Γw.blank ::
      ((takeField (takeField l).2).1 ++ Γw.blank :: tail)) ∨
    l = (takeField l).1 ++ Γw.blank :: (takeField (takeField l).2).1 ∨
    ((takeField l).1 = l ∧ (takeField (takeField l).2).1 = []) := by
  rcases takeField_structure l with hdec | ⟨h1, h2⟩
  · rcases takeField_structure (takeField l).2 with hdec2 | ⟨h21, _⟩
    · exact Or.inl ⟨(takeField (takeField l).2).2, by rw [← hdec2]; exact hdec⟩
    · exact Or.inr (Or.inl (by rw [h21]; exact hdec))
  · exact Or.inr (Or.inr ⟨h1, by rw [h2]; rfl⟩)

/-- Cell layout of a tape holding `l`, in terms of its first two fields
    `f₁ = (takeField l).1` and `f₂ = (takeField (takeField l).2).1`:
    the first field occupies cells `1..|f₁|`, cell `|f₁|+1` is blank, the
    second field occupies cells `|f₁|+2..|f₁|+|f₂|+1`, the cell after it is
    blank, and the two field lengths together are bounded by `|l|`. -/
private theorem holdsExact_two_fields {t : Tape} {l : List Γw} (h : t.HoldsExact l) :
    (∀ k, (hk : k < (takeField l).1.length) →
      t.cells (1 + k) = (((takeField l).1)[k]).toΓ) ∧
    t.cells (1 + (takeField l).1.length) = Γ.blank ∧
    (∀ k, (hk : k < (takeField (takeField l).2).1.length) →
      t.cells ((takeField l).1.length + 2 + k)
        = (((takeField (takeField l).2).1)[k]).toΓ) ∧
    t.cells ((takeField l).1.length + 2 + (takeField (takeField l).2).1.length)
      = Γ.blank ∧
    (takeField l).1.length + (takeField (takeField l).2).1.length ≤ l.length := by
  rcases two_fields_decomp l with ⟨tail, hdec⟩ | hdec | ⟨h1, h2⟩
  · have hlen := congrArg List.length hdec
    simp only [List.length_append, List.length_cons] at hlen
    rw [hdec] at h
    refine ⟨fun k hk => ?_, ?_, fun k hk => ?_, ?_, by omega⟩
    · have h1 := Tape.HoldsExact.cells_lt h (i := k)
        (by simp only [List.length_append, List.length_cons]; omega)
      rw [List.getElem_append_left hk] at h1
      rw [Nat.add_comm]; exact h1
    · have h1 := Tape.HoldsExact.cells_lt h (i := (takeField l).1.length)
        (by simp only [List.length_append, List.length_cons]; omega)
      rw [getElem_append_cons_self] at h1
      rw [Nat.add_comm]; exact h1
    · have h1 := Tape.HoldsExact.cells_lt h (i := (takeField l).1.length + 1 + k)
        (by simp only [List.length_append, List.length_cons]; omega)
      have hk2 : k < ((takeField (takeField l).2).1 ++ Γw.blank :: tail).length := by
        simp only [List.length_append, List.length_cons]; omega
      rw [getElem_append_cons_right hk2, List.getElem_append_left hk] at h1
      rw [show (takeField l).1.length + 2 + k
        = (takeField l).1.length + 1 + k + 1 by omega]
      exact h1
    · have h1 := Tape.HoldsExact.cells_lt h
        (i := (takeField l).1.length + 1 + (takeField (takeField l).2).1.length)
        (by simp only [List.length_append, List.length_cons]; omega)
      have hk2 : (takeField (takeField l).2).1.length
          < ((takeField (takeField l).2).1 ++ Γw.blank :: tail).length := by
        simp only [List.length_append, List.length_cons]; omega
      rw [getElem_append_cons_right hk2, getElem_append_cons_self] at h1
      rw [show (takeField l).1.length + 2 + (takeField (takeField l).2).1.length
        = (takeField l).1.length + 1 + (takeField (takeField l).2).1.length + 1
        by omega]
      exact h1
  · have hlen := congrArg List.length hdec
    simp only [List.length_append, List.length_cons] at hlen
    rw [hdec] at h
    refine ⟨fun k hk => ?_, ?_, fun k hk => ?_, ?_, by omega⟩
    · have h1 := Tape.HoldsExact.cells_lt h (i := k)
        (by simp only [List.length_append, List.length_cons]; omega)
      rw [List.getElem_append_left hk] at h1
      rw [Nat.add_comm]; exact h1
    · have h1 := Tape.HoldsExact.cells_lt h (i := (takeField l).1.length)
        (by simp only [List.length_append, List.length_cons]; omega)
      rw [getElem_append_cons_self] at h1
      rw [Nat.add_comm]; exact h1
    · have h1 := Tape.HoldsExact.cells_lt h (i := (takeField l).1.length + 1 + k)
        (by simp only [List.length_append, List.length_cons]; omega)
      rw [getElem_append_cons_right hk] at h1
      rw [show (takeField l).1.length + 2 + k
        = (takeField l).1.length + 1 + k + 1 by omega]
      exact h1
    · have h1 := Tape.HoldsExact.cells_ge h
        (i := (takeField l).1.length + 1 + (takeField (takeField l).2).1.length)
        (by simp only [List.length_append, List.length_cons]; omega)
      rw [show (takeField l).1.length + 2 + (takeField (takeField l).2).1.length
        = (takeField l).1.length + 1 + (takeField (takeField l).2).1.length + 1
        by omega]
      exact h1
  · have hlenF : (takeField l).1.length = l.length := by rw [h1]
    have hF2 : (takeField (takeField l).2).1.length = 0 := by rw [h2]; rfl
    refine ⟨fun k hk => ?_, ?_, fun k hk => by omega, ?_, by omega⟩
    · rw [Nat.add_comm, List.getElem_of_eq h1 hk]
      exact Tape.HoldsExact.cells_lt h (i := k) (by omega)
    · rw [Nat.add_comm]
      exact Tape.HoldsExact.cells_ge h (i := (takeField l).1.length) (by omega)
    · rw [show (takeField l).1.length + 2 + (takeField (takeField l).2).1.length
        = (takeField l).1.length + 1 + (takeField (takeField l).2).1.length + 1
        by omega]
      exact Tape.HoldsExact.cells_ge h
        (i := (takeField l).1.length + 1 + (takeField (takeField l).2).1.length)
        (by omega)

-- ════════════════════════════════════════════════════════════════════════
-- Phase A: skip past the first desc field
-- ════════════════════════════════════════════════════════════════════════

/-- From `.skip` with the desc head at cell `1 + k` inside (or just past)
    the first field `f`, reach `.compare` with the desc head at cell
    `|f| + 2` in `(|f| - k) + 1` steps. Everything except the desc head is
    unchanged. -/
private theorem skip_loop (f : List Γw) (hf : ∀ s ∈ f, s ≠ Γw.blank) :
    ∀ (m k : ℕ) (c : Cfg 6 haltTestTM.Q),
    m + k = f.length →
    c.state = HaltTestPhase.skip →
    (c.work 4).head = 1 + k →
    (∀ j, (hj : j < f.length) → (c.work 4).cells (1 + j) = (f[j]).toΓ) →
    (c.work 4).cells (1 + f.length) = Γ.blank →
    c.input.read ≠ Γ.start →
    c.output.read ≠ Γ.start →
    (∀ i : Fin 6, i ≠ 4 → (c.work i).read ≠ Γ.start) →
    ∃ c', haltTestTM.reachesIn (m + 1) c c' ∧
      c'.state = HaltTestPhase.compare ∧
      c'.input = c.input ∧
      (∀ i : Fin 6, i ≠ 4 → c'.work i = c.work i) ∧
      c'.output = c.output ∧
      (c'.work 4).cells = (c.work 4).cells ∧
      (c'.work 4).head = f.length + 2 := by
  intro m
  induction m with
  | zero =>
    intro k c hmk hstate hhead hcells hblank hin hout hothers
    have hk : k = f.length := by omega
    subst hk
    have hread : (c.work 4).read = Γ.blank := by
      rw [Tape.read, hhead]; exact hblank
    have hread_ns : (c.work 4).read ≠ Γ.start := by rw [hread]; simp
    have hstep : ∃ c₁, haltTestTM.step c = some c₁ ∧
        c₁.state = HaltTestPhase.compare ∧
        c₁.input = c.input ∧
        (∀ i : Fin 6, i ≠ 4 → c₁.work i = c.work i) ∧
        c₁.output = c.output ∧
        (c₁.work 4).cells = (c.work 4).cells ∧
        (c₁.work 4).head = (c.work 4).head + 1 := by
      simp only [TM.step, ↓reduceIte, hstate, haltTestTM, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · exact input_idle_fix c.input hin
      · intro i hne; dsimp only []
        rw [ite_eq_right hne]
        exact tape_idle_fix _ (hothers i hne)
      · exact tape_idle_fix c.output hout
      · dsimp only []
        rw [ite_eq_left rfl]
        exact tape_readBackWrite_preserves _ _ (Or.inr hread_ns)
      · dsimp only []
        rw [ite_eq_left rfl]
        simp [Tape.writeAndMove, Tape.move, Tape.write_head]
    obtain ⟨c₁, hstep', hst₁, hin₁, hw₁, hout₁, hcells₁, hhead₁⟩ := hstep
    exact ⟨c₁, .step hstep' .zero, hst₁, hin₁, hw₁, hout₁, hcells₁,
      by rw [hhead₁, hhead]; omega⟩
  | succ m ih =>
    intro k c hmk hstate hhead hcells hblank hin hout hothers
    have hk : k < f.length := by omega
    have hread : (c.work 4).read = (f[k]).toΓ := by
      rw [Tape.read, hhead]; exact hcells k hk
    have hread_nb : (c.work 4).read ≠ Γ.blank := by
      rw [hread]; exact toΓ_ne_blank (hf _ (f.getElem_mem hk))
    have hread_ns : (c.work 4).read ≠ Γ.start := by
      rw [hread]
      exact Γw.toΓ_ne_start _
    have hstep : ∃ c₁, haltTestTM.step c = some c₁ ∧
        c₁.state = HaltTestPhase.skip ∧
        c₁.input = c.input ∧
        (∀ i : Fin 6, i ≠ 4 → c₁.work i = c.work i) ∧
        c₁.output = c.output ∧
        (c₁.work 4).cells = (c.work 4).cells ∧
        (c₁.work 4).head = (c.work 4).head + 1 := by
      simp only [TM.step, ↓reduceIte, hstate, haltTestTM, hread_nb]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · exact input_idle_fix c.input hin
      · intro i hne; dsimp only []
        rw [ite_eq_right hne]
        exact tape_idle_fix _ (hothers i hne)
      · exact tape_idle_fix c.output hout
      · dsimp only []
        rw [ite_eq_left rfl]
        exact tape_readBackWrite_preserves _ _ (Or.inr hread_ns)
      · dsimp only []
        rw [ite_eq_left rfl]
        simp [Tape.writeAndMove, Tape.move, Tape.write_head]
    obtain ⟨c₁, hstep', hst₁, hin₁, hw₁, hout₁, hcells₁, hhead₁⟩ := hstep
    obtain ⟨c', hreach, hst', hin', hw', hout', hcells', hhead'⟩ :=
      ih (k + 1) c₁ (by omega) hst₁
        (by rw [hhead₁, hhead]; omega)
        (by intro j hj; rw [hcells₁]; exact hcells j hj)
        (by rw [hcells₁]; exact hblank)
        (by rw [hin₁]; exact hin)
        (by rw [hout₁]; exact hout)
        (by intro i hne; rw [hw₁ i hne]; exact hothers i hne)
    exact ⟨c', .step hstep' hreach, hst',
      by rw [hin', hin₁],
      fun i hne => by rw [hw' i hne, hw₁ i hne],
      by rw [hout', hout₁],
      by rw [hcells', hcells₁],
      hhead'⟩

-- ════════════════════════════════════════════════════════════════════════
-- Phase B: lockstep compare of state tape vs desc field
-- ════════════════════════════════════════════════════════════════════════

/-- Match detection: both heads read `□` — one step to `.writeOne`, all
    tapes unchanged. -/
private theorem compare_match_step (c : Cfg 6 haltTestTM.Q)
    (hstate : c.state = HaltTestPhase.compare)
    (h3 : (c.work 3).read = Γ.blank)
    (h4 : (c.work 4).read = Γ.blank)
    (hin : c.input.read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start)
    (hoth : ∀ i : Fin 6, i ≠ 3 → i ≠ 4 → (c.work i).read ≠ Γ.start) :
    ∃ c₁, haltTestTM.step c = some c₁ ∧
      c₁.state = HaltTestPhase.writeOne ∧
      c₁.input = c.input ∧ (∀ i : Fin 6, c₁.work i = c.work i) ∧
      c₁.output = c.output := by
  simp only [TM.step, ↓reduceIte, hstate, haltTestTM, h3, h4, and_self]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · exact input_idle_fix c.input hin
  · intro i
    dsimp only []
    by_cases h3i : i = 3
    · subst h3i; exact tape_idle_fix _ (by rw [h3]; simp)
    · by_cases h4i : i = 4
      · subst h4i; exact tape_idle_fix _ (by rw [h4]; simp)
      · exact tape_idle_fix _ (hoth i h3i h4i)
  · exact tape_idle_fix c.output hout

/-- Mismatch detection: the two reads differ — one step to `.writeZero`,
    all tapes unchanged. -/
private theorem compare_mismatch_step (c : Cfg 6 haltTestTM.Q)
    (hstate : c.state = HaltTestPhase.compare)
    (hneq : (c.work 3).read ≠ (c.work 4).read)
    (h3 : (c.work 3).read ≠ Γ.start)
    (h4 : (c.work 4).read ≠ Γ.start)
    (hin : c.input.read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start)
    (hoth : ∀ i : Fin 6, i ≠ 3 → i ≠ 4 → (c.work i).read ≠ Γ.start) :
    ∃ c₁, haltTestTM.step c = some c₁ ∧
      c₁.state = HaltTestPhase.writeZero ∧
      c₁.input = c.input ∧ (∀ i : Fin 6, c₁.work i = c.work i) ∧
      c₁.output = c.output := by
  have hc1 : ¬((c.work 3).read = Γ.blank ∧ (c.work 4).read = Γ.blank) :=
    fun ⟨a, b⟩ => hneq (a.trans b.symm)
  simp only [TM.step, ↓reduceIte, hstate, haltTestTM, hc1, hneq]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · exact input_idle_fix c.input hin
  · intro i
    dsimp only []
    by_cases h3i : i = 3
    · subst h3i; exact tape_idle_fix _ h3
    · by_cases h4i : i = 4
      · subst h4i; exact tape_idle_fix _ h4
      · exact tape_idle_fix _ (hoth i h3i h4i)
  · exact tape_idle_fix c.output hout

/-- Lockstep advance: equal non-blank reads — one step staying in
    `.compare`, both heads move right, all cells and other tapes
    unchanged. -/
private theorem compare_advance_step (c : Cfg 6 haltTestTM.Q)
    (hstate : c.state = HaltTestPhase.compare)
    (heq : (c.work 3).read = (c.work 4).read)
    (h3nb : (c.work 3).read ≠ Γ.blank)
    (h3 : (c.work 3).read ≠ Γ.start)
    (h4 : (c.work 4).read ≠ Γ.start)
    (hin : c.input.read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start)
    (hoth : ∀ i : Fin 6, i ≠ 3 → i ≠ 4 → (c.work i).read ≠ Γ.start) :
    ∃ c₁, haltTestTM.step c = some c₁ ∧
      c₁.state = HaltTestPhase.compare ∧
      c₁.input = c.input ∧
      (∀ i : Fin 6, i ≠ 3 → i ≠ 4 → c₁.work i = c.work i) ∧
      c₁.output = c.output ∧
      (c₁.work 3).cells = (c.work 3).cells ∧
      (c₁.work 4).cells = (c.work 4).cells ∧
      (c₁.work 3).head = (c.work 3).head + 1 ∧
      (c₁.work 4).head = (c.work 4).head + 1 := by
  have hc1 : ¬((c.work 3).read = Γ.blank ∧ (c.work 4).read = Γ.blank) :=
    fun ⟨a, _⟩ => h3nb a
  have hc2 : ((c.work 3).read = (c.work 4).read) = True := by simp [heq]
  simp only [TM.step, ↓reduceIte, hstate, haltTestTM, hc1, hc2]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact input_idle_fix c.input hin
  · intro i h3i h4i
    dsimp only []
    rw [ite_eq_right h3i, ite_eq_right h4i]
    exact tape_idle_fix _ (hoth i h3i h4i)
  · exact tape_idle_fix c.output hout
  · dsimp only []
    rw [ite_eq_left rfl]
    exact tape_readBackWrite_preserves _ _ (Or.inr h3)
  · dsimp only []
    rw [ite_eq_right (by decide : (4 : Fin 6) ≠ 3), ite_eq_left rfl]
    exact tape_readBackWrite_preserves _ _ (Or.inr h4)
  · dsimp only []
    rw [ite_eq_left rfl]
    simp [Tape.writeAndMove, Tape.move, Tape.write_head]
  · dsimp only []
    rw [ite_eq_right (by decide : (4 : Fin 6) ≠ 3), ite_eq_left rfl]
    simp [Tape.writeAndMove, Tape.move, Tape.write_head]

/-- The lockstep compare loop: with blank-free `A` under the state head
    (blank after) and blank-free `B` under the desc head (blank after), the
    machine reaches the verdict state for `A = B` within `|A| + 1` steps,
    leaving all cells and all other tapes unchanged; both heads end between
    their start and start + field length. -/
private theorem compare_loop :
    ∀ (A : List Γw), (∀ s ∈ A, s ≠ Γw.blank) →
    ∀ (B : List Γw), (∀ s ∈ B, s ≠ Γw.blank) →
    ∀ (c : Cfg 6 haltTestTM.Q) (p q : ℕ),
    c.state = HaltTestPhase.compare →
    (c.work 3).head = p →
    (c.work 4).head = q →
    (∀ j, (hj : j < A.length) → (c.work 3).cells (p + j) = (A[j]).toΓ) →
    (c.work 3).cells (p + A.length) = Γ.blank →
    (∀ j, (hj : j < B.length) → (c.work 4).cells (q + j) = (B[j]).toΓ) →
    (c.work 4).cells (q + B.length) = Γ.blank →
    c.input.read ≠ Γ.start →
    c.output.read ≠ Γ.start →
    (∀ i : Fin 6, i ≠ 3 → i ≠ 4 → (c.work i).read ≠ Γ.start) →
    ∃ c' t, t ≤ A.length + 1 ∧ haltTestTM.reachesIn t c c' ∧
      c'.state = (if A = B then HaltTestPhase.writeOne else HaltTestPhase.writeZero) ∧
      c'.input = c.input ∧
      (∀ i : Fin 6, i ≠ 3 → i ≠ 4 → c'.work i = c.work i) ∧
      c'.output = c.output ∧
      (c'.work 3).cells = (c.work 3).cells ∧
      (c'.work 4).cells = (c.work 4).cells ∧
      p ≤ (c'.work 3).head ∧ (c'.work 3).head ≤ p + A.length ∧
      q ≤ (c'.work 4).head ∧ (c'.work 4).head ≤ q + B.length := by
  intro A
  induction A with
  | nil =>
    intro _ B hB c p q hstate hh3 hh4 hc3 hb3 hc4 hb4 hin hout hoth
    have hr3 : (c.work 3).read = Γ.blank := by
      rw [Tape.read, hh3]; simpa using hb3
    cases B with
    | nil =>
      have hr4 : (c.work 4).read = Γ.blank := by
        rw [Tape.read, hh4]; simpa using hb4
      obtain ⟨c₁, hstep', hst₁, hin₁, hw₁, hout₁⟩ :=
        compare_match_step c hstate hr3 hr4 hin hout hoth
      refine ⟨c₁, 1, by omega, .step hstep' .zero, by simpa using hst₁,
        hin₁, fun i h3i h4i => hw₁ i, hout₁,
        by rw [hw₁ 3], by rw [hw₁ 4], ?_, ?_, ?_, ?_⟩ <;>
          rw [hw₁] <;> omega
    | cons b B' =>
      have hr4 : (c.work 4).read = (b).toΓ := by
        rw [Tape.read, hh4]; exact hc4 0 (by simp)
      have hneq : (c.work 3).read ≠ (c.work 4).read := by
        rw [hr3, hr4]
        exact fun h => toΓ_ne_blank (hB b (by simp)) h.symm
      obtain ⟨c₁, hstep', hst₁, hin₁, hw₁, hout₁⟩ :=
        compare_mismatch_step c hstate hneq (by rw [hr3]; simp)
          (by rw [hr4]; exact Γw.toΓ_ne_start b) hin hout hoth
      refine ⟨c₁, 1, by omega, .step hstep' .zero, by simpa using hst₁,
        hin₁, fun i h3i h4i => hw₁ i, hout₁,
        by rw [hw₁ 3], by rw [hw₁ 4], ?_, ?_, ?_, ?_⟩ <;>
          rw [hw₁] <;> omega
  | cons a A' ihA =>
    intro hA B hB c p q hstate hh3 hh4 hc3 hb3 hc4 hb4 hin hout hoth
    have hr3 : (c.work 3).read = a.toΓ := by
      rw [Tape.read, hh3]; exact hc3 0 (by simp)
    have hr3nb : (c.work 3).read ≠ Γ.blank := by
      rw [hr3]; exact toΓ_ne_blank (hA a (by simp))
    have hr3ns : (c.work 3).read ≠ Γ.start := by
      rw [hr3]
      exact Γw.toΓ_ne_start a
    cases B with
    | nil =>
      have hr4 : (c.work 4).read = Γ.blank := by
        rw [Tape.read, hh4]; simpa using hb4
      have hneq : (c.work 3).read ≠ (c.work 4).read := by
        rw [hr3, hr4]
        exact toΓ_ne_blank (hA a (by simp))
      obtain ⟨c₁, hstep', hst₁, hin₁, hw₁, hout₁⟩ :=
        compare_mismatch_step c hstate hneq hr3ns (by rw [hr4]; simp) hin hout hoth
      refine ⟨c₁, 1, by omega, .step hstep' .zero, by simpa using hst₁,
        hin₁, fun i h3i h4i => hw₁ i, hout₁,
        by rw [hw₁ 3], by rw [hw₁ 4], ?_, ?_, ?_, ?_⟩ <;>
          rw [hw₁] <;> omega
    | cons b B' =>
      have hr4 : (c.work 4).read = b.toΓ := by
        rw [Tape.read, hh4]; exact hc4 0 (by simp)
      by_cases hab : a = b
      · subst hab
        have heq : (c.work 3).read = (c.work 4).read := by rw [hr3, hr4]
        obtain ⟨c₁, hstep', hst₁, hin₁, hw₁, hout₁, hcl3, hcl4, hhd3, hhd4⟩ :=
          compare_advance_step c hstate heq hr3nb hr3ns
            (by rw [hr4]; exact Γw.toΓ_ne_start a) hin hout hoth
        obtain ⟨c', t', ht', hreach, hst', hin', hw', hout', hcl3', hcl4',
            hlo3, hhi3, hlo4, hhi4⟩ :=
          ihA (fun s hs => hA s (by simp [hs]))
            B' (fun s hs => hB s (by simp [hs]))
            c₁ (p + 1) (q + 1) hst₁
            (by rw [hhd3, hh3]) (by rw [hhd4, hh4])
            (by
              intro j hj
              rw [hcl3, show p + 1 + j = p + (j + 1) by omega]
              exact hc3 (j + 1) (by simpa using Nat.succ_lt_succ hj))
            (by
              rw [hcl3, show p + 1 + A'.length = p + (a :: A').length by
                simp only [List.length_cons]; omega]
              exact hb3)
            (by
              intro j hj
              rw [hcl4, show q + 1 + j = q + (j + 1) by omega]
              exact hc4 (j + 1) (by simpa using Nat.succ_lt_succ hj))
            (by
              rw [hcl4, show q + 1 + B'.length = q + (a :: B').length by
                simp only [List.length_cons]; omega]
              exact hb4)
            (by rw [hin₁]; exact hin)
            (by rw [hout₁]; exact hout)
            (by intro i h3i h4i; rw [hw₁ i h3i h4i]; exact hoth i h3i h4i)
        refine ⟨c', t' + 1, by simp; omega, .step hstep' hreach, ?_,
          by rw [hin', hin₁],
          fun i h3i h4i => by rw [hw' i h3i h4i, hw₁ i h3i h4i],
          by rw [hout', hout₁],
          by rw [hcl3', hcl3], by rw [hcl4', hcl4],
          by omega, by simp; omega, by omega, by simp; omega⟩
        · rw [hst']
          exact if_congr (by simp) rfl rfl
      · have hneq : (c.work 3).read ≠ (c.work 4).read := by
          rw [hr3, hr4]
          exact fun h => hab (toΓ_inj h)
        obtain ⟨c₁, hstep', hst₁, hin₁, hw₁, hout₁⟩ :=
          compare_mismatch_step c hstate hneq hr3ns
            (by rw [hr4]; exact Γw.toΓ_ne_start b) hin hout hoth
        refine ⟨c₁, 1, by simp, .step hstep' .zero, ?_,
          hin₁, fun i h3i h4i => hw₁ i, hout₁,
          by rw [hw₁ 3], by rw [hw₁ 4], ?_, ?_, ?_, ?_⟩
        · rw [hst₁, ite_eq_right (by simp [hab])]
        all_goals (rw [hw₁]; omega)

-- ════════════════════════════════════════════════════════════════════════
-- Phase C: write the verdict at output cell 1
-- ════════════════════════════════════════════════════════════════════════

/-- The verdict step: from `.writeOne`/`.writeZero` (selected by `P`) with
    the output head at cell 1, one step writes the verdict symbol at output
    cell 1 and enters `.rewindSt`; the output head stays at 1 and every
    other tape is unchanged. -/
private theorem verdict_step (P : Prop) [Decidable P] (c : Cfg 6 haltTestTM.Q)
    (hstate : c.state
      = (if P then HaltTestPhase.writeOne else HaltTestPhase.writeZero))
    (hoh : c.output.head = 1)
    (hout : c.output.read ≠ Γ.start)
    (hin : c.input.read ≠ Γ.start)
    (h3 : (c.work 3).read ≠ Γ.start)
    (h4 : (c.work 4).read ≠ Γ.start)
    (hoth : ∀ i : Fin 6, i ≠ 3 → i ≠ 4 → (c.work i).read ≠ Γ.start) :
    ∃ c₁, haltTestTM.step c = some c₁ ∧
      c₁.state = HaltTestPhase.rewindSt ∧
      c₁.input = c.input ∧ (∀ i : Fin 6, c₁.work i = c.work i) ∧
      c₁.output.cells = Function.update c.output.cells 1
        (if P then Γ.one else Γ.zero) ∧
      c₁.output.head = 1 := by
  have hstay : idleDir c.output.read = Dir3.stay := by simp [idleDir, hout]
  by_cases hP : P
  · rw [ite_eq_left hP] at hstate
    simp only [TM.step, hstate, haltTestTM]
    refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · exact input_idle_fix c.input hin
    · intro i
      dsimp only []
      by_cases h3i : i = 3
      · subst h3i; exact tape_idle_fix _ h3
      · by_cases h4i : i = 4
        · subst h4i; exact tape_idle_fix _ h4
        · exact tape_idle_fix _ (hoth i h3i h4i)
    · rw [ite_eq_left hP]
      show ((c.output.write (Γw.one).toΓ).move (idleDir c.output.read)).cells = _
      rw [Tape.move_cells]
      simp only [Tape.write, hoh, Γw.toΓ]
      rw [ite_eq_right Nat.one_ne_zero]
    · show ((c.output.write (Γw.one).toΓ).move (idleDir c.output.read)).head = 1
      rw [hstay]
      simp [Tape.move, Tape.write_head, hoh]
  · rw [ite_eq_right hP] at hstate
    simp only [TM.step, hstate, haltTestTM]
    refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · exact input_idle_fix c.input hin
    · intro i
      dsimp only []
      by_cases h3i : i = 3
      · subst h3i; exact tape_idle_fix _ h3
      · by_cases h4i : i = 4
        · subst h4i; exact tape_idle_fix _ h4
        · exact tape_idle_fix _ (hoth i h3i h4i)
    · rw [ite_eq_right hP]
      show ((c.output.write (Γw.zero).toΓ).move (idleDir c.output.read)).cells = _
      rw [Tape.move_cells]
      simp only [Tape.write, hoh, Γw.toΓ]
      rw [ite_eq_right Nat.one_ne_zero]
    · show ((c.output.write (Γw.zero).toΓ).move (idleDir c.output.read)).head = 1
      rw [hstay]
      simp [Tape.move, Tape.write_head, hoh]

-- ════════════════════════════════════════════════════════════════════════
-- Phase D: rewind the state head, then the desc head
-- ════════════════════════════════════════════════════════════════════════

/-- Rewind the state head: from `.rewindSt` with the state head at `m`,
    reach `.rewindD` with the state head at cell 1 in `m + 1` steps.
    Everything except the state head is unchanged. -/
private theorem rewindSt_loop :
    ∀ (m : ℕ) (c : Cfg 6 haltTestTM.Q),
    c.state = HaltTestPhase.rewindSt →
    (c.work 3).head = m →
    (c.work 3).cells 0 = Γ.start →
    (∀ j, 1 ≤ j → (c.work 3).cells j ≠ Γ.start) →
    c.input.read ≠ Γ.start →
    c.output.read ≠ Γ.start →
    (c.work 4).read ≠ Γ.start →
    (∀ i : Fin 6, i ≠ 3 → i ≠ 4 → (c.work i).read ≠ Γ.start) →
    ∃ c', haltTestTM.reachesIn (m + 1) c c' ∧
      c'.state = HaltTestPhase.rewindD ∧
      c'.input = c.input ∧
      (∀ i : Fin 6, i ≠ 3 → c'.work i = c.work i) ∧
      c'.output = c.output ∧
      (c'.work 3).cells = (c.work 3).cells ∧
      (c'.work 3).head = 1 := by
  intro m
  induction m with
  | zero =>
    intro c hstate hhead hc0 hns hin hout h4 hoth
    have hread : (c.work 3).read = Γ.start := by rw [Tape.read, hhead]; exact hc0
    have hstep : ∃ c₁, haltTestTM.step c = some c₁ ∧
        c₁.state = HaltTestPhase.rewindD ∧
        c₁.input = c.input ∧ (∀ i : Fin 6, i ≠ 3 → c₁.work i = c.work i) ∧
        c₁.output = c.output ∧ (c₁.work 3).cells = (c.work 3).cells ∧
        (c₁.work 3).head = 1 := by
      simp only [TM.step, ↓reduceIte, hstate, haltTestTM, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · exact input_idle_fix c.input hin
      · intro i hne; dsimp only []
        rw [ite_eq_right hne]
        by_cases h4i : i = 4
        · subst h4i; exact tape_idle_fix _ h4
        · exact tape_idle_fix _ (hoth i hne h4i)
      · exact tape_idle_fix c.output hout
      · dsimp only []
        rw [ite_eq_left rfl]
        exact tape_readBackWrite_preserves _ _ (Or.inl hhead)
      · dsimp only []
        rw [ite_eq_left rfl]
        simp [Tape.writeAndMove, Tape.move, Tape.write_head, hhead]
    obtain ⟨c₁, hstep', hst₁, hin₁, hw₁, hout₁, hcells₁, hhead₁⟩ := hstep
    exact ⟨c₁, .step hstep' .zero, hst₁, hin₁, hw₁, hout₁, hcells₁, hhead₁⟩
  | succ m ih =>
    intro c hstate hhead hc0 hns hin hout h4 hoth
    have hread : (c.work 3).read ≠ Γ.start := by
      rw [Tape.read, hhead]; exact hns (m + 1) (by omega)
    have hstep : ∃ c₁, haltTestTM.step c = some c₁ ∧
        c₁.state = HaltTestPhase.rewindSt ∧
        c₁.input = c.input ∧ (∀ i : Fin 6, i ≠ 3 → c₁.work i = c.work i) ∧
        c₁.output = c.output ∧ (c₁.work 3).cells = (c.work 3).cells ∧
        (c₁.work 3).head = m := by
      simp only [TM.step, ↓reduceIte, hstate, haltTestTM, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · exact input_idle_fix c.input hin
      · intro i hne; dsimp only []
        rw [ite_eq_right hne]
        by_cases h4i : i = 4
        · subst h4i; exact tape_idle_fix _ h4
        · exact tape_idle_fix _ (hoth i hne h4i)
      · exact tape_idle_fix c.output hout
      · dsimp only []
        rw [ite_eq_left rfl]
        exact tape_readBackWrite_preserves _ _ (Or.inr hread)
      · dsimp only []
        rw [ite_eq_left rfl]
        simp [Tape.writeAndMove, Tape.move, Tape.write_head, hhead]
    obtain ⟨c₁, hstep', hst₁, hin₁, hw₁, hout₁, hcells₁, hhead₁⟩ := hstep
    obtain ⟨c', hreach, hst', hin', hw', hout', hcells', hhead'⟩ :=
      ih c₁ hst₁ hhead₁
        (by rw [hcells₁]; exact hc0)
        (by intro j hj; rw [hcells₁]; exact hns j hj)
        (by rw [hin₁]; exact hin)
        (by rw [hout₁]; exact hout)
        (by rw [hw₁ 4 (by decide)]; exact h4)
        (by intro i h3i h4i; rw [hw₁ i h3i]; exact hoth i h3i h4i)
    exact ⟨c', .step hstep' hreach, hst',
      by rw [hin', hin₁],
      fun i hne => by rw [hw' i hne, hw₁ i hne],
      by rw [hout', hout₁],
      by rw [hcells', hcells₁],
      hhead'⟩

/-- Rewind the desc head: from `.rewindD` with the desc head at `m`, halt
    with the desc head at cell 1 in `m + 1` steps. Everything except the
    desc head is unchanged. -/
private theorem rewindD_loop :
    ∀ (m : ℕ) (c : Cfg 6 haltTestTM.Q),
    c.state = HaltTestPhase.rewindD →
    (c.work 4).head = m →
    (c.work 4).cells 0 = Γ.start →
    (∀ j, 1 ≤ j → (c.work 4).cells j ≠ Γ.start) →
    c.input.read ≠ Γ.start →
    c.output.read ≠ Γ.start →
    (c.work 3).read ≠ Γ.start →
    (∀ i : Fin 6, i ≠ 3 → i ≠ 4 → (c.work i).read ≠ Γ.start) →
    ∃ c', haltTestTM.reachesIn (m + 1) c c' ∧
      c'.state = HaltTestPhase.done ∧
      c'.input = c.input ∧
      (∀ i : Fin 6, i ≠ 4 → c'.work i = c.work i) ∧
      c'.output = c.output ∧
      (c'.work 4).cells = (c.work 4).cells ∧
      (c'.work 4).head = 1 := by
  intro m
  induction m with
  | zero =>
    intro c hstate hhead hc0 hns hin hout h3 hoth
    have hread : (c.work 4).read = Γ.start := by rw [Tape.read, hhead]; exact hc0
    have hstep : ∃ c₁, haltTestTM.step c = some c₁ ∧
        c₁.state = HaltTestPhase.done ∧
        c₁.input = c.input ∧ (∀ i : Fin 6, i ≠ 4 → c₁.work i = c.work i) ∧
        c₁.output = c.output ∧ (c₁.work 4).cells = (c.work 4).cells ∧
        (c₁.work 4).head = 1 := by
      simp only [TM.step, ↓reduceIte, hstate, haltTestTM, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · exact input_idle_fix c.input hin
      · intro i hne; dsimp only []
        rw [ite_eq_right hne]
        by_cases h3i : i = 3
        · subst h3i; exact tape_idle_fix _ h3
        · exact tape_idle_fix _ (hoth i h3i hne)
      · exact tape_idle_fix c.output hout
      · dsimp only []
        rw [ite_eq_left rfl]
        exact tape_readBackWrite_preserves _ _ (Or.inl hhead)
      · dsimp only []
        rw [ite_eq_left rfl]
        simp [Tape.writeAndMove, Tape.move, Tape.write_head, hhead]
    obtain ⟨c₁, hstep', hst₁, hin₁, hw₁, hout₁, hcells₁, hhead₁⟩ := hstep
    exact ⟨c₁, .step hstep' .zero, hst₁, hin₁, hw₁, hout₁, hcells₁, hhead₁⟩
  | succ m ih =>
    intro c hstate hhead hc0 hns hin hout h3 hoth
    have hread : (c.work 4).read ≠ Γ.start := by
      rw [Tape.read, hhead]; exact hns (m + 1) (by omega)
    have hstep : ∃ c₁, haltTestTM.step c = some c₁ ∧
        c₁.state = HaltTestPhase.rewindD ∧
        c₁.input = c.input ∧ (∀ i : Fin 6, i ≠ 4 → c₁.work i = c.work i) ∧
        c₁.output = c.output ∧ (c₁.work 4).cells = (c.work 4).cells ∧
        (c₁.work 4).head = m := by
      simp only [TM.step, ↓reduceIte, hstate, haltTestTM, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · exact input_idle_fix c.input hin
      · intro i hne; dsimp only []
        rw [ite_eq_right hne]
        by_cases h3i : i = 3
        · subst h3i; exact tape_idle_fix _ h3
        · exact tape_idle_fix _ (hoth i h3i hne)
      · exact tape_idle_fix c.output hout
      · dsimp only []
        rw [ite_eq_left rfl]
        exact tape_readBackWrite_preserves _ _ (Or.inr hread)
      · dsimp only []
        rw [ite_eq_left rfl]
        simp [Tape.writeAndMove, Tape.move, Tape.write_head, hhead]
    obtain ⟨c₁, hstep', hst₁, hin₁, hw₁, hout₁, hcells₁, hhead₁⟩ := hstep
    obtain ⟨c', hreach, hst', hin', hw', hout', hcells', hhead'⟩ :=
      ih c₁ hst₁ hhead₁
        (by rw [hcells₁]; exact hc0)
        (by intro j hj; rw [hcells₁]; exact hns j hj)
        (by rw [hin₁]; exact hin)
        (by rw [hout₁]; exact hout)
        (by rw [hw₁ 3 (by decide)]; exact h3)
        (by intro i h3i h4i; rw [hw₁ i h4i]; exact hoth i h3i h4i)
    exact ⟨c', .step hstep' hreach, hst',
      by rw [hin', hin₁],
      fun i hne => by rw [hw' i hne, hw₁ i hne],
      by rw [hout', hout₁],
      by rw [hcells', hcells₁],
      hhead'⟩

-- ════════════════════════════════════════════════════════════════════════
-- Main theorem
-- ════════════════════════════════════════════════════════════════════════

/-- **Halt test specification** (ghost-initial-tape style). Starting from
    `qstart` where the state tape (work tape 3) holds the blank-free string
    `stSyms` and the desc tape (work tape 4) holds `dSyms` (both heads at
    cell 1), with the output head resting at cell 1, `haltTestTM` halts
    within `2·|dSyms| + 2·|stSyms| + 12` steps having

    * written the verdict at output cell 1: `Γ.one` iff `stSyms` equals the
      *second field* of `dSyms` (the qhalt field, `(takeField (takeField
      dSyms).2).1`), `Γ.zero` otherwise;
    * restored work tapes 3 and 4 *exactly* (same cells, head back at 1);
    * left the input tape, the other four work tapes, all other output
      cells, and the output head unchanged. -/
theorem haltTestTM_hoareTime (stSyms dSyms : List Γw)
    (hstnb : ∀ s ∈ stSyms, s ≠ Γw.blank)
    (inp₀ : Tape) (work₀ : Fin 6 → Tape) (out₀ : Tape)
    (hst : (work₀ 3).HoldsExact stSyms) (hsth : (work₀ 3).head = 1)
    (hd : (work₀ 4).HoldsExact dSyms) (hdh : (work₀ 4).head = 1)
    (_hout0 : out₀.cells 0 = Γ.start)
    (houtns : ∀ j, 1 ≤ j → out₀.cells j ≠ Γ.start)
    (houth : out₀.head = 1)
    (hinp : inp₀.read ≠ Γ.start)
    (hothers : ∀ i : Fin 6, i ≠ 3 → i ≠ 4 → (work₀ i).read ≠ Γ.start) :
    haltTestTM.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∀ i : Fin 6, i ≠ 3 → i ≠ 4 → work i = work₀ i) ∧
        work 3 = work₀ 3 ∧ work 4 = work₀ 4 ∧
        out.cells = Function.update out₀.cells 1
          (if stSyms = (takeField (takeField dSyms).2).1 then Γ.one else Γ.zero) ∧
        out.head = 1)
      (2 * dSyms.length + 2 * stSyms.length + 12) := by
  intro inp work out ⟨hi, hw, ho⟩
  subst hi; subst hw; subst ho
  -- standing facts about the initial tapes
  have hst_wf := Tape.HoldsExact.startInvariant hst
  have hd_wf := Tape.HoldsExact.startInvariant hd
  have h3read : (work 3).read ≠ Γ.start := by
    rw [Tape.read, hsth]; exact hst_wf.2 1 le_rfl
  have h4read : (work 4).read ≠ Γ.start := by
    rw [Tape.read, hdh]; exact hd_wf.2 1 le_rfl
  have hout_read : out.read ≠ Γ.start := by
    rw [Tape.read, houth]; exact houtns 1 le_rfl
  obtain ⟨hdc1, hdb1, hdc2, hdb2, hdlen⟩ := holdsExact_two_fields hd
  -- ── Phase A: skip the first desc field ──
  obtain ⟨c₁, hr₁, hst₁, hin₁, hw₁, hout₁, hcl₁, hhd₁⟩ :=
    skip_loop (takeField dSyms).1 (takeField_fst_ne_blank dSyms)
      (takeField dSyms).1.length 0
      { state := haltTestTM.qstart, input := inp, work := work, output := out }
      (by omega) rfl hdh hdc1 hdb1 hinp hout_read
      (by
        intro i hne
        by_cases h3i : i = 3
        · subst h3i; exact h3read
        · exact hothers i h3i hne)
  have hin₁' : c₁.input = inp := hin₁
  have hout₁' : c₁.output = out := hout₁
  have hw₁' : ∀ i : Fin 6, i ≠ 4 → c₁.work i = work i := hw₁
  have hcl₁' : (c₁.work 4).cells = (work 4).cells := hcl₁
  have hw₁3 : c₁.work 3 = work 3 := hw₁' 3 (by decide)
  -- ── Phase B: lockstep compare ──
  obtain ⟨c₂, t₂, ht₂, hr₂, hst₂, hin₂, hw₂, hout₂, hcl₂3, hcl₂4,
      hlo₂3, hhi₂3, hlo₂4, hhi₂4⟩ :=
    compare_loop stSyms hstnb (takeField (takeField dSyms).2).1
      (takeField_fst_ne_blank _)
      c₁ 1 ((takeField dSyms).1.length + 2) hst₁
      (by rw [hw₁3]; exact hsth) hhd₁
      (by
        intro j hj
        rw [hw₁3, Nat.add_comm]
        exact Tape.HoldsExact.cells_lt hst hj)
      (by rw [hw₁3, Nat.add_comm]; exact Tape.HoldsExact.cells_ge hst le_rfl)
      (by intro j hj; rw [hcl₁']; exact hdc2 j hj)
      (by rw [hcl₁']; exact hdb2)
      (by rw [hin₁']; exact hinp)
      (by rw [hout₁']; exact hout_read)
      (by
        intro i h3i h4i
        rw [hw₁' i h4i]
        exact hothers i h3i h4i)
  have hcl₂3' : (c₂.work 3).cells = (work 3).cells := by rw [hcl₂3, hw₁3]
  have hcl₂4' : (c₂.work 4).cells = (work 4).cells := by rw [hcl₂4, hcl₁']
  have hin₂' : c₂.input = inp := by rw [hin₂, hin₁']
  have hout₂' : c₂.output = out := by rw [hout₂, hout₁']
  -- ── Phase C: write the verdict ──
  obtain ⟨c₃, hstep₃, hst₃, hin₃, hw₃, hclo₃, hho₃⟩ :=
    verdict_step (stSyms = (takeField (takeField dSyms).2).1) c₂ hst₂
      (by rw [hout₂', houth])
      (by rw [hout₂']; exact hout_read)
      (by rw [hin₂']; exact hinp)
      (by rw [Tape.read, hcl₂3']; exact hst_wf.2 _ (by omega))
      (by rw [Tape.read, hcl₂4']; exact hd_wf.2 _ (by omega))
      (by
        intro i h3i h4i
        rw [hw₂ i h3i h4i, hw₁' i h4i]
        exact hothers i h3i h4i)
  have hin₃' : c₃.input = inp := by rw [hin₃, hin₂']
  have hclo₃' : c₃.output.cells = Function.update out.cells 1
      (if stSyms = (takeField (takeField dSyms).2).1 then Γ.one else Γ.zero) := by
    rw [hclo₃, hout₂']
  have hout₃read : c₃.output.read ≠ Γ.start := by
    rw [Tape.read, hho₃, hclo₃', Function.update_self]
    split <;> simp
  have hcl₃3 : (c₃.work 3).cells = (work 3).cells := by rw [hw₃ 3, hcl₂3']
  have hcl₃4 : (c₃.work 4).cells = (work 4).cells := by rw [hw₃ 4, hcl₂4']
  have hhd₃3 : (c₃.work 3).head = (c₂.work 3).head := by rw [hw₃ 3]
  have hhd₃4 : (c₃.work 4).head = (c₂.work 4).head := by rw [hw₃ 4]
  -- ── Phase D1: rewind the state head ──
  obtain ⟨c₄, hr₄, hst₄, hin₄, hw₄, hout₄, hcl₄, hhd₄⟩ :=
    rewindSt_loop (c₃.work 3).head c₃ hst₃ rfl
      (by rw [hcl₃3]; exact hst_wf.1)
      (by intro j hj; rw [hcl₃3]; exact hst_wf.2 j hj)
      (by rw [hin₃']; exact hinp)
      hout₃read
      (by rw [Tape.read, hcl₃4]; exact hd_wf.2 _ (by omega))
      (by
        intro i h3i h4i
        rw [hw₃ i, hw₂ i h3i h4i, hw₁' i h4i]
        exact hothers i h3i h4i)
  have hin₄' : c₄.input = inp := by rw [hin₄, hin₃']
  have hw₄4 : c₄.work 4 = c₃.work 4 := hw₄ 4 (by decide)
  have hcl₄3 : (c₄.work 3).cells = (work 3).cells := by rw [hcl₄, hcl₃3]
  -- ── Phase D2: rewind the desc head ──
  obtain ⟨c₅, hr₅, hst₅, hin₅, hw₅, hout₅, hcl₅, hhd₅⟩ :=
    rewindD_loop (c₄.work 4).head c₄ hst₄ rfl
      (by rw [hw₄4, hcl₃4]; exact hd_wf.1)
      (by intro j hj; rw [hw₄4, hcl₃4]; exact hd_wf.2 j hj)
      (by rw [hin₄']; exact hinp)
      (by rw [hout₄]; exact hout₃read)
      (by rw [Tape.read, hhd₄, hcl₄3]; exact hst_wf.2 1 le_rfl)
      (by
        intro i h3i h4i
        rw [hw₄ i h3i, hw₃ i, hw₂ i h3i h4i, hw₁' i h4i]
        exact hothers i h3i h4i)
  -- ── assemble ──
  have hm₃ : (c₃.work 3).head ≤ 1 + stSyms.length := by
    rw [hhd₃3]; exact hhi₂3
  have hm₄ : (c₄.work 4).head ≤ (takeField dSyms).1.length + 2
      + (takeField (takeField dSyms).2).1.length := by
    rw [hw₄4, hhd₃4]; exact hhi₂4
  refine ⟨c₅,
    ((takeField dSyms).1.length + 1 + t₂ + 1 + ((c₃.work 3).head + 1))
      + ((c₄.work 4).head + 1),
    by omega,
    reachesIn_trans _ (reachesIn_trans _ (reachesIn_trans _
      (reachesIn_trans _ hr₁ hr₂) (.step hstep₃ .zero)) hr₄) hr₅,
    hst₅, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- input unchanged
    rw [hin₅, hin₄']
  · -- work tapes 0, 1, 2, 5 unchanged
    intro i h3i h4i
    rw [hw₅ i h4i, hw₄ i h3i, hw₃ i, hw₂ i h3i h4i, hw₁' i h4i]
  · -- work tape 3 exactly restored
    rw [hw₅ 3 (by decide)]
    exact tape_eq_of_parts (by rw [hhd₄, hsth]) (by rw [hcl₄3])
  · -- work tape 4 exactly restored
    exact tape_eq_of_parts (by rw [hhd₅, hdh]) (by rw [hcl₅, hw₄4, hcl₃4])
  · -- output cells updated at cell 1
    rw [hout₅, hout₄]
    exact hclo₃'
  · -- output head at 1
    rw [hout₅, hout₄]
    exact hho₃

end TM

end Complexity
