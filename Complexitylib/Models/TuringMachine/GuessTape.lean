/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.ChoiceTape

/-!
# Building a nondeterministic machine from a deterministic one

`Complexitylib.Models.TuringMachine.ChoiceTape` runs one path of a given `NTM` deterministically.
This file goes the other way, which is what a *construction* needs: it turns a deterministic
machine that reads a **guess tape** into a nondeterministic machine whose choices supply that
tape's contents.

The point is leverage. Every subroutine in `Complexitylib.Models.TuringMachine.Subroutines` is
deterministic, and so is every Hoare-style contract proved about them. Assembling an `NTM` by
hand forgoes all of it. Assembling a `TM` that consults one extra tape for its guesses, and then
applying `NTM.ofGuess`, keeps the whole toolkit and confines the nondeterminism to a single
tape read.

## Conventions

The guess tape is the **last** work tape, matching `NTM.choiceTM`. A machine that uses it as a
guess tape must, at every step, write the cell back unchanged and move that head one cell right —
that is `TM.GuessDiscipline`. The discipline is what makes the guesses independent: the machine
consumes exactly one fresh bit per step and can never revisit one.

## Main definitions

- `NTM.ofGuess` — the nondeterministic machine a guess-reading deterministic machine denotes
- `TM.GuessDiscipline` — write the guess cell back, advance its head
- `Tape.BoolFrom` — the guess tape holds Boolean symbols for the next `T` cells

## Main results

- `NTM.choiceTM_ofGuess_δ` — the round trip is the identity on transitions
- `NTM.step_ofGuess` — and on steps, wherever the guess cell holds a bit
- `NTM.reachesIn_ofGuess_iff` — and on runs
- `NTM.ofGuess_simulates` — a `T`-step run of `M` on a loaded guess tape is a trace of
  `NTM.ofGuess M` along the bits loaded onto it
-/

@[expose] public section

namespace Complexity

namespace Tape

/-- The next `T` cells from the head hold Boolean symbols. -/
def BoolFrom (t : Tape) (T : ℕ) : Prop :=
  ∀ j < T, ∃ b : Bool, t.cells (t.head + j) = Γ.ofBool b

theorem BoolFrom.read {t : Tape} {T : ℕ} (h : t.BoolFrom (T + 1)) :
    ∃ b : Bool, t.read = Γ.ofBool b := by
  obtain ⟨b, hb⟩ := h 0 (Nat.succ_pos T)
  exact ⟨b, by simpa [Tape.read] using hb⟩

theorem BoolFrom.read_ne_start {t : Tape} {T : ℕ} (h : t.BoolFrom (T + 1)) :
    t.read ≠ Γ.start := by
  obtain ⟨b, hb⟩ := h.read
  rw [hb]
  exact Γ.ofBool_ne_start b

theorem BoolFrom.move_right {t : Tape} {T : ℕ} (h : t.BoolFrom (T + 1)) :
    (t.move Dir3.right).BoolFrom T := by
  intro j hj
  obtain ⟨b, hb⟩ := h (j + 1) (by omega)
  refine ⟨b, ?_⟩
  show t.cells (t.head + 1 + j) = Γ.ofBool b
  rw [show t.head + 1 + j = t.head + (j + 1) by omega]
  exact hb

theorem BoolFrom.mono {t : Tape} {T T' : ℕ} (h : t.BoolFrom T) (hle : T' ≤ T) :
    t.BoolFrom T' :=
  fun j hj => h j (by omega)

end Tape

namespace TM

variable {k : ℕ}

/-- **The guess-tape discipline.** At every transition the machine writes the last work tape's
cell back unchanged and advances that head one cell right, so it consumes exactly one fresh
guess per step and never revisits one. -/
structure GuessDiscipline (M : TM (k + 1)) : Prop where
  /-- The guess cell is written back unchanged. -/
  write : ∀ (q : M.Q) (iHead : Γ) (wHeads : Fin (k + 1) → Γ) (oHead : Γ),
    (M.δ q iHead wHeads oHead).2.1 (Fin.last k) = readBackWrite (wHeads (Fin.last k))
  /-- The guess head advances one cell right. -/
  dir : ∀ (q : M.Q) (iHead : Γ) (wHeads : Fin (k + 1) → Γ) (oHead : Γ),
    (M.δ q iHead wHeads oHead).2.2.2.2.1 (Fin.last k) = Dir3.right

end TM

namespace NTM

variable {k : ℕ}

/-- **The nondeterministic machine a guess-reading deterministic machine denotes.** The choice
bit is fed to `M` as the symbol under the last work head, and that tape disappears. -/
def ofGuess (M : TM (k + 1)) : NTM k where
  Q := M.Q
  qstart := M.qstart
  qhalt := M.qhalt
  δ b q iHead wHeads oHead :=
    let r := M.δ q iHead (Fin.snoc wHeads (Γ.ofBool b)) oHead
    (r.1, fun j => r.2.1 j.castSucc, r.2.2.1, r.2.2.2.1,
      fun j => r.2.2.2.2.1 j.castSucc, r.2.2.2.2.2)
  δ_right_of_start := by
    intro b q iHead wHeads oHead
    have h := M.δ_right_of_start q iHead (Fin.snoc wHeads (Γ.ofBool b)) oHead
    dsimp only at h ⊢
    refine ⟨h.1, fun i hi => ?_, h.2.2⟩
    exact h.2.1 i.castSucc (by rwa [Fin.snoc_castSucc])

@[simp] theorem ofGuess_Q (M : TM (k + 1)) : (ofGuess M).Q = M.Q := rfl

@[simp] theorem ofGuess_qhalt (M : TM (k + 1)) : (ofGuess M).qhalt = M.qhalt := rfl

@[simp] theorem ofGuess_qstart (M : TM (k + 1)) : (ofGuess M).qstart = M.qstart := rfl

private theorem snoc_init_self' {α : Type} (f : Fin (k + 1) → α) :
    Fin.snoc (fun j => f j.castSucc) (f (Fin.last k)) = f :=
  Fin.snoc_init_self f

/-- **The round trip is the identity on transitions.** Reattaching the guess tape to
`NTM.ofGuess M` recovers `M`, wherever the guess cell holds a bit. -/
theorem choiceTM_ofGuess_δ (M : TM (k + 1)) (hM : TM.GuessDiscipline M)
    (q : M.Q) (iHead : Γ) (wHeads : Fin (k + 1) → Γ) (oHead : Γ) (b : Bool)
    (hb : wHeads (Fin.last k) = Γ.ofBool b) :
    (choiceTM (ofGuess M)).δ q iHead wHeads oHead = M.δ q iHead wHeads oHead := by
  have hcell : Γ.ofBool (decide (wHeads (Fin.last k) = Γ.one)) = wHeads (Fin.last k) := by
    rw [hb]; cases b <;> decide
  dsimp only [choiceTM, ofGuess]
  rw [hcell, snoc_init_self' wHeads, ← hM.write q iHead wHeads oHead,
    ← hM.dir q iHead wHeads oHead, snoc_init_self', snoc_init_self']

/-- **The round trip is the identity on steps**, wherever the guess cell holds a bit. -/
theorem step_ofGuess (M : TM (k + 1)) (hM : TM.GuessDiscipline M) {c : Cfg (k + 1) M.Q}
    (hb : ∃ b : Bool, (c.work (Fin.last k)).read = Γ.ofBool b) :
    (choiceTM (ofGuess M)).step c = M.step c := by
  obtain ⟨b, hbv⟩ := hb
  by_cases hhalt : c.state = M.qhalt
  · have h1 : (choiceTM (ofGuess M)).step c = none := by
      unfold TM.step
      simp [hhalt, choiceTM, ofGuess]
    have h2 : M.step c = none := by
      unfold TM.step
      simp [hhalt]
    rw [h1, h2]
    rfl
  · rw [TM.step_of_not_halted (choiceTM (ofGuess M)) hhalt, TM.step_of_not_halted M hhalt]
    have hδ := choiceTM_ofGuess_δ M hM c.state c.input.read (fun i => (c.work i).read)
      c.output.read b hbv
    simp only [TM.stepCfg, hδ]
    rfl

/-- **A step leaves the guess tape alone and advances its head.** -/
theorem work_last_stepCfg (M : TM (k + 1)) (hM : TM.GuessDiscipline M) (c : Cfg (k + 1) M.Q)
    (hread : (c.work (Fin.last k)).read ≠ Γ.start) :
    (M.stepCfg c).work (Fin.last k) = (c.work (Fin.last k)).move Dir3.right := by
  show (c.work (Fin.last k)).writeAndMove ((M.δ c.state c.input.read
      (fun i => (c.work i).read) c.output.read).2.1 (Fin.last k))
      ((M.δ c.state c.input.read (fun i => (c.work i).read) c.output.read).2.2.2.2.1
        (Fin.last k))
    = (c.work (Fin.last k)).move Dir3.right
  rw [hM.write, hM.dir]
  exact TM.writeAndMove_readBack _ hread Dir3.right

/-- **The round trip is the identity on runs**, as long as the guess tape holds bits for as many
cells as the run has steps. -/
theorem reachesIn_ofGuess_iff (M : TM (k + 1)) (hM : TM.GuessDiscipline M) :
    ∀ (t : ℕ) (c c' : Cfg (k + 1) M.Q), (c.work (Fin.last k)).BoolFrom t →
      ((choiceTM (ofGuess M)).reachesIn t c c' ↔ M.reachesIn t c c') := by
  intro t
  induction t with
  | zero =>
      intro c c' _
      erw [TM.reachesIn_zero_iff, TM.reachesIn_zero_iff]
      exact Iff.rfl
  | succ t ih =>
      intro c c' hbool
      by_cases hhalt : c.state = M.qhalt
      · have h1 : M.step c = none := by
          unfold TM.step
          simp [hhalt]
        constructor
        · intro h
          erw [TM.reachesIn_succ_iff] at h
          obtain ⟨c₁, hs, -⟩ := h
          rw [step_ofGuess M hM hbool.read, h1] at hs
          exact absurd hs (by simp)
        · intro h
          erw [TM.reachesIn_succ_iff] at h
          obtain ⟨c₁, hs, -⟩ := h
          rw [h1] at hs
          exact absurd hs (by simp)
      · have hstep : M.step c = some (M.stepCfg c) := TM.step_of_not_halted M hhalt
        have hbool₁ : ((M.stepCfg c).work (Fin.last k)).BoolFrom t := by
          rw [work_last_stepCfg M hM c hbool.read_ne_start]
          exact hbool.move_right
        constructor
        · intro h
          erw [TM.reachesIn_succ_iff] at h
          obtain ⟨c₁, hs, hr⟩ := h
          rw [step_ofGuess M hM hbool.read, hstep] at hs
          have hs' : M.stepCfg c = c₁ := Option.some.inj hs
          subst hs'
          exact TM.reachesIn.step hstep ((ih _ c' hbool₁).mp hr)
        · intro h
          erw [TM.reachesIn_succ_iff] at h
          obtain ⟨c₁, hs, hr⟩ := h
          rw [hstep] at hs
          have hs' : M.stepCfg c = c₁ := Option.some.inj hs
          subst hs'
          refine TM.reachesIn.step ?_ ((ih _ c' hbool₁).mpr hr)
          rw [step_ofGuess M hM hbool.read]
          exact hstep

/-- **A run of `M` on a loaded guess tape is a trace of `NTM.ofGuess M`.** This is the transfer
that lets a nondeterministic construction be carried out deterministically: build `M`, prove
whatever is wanted of its runs with the deterministic toolkit, and read it off here as a
statement about the paths of `NTM.ofGuess M`. -/
theorem ofGuess_simulates (M : TM (k + 1)) (hM : TM.GuessDiscipline M) (T : ℕ)
    (c : Cfg (k + 1) M.Q)
    (hinv : (c.work (Fin.last k)).StartInvariant)
    (hhead : 1 ≤ (c.work (Fin.last k)).head)
    (hbool : (c.work (Fin.last k)).BoolFrom T) :
    ∃ (c' : Cfg (k + 1) M.Q) (t : ℕ), t ≤ T ∧ M.reachesIn t c c' ∧
      (t < T → M.halted c') ∧
      dropChoice c' = (ofGuess M).trace T (fun j => choiceStream c j.val) (dropChoice c) := by
  obtain ⟨c', t, hle, hreach, hstop, heq⟩ := choiceTM_simulates (ofGuess M) T c hinv hhead
  exact ⟨c', t, hle, (reachesIn_ofGuess_iff M hM t c c' (hbool.mono hle)).mp hreach, hstop, heq⟩

/-- **Reading back a loaded guess tape.** A tape whose cells from the head onward spell `g`
presents exactly `g` as its choice stream. -/
theorem choiceStream_of_loaded {Q : Type} {c : Cfg (k + 1) Q} {g : ℕ → Bool} {T : ℕ}
    (h : ∀ j < T, (c.work (Fin.last k)).cells ((c.work (Fin.last k)).head + j) = Γ.ofBool (g j))
    {j : ℕ} (hj : j < T) : choiceStream c j = g j := by
  rw [choiceStream, h j hj]
  cases g j <;> decide

/-! ## Loading a guess tape -/

/-- The guess tape carrying `g`: cell `j + 1` holds `g j`, and the head starts on cell 1. -/
def loadTape (g : ℕ → Bool) : Tape where
  head := 1
  cells := fun j => if j = 0 then Γ.start else Γ.ofBool (g (j - 1))

@[simp] theorem loadTape_head (g : ℕ → Bool) : (loadTape g).head = 1 := rfl

theorem loadTape_cells_succ (g : ℕ → Bool) (j : ℕ) :
    (loadTape g).cells (j + 1) = Γ.ofBool (g j) := by
  simp [loadTape]

theorem loadTape_startInvariant (g : ℕ → Bool) : (loadTape g).StartInvariant := by
  refine ⟨by simp [loadTape], fun j hj => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [loadTape_cells_succ]
  exact Γ.ofBool_ne_start _

theorem loadTape_boolFrom (g : ℕ → Bool) (T : ℕ) : (loadTape g).BoolFrom T := by
  intro j _
  exact ⟨g j, by simp [loadTape]⟩

/-- The starting configuration of the deterministic machine: the input in place, every work tape
blank except the last, which carries the guesses. -/
def loadCfg (M : TM (k + 1)) (x : List Bool) (g : ℕ → Bool) : Cfg (k + 1) M.Q where
  state := M.qstart
  input := Tape.init (x.map Γ.ofBool)
  work := Fin.snoc (fun _ => Tape.init ([] : List Γ)) (loadTape g)
  output := Tape.init ([] : List Γ)

@[simp] theorem loadCfg_work_last (M : TM (k + 1)) (x : List Bool) (g : ℕ → Bool) :
    (loadCfg M x g).work (Fin.last k) = loadTape g := by
  simp [loadCfg]

theorem dropChoice_loadCfg (M : TM (k + 1)) (x : List Bool) (g : ℕ → Bool) :
    dropChoice (loadCfg M x g) = (ofGuess M).initCfg x := by
  refine Cfg.ext rfl rfl ?_ rfl
  funext i
  simp [dropChoice, loadCfg]

/-- **The paths of `NTM.ofGuess M` are the runs of `M` on a loaded guess tape.** This is the
form a construction uses: design `M` so that its run on guess string `g` does what the path
along `g` should do, and this reads that back as a statement about `NTM.ofGuess M`. -/
theorem ofGuess_trace (M : TM (k + 1)) (hM : TM.GuessDiscipline M) (x : List Bool) (T : ℕ)
    (g : ℕ → Bool) :
    ∃ (c' : Cfg (k + 1) M.Q) (t : ℕ), t ≤ T ∧ M.reachesIn t (loadCfg M x g) c' ∧
      (t < T → M.halted c') ∧
      dropChoice c' = (ofGuess M).trace T (fun j => g j.val) ((ofGuess M).initCfg x) := by
  obtain ⟨c', t, hle, hreach, hstop, heq⟩ := ofGuess_simulates M hM T (loadCfg M x g)
    (by simpa using loadTape_startInvariant g) (by simp) (by simpa using loadTape_boolFrom g T)
  refine ⟨c', t, hle, hreach, hstop, ?_⟩
  rw [heq]
  congr 1
  · funext j
    exact choiceStream_of_loaded (T := T)
      (fun i _ => by simp [loadCfg, loadTape]) j.isLt
  · exact dropChoice_loadCfg M x g

end NTM

end Complexity
