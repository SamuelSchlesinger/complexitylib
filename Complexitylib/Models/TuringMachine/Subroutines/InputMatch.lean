/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Hoare
public import Complexitylib.Models.TuringMachine.Combinators
public import Complexitylib.Models.TuringMachine.Subroutines.MoveLeftStep
public import Complexitylib.Models.TuringMachine.ChoiceTape
public import Complexitylib.Models.TuringMachine.GuessStream

/-!
# Checking a guessed symbol against the input head

A scan reads work tapes. The one thing it cannot see is the input tape, so a machine that
simulates another machine's input head has to compare the symbol under that head against what it
guessed by hand.

`TM.inMatchTM` does exactly that, in two steps: it compares the two cells of a register against
the two bits a caller-supplied encoding assigns to the symbol under the input head, and leaves the
verdict on a result register. The input head does not move, so a simulation whose input head sits
at the simulated position keeps it there.

## Main definitions

- `TM.inMatchTM` — the check
- `TM.inMoveTM` — moving the input head by a guessed direction held in two one-cell registers, so
  it tracks the simulated one
- `TM.copyCellTM` — copying one register's cell onto another, which is how a scan's verdict leaves
  the result tape
- `TM.andCellTM` — conjoining one register's cell into another, which is how a machine with no
  early exit remembers that a check failed

## Main results

- `TM.inMatchTM_hoareTime` — its contract: two steps, the verdict on the result register, the
  compared register rewound, every other tape untouched
- `TM.inMoveTM_hoareTime` — and the move's: one step, the input head where the register says
- `TM.copyCellTM_hoareTime` — and the copy's
- `TM.andCellTM_hoareTime` — and the conjunction's
- `TM.guessProtocol_andCellTM` — the conjunction never consults the guess tape
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Control states of `TM.inMatchTM`: compare the first bit, then the second, then halt. -/
inductive InMatchPhase where
  | first | second | done
  deriving DecidableEq

instance : Fintype InMatchPhase where
  elems := {.first, .second, .done}
  complete := fun x => by cases x <;> simp

/-- **Check a guessed symbol against the input head.** Register `sym`, parked at cell one, holds
two bits; `expect` says which two bits the symbol under the input head should give. The verdict
lands on register `res`, and `sym` is left where it started. -/
def inMatchTM (expect : Γ → Bool × Bool) (sym res : Fin n) : TM n where
  Q := InMatchPhase
  qstart := .first
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .first =>
      (.second,
        fun i => if i = res then
            (if wHeads sym = Γ.ofBool (expect iHead).1 then Γw.one else Γw.zero)
          else readBackWrite (wHeads i),
        readBackWrite oHead, idleDir iHead,
        fun i => if i = sym then Dir3.right else idleDir (wHeads i), idleDir oHead)
    | .second =>
      (.done,
        fun i => if i = res then
            (if wHeads res = Γ.one ∧ wHeads sym = Γ.ofBool (expect iHead).2
              then Γw.one else Γw.zero)
          else readBackWrite (wHeads i),
        readBackWrite oHead, idleDir iHead,
        fun i => if i = sym then moveLeftDir (wHeads sym) else idleDir (wHeads i), idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .first =>
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi
      simp only []
      split
      · rfl
      · exact idleDir_right_of_start hwi
    | .second =>
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi
      simp only []
      split
      · next heq => subst heq; exact moveLeftDir_right_of_start hwi
      · exact idleDir_right_of_start hwi
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- The verdict `TM.inMatchTM` writes: both cells of `sym` agree with the two bits the symbol
under the input head is expected to give. -/
def inMatchVerdict (expect : Γ → Bool × Bool) (g : Γ) (c₁ c₂ : Γ) : Bool :=
  decide (c₁ = Γ.ofBool (expect g).1) && decide (c₂ = Γ.ofBool (expect g).2)

/-- The tape `TM.inMatchTM` leaves on its result register. -/
def inMatchRes (expect : Γ → Bool × Bool) (g : Γ) (c₁ c₂ : Γ) (t : Tape) : Tape :=
  ⟨1, Function.update t.cells 1 (Γ.ofBool (inMatchVerdict expect g c₁ c₂))⟩

/-- **The contract of the input-symbol check.** Two steps; the verdict lands on cell one of the
result register, the compared register comes back to cell one with its contents intact, and every
other tape — the input tape included — is untouched. -/
theorem inMatchTM_hoareTime (expect : Γ → Bool × Bool) (sym res : Fin n) (hsr : sym ≠ res)
    (inp₀ out₀ : Tape) (W₀ : Fin n → Tape)
    (hinv : ∀ i, (W₀ i).StartInvariant) (hh : ∀ i, 1 ≤ (W₀ i).head)
    (hinp : inp₀.read ≠ Γ.start) (hout : out₀.read ≠ Γ.start)
    (hsym : (W₀ sym).head = 1) (hres : (W₀ res).head = 1) :
    (inMatchTM expect sym res).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = W₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        (∀ i, i ≠ res → work i = W₀ i) ∧
        work res = inMatchRes expect inp₀.read ((W₀ sym).cells 1) ((W₀ sym).cells 2) (W₀ res))
      2 := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  classical
  -- What one step does to a tape parked at cell one, and to a tape it leaves alone.
  have hstay : ∀ (t : Tape) (s : Γw), t.StartInvariant → t.head = 1 →
      t.writeAndMove s.toΓ (idleDir t.read) = ⟨1, Function.update t.cells 1 s.toΓ⟩ := by
    intro t s hinvt ht
    have hns : t.read ≠ Γ.start := hinvt.read_ne_start (by omega)
    rw [idleDir, ite_eq_right hns]
    refine Tape.ext ?_ ?_
    · show (t.write s.toΓ).head = 1
      rw [Tape.write_head, ht]
    · show (t.write s.toΓ).cells = _
      rw [Tape.write, ite_eq_right (by omega), ht]
  have hright : ∀ (t : Tape), t.StartInvariant → t.head = 1 →
      t.writeAndMove (readBackWrite t.read).toΓ Dir3.right = ⟨2, t.cells⟩ := by
    intro t hinvt ht
    rw [writeAndMove_readBack_of_startInvariant t hinvt]
    refine Tape.ext ?_ (Tape.move_cells t Dir3.right)
    show t.head + 1 = 2
    omega
  have hleft2 : ∀ (t : Tape), t.StartInvariant → t.head = 2 →
      t.writeAndMove (readBackWrite t.read).toΓ (moveLeftDir t.read) = ⟨1, t.cells⟩ := by
    intro t hinvt ht
    have hns : t.read ≠ Γ.start := hinvt.read_ne_start (by omega)
    rw [writeAndMove_readBack_of_startInvariant t hinvt, moveLeftDir, ite_eq_right hns]
    refine Tape.ext ?_ (Tape.move_cells t Dir3.left)
    show t.head - 1 = 1
    omega
  have hidle : ∀ (t : Tape), t.StartInvariant → 1 ≤ t.head →
      t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read) = t := by
    intro t hinvt ht
    have hns : t.read ≠ Γ.start := hinvt.read_ne_start ht
    rw [writeAndMove_readBack_of_startInvariant t hinvt, idleDir, ite_eq_right hns]
    rfl
  set v₁ : Bool := decide ((work sym).cells 1 = Γ.ofBool (expect inp.read).1) with hv1
  set W1 : Fin n → Tape := fun i =>
    if i = res then (⟨1, Function.update (work res).cells 1 (Γ.ofBool v₁)⟩ : Tape)
    else if i = sym then (⟨2, (work sym).cells⟩ : Tape) else work i with hW1
  have hsymread : (work sym).read = (work sym).cells 1 := by rw [Tape.read, hsym]
  have hstep1 : (inMatchTM expect sym res).step
      ⟨InMatchPhase.first, inp, work, out⟩ = some ⟨InMatchPhase.second, inp, W1, out⟩ := by
    rw [TM.step_of_not_halted _ (show InMatchPhase.first ≠ InMatchPhase.done by decide)]
    refine congrArg some (Cfg.ext rfl ?_ ?_ ?_)
    · show inp.move (idleDir inp.read) = inp
      exact transitionInput_eq_self hinp
    · show (fun i => (work i).writeAndMove _ _) = W1
      funext i
      rw [hW1]
      show (work i).writeAndMove
        ((if i = res then (if (work sym).read = Γ.ofBool (expect inp.read).1
            then Γw.one else Γw.zero) else readBackWrite (work i).read) : Γw).toΓ
        (if i = sym then Dir3.right else idleDir (work i).read) = _
      simp only []
      by_cases hir : i = res
      · have hisym : ¬ (i = sym) := fun hc => hsr (hc.symm.trans hir)
        rw [ite_eq_left hir, ite_eq_right hisym, ite_eq_left hir,
          hstay (work i) _ (hinv i) (by rw [hir]; exact hres), hir]
        refine Tape.ext rfl ?_
        show Function.update (work res).cells 1 _ = Function.update (work res).cells 1 _
        rw [hv1, hsymread]
        by_cases hc : (work sym).cells 1 = Γ.ofBool (expect inp.read).1
        · rw [ite_eq_left hc, decide_eq_true hc]
          rfl
        · rw [ite_eq_right hc, decide_eq_false hc]
          rfl
      · rw [ite_eq_right hir, ite_eq_right hir]
        by_cases his : i = sym
        · rw [ite_eq_left his, ite_eq_left his, his, hright (work sym) (hinv sym) hsym]
        · rw [ite_eq_right his, ite_eq_right his, hidle (work i) (hinv i) (hh i)]
    · exact transitionTape_eq_self hout
  -- The tapes after the first step are still well formed.
  have hW1res : W1 res = ⟨1, Function.update (work res).cells 1 (Γ.ofBool v₁)⟩ := by
    rw [hW1]
    show (if res = res then _ else _) = _
    rw [ite_eq_left rfl]
  have hW1sym : W1 sym = ⟨2, (work sym).cells⟩ := by
    rw [hW1]
    show (if sym = res then _ else if sym = sym then _ else _) = _
    rw [ite_eq_right hsr, ite_eq_left rfl]
  have hW1other : ∀ i, i ≠ res → i ≠ sym → W1 i = work i := by
    intro i h1 h2
    rw [hW1]
    show (if i = res then _ else if i = sym then _ else _) = _
    rw [ite_eq_right h1, ite_eq_right h2]
  have hinv1 : ∀ i, (W1 i).StartInvariant := by
    intro i
    by_cases hir : i = res
    · subst hir
      rw [hW1res]
      refine ⟨?_, ?_⟩
      · show Function.update (work i).cells 1 (Γ.ofBool v₁) 0 = Γ.start
        rw [Function.update_of_ne (show (0 : ℕ) ≠ 1 by decide)]
        exact (hinv i).1
      · intro q hq
        show Function.update (work i).cells 1 (Γ.ofBool v₁) q ≠ Γ.start
        by_cases hq1 : q = 1
        · rw [hq1, Function.update_self]
          cases v₁ <;> exact fun hc => Γ.noConfusion hc
        · rw [Function.update_of_ne hq1]
          exact (hinv i).2 q hq
    · by_cases his : i = sym
      · subst his
        rw [hW1sym]
        exact ⟨(hinv i).1, (hinv i).2⟩
      · rw [hW1other i hir his]
        exact hinv i
  have hh1 : ∀ i, 1 ≤ (W1 i).head := by
    intro i
    by_cases hir : i = res
    · subst hir
      rw [hW1res]
    · by_cases his : i = sym
      · subst his
        rw [hW1sym]
        exact (by omega : (1 : ℕ) ≤ 2)
      · rw [hW1other i hir his]; exact hh i
  have hread1res : (W1 res).read = Γ.ofBool v₁ := by
    rw [hW1res]
    show Function.update (work res).cells 1 (Γ.ofBool v₁) 1 = _
    rw [Function.update_self]
  have hread1sym : (W1 sym).read = (work sym).cells 2 := by rw [hW1sym]; rfl
  set v₂ : Bool := inMatchVerdict expect inp.read ((work sym).cells 1) ((work sym).cells 2)
    with hv2
  set W2 : Fin n → Tape := fun i =>
    if i = res then (⟨1, Function.update (work res).cells 1 (Γ.ofBool v₂)⟩ : Tape) else work i
    with hW2
  have hstep2 : (inMatchTM expect sym res).step
      ⟨InMatchPhase.second, inp, W1, out⟩ = some ⟨InMatchPhase.done, inp, W2, out⟩ := by
    rw [TM.step_of_not_halted _ (show InMatchPhase.second ≠ InMatchPhase.done by decide)]
    refine congrArg some (Cfg.ext rfl ?_ ?_ ?_)
    · show inp.move (idleDir inp.read) = inp
      exact transitionInput_eq_self hinp
    · show (fun i => (W1 i).writeAndMove _ _) = W2
      funext i
      rw [hW2]
      show (W1 i).writeAndMove
        ((if i = res then (if (W1 res).read = Γ.one ∧ (W1 sym).read
              = Γ.ofBool (expect inp.read).2 then Γw.one else Γw.zero)
          else readBackWrite (W1 i).read) : Γw).toΓ
        (if i = sym then moveLeftDir (W1 sym).read else idleDir (W1 i).read) = _
      simp only []
      by_cases hir : i = res
      · have hisym : ¬ (i = sym) := fun hc => hsr (hc.symm.trans hir)
        rw [ite_eq_left hir, ite_eq_right hisym, ite_eq_left hir, hir,
          hstay (W1 res) _ (hinv1 res) (by rw [hW1res])]
        refine Tape.ext rfl ?_
        show Function.update (W1 res).cells 1 _ = Function.update (work res).cells 1 _
        rw [hread1res, hread1sym, hW1res]
        show Function.update (Function.update (work res).cells 1 (Γ.ofBool v₁)) 1 _
          = Function.update (work res).cells 1 _
        rw [Function.update_idem]
        refine congrArg _ ?_
        rw [hv2, inMatchVerdict, hv1]
        by_cases hc : Γ.ofBool v₁ = Γ.one ∧ (work sym).cells 2 = Γ.ofBool (expect inp.read).2
        · rw [ite_eq_left hc]
          have h1 : v₁ = true := by
            rcases hc with ⟨hc1, -⟩
            by_contra hne
            rw [Bool.not_eq_true] at hne
            rw [hne] at hc1
            simp [Γ.ofBool] at hc1
          rw [hv1] at h1
          rw [h1, decide_eq_true hc.2]
          rfl
        · rw [ite_eq_right hc]
          have h2 : ¬ (decide ((work sym).cells 1 = Γ.ofBool (expect inp.read).1) &&
              decide ((work sym).cells 2 = Γ.ofBool (expect inp.read).2)) = true := by
            intro hall
            rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hall
            refine hc ⟨?_, hall.2⟩
            rw [hv1, decide_eq_true hall.1]
            rfl
          rw [Bool.not_eq_true] at h2
          rw [h2]
          rfl
      · rw [ite_eq_right hir, ite_eq_right hir]
        by_cases his : i = sym
        · rw [ite_eq_left his, his, hleft2 (W1 sym) (hinv1 sym) (by rw [hW1sym])]
          rw [hW1sym]
          exact Tape.ext hsym.symm rfl
        · rw [ite_eq_right his, hidle (W1 i) (hinv1 i) (hh1 i)]
          exact hW1other i hir his
    · exact transitionTape_eq_self hout
  refine ⟨⟨InMatchPhase.done, inp, W2, out⟩, 2, le_rfl,
    TM.reachesIn.step hstep1 (TM.reachesIn.step hstep2 TM.reachesIn.zero), rfl, rfl, rfl,
    fun i hi => ?_, ?_⟩
  · rw [hW2]
    show (if i = res then _ else _) = _
    rw [ite_eq_right hi]
  · rw [hW2]
    show (if res = res then _ else _) = _
    rw [ite_eq_left rfl]
    rfl

/-! ## Moving the input head with the simulated one -/

/-- Control states of `TM.inMoveTM`. -/
inductive InMovePhase where
  | go | done
  deriving DecidableEq

instance : Fintype InMovePhase where
  elems := {.go, .done}
  complete := fun x => by cases x <;> simp

/-- **Move the input head by the direction two registers' cells name.** A guessed cell holds a
bit, so it cannot name one of three directions on its own; a machine's transition sees every head
at once, so two one-cell registers do it in a single step. Reading `▷` still forces a move right,
as it must. -/
def inMoveTM (decode : Γ → Γ → Dir3) (mv dir : Fin n) : TM n where
  Q := InMovePhase
  qstart := .go
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .go =>
      (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
        (if iHead = Γ.start then Dir3.right else decode (wHeads mv) (wHeads dir)),
        fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .go =>
      exact ⟨fun h => ite_eq_left h, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- **The contract of the input-head move.** One step; the input head moves as the register says,
and every other tape is untouched. -/
theorem inMoveTM_hoareTime (decode : Γ → Γ → Dir3) (mv dir : Fin n)
    (inp₀ out₀ : Tape) (W₀ : Fin n → Tape)
    (hinv : ∀ i, (W₀ i).StartInvariant) (hh : ∀ i, 1 ≤ (W₀ i).head)
    (hinp : inp₀.read ≠ Γ.start) (hout : out₀.read ≠ Γ.start) :
    (inMoveTM decode mv dir).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = W₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀.move (decode (W₀ mv).read (W₀ dir).read) ∧ work = W₀ ∧ out = out₀)
      1 := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  have hidle : ∀ (t : Tape), t.StartInvariant → 1 ≤ t.head →
      t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read) = t := by
    intro t hinvt ht
    rw [writeAndMove_readBack_of_startInvariant t hinvt, idleDir,
      ite_eq_right (hinvt.read_ne_start ht)]
    rfl
  have hstep : (inMoveTM decode mv dir).step ⟨InMovePhase.go, inp, work, out⟩
      = some ⟨InMovePhase.done, inp.move (decode (work mv).read (work dir).read), work, out⟩ := by
    rw [TM.step_of_not_halted _ (show InMovePhase.go ≠ InMovePhase.done by decide)]
    refine congrArg some (Cfg.ext rfl ?_ ?_ (transitionTape_eq_self hout))
    · show inp.move (if inp.read = Γ.start then Dir3.right
        else decode (work mv).read (work dir).read) = _
      rw [ite_eq_right hinp]
    · show (fun i => (work i).writeAndMove _ _) = work
      funext i
      exact hidle (work i) (hinv i) (hh i)
  exact ⟨_, 1, le_rfl, TM.reachesIn.step hstep TM.reachesIn.zero, rfl, rfl, rfl, rfl⟩

/-! ## Copying one cell to another register -/

/-- **Copy the symbol under one register's head onto another register.** A scan leaves its verdict
on the machine's result tape, which no scan can read; moving it onto an ordinary register is what
lets a later check take it into account. -/
def copyCellTM (src dst : Fin n) : TM n where
  Q := InMovePhase
  qstart := .go
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .go =>
      (.done,
        fun i => if i = dst then readBackWrite (wHeads src) else readBackWrite (wHeads i),
        readBackWrite oHead, idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .go => exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- **The contract of the cell copy.** One step; the destination's cell under its head becomes the
source's, and nothing else moves. -/
theorem copyCellTM_hoareTime (src dst : Fin n) (inp₀ out₀ : Tape) (W₀ : Fin n → Tape)
    (hinv : ∀ i, (W₀ i).StartInvariant) (hh : ∀ i, 1 ≤ (W₀ i).head)
    (hinp : inp₀.read ≠ Γ.start) (hout : out₀.read ≠ Γ.start) :
    (copyCellTM src dst).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧ work = W₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        (∀ i, i ≠ dst → work i = W₀ i) ∧
        work dst = ⟨(W₀ dst).head,
          Function.update (W₀ dst).cells (W₀ dst).head (readBackWrite (W₀ src).read).toΓ⟩)
      1 := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  have hidle : ∀ (t : Tape), t.StartInvariant → 1 ≤ t.head →
      t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read) = t := by
    intro t hinvt ht
    rw [writeAndMove_readBack_of_startInvariant t hinvt, idleDir,
      ite_eq_right (hinvt.read_ne_start ht)]
    rfl
  have hwrite : ∀ (t : Tape) (s : Γ), t.StartInvariant → 1 ≤ t.head →
      t.writeAndMove s (idleDir t.read)
        = ⟨t.head, Function.update t.cells t.head s⟩ := by
    intro t s hinvt ht
    rw [idleDir, ite_eq_right (hinvt.read_ne_start ht)]
    refine Tape.ext ?_ ?_
    · show (t.write s).head = t.head
      rw [Tape.write_head]
    · show (t.write s).cells = _
      rw [Tape.write, ite_eq_right (by omega)]
  have hstep : (copyCellTM src dst).step ⟨InMovePhase.go, inp, work, out⟩
      = some ⟨InMovePhase.done, inp,
        fun i => if i = dst then (⟨(work dst).head,
            Function.update (work dst).cells (work dst).head
              (readBackWrite (work src).read).toΓ⟩ : Tape)
          else work i, out⟩ := by
    rw [TM.step_of_not_halted _ (show InMovePhase.go ≠ InMovePhase.done by decide)]
    refine congrArg some (Cfg.ext rfl (transitionInput_eq_self hinp) ?_
      (transitionTape_eq_self hout))
    funext i
    show (work i).writeAndMove
      ((if i = dst then readBackWrite (work src).read else readBackWrite (work i).read) : Γw).toΓ
      (idleDir (work i).read) = (if i = dst then _ else _)
    by_cases hi : i = dst
    · rw [ite_eq_left hi, ite_eq_left hi, hi, hwrite (work dst) _ (hinv dst) (hh dst)]
    · rw [ite_eq_right hi, ite_eq_right hi, hidle (work i) (hinv i) (hh i)]
  refine ⟨_, 1, le_rfl, TM.reachesIn.step hstep TM.reachesIn.zero, rfl, rfl, rfl,
    fun i hi => ?_, ?_⟩
  · show (if i = dst then _ else _) = work i
    rw [ite_eq_right hi]
  · show (if dst = dst then _ else _) = _
    rw [ite_eq_left rfl]

/-- **Conjoin one register's cell into another.** The destination's cell under its head becomes
`1` exactly when both it and the source's cell held `1`. A loop driver with no early exit — such
as `TM.binaryForTM` — cannot stop at the first failed check, so its body accumulates the verdicts
here instead. -/
def andCellTM (src dst : Fin n) : TM n where
  Q := InMovePhase
  qstart := .go
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .go =>
      (.done,
        fun i => if i = dst then
            (if wHeads src = Γ.one ∧ wHeads dst = Γ.one then Γw.one else Γw.zero)
          else readBackWrite (wHeads i),
        readBackWrite oHead, idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .go => exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- **The contract of the cell conjunction.** One step; the destination's cell under its head
becomes the conjunction of the two cells, and nothing else moves. -/
theorem andCellTM_hoareTime (src dst : Fin n) (inp₀ out₀ : Tape) (W₀ : Fin n → Tape)
    (hinv : ∀ i, (W₀ i).StartInvariant) (hh : ∀ i, 1 ≤ (W₀ i).head)
    (hinp : inp₀.read ≠ Γ.start) (hout : out₀.read ≠ Γ.start) :
    (andCellTM src dst).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧ work = W₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        (∀ i, i ≠ dst → work i = W₀ i) ∧
        work dst = ⟨(W₀ dst).head,
          Function.update (W₀ dst).cells (W₀ dst).head
            (if (W₀ src).read = Γ.one ∧ (W₀ dst).read = Γ.one then Γ.one else Γ.zero)⟩)
      1 := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  have hwrite : ∀ (t : Tape) (s : Γ), t.StartInvariant → 1 ≤ t.head →
      t.writeAndMove s (idleDir t.read)
        = ⟨t.head, Function.update t.cells t.head s⟩ := by
    intro t s hinvt ht
    rw [idleDir, ite_eq_right (hinvt.read_ne_start ht)]
    refine Tape.ext ?_ ?_
    · show (t.write s).head = t.head
      rw [Tape.write_head]
    · show (t.write s).cells = _
      rw [Tape.write, ite_eq_right (by omega)]
  have hidle : ∀ (t : Tape), t.StartInvariant → 1 ≤ t.head →
      t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read) = t := by
    intro t hinvt ht
    rw [writeAndMove_readBack_of_startInvariant t hinvt, idleDir,
      ite_eq_right (hinvt.read_ne_start ht)]
    rfl
  have hstep : (andCellTM src dst).step ⟨InMovePhase.go, inp, work, out⟩
      = some ⟨InMovePhase.done, inp,
        fun i => if i = dst then (⟨(work dst).head,
            Function.update (work dst).cells (work dst).head
              (if (work src).read = Γ.one ∧ (work dst).read = Γ.one then Γ.one else Γ.zero)⟩
            : Tape)
          else work i, out⟩ := by
    rw [TM.step_of_not_halted _ (show InMovePhase.go ≠ InMovePhase.done by decide)]
    refine congrArg some (Cfg.ext rfl (transitionInput_eq_self hinp) ?_
      (transitionTape_eq_self hout))
    funext i
    show (work i).writeAndMove
      ((if i = dst then
          (if (work src).read = Γ.one ∧ (work dst).read = Γ.one then Γw.one else Γw.zero)
        else readBackWrite (work i).read) : Γw).toΓ
      (idleDir (work i).read) = (if i = dst then _ else _)
    by_cases hi : i = dst
    · subst hi
      rw [ite_eq_left rfl, ite_eq_left rfl, hwrite (work i) _ (hinv i) (hh i)]
      by_cases hc : (work src).read = Γ.one ∧ (work i).read = Γ.one
      · rw [ite_eq_left hc, ite_eq_left hc]
        rfl
      · rw [ite_eq_right hc, ite_eq_right hc]
        rfl
    · rw [ite_eq_right hi, ite_eq_right hi, hidle (work i) (hinv i) (hh i)]
  refine ⟨_, 1, le_rfl, TM.reachesIn.step hstep TM.reachesIn.zero, rfl, rfl, rfl,
    fun i hi => ?_, ?_⟩
  · show (if i = dst then _ else _) = work i
    rw [ite_eq_right hi]
  · show (if dst = dst then _ else _) = _
    rw [ite_eq_left rfl]

/-- **The cell conjunction never consults the guess tape**, so it may sit inside a
nondeterministic assembly. -/
theorem guessProtocol_andCellTM {k : ℕ} (src dst : Fin (k + 1))
    (hsrc : src ≠ Fin.last k) (hdst : dst ≠ Fin.last k) :
    GuessProtocol (andCellTM src dst) (fun _ => false) := by
  have hdst' : ¬ (Fin.last k = dst) := fun h => hdst h.symm
  refine ⟨?_, ?_, ?_⟩
  · intro q hq iHead wHeads oHead
    cases q with
    | go => simp [andCellTM, hdst']
    | done => exact absurd rfl hq
  · intro q hq iHead wHeads oHead hg
    cases q with
    | go => simp [andCellTM, idleDir, hg]
    | done => exact absurd rfl hq
  · intro q hq _ iHead ww oHead g g'
    obtain ⟨js, hjs⟩ := Fin.exists_castSucc_eq.mpr hsrc
    obtain ⟨jd, hjd⟩ := Fin.exists_castSucc_eq.mpr hdst
    subst hjs
    subst hjd
    cases q with
    | go => simp [andCellTM, visible, Fin.snoc_castSucc]
    | done => simp [andCellTM, visible, allIdle, Fin.snoc_castSucc]

end TM

end Complexity
