/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.GuessStream
public import Complexitylib.Models.TuringMachine.Subroutines.ParkRewind
public import Complexitylib.Models.TuringMachine.Hoare
public import Complexitylib.Models.TuringMachine.Registers.RegisterOps

/-!
# Assembling a machine that guesses

`Complexitylib.Models.TuringMachine.GuessStream` reduces building a nondeterministic machine to
building a deterministic one that satisfies `TM.GuessProtocol` on its last work tape. This file
supplies the parts.

`TM.liftLast` puts an ordinary machine to work on the first tapes and leaves the guess tape
untouched, so every existing subroutine can be used verbatim. `TM.GuessProtocol` is then closed
under `TM.seqTM` and `TM.loopTM`, which is what lets the guessing and the not-guessing be
assembled into one machine: all three of its conditions are pointwise properties of the transition
function, and the combinators' own steps preserve every tape they are not driving.

## Main definitions

- `TM.liftLast` — run a machine on the first work tapes, holding the last one still
- `TM.guessReadTM` — copy the guess cell onto a work tape and advance the guess head
- `TM.guessWriteTM` — the same, advancing the target head too, so a block of guesses can be
  written
- `TM.guessBlockTM` — a fixed number of those in sequence
- `TM.guessBlocksTM` — and a block written into each of several registers
- `TM.guessThenTM` — guess some blocks, then run a guess-free machine on them
- `TM.guessStageTM` — and the stage every construction is built from: guess, then rewind the
  guessed registers so a scan can read them
- `TM.guessWriteTapes`, `TM.guessBlockTapes` — the tapes one guess-write, and a block of them,
  leave behind

## Main results

- `TM.guessProtocol_liftLast` — a lifted machine never consults the guess tape
- `TM.liftLast_reachesIn` — and its runs are the original's
- `TM.lift4`, `TM.lift4_hoareTime` — the same, four tapes at a time
- `TM.guessProtocol_seqTM`, `TM.guessProtocol_loopTM` — the protocol survives composition
- `TM.guessProtocol_guessReadTM`, `TM.guessReadTM_stepCfg`,
  `TM.guessProtocol_guessWriteTM`, `TM.guessWriteTM_stepCfg` — what the primitives do
- `TM.guessProtocol_guessBlockTM`, `TM.guessProtocol_guessBlocksTM`,
  `TM.guessProtocol_guessThenTM` — and these respect the protocol
- `TM.skipTM_hoareTime'`, `TM.guessBlocksTM_hoareTime`, `TM.guessThenTM_hoareTime` — and their
  contracts
- `TM.guessWriteTM_hoareTime`, `TM.guessBlockTM_hoareTime` — their contracts
- `TM.guessWriteTapes_last`, `TM.guessWriteTapes_target`, `TM.guessWriteTapes_other` — what one
  guess-write does to each tape, off the left marker
- `TM.guessWriteTapes_target_head`, `TM.guessWriteTapes_target_cells`,
  `TM.guessWriteTapes_target_cells_ne` — where the guessed bit lands
- `TM.guessWriteTapes_startInvariant`, `TM.guessWriteTapes_head_pos` — and that the invariants
  survive it
- `TM.GuessFrom`, `TM.guessFrom_after` — what the guess tape still holds, and that a stage
  consumes a prefix and leaves the rest
- `TM.guessBlocksTapes_spec` — what several blocks leave behind, when the registers are distinct
- `TM.guessList`, `TM.guessList_getElem` — the guess stream that realizes a family of blocks
- `TM.StageBlocks`, `TM.exists_stageBlocks`, `TM.blocks_of_stageBlocks` — and one that feeds every
  stage of a loop, with each stage reading its own blocks off it
- `TM.guessBlockTapes_spec` — what a whole block leaves behind: both heads advanced by the number
  of bits, those bits on the target, nothing else touched
-/

@[expose] public section

namespace Complexity

namespace TM

variable {k m : ℕ}

/-! ## Lifting a machine past the guess tape -/

/-- Run `D` on the first `m` work tapes, writing the last one back unchanged and holding its head
still. -/
def liftLast (D : TM m) : TM (m + 1) where
  Q := D.Q
  qstart := D.qstart
  qhalt := D.qhalt
  δ q iHead wHeads oHead :=
    let r := D.δ q iHead (fun i => wHeads i.castSucc) oHead
    (r.1, Fin.snoc r.2.1 (readBackWrite (wHeads (Fin.last m))), r.2.2.1, r.2.2.2.1,
      Fin.snoc r.2.2.2.2.1 (idleDir (wHeads (Fin.last m))), r.2.2.2.2.2)
  δ_right_of_start := by
    intro q iHead wHeads oHead
    have h := D.δ_right_of_start q iHead (fun i => wHeads i.castSucc) oHead
    dsimp only at h ⊢
    refine ⟨h.1, fun i => ?_, h.2.2⟩
    refine Fin.lastCases ?_ ?_ i
    · intro hs
      rw [Fin.snoc_last]
      exact idleDir_right_of_start hs
    · intro j hj
      rw [Fin.snoc_castSucc]
      exact h.2.1 j hj

@[simp] theorem liftLast_qhalt (D : TM m) : (liftLast D).qhalt = D.qhalt := rfl

@[simp] theorem liftLast_qstart (D : TM m) : (liftLast D).qstart = D.qstart := rfl

/-- A lifted machine never consults the guess tape, so it advances nowhere. -/
theorem guessProtocol_liftLast (D : TM m) : GuessProtocol (liftLast D) (fun _ => false) := by
  refine ⟨fun q _ iHead wHeads oHead => ?_, fun q _ iHead wHeads oHead h => ?_,
    fun q _ _ iHead ww oHead g g' => ?_⟩
  · simp [liftLast]
  · simp [liftLast, idleDir, h]
  · simp only [visible, liftLast, Fin.snoc_castSucc]

/-- One step of a lifted machine is one step of the original, with the guess tape untouched. -/
theorem liftLast_stepCfg (D : TM m) (c : Cfg m D.Q) (τ : Tape) (hτ : τ.read ≠ Γ.start) :
    (liftLast D).stepCfg (NTM.attach c τ) = NTM.attach (D.stepCfg c) τ := by
  refine Cfg.ext ?_ ?_ ?_ ?_
  · simp [TM.stepCfg, liftLast, NTM.attach]
  · simp [TM.stepCfg, liftLast, NTM.attach]
  · funext i
    refine Fin.lastCases ?_ ?_ i
    · simp only [TM.stepCfg, liftLast, NTM.attach, Fin.snoc_last]
      rw [writeAndMove_readBack _ hτ, idleDir, ite_eq_right hτ]
      rfl
    · intro j
      simp [TM.stepCfg, liftLast, NTM.attach]
  · simp [TM.stepCfg, liftLast, NTM.attach]

/-- **A run of a lifted machine is a run of the original.** -/
theorem liftLast_reachesIn (D : TM m) (τ : Tape) (hτ : τ.read ≠ Γ.start) :
    ∀ (t : ℕ) {c c' : Cfg m D.Q}, D.reachesIn t c c' →
      (liftLast D).reachesIn t (NTM.attach c τ) (NTM.attach c' τ) := by
  intro t
  induction t with
  | zero =>
      intro c c' h
      rw [reachesIn_zero_iff] at h
      subst h
      exact reachesIn.zero
  | succ t ih =>
      intro c c' h
      rw [reachesIn_succ_iff] at h
      obtain ⟨c₁, hstep, hrest⟩ := h
      have hne : c.state ≠ D.qhalt := by
        intro hq
        unfold TM.step at hstep
        rw [ite_eq_left hq] at hstep
        exact absurd hstep (by simp)
      have hb : D.stepCfg c = c₁ := by
        rw [step_of_not_halted D hne] at hstep
        exact Option.some.inj hstep
      subst hb
      refine reachesIn.step ?_ (ih hrest)
      rw [step_of_not_halted (liftLast D) hne, liftLast_stepCfg D c τ hτ]
      rfl

/-- The starting configuration of a lifted machine is the original's with the guess tape
attached. -/
theorem liftLast_initCfg (D : TM m) (inp out : Tape) (work : Fin (m + 1) → Tape) :
    ({ state := (liftLast D).qstart, input := inp, work := work, output := out } :
        Cfg (m + 1) (liftLast D).Q)
      = NTM.attach
          { state := D.qstart
            input := inp
            work := fun i => work i.castSucc
            output := out } (work (Fin.last m)) := by
  refine Cfg.ext rfl rfl ?_ rfl
  exact (Fin.snoc_init_self work).symm

/-- **A Hoare triple for a lifted machine.** Everything the original guarantees still holds, and
the guess tape comes out exactly as it went in. -/
theorem liftLast_hoareTime (D : TM m) {pre post : TapePred m} {bound : ℕ}
    (h : D.HoareTime pre post bound) (τ : Tape) (hτ : τ.read ≠ Γ.start) :
    (liftLast D).HoareTime
      (fun inp work out => work (Fin.last m) = τ ∧ pre inp (fun i => work i.castSucc) out)
      (fun inp work out => work (Fin.last m) = τ ∧ post inp (fun i => work i.castSucc) out)
      bound := by
  rintro inp work out ⟨hlast, hpre⟩
  obtain ⟨c', t, hle, hreach, hhalt, hpost⟩ := h inp (fun i => work i.castSucc) out hpre
  refine ⟨NTM.attach c' τ, t, hle, ?_, hhalt, ?_, ?_⟩
  · rw [liftLast_initCfg D inp out work, hlast]
    exact liftLast_reachesIn D τ hτ t hreach
  · simp [NTM.attach]
  · simpa [NTM.attach] using hpost

/-- Lift a machine past four fresh tapes, holding them still. Four at a time because a check's
block is four tapes wide. -/
def lift4 (D : TM m) : TM (m + 4) :=
  liftLast (liftLast (liftLast (liftLast D)))

/-- A lifted-by-four machine never consults the last tape. -/
theorem guessProtocol_lift4 (D : TM m) :
    GuessProtocol (lift4 D) (fun _ => false) :=
  guessProtocol_liftLast _

/-- **A lifted-by-four machine's contract.** Four fresh tapes come through untouched. -/
theorem lift4_hoareTime (D : TM m) {pre post : TapePred m} {b : ℕ}
    (h : D.HoareTime pre post b) (τ₁ τ₂ τ₃ τ₄ : Tape)
    (h₁ : τ₁.read ≠ Γ.start) (h₂ : τ₂.read ≠ Γ.start) (h₃ : τ₃.read ≠ Γ.start)
    (h₄ : τ₄.read ≠ Γ.start) :
    (lift4 D).HoareTime
      (fun inp work out => work (Fin.last (m + 3)) = τ₄ ∧
        (fun i => work i.castSucc) (Fin.last (m + 2)) = τ₃ ∧
        (fun i => work i.castSucc.castSucc) (Fin.last (m + 1)) = τ₂ ∧
        (fun i => work i.castSucc.castSucc.castSucc) (Fin.last m) = τ₁ ∧
        pre inp (fun i => work i.castSucc.castSucc.castSucc.castSucc) out)
      (fun inp work out => work (Fin.last (m + 3)) = τ₄ ∧
        (fun i => work i.castSucc) (Fin.last (m + 2)) = τ₃ ∧
        (fun i => work i.castSucc.castSucc) (Fin.last (m + 1)) = τ₂ ∧
        (fun i => work i.castSucc.castSucc.castSucc) (Fin.last m) = τ₁ ∧
        post inp (fun i => work i.castSucc.castSucc.castSucc.castSucc) out)
      b :=
  liftLast_hoareTime _ (liftLast_hoareTime _
    (liftLast_hoareTime _ (liftLast_hoareTime D h τ₁ h₁) τ₂ h₂) τ₃ h₃) τ₄ h₄

/-- Lift a machine past `r` fresh tapes, holding them still. The original tapes
keep their indices — `Fin.castAdd r` — and the fresh ones are appended.

`TM.liftTM` in `Models/TuringMachine/Lift.lean` widens a machine the same way,
but its interface carries *blank* extra tapes, for lifting whole decision
procedures. This one is the iterated `liftLast`, so its Hoare rule below carries
arbitrary extra tapes through untouched — what an assembled subroutine needs. -/
def liftMany (D : TM m) : (r : ℕ) → TM (m + r)
  | 0 => D
  | r + 1 => liftLast (liftMany D r)

/-- **A padded machine's contract.** The `r` fresh tapes come through
untouched, and the original tapes keep their meaning under `Fin.castAdd`. -/
theorem liftMany_hoareTime (D : TM m) {pre post : TapePred m} {b : ℕ}
    (h : D.HoareTime pre post b) :
    ∀ (r : ℕ) (τ : Fin r → Tape), (∀ i, (τ i).read ≠ Γ.start) →
      (liftMany D r).HoareTime
        (fun inp work out => (∀ i, work (Fin.natAdd m i) = τ i) ∧
          pre inp (fun i => work (Fin.castAdd r i)) out)
        (fun inp work out => (∀ i, work (Fin.natAdd m i) = τ i) ∧
          post inp (fun i => work (Fin.castAdd r i)) out)
        b := by
  intro r
  induction r with
  | zero =>
    intro τ _
    refine TM.HoareTime.consequence (h := h) ?_ ?_ (Nat.le_refl b)
    · rintro inp work out ⟨-, hpre⟩
      simpa only [Fin.castAdd_zero, Fin.cast_eq_self] using hpre
    · intro inp work out hpost
      exact ⟨fun i => absurd i.isLt (Nat.not_lt_zero i.val), by
        simpa only [Fin.castAdd_zero, Fin.cast_eq_self] using hpost⟩
  | succ r ih =>
    intro τ hτ
    have hlift := liftLast_hoareTime (liftMany D r)
      (ih (fun i => τ i.castSucc) fun i => hτ _) (τ (Fin.last r))
      (hτ (Fin.last r))
    have hnat : ∀ (work : Fin (m + r + 1) → Tape) (i : Fin (r + 1)),
        work (Fin.natAdd m i) =
          (Fin.snoc (fun j : Fin r => work (Fin.natAdd m j).castSucc)
            (work (Fin.last (m + r))) : Fin (r + 1) → Tape) i := by
      intro work i
      refine Fin.lastCases ?_ ?_ i
      · rw [Fin.snoc_last]
        congr 1
      · intro j
        rw [Fin.snoc_castSucc]
        congr 1
    have hcast : ∀ (work : Fin (m + r + 1) → Tape) (i : Fin m),
        work (Fin.castAdd (r + 1) i) = work (Fin.castAdd r i).castSucc := by
      intro work i
      congr 1
    refine TM.HoareTime.consequence (h := hlift) ?_ ?_ (Nat.le_refl b)
    · rintro inp work out ⟨hfresh, hpre⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [← hfresh (Fin.last r)]
        exact congrArg work (Fin.ext (by simp))
      · intro i
        have := hfresh i.castSucc
        rw [hnat work i.castSucc, Fin.snoc_castSucc] at this
        exact this
      · simpa only [hcast work] using hpre
    · rintro inp work out ⟨hlast, hfresh, hpost⟩
      refine ⟨?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · rw [hnat work (Fin.last r), Fin.snoc_last, hlast]
        · intro j
          rw [hnat work j.castSucc, Fin.snoc_castSucc]
          exact hfresh j
      · simpa only [hcast work] using hpost

/-- A lifted machine keeps the one-way-output discipline. -/
theorem IsTransducer.liftLast {D : TM m} (h : D.IsTransducer) :
    (liftLast D).IsTransducer := fun q iHead wHeads oHead =>
  h q iHead (fun i => wHeads i.castSucc) oHead

/-- A padded machine keeps the one-way-output discipline. -/
theorem IsTransducer.liftMany {D : TM m} (h : D.IsTransducer) :
    ∀ r, (liftMany D r).IsTransducer
  | 0 => h
  | r + 1 => (h.liftMany r).liftLast

/-! ## The protocol survives composition -/

/-- The advancing states of a sequential composition: each part's own, with the handoff step —
which the combinator takes in `A`'s halt state — excluded. -/
def seqAdv {A B : TM (k + 1)} (AdvA : A.Q → Bool) (AdvB : B.Q → Bool) :
    SeqQ A.Q B.Q → Bool :=
  Sum.elim (fun q => AdvA q && !decide (q = A.qhalt)) AdvB

/-- **The guess protocol survives sequential composition.** -/
theorem guessProtocol_seqTM {A B : TM (k + 1)} {AdvA : A.Q → Bool} {AdvB : B.Q → Bool}
    (hA : GuessProtocol A AdvA) (hB : GuessProtocol B AdvB) :
    GuessProtocol (seqTM A B) (seqAdv AdvA AdvB) := by
  have hinr : ∀ q : B.Q, (Sum.inr q : SeqQ A.Q B.Q) ≠ (seqTM A B).qhalt → q ≠ B.qhalt :=
    fun q hq hb => hq (by rw [hb]; rfl)
  refine ⟨?_, ?_, ?_⟩
  · rintro (q | q) hq iHead wHeads oHead
    · by_cases h : q = A.qhalt
      · subst h
        simp [seqTM]
      · have hred : ((seqTM A B).δ (Sum.inl q) iHead wHeads oHead).2.1
            = (A.δ q iHead wHeads oHead).2.1 := by simp [seqTM, h]
        rw [hred]
        exact hA.write q h iHead wHeads oHead
    · have h := hinr q hq
      have hred : ((seqTM A B).δ (Sum.inr q) iHead wHeads oHead).2.1
          = (B.δ q iHead wHeads oHead).2.1 := by simp [seqTM, h]
      rw [hred]
      exact hB.write q h iHead wHeads oHead
  · rintro (q | q) hq iHead wHeads oHead hs
    · by_cases h : q = A.qhalt
      · subst h
        simp [seqTM, seqAdv, idleDir, hs]
      · have hred : ((seqTM A B).δ (Sum.inl q) iHead wHeads oHead).2.2.2.2.1
            = (A.δ q iHead wHeads oHead).2.2.2.2.1 := by simp [seqTM, h]
        rw [hred, hA.dir q h iHead wHeads oHead hs]
        simp [seqAdv, h]
    · have h := hinr q hq
      have hred : ((seqTM A B).δ (Sum.inr q) iHead wHeads oHead).2.2.2.2.1
          = (B.δ q iHead wHeads oHead).2.2.2.2.1 := by simp [seqTM, h]
      rw [hred, hB.dir q h iHead wHeads oHead hs]
      simp [seqAdv]
      rfl
  · rintro (q | q) hq hadv iHead ww oHead g g'
    · by_cases h : q = A.qhalt
      · subst h
        simp [seqTM, visible]
      · have hadvA : ¬ AdvA q = true := by
          simpa [seqAdv, h] using hadv
        have hAi := hA.indep q h hadvA iHead ww oHead g g'
        have hmap := congrArg (fun z : A.Q × (Fin k → Γw) × Γw × Dir3 × (Fin k → Dir3) × Dir3 =>
          ((Sum.inl z.1 : SeqQ A.Q B.Q), z.2)) hAi
        simpa [seqTM, visible, h] using hmap
    · have h := hinr q hq
      have hBi := hB.indep q h (by simpa [seqAdv] using hadv) iHead ww oHead g g'
      have hmap := congrArg (fun z : B.Q × (Fin k → Γw) × Γw × Dir3 × (Fin k → Dir3) × Dir3 =>
        ((Sum.inr z.1 : SeqQ A.Q B.Q), z.2)) hBi
      simpa [seqTM, visible, h] using hmap

/-- The advancing states of a loop: each part's own, with the combinator's own control phases and
handoff steps excluded. -/
def loopAdv {Body Test : TM (k + 1)} (AdvB : Body.Q → Bool) (AdvT : Test.Q → Bool) :
    LoopQ Body.Q Test.Q → Bool :=
  Sum.elim (fun q => AdvB q && !decide (q = Body.qhalt))
    (Sum.elim (fun _ => false) (fun q => AdvT q && !decide (q = Test.qhalt)))

/-- **The guess protocol survives looping.** -/
theorem guessProtocol_loopTM {Body Test : TM (k + 1)} {AdvB : Body.Q → Bool}
    {AdvT : Test.Q → Bool} (hB : GuessProtocol Body AdvB) (hT : GuessProtocol Test AdvT) :
    GuessProtocol (loopTM Body Test) (loopAdv AdvB AdvT) := by
  have hphase : ∀ p : LoopPhase, (Sum.inr (Sum.inl p) : LoopQ Body.Q Test.Q)
      ≠ (loopTM Body Test).qhalt → p ≠ LoopPhase.done := fun p hq hd => hq (by rw [hd]; rfl)
  refine ⟨?_, ?_, ?_⟩
  · rintro (q | (p | q)) hq iHead wHeads oHead
    · by_cases h : q = Body.qhalt
      · subst h
        simp [loopTM]
      · have hred : ((loopTM Body Test).δ (Sum.inl q) iHead wHeads oHead).2.1
            = (Body.δ q iHead wHeads oHead).2.1 := by simp [loopTM, h]
        rw [hred]
        exact hB.write q h iHead wHeads oHead
    · have hp := hphase p hq
      cases p with
      | rewindOut =>
          simp only [loopTM]
          split <;> rfl
      | check =>
          simp only [loopTM]
          split <;> rfl
      | done => exact absurd rfl hp
    · by_cases h : q = Test.qhalt
      · subst h
        simp [loopTM]
      · have hred : ((loopTM Body Test).δ (Sum.inr (Sum.inr q)) iHead wHeads oHead).2.1
            = (Test.δ q iHead wHeads oHead).2.1 := by simp [loopTM, h]
        rw [hred]
        exact hT.write q h iHead wHeads oHead
  · rintro (q | (p | q)) hq iHead wHeads oHead hs
    · by_cases h : q = Body.qhalt
      · subst h
        simp [loopTM, loopAdv, idleDir, hs]
      · have hred : ((loopTM Body Test).δ (Sum.inl q) iHead wHeads oHead).2.2.2.2.1
            = (Body.δ q iHead wHeads oHead).2.2.2.2.1 := by simp [loopTM, h]
        rw [hred, hB.dir q h iHead wHeads oHead hs]
        simp [loopAdv, h]
    · have hp := hphase p hq
      cases p with
      | rewindOut =>
          simp only [loopTM]
          split <;> simp [loopAdv, idleDir, hs]
      | check =>
          simp only [loopTM]
          split <;> simp [loopAdv, idleDir, hs]
      | done => exact absurd rfl hp
    · by_cases h : q = Test.qhalt
      · subst h
        simp [loopTM, loopAdv, idleDir, hs]
      · have hred : ((loopTM Body Test).δ (Sum.inr (Sum.inr q)) iHead wHeads oHead).2.2.2.2.1
            = (Test.δ q iHead wHeads oHead).2.2.2.2.1 := by simp [loopTM, h]
        rw [hred, hT.dir q h iHead wHeads oHead hs]
        simp [loopAdv, h]
  · rintro (q | (p | q)) hq hadv iHead ww oHead g g'
    · by_cases h : q = Body.qhalt
      · subst h
        simp [loopTM, visible]
      · have hadvB : ¬ AdvB q = true := by simpa [loopAdv, h] using hadv
        have hBi := hB.indep q h hadvB iHead ww oHead g g'
        have hmap := congrArg
          (fun z : Body.Q × (Fin k → Γw) × Γw × Dir3 × (Fin k → Dir3) × Dir3 =>
            ((Sum.inl z.1 : LoopQ Body.Q Test.Q), z.2)) hBi
        simpa [loopTM, visible, h] using hmap
    · have hp := hphase p hq
      cases p with
      | rewindOut =>
          simp only [loopTM]
          split <;> simp [visible]
      | check =>
          simp only [loopTM]
          split <;> simp [visible]
      | done => exact absurd rfl hp
    · by_cases h : q = Test.qhalt
      · subst h
        simp [loopTM, visible]
      · have hadvT : ¬ AdvT q = true := by simpa [loopAdv, h] using hadv
        have hTi := hT.indep q h hadvT iHead ww oHead g g'
        have hmap := congrArg
          (fun z : Test.Q × (Fin k → Γw) × Γw × Dir3 × (Fin k → Dir3) × Dir3 =>
            ((Sum.inr (Sum.inr z.1) : LoopQ Body.Q Test.Q), z.2)) hTi
        simpa [loopTM, visible, h] using hmap

/-! ## Reading a guess -/

/-- Control states of `TM.guessReadTM`. -/
inductive GuessPhase where
  /-- Copy the guess cell onto the target tape. -/
  | read
  /-- Halt. -/
  | done
  deriving DecidableEq

instance : Fintype GuessPhase where
  elems := {.read, .done}
  complete := fun x => by cases x <;> simp

/-- The advancing state of the guess primitives: only `read` consumes a guess bit.
Stated on `GuessPhase` itself so instance search never has to see through a
machine's `Q` projection. -/
@[simp] def guessPhaseAdv (q : GuessPhase) : Bool := decide (q = GuessPhase.read)

/-- **The guess-reading primitive.** In one step it copies the symbol under the guess head onto
work tape `j`, advances the guess head, and halts. This is the only place a machine assembled
with `TM.liftLast` ever consults the guess tape. -/
def guessReadTM (j : Fin (k + 1)) : TM (k + 1) where
  Q := GuessPhase
  qstart := .read
  qhalt := .done
  δ q iHead wHeads oHead :=
    match q with
    | .read =>
      (GuessPhase.done,
        fun i => if i = j then readBackWrite (wHeads (Fin.last k)) else readBackWrite (wHeads i),
        readBackWrite oHead,
        idleDir iHead,
        fun i => if i = Fin.last k then Dir3.right else idleDir (wHeads i),
        idleDir oHead)
    | .done => allIdle GuessPhase.done iHead wHeads oHead
  δ_right_of_start := by
    intro q iHead wHeads oHead
    match q with
    | .read =>
      refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
      dsimp only
      split
      · rfl
      · exact idleDir_right_of_start hi
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

@[simp] theorem guessReadTM_qhalt (j : Fin (k + 1)) :
    (guessReadTM j).qhalt = GuessPhase.done := rfl

@[simp] theorem guessReadTM_qstart (j : Fin (k + 1)) :
    (guessReadTM j).qstart = GuessPhase.read := rfl

/-- The guess-reading primitive advances exactly in its one working state. -/
theorem guessProtocol_guessReadTM (j : Fin (k + 1)) :
    GuessProtocol (guessReadTM j) guessPhaseAdv := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (_ | _) hq iHead wHeads oHead
    · simp only [guessReadTM]
      split <;> simp_all
    · exact absurd rfl hq
  · rintro (_ | _) hq iHead wHeads oHead hs
    · simp [guessReadTM]
    · exact absurd rfl hq
  · rintro (_ | _) hq hadv iHead ww oHead g g'
    · simp at hadv
    · exact absurd rfl hq

/-- One step of the guess-reading primitive: the guess symbol lands on tape `j`, the guess head
advances, and every other tape is left where it was. -/
theorem guessReadTM_stepCfg (j : Fin (k + 1)) (hj : j ≠ Fin.last k)
    (c : Cfg (k + 1) (guessReadTM j).Q) (hstate : c.state = GuessPhase.read) :
    ((guessReadTM j).stepCfg c).state = GuessPhase.done ∧
      ((guessReadTM j).stepCfg c).work j
        = (c.work j).writeAndMove (readBackWrite (c.work (Fin.last k)).read).toΓ
            (idleDir (c.work j).read) ∧
      ((guessReadTM j).stepCfg c).work (Fin.last k)
        = (c.work (Fin.last k)).writeAndMove
            (readBackWrite (c.work (Fin.last k)).read).toΓ Dir3.right ∧
      (∀ i, i ≠ j → i ≠ Fin.last k →
        ((guessReadTM j).stepCfg c).work i
          = (c.work i).writeAndMove (readBackWrite (c.work i).read).toΓ
              (idleDir (c.work i).read)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [TM.stepCfg, guessReadTM, hstate]
  · simp [TM.stepCfg, guessReadTM, hstate, hj]
  · simp [TM.stepCfg, guessReadTM, hstate, Ne.symm hj]
  · intro i hij hil
    simp [TM.stepCfg, guessReadTM, hstate, hij, hil]

/-- **The guess-writing primitive.** Like `TM.guessReadTM`, but it also advances the target head,
so that repeating it writes a block of guessed bits. -/
def guessWriteTM (j : Fin (k + 1)) : TM (k + 1) where
  Q := GuessPhase
  qstart := .read
  qhalt := .done
  δ q iHead wHeads oHead :=
    match q with
    | .read =>
      (GuessPhase.done,
        fun i => if i = j then readBackWrite (wHeads (Fin.last k)) else readBackWrite (wHeads i),
        readBackWrite oHead,
        idleDir iHead,
        fun i => if i = Fin.last k then Dir3.right else if i = j then Dir3.right
          else idleDir (wHeads i),
        idleDir oHead)
    | .done => allIdle GuessPhase.done iHead wHeads oHead
  δ_right_of_start := by
    intro q iHead wHeads oHead
    match q with
    | .read =>
      refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
      dsimp only
      split
      · rfl
      · split
        · rfl
        · exact idleDir_right_of_start hi
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

@[simp] theorem guessWriteTM_qhalt (j : Fin (k + 1)) :
    (guessWriteTM j).qhalt = GuessPhase.done := rfl

@[simp] theorem guessWriteTM_qstart (j : Fin (k + 1)) :
    (guessWriteTM j).qstart = GuessPhase.read := rfl

/-- The guess-writing primitive advances exactly in its one working state. -/
theorem guessProtocol_guessWriteTM (j : Fin (k + 1)) :
    GuessProtocol (guessWriteTM j) guessPhaseAdv := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (_ | _) hq iHead wHeads oHead
    · simp only [guessWriteTM]
      split <;> simp_all
    · exact absurd rfl hq
  · rintro (_ | _) hq iHead wHeads oHead hs
    · simp [guessWriteTM]
    · exact absurd rfl hq
  · rintro (_ | _) hq hadv iHead ww oHead g g'
    · simp at hadv
    · exact absurd rfl hq

/-- One step of the guess-writing primitive: the guess symbol lands on tape `j`, which then
advances, the guess head advances, and every other tape is left where it was. -/
theorem guessWriteTM_stepCfg (j : Fin (k + 1)) (hj : j ≠ Fin.last k)
    (c : Cfg (k + 1) (guessWriteTM j).Q) (hstate : c.state = GuessPhase.read) :
    ((guessWriteTM j).stepCfg c).state = GuessPhase.done ∧
      ((guessWriteTM j).stepCfg c).work j
        = (c.work j).writeAndMove (readBackWrite (c.work (Fin.last k)).read).toΓ Dir3.right ∧
      ((guessWriteTM j).stepCfg c).work (Fin.last k)
        = (c.work (Fin.last k)).writeAndMove
            (readBackWrite (c.work (Fin.last k)).read).toΓ Dir3.right ∧
      (∀ i, i ≠ j → i ≠ Fin.last k →
        ((guessWriteTM j).stepCfg c).work i
          = (c.work i).writeAndMove (readBackWrite (c.work i).read).toΓ
              (idleDir (c.work i).read)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [TM.stepCfg, guessWriteTM, hstate]
  · simp [TM.stepCfg, guessWriteTM, hstate, hj]
  · simp [TM.stepCfg, guessWriteTM, hstate, Ne.symm hj]
  · intro i hij hil
    simp [TM.stepCfg, guessWriteTM, hstate, hij, hil]

/-- The tapes after one guess-write: the target takes the guessed symbol and advances, the guess
tape advances, and every other tape passes through the phase transition unchanged. -/
def guessWriteTapes (j : Fin (k + 1)) (W : Fin (k + 1) → Tape) : Fin (k + 1) → Tape :=
  fun i => if i = j then (W j).writeAndMove (readBackWrite (W (Fin.last k)).read).toΓ Dir3.right
    else if i = Fin.last k then (W (Fin.last k)).writeAndMove
      (readBackWrite (W (Fin.last k)).read).toΓ Dir3.right
    else transitionTape (W i)

/-- **The contract of one guess-write.** -/
theorem guessWriteTM_hoareTime (j : Fin (k + 1)) (hj : j ≠ Fin.last k)
    (inp₀ out₀ : Tape) (W₀ : Fin (k + 1) → Tape) :
    (guessWriteTM j).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧ work = W₀)
      (fun inp work out => inp = transitionInput inp₀ ∧ out = transitionTape out₀ ∧
        work = guessWriteTapes j W₀) 1 := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  have hne : (GuessPhase.read : (guessWriteTM j).Q) ≠ (guessWriteTM j).qhalt := by
    intro h
    exact GuessPhase.noConfusion h
  refine ⟨(guessWriteTM j).stepCfg
    { state := (guessWriteTM j).qstart, input := inp, work := work, output := out },
    1, le_rfl, reachesIn.step (step_of_not_halted _ hne) reachesIn.zero, ?_, ?_, ?_, ?_⟩
  · exact (guessWriteTM_stepCfg j hj _ rfl).1
  · rfl
  · rfl
  · obtain ⟨-, h1, h2, h3⟩ := guessWriteTM_stepCfg j hj
      { state := (guessWriteTM j).qstart, input := inp, work := work, output := out } rfl
    funext i
    rw [guessWriteTapes]
    by_cases hij : i = j
    · rw [ite_eq_left hij, hij]
      exact h1
    · rw [ite_eq_right hij]
      by_cases hil : i = Fin.last k
      · rw [ite_eq_left hil, hil]
        exact h2
      · rw [ite_eq_right hil]
        exact h3 i hij hil

/-! ## Writing a block of guesses

A parameter block is a fixed number of bits — fixed because it holds a state, a choice bit and
one symbol per head, none of which grows with the input — so the machine that writes it can be
built by recursion on that number rather than by a counted loop. -/

/-- Write `n + 1` guessed bits onto work tape `j`, advancing it. -/
def guessBlockTM (j : Fin (k + 1)) : ℕ → TM (k + 1)
  | 0 => guessWriteTM j
  | n + 1 => seqTM (guessWriteTM j) (guessBlockTM j n)

/-- Its advancing states: every state of every stage. -/
def guessBlockAdv (j : Fin (k + 1)) : (n : ℕ) → (guessBlockTM j n).Q → Bool
  | 0 => guessPhaseAdv
  | n + 1 => seqAdv guessPhaseAdv (guessBlockAdv j n)

/-- The tapes a block of guess-writes leaves behind. Each stage writes, then the composition's
own handoff step passes every tape through `TM.transitionTape`. -/
def guessBlockTapes (j : Fin (k + 1)) : ℕ → (Fin (k + 1) → Tape) → (Fin (k + 1) → Tape)
  | 0, W => guessWriteTapes j W
  | n + 1, W => guessBlockTapes j n (fun i => transitionTape (guessWriteTapes j W i))

/-- The input tape a block of guess-writes leaves behind. -/
def guessBlockInput : ℕ → Tape → Tape
  | 0, t => transitionInput t
  | n + 1, t => guessBlockInput n (transitionInput (transitionInput t))

/-- The output tape a block of guess-writes leaves behind. -/
def guessBlockOutput : ℕ → Tape → Tape
  | 0, t => transitionTape t
  | n + 1, t => guessBlockOutput n (transitionTape (transitionTape t))

/-- **The contract of a block of guess-writes.** -/
theorem guessBlockTM_hoareTime (j : Fin (k + 1)) (hj : j ≠ Fin.last k) :
    ∀ (n : ℕ) (inp₀ out₀ : Tape) (W₀ : Fin (k + 1) → Tape),
      (guessBlockTM j n).HoareTime
        (fun inp work out => inp = inp₀ ∧ out = out₀ ∧ work = W₀)
        (fun inp work out => inp = guessBlockInput n inp₀ ∧ out = guessBlockOutput n out₀ ∧
          work = guessBlockTapes j n W₀) (2 * n + 1) := by
  intro n
  induction n with
  | zero =>
      intro inp₀ out₀ W₀
      exact guessWriteTM_hoareTime j hj inp₀ out₀ W₀
  | succ n ih =>
      intro inp₀ out₀ W₀
      have hcomp := seqTM_hoareTime (guessWriteTM j) (guessBlockTM j n)
        (guessWriteTM_hoareTime j hj inp₀ out₀ W₀)
        (h_trans := fun inp work out h => by
          obtain ⟨h1, h2, h3⟩ := h
          exact ⟨by rw [h1], by rw [h2], by rw [h3]⟩)
        (ih (transitionInput (transitionInput inp₀)) (transitionTape (transitionTape out₀))
          (fun i => transitionTape (guessWriteTapes j W₀ i)))
      have hb : 1 + 1 + (2 * n + 1) = 2 * (n + 1) + 1 := by omega
      rw [hb] at hcomp
      exact hcomp

/-! ## What a block of guesses actually leaves behind

On tapes whose heads are off the left marker — which is how every stage of an assembled machine
runs — the phase transitions are the identity, and the description collapses. -/

theorem guessBlockInput_eq_self {t : Tape} (h : t.read ≠ Γ.start) :
    ∀ n : ℕ, guessBlockInput n t = t := by
  intro n
  induction n with
  | zero => exact transitionInput_eq_self h
  | succ n ih =>
      rw [guessBlockInput, transitionInput_eq_self h, transitionInput_eq_self h]
      exact ih

theorem guessBlockOutput_eq_self {t : Tape} (h : t.read ≠ Γ.start) :
    ∀ n : ℕ, guessBlockOutput n t = t := by
  intro n
  induction n with
  | zero => exact transitionTape_eq_self h
  | succ n ih =>
      rw [guessBlockOutput, transitionTape_eq_self h, transitionTape_eq_self h]
      exact ih

theorem guessWriteTapes_last (j : Fin (k + 1)) (hj : j ≠ Fin.last k) (W : Fin (k + 1) → Tape)
    (hg : (W (Fin.last k)).read ≠ Γ.start) :
    guessWriteTapes j W (Fin.last k) = (W (Fin.last k)).move Dir3.right := by
  rw [guessWriteTapes, ite_eq_right (Ne.symm hj), ite_eq_left rfl, writeAndMove_readBack _ hg]

theorem guessWriteTapes_target (j : Fin (k + 1)) (W : Fin (k + 1) → Tape)
    (hg : (W (Fin.last k)).read ≠ Γ.start) :
    guessWriteTapes j W j = ((W j).write (W (Fin.last k)).read).move Dir3.right := by
  rw [guessWriteTapes, ite_eq_left rfl, toΓ_readBackWrite_of_ne_start hg]

theorem guessWriteTapes_other (j : Fin (k + 1)) (W : Fin (k + 1) → Tape) (i : Fin (k + 1))
    (hij : i ≠ j) (hil : i ≠ Fin.last k) (h : (W i).read ≠ Γ.start) :
    guessWriteTapes j W i = W i := by
  rw [guessWriteTapes, ite_eq_right hij, ite_eq_right hil, transitionTape_eq_self h]

theorem guessWriteTapes_target_head (j : Fin (k + 1)) (W : Fin (k + 1) → Tape)
    (hg : (W (Fin.last k)).read ≠ Γ.start) :
    (guessWriteTapes j W j).head = (W j).head + 1 := by
  rw [guessWriteTapes_target j W hg]
  show ((W j).write (W (Fin.last k)).read).head + 1 = _
  rw [Tape.write_head]

theorem guessWriteTapes_target_cells (j : Fin (k + 1)) (W : Fin (k + 1) → Tape)
    (hg : (W (Fin.last k)).read ≠ Γ.start) (hh : 1 ≤ (W j).head) :
    (guessWriteTapes j W j).cells ((W j).head) = (W (Fin.last k)).read := by
  rw [guessWriteTapes_target j W hg]
  show ((W j).write (W (Fin.last k)).read).cells ((W j).head) = _
  rw [Tape.write, ite_eq_right (by omega)]
  exact Function.update_self _ _ _

theorem guessWriteTapes_target_cells_ne (j : Fin (k + 1)) (W : Fin (k + 1) → Tape)
    (hg : (W (Fin.last k)).read ≠ Γ.start) {q : ℕ} (hq : q ≠ (W j).head) :
    (guessWriteTapes j W j).cells q = (W j).cells q := by
  rw [guessWriteTapes_target j W hg]
  show ((W j).write (W (Fin.last k)).read).cells q = _
  rw [Tape.write]
  split
  · rfl
  · exact Function.update_of_ne hq _ _

theorem guessWriteTapes_startInvariant (j : Fin (k + 1)) (W : Fin (k + 1) → Tape)
    (hinv : ∀ i, (W i).StartInvariant) (hh : ∀ i, 1 ≤ (W i).head) (i : Fin (k + 1)) :
    (guessWriteTapes j W i).StartInvariant := by
  have hg : (W (Fin.last k)).read ≠ Γ.start :=
    (hinv (Fin.last k)).read_ne_start (hh (Fin.last k))
  rw [guessWriteTapes]
  split
  · exact (hinv j).writeAndMove _ _
  · split
    · exact (hinv (Fin.last k)).writeAndMove _ _
    · rw [transitionTape_eq_self ((hinv i).read_ne_start (hh i))]
      exact hinv i

theorem guessWriteTapes_head_pos (j : Fin (k + 1)) (hj : j ≠ Fin.last k)
    (W : Fin (k + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant) (hh : ∀ i, 1 ≤ (W i).head)
    (i : Fin (k + 1)) : 1 ≤ (guessWriteTapes j W i).head := by
  have hg : (W (Fin.last k)).read ≠ Γ.start :=
    (hinv (Fin.last k)).read_ne_start (hh (Fin.last k))
  by_cases hij : i = j
  · rw [hij, guessWriteTapes_target_head j W hg]
    omega
  · by_cases hil : i = Fin.last k
    · rw [hil, guessWriteTapes_last j hj W hg]
      show 1 ≤ (W (Fin.last k)).head + 1
      omega
    · rw [guessWriteTapes_other j W i hij hil ((hinv i).read_ne_start (hh i))]
      exact hh i

/-- A block of guess-writes preserves the left-marker invariant. -/
theorem guessBlockTapes_startInvariant (j : Fin (k + 1)) (hj : j ≠ Fin.last k) :
    ∀ (n : ℕ) (W : Fin (k + 1) → Tape), (∀ i, (W i).StartInvariant) → (∀ i, 1 ≤ (W i).head) →
      ∀ i, (guessBlockTapes j n W i).StartInvariant := by
  intro n
  induction n with
  | zero => intro W hinv hh i; exact guessWriteTapes_startInvariant j W hinv hh i
  | succ n ih =>
      intro W hinv hh i
      have hinv' : ∀ i, (guessWriteTapes j W i).StartInvariant :=
        guessWriteTapes_startInvariant j W hinv hh
      have hh' : ∀ i, 1 ≤ (guessWriteTapes j W i).head :=
        guessWriteTapes_head_pos j hj W hinv hh
      rw [guessBlockTapes]
      refine ih _ (fun i => ?_) (fun i => ?_) i
      · rw [transitionTape_eq_self ((hinv' i).read_ne_start (hh' i))]; exact hinv' i
      · rw [transitionTape_eq_self ((hinv' i).read_ne_start (hh' i))]; exact hh' i

/-- **What a block of guess-writes leaves behind.** The guess tape and the target have both
advanced by the number of bits written, the target's cells hold those bits, its earlier cells and
every other tape are untouched. -/
theorem guessBlockTapes_spec (j : Fin (k + 1)) (hj : j ≠ Fin.last k) :
    ∀ (n : ℕ) (W : Fin (k + 1) → Tape), (∀ i, (W i).StartInvariant) → (∀ i, 1 ≤ (W i).head) →
      guessBlockTapes j n W (Fin.last k)
          = ⟨(W (Fin.last k)).head + (n + 1), (W (Fin.last k)).cells⟩ ∧
        (guessBlockTapes j n W j).head = (W j).head + (n + 1) ∧
        (∀ i, i ≠ j → i ≠ Fin.last k → guessBlockTapes j n W i = W i) ∧
        (∀ q < (W j).head, (guessBlockTapes j n W j).cells q = (W j).cells q) ∧
        (∀ p ≤ n, (guessBlockTapes j n W j).cells ((W j).head + p)
          = (W (Fin.last k)).cells ((W (Fin.last k)).head + p)) := by
  intro n
  induction n with
  | zero =>
      intro W hinv hh
      have hg : (W (Fin.last k)).read ≠ Γ.start :=
        (hinv (Fin.last k)).read_ne_start (hh (Fin.last k))
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [guessBlockTapes, guessWriteTapes_last j hj W hg]
        rfl
      · rw [guessBlockTapes, guessWriteTapes_target_head j W hg]
      · intro i hij hil
        rw [guessBlockTapes, guessWriteTapes_other j W i hij hil ((hinv i).read_ne_start (hh i))]
      · intro q hq
        rw [guessBlockTapes, guessWriteTapes_target_cells_ne j W hg (by omega)]
      · intro p hp
        have hp0 : p = 0 := by omega
        rw [hp0, guessBlockTapes, Nat.add_zero, Nat.add_zero,
          guessWriteTapes_target_cells j W hg (hh j)]
        rfl
  | succ n ih =>
      intro W hinv hh
      have hg : (W (Fin.last k)).read ≠ Γ.start :=
        (hinv (Fin.last k)).read_ne_start (hh (Fin.last k))
      have hinv' : ∀ i, (guessWriteTapes j W i).StartInvariant :=
        guessWriteTapes_startInvariant j W hinv hh
      have hh' : ∀ i, 1 ≤ (guessWriteTapes j W i).head :=
        guessWriteTapes_head_pos j hj W hinv hh
      have hstep : guessBlockTapes j (n + 1) W = guessBlockTapes j n (guessWriteTapes j W) := by
        rw [guessBlockTapes]
        congr 1
        funext i
        exact transitionTape_eq_self ((hinv' i).read_ne_start (hh' i))
      obtain ⟨i1, i2, i3, i4, i5⟩ := ih (guessWriteTapes j W) hinv' hh'
      have hlast : guessWriteTapes j W (Fin.last k)
          = ⟨(W (Fin.last k)).head + 1, (W (Fin.last k)).cells⟩ := by
        rw [guessWriteTapes_last j hj W hg]
        rfl
      have hjh : (guessWriteTapes j W j).head = (W j).head + 1 :=
        guessWriteTapes_target_head j W hg
      rw [hstep]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [i1, hlast]
        show (⟨(W (Fin.last k)).head + 1 + (n + 1), (W (Fin.last k)).cells⟩ : Tape) = _
        congr 1
        omega
      · rw [i2, hjh]
        omega
      · intro i hij hil
        rw [i3 i hij hil, guessWriteTapes_other j W i hij hil ((hinv i).read_ne_start (hh i))]
      · intro q hq
        rw [i4 q (by omega), guessWriteTapes_target_cells_ne j W hg (by omega)]
      · intro p hp
        rcases Nat.eq_zero_or_pos p with hp0 | hp0
        · rw [hp0, Nat.add_zero, i4 ((W j).head) (by omega),
            guessWriteTapes_target_cells j W hg (hh j)]
          rfl
        · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
          have hq := i5 q (by omega)
          rw [hjh, hlast] at hq
          rw [show (W j).head + (q + 1) = (W j).head + 1 + q by omega, hq]
          show (W (Fin.last k)).cells ((W (Fin.last k)).head + 1 + q) = _
          congr 1
          omega

/-- **A block of guesses respects the protocol.** -/
theorem guessProtocol_guessBlockTM (j : Fin (k + 1)) :
    ∀ n : ℕ, GuessProtocol (guessBlockTM j n) (guessBlockAdv j n) := by
  intro n
  induction n with
  | zero => exact guessProtocol_guessWriteTM j
  | succ n ih => exact guessProtocol_seqTM (guessProtocol_guessWriteTM j) ih

/-! ## Several blocks of guesses

A configuration is spread over several registers, so guessing one means writing a block into each.
The registers are addressed by index, so no placement is involved. -/

/-- The do-nothing machine never consults the guess tape. -/
theorem guessProtocol_skipTM : GuessProtocol (skipTM (n := k + 1)) (fun _ => false) := by
  refine ⟨fun q _ iHead wHeads oHead => rfl, fun q _ iHead wHeads oHead h => ?_,
    fun q _ _ iHead ww oHead g g' => ?_⟩
  · show idleDir (wHeads (Fin.last k)) = _
    rw [idleDir, ite_eq_right h]
    simp
  · simp [visible, skipTM]

/-- **The do-nothing machine's contract**, in the pinned form the guess stages use: one step, and
every tape passes through the phase transition. -/
theorem skipTM_hoareTime' (inp₀ out₀ : Tape) (W₀ : Fin (k + 1) → Tape) :
    (skipTM (n := k + 1)).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧ work = W₀)
      (fun inp work out => inp = transitionInput inp₀ ∧ out = transitionTape out₀ ∧
        work = fun i => transitionTape (W₀ i)) 1 := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  have hne : (skipTM (n := k + 1)).qstart ≠ (skipTM (n := k + 1)).qhalt := by
    intro h
    exact BumpPhase.noConfusion h
  refine ⟨(skipTM (n := k + 1)).stepCfg
    { state := (skipTM (n := k + 1)).qstart, input := inp, work := work, output := out },
    1, le_rfl, reachesIn.step (step_of_not_halted _ hne) reachesIn.zero, rfl, rfl, rfl, rfl⟩

/-- A block of guess-writes leaves every head off the left marker. -/
theorem guessBlockTapes_head_pos (j : Fin (k + 1)) (hj : j ≠ Fin.last k) (n : ℕ)
    (W : Fin (k + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant) (hh : ∀ i, 1 ≤ (W i).head)
    (i : Fin (k + 1)) : 1 ≤ (guessBlockTapes j n W i).head := by
  obtain ⟨hlast, hjhead, hother, -, -⟩ := guessBlockTapes_spec j hj n W hinv hh
  by_cases hil : i = Fin.last k
  · rw [hil, hlast]
    have := hh (Fin.last k)
    show 1 ≤ (W (Fin.last k)).head + (n + 1)
    omega
  · by_cases hij : i = j
    · rw [hij, hjhead]
      have := hh j
      omega
    · rw [hother i hij hil]
      exact hh i

/-- Where block `p`'s guesses sit on the guess tape: each block consumes one cell per bit plus
one for the block's final advance. -/
def guessOffset (w : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | p + 1 => guessOffset w p + (w p + 1)

/-- Offsets grow with the number of blocks. -/
theorem guessOffset_le (w : ℕ → ℕ) : ∀ {p t : ℕ}, p ≤ t → guessOffset w p ≤ guessOffset w t := by
  intro p t
  induction t with
  | zero => intro h; rw [Nat.le_zero.mp h]
  | succ t ih =>
      intro h
      rcases Nat.lt_or_ge p (t + 1) with hp | hp
      · have := ih (by omega)
        rw [guessOffset]
        omega
      · rw [show p = t + 1 by omega]

/-- The bits of a family of blocks, laid end to end: this is the guess stream that makes each
register of `TM.guessBlocksTM` hold what the caller wants it to hold. -/
def guessList (w : ℕ → ℕ) (b : ℕ → ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | p + 1 => guessList w b p ++ List.ofFn (fun q : Fin (w p + 1) => b p q.val)

@[simp] theorem guessList_length (w : ℕ → ℕ) (b : ℕ → ℕ → Bool) (t : ℕ) :
    (guessList w b t).length = guessOffset w t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [guessList, guessOffset, List.length_append, ih, List.length_ofFn]

/-- **Block `p`'s bits sit at offset `guessOffset w p`.** -/
theorem guessList_getElem (w : ℕ → ℕ) (b : ℕ → ℕ → Bool) :
    ∀ (t p q : ℕ), p < t → q ≤ w p →
      (guessList w b t)[guessOffset w p + q]? = some (b p q) := by
  intro t
  induction t with
  | zero => intro p q hp; omega
  | succ t ih =>
      intro p q hp hq
      rw [guessList]
      rcases Nat.lt_or_ge p t with hpt | hpt
      · have hlt : guessOffset w p + q < (guessList w b t).length := by
          have h1 : guessOffset w (p + 1) ≤ guessOffset w t := guessOffset_le w hpt
          rw [guessList_length]
          rw [guessOffset] at h1
          omega
        rw [List.getElem?_append_left hlt]
        exact ih p q hpt hq
      · have hpe : p = t := by omega
        subst hpe
        have hge : (guessList w b p).length ≤ guessOffset w p + q := by
          rw [guessList_length]; omega
        rw [List.getElem?_append_right hge, guessList_length,
          show guessOffset w p + q - guessOffset w p = q by omega]
        rw [List.getElem?_ofFn]
        simp [hq, Nat.lt_succ_of_le]

/-- Write a block of guesses into each of `t` registers in turn. -/
def guessBlocksTM (j : ℕ → Fin (k + 1)) (w : ℕ → ℕ) : ℕ → TM (k + 1)
  | 0 => skipTM
  | t + 1 => seqTM (guessBlocksTM j w t) (guessBlockTM (j t) (w t))

/-- Its advancing states. -/
def guessBlocksAdv (j : ℕ → Fin (k + 1)) (w : ℕ → ℕ) :
    (t : ℕ) → (guessBlocksTM j w t).Q → Bool
  | 0 => fun _ => false
  | t + 1 => seqAdv (guessBlocksAdv j w t) (guessBlockAdv (j t) (w t))

/-- The tapes several blocks of guesses leave behind. -/
def guessBlocksTapes (j : ℕ → Fin (k + 1)) (w : ℕ → ℕ) :
    ℕ → (Fin (k + 1) → Tape) → (Fin (k + 1) → Tape)
  | 0, W => fun i => transitionTape (W i)
  | t + 1, W => guessBlockTapes (j t) (w t)
      (fun i => transitionTape (guessBlocksTapes j w t W i))

/-- **A guessed block leaves the tape beyond it untouched.** The blank that stops a scan belongs
to the tape, not to the guess, so it has to survive the guess. -/
theorem guessBlockTapes_beyond (j : Fin (k + 1)) (hj : j ≠ Fin.last k) :
    ∀ (n : ℕ) (W : Fin (k + 1) → Tape), (∀ i, (W i).StartInvariant) → (∀ i, 1 ≤ (W i).head) →
      ∀ q, (W j).head + n < q → (guessBlockTapes j n W j).cells q = (W j).cells q := by
  intro n
  induction n with
  | zero =>
      intro W hinv hh q hq
      have hg : (W (Fin.last k)).read ≠ Γ.start :=
        (hinv (Fin.last k)).read_ne_start (hh (Fin.last k))
      rw [guessBlockTapes, guessWriteTapes_target_cells_ne j W hg (by omega)]
  | succ n ih =>
      intro W hinv hh q hq
      have hg : (W (Fin.last k)).read ≠ Γ.start :=
        (hinv (Fin.last k)).read_ne_start (hh (Fin.last k))
      have hinv' : ∀ i, (guessWriteTapes j W i).StartInvariant :=
        guessWriteTapes_startInvariant j W hinv hh
      have hh' : ∀ i, 1 ≤ (guessWriteTapes j W i).head :=
        guessWriteTapes_head_pos j hj W hinv hh
      have hstep : guessBlockTapes j (n + 1) W = guessBlockTapes j n (guessWriteTapes j W) := by
        rw [guessBlockTapes]
        congr 1
        funext i
        exact transitionTape_eq_self ((hinv' i).read_ne_start (hh' i))
      have hjh : (guessWriteTapes j W j).head = (W j).head + 1 :=
        guessWriteTapes_target_head j W hg
      rw [hstep, ih (guessWriteTapes j W) hinv' hh' q (by rw [hjh]; omega),
        guessWriteTapes_target_cells_ne j W hg (by omega)]

/-- **What several blocks of guesses leave behind.** When the target registers are distinct, each
one ends up holding its own block of guessed bits, read off the guess tape at that block's
offset — which is what lets a stage guess a whole structured object at once. -/
theorem guessBlocksTapes_spec (j : ℕ → Fin (k + 1)) (hj : ∀ p, j p ≠ Fin.last k) (w : ℕ → ℕ) :
    ∀ (t : ℕ) (W : Fin (k + 1) → Tape), (∀ i, (W i).StartInvariant) → (∀ i, 1 ≤ (W i).head) →
      (∀ p q, p < t → q < t → j p = j q → p = q) →
      (∀ i, (guessBlocksTapes j w t W i).StartInvariant) ∧
      (∀ i, 1 ≤ (guessBlocksTapes j w t W i).head) ∧
      guessBlocksTapes j w t W (Fin.last k)
          = ⟨(W (Fin.last k)).head + guessOffset w t, (W (Fin.last k)).cells⟩ ∧
      (∀ i, i ≠ Fin.last k → (∀ p, p < t → i ≠ j p) → guessBlocksTapes j w t W i = W i) ∧
      (∀ p, p < t →
        (guessBlocksTapes j w t W (j p)).head = (W (j p)).head + (w p + 1) ∧
        ∀ q, q ≤ w p → (guessBlocksTapes j w t W (j p)).cells ((W (j p)).head + q)
          = (W (Fin.last k)).cells ((W (Fin.last k)).head + guessOffset w p + q)) := by
  intro t
  induction t with
  | zero =>
      intro W hinv hh _
      have hid : ∀ i, transitionTape (W i) = W i := fun i =>
        transitionTape_eq_self ((hinv i).read_ne_start (hh i))
      refine ⟨fun i => ?_, fun i => ?_, ?_, fun i _ _ => ?_, fun p hp => absurd hp (by omega)⟩
      · rw [guessBlocksTapes]; simp only []; rw [hid]; exact hinv i
      · rw [guessBlocksTapes]; simp only []; rw [hid]; exact hh i
      · rw [guessBlocksTapes]; simp only []; rw [hid]; rfl
      · rw [guessBlocksTapes]; simp only []; rw [hid]
  | succ t ih =>
      intro W hinv hh hinj
      obtain ⟨uinv, uhh, ulast, uother, ublk⟩ :=
        ih W hinv hh (fun p q hp hq h => hinj p q (by omega) (by omega) h)
      have hstep : guessBlocksTapes j w (t + 1) W
          = guessBlockTapes (j t) (w t) (guessBlocksTapes j w t W) := by
        rw [guessBlocksTapes]
        congr 1
        funext i
        exact transitionTape_eq_self ((uinv i).read_ne_start (uhh i))
      obtain ⟨blast, bhead, bother, -, bcells⟩ :=
        guessBlockTapes_spec (j t) (hj t) (w t) (guessBlocksTapes j w t W) uinv uhh
      have huj : guessBlocksTapes j w t W (j t) = W (j t) :=
        uother (j t) (hj t) (fun p hp h => absurd (hinj t p (by omega) (by omega) h) (by omega))
      refine ⟨fun i => ?_, fun i => ?_, ?_, fun i hil hip => ?_, fun p hp => ?_⟩
      · rw [hstep]
        exact guessBlockTapes_startInvariant (j t) (hj t) (w t) _ uinv uhh i
      · rw [hstep]
        exact guessBlockTapes_head_pos (j t) (hj t) (w t) _ uinv uhh i
      · rw [hstep, blast, ulast]
        simp [guessOffset, Nat.add_assoc]
      · rw [hstep, bother i (hip t (by omega)) hil]
        exact uother i hil (fun p hp => hip p (by omega))
      · rcases Nat.lt_or_ge p t with hpt | hpt
        · have hne : j p ≠ j t := fun h =>
            absurd (hinj p t (by omega) (by omega) h) (by omega)
          rw [hstep, bother (j p) hne (hj p)]
          exact ublk p hpt
        · have hpe : p = t := by omega
          subst hpe
          refine ⟨?_, fun q hq => ?_⟩
          · rw [hstep, bhead, huj]
          · rw [hstep, ← huj, bcells q hq, ulast]

/-- **And so do several blocks.** A register is written by at most one block, so beyond that
block's own width its cells are the ones it started with. -/
theorem guessBlocksTapes_beyond (j : ℕ → Fin (k + 1)) (hj : ∀ p, j p ≠ Fin.last k) (w : ℕ → ℕ) :
    ∀ (t : ℕ) (W : Fin (k + 1) → Tape), (∀ i, (W i).StartInvariant) → (∀ i, 1 ≤ (W i).head) →
      (∀ p q, p < t → q < t → j p = j q → p = q) →
      ∀ p, p < t → ∀ q, (W (j p)).head + w p < q →
        (guessBlocksTapes j w t W (j p)).cells q = (W (j p)).cells q := by
  intro t
  induction t with
  | zero => intro _ _ _ _ p hp; exact absurd hp (by omega)
  | succ t ih =>
      intro W hinv hh hinj p hp q hq
      obtain ⟨uinv, uhh, -, uother, -⟩ :=
        guessBlocksTapes_spec j hj w t W hinv hh
          (fun p q hp hq h => hinj p q (by omega) (by omega) h)
      have hstep : guessBlocksTapes j w (t + 1) W
          = guessBlockTapes (j t) (w t) (guessBlocksTapes j w t W) := by
        rw [guessBlocksTapes]
        congr 1
        funext i
        exact transitionTape_eq_self ((uinv i).read_ne_start (uhh i))
      have huj : guessBlocksTapes j w t W (j t) = W (j t) :=
        uother (j t) (hj t) (fun p hp h => absurd (hinj t p (by omega) (by omega) h) (by omega))
      rcases Nat.lt_or_ge p t with hpt | hpt
      · have hne : j p ≠ j t := fun h =>
          absurd (hinj p t (by omega) (by omega) h) (by omega)
        rw [hstep, (guessBlockTapes_spec (j t) (hj t) (w t) (guessBlocksTapes j w t W) uinv
          uhh).2.2.1 (j p) hne (hj p)]
        exact ih W hinv hh (fun p q hp hq h => hinj p q (by omega) (by omega) h) p hpt q hq
      · have hpe : p = t := by omega
        subst hpe
        have h := guessBlockTapes_beyond (j p) (hj p) (w p) (guessBlocksTapes j w p W) uinv uhh q
          (by rw [huj]; exact hq)
        rw [hstep, h, huj]

/-- The input tape they leave behind. -/
def guessBlocksInput (w : ℕ → ℕ) : ℕ → Tape → Tape
  | 0, t => transitionInput t
  | s + 1, t => guessBlockInput (w s) (transitionInput (guessBlocksInput w s t))

/-- The output tape they leave behind. -/
def guessBlocksOutput (w : ℕ → ℕ) : ℕ → Tape → Tape
  | 0, t => transitionTape t
  | s + 1, t => guessBlockOutput (w s) (transitionTape (guessBlocksOutput w s t))

/-- Several blocks of guesses leave a parked input tape alone. -/
theorem guessBlocksInput_eq_self {t : Tape} (h : t.read ≠ Γ.start) (w : ℕ → ℕ) :
    ∀ s : ℕ, guessBlocksInput w s t = t := by
  intro s
  induction s with
  | zero => exact transitionInput_eq_self h
  | succ s ih =>
      rw [guessBlocksInput, ih, transitionInput_eq_self h, guessBlockInput_eq_self h]

/-- Several blocks of guesses leave a parked output tape alone. -/
theorem guessBlocksOutput_eq_self {t : Tape} (h : t.read ≠ Γ.start) (w : ℕ → ℕ) :
    ∀ s : ℕ, guessBlocksOutput w s t = t := by
  intro s
  induction s with
  | zero => exact transitionTape_eq_self h
  | succ s ih =>
      rw [guessBlocksOutput, ih, transitionTape_eq_self h, guessBlockOutput_eq_self h]

/-- How long several blocks of guesses take. -/
def guessBlocksTime (w : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | t + 1 => guessBlocksTime w t + 1 + (2 * w t + 1)

/-- **The contract of several blocks of guesses.** -/
theorem guessBlocksTM_hoareTime (j : ℕ → Fin (k + 1)) (hj : ∀ t, j t ≠ Fin.last k)
    (w : ℕ → ℕ) :
    ∀ (t : ℕ) (inp₀ out₀ : Tape) (W₀ : Fin (k + 1) → Tape),
      (guessBlocksTM j w t).HoareTime
        (fun inp work out => inp = inp₀ ∧ out = out₀ ∧ work = W₀)
        (fun inp work out => inp = guessBlocksInput w t inp₀ ∧
          out = guessBlocksOutput w t out₀ ∧ work = guessBlocksTapes j w t W₀)
        (guessBlocksTime w t) := by
  intro t
  induction t with
  | zero =>
      intro inp₀ out₀ W₀
      exact skipTM_hoareTime' inp₀ out₀ W₀
  | succ t ih =>
      intro inp₀ out₀ W₀
      have hcomp := seqTM_hoareTime (guessBlocksTM j w t) (guessBlockTM (j t) (w t))
        (ih inp₀ out₀ W₀)
        (h_trans := fun inp work out h => by
          obtain ⟨h1, h2, h3⟩ := h
          exact ⟨by rw [h1], by rw [h2], by rw [h3]⟩)
        (guessBlockTM_hoareTime (j t) (hj t) (w t)
          (transitionInput (guessBlocksInput w t inp₀))
          (transitionTape (guessBlocksOutput w t out₀))
          (fun i => transitionTape (guessBlocksTapes j w t W₀ i)))
      exact hcomp

/-- **Several blocks of guesses respect the protocol.** -/
theorem guessProtocol_guessBlocksTM (j : ℕ → Fin (k + 1)) (w : ℕ → ℕ) :
    ∀ t : ℕ, GuessProtocol (guessBlocksTM j w t) (guessBlocksAdv j w t) := by
  intro t
  induction t with
  | zero => exact guessProtocol_skipTM
  | succ t ih => exact guessProtocol_seqTM ih (guessProtocol_guessBlockTM (j t) (w t))

/-- **Guess, then check.** Every stage of a guess-and-verify machine has this shape: write some
blocks of guesses onto the registers, then run a guess-free machine on them. -/
def guessThenTM (j : ℕ → Fin (k + 1)) (w : ℕ → ℕ) (t : ℕ) (D : TM k) : TM (k + 1) :=
  seqTM (guessBlocksTM j w t) (liftLast D)

/-- **A guess-and-check stage respects the protocol.** -/
theorem guessProtocol_guessThenTM (j : ℕ → Fin (k + 1)) (w : ℕ → ℕ) (t : ℕ) (D : TM k) :
    GuessProtocol (guessThenTM j w t D)
      (seqAdv (guessBlocksAdv j w t) (fun _ => false)) :=
  guessProtocol_seqTM (guessProtocol_guessBlocksTM j w t) (guessProtocol_liftLast D)

/-- **The contract of a guess-and-check stage.** The caller says what the guessed tapes give the
checking machine; this composes the two halves. -/
theorem guessThenTM_hoareTime (j : ℕ → Fin (k + 1)) (hj : ∀ t, j t ≠ Fin.last k) (w : ℕ → ℕ)
    (t : ℕ) (D : TM k) {mid post : TapePred (k + 1)} {b : ℕ}
    (inp₀ out₀ : Tape) (W₀ : Fin (k + 1) → Tape)
    (h_trans : ∀ inp work out,
      (inp = guessBlocksInput w t inp₀ ∧ out = guessBlocksOutput w t out₀ ∧
        work = guessBlocksTapes j w t W₀) →
      mid (transitionInput inp) (fun i => transitionTape (work i)) (transitionTape out))
    (hD : (liftLast D).HoareTime mid post b) :
    (guessThenTM j w t D).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧ work = W₀) post
      (guessBlocksTime w t + 1 + b) :=
  seqTM_hoareTime (guessBlocksTM j w t) (liftLast D)
    (guessBlocksTM_hoareTime j hj w t inp₀ out₀ W₀) h_trans hD

/-! ## What the guess tape still holds

A stage consumes a prefix of the guess tape and leaves the rest for the stages after it. Stating
that as a predicate on the tape lets a loop carry it as an invariant: each iteration shifts the
stream by the bits it used. -/

/-- The guess tape carries the bits of `g` from its head onward. -/
def GuessFrom (g : ℕ → Bool) (t : Tape) : Prop :=
  ∀ q, t.cells (t.head + q) = Γ.ofBool (g q)

/-- **A loaded guess tape carries its stream.** -/
theorem guessFrom_loadTape (g : ℕ → Bool) : GuessFrom g (NTM.loadTape g) := by
  intro q
  show (NTM.loadTape g).cells (1 + q) = _
  rw [show 1 + q = q + 1 by omega, NTM.loadTape_cells_succ]

/-- **A stage's blocks are read off the stream at their offsets.** -/
theorem guessFrom_blocks {g : ℕ → Bool} {t : Tape} (h : GuessFrom g t) (w : ℕ → ℕ) (p q : ℕ) :
    t.cells (t.head + guessOffset w p + q) = Γ.ofBool (g (guessOffset w p + q)) := by
  rw [show t.head + guessOffset w p + q = t.head + (guessOffset w p + q) by omega]
  exact h (guessOffset w p + q)

/-- **A stage consumes a prefix and leaves the rest.** -/
theorem guessFrom_after (j : ℕ → Fin (k + 1)) (hj : ∀ p, j p ≠ Fin.last k) (w : ℕ → ℕ) (t : ℕ)
    (W : Fin (k + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant) (hh : ∀ i, 1 ≤ (W i).head)
    (hinj : ∀ p q, p < t → q < t → j p = j q → p = q) (g : ℕ → Bool)
    (hg : GuessFrom g (W (Fin.last k))) :
    GuessFrom (fun q => g (guessOffset w t + q)) (guessBlocksTapes j w t W (Fin.last k)) := by
  obtain ⟨-, -, hlast, -, -⟩ := guessBlocksTapes_spec j hj w t W hinv hh hinj
  intro q
  rw [hlast]
  show (W (Fin.last k)).cells ((W (Fin.last k)).head + guessOffset w t + q) = _
  exact guessFrom_blocks hg w t q

/-! ## A stream that feeds every stage

A machine that guesses in a loop consumes one stage's worth of bits per pass. Saying what the
whole guess tape must contain is then a statement about a doubly-indexed family: stage `s`, block
`p`, bit `q`. Such a stream always exists — the offsets of distinct stages and blocks never
collide. -/

/-- The stream gives stage `s` its block `p`'s bit `q`. -/
def StageBlocks (w : ℕ → ℕ) (t : ℕ) (b : ℕ → ℕ → ℕ → Bool) (g : ℕ → Bool) : Prop :=
  ∀ s p q, p < t → q ≤ w p → g (s * guessOffset w t + (guessOffset w p + q)) = b s p q

theorem guessOffset_pos (w : ℕ → ℕ) {t : ℕ} (ht : 0 < t) : 0 < guessOffset w t := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [guessOffset]
  omega

theorem guessOffset_lt (w : ℕ → ℕ) {t p q : ℕ} (hp : p < t) (hq : q ≤ w p) :
    guessOffset w p + q < guessOffset w t := by
  have h : guessOffset w (p + 1) ≤ guessOffset w t := guessOffset_le w hp
  rw [guessOffset] at h
  omega

/-- **Every family of stages is realized by some stream.** -/
theorem exists_stageBlocks (w : ℕ → ℕ) {t : ℕ} (ht : 0 < t) (b : ℕ → ℕ → ℕ → Bool) :
    ∃ g : ℕ → Bool, StageBlocks w t b g := by
  classical
  refine ⟨fun o => ((guessList w (b (o / guessOffset w t)) t)[o % guessOffset w t]?).getD false,
    ?_⟩
  intro s p q hp hq
  have hG : 0 < guessOffset w t := guessOffset_pos w ht
  have hlt : guessOffset w p + q < guessOffset w t := guessOffset_lt w hp hq
  have hdiv : (s * guessOffset w t + (guessOffset w p + q)) / guessOffset w t = s := by
    rw [show s * guessOffset w t + (guessOffset w p + q)
      = (guessOffset w p + q) + s * guessOffset w t by omega,
      Nat.add_mul_div_right _ _ hG, Nat.div_eq_of_lt hlt, Nat.zero_add]
  have hmod : (s * guessOffset w t + (guessOffset w p + q)) % guessOffset w t
      = guessOffset w p + q := by
    rw [show s * guessOffset w t + (guessOffset w p + q)
      = (guessOffset w p + q) + s * guessOffset w t by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  show ((guessList w (b _) t)[_]?).getD false = _
  rw [hdiv, hmod, guessList_getElem w (b s) t p q hp hq]
  rfl

/-- **A stage reads its own blocks off the stream.** This is the hypothesis a guess stage's
contract asks for, supplied by the loop invariant's guess-tape clause. -/
theorem blocks_of_stageBlocks {w : ℕ → ℕ} {t : ℕ} {b : ℕ → ℕ → ℕ → Bool} {g : ℕ → Bool}
    (hs : StageBlocks w t b g) (s : ℕ) {τ : Tape}
    (hgf : GuessFrom (fun q => g (s * guessOffset w t + q)) τ) :
    ∀ p, p < t → ∀ q, q ≤ w p → τ.cells (τ.head + guessOffset w p + q) = Γ.ofBool (b s p q) := by
  intro p hp q hq
  rw [guessFrom_blocks hgf w p q, hs s p q hp hq]

/-! ## A whole guess-and-rewind stage -/

/-- **A guess stage.** Write a block of guesses onto each of `t` registers, then bring the named
registers' heads back to cell one — the form every scan expects to read. The input head is left
alone: a machine simulating another one keeps its input head where the simulation put it. -/
def guessStageTM (j : ℕ → Fin (k + 1)) (w : ℕ → ℕ) (t : ℕ) (targets : List (Fin k)) :
    TM (k + 1) :=
  guessThenTM j w t (parkRewindWorkTM targets)

/-- **A guess stage respects the protocol.** -/
theorem guessProtocol_guessStageTM (j : ℕ → Fin (k + 1)) (w : ℕ → ℕ) (t : ℕ)
    (targets : List (Fin k)) :
    GuessProtocol (guessStageTM j w t targets)
      (seqAdv (guessBlocksAdv j w t) (fun _ => false)) :=
  guessProtocol_guessThenTM j w t (parkRewindWorkTM targets)

/-- **The contract of a guess stage.** -/
theorem guessStageTM_hoareTime (j : ℕ → Fin (k + 1)) (hj : ∀ p, j p ≠ Fin.last k) (w : ℕ → ℕ)
    (t : ℕ) (targets : List (Fin k)) (hnodup : targets.Nodup) (B : ℕ) (hB : 1 ≤ B)
    (inp₀ out₀ : Tape) (W₀ : Fin (k + 1) → Tape)
    (hinpSI : inp₀.StartInvariant) (houtSI : out₀.StartInvariant)
    (hinp : inp₀.read ≠ Γ.start) (hout : out₀.read ≠ Γ.start)
    (hinvW : ∀ i, (W₀ i).StartInvariant) (hhW : ∀ i, 1 ≤ (W₀ i).head)
    (hinj : ∀ p q, p < t → q < t → j p = j q → p = q)
    (hbound : ∀ i, i ∈ targets → (guessBlocksTapes j w t W₀ i.castSucc).head ≤ B) :
    (guessStageTM j w t targets).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧ work = W₀)
      (fun inp work out =>
        work (Fin.last k) = guessBlocksTapes j w t W₀ (Fin.last k) ∧
        inp = parkTape inp₀ ∧
        (fun i => work i.castSucc)
            = (fun i => if i ∈ targets
                then (⟨1, (guessBlocksTapes j w t W₀ i.castSucc).cells⟩ : Tape)
                else parkTape (guessBlocksTapes j w t W₀ i.castSucc)) ∧
        out = parkTape out₀)
      (guessBlocksTime w t + 1 + (1 + 1 + (targets.length * (B + 3) + 1))) := by
  obtain ⟨ginv, ghh, -, -, -⟩ := guessBlocksTapes_spec j hj w t W₀ hinvW hhW hinj
  have gns : ∀ i, (guessBlocksTapes j w t W₀ i).read ≠ Γ.start :=
    fun i => (ginv i).read_ne_start (ghh i)
  refine guessThenTM_hoareTime j hj w t (parkRewindWorkTM targets) inp₀ out₀ W₀ ?_
    (liftLast_hoareTime (parkRewindWorkTM targets)
      (parkRewindWorkTM_hoareTime targets hnodup B hB inp₀
        (fun i => guessBlocksTapes j w t W₀ i.castSucc) out₀ hinpSI
        (fun i => ginv i.castSucc) houtSI hbound)
      (guessBlocksTapes j w t W₀ (Fin.last k)) (gns (Fin.last k)))
  rintro inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨transitionTape_eq_self (gns (Fin.last k)), ?_, ?_, ?_⟩
  · rw [guessBlocksInput_eq_self hinp, transitionInput_eq_self hinp]
  · funext i
    exact transitionTape_eq_self (gns i.castSucc)
  · rw [guessBlocksOutput_eq_self hout, transitionTape_eq_self hout]

end TM

end Complexity
