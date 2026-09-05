/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.SAT.Language
public import Complexitylib.Classes.NP.Internal.PairBuildTM
public import Complexitylib.Models.TuringMachine.Subroutines.GuessBounded
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Retarget

/-!
# SAT-specialized guess-and-verify NTM

This file implements the concrete SAT route to NP. It avoids the still-open
generic `NP.WitnessNTMConstruction` by using the proved linear counter
subroutine for SAT witnesses, whose length is bounded by `|x| + 1`. The final
theorems prove the composed machine decides `language` in polynomial time from a
polynomial-time verifier.

The machine is parameterized by a verifier DTM `M : TM k` for
`pairLang Witness`.  Its work-tape layout is:

- `0 .. k-1`: verifier-internal work tapes,
- `k`: pair tape, used as the virtual input for `M`,
- `k+1`: guessed witness tape,
- `k+2`: unary counter tape.

The state space is a direct sequence of the existing subroutine phases:
counter setup, input rewind, bounded guessing, pair building, and verifier
simulation.
-/


@[expose] public section

namespace Complexity

namespace SAT

open Complexity TM

variable {k : ℕ}

/-- Deterministic setup budget for the SAT-specialized machine before pair
    construction starts: build the `|x|+1` counter, rewind the input, and run
    the bounded guessing subroutine through its phase exit. -/
def satGuessVerifySetupTime (n : ℕ) : ℕ :=
  TM.inputLengthPlusOneCounterTime n + 1 +
    (TM.inputLengthPlusOneCounterTime n + 1 + 2 + 1 +
      (NTM.guessBoundedTime (n + 1) 0 + 1))

/-- A uniform verifier-time window for all witnesses of length at most
    `n + 1`.  We take a finite maximum because the verifier bound `f` is not
    assumed monotone. -/
def satVerifierWindowTime (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  (Finset.range (n + 2)).sup fun m => f (2 * n + 2 + m)

/-- SAT-specialized witness-independent run budget induced by a verifier bound
    `f`. -/
def satGuessVerifyTime (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  satGuessVerifySetupTime n +
    (TM.pairBuildTime n (n + 1) + satVerifierWindowTime f n)

/-- The verifier window bound dominates `f` on any pair `⟨x, y⟩` whose witness
    `y` has length at most `|x| + 1`. -/
theorem satVerifierWindowTime_bounds_pair (f : ℕ → ℕ) (x y : List Bool)
    (hlen : y.length ≤ x.length + 1) :
    f (pair x y).length ≤ satVerifierWindowTime f x.length := by
  rw [pair_length]
  unfold satVerifierWindowTime
  exact Finset.le_sup (s := Finset.range (x.length + 2))
    (f := fun m => f (2 * x.length + 2 + m))
    (by rw [Finset.mem_range]; omega)

/-- Work-tape index for the pair/virtual-input tape. -/
def satPairIdx (k : ℕ) : Fin (k + 3) := ⟨k, by omega⟩

/-- Work-tape index for the guessed witness tape. -/
def satWitnessIdx (k : ℕ) : Fin (k + 3) := ⟨k + 1, by omega⟩

/-- Work-tape index for the unary guess-bound counter. -/
def satCounterIdx (k : ℕ) : Fin (k + 3) := ⟨k + 2, by omega⟩

/-- Embed a verifier-internal work-tape index into the SAT machine layout. -/
def satVerifierWorkIdx {k : ℕ} (i : Fin k) : Fin (k + 3) :=
  ⟨i.val, by omega⟩

/-- The witness tape and the pair tape are distinct work tapes. -/
theorem satWitnessIdx_ne_pairIdx (k : ℕ) : satWitnessIdx k ≠ satPairIdx k := by
  intro h
  have := congrArg Fin.val h
  simp [satWitnessIdx, satPairIdx] at this

/-- The counter tape and the pair tape are distinct work tapes. -/
theorem satCounterIdx_ne_pairIdx (k : ℕ) : satCounterIdx k ≠ satPairIdx k := by
  intro h
  have := congrArg Fin.val h
  simp [satCounterIdx, satPairIdx] at this

/-- The counter tape and the witness tape are distinct work tapes. -/
theorem satCounterIdx_ne_witnessIdx (k : ℕ) : satCounterIdx k ≠ satWitnessIdx k := by
  intro h
  have := congrArg Fin.val h
  simp [satCounterIdx, satWitnessIdx] at this

/-- Embedded verifier work tapes are distinct from the pair tape. -/
theorem satVerifierWorkIdx_ne_pairIdx {k : ℕ} (i : Fin k) :
    satVerifierWorkIdx i ≠ satPairIdx k := by
  intro h
  have := congrArg Fin.val h
  simp [satVerifierWorkIdx, satPairIdx] at this
  omega

/-- Embedded verifier work tapes are distinct from the witness tape. -/
theorem satVerifierWorkIdx_ne_witnessIdx {k : ℕ} (i : Fin k) :
    satVerifierWorkIdx i ≠ satWitnessIdx k := by
  intro h
  have := congrArg Fin.val h
  simp [satVerifierWorkIdx, satWitnessIdx] at this
  omega

/-- Embedded verifier work tapes are distinct from the counter tape. -/
theorem satVerifierWorkIdx_ne_counterIdx {k : ℕ} (i : Fin k) :
    satVerifierWorkIdx i ≠ satCounterIdx k := by
  intro h
  have := congrArg Fin.val h
  simp [satVerifierWorkIdx, satCounterIdx] at this
  omega

/-- Control states for the SAT-specialized guess-and-verify machine. -/
inductive GuessVerifyPhase (Q : Type) where
  /-- Building the `|x| + 1` unary counter on the counter tape. -/
  | counter : TM.LinearCounterPhase → GuessVerifyPhase Q
  /-- Rewinding the input head back to the start marker. -/
  | rewindInput : TM.RewindPhase → GuessVerifyPhase Q
  /-- Nondeterministically guessing a counter-bounded witness. -/
  | guess : NTM.GuessBoundedPhase → GuessVerifyPhase Q
  /-- Writing `pair x y` of input and witness onto the pair tape. -/
  | pair : TM.PairBuildPhase → GuessVerifyPhase Q
  /-- Simulating the verifier `M` in state `Q` on the pair tape. -/
  | verify : Q → GuessVerifyPhase Q
  deriving DecidableEq

/-- `GuessVerifyPhase Q` is finite whenever `Q` is. -/
instance {Q : Type} [DecidableEq Q] [Fintype Q] : Fintype (GuessVerifyPhase Q) where
  elems :=
    (Finset.univ.image GuessVerifyPhase.counter) ∪
    (Finset.univ.image GuessVerifyPhase.rewindInput) ∪
    (Finset.univ.image GuessVerifyPhase.guess) ∪
    (Finset.univ.image GuessVerifyPhase.pair) ∪
    (Finset.univ.image GuessVerifyPhase.verify)
  complete := by
    intro q
    cases q <;> simp

/-- State reached when entering the verifier phase from already-started tapes.
    This is the state component of `M`'s forced first step from its true initial
    configuration, where every tape reads `▷`. -/
def verifierStartedState (M : TM k) : M.Q :=
  (M.δ M.qstart Γ.start (fun _ : Fin k => Γ.start) Γ.start).1

/-- Boundary transition that preserves symbols and advances heads parked on `▷`. -/
def phaseBoundary {Q : Type} (q : GuessVerifyPhase Q)
    (iHead : Γ) (wHeads : Fin (k + 3) → Γ) (oHead : Γ) :
    GuessVerifyPhase Q × (Fin (k + 3) → Γw) × Γw ×
      Dir3 × (Fin (k + 3) → Dir3) × Dir3 :=
  (q, fun i => readBackWrite (wHeads i), readBackWrite oHead,
    idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)

private theorem phaseBoundary_right_of_start {Q : Type} (q : GuessVerifyPhase Q)
    (iHead : Γ) (wHeads : Fin (k + 3) → Γ) (oHead : Γ) :
    (iHead = Γ.start → (phaseBoundary (k := k) q iHead wHeads oHead).2.2.2.1 = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start →
      (phaseBoundary (k := k) q iHead wHeads oHead).2.2.2.2.1 i = Dir3.right) ∧
    (oHead = Γ.start → (phaseBoundary (k := k) q iHead wHeads oHead).2.2.2.2.2 = Dir3.right) :=
  rightOfStart_allIdle iHead wHeads oHead

/-- Lift of the deterministic verifier transition to the guess-and-verify tape layout. -/
def satVerifyTransition (M : TM k) (q : M.Q)
    (iHead : Γ) (wHeads : Fin (k + 3) → Γ) (oHead : Γ) :
    GuessVerifyPhase M.Q × (Fin (k + 3) → Γw) × Γw ×
      Dir3 × (Fin (k + 3) → Dir3) × Dir3 :=
  let virtualInput : Γ := wHeads (satPairIdx k)
  let innerWork : Fin k → Γ := fun i => wHeads (satVerifierWorkIdx i)
  let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
    M.δ q virtualInput innerWork oHead
  (.verify q',
    fun i =>
      if h : i.val < k then workWrites ⟨i.val, h⟩
      else if i.val = k then readBackWrite virtualInput
      else readBackWrite (wHeads i),
    outWrite,
    idleDir iHead,
    fun i =>
      if h : i.val < k then workDirs ⟨i.val, h⟩
      else if i.val = k then inDir
      else idleDir (wHeads i),
    outDir)

private theorem satVerifyTransition_right_of_start (M : TM k) (q : M.Q)
    (iHead : Γ) (wHeads : Fin (k + 3) → Γ) (oHead : Γ) :
    let tr := satVerifyTransition M q iHead wHeads oHead
    (iHead = Γ.start → tr.2.2.2.1 = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → tr.2.2.2.2.1 i = Dir3.right) ∧
    (oHead = Γ.start → tr.2.2.2.2.2 = Dir3.right) := by
  unfold satVerifyTransition
  dsimp only []
  have hδ := M.δ_right_of_start q (wHeads (satPairIdx k))
    (fun i : Fin k => wHeads (satVerifierWorkIdx i)) oHead
  obtain ⟨hinp, hwork, hout⟩ := hδ
  refine ⟨idleDir_right_of_start, ?_, hout⟩
  intro i hwi
  by_cases hik : i.val < k
  · simp [hik]
    exact hwork ⟨i.val, hik⟩ (by
      rw [show satVerifierWorkIdx ⟨i.val, hik⟩ = i from by ext; rfl]
      exact hwi)
  · simp [hik]
    by_cases hip : i.val = k
    · simp [hip]
      exact hinp (by
        rw [show satPairIdx k = i from by ext; exact hip.symm]
        exact hwi)
    · simp [hip, idleDir_right_of_start hwi]

/-- Nondeterministic transition function for the combined SAT guess-and-verify machine. -/
def satGuessVerifyDelta (M : TM k) :
    Bool → GuessVerifyPhase M.Q → Γ → (Fin (k + 3) → Γ) → Γ →
      GuessVerifyPhase M.Q × (Fin (k + 3) → Γw) × Γw ×
        Dir3 × (Fin (k + 3) → Dir3) × Dir3 :=
  fun choice state iHead wHeads oHead =>
    match state with
    | .counter q =>
      if q = TM.LinearCounterPhase.done then
        phaseBoundary (.rewindInput TM.RewindPhase.moveLeft) iHead wHeads oHead
      else
        let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
          (TM.inputLengthPlusOneCounterTM (satCounterIdx k)).δ q iHead wHeads oHead
        (.counter q', workWrites, outWrite, inDir, workDirs, outDir)
    | .rewindInput q =>
      if q = TM.RewindPhase.done then
        phaseBoundary (.guess NTM.GuessBoundedPhase.choose) iHead wHeads oHead
      else
        let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
          (TM.rewindInputTM (n := k + 3)).δ q iHead wHeads oHead
        (.rewindInput q', workWrites, outWrite, inDir, workDirs, outDir)
    | .guess q =>
      if q = NTM.GuessBoundedPhase.done then
        phaseBoundary (.pair TM.PairBuildPhase.init) iHead wHeads oHead
      else
        let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
          (NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)).δ
            choice q iHead wHeads oHead
        (.guess q', workWrites, outWrite, inDir, workDirs, outDir)
    | .pair q =>
      if q = TM.PairBuildPhase.done then
        phaseBoundary (.verify (verifierStartedState M)) iHead wHeads oHead
      else
        let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
          (TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).δ q iHead wHeads oHead
        (.pair q', workWrites, outWrite, inDir, workDirs, outDir)
    | .verify q =>
        satVerifyTransition M q iHead wHeads oHead

private theorem satGuessVerifyDelta_right_of_start (M : TM k)
    (choice : Bool) (state : GuessVerifyPhase M.Q)
    (iHead : Γ) (wHeads : Fin (k + 3) → Γ) (oHead : Γ) :
    let tr := satGuessVerifyDelta M choice state iHead wHeads oHead
    (iHead = Γ.start → tr.2.2.2.1 = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → tr.2.2.2.2.1 i = Dir3.right) ∧
    (oHead = Γ.start → tr.2.2.2.2.2 = Dir3.right) := by
  cases state with
  | counter q =>
      by_cases hdone : q = TM.LinearCounterPhase.done
      · simpa [satGuessVerifyDelta, hdone] using
          phaseBoundary_right_of_start
            (k := k) (Q := M.Q) (.rewindInput TM.RewindPhase.moveLeft) iHead wHeads oHead
      · have hδ := (TM.inputLengthPlusOneCounterTM (satCounterIdx k)).δ_right_of_start
          q iHead wHeads oHead
        simpa [satGuessVerifyDelta, hdone] using hδ
  | rewindInput q =>
      by_cases hdone : q = TM.RewindPhase.done
      · simpa [satGuessVerifyDelta, hdone] using
          phaseBoundary_right_of_start
            (k := k) (Q := M.Q) (.guess NTM.GuessBoundedPhase.choose) iHead wHeads oHead
      · have hδ := (TM.rewindInputTM (n := k + 3)).δ_right_of_start q iHead wHeads oHead
        simpa [satGuessVerifyDelta, hdone] using hδ
  | guess q =>
      by_cases hdone : q = NTM.GuessBoundedPhase.done
      · simpa [satGuessVerifyDelta, hdone] using
          phaseBoundary_right_of_start
            (k := k) (Q := M.Q) (.pair TM.PairBuildPhase.init) iHead wHeads oHead
      · have hδ := (NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)).δ_right_of_start
          choice q iHead wHeads oHead
        simpa [satGuessVerifyDelta, hdone] using hδ
  | pair q =>
      by_cases hdone : q = TM.PairBuildPhase.done
      · simpa [satGuessVerifyDelta, hdone] using
          phaseBoundary_right_of_start
            (k := k) (Q := M.Q) (.verify (verifierStartedState M)) iHead wHeads oHead
      · have hδ := (TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).δ_right_of_start
          q iHead wHeads oHead
        simpa [satGuessVerifyDelta, hdone] using hδ
  | verify q =>
      simpa [satGuessVerifyDelta] using
        satVerifyTransition_right_of_start M q iHead wHeads oHead

/-- SAT-specialized guess-and-verify NTM parameterized by a verifier `M`.

It is a concrete composed machine. The proof layer below shows that, when `M`
decides `pairLang Witness`, this machine decides `language` in polynomial time. -/
def satGuessVerifyNTM (M : TM k) : NTM (k + 3) :=
  haveI : DecidableEq M.Q := M.decEq
  haveI : Fintype M.Q := M.finQ
  { Q := GuessVerifyPhase M.Q
    qstart := .counter TM.LinearCounterPhase.scan
    qhalt := .verify M.qhalt
    δ := satGuessVerifyDelta M
    δ_right_of_start := by
      intro choice state iHead wHeads oHead
      exact satGuessVerifyDelta_right_of_start M choice state iHead wHeads oHead }

/-- The deterministic machine simulated during the verifier phase of
    `satGuessVerifyNTM`.  It runs `M` with `M`'s input head retargeted to the
    SAT pair tape, while the real input tape and the setup-only work tapes are
    idled. -/
def satVerifyPhaseTM (M : TM k) : TM (k + 3) :=
  { Q := M.Q
    qstart := verifierStartedState M
    qhalt := M.qhalt
    δ := fun q iHead wHeads oHead =>
      let virtualInput : Γ := wHeads (satPairIdx k)
      let innerWork : Fin k → Γ := fun i => wHeads (satVerifierWorkIdx i)
      let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
        M.δ q virtualInput innerWork oHead
      (q',
        fun i =>
          if h : i.val < k then workWrites ⟨i.val, h⟩
          else if i.val = k then readBackWrite virtualInput
          else readBackWrite (wHeads i),
        outWrite,
        idleDir iHead,
        fun i =>
          if h : i.val < k then workDirs ⟨i.val, h⟩
          else if i.val = k then inDir
          else idleDir (wHeads i),
        outDir)
    δ_right_of_start := by
      intro q iHead wHeads oHead
      have hδ := M.δ_right_of_start q (wHeads (satPairIdx k))
        (fun i : Fin k => wHeads (satVerifierWorkIdx i)) oHead
      obtain ⟨hinp, hwork, hout⟩ := hδ
      refine ⟨idleDir_right_of_start, ?_, hout⟩
      intro i hwi
      by_cases hik : i.val < k
      · simp [hik]
        exact hwork ⟨i.val, hik⟩ (by
          rw [show satVerifierWorkIdx ⟨i.val, hik⟩ = i from by ext; rfl]
          exact hwi)
      · simp [hik]
        by_cases hip : i.val = k
        · simp [hip]
          exact hinp (by
            rw [show satPairIdx k = i from by ext; exact hip.symm]
            exact hwi)
        · simp [hip, idleDir_right_of_start hwi] }

/-- Project a SAT verifier-phase configuration to the corresponding
    configuration of the underlying verifier `M`: the SAT pair tape becomes
    `M`'s input tape, and the first `k` SAT work tapes become `M`'s work
    tapes. -/
def satVerifyInnerCfg (M : TM k) (c : Cfg (k + 3) M.Q) : Cfg k M.Q :=
  { state := c.state
    input := c.work (satPairIdx k)
    work := fun i => c.work (satVerifierWorkIdx i)
    output := c.output }

/-- If the SAT verifier wrapper has just entered the verifier state with the
    pair tape as virtual input and blank started verifier work/output tapes,
    its projection is exactly `M`'s post-start configuration on that pair. -/
theorem satVerifyInnerCfg_eq_startedCfg (M : TM k) (z : List Bool)
    (hne : M.qstart ≠ M.qhalt) (c : Cfg (k + 3) M.Q)
    (hstate : c.state = verifierStartedState M)
    (hpair : c.work (satPairIdx k) =
      (Tape.init (z.map Γ.ofBool)).move Dir3.right)
    (hout : c.output = (Tape.init []).move Dir3.right)
    (hwork : ∀ i : Fin k, c.work (satVerifierWorkIdx i) =
      (Tape.init []).move Dir3.right) :
    satVerifyInnerCfg M c = TM.startedCfg M z hne := by
  cases c with
  | mk state input work output =>
      simp [satVerifyInnerCfg, verifierStartedState, TM.startedCfg, TM.step, hne,
        Tape.read, Tape.init] at hstate hpair hout hwork ⊢
      refine ⟨hstate, ?_, ?_, ?_⟩
      · rw [hpair]
        simpa [TM.startedCfg, TM.step, hne, Tape.read, Tape.init] using
          (TM.startedCfg_input_eq M z hne).symm
      · funext i
        rw [hwork i]
        simpa [TM.startedCfg, TM.step, hne, Tape.read, Tape.init] using
          (TM.startedCfg_work_eq_init_move_right M z hne i).symm
      · rw [hout]
        simpa [TM.startedCfg, TM.step, hne, Tape.read, Tape.init] using
          (TM.startedCfg_output_eq_init_move_right M z hne).symm

/-- A verifier that decides a language also halts from its post-start
    configuration. This is the verifier suffix shape used by the composed SAT
    machine, whose phase boundary has already performed the first move off
    `▷`. -/
theorem verifier_started_trace_halts_of_decidesInTime (M : TM k)
    {L : Language} {f : ℕ → ℕ} (hM : M.DecidesInTime L f) (z : List Bool) :
    ∃ V, V + 1 ≤ f z.length ∧
      ∀ choices : Fin V → Bool,
        M.halted ((M.toNTM).trace V choices
          (TM.startedCfg M z (TM.qstart_ne_qhalt_of_decidesInTime M hM))) := by
  let hne := TM.qstart_ne_qhalt_of_decidesInTime M hM
  obtain ⟨cFinal, t, ht, hreach, hhalt, _, _⟩ := hM z
  have ht_ne : t ≠ 0 := by
    intro ht0
    subst ht0
    cases hreach
    exact hne hhalt
  obtain ⟨V, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht_ne
  obtain ⟨cMid, hstep, hrest⟩ : ∃ cMid,
      M.step (M.initCfg z) = some cMid ∧ M.reachesIn V cMid cFinal := by
    cases hreach with
    | step hstep hrest => exact ⟨_, hstep, hrest⟩
  have hstarted : cMid = TM.startedCfg M z hne := by
    have hs : some cMid = some (TM.startedCfg M z hne) := by
      rw [← hstep, TM.step_initCfg_startedCfg M z hne]
    exact Option.some.inj hs
  subst hstarted
  refine ⟨V, by omega, ?_⟩
  intro choices
  have htrace := M.toNTM_trace_of_reachesIn hrest hhalt le_rfl choices
  rw [htrace]
  exact hhalt

/-- Output-carrying version of
    `verifier_started_trace_halts_of_decidesInTime`. -/
theorem verifier_started_trace_decides_of_decidesInTime (M : TM k)
    {L : Language} {f : ℕ → ℕ} (hM : M.DecidesInTime L f) (z : List Bool) :
    ∃ V, V + 1 ≤ f z.length ∧
      ∀ choices : Fin V → Bool,
        let cFinal := (M.toNTM).trace V choices
          (TM.startedCfg M z (TM.qstart_ne_qhalt_of_decidesInTime M hM))
        M.halted cFinal ∧
          (z ∈ L → cFinal.output.cells 1 = Γ.one) ∧
          (z ∉ L → cFinal.output.cells 1 = Γ.zero) := by
  let hne := TM.qstart_ne_qhalt_of_decidesInTime M hM
  obtain ⟨cFinal, t, ht, hreach, hhalt, hyes, hno⟩ := hM z
  have ht_ne : t ≠ 0 := by
    intro ht0
    subst ht0
    cases hreach
    exact hne hhalt
  obtain ⟨V, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht_ne
  obtain ⟨cMid, hstep, hrest⟩ : ∃ cMid,
      M.step (M.initCfg z) = some cMid ∧ M.reachesIn V cMid cFinal := by
    cases hreach with
    | step hstep hrest => exact ⟨_, hstep, hrest⟩
  have hstarted : cMid = TM.startedCfg M z hne := by
    have hs : some cMid = some (TM.startedCfg M z hne) := by
      rw [← hstep, TM.step_initCfg_startedCfg M z hne]
    exact Option.some.inj hs
  subst hstarted
  refine ⟨V, by omega, ?_⟩
  intro choices
  have htrace := M.toNTM_trace_of_reachesIn hrest hhalt le_rfl choices
  rw [htrace]
  exact ⟨hhalt, hyes, hno⟩

private theorem satTape_writeBack_eq_move (t : Tape) (d : Dir3)
    (h : t.head = 0 ∨ t.read ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read).toΓ d = t.move d := by
  show (t.write (readBackWrite t.read).toΓ).move d = t.move d
  have hwrite : t.write (readBackWrite t.read).toΓ = t := by
    simp only [Tape.write]
    rcases h with hhead | hread
    · simp [hhead]
    · split
      · rfl
      · rw [toΓ_readBackWrite_of_ne_start hread]
        simp [Tape.read, Function.update_eq_self]
  rw [hwrite]

private theorem tape_write_readBack_move_cells_ne_start (t : Tape) (d : Dir3)
    (hclean : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start) :
    ∀ j, j ≥ 1 →
      (t.writeAndMove (readBackWrite t.read).toΓ d).cells j ≠ Γ.start := by
  intro j hj
  rw [Tape.writeAndMove, Tape.move_cells]
  by_cases hhead0 : t.head = 0
  · simp [Tape.write, hhead0]
    exact hclean j hj
  · by_cases hjhead : j = t.head
    · subst j
      simp [Tape.write, hhead0]
      cases t.read <;> simp [readBackWrite]
    · simp [Tape.write, hhead0, Function.update, hjhead]
      exact hclean j hj

/-- One verifier-phase step projects to one ordinary verifier step, provided
    the virtual-input/pair tape is structurally stable for the no-op
    `readBackWrite`. -/
theorem satVerifyPhaseTM_trace_one_project (M : TM k)
    (choice : Bool) (c : Cfg (k + 3) M.Q)
    (hstate : c.state ≠ M.qhalt)
    (hpair : (c.work (satPairIdx k)).head = 0 ∨
      (c.work (satPairIdx k)).read ≠ Γ.start) :
    satVerifyInnerCfg M
        (((satVerifyPhaseTM M).toNTM).trace 1 (fun _ => choice) c) =
      ((M.toNTM).trace 1 (fun _ => choice) (satVerifyInnerCfg M c)) := by
  cases c with
  | mk state input work output =>
    have hstate' : state ≠ M.qhalt := by
      simpa using hstate
    simp [satVerifyInnerCfg, satVerifyPhaseTM, TM.toNTM, NTM.trace, hstate']
    constructor
    · simpa [satPairIdx] using satTape_writeBack_eq_move (work (satPairIdx k)) _ hpair
    · funext i
      simp [satVerifierWorkIdx]

/-- Multi-step projection from the SAT verifier phase back to `M.toNTM`,
    assuming the virtual-input/pair tape is stable for each proper verifier
    prefix. -/
theorem satVerifyPhaseTM_trace_project_prefix (M : TM k) :
    ∀ (T : ℕ) (choices : Fin T → Bool) (c : Cfg (k + 3) M.Q),
      (∀ t (ht : t < T),
        let ct := ((satVerifyPhaseTM M).toNTM).trace t
          (fun i => choices ⟨i.val, Nat.lt_trans i.isLt ht⟩) c
        (ct.work (satPairIdx k)).head = 0 ∨
          (ct.work (satPairIdx k)).read ≠ Γ.start) →
      satVerifyInnerCfg M (((satVerifyPhaseTM M).toNTM).trace T choices c) =
        (M.toNTM).trace T choices (satVerifyInnerCfg M c) := by
  intro T
  induction T with
  | zero =>
      intro choices c _hpair
      rfl
  | succ T ih =>
      intro choices c hpair
      let verifyNTM := (satVerifyPhaseTM M).toNTM
      let innerNTM := M.toNTM
      by_cases hhalt : c.state = M.qhalt
      · simp [satVerifyPhaseTM, TM.toNTM, NTM.trace, satVerifyInnerCfg, hhalt]
      · let choicesTail : Fin T → Bool := fun i => choices ⟨i.val + 1, by omega⟩
        let c1 : Cfg (k + 3) M.Q :=
          verifyNTM.trace 1 (fun _ => choices ⟨0, by omega⟩) c
        have hpair0 : (c.work (satPairIdx k)).head = 0 ∨
            (c.work (satPairIdx k)).read ≠ Γ.start := by
          have h0 := hpair 0 (by omega)
          simpa [verifyNTM, NTM.trace, hhalt] using h0
        have htail : ∀ t (ht : t < T),
            let ct := verifyNTM.trace t
              (fun i => choicesTail ⟨i.val, Nat.lt_trans i.isLt ht⟩) c1
            (ct.work (satPairIdx k)).head = 0 ∨
              (ct.work (satPairIdx k)).read ≠ Γ.start := by
          intro t ht
          have hfull := hpair (t + 1) (by omega)
          let choicesPrefix : Fin (t + 1) → Bool := fun i => choices ⟨i.val, by omega⟩
          have hsplit :=
            NTM.trace_succ verifyNTM t choicesPrefix c
          change
            let ct := verifyNTM.trace t
              (fun i => choicesTail ⟨i.val, Nat.lt_trans i.isLt ht⟩) c1
            (ct.work (satPairIdx k)).head = 0 ∨
              (ct.work (satPairIdx k)).read ≠ Γ.start
          rw [← hsplit]
          exact hfull
        rw [NTM.trace_succ verifyNTM T choices c]
        rw [NTM.trace_succ innerNTM T choices (satVerifyInnerCfg M c)]
        have hone :=
          satVerifyPhaseTM_trace_one_project M (choices ⟨0, by omega⟩) c hhalt hpair0
        rw [ih choicesTail c1 htail]
        rw [hone]

/-- The verifier-phase wrapper halts exactly when its projection to `M`
    halts. -/
theorem satVerifyPhaseTM_halted_iff (M : TM k) (c : Cfg (k + 3) M.Q) :
    (satVerifyPhaseTM M).halted c ↔ M.halted (satVerifyInnerCfg M c) :=
  Iff.rfl

/-- Halting transfers from the projected verifier trace back to the SAT
    verifier phase. -/
theorem satVerifyPhaseTM_halts_of_inner_trace_halts (M : TM k)
    (T : ℕ) (choices : Fin T → Bool) (c : Cfg (k + 3) M.Q)
    (hpair : ∀ t (ht : t < T),
      let ct := ((satVerifyPhaseTM M).toNTM).trace t
        (fun i => choices ⟨i.val, Nat.lt_trans i.isLt ht⟩) c
      (ct.work (satPairIdx k)).head = 0 ∨
        (ct.work (satPairIdx k)).read ≠ Γ.start)
    (hinner : M.halted ((M.toNTM).trace T choices (satVerifyInnerCfg M c))) :
    (satVerifyPhaseTM M).halted (((satVerifyPhaseTM M).toNTM).trace T choices c) := by
  have hproj := satVerifyPhaseTM_trace_project_prefix M T choices c hpair
  erw [satVerifyPhaseTM_halted_iff, hproj]
  exact hinner

/-- One verifier-phase step preserves the invariant that the SAT pair tape has
    no start markers outside cell zero. -/
theorem satVerifyPhaseTM_pair_cells_ne_start_trace_one (M : TM k)
    (choice : Bool) (c : Cfg (k + 3) M.Q)
    (hclean : ∀ j, j ≥ 1 → (c.work (satPairIdx k)).cells j ≠ Γ.start) :
    ∀ j, j ≥ 1 →
      ((((satVerifyPhaseTM M).toNTM).trace 1 (fun _ => choice) c).work
        (satPairIdx k)).cells j ≠ Γ.start := by
  by_cases hhalt : c.state = M.qhalt
  · simpa [NTM.trace, TM.toNTM, satVerifyPhaseTM, hhalt] using hclean
  · cases c with
    | mk state input work output =>
        intro j hj
        simp [NTM.trace, TM.toNTM, satVerifyPhaseTM, hhalt, satPairIdx]
        exact tape_write_readBack_move_cells_ne_start (work (satPairIdx k)) _ hclean j hj

/-- The SAT pair tape stays free of start markers outside cell zero throughout
    the verifier phase. -/
theorem satVerifyPhaseTM_pair_cells_ne_start_trace (M : TM k) :
    ∀ (T : ℕ) (choices : Fin T → Bool) (c : Cfg (k + 3) M.Q),
      (∀ j, j ≥ 1 → (c.work (satPairIdx k)).cells j ≠ Γ.start) →
      ∀ j, j ≥ 1 →
        ((((satVerifyPhaseTM M).toNTM).trace T choices c).work
          (satPairIdx k)).cells j ≠ Γ.start := by
  intro T choices c hclean
  apply ((satVerifyPhaseTM M).toNTM).trace_invariant T choices c
    (fun _ current => ∀ j, j ≥ 1 →
      (current.work (satPairIdx k)).cells j ≠ Γ.start) hclean
  intro time htime current hcurrent
  exact satVerifyPhaseTM_pair_cells_ne_start_trace_one M
    (choices ⟨time, htime⟩) current hcurrent

/-- A clean SAT pair tape supplies the structural guard needed by the verifier
    projection: if the pair head is away from cell zero, it cannot be reading a
    start marker. -/
theorem satVerifyPhaseTM_pair_guard_of_clean (M : TM k)
    (T : ℕ) (choices : Fin T → Bool) (c : Cfg (k + 3) M.Q)
    (hclean : ∀ j, j ≥ 1 → (c.work (satPairIdx k)).cells j ≠ Γ.start) :
    ∀ t (ht : t < T),
      let ct := ((satVerifyPhaseTM M).toNTM).trace t
        (fun i => choices ⟨i.val, Nat.lt_trans i.isLt ht⟩) c
      (ct.work (satPairIdx k)).head = 0 ∨
        (ct.work (satPairIdx k)).read ≠ Γ.start := by
  intro t ht
  let choicesT : Fin t → Bool :=
    fun i => choices ⟨i.val, Nat.lt_trans i.isLt ht⟩
  let ct := ((satVerifyPhaseTM M).toNTM).trace t choicesT c
  by_cases hhead : (ct.work (satPairIdx k)).head = 0
  · exact Or.inl hhead
  · right
    have hclean_t :=
      satVerifyPhaseTM_pair_cells_ne_start_trace M t choicesT c hclean
    simpa [ct, choicesT, Tape.read] using
      hclean_t (ct.work (satPairIdx k)).head (by omega)

/-- Wrap a counter-subroutine configuration into the composed machine. -/
def satCounterWrap (M : TM k) (c : Cfg (k + 3) TM.LinearCounterPhase) :
    Cfg (k + 3) (GuessVerifyPhase M.Q) :=
  { state := .counter c.state, input := c.input, work := c.work, output := c.output }

/-- Wrap an input-rewind configuration into the composed machine. -/
def satRewindInputWrap (M : TM k) (c : Cfg (k + 3) TM.RewindPhase) :
    Cfg (k + 3) (GuessVerifyPhase M.Q) :=
  { state := .rewindInput c.state, input := c.input, work := c.work, output := c.output }

/-- Wrap a bounded-guess configuration into the composed machine. -/
def satGuessWrap (M : TM k) (c : Cfg (k + 3) NTM.GuessBoundedPhase) :
    Cfg (k + 3) (GuessVerifyPhase M.Q) :=
  { state := .guess c.state, input := c.input, work := c.work, output := c.output }

/-- Wrap a pair-builder configuration into the composed machine. -/
def satPairWrap (M : TM k) (c : Cfg (k + 3) TM.PairBuildPhase) :
    Cfg (k + 3) (GuessVerifyPhase M.Q) :=
  { state := .pair c.state, input := c.input, work := c.work, output := c.output }

/-- Wrap a verifier configuration into the composed machine. -/
def satVerifyWrap (M : TM k) (c : Cfg (k + 3) M.Q) :
    Cfg (k + 3) (GuessVerifyPhase M.Q) :=
  { state := .verify c.state, input := c.input, work := c.work, output := c.output }

/-- The composed machine halts on a wrapped verifier configuration exactly
    when the verifier-phase machine halts on the unwrapped one. -/
theorem satGuessVerify_verify_halted_iff (M : TM k) (c : Cfg (k + 3) M.Q) :
    (satGuessVerifyNTM M).halted (satVerifyWrap M c) ↔
      (satVerifyPhaseTM M).halted c :=
  by simp [NTM.halted, TM.halted, Cfg.isHalted, satGuessVerifyNTM,
    satVerifyPhaseTM, satVerifyWrap]

/-- Tape effect of a SAT phase boundary on the real input tape. -/
def satBoundaryInput (inp : Tape) : Tape :=
  inp.move (idleDir inp.read)

/-- Tape effect of a SAT phase boundary on the work tapes. -/
def satBoundaryWork (work : Fin (k + 3) → Tape) : Fin (k + 3) → Tape :=
  fun i => (work i).writeAndMove (readBackWrite (work i).read) (idleDir (work i).read)

/-- Tape effect of a SAT phase boundary on the output tape. -/
def satBoundaryOutput (out : Tape) : Tape :=
  out.writeAndMove (readBackWrite out.read) (idleDir out.read)

/-- A phase boundary leaves the input tape unchanged when its head is past
    cell zero and no start markers occur beyond cell zero. -/
theorem satBoundaryInput_stable (inp : Tape)
    (hhead : inp.head ≥ 1) (hns : ∀ j, j ≥ 1 → inp.cells j ≠ Γ.start) :
    satBoundaryInput inp = inp :=
  tape_move_idleDir_stable inp hhead hns

/-- A phase boundary leaves a work tape unchanged when its head is past cell
    zero and no start markers occur beyond cell zero. -/
theorem satBoundaryWork_stable (work : Fin (k + 3) → Tape) (i : Fin (k + 3))
    (hhead : (work i).head ≥ 1)
    (hns : ∀ j, j ≥ 1 → (work i).cells j ≠ Γ.start) :
    satBoundaryWork work i = work i :=
  tape_writeAndMove_stable (work i) hhead hns

/-- A phase boundary leaves a work tape unchanged when it is not currently
    reading a start marker. -/
theorem satBoundaryWork_stable_of_read_ne_start
    (work : Fin (k + 3) → Tape) (i : Fin (k + 3))
    (hread : (work i).read ≠ Γ.start) :
    satBoundaryWork work i = work i := by
  simpa [satBoundaryWork] using
    Tape.writeAndMove_readBack_idle_of_ne_start (work i) hread

/-- Exact initialized Boolean contents on the SAT pair tape imply the clean-tape
    invariant required by the verifier phase. -/
theorem satPair_cells_ne_start_of_initTape_ofBool_move_right (M : TM k)
    (bits : List Bool) (c : Cfg (k + 3) M.Q)
    (hpair : c.work (satPairIdx k) =
      (Tape.init (bits.map Γ.ofBool)).move Dir3.right) :
    ∀ j, j ≥ 1 → (c.work (satPairIdx k)).cells j ≠ Γ.start := by
  rw [hpair]
  exact Tape.init_ofBool_move_right_cells_ne_start bits

private theorem tape_eq_initTape_ofBool_move_right_of_head_cells
    (t : Tape) (bits : List Bool)
    (hhead : t.head = 1)
    (hcells : t.cells = (Tape.init (bits.map Γ.ofBool)).cells) :
    t = (Tape.init (bits.map Γ.ofBool)).move Dir3.right := by
  cases t with
  | mk head cells =>
      simp [Tape.move, Tape.init] at hhead hcells ⊢
      subst head
      subst cells
      exact ⟨rfl, rfl⟩

/-- A phase boundary leaves every work tape unchanged when all heads are past
    cell zero and no start markers occur beyond cell zero. -/
theorem satBoundaryWork_stable_all (work : Fin (k + 3) → Tape)
    (hhead : ∀ i, (work i).head ≥ 1)
    (hns : ∀ i j, j ≥ 1 → (work i).cells j ≠ Γ.start) :
    satBoundaryWork work = work := by
  funext i
  exact satBoundaryWork_stable work i (hhead i) (hns i)

/-- A phase boundary leaves the output tape unchanged when its head is past
    cell zero and no start markers occur beyond cell zero. -/
theorem satBoundaryOutput_stable (out : Tape)
    (hhead : out.head ≥ 1) (hns : ∀ j, j ≥ 1 → out.cells j ≠ Γ.start) :
    satBoundaryOutput out = out :=
  tape_writeAndMove_stable out hhead hns

/-- A phase boundary leaves the output tape unchanged when it is not currently
    reading a start marker. -/
theorem satBoundaryOutput_stable_of_read_ne_start (out : Tape)
    (hread : out.read ≠ Γ.start) :
    satBoundaryOutput out = out := by
  simpa [satBoundaryOutput] using
    Tape.writeAndMove_readBack_idle_of_ne_start out hread

/-- One composed-machine step on a non-done counter configuration simulates
    one step of the counter subroutine. -/
theorem satGuessVerify_counter_trace_one (M : TM k)
    (choice : Bool) (c : Cfg (k + 3) TM.LinearCounterPhase)
    (hstate : c.state ≠ TM.LinearCounterPhase.done) :
    (satGuessVerifyNTM M).trace 1 (fun _ => choice) (satCounterWrap M c) =
      satCounterWrap M
        (((TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM).trace 1
          (fun _ => choice) c) := by
  cases c with
  | mk state input work output =>
    have hstate' : state ≠ TM.LinearCounterPhase.done := by
      simpa using hstate
    simp [satCounterWrap, satGuessVerifyNTM, satGuessVerifyDelta, NTM.trace,
      TM.toNTM, TM.inputLengthPlusOneCounterTM, hstate']

/-- Multi-step counter-phase simulation up to, but not across, the counter
    subroutine's halt state. -/
theorem satGuessVerify_counter_trace_prefix (M : TM k) :
    ∀ (T : ℕ) (choices : Fin T → Bool)
      (c : Cfg (k + 3) TM.LinearCounterPhase),
      (∀ t (ht : t < T),
        ((((TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM).trace t
          (fun i => choices ⟨i.val, Nat.lt_trans i.isLt ht⟩) c).state ≠
            TM.LinearCounterPhase.done)) →
      (satGuessVerifyNTM M).trace T choices (satCounterWrap M c) =
        satCounterWrap M
          (((TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM).trace T choices c) := by
  intro T
  induction T with
  | zero =>
      intro choices c _hnot
      rfl
  | succ T ih =>
      intro choices c hnot
      let counterNTM := (TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM
      let choicesTail : Fin T → Bool := fun i => choices ⟨i.val + 1, by omega⟩
      let c1 : Cfg (k + 3) TM.LinearCounterPhase :=
        counterNTM.trace 1 (fun _ => choices ⟨0, by omega⟩) c
      have hstate : c.state ≠ TM.LinearCounterPhase.done := by
        have h0 := hnot 0 (by omega)
        exact h0
      rw [NTM.trace_succ (satGuessVerifyNTM M) T choices (satCounterWrap M c)]
      rw [satGuessVerify_counter_trace_one M (choices ⟨0, by omega⟩) c hstate]
      have htail : ∀ t (ht : t < T),
          (counterNTM.trace t
            (fun i => choicesTail ⟨i.val, Nat.lt_trans i.isLt ht⟩) c1).state ≠
              TM.LinearCounterPhase.done := by
        intro t ht
        have hfull := hnot (t + 1) (by omega)
        let choicesPrefix : Fin (t + 1) → Bool := fun i => choices ⟨i.val, by omega⟩
        have hsplit :=
          NTM.trace_succ counterNTM t choicesPrefix c
        change (counterNTM.trace t
          (fun i => choicesTail ⟨i.val, Nat.lt_trans i.isLt ht⟩) c1).state ≠
            TM.LinearCounterPhase.done
        rw [← hsplit]
        exact hfull
      rw [ih choicesTail c1 htail]
      have hsplitFull :=
        NTM.trace_succ counterNTM T choices c
      rw [hsplitFull]

/-- If the counter subroutine first reaches `done` at time `T`, then the
    composed machine exits the counter phase on the next step. -/
theorem satGuessVerify_counter_trace_exit (M : TM k) (T : ℕ)
    (choices : Fin (T + 1) → Bool)
    (c : Cfg (k + 3) TM.LinearCounterPhase)
    (hnot : ∀ t (ht : t < T),
      (((TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM).trace t
        (fun i => choices ⟨i.val, by omega⟩) c).state ≠
          TM.LinearCounterPhase.done)
    (hdone :
      (((TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM).trace T
        (fun i => choices ⟨i.val, by omega⟩) c).state =
          TM.LinearCounterPhase.done) :
    let counterNTM := (TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM
    let counterChoices : Fin T → Bool := fun i => choices ⟨i.val, by omega⟩
    let cT := counterNTM.trace T counterChoices c
    (satGuessVerifyNTM M).trace (T + 1) choices (satCounterWrap M c) =
      satRewindInputWrap M
        { state := TM.RewindPhase.moveLeft,
          input := satBoundaryInput cT.input,
          work := satBoundaryWork cT.work,
          output := satBoundaryOutput cT.output } := by
  let counterNTM := (TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM
  let counterChoices : Fin T → Bool := fun i => choices ⟨i.val, by omega⟩
  let cT := counterNTM.trace T counterChoices c
  have hprefixHyp : ∀ t (ht : t < T),
      (counterNTM.trace t
        (fun i => counterChoices ⟨i.val, Nat.lt_trans i.isLt ht⟩) c).state ≠
          TM.LinearCounterPhase.done := by
    intro t ht
    simpa [counterNTM, counterChoices] using hnot t ht
  have hprefix :=
    satGuessVerify_counter_trace_prefix M T counterChoices c hprefixHyp
  have hsplit :=
    NTM.trace_snoc (satGuessVerifyNTM M) T choices (satCounterWrap M c)
  have hprefix' :
      (satGuessVerifyNTM M).trace T
          (fun i => choices i.castSucc) (satCounterWrap M c) =
        satCounterWrap M cT := by
    simp [counterNTM, counterChoices, cT]
    exact hprefix
  rw [hsplit, hprefix']
  change (satGuessVerifyNTM M).trace 1
      (fun _ => choices (Fin.last T)) (satCounterWrap M cT) =
    satRewindInputWrap M
      { state := TM.RewindPhase.moveLeft,
        input := satBoundaryInput cT.input,
        work := satBoundaryWork cT.work,
        output := satBoundaryOutput cT.output }
  have hdone' : cT.state = TM.LinearCounterPhase.done := by
    simpa [cT, counterNTM, counterChoices] using hdone
  simp [satCounterWrap, satRewindInputWrap, satGuessVerifyNTM, satGuessVerifyDelta,
    phaseBoundary, satBoundaryInput, satBoundaryOutput, NTM.trace, hdone']
  funext i
  rfl

private theorem satCounter_trace_preserves_started_blank_other_work
    (T : ℕ) (choices : Fin T → Bool)
    (c : Cfg (k + 3) TM.LinearCounterPhase)
    (i : Fin (k + 3)) (hi : i ≠ satCounterIdx k)
    (hwork : c.work i = (Tape.init []).move Dir3.right) :
    (((TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM).trace T choices c).work i =
      (Tape.init []).move Dir3.right := by
  apply ((TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM).trace_invariant
    T choices c (fun _ current =>
      current.work i = (Tape.init []).move Dir3.right) hwork
  intro time htime current hcurrent
  exact TM.inputLengthPlusOneCounterTM_toNTM_trace_one_preserves_started_blank_other_work
    (satCounterIdx k) (choices ⟨time, htime⟩) current i hi hcurrent

private theorem satCounter_trace_succ_initializes_blank_other_work
    (T : ℕ) (choices : Fin (T + 1) → Bool)
    (c : Cfg (k + 3) TM.LinearCounterPhase)
    (i : Fin (k + 3)) (hi : i ≠ satCounterIdx k)
    (hstate : c.state ≠ TM.LinearCounterPhase.done)
    (hwork : c.work i = Tape.init []) :
    (((TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM).trace (T + 1) choices c).work i =
      (Tape.init []).move Dir3.right := by
  let counterNTM := (TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM
  let c1 : Cfg (k + 3) TM.LinearCounterPhase :=
    counterNTM.trace 1 (fun _ => choices ⟨0, by omega⟩) c
  have h1 : c1.work i = (Tape.init []).move Dir3.right := by
    exact TM.inputLengthPlusOneCounterTM_toNTM_trace_one_initializes_blank_other_work
      (satCounterIdx k) (choices ⟨0, by omega⟩) c i hi hstate hwork
  rw [NTM.trace_succ counterNTM T choices c]
  exact satCounter_trace_preserves_started_blank_other_work T
    (fun j => choices ⟨j.val + 1, by omega⟩) c1 i hi h1

private theorem satCounter_trace_preserves_started_blank_output
    (T : ℕ) (choices : Fin T → Bool)
    (c : Cfg (k + 3) TM.LinearCounterPhase)
    (houtput : c.output = (Tape.init []).move Dir3.right) :
    (((TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM).trace T choices c).output =
      (Tape.init []).move Dir3.right := by
  apply ((TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM).trace_invariant
    T choices c (fun _ current =>
      current.output = (Tape.init []).move Dir3.right) houtput
  intro time htime current hcurrent
  exact TM.inputLengthPlusOneCounterTM_toNTM_trace_one_preserves_started_blank_output
    (satCounterIdx k) (choices ⟨time, htime⟩) current hcurrent

private theorem satCounter_trace_succ_initializes_blank_output
    (T : ℕ) (choices : Fin (T + 1) → Bool)
    (c : Cfg (k + 3) TM.LinearCounterPhase)
    (hstate : c.state ≠ TM.LinearCounterPhase.done)
    (houtput : c.output = Tape.init []) :
    (((TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM).trace (T + 1) choices c).output =
      (Tape.init []).move Dir3.right := by
  let counterNTM := (TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM
  let c1 : Cfg (k + 3) TM.LinearCounterPhase :=
    counterNTM.trace 1 (fun _ => choices ⟨0, by omega⟩) c
  have h1 : c1.output = (Tape.init []).move Dir3.right := by
    exact TM.inputLengthPlusOneCounterTM_toNTM_trace_one_initializes_blank_output
      (satCounterIdx k) (choices ⟨0, by omega⟩) c hstate houtput
  rw [NTM.trace_succ counterNTM T choices c]
  exact satCounter_trace_preserves_started_blank_output T
    (fun j => choices ⟨j.val + 1, by omega⟩) c1 h1

private theorem satCounter_init_boundary_started_blank_other_work
    (x : List Bool) (T : ℕ) (choices : Fin T → Bool)
    (i : Fin (k + 3)) (hi : i ≠ satCounterIdx k) :
    let counterNTM := (TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM
    let c0 : Cfg (k + 3) TM.LinearCounterPhase :=
      { state := TM.LinearCounterPhase.scan,
        input := Tape.init (x.map Γ.ofBool),
        work := fun _ => Tape.init [],
        output := Tape.init [] }
    let cT := counterNTM.trace T choices c0
    satBoundaryWork cT.work i = (Tape.init []).move Dir3.right := by
  cases T with
  | zero =>
      change satBoundaryWork (fun _ : Fin (k + 3) => Tape.init []) i =
        (Tape.init []).move Dir3.right
      simp [satBoundaryWork, Tape.writeAndMove, Tape.write, Tape.move, Tape.read,
        idleDir, Tape.init]
  | succ T =>
      let counterNTM := (TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM
      let c0 : Cfg (k + 3) TM.LinearCounterPhase :=
        { state := TM.LinearCounterPhase.scan,
          input := Tape.init (x.map Γ.ofBool),
          work := fun _ => Tape.init [],
          output := Tape.init [] }
      have htrace :
          (counterNTM.trace (T + 1) choices c0).work i =
            (Tape.init []).move Dir3.right := by
        exact satCounter_trace_succ_initializes_blank_other_work T choices c0 i hi
          (by simp [c0]) (by simp [c0])
      have hread :
          ((counterNTM.trace (T + 1) choices c0).work i).read ≠ Γ.start := by
        rw [htrace]
        simp [Tape.read, Tape.move, Tape.init]
      change satBoundaryWork (counterNTM.trace (T + 1) choices c0).work i =
        (Tape.init []).move Dir3.right
      rw [satBoundaryWork_stable_of_read_ne_start
        (counterNTM.trace (T + 1) choices c0).work i hread]
      exact htrace

private theorem satCounter_init_boundary_started_blank_output
    (x : List Bool) (T : ℕ) (choices : Fin T → Bool) :
    let counterNTM := (TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM
    let c0 : Cfg (k + 3) TM.LinearCounterPhase :=
      { state := TM.LinearCounterPhase.scan,
        input := Tape.init (x.map Γ.ofBool),
        work := fun _ => Tape.init [],
        output := Tape.init [] }
    let cT := counterNTM.trace T choices c0
    satBoundaryOutput cT.output = (Tape.init []).move Dir3.right := by
  cases T with
  | zero =>
      change satBoundaryOutput (Tape.init []) =
        (Tape.init []).move Dir3.right
      simp [satBoundaryOutput, Tape.writeAndMove, Tape.write, Tape.move, Tape.read,
        idleDir, Tape.init]
  | succ T =>
      let counterNTM := (TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM
      let c0 : Cfg (k + 3) TM.LinearCounterPhase :=
        { state := TM.LinearCounterPhase.scan,
          input := Tape.init (x.map Γ.ofBool),
          work := fun _ => Tape.init [],
          output := Tape.init [] }
      have htrace :
          (counterNTM.trace (T + 1) choices c0).output =
            (Tape.init []).move Dir3.right := by
        exact satCounter_trace_succ_initializes_blank_output T choices c0
          (by simp [c0]) (by simp [c0])
      have hread :
          ((counterNTM.trace (T + 1) choices c0).output).read ≠ Γ.start := by
        rw [htrace]
        simp [Tape.read, Tape.move, Tape.init]
      change satBoundaryOutput (counterNTM.trace (T + 1) choices c0).output =
        (Tape.init []).move Dir3.right
      rw [satBoundaryOutput_stable_of_read_ne_start
        (counterNTM.trace (T + 1) choices c0).output hread]
      exact htrace

/-- From the actual composed-machine initial configuration, the counter setup
    phase reaches the input-rewind phase within the counter bound plus the
    one boundary step. -/
theorem satGuessVerify_counter_init_exits (M : TM k) (x : List Bool)
    (choices : Fin (TM.inputLengthPlusOneCounterTime x.length + 1) → Bool) :
    ∃ t, ∃ ht : t ≤ TM.inputLengthPlusOneCounterTime x.length,
      let counterNTM := (TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM
      let counterChoices : Fin t → Bool := fun i => choices ⟨i.val, by omega⟩
      let c0 : Cfg (k + 3) TM.LinearCounterPhase :=
        { state := TM.LinearCounterPhase.scan,
          input := Tape.init (x.map Γ.ofBool),
          work := fun _ => Tape.init [],
          output := Tape.init [] }
      let cT := counterNTM.trace t counterChoices c0
      (satGuessVerifyNTM M).trace (t + 1)
        (fun i => choices (Fin.castLE (by omega : t + 1 ≤
          TM.inputLengthPlusOneCounterTime x.length + 1) i))
        ((satGuessVerifyNTM M).initCfg x) =
        satRewindInputWrap M
          { state := TM.RewindPhase.moveLeft,
            input := satBoundaryInput cT.input,
            work := satBoundaryWork cT.work,
            output := satBoundaryOutput cT.output } ∧
      (satBoundaryInput cT.input).cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → (satBoundaryInput cT.input).cells j ≠ Γ.start) ∧
      (satBoundaryInput cT.input).cells =
        (Tape.init (x.map Γ.ofBool)).cells ∧
      (satBoundaryInput cT.input).head ≤
        TM.inputLengthPlusOneCounterTime x.length + 1 ∧
      (satBoundaryWork cT.work (satCounterIdx k)).HasUnaryCounter (x.length + 1) ∧
      (∀ i, i ≠ satCounterIdx k →
        satBoundaryWork cT.work i = (Tape.init []).move Dir3.right) ∧
      satBoundaryWork cT.work (satWitnessIdx k) =
        (Tape.init []).move Dir3.right ∧
      satBoundaryWork cT.work (satPairIdx k) =
        (Tape.init []).move Dir3.right ∧
      satBoundaryOutput cT.output =
        (Tape.init []).move Dir3.right := by
  let B := TM.inputLengthPlusOneCounterTime x.length
  let counterNTM := (TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM
  let counterChoicesB : Fin B → Bool := fun i => choices ⟨i.val, by omega⟩
  let c0 : Cfg (k + 3) TM.LinearCounterPhase :=
    { state := TM.LinearCounterPhase.scan,
      input := Tape.init (x.map Γ.ofBool),
      work := fun _ => Tape.init [],
      output := Tape.init [] }
  have hcounter :=
    TM.inputLengthPlusOneCounterTM_toNTM_hoareTime (satCounterIdx k) x
  have hpre :
      (Tape.init (x.map Γ.ofBool) = Tape.init (x.map Γ.ofBool) ∧
        (fun _ : Fin (k + 3) => Tape.init []) (satCounterIdx k) =
          Tape.init []) := by
    simp
  obtain ⟨t, ht, hhalt, hpost, hfirst⟩ :=
    hcounter.exists_first_halt_time_with_post
      (inp := Tape.init (x.map Γ.ofBool))
      (work := fun _ : Fin (k + 3) => Tape.init [])
      (out := Tape.init []) hpre counterChoicesB
  refine ⟨t, by simpa [B] using ht, ?_⟩
  let counterChoices : Fin t → Bool := fun i => choices ⟨i.val, by omega⟩
  let cT := counterNTM.trace t counterChoices c0
  let choicesExit : Fin (t + 1) → Bool :=
    fun i => choices (Fin.castLE (by omega : t + 1 ≤ B + 1) i)
  have hdone : (counterNTM.trace t
      (fun i => choicesExit ⟨i.val, by omega⟩) c0).state =
        TM.LinearCounterPhase.done := by
    simp [B, counterNTM, choicesExit, c0]
    exact hhalt
  have hnot : ∀ s (hs : s < t),
      (counterNTM.trace s (fun i => choicesExit ⟨i.val, by omega⟩) c0).state ≠
        TM.LinearCounterPhase.done := by
    intro s hs
    have hfirst_s := hfirst s hs
    simp [B, counterNTM, choicesExit, c0]
    exact hfirst_s
  have hexit :=
    satGuessVerify_counter_trace_exit M t choicesExit c0 hnot hdone
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [B, counterNTM, counterChoices, cT, choicesExit, c0, satCounterWrap,
      satGuessVerifyNTM] using hexit
  · have hcells := NTM.input_cells_trace counterNTM t counterChoices c0
    have hinv := Tape.StartInvariant.init_ofBool x
    have hcell0 : cT.input.cells 0 = (Tape.init (x.map Γ.ofBool)).cells 0 := by
      simpa [cT, c0] using congrFun hcells 0
    show (satBoundaryInput cT.input).cells 0 = Γ.start
    rw [satBoundaryInput, Tape.move_cells, hcell0]
    exact hinv.1
  · intro j hj
    have hcells := NTM.input_cells_trace counterNTM t counterChoices c0
    have hinv := Tape.StartInvariant.init_ofBool x
    have hcell : cT.input.cells j = (Tape.init (x.map Γ.ofBool)).cells j := by
      simpa [cT, c0] using congrFun hcells j
    show (satBoundaryInput cT.input).cells j ≠ Γ.start
    rw [satBoundaryInput, Tape.move_cells, hcell]
    exact hinv.2 j hj
  · have hcells := NTM.input_cells_trace counterNTM t counterChoices c0
    funext j
    have hcell : cT.input.cells j = (Tape.init (x.map Γ.ofBool)).cells j := by
      simpa [cT, c0] using congrFun hcells j
    show (satBoundaryInput cT.input).cells j = (Tape.init (x.map Γ.ofBool)).cells j
    rw [satBoundaryInput, Tape.move_cells, hcell]
  · have htrace_head := NTM.input_head_trace_le counterNTM t counterChoices c0
    have hcT_head : cT.input.head ≤ t := by
      have hc0 : c0.input.head = 0 := by simp [c0, Tape.init]
      rw [hc0, Nat.zero_add] at htrace_head
      simpa [cT] using htrace_head
    have hmove : (satBoundaryInput cT.input).head ≤ cT.input.head + 1 := by
      unfold satBoundaryInput
      cases idleDir cT.input.read <;> simp [Tape.move]
      omega
    exact le_trans hmove (by omega)
  · have hcounter_post :
        (cT.work (satCounterIdx k)).HasUnaryCounter (x.length + 1) := by
      simp [counterNTM, counterChoices, cT, c0]
      exact hpost
    have hread_counter : (cT.work (satCounterIdx k)).read ≠ Γ.start := by
      have hcell := hcounter_post.2.1 0 (by omega : 0 < x.length + 1)
      simp [Tape.read, hcounter_post.1, hcell]
    rw [satBoundaryWork_stable_of_read_ne_start cT.work (satCounterIdx k) hread_counter]
    exact hcounter_post
  · intro i hi
    have hframe :=
      satCounter_init_boundary_started_blank_other_work x t counterChoices i hi
    simpa [counterNTM, counterChoices, cT, c0] using hframe
  · have hwitness :=
      satCounter_init_boundary_started_blank_other_work x t counterChoices
        (satWitnessIdx k) (Ne.symm (satCounterIdx_ne_witnessIdx k))
    simpa [counterNTM, counterChoices, cT, c0] using hwitness
  · have hpair :=
      satCounter_init_boundary_started_blank_other_work x t counterChoices
        (satPairIdx k) (Ne.symm (satCounterIdx_ne_pairIdx k))
    simpa [counterNTM, counterChoices, cT, c0] using hpair
  · have houtput :=
      satCounter_init_boundary_started_blank_output (k := k) x t counterChoices
    simpa [counterNTM, counterChoices, cT, c0] using houtput

/-- One composed-machine step on a non-done rewind configuration simulates one
    step of the input-rewind subroutine. -/
theorem satGuessVerify_rewindInput_trace_one (M : TM k)
    (choice : Bool) (c : Cfg (k + 3) TM.RewindPhase)
    (hstate : c.state ≠ TM.RewindPhase.done) :
    (satGuessVerifyNTM M).trace 1 (fun _ => choice) (satRewindInputWrap M c) =
      satRewindInputWrap M
        (((TM.rewindInputTM (n := k + 3)).toNTM).trace 1
          (fun _ => choice) c) := by
  cases c with
  | mk state input work output =>
    have hstate' : state ≠ TM.RewindPhase.done := by
      simpa using hstate
    simp [satRewindInputWrap, satGuessVerifyNTM, satGuessVerifyDelta, NTM.trace,
      TM.toNTM, TM.rewindInputTM, hstate']

/-- Multi-step input-rewind simulation up to, but not across, the rewind
    subroutine's halt state. -/
theorem satGuessVerify_rewindInput_trace_prefix (M : TM k) :
    ∀ (T : ℕ) (choices : Fin T → Bool)
      (c : Cfg (k + 3) TM.RewindPhase),
      (∀ t (ht : t < T),
        (((TM.rewindInputTM (n := k + 3)).toNTM).trace t
          (fun i => choices ⟨i.val, Nat.lt_trans i.isLt ht⟩) c).state ≠
            TM.RewindPhase.done) →
      (satGuessVerifyNTM M).trace T choices (satRewindInputWrap M c) =
        satRewindInputWrap M
          (((TM.rewindInputTM (n := k + 3)).toNTM).trace T choices c) := by
  intro T
  induction T with
  | zero =>
      intro choices c _hnot
      rfl
  | succ T ih =>
      intro choices c hnot
      let rewindNTM := (TM.rewindInputTM (n := k + 3)).toNTM
      let choicesTail : Fin T → Bool := fun i => choices ⟨i.val + 1, by omega⟩
      let c1 : Cfg (k + 3) TM.RewindPhase :=
        rewindNTM.trace 1 (fun _ => choices ⟨0, by omega⟩) c
      have hstate : c.state ≠ TM.RewindPhase.done := by
        have h0 := hnot 0 (by omega)
        exact h0
      rw [NTM.trace_succ (satGuessVerifyNTM M) T choices (satRewindInputWrap M c)]
      rw [satGuessVerify_rewindInput_trace_one M (choices ⟨0, by omega⟩) c hstate]
      have htail : ∀ t (ht : t < T),
          (rewindNTM.trace t
            (fun i => choicesTail ⟨i.val, Nat.lt_trans i.isLt ht⟩) c1).state ≠
              TM.RewindPhase.done := by
        intro t ht
        have hfull := hnot (t + 1) (by omega)
        let choicesPrefix : Fin (t + 1) → Bool := fun i => choices ⟨i.val, by omega⟩
        have hsplit :=
          NTM.trace_succ rewindNTM t choicesPrefix c
        change (rewindNTM.trace t
          (fun i => choicesTail ⟨i.val, Nat.lt_trans i.isLt ht⟩) c1).state ≠
            TM.RewindPhase.done
        rw [← hsplit]
        exact hfull
      rw [ih choicesTail c1 htail]
      have hsplitFull :=
        NTM.trace_succ rewindNTM T choices c
      rw [hsplitFull]

/-- If the input-rewind subroutine first reaches `done` at time `T`, then the
    composed machine exits the rewind phase on the next step. -/
theorem satGuessVerify_rewindInput_trace_exit (M : TM k) (T : ℕ)
    (choices : Fin (T + 1) → Bool)
    (c : Cfg (k + 3) TM.RewindPhase)
    (hnot : ∀ t (ht : t < T),
      (((TM.rewindInputTM (n := k + 3)).toNTM).trace t
        (fun i => choices ⟨i.val, by omega⟩) c).state ≠
          TM.RewindPhase.done)
    (hdone :
      (((TM.rewindInputTM (n := k + 3)).toNTM).trace T
        (fun i => choices ⟨i.val, by omega⟩) c).state =
          TM.RewindPhase.done) :
    let rewindNTM := (TM.rewindInputTM (n := k + 3)).toNTM
    let rewindChoices : Fin T → Bool := fun i => choices ⟨i.val, by omega⟩
    let cT := rewindNTM.trace T rewindChoices c
    (satGuessVerifyNTM M).trace (T + 1) choices (satRewindInputWrap M c) =
      satGuessWrap M
        { state := NTM.GuessBoundedPhase.choose,
          input := satBoundaryInput cT.input,
          work := satBoundaryWork cT.work,
          output := satBoundaryOutput cT.output } := by
  let rewindNTM := (TM.rewindInputTM (n := k + 3)).toNTM
  let rewindChoices : Fin T → Bool := fun i => choices ⟨i.val, by omega⟩
  let cT := rewindNTM.trace T rewindChoices c
  have hprefixHyp : ∀ t (ht : t < T),
      (rewindNTM.trace t
        (fun i => rewindChoices ⟨i.val, Nat.lt_trans i.isLt ht⟩) c).state ≠
          TM.RewindPhase.done := by
    intro t ht
    simpa [rewindNTM, rewindChoices] using hnot t ht
  have hprefix :=
    satGuessVerify_rewindInput_trace_prefix M T rewindChoices c hprefixHyp
  have hsplit :=
    NTM.trace_snoc (satGuessVerifyNTM M) T choices (satRewindInputWrap M c)
  have hprefix' :
      (satGuessVerifyNTM M).trace T
          (fun i => choices i.castSucc) (satRewindInputWrap M c) =
        satRewindInputWrap M cT := by
    simp [rewindNTM, rewindChoices, cT]
    exact hprefix
  rw [hsplit, hprefix']
  change (satGuessVerifyNTM M).trace 1
      (fun _ => choices (Fin.last T)) (satRewindInputWrap M cT) =
    satGuessWrap M
      { state := NTM.GuessBoundedPhase.choose,
        input := satBoundaryInput cT.input,
        work := satBoundaryWork cT.work,
        output := satBoundaryOutput cT.output }
  have hdone' : cT.state = TM.RewindPhase.done := by
    simpa [cT, rewindNTM, rewindChoices] using hdone
  simp [satRewindInputWrap, satGuessWrap, satGuessVerifyNTM, satGuessVerifyDelta,
    phaseBoundary, satBoundaryInput, satBoundaryOutput, NTM.trace, hdone']
  funext i
  rfl

/-- From a standard input-rewind phase start, the composed machine reaches
    bounded guessing within the input-rewind bound plus the one boundary step. -/
theorem satGuessVerify_rewindInput_exits (M : TM k) (B : ℕ)
    (inp : Tape) (work : Fin (k + 3) → Tape) (out : Tape)
    (hpre : inp.cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → inp.cells j ≠ Γ.start) ∧ inp.head ≤ B)
    (choices : Fin (B + 2 + 1) → Bool) :
    ∃ t, ∃ ht : t ≤ B + 2,
      let rewindNTM := (TM.rewindInputTM (n := k + 3)).toNTM
      let rewindChoices : Fin t → Bool := fun i => choices ⟨i.val, by omega⟩
      let c0 : Cfg (k + 3) TM.RewindPhase :=
        { state := TM.RewindPhase.moveLeft, input := inp, work := work, output := out }
      let cT := rewindNTM.trace t rewindChoices c0
      (satGuessVerifyNTM M).trace (t + 1)
        (fun i => choices (Fin.castLE (by omega : t + 1 ≤ B + 2 + 1) i))
        (satRewindInputWrap M c0) =
        satGuessWrap M
          { state := NTM.GuessBoundedPhase.choose,
            input := satBoundaryInput cT.input,
            work := satBoundaryWork cT.work,
            output := satBoundaryOutput cT.output } ∧
      (satBoundaryInput cT.input).head = 1 := by
  let R := B + 2
  let rewindNTM := (TM.rewindInputTM (n := k + 3)).toNTM
  let rewindChoicesR : Fin R → Bool := fun i => choices ⟨i.val, by omega⟩
  let c0 : Cfg (k + 3) TM.RewindPhase :=
    { state := TM.RewindPhase.moveLeft, input := inp, work := work, output := out }
  have hrewind := TM.rewindInputTM_toNTM_hoareTime (n := k + 3) B
  obtain ⟨t, ht, hhalt, hpost, hfirst⟩ :=
    hrewind.exists_first_halt_time_with_post
      (inp := inp) (work := work) (out := out) hpre rewindChoicesR
  refine ⟨t, by simpa [R] using ht, ?_⟩
  let rewindChoices : Fin t → Bool := fun i => choices ⟨i.val, by omega⟩
  let cT := rewindNTM.trace t rewindChoices c0
  let choicesExit : Fin (t + 1) → Bool :=
    fun i => choices (Fin.castLE (by omega : t + 1 ≤ R + 1) i)
  have hdone : (rewindNTM.trace t
      (fun i => choicesExit ⟨i.val, by omega⟩) c0).state =
        TM.RewindPhase.done := by
    simp [R, rewindNTM, choicesExit, c0]
    exact hhalt
  have hnot : ∀ s (hs : s < t),
      (rewindNTM.trace s (fun i => choicesExit ⟨i.val, by omega⟩) c0).state ≠
        TM.RewindPhase.done := by
    intro s hs
    have hfirst_s := hfirst s hs
    simp [R, rewindNTM, choicesExit, c0]
    exact hfirst_s
  have hexit :=
    satGuessVerify_rewindInput_trace_exit M t choicesExit c0 hnot hdone
  refine ⟨?_, ?_⟩
  · simpa [R, rewindNTM, rewindChoices, cT, choicesExit, c0] using hexit
  · have hhead : cT.input.head = 1 := by
      simp [rewindNTM, rewindChoices, cT, c0]
      exact hpost
    have hcells := NTM.input_cells_trace rewindNTM t rewindChoices c0
    have hnostart : ∀ j, j ≥ 1 → cT.input.cells j ≠ Γ.start := by
      intro j hj
      have hcell : cT.input.cells j = inp.cells j := by
        simpa [cT, c0] using congrFun hcells j
      rw [hcell]
      exact hpre.2.1 j hj
    rw [satBoundaryInput_stable cT.input (by rw [hhead]) hnostart]
    exact hhead

/-- Rich input-rewind exit theorem: in addition to reaching the guess phase
    with the input head restored, preserve all work tapes and output through
    the boundary when their heads are already past `▷`. -/
theorem satGuessVerify_rewindInput_exits_with_frames (M : TM k) (B : ℕ)
    (inp : Tape) (work : Fin (k + 3) → Tape) (out : Tape)
    (hpre : inp.cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → inp.cells j ≠ Γ.start) ∧ inp.head ≤ B)
    (hout : out.read ≠ Γ.start ∧ out.head ≥ 1)
    (hwork : ∀ i, (work i).read ≠ Γ.start ∧ (work i).head ≥ 1)
    (choices : Fin (B + 2 + 1) → Bool) :
    ∃ t, ∃ ht : t ≤ B + 2,
      let rewindNTM := (TM.rewindInputTM (n := k + 3)).toNTM
      let rewindChoices : Fin t → Bool := fun i => choices ⟨i.val, by omega⟩
      let c0 : Cfg (k + 3) TM.RewindPhase :=
        { state := TM.RewindPhase.moveLeft, input := inp, work := work, output := out }
      let cT := rewindNTM.trace t rewindChoices c0
      (satGuessVerifyNTM M).trace (t + 1)
        (fun i => choices (Fin.castLE (by omega : t + 1 ≤ B + 2 + 1) i))
        (satRewindInputWrap M c0) =
        satGuessWrap M
          { state := NTM.GuessBoundedPhase.choose,
            input := satBoundaryInput cT.input,
            work := satBoundaryWork cT.work,
            output := satBoundaryOutput cT.output } ∧
      (satBoundaryInput cT.input).head = 1 ∧
      (satBoundaryInput cT.input).cells = inp.cells ∧
      satBoundaryWork cT.work = work ∧
      satBoundaryOutput cT.output = out := by
  let R := B + 2
  let rewindNTM := (TM.rewindInputTM (n := k + 3)).toNTM
  let rewindChoicesR : Fin R → Bool := fun i => choices ⟨i.val, by omega⟩
  let c0 : Cfg (k + 3) TM.RewindPhase :=
    { state := TM.RewindPhase.moveLeft, input := inp, work := work, output := out }
  let P : Tape → (Fin (k + 3) → Tape) → Tape → Prop :=
    fun _ work' out' => work' = work ∧ out' = out
  have hP_preserved :
      ∀ (inp0 : Tape) (work0 : Fin (k + 3) → Tape) (out0 : Tape)
        (inp' : Tape) (work' : Fin (k + 3) → Tape) (out' : Tape),
        P inp0 work0 out0 →
        inp'.cells = inp0.cells →
        inp'.head = 1 →
        work' = work0 →
        out' = out0 →
        P inp' work' out' := by
    intro _ work0 out0 _ work' out' hP _ _ hwork' hout'
    exact ⟨hwork'.trans hP.1, hout'.trans hP.2⟩
  have hrewind :=
    TM.rewindInputTM_toNTM_hoareTime_frame (n := k + 3) B
      (P := P) hP_preserved
  have hpre_rich :
      inp.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → inp.cells j ≠ Γ.start) ∧
        inp.head ≤ B ∧
        out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
        (∀ i, (work i).read ≠ Γ.start ∧ (work i).head ≥ 1) ∧
        P inp work out := by
    exact ⟨hpre.1, hpre.2.1, hpre.2.2, hout.1, hout.2, hwork, rfl, rfl⟩
  obtain ⟨t, ht, hhalt, hpost, hfirst⟩ :=
    hrewind.exists_first_halt_time_with_post
      (inp := inp) (work := work) (out := out) hpre_rich rewindChoicesR
  refine ⟨t, by simpa [R] using ht, ?_⟩
  let rewindChoices : Fin t → Bool := fun i => choices ⟨i.val, by omega⟩
  let cT := rewindNTM.trace t rewindChoices c0
  let choicesExit : Fin (t + 1) → Bool :=
    fun i => choices (Fin.castLE (by omega : t + 1 ≤ R + 1) i)
  have hdone : (rewindNTM.trace t
      (fun i => choicesExit ⟨i.val, by omega⟩) c0).state =
        TM.RewindPhase.done := by
    simp [R, rewindNTM, choicesExit, c0]
    exact hhalt
  have hnot : ∀ s (hs : s < t),
      (rewindNTM.trace s (fun i => choicesExit ⟨i.val, by omega⟩) c0).state ≠
        TM.RewindPhase.done := by
    intro s hs
    have hfirst_s := hfirst s hs
    simp [R, rewindNTM, choicesExit, c0]
    exact hfirst_s
  have hexit :=
    satGuessVerify_rewindInput_trace_exit M t choicesExit c0 hnot hdone
  have hrich_post :
      cT.input.head = 1 ∧ cT.work = work ∧ cT.output = out := by
    simp [rewindNTM, rewindChoices, cT, c0]
    exact hpost
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [R, rewindNTM, rewindChoices, cT, choicesExit, c0] using hexit
  · have hcells := NTM.input_cells_trace rewindNTM t rewindChoices c0
    have hnostart : ∀ j, j ≥ 1 → cT.input.cells j ≠ Γ.start := by
      intro j hj
      have hcell : cT.input.cells j = inp.cells j := by
        simpa [cT, c0] using congrFun hcells j
      rw [hcell]
      exact hpre.2.1 j hj
    rw [satBoundaryInput_stable cT.input (by rw [hrich_post.1]) hnostart]
    exact hrich_post.1
  · have hcells := NTM.input_cells_trace rewindNTM t rewindChoices c0
    have hnostart : ∀ j, j ≥ 1 → cT.input.cells j ≠ Γ.start := by
      intro j hj
      have hcell : cT.input.cells j = inp.cells j := by
        simpa [cT, c0] using congrFun hcells j
      rw [hcell]
      exact hpre.2.1 j hj
    rw [satBoundaryInput_stable cT.input (by rw [hrich_post.1]) hnostart]
    simpa [cT, c0] using hcells
  · rw [hrich_post.2.1]
    funext i
    exact satBoundaryWork_stable_of_read_ne_start work i (hwork i).1
  · rw [hrich_post.2.2]
    exact satBoundaryOutput_stable_of_read_ne_start out hout.1

/-- Exact-input corollary of the rich rewind exit, specialized for an input
    tape whose cells are the initialized encoding of `x`. -/
theorem satGuessVerify_rewindInput_exits_with_frames_exact_input (M : TM k) (B : ℕ)
    (x : List Bool) (inp : Tape) (work : Fin (k + 3) → Tape) (out : Tape)
    (hpre : inp.cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → inp.cells j ≠ Γ.start) ∧ inp.head ≤ B)
    (hinput_cells : inp.cells = (Tape.init (x.map Γ.ofBool)).cells)
    (hout : out.read ≠ Γ.start ∧ out.head ≥ 1)
    (hwork : ∀ i, (work i).read ≠ Γ.start ∧ (work i).head ≥ 1)
    (choices : Fin (B + 2 + 1) → Bool) :
    ∃ t, ∃ ht : t ≤ B + 2,
      let rewindNTM := (TM.rewindInputTM (n := k + 3)).toNTM
      let rewindChoices : Fin t → Bool := fun i => choices ⟨i.val, by omega⟩
      let c0 : Cfg (k + 3) TM.RewindPhase :=
        { state := TM.RewindPhase.moveLeft, input := inp, work := work, output := out }
      let cT := rewindNTM.trace t rewindChoices c0
      (satGuessVerifyNTM M).trace (t + 1)
        (fun i => choices (Fin.castLE (by omega : t + 1 ≤ B + 2 + 1) i))
        (satRewindInputWrap M c0) =
        satGuessWrap M
          { state := NTM.GuessBoundedPhase.choose,
            input := satBoundaryInput cT.input,
            work := satBoundaryWork cT.work,
            output := satBoundaryOutput cT.output } ∧
      satBoundaryInput cT.input =
        (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
      satBoundaryWork cT.work = work ∧
      satBoundaryOutput cT.output = out := by
  obtain ⟨t, ht, hrich⟩ :=
    satGuessVerify_rewindInput_exits_with_frames M B inp work out
      hpre hout hwork choices
  refine ⟨t, ht, ?_⟩
  let rewindNTM := (TM.rewindInputTM (n := k + 3)).toNTM
  let rewindChoices : Fin t → Bool := fun i => choices ⟨i.val, by omega⟩
  let c0 : Cfg (k + 3) TM.RewindPhase :=
    { state := TM.RewindPhase.moveLeft, input := inp, work := work, output := out }
  let cT := rewindNTM.trace t rewindChoices c0
  have hrich' :
      (satGuessVerifyNTM M).trace (t + 1)
        (fun i => choices (Fin.castLE (by omega : t + 1 ≤ B + 2 + 1) i))
        (satRewindInputWrap M c0) =
        satGuessWrap M
          { state := NTM.GuessBoundedPhase.choose,
            input := satBoundaryInput cT.input,
            work := satBoundaryWork cT.work,
            output := satBoundaryOutput cT.output } ∧
      (satBoundaryInput cT.input).head = 1 ∧
      (satBoundaryInput cT.input).cells = inp.cells ∧
      satBoundaryWork cT.work = work ∧
      satBoundaryOutput cT.output = out := by
    simpa [rewindNTM, rewindChoices, c0, cT] using hrich
  refine ⟨hrich'.1, ?_, hrich'.2.2.2.1, hrich'.2.2.2.2⟩
  exact tape_eq_initTape_ofBool_move_right_of_head_cells
    (satBoundaryInput cT.input) x hrich'.2.1 (by rw [hrich'.2.2.1, hinput_cells])

/-- One composed-machine step on a non-done guess configuration simulates one
    step of the bounded-guessing subroutine with the same choice bit. -/
theorem satGuessVerify_guess_trace_one (M : TM k)
    (choice : Bool) (c : Cfg (k + 3) NTM.GuessBoundedPhase)
    (hstate : c.state ≠ NTM.GuessBoundedPhase.done) :
    (satGuessVerifyNTM M).trace 1 (fun _ => choice) (satGuessWrap M c) =
      satGuessWrap M
        ((NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)).trace 1
          (fun _ => choice) c) := by
  cases c with
  | mk state input work output =>
    have hstate' : state ≠ NTM.GuessBoundedPhase.done := by
      simpa using hstate
    simp [satGuessWrap, satGuessVerifyNTM, satGuessVerifyDelta, NTM.trace,
      NTM.guessBoundedNTM, hstate']

/-- Multi-step bounded-guess simulation up to, but not across, the guess
    subroutine's halt state. -/
theorem satGuessVerify_guess_trace_prefix (M : TM k) :
    ∀ (T : ℕ) (choices : Fin T → Bool)
      (c : Cfg (k + 3) NTM.GuessBoundedPhase),
      (∀ t (ht : t < T),
        ((NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)).trace t
          (fun i => choices ⟨i.val, Nat.lt_trans i.isLt ht⟩) c).state ≠
            NTM.GuessBoundedPhase.done) →
      (satGuessVerifyNTM M).trace T choices (satGuessWrap M c) =
        satGuessWrap M
          ((NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)).trace T choices c) := by
  intro T
  induction T with
  | zero =>
      intro choices c _hnot
      rfl
  | succ T ih =>
      intro choices c hnot
      let guessNTM := NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)
      let choicesTail : Fin T → Bool := fun i => choices ⟨i.val + 1, by omega⟩
      let c1 : Cfg (k + 3) NTM.GuessBoundedPhase :=
        guessNTM.trace 1 (fun _ => choices ⟨0, by omega⟩) c
      have hstate : c.state ≠ NTM.GuessBoundedPhase.done := by
        have h0 := hnot 0 (by omega)
        exact h0
      rw [NTM.trace_succ (satGuessVerifyNTM M) T choices (satGuessWrap M c)]
      rw [satGuessVerify_guess_trace_one M (choices ⟨0, by omega⟩) c hstate]
      have htail : ∀ t (ht : t < T),
          (guessNTM.trace t
            (fun i => choicesTail ⟨i.val, Nat.lt_trans i.isLt ht⟩) c1).state ≠
              NTM.GuessBoundedPhase.done := by
        intro t ht
        have hfull := hnot (t + 1) (by omega)
        let choicesPrefix : Fin (t + 1) → Bool := fun i => choices ⟨i.val, by omega⟩
        have hsplit :=
          NTM.trace_succ guessNTM t choicesPrefix c
        change (guessNTM.trace t
          (fun i => choicesTail ⟨i.val, Nat.lt_trans i.isLt ht⟩) c1).state ≠
            NTM.GuessBoundedPhase.done
        rw [← hsplit]
        exact hfull
      rw [ih choicesTail c1 htail]
      have hsplitFull :=
        NTM.trace_succ guessNTM T choices c
      rw [hsplitFull]

/-- If the bounded-guess subroutine first reaches `done` at time `T`, then
    the composed machine exits the guess phase on the next step. -/
theorem satGuessVerify_guess_trace_exit (M : TM k) (T : ℕ)
    (choices : Fin (T + 1) → Bool)
    (c : Cfg (k + 3) NTM.GuessBoundedPhase)
    (hnot : ∀ t (ht : t < T),
      ((NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)).trace t
        (fun i => choices ⟨i.val, by omega⟩) c).state ≠
          NTM.GuessBoundedPhase.done)
    (hdone :
      ((NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)).trace T
        (fun i => choices ⟨i.val, by omega⟩) c).state =
          NTM.GuessBoundedPhase.done) :
    let guessNTM := NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)
    let guessChoices : Fin T → Bool := fun i => choices ⟨i.val, by omega⟩
    let cT := guessNTM.trace T guessChoices c
    (satGuessVerifyNTM M).trace (T + 1) choices (satGuessWrap M c) =
      satPairWrap M
        { state := TM.PairBuildPhase.init,
          input := satBoundaryInput cT.input,
          work := satBoundaryWork cT.work,
          output := satBoundaryOutput cT.output } := by
  let guessNTM := NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)
  let guessChoices : Fin T → Bool := fun i => choices ⟨i.val, by omega⟩
  let cT := guessNTM.trace T guessChoices c
  have hprefixHyp : ∀ t (ht : t < T),
      (guessNTM.trace t
        (fun i => guessChoices ⟨i.val, Nat.lt_trans i.isLt ht⟩) c).state ≠
          NTM.GuessBoundedPhase.done := by
    intro t ht
    simpa [guessNTM, guessChoices] using hnot t ht
  have hprefix :=
    satGuessVerify_guess_trace_prefix M T guessChoices c hprefixHyp
  have hsplit :=
    NTM.trace_snoc (satGuessVerifyNTM M) T choices (satGuessWrap M c)
  have hprefix' :
      (satGuessVerifyNTM M).trace T
          (fun i => choices i.castSucc) (satGuessWrap M c) =
        satGuessWrap M cT := by
    simp [guessNTM, guessChoices, cT]
    exact hprefix
  rw [hsplit, hprefix']
  change (satGuessVerifyNTM M).trace 1
      (fun _ => choices (Fin.last T)) (satGuessWrap M cT) =
    satPairWrap M
      { state := TM.PairBuildPhase.init,
        input := satBoundaryInput cT.input,
        work := satBoundaryWork cT.work,
        output := satBoundaryOutput cT.output }
  have hdone' : cT.state = NTM.GuessBoundedPhase.done := by
    simpa [cT, guessNTM, guessChoices] using hdone
  simp [satGuessWrap, satPairWrap, satGuessVerifyNTM, satGuessVerifyDelta,
    phaseBoundary, satBoundaryInput, satBoundaryOutput, NTM.trace, hdone']
  funext i
  rfl

/-- From a standard bounded-guess phase start, the composed machine reaches
    pair building within the guess bound plus the one boundary step. -/
theorem satGuessVerify_guess_exits (M : TM k) (B : ℕ)
    (inp : Tape) (work : Fin (k + 3) → Tape) (out : Tape)
    (hpre : (work (satWitnessIdx k)).HasBinaryPrefix [] ∧
      (work (satWitnessIdx k)).cells 0 = Γ.start ∧
      (work (satCounterIdx k)).HasUnaryCounter B)
    (choices : Fin (NTM.guessBoundedTime B 0 + 1) → Bool) :
    ∃ t, ∃ _ht : t ≤ NTM.guessBoundedTime B 0,
      let guessNTM := NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)
      let guessChoices : Fin t → Bool := fun i => choices ⟨i.val, by omega⟩
      let c0 : Cfg (k + 3) NTM.GuessBoundedPhase :=
        { state := NTM.GuessBoundedPhase.choose, input := inp, work := work, output := out }
      let cT := guessNTM.trace t guessChoices c0
      (satGuessVerifyNTM M).trace (t + 1)
        (fun i => choices (Fin.castLE (by omega : t + 1 ≤
          NTM.guessBoundedTime B 0 + 1) i))
        (satGuessWrap M c0) =
        satPairWrap M
          { state := TM.PairBuildPhase.init,
            input := satBoundaryInput cT.input,
            work := satBoundaryWork cT.work,
            output := satBoundaryOutput cT.output } ∧
      ∃ y : List Bool, y.length ≤ B ∧
        satBoundaryWork cT.work (satWitnessIdx k) =
          (Tape.init (y.map Γ.ofBool)).move Dir3.right := by
  let G := NTM.guessBoundedTime B 0
  let guessNTM := NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)
  let guessChoicesG : Fin G → Bool := fun i => choices ⟨i.val, by omega⟩
  let c0 : Cfg (k + 3) NTM.GuessBoundedPhase :=
    { state := NTM.GuessBoundedPhase.choose, input := inp, work := work, output := out }
  have hguess :=
    NTM.guessBoundedNTM_hoareTime_with_cell0
      (satWitnessIdx k) (satCounterIdx k) (Ne.symm (satCounterIdx_ne_witnessIdx k)) B
  obtain ⟨t, ht, hhalt, hpost, hfirst⟩ :=
    hguess.exists_first_halt_time_with_post
      (inp := inp) (work := work) (out := out) hpre guessChoicesG
  refine ⟨t, by simpa [G] using ht, ?_⟩
  let guessChoices : Fin t → Bool := fun i => choices ⟨i.val, by omega⟩
  let cT := guessNTM.trace t guessChoices c0
  let choicesExit : Fin (t + 1) → Bool :=
    fun i => choices (Fin.castLE (by omega : t + 1 ≤ G + 1) i)
  have hdone : (guessNTM.trace t
      (fun i => choicesExit ⟨i.val, by omega⟩) c0).state =
        NTM.GuessBoundedPhase.done := by
    simp [G, guessNTM, choicesExit, c0]
    exact hhalt
  have hnot : ∀ s (hs : s < t),
      (guessNTM.trace s (fun i => choicesExit ⟨i.val, by omega⟩) c0).state ≠
        NTM.GuessBoundedPhase.done := by
    intro s hs
    have hfirst_s := hfirst s hs
    simp [G, guessNTM, choicesExit, c0]
    exact hfirst_s
  have hexit :=
    satGuessVerify_guess_trace_exit M t choicesExit c0 hnot hdone
  refine ⟨?_, ?_⟩
  · simpa [G, guessNTM, guessChoices, cT, choicesExit, c0] using hexit
  · have hguess_post :
        (cT.work (satWitnessIdx k)).HasBoundedBinaryString B ∧
          (cT.work (satWitnessIdx k)).cells 0 = Γ.start := by
      simp [guessNTM, guessChoices, cT, c0]
      exact hpost
    obtain ⟨bits, hlen, hbits⟩ := hguess_post.1
    have hread : (cT.work (satWitnessIdx k)).read ≠ Γ.start := by
      have hnostart := Tape.cells_ne_start_of_hasBinaryString hbits
      simpa [Tape.read, hbits.1] using hnostart 1 (by omega)
    rw [satBoundaryWork_stable_of_read_ne_start cT.work (satWitnessIdx k) hread]
    exact Tape.exists_eq_init_move_right_of_hasBoundedBinaryString hguess_post.1 hguess_post.2

/-- Arbitrary-choice guess exit with the frame facts needed by pair building:
    the produced witness is bounded by the counter, while the real input, pair
    tape, output, and verifier work tapes are preserved through the boundary. -/
theorem satGuessVerify_guess_exits_with_frames (M : TM k) (B : ℕ)
    (inp : Tape) (work : Fin (k + 3) → Tape) (out : Tape)
    (hpre : (work (satWitnessIdx k)).HasBinaryPrefix [] ∧
      (work (satWitnessIdx k)).cells 0 = Γ.start ∧
      (work (satCounterIdx k)).HasUnaryCounter B ∧
      work (satPairIdx k) = (Tape.init []).move Dir3.right)
    (hinp : inp.head ≥ 1 ∧ ∀ j, j ≥ 1 → inp.cells j ≠ Γ.start)
    (hout : out.read ≠ Γ.start)
    (hwork : ∀ i : Fin k, (work (satVerifierWorkIdx i)).read ≠ Γ.start)
    (choices : Fin (NTM.guessBoundedTime B 0 + 1) → Bool) :
    ∃ t, ∃ _ht : t ≤ NTM.guessBoundedTime B 0,
      ∃ y : List Bool, y.length ≤ B ∧
      let guessNTM := NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)
      let guessChoices : Fin t → Bool := fun i => choices ⟨i.val, by omega⟩
      let c0 : Cfg (k + 3) NTM.GuessBoundedPhase :=
        { state := NTM.GuessBoundedPhase.choose, input := inp, work := work, output := out }
      let cT := guessNTM.trace t guessChoices c0
      (satGuessVerifyNTM M).trace (t + 1)
        (fun i => choices (Fin.castLE (by omega : t + 1 ≤
          NTM.guessBoundedTime B 0 + 1) i))
        (satGuessWrap M c0) =
        satPairWrap M
          { state := TM.PairBuildPhase.init,
            input := satBoundaryInput cT.input,
            work := satBoundaryWork cT.work,
            output := satBoundaryOutput cT.output } ∧
      satBoundaryInput cT.input = inp ∧
      satBoundaryWork cT.work (satWitnessIdx k) =
        (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
      satBoundaryWork cT.work (satPairIdx k) =
        (Tape.init []).move Dir3.right ∧
      satBoundaryOutput cT.output = out ∧
      (∀ i : Fin k, satBoundaryWork cT.work (satVerifierWorkIdx i) =
        work (satVerifierWorkIdx i)) := by
  obtain ⟨t, ht, hbasic⟩ :=
    satGuessVerify_guess_exits M B inp work out
      ⟨hpre.1, hpre.2.1, hpre.2.2.1⟩ choices
  let guessNTM := NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)
  let guessChoices : Fin t → Bool := fun i => choices ⟨i.val, by omega⟩
  let c0 : Cfg (k + 3) NTM.GuessBoundedPhase :=
    { state := NTM.GuessBoundedPhase.choose, input := inp, work := work, output := out }
  let cT := guessNTM.trace t guessChoices c0
  have hexit :
      (satGuessVerifyNTM M).trace (t + 1)
        (fun i => choices (Fin.castLE (by omega : t + 1 ≤
          NTM.guessBoundedTime B 0 + 1) i))
        (satGuessWrap M c0) =
        satPairWrap M
          { state := TM.PairBuildPhase.init,
            input := satBoundaryInput cT.input,
            work := satBoundaryWork cT.work,
            output := satBoundaryOutput cT.output } := by
    simpa [guessNTM, guessChoices, c0, cT] using hbasic.1
  obtain ⟨y, hy, hwitness⟩ := hbasic.2
  have hinpRead : inp.read ≠ Γ.start := by
    have hns := hinp.2 inp.head hinp.1
    simpa [Tape.read] using hns
  have hinput_trace : cT.input = inp := by
    simpa [guessNTM, guessChoices, c0, cT] using
      NTM.guessBoundedNTM_trace_preserves_input
        (satWitnessIdx k) (satCounterIdx k) t guessChoices c0
        (by simpa [c0] using hinpRead)
  have hinput_boundary : satBoundaryInput cT.input = inp := by
    rw [hinput_trace]
    exact satBoundaryInput_stable inp hinp.1 hinp.2
  have hpair_read : (work (satPairIdx k)).read ≠ Γ.start := by
    rw [hpre.2.2.2]
    simp [Tape.read, Tape.move, Tape.init]
  have hpair_trace : cT.work (satPairIdx k) = work (satPairIdx k) := by
    simpa [guessNTM, guessChoices, c0, cT] using
      NTM.guessBoundedNTM_trace_preserves_other_work
        (satWitnessIdx k) (satCounterIdx k) (satPairIdx k) t guessChoices c0
        (Ne.symm (satWitnessIdx_ne_pairIdx k))
        (Ne.symm (satCounterIdx_ne_pairIdx k))
        (by simpa [c0] using hpair_read)
  have hpair_boundary :
      satBoundaryWork cT.work (satPairIdx k) =
        (Tape.init []).move Dir3.right := by
    have hread : (cT.work (satPairIdx k)).read ≠ Γ.start := by
      rw [hpair_trace, hpre.2.2.2]
      simp [Tape.read, Tape.move, Tape.init]
    rw [satBoundaryWork_stable_of_read_ne_start cT.work (satPairIdx k) hread,
      hpair_trace]
    exact hpre.2.2.2
  have houtput_trace : cT.output = out := by
    simpa [guessNTM, guessChoices, c0, cT] using
      NTM.guessBoundedNTM_trace_preserves_output
        (satWitnessIdx k) (satCounterIdx k) t guessChoices c0
        (by simpa [c0] using hout)
  have houtput_boundary : satBoundaryOutput cT.output = out := by
    rw [houtput_trace]
    exact satBoundaryOutput_stable_of_read_ne_start out hout
  have hverifier_boundary :
      ∀ i : Fin k, satBoundaryWork cT.work (satVerifierWorkIdx i) =
        work (satVerifierWorkIdx i) := by
    intro i
    have htrace :
        cT.work (satVerifierWorkIdx i) = work (satVerifierWorkIdx i) := by
      simpa [guessNTM, guessChoices, c0, cT] using
        NTM.guessBoundedNTM_trace_preserves_other_work
          (satWitnessIdx k) (satCounterIdx k) (satVerifierWorkIdx i) t
          guessChoices c0
          (satVerifierWorkIdx_ne_witnessIdx i)
          (satVerifierWorkIdx_ne_counterIdx i)
          (by simpa [c0] using hwork i)
    have hread : (cT.work (satVerifierWorkIdx i)).read ≠ Γ.start := by
      rw [htrace]
      exact hwork i
    rw [satBoundaryWork_stable_of_read_ne_start cT.work (satVerifierWorkIdx i) hread]
    exact htrace
  refine ⟨t, ht, y, hy, ?_⟩
  exact ⟨hexit, hinput_boundary, hwitness, hpair_boundary, houtput_boundary,
    hverifier_boundary⟩

/-- Completeness-oriented guess exit: for any requested witness within the
    unary counter bound, there is a nondeterministic choice sequence that exits
    the guess phase with exactly that witness and leaves the pair tape blank. -/
theorem satGuessVerify_guess_generates_with_pair_frame (M : TM k) (B : ℕ)
    (y : List Bool) (inp : Tape) (work : Fin (k + 3) → Tape) (out : Tape)
    (hlen : y.length ≤ B)
    (hpre : (work (satWitnessIdx k)).HasBinaryPrefix [] ∧
      (work (satWitnessIdx k)).cells 0 = Γ.start ∧
      (work (satCounterIdx k)).HasUnaryCounter B ∧
      work (satPairIdx k) = (Tape.init []).move Dir3.right) :
    ∃ t, ∃ _ : t ≤ NTM.guessBoundedTime B 0,
      ∃ choices : Fin (t + 1) → Bool,
      let guessNTM := NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)
      let guessChoices : Fin t → Bool := fun i => choices ⟨i.val, by omega⟩
      let c0 : Cfg (k + 3) NTM.GuessBoundedPhase :=
        { state := NTM.GuessBoundedPhase.choose, input := inp, work := work, output := out }
      let cT := guessNTM.trace t guessChoices c0
      (satGuessVerifyNTM M).trace (t + 1) choices (satGuessWrap M c0) =
        satPairWrap M
          { state := TM.PairBuildPhase.init,
            input := satBoundaryInput cT.input,
            work := satBoundaryWork cT.work,
            output := satBoundaryOutput cT.output } ∧
      satBoundaryWork cT.work (satWitnessIdx k) =
        (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
      satBoundaryWork cT.work (satPairIdx k) =
        (Tape.init []).move Dir3.right := by
  let G := NTM.guessBoundedTime B 0
  let guessNTM := NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)
  let c0 : Cfg (k + 3) NTM.GuessBoundedPhase :=
    { state := NTM.GuessBoundedPhase.choose, input := inp, work := work, output := out }
  obtain ⟨choicesG, hchoicesG⟩ :=
    NTM.guessBoundedNTM_choose_generates_witness_initTape_move_right
      (satWitnessIdx k) (satCounterIdx k) (Ne.symm (satCounterIdx_ne_witnessIdx k))
      B [] y c0 hlen rfl hpre.1 hpre.2.1 hpre.2.2.1
  obtain ⟨t, ht, hhalt, hfirst⟩ :=
    NTM.exists_first_halt_time_of_trace_halted guessNTM G choicesG c0 hchoicesG.1
  let choicesExit : Fin (t + 1) → Bool := fun i =>
    if hi : i.val < G then choicesG ⟨i.val, hi⟩ else false
  have hprefix_t :
      (fun i : Fin t => choicesExit ⟨i.val, by omega⟩) =
        fun i => choicesG (Fin.castLE ht i) := by
    funext i
    have hlt : (i.val : ℕ) < G := Nat.lt_of_lt_of_le i.isLt ht
    simp [choicesExit, hlt]
    apply congrArg choicesG
    exact Fin.ext rfl
  refine ⟨t, by simpa [G] using ht, choicesExit, ?_⟩
  let guessChoices : Fin t → Bool := fun i => choicesExit ⟨i.val, by omega⟩
  let cT := guessNTM.trace t guessChoices c0
  have hdone : (guessNTM.trace t
      (fun i => choicesExit ⟨i.val, by omega⟩) c0).state =
        NTM.GuessBoundedPhase.done := by
    change (guessNTM.trace t (fun i => choicesExit ⟨i.val, by omega⟩) c0).state =
      guessNTM.qhalt
    rw [hprefix_t]
    simpa [NTM.halted] using hhalt
  have hnot : ∀ s (hs : s < t),
      (guessNTM.trace s (fun i => choicesExit ⟨i.val, by omega⟩) c0).state ≠
        NTM.GuessBoundedPhase.done := by
    intro s hs
    have hprefix_s :
        (fun i : Fin s => choicesExit ⟨i.val, by omega⟩) =
          fun i => choicesG
            (Fin.castLE (le_trans (Nat.le_of_lt hs) ht) i) := by
      funext i
      have hlt : (i.val : ℕ) < G :=
        Nat.lt_of_lt_of_le i.isLt (le_trans (Nat.le_of_lt hs) ht)
      simp [choicesExit, hlt]
      apply congrArg choicesG
      exact Fin.ext rfl
    have hfirst_s := hfirst s hs
    change (guessNTM.trace s (fun i => choicesExit ⟨i.val, by omega⟩) c0).state ≠
      guessNTM.qhalt
    rw [hprefix_s]
    simpa [NTM.halted] using hfirst_s
  have hexit :=
    satGuessVerify_guess_trace_exit M t choicesExit c0 hnot hdone
  have hwitness_full :
      ((guessNTM.trace G choicesG c0).work (satWitnessIdx k)) =
        (Tape.init (y.map Γ.ofBool)).move Dir3.right := by
    simpa [G, guessNTM, c0] using hchoicesG.2
  let choicesT : Fin t → Bool := fun i => choicesG (Fin.castLE ht i)
  have heq := guessNTM.trace_mono ht (choices := choicesT) (choices' := choicesG)
    (c := c0) (by intro i; rfl) hhalt
  have hwitness_first :
      ((guessNTM.trace t choicesT c0).work (satWitnessIdx k)) =
        (Tape.init (y.map Γ.ofBool)).move Dir3.right := by
    rw [heq] at hwitness_full
    exact hwitness_full
  have hwitness_cT :
      cT.work (satWitnessIdx k) =
        (Tape.init (y.map Γ.ofBool)).move Dir3.right := by
    change ((guessNTM.trace t (fun i => choicesExit ⟨i.val, by omega⟩) c0).work
      (satWitnessIdx k)) = (Tape.init (y.map Γ.ofBool)).move Dir3.right
    rw [hprefix_t]
    exact hwitness_first
  have hpair_read : (work (satPairIdx k)).read ≠ Γ.start := by
    rw [hpre.2.2.2]
    simp [Tape.read, Tape.move, Tape.init]
  have hpair_trace :
      cT.work (satPairIdx k) = work (satPairIdx k) := by
    change ((guessNTM.trace t (fun i => choicesExit ⟨i.val, by omega⟩) c0).work
      (satPairIdx k)) = work (satPairIdx k)
    simpa [guessNTM, c0] using
      NTM.guessBoundedNTM_trace_preserves_other_work
        (satWitnessIdx k) (satCounterIdx k) (satPairIdx k) t
        (fun i => choicesExit ⟨i.val, by omega⟩) c0
        (Ne.symm (satWitnessIdx_ne_pairIdx k))
        (Ne.symm (satCounterIdx_ne_pairIdx k))
        (by simpa [c0] using hpair_read)
  have hpair_cT :
      cT.work (satPairIdx k) = (Tape.init []).move Dir3.right := by
    rw [hpair_trace]
    exact hpre.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · simpa [G, guessNTM, guessChoices, cT, choicesExit, c0] using hexit
  · have hread : (cT.work (satWitnessIdx k)).read ≠ Γ.start := by
      rw [hwitness_cT]
      exact Tape.init_ofBool_move_right_read_ne_start y
    rw [satBoundaryWork_stable_of_read_ne_start cT.work (satWitnessIdx k) hread]
    exact hwitness_cT
  · have hread : (cT.work (satPairIdx k)).read ≠ Γ.start := by
      rw [hpair_cT]
      simp [Tape.read, Tape.move, Tape.init]
    rw [satBoundaryWork_stable_of_read_ne_start cT.work (satPairIdx k) hread]
    exact hpair_cT

/-- Started-input strengthening of `satGuessVerify_guess_generates_with_pair_frame`.
    Besides producing the requested witness and preserving the blank pair tape,
    the phase exit keeps the exact started input tape needed by pair building. -/
theorem satGuessVerify_guess_generates_with_input_pair_frame (M : TM k) (B : ℕ)
    (x y : List Bool) (inp : Tape) (work : Fin (k + 3) → Tape) (out : Tape)
    (hlen : y.length ≤ B)
    (hinput : inp = (Tape.init (x.map Γ.ofBool)).move Dir3.right)
    (hpre : (work (satWitnessIdx k)).HasBinaryPrefix [] ∧
      (work (satWitnessIdx k)).cells 0 = Γ.start ∧
      (work (satCounterIdx k)).HasUnaryCounter B ∧
      work (satPairIdx k) = (Tape.init []).move Dir3.right) :
    ∃ t, ∃ _ : t ≤ NTM.guessBoundedTime B 0,
      ∃ choices : Fin (t + 1) → Bool,
      let guessNTM := NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)
      let guessChoices : Fin t → Bool := fun i => choices ⟨i.val, by omega⟩
      let c0 : Cfg (k + 3) NTM.GuessBoundedPhase :=
        { state := NTM.GuessBoundedPhase.choose, input := inp, work := work, output := out }
      let cT := guessNTM.trace t guessChoices c0
      (satGuessVerifyNTM M).trace (t + 1) choices (satGuessWrap M c0) =
        satPairWrap M
          { state := TM.PairBuildPhase.init,
            input := satBoundaryInput cT.input,
            work := satBoundaryWork cT.work,
            output := satBoundaryOutput cT.output } ∧
      satBoundaryInput cT.input =
        (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
      satBoundaryWork cT.work (satWitnessIdx k) =
        (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
      satBoundaryWork cT.work (satPairIdx k) =
        (Tape.init []).move Dir3.right := by
  obtain ⟨t, ht, choices, hguess⟩ :=
    satGuessVerify_guess_generates_with_pair_frame M B y inp work out hlen hpre
  refine ⟨t, ht, choices, ?_⟩
  let guessNTM := NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)
  let guessChoices : Fin t → Bool := fun i => choices ⟨i.val, by omega⟩
  let c0 : Cfg (k + 3) NTM.GuessBoundedPhase :=
    { state := NTM.GuessBoundedPhase.choose, input := inp, work := work, output := out }
  let cT := guessNTM.trace t guessChoices c0
  have hguess' :
      (satGuessVerifyNTM M).trace (t + 1) choices (satGuessWrap M c0) =
        satPairWrap M
          { state := TM.PairBuildPhase.init,
            input := satBoundaryInput cT.input,
            work := satBoundaryWork cT.work,
            output := satBoundaryOutput cT.output } ∧
      satBoundaryWork cT.work (satWitnessIdx k) =
        (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
      satBoundaryWork cT.work (satPairIdx k) =
        (Tape.init []).move Dir3.right := by
    simpa [guessNTM, guessChoices, c0, cT] using hguess
  have hinput_read : inp.read ≠ Γ.start := by
    rw [hinput]
    exact Tape.init_ofBool_move_right_read_ne_start x
  have hinput_cT : cT.input = inp := by
    simpa [guessNTM, guessChoices, c0, cT] using
      NTM.guessBoundedNTM_trace_preserves_input
        (satWitnessIdx k) (satCounterIdx k) t guessChoices c0 hinput_read
  refine ⟨hguess'.1, ?_, hguess'.2.1, hguess'.2.2⟩
  rw [hinput_cT, hinput]
  exact satBoundaryInput_stable ((Tape.init (x.map Γ.ofBool)).move Dir3.right)
    (by simp [Tape.move, Tape.init])
    (Tape.init_ofBool_move_right_cells_ne_start x)

/-- Compose input rewind with the completeness-oriented guess phase. Starting
    from a rewind configuration whose work/output frames already satisfy the
    guess preconditions, there is a choice sequence reaching pair-building with
    exact input, witness, and blank pair tapes. -/
theorem satGuessVerify_rewind_then_guess_generates_pair (M : TM k) (B : ℕ)
    (x y : List Bool) (inp : Tape) (work : Fin (k + 3) → Tape) (out : Tape)
    (hrewindPre : inp.cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → inp.cells j ≠ Γ.start) ∧ inp.head ≤ B)
    (hinput_cells : inp.cells = (Tape.init (x.map Γ.ofBool)).cells)
    (hout : out.read ≠ Γ.start ∧ out.head ≥ 1)
    (hwork : ∀ i, (work i).read ≠ Γ.start ∧ (work i).head ≥ 1)
    (hlen : y.length ≤ x.length + 1)
    (hguessPre : (work (satWitnessIdx k)).HasBinaryPrefix [] ∧
      (work (satWitnessIdx k)).cells 0 = Γ.start ∧
      (work (satCounterIdx k)).HasUnaryCounter (x.length + 1) ∧
      work (satPairIdx k) = (Tape.init []).move Dir3.right) :
    ∃ T, ∃ choices : Fin T → Bool,
      ∃ cPair : Cfg (k + 3) TM.PairBuildPhase,
        T ≤ B + 2 + 1 + (NTM.guessBoundedTime (x.length + 1) 0 + 1) ∧
        (satGuessVerifyNTM M).trace T choices
          (satRewindInputWrap M
            { state := TM.RewindPhase.moveLeft, input := inp, work := work, output := out }) =
          satPairWrap M cPair ∧
        cPair.state = TM.PairBuildPhase.init ∧
        cPair.input = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
        cPair.work (satWitnessIdx k) =
          (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
        cPair.work (satPairIdx k) = (Tape.init []).move Dir3.right ∧
        cPair.output = out ∧
        (∀ i : Fin k, cPair.work (satVerifierWorkIdx i) =
          work (satVerifierWorkIdx i)) := by
  let rewindAllChoices : Fin (B + 2 + 1) → Bool := fun _ => false
  obtain ⟨tr, htr, hrewind⟩ :=
    satGuessVerify_rewindInput_exits_with_frames_exact_input M B x inp work out
      hrewindPre hinput_cells hout hwork rewindAllChoices
  let rewindNTM := (TM.rewindInputTM (n := k + 3)).toNTM
  let rewindChoices : Fin tr → Bool := fun i => rewindAllChoices ⟨i.val, by omega⟩
  let cRewind0 : Cfg (k + 3) TM.RewindPhase :=
    { state := TM.RewindPhase.moveLeft, input := inp, work := work, output := out }
  let cR := rewindNTM.trace tr rewindChoices cRewind0
  have hrewind' :
      (satGuessVerifyNTM M).trace (tr + 1)
        (fun i => rewindAllChoices (Fin.castLE (by omega : tr + 1 ≤ B + 2 + 1) i))
        (satRewindInputWrap M cRewind0) =
        satGuessWrap M
          { state := NTM.GuessBoundedPhase.choose,
            input := satBoundaryInput cR.input,
            work := satBoundaryWork cR.work,
            output := satBoundaryOutput cR.output } ∧
      satBoundaryInput cR.input =
        (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
      satBoundaryWork cR.work = work ∧
      satBoundaryOutput cR.output = out := by
    simpa [rewindNTM, rewindChoices, cRewind0, cR] using hrewind
  have hguessPre' :
      ((satBoundaryWork cR.work) (satWitnessIdx k)).HasBinaryPrefix [] ∧
      ((satBoundaryWork cR.work) (satWitnessIdx k)).cells 0 = Γ.start ∧
      ((satBoundaryWork cR.work) (satCounterIdx k)).HasUnaryCounter (x.length + 1) ∧
      (satBoundaryWork cR.work) (satPairIdx k) =
        (Tape.init []).move Dir3.right := by
    rw [hrewind'.2.2.1]
    exact hguessPre
  obtain ⟨tg, htg, guessChoices, hguess⟩ :=
    satGuessVerify_guess_generates_with_input_pair_frame M (x.length + 1) x y
      (satBoundaryInput cR.input) (satBoundaryWork cR.work) (satBoundaryOutput cR.output)
      hlen hrewind'.2.1 hguessPre'
  let guessNTM := NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)
  let guessChoicesPrefix : Fin tg → Bool := fun i => guessChoices ⟨i.val, by omega⟩
  let cGuess0 : Cfg (k + 3) NTM.GuessBoundedPhase :=
    { state := NTM.GuessBoundedPhase.choose,
      input := satBoundaryInput cR.input,
      work := satBoundaryWork cR.work,
      output := satBoundaryOutput cR.output }
  let cG := guessNTM.trace tg guessChoicesPrefix cGuess0
  let cPair : Cfg (k + 3) TM.PairBuildPhase :=
    { state := TM.PairBuildPhase.init,
      input := satBoundaryInput cG.input,
      work := satBoundaryWork cG.work,
      output := satBoundaryOutput cG.output }
  let T := (tr + 1) + (tg + 1)
  let choices : Fin T → Bool := fun i =>
    if hi : i.val < tr + 1 then false
    else guessChoices ⟨i.val - (tr + 1), by omega⟩
  refine ⟨T, choices, cPair, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · have hprefixChoices :
        (fun i : Fin (tr + 1) =>
          choices (Fin.castLE (Nat.le_add_right (tr + 1) (tg + 1)) i)) =
        (fun i : Fin (tr + 1) =>
          rewindAllChoices (Fin.castLE (by omega : tr + 1 ≤ B + 2 + 1) i)) := by
      funext i
      unfold choices
      rw [dite_eq_left (by simpa [Fin.castLE] using i.isLt)]
    have hsuffixChoices :
        (fun i : Fin (tg + 1) => choices (Fin.natAdd (tr + 1) i)) =
          guessChoices := by
      funext i
      unfold choices
      rw [dite_eq_right (by simp [Fin.natAdd]; omega)]
      exact congrArg guessChoices (Fin.ext (by simp [Fin.natAdd]))
    rw [NTM.trace_add (satGuessVerifyNTM M) (tr + 1) (tg + 1)
      choices (satRewindInputWrap M cRewind0)]
    rw [hprefixChoices]
    rw [hrewind'.1]
    rw [hsuffixChoices]
    simpa [guessNTM, guessChoicesPrefix, cGuess0, cG, cPair] using hguess.1
  · rfl
  · simpa [cPair] using hguess.2.1
  · simpa [cPair] using hguess.2.2.1
  · simpa [cPair] using hguess.2.2.2
  · have hout_init_read :
        (satBoundaryOutput cR.output).read ≠ Γ.start := by
      rw [hrewind'.2.2.2]
      exact hout.1
    have hout_cG :
        cG.output = satBoundaryOutput cR.output := by
      simpa [guessNTM, guessChoicesPrefix, cGuess0, cG] using
        NTM.guessBoundedNTM_trace_preserves_output
          (satWitnessIdx k) (satCounterIdx k) tg guessChoicesPrefix cGuess0
          (by simpa [cGuess0] using hout_init_read)
    change satBoundaryOutput cG.output = out
    rw [hout_cG, hrewind'.2.2.2]
    exact satBoundaryOutput_stable_of_read_ne_start out hout.1
  · intro i
    have hwork_init_read :
        ((satBoundaryWork cR.work) (satVerifierWorkIdx i)).read ≠ Γ.start := by
      rw [hrewind'.2.2.1]
      exact (hwork (satVerifierWorkIdx i)).1
    have hwork_cG :
        cG.work (satVerifierWorkIdx i) =
          (satBoundaryWork cR.work) (satVerifierWorkIdx i) := by
      simpa [guessNTM, guessChoicesPrefix, cGuess0, cG] using
        NTM.guessBoundedNTM_trace_preserves_other_work
          (satWitnessIdx k) (satCounterIdx k) (satVerifierWorkIdx i) tg
          guessChoicesPrefix cGuess0
          (satVerifierWorkIdx_ne_witnessIdx i)
          (satVerifierWorkIdx_ne_counterIdx i)
          (by simpa [cGuess0] using hwork_init_read)
    change satBoundaryWork cG.work (satVerifierWorkIdx i) = work (satVerifierWorkIdx i)
    rw [satBoundaryWork_stable_of_read_ne_start cG.work (satVerifierWorkIdx i) (by
      rw [hwork_cG]
      exact hwork_init_read)]
    rw [hwork_cG, hrewind'.2.2.1]

/-- Compose counter setup, input rewind, and the completeness-oriented guess
    phase from the actual composed-machine initial configuration. The result is
    a pair-phase configuration with exact input, requested witness, and a blank
    pair tape. -/
theorem satGuessVerify_setup_generates_pair (M : TM k) (x y : List Bool)
    (hlen : y.length ≤ x.length + 1) :
    ∃ T, ∃ choices : Fin T → Bool,
      ∃ cPair : Cfg (k + 3) TM.PairBuildPhase,
        T ≤
          TM.inputLengthPlusOneCounterTime x.length + 1 +
            (TM.inputLengthPlusOneCounterTime x.length + 1 + 2 + 1 +
              (NTM.guessBoundedTime (x.length + 1) 0 + 1)) ∧
        (satGuessVerifyNTM M).trace T choices ((satGuessVerifyNTM M).initCfg x) =
          satPairWrap M cPair ∧
        cPair.state = TM.PairBuildPhase.init ∧
        cPair.input = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
        cPair.work (satWitnessIdx k) =
          (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
        cPair.work (satPairIdx k) = (Tape.init []).move Dir3.right ∧
        cPair.output = (Tape.init []).move Dir3.right ∧
        (∀ i : Fin k, cPair.work (satVerifierWorkIdx i) =
          (Tape.init []).move Dir3.right) := by
  let C := TM.inputLengthPlusOneCounterTime x.length
  let counterAllChoices : Fin (C + 1) → Bool := fun _ => false
  obtain ⟨tc, htc, hcounter⟩ :=
    satGuessVerify_counter_init_exits M x counterAllChoices
  let counterNTM := (TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM
  let counterChoices : Fin tc → Bool := fun i => counterAllChoices ⟨i.val, by omega⟩
  let cCounter0 : Cfg (k + 3) TM.LinearCounterPhase :=
    { state := TM.LinearCounterPhase.scan,
      input := Tape.init (x.map Γ.ofBool),
      work := fun _ => Tape.init [],
      output := Tape.init [] }
  let cC := counterNTM.trace tc counterChoices cCounter0
  have hcounter' :
      (satGuessVerifyNTM M).trace (tc + 1)
        (fun i => counterAllChoices (Fin.castLE (by omega : tc + 1 ≤ C + 1) i))
        ((satGuessVerifyNTM M).initCfg x) =
        satRewindInputWrap M
          { state := TM.RewindPhase.moveLeft,
            input := satBoundaryInput cC.input,
            work := satBoundaryWork cC.work,
            output := satBoundaryOutput cC.output } ∧
      (satBoundaryInput cC.input).cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → (satBoundaryInput cC.input).cells j ≠ Γ.start) ∧
      (satBoundaryInput cC.input).cells =
        (Tape.init (x.map Γ.ofBool)).cells ∧
      (satBoundaryInput cC.input).head ≤ C + 1 ∧
      (satBoundaryWork cC.work (satCounterIdx k)).HasUnaryCounter (x.length + 1) ∧
      (∀ i, i ≠ satCounterIdx k →
        satBoundaryWork cC.work i = (Tape.init []).move Dir3.right) ∧
      satBoundaryWork cC.work (satWitnessIdx k) =
        (Tape.init []).move Dir3.right ∧
      satBoundaryWork cC.work (satPairIdx k) =
        (Tape.init []).move Dir3.right ∧
      satBoundaryOutput cC.output =
        (Tape.init []).move Dir3.right := by
    simpa [C, counterNTM, counterChoices, cCounter0, cC] using hcounter
  let inpR := satBoundaryInput cC.input
  let workR := satBoundaryWork cC.work
  let outR := satBoundaryOutput cC.output
  have hcounterInputPre :
      inpR.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → inpR.cells j ≠ Γ.start) ∧ inpR.head ≤ C + 1 := by
    exact ⟨hcounter'.2.1, hcounter'.2.2.1, hcounter'.2.2.2.2.1⟩
  have hcounterInputCells :
      inpR.cells = (Tape.init (x.map Γ.ofBool)).cells :=
    hcounter'.2.2.2.1
  have hcounterUnary :
      (workR (satCounterIdx k)).HasUnaryCounter (x.length + 1) :=
    hcounter'.2.2.2.2.2.1
  have hothers :
      ∀ i, i ≠ satCounterIdx k →
        workR i = (Tape.init []).move Dir3.right :=
    hcounter'.2.2.2.2.2.2.1
  have hwitnessBlank :
      workR (satWitnessIdx k) = (Tape.init []).move Dir3.right :=
    hcounter'.2.2.2.2.2.2.2.1
  have hpairBlank :
      workR (satPairIdx k) = (Tape.init []).move Dir3.right :=
    hcounter'.2.2.2.2.2.2.2.2.1
  have houtBlank : outR = (Tape.init []).move Dir3.right :=
    hcounter'.2.2.2.2.2.2.2.2.2
  have houtR : outR.read ≠ Γ.start ∧ outR.head ≥ 1 := by
    rw [houtBlank]
    constructor <;> simp [Tape.read, Tape.move, Tape.init]
  have hworkR : ∀ i, (workR i).read ≠ Γ.start ∧ (workR i).head ≥ 1 := by
    intro i
    by_cases hic : i = satCounterIdx k
    · subst i
      constructor
      · have hread := Tape.hasUnaryCounter_read_pos hcounterUnary (by omega : 0 < x.length + 1)
        rw [hread]
        simp
      · rw [hcounterUnary.1]
    · have hblank := hothers i hic
      rw [hblank]
      constructor <;> simp [Tape.read, Tape.move, Tape.init]
  have hguessPreR :
      (workR (satWitnessIdx k)).HasBinaryPrefix [] ∧
      (workR (satWitnessIdx k)).cells 0 = Γ.start ∧
      (workR (satCounterIdx k)).HasUnaryCounter (x.length + 1) ∧
      workR (satPairIdx k) = (Tape.init []).move Dir3.right := by
    refine ⟨?_, ?_, hcounterUnary, hpairBlank⟩
    · rw [hwitnessBlank]
      exact Tape.init_nil_move_right_hasBinaryPrefix_nil
    · rw [hwitnessBlank]
      simp [Tape.move, Tape.init]
  obtain ⟨Ttail, tailChoices, cPair, hTtail, htailTrace, hpairState,
    hpairInput, hpairWitness, hpairBlankFinal, hpairOutput, hpairVerifierWork⟩ :=
    satGuessVerify_rewind_then_guess_generates_pair M (C + 1) x y
      inpR workR outR hcounterInputPre hcounterInputCells houtR hworkR hlen hguessPreR
  let T := (tc + 1) + Ttail
  let choices : Fin T → Bool := fun i =>
    if hi : i.val < tc + 1 then false
    else tailChoices ⟨i.val - (tc + 1), by omega⟩
  refine ⟨T, choices, cPair, ?_, ?_, hpairState, hpairInput, hpairWitness,
    hpairBlankFinal, ?_, ?_⟩
  · omega
  · have hprefixChoices :
        (fun i : Fin (tc + 1) =>
          choices (Fin.castLE (Nat.le_add_right (tc + 1) Ttail) i)) =
        (fun i : Fin (tc + 1) =>
          counterAllChoices (Fin.castLE (by omega : tc + 1 ≤ C + 1) i)) := by
      funext i
      unfold choices
      rw [dite_eq_left (by simpa [Fin.castLE] using i.isLt)]
    have hsuffixChoices :
        (fun i : Fin Ttail => choices (Fin.natAdd (tc + 1) i)) =
          tailChoices := by
      funext i
      unfold choices
      rw [dite_eq_right (by simp [Fin.natAdd]; omega)]
      exact congrArg tailChoices (Fin.ext (by simp [Fin.natAdd]))
    rw [NTM.trace_add (satGuessVerifyNTM M) (tc + 1) Ttail
      choices ((satGuessVerifyNTM M).initCfg x)]
    rw [hprefixChoices]
    rw [hcounter'.1]
    rw [hsuffixChoices]
    simpa [inpR, workR, outR] using htailTrace
  · rw [hpairOutput]
    exact houtBlank
  · intro i
    rw [hpairVerifierWork i]
    exact hothers (satVerifierWorkIdx i) (satVerifierWorkIdx_ne_counterIdx i)

/-- Arbitrary-choice setup composition from the real initial configuration.
    Within the setup budget, every setup choice prefix reaches pair building
    with some bounded witness, exact started input, blank pair/output tapes, and
    blank verifier work tapes. -/
theorem satGuessVerify_setup_exits_with_pair_frames (M : TM k) (x : List Bool)
    (choices : Fin (satGuessVerifySetupTime x.length) → Bool) :
    ∃ T, ∃ hT : T ≤ satGuessVerifySetupTime x.length,
      ∃ y : List Bool, y.length ≤ x.length + 1 ∧
      ∃ cPair : Cfg (k + 3) TM.PairBuildPhase,
        let setupChoices : Fin T → Bool := fun i => choices (Fin.castLE hT i)
        (satGuessVerifyNTM M).trace T setupChoices ((satGuessVerifyNTM M).initCfg x) =
          satPairWrap M cPair ∧
        cPair.state = TM.PairBuildPhase.init ∧
        cPair.input = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
        cPair.work (satWitnessIdx k) =
          (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
        cPair.work (satPairIdx k) = (Tape.init []).move Dir3.right ∧
        cPair.output = (Tape.init []).move Dir3.right ∧
        (∀ i : Fin k, cPair.work (satVerifierWorkIdx i) =
          (Tape.init []).move Dir3.right) := by
  let C := TM.inputLengthPlusOneCounterTime x.length
  let B := x.length + 1
  let G := NTM.guessBoundedTime B 0
  let counterAllChoices : Fin (C + 1) → Bool := fun i =>
    choices (Fin.castLE (by
      unfold satGuessVerifySetupTime
      omega) i)
  obtain ⟨tc, htc, hcounter⟩ :=
    satGuessVerify_counter_init_exits M x counterAllChoices
  let counterNTM := (TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM
  let counterChoices : Fin tc → Bool := fun i => counterAllChoices ⟨i.val, by omega⟩
  let cCounter0 : Cfg (k + 3) TM.LinearCounterPhase :=
    { state := TM.LinearCounterPhase.scan,
      input := Tape.init (x.map Γ.ofBool),
      work := fun _ => Tape.init [],
      output := Tape.init [] }
  let cC := counterNTM.trace tc counterChoices cCounter0
  have hcounter' :
      (satGuessVerifyNTM M).trace (tc + 1)
        (fun i => counterAllChoices (Fin.castLE (by omega : tc + 1 ≤ C + 1) i))
        ((satGuessVerifyNTM M).initCfg x) =
        satRewindInputWrap M
          { state := TM.RewindPhase.moveLeft,
            input := satBoundaryInput cC.input,
            work := satBoundaryWork cC.work,
            output := satBoundaryOutput cC.output } ∧
      (satBoundaryInput cC.input).cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → (satBoundaryInput cC.input).cells j ≠ Γ.start) ∧
      (satBoundaryInput cC.input).cells =
        (Tape.init (x.map Γ.ofBool)).cells ∧
      (satBoundaryInput cC.input).head ≤ C + 1 ∧
      (satBoundaryWork cC.work (satCounterIdx k)).HasUnaryCounter B ∧
      (∀ i, i ≠ satCounterIdx k →
        satBoundaryWork cC.work i = (Tape.init []).move Dir3.right) ∧
      satBoundaryWork cC.work (satWitnessIdx k) =
        (Tape.init []).move Dir3.right ∧
      satBoundaryWork cC.work (satPairIdx k) =
        (Tape.init []).move Dir3.right ∧
      satBoundaryOutput cC.output =
        (Tape.init []).move Dir3.right := by
    simpa [C, B, counterNTM, counterChoices, cCounter0, cC] using hcounter
  let inpR := satBoundaryInput cC.input
  let workR := satBoundaryWork cC.work
  let outR := satBoundaryOutput cC.output
  have hcounterInputPre :
      inpR.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → inpR.cells j ≠ Γ.start) ∧ inpR.head ≤ C + 1 := by
    exact ⟨hcounter'.2.1, hcounter'.2.2.1, hcounter'.2.2.2.2.1⟩
  have hcounterInputCells :
      inpR.cells = (Tape.init (x.map Γ.ofBool)).cells :=
    hcounter'.2.2.2.1
  have hcounterUnary :
      (workR (satCounterIdx k)).HasUnaryCounter B :=
    hcounter'.2.2.2.2.2.1
  have hothers :
      ∀ i, i ≠ satCounterIdx k →
        workR i = (Tape.init []).move Dir3.right :=
    hcounter'.2.2.2.2.2.2.1
  have hwitnessBlank :
      workR (satWitnessIdx k) = (Tape.init []).move Dir3.right :=
    hcounter'.2.2.2.2.2.2.2.1
  have hpairBlank :
      workR (satPairIdx k) = (Tape.init []).move Dir3.right :=
    hcounter'.2.2.2.2.2.2.2.2.1
  have houtBlank : outR = (Tape.init []).move Dir3.right :=
    hcounter'.2.2.2.2.2.2.2.2.2
  have houtR : outR.read ≠ Γ.start ∧ outR.head ≥ 1 := by
    rw [houtBlank]
    constructor <;> simp [Tape.read, Tape.move, Tape.init]
  have hworkR : ∀ i, (workR i).read ≠ Γ.start ∧ (workR i).head ≥ 1 := by
    intro i
    by_cases hic : i = satCounterIdx k
    · subst i
      constructor
      · have hread := Tape.hasUnaryCounter_read_pos hcounterUnary (by omega : 0 < B)
        rw [hread]
        simp
      · rw [hcounterUnary.1]
    · have hblank := hothers i hic
      rw [hblank]
      constructor <;> simp [Tape.read, Tape.move, Tape.init]
  let rewindAllChoices : Fin (C + 1 + 2 + 1) → Bool := fun i =>
    choices ⟨tc + 1 + i.val, by
      unfold satGuessVerifySetupTime
      omega⟩
  obtain ⟨tr, htr, hrewind⟩ :=
    satGuessVerify_rewindInput_exits_with_frames_exact_input M (C + 1) x
      inpR workR outR hcounterInputPre hcounterInputCells houtR hworkR
      rewindAllChoices
  let rewindNTM := (TM.rewindInputTM (n := k + 3)).toNTM
  let rewindChoices : Fin tr → Bool := fun i => rewindAllChoices ⟨i.val, by omega⟩
  let cRewind0 : Cfg (k + 3) TM.RewindPhase :=
    { state := TM.RewindPhase.moveLeft, input := inpR, work := workR, output := outR }
  let cR := rewindNTM.trace tr rewindChoices cRewind0
  have hrewind' :
      (satGuessVerifyNTM M).trace (tr + 1)
        (fun i => rewindAllChoices (Fin.castLE (by omega : tr + 1 ≤ C + 1 + 2 + 1) i))
        (satRewindInputWrap M cRewind0) =
        satGuessWrap M
          { state := NTM.GuessBoundedPhase.choose,
            input := satBoundaryInput cR.input,
            work := satBoundaryWork cR.work,
            output := satBoundaryOutput cR.output } ∧
      satBoundaryInput cR.input =
        (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
      satBoundaryWork cR.work = workR ∧
      satBoundaryOutput cR.output = outR := by
    simpa [rewindNTM, rewindChoices, cRewind0, cR] using hrewind
  have hguessPre :
      ((satBoundaryWork cR.work) (satWitnessIdx k)).HasBinaryPrefix [] ∧
      ((satBoundaryWork cR.work) (satWitnessIdx k)).cells 0 = Γ.start ∧
      ((satBoundaryWork cR.work) (satCounterIdx k)).HasUnaryCounter B ∧
      (satBoundaryWork cR.work) (satPairIdx k) =
        (Tape.init []).move Dir3.right := by
    rw [hrewind'.2.2.1]
    refine ⟨?_, ?_, hcounterUnary, hpairBlank⟩
    · rw [hwitnessBlank]
      exact Tape.init_nil_move_right_hasBinaryPrefix_nil
    · rw [hwitnessBlank]
      simp [Tape.move, Tape.init]
  have hguessInput :
      (satBoundaryInput cR.input).head ≥ 1 ∧
        ∀ j, j ≥ 1 → (satBoundaryInput cR.input).cells j ≠ Γ.start := by
    rw [hrewind'.2.1]
    exact ⟨by simp [Tape.move, Tape.init],
      Tape.init_ofBool_move_right_cells_ne_start x⟩
  have hguessOut : (satBoundaryOutput cR.output).read ≠ Γ.start := by
    rw [hrewind'.2.2.2, houtBlank]
    simp [Tape.read, Tape.move, Tape.init]
  have hguessWork : ∀ i : Fin k,
      ((satBoundaryWork cR.work) (satVerifierWorkIdx i)).read ≠ Γ.start := by
    intro i
    rw [hrewind'.2.2.1]
    exact (hworkR (satVerifierWorkIdx i)).1
  have hguessAllBound :
      ∀ i : Fin (G + 1), tc + 1 + (tr + 1) + i.val < satGuessVerifySetupTime x.length := by
    intro i
    unfold G B satGuessVerifySetupTime
    omega
  let guessAllChoices : Fin (G + 1) → Bool := fun i =>
    choices ⟨tc + 1 + (tr + 1) + i.val, hguessAllBound i⟩
  obtain ⟨tg, htg, y, hy, hguess⟩ :=
    satGuessVerify_guess_exits_with_frames M B
      (satBoundaryInput cR.input) (satBoundaryWork cR.work)
      (satBoundaryOutput cR.output) hguessPre hguessInput hguessOut
      hguessWork guessAllChoices
  let guessNTM := NTM.guessBoundedNTM (satWitnessIdx k) (satCounterIdx k)
  let guessChoices : Fin tg → Bool := fun i => guessAllChoices ⟨i.val, by omega⟩
  let cGuess0 : Cfg (k + 3) NTM.GuessBoundedPhase :=
    { state := NTM.GuessBoundedPhase.choose,
      input := satBoundaryInput cR.input,
      work := satBoundaryWork cR.work,
      output := satBoundaryOutput cR.output }
  let cG := guessNTM.trace tg guessChoices cGuess0
  let cPair : Cfg (k + 3) TM.PairBuildPhase :=
    { state := TM.PairBuildPhase.init,
      input := satBoundaryInput cG.input,
      work := satBoundaryWork cG.work,
      output := satBoundaryOutput cG.output }
  have hguess' :
      (satGuessVerifyNTM M).trace (tg + 1)
        (fun i => guessAllChoices (Fin.castLE (by omega : tg + 1 ≤ G + 1) i))
        (satGuessWrap M cGuess0) =
        satPairWrap M cPair ∧
      satBoundaryInput cG.input = satBoundaryInput cR.input ∧
      satBoundaryWork cG.work (satWitnessIdx k) =
        (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
      satBoundaryWork cG.work (satPairIdx k) =
        (Tape.init []).move Dir3.right ∧
      satBoundaryOutput cG.output = satBoundaryOutput cR.output ∧
      (∀ i : Fin k, satBoundaryWork cG.work (satVerifierWorkIdx i) =
        (satBoundaryWork cR.work) (satVerifierWorkIdx i)) := by
    simpa [G, guessNTM, guessChoices, cGuess0, cG, cPair] using hguess
  let T := (tc + 1) + ((tr + 1) + (tg + 1))
  have hT : T ≤ satGuessVerifySetupTime x.length := by
    have htg' : tg ≤ NTM.guessBoundedTime (x.length + 1) 0 := by
      simpa [B] using htg
    dsimp [T, satGuessVerifySetupTime]
    omega
  let setupChoices : Fin T → Bool := fun i => choices (Fin.castLE hT i)
  refine ⟨T, hT, y, hy, cPair, ?_⟩
  have hcounterChoices :
      (fun i : Fin (tc + 1) =>
        setupChoices (Fin.castLE (Nat.le_add_right (tc + 1) ((tr + 1) + (tg + 1))) i)) =
      (fun i : Fin (tc + 1) =>
        counterAllChoices (Fin.castLE (by omega : tc + 1 ≤ C + 1) i)) := by
    funext i
    simp [setupChoices, counterAllChoices, Fin.castLE]
  have htailTrace :
      (satGuessVerifyNTM M).trace ((tr + 1) + (tg + 1))
        (fun i => setupChoices (Fin.natAdd (tc + 1) i))
        (satRewindInputWrap M cRewind0) =
        satPairWrap M cPair := by
    have hrewindChoices :
        (fun i : Fin (tr + 1) =>
          (fun i : Fin ((tr + 1) + (tg + 1)) =>
            setupChoices (Fin.natAdd (tc + 1) i))
            (Fin.castLE (Nat.le_add_right (tr + 1) (tg + 1)) i)) =
        (fun i : Fin (tr + 1) =>
          rewindAllChoices (Fin.castLE (by omega : tr + 1 ≤ C + 1 + 2 + 1) i)) := by
      funext i
      simp [setupChoices, rewindAllChoices, Fin.castLE, Fin.natAdd]
    have hguessChoices :
        (fun i : Fin (tg + 1) =>
          (fun i : Fin ((tr + 1) + (tg + 1)) =>
            setupChoices (Fin.natAdd (tc + 1) i))
            (Fin.natAdd (tr + 1) i)) =
        (fun i : Fin (tg + 1) =>
          guessAllChoices (Fin.castLE (by omega : tg + 1 ≤ G + 1) i)) := by
      funext i
      change choices ⟨tc + 1 + ((tr + 1) + i.val), by omega⟩ =
        choices ⟨tc + 1 + (tr + 1) + i.val, by omega⟩
      exact congrArg choices (Fin.ext ((Nat.add_assoc (tc + 1) (tr + 1) i.val).symm))
    rw [NTM.trace_add (satGuessVerifyNTM M) (tr + 1) (tg + 1)
      (fun i : Fin ((tr + 1) + (tg + 1)) =>
        setupChoices (Fin.natAdd (tc + 1) i)) (satRewindInputWrap M cRewind0)]
    rw [hrewindChoices, hrewind'.1, hguessChoices]
    exact hguess'.1
  change
    (satGuessVerifyNTM M).trace ((tc + 1) + ((tr + 1) + (tg + 1)))
        setupChoices ((satGuessVerifyNTM M).initCfg x) = satPairWrap M cPair ∧
      cPair.state = TM.PairBuildPhase.init ∧
      cPair.input = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
      cPair.work (satWitnessIdx k) =
        (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
      cPair.work (satPairIdx k) = (Tape.init []).move Dir3.right ∧
      cPair.output = (Tape.init []).move Dir3.right ∧
      (∀ i : Fin k, cPair.work (satVerifierWorkIdx i) =
        (Tape.init []).move Dir3.right)
  rw [NTM.trace_add (satGuessVerifyNTM M) (tc + 1) ((tr + 1) + (tg + 1))
    setupChoices ((satGuessVerifyNTM M).initCfg x)]
  rw [hcounterChoices, hcounter'.1]
  rw [htailTrace]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show cPair.input = satBoundaryInput cG.input by rfl, hguess'.2.1,
      hrewind'.2.1]
  · simpa [cPair] using hguess'.2.2.1
  · simpa [cPair] using hguess'.2.2.2.1
  · rw [show cPair.output = satBoundaryOutput cG.output by rfl,
      hguess'.2.2.2.2.1, hrewind'.2.2.2, houtBlank]
  · intro i
    rw [show cPair.work (satVerifierWorkIdx i) =
      satBoundaryWork cG.work (satVerifierWorkIdx i) by rfl,
      hguess'.2.2.2.2.2 i, hrewind'.2.2.1]
    exact hothers (satVerifierWorkIdx i) (satVerifierWorkIdx_ne_counterIdx i)

/-- One composed-machine step on a non-done pair configuration simulates one
    step of the pair-builder subroutine. -/
theorem satGuessVerify_pair_trace_one (M : TM k)
    (choice : Bool) (c : Cfg (k + 3) TM.PairBuildPhase)
    (hstate : c.state ≠ TM.PairBuildPhase.done) :
    (satGuessVerifyNTM M).trace 1 (fun _ => choice) (satPairWrap M c) =
      satPairWrap M
        (((TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM).trace 1
          (fun _ => choice) c) := by
  cases c with
  | mk state input work output =>
    have hstate' : state ≠ TM.PairBuildPhase.done := by
      simpa using hstate
    simp [satPairWrap, satGuessVerifyNTM, satGuessVerifyDelta, NTM.trace,
      TM.toNTM, TM.pairBuildTM, hstate']

/-- Multi-step pair-builder simulation up to, but not across, the pair
    subroutine's halt state. -/
theorem satGuessVerify_pair_trace_prefix (M : TM k) :
    ∀ (T : ℕ) (choices : Fin T → Bool)
      (c : Cfg (k + 3) TM.PairBuildPhase),
      (∀ t (ht : t < T),
        (((TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM).trace t
          (fun i => choices ⟨i.val, Nat.lt_trans i.isLt ht⟩) c).state ≠
            TM.PairBuildPhase.done) →
      (satGuessVerifyNTM M).trace T choices (satPairWrap M c) =
        satPairWrap M
          (((TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM).trace T choices c) := by
  intro T
  induction T with
  | zero =>
      intro choices c _hnot
      rfl
  | succ T ih =>
      intro choices c hnot
      let pairNTM := (TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM
      let choicesTail : Fin T → Bool := fun i => choices ⟨i.val + 1, by omega⟩
      let c1 : Cfg (k + 3) TM.PairBuildPhase :=
        pairNTM.trace 1 (fun _ => choices ⟨0, by omega⟩) c
      have hstate : c.state ≠ TM.PairBuildPhase.done := by
        have h0 := hnot 0 (by omega)
        exact h0
      rw [NTM.trace_succ (satGuessVerifyNTM M) T choices (satPairWrap M c)]
      rw [satGuessVerify_pair_trace_one M (choices ⟨0, by omega⟩) c hstate]
      have htail : ∀ t (ht : t < T),
          (pairNTM.trace t
            (fun i => choicesTail ⟨i.val, Nat.lt_trans i.isLt ht⟩) c1).state ≠
              TM.PairBuildPhase.done := by
        intro t ht
        have hfull := hnot (t + 1) (by omega)
        let choicesPrefix : Fin (t + 1) → Bool := fun i => choices ⟨i.val, by omega⟩
        have hsplit :=
          NTM.trace_succ pairNTM t choicesPrefix c
        change (pairNTM.trace t
          (fun i => choicesTail ⟨i.val, Nat.lt_trans i.isLt ht⟩) c1).state ≠
            TM.PairBuildPhase.done
        rw [← hsplit]
        exact hfull
      rw [ih choicesTail c1 htail]
      have hsplitFull :=
        NTM.trace_succ pairNTM T choices c
      rw [hsplitFull]

/-- If the pair-builder subroutine first reaches `done` at time `T`, then the
    composed machine exits the pair phase on the next step. -/
theorem satGuessVerify_pair_trace_exit (M : TM k) (T : ℕ)
    (choices : Fin (T + 1) → Bool)
    (c : Cfg (k + 3) TM.PairBuildPhase)
    (hnot : ∀ t (ht : t < T),
      (((TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM).trace t
        (fun i => choices ⟨i.val, by omega⟩) c).state ≠
          TM.PairBuildPhase.done)
    (hdone :
      (((TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM).trace T
        (fun i => choices ⟨i.val, by omega⟩) c).state =
          TM.PairBuildPhase.done) :
    let pairNTM := (TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM
    let pairChoices : Fin T → Bool := fun i => choices ⟨i.val, by omega⟩
    let cT := pairNTM.trace T pairChoices c
    (satGuessVerifyNTM M).trace (T + 1) choices (satPairWrap M c) =
      satVerifyWrap M
        { state := verifierStartedState M,
          input := satBoundaryInput cT.input,
          work := satBoundaryWork cT.work,
          output := satBoundaryOutput cT.output } := by
  let pairNTM := (TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM
  let pairChoices : Fin T → Bool := fun i => choices ⟨i.val, by omega⟩
  let cT := pairNTM.trace T pairChoices c
  have hprefixHyp : ∀ t (ht : t < T),
      (pairNTM.trace t
        (fun i => pairChoices ⟨i.val, Nat.lt_trans i.isLt ht⟩) c).state ≠
          TM.PairBuildPhase.done := by
    intro t ht
    simpa [pairNTM, pairChoices] using hnot t ht
  have hprefix :=
    satGuessVerify_pair_trace_prefix M T pairChoices c hprefixHyp
  have hsplit :=
    NTM.trace_snoc (satGuessVerifyNTM M) T choices (satPairWrap M c)
  have hprefix' :
      (satGuessVerifyNTM M).trace T
          (fun i => choices i.castSucc) (satPairWrap M c) =
        satPairWrap M cT := by
    simp [pairNTM, pairChoices, cT]
    exact hprefix
  rw [hsplit, hprefix']
  change (satGuessVerifyNTM M).trace 1
      (fun _ => choices (Fin.last T)) (satPairWrap M cT) =
    satVerifyWrap M
      { state := verifierStartedState M,
        input := satBoundaryInput cT.input,
        work := satBoundaryWork cT.work,
        output := satBoundaryOutput cT.output }
  have hdone' : cT.state = TM.PairBuildPhase.done := by
    simpa [cT, pairNTM, pairChoices] using hdone
  simp [satPairWrap, satVerifyWrap, satGuessVerifyNTM, satGuessVerifyDelta,
    phaseBoundary, satBoundaryInput, satBoundaryOutput, NTM.trace, hdone']
  funext i
  rfl

/-- From a standard pair-builder phase start, the composed machine reaches
    verifier simulation within the pair-builder bound plus the one boundary
    step. -/
theorem satGuessVerify_pair_exits (M : TM k) (x y : List Bool)
    (work : Fin (k + 3) → Tape) (out : Tape)
    (hpre :
      work (satWitnessIdx k) = (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
      work (satPairIdx k) = (Tape.init []).move Dir3.right)
    (choices : Fin (TM.pairBuildTime x.length y.length + 1) → Bool) :
    ∃ t, ∃ ht : t ≤ TM.pairBuildTime x.length y.length,
      let pairNTM := (TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM
      let pairChoices : Fin t → Bool := fun i => choices ⟨i.val, by omega⟩
      let c0 : Cfg (k + 3) TM.PairBuildPhase :=
        { state := TM.PairBuildPhase.init,
          input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
          work := work,
          output := out }
      let cT := pairNTM.trace t pairChoices c0
      (satGuessVerifyNTM M).trace (t + 1)
        (fun i => choices (Fin.castLE (by omega : t + 1 ≤
          TM.pairBuildTime x.length y.length + 1) i))
        (satPairWrap M c0) =
        satVerifyWrap M
          { state := verifierStartedState M,
            input := satBoundaryInput cT.input,
            work := satBoundaryWork cT.work,
            output := satBoundaryOutput cT.output } ∧
      satBoundaryWork cT.work (satPairIdx k) =
        (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right := by
  let P := TM.pairBuildTime x.length y.length
  let pairNTM := (TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM
  let pairChoicesP : Fin P → Bool := fun i => choices ⟨i.val, by omega⟩
  let inp0 := (Tape.init (x.map Γ.ofBool)).move Dir3.right
  let c0 : Cfg (k + 3) TM.PairBuildPhase :=
    { state := TM.PairBuildPhase.init, input := inp0, work := work, output := out }
  have hpair :=
    TM.pairBuildTM_toNTM_hoareTime_all_started_initTape_move_right
      (satWitnessIdx k) (satPairIdx k) (satWitnessIdx_ne_pairIdx k) x y
  have hpre' :
      inp0 = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
      work (satWitnessIdx k) = (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
      work (satPairIdx k) = (Tape.init []).move Dir3.right := by
    exact ⟨rfl, hpre.1, hpre.2⟩
  obtain ⟨t, ht, hhalt, hpost, hfirst⟩ :=
    hpair.exists_first_halt_time_with_post
      (inp := inp0) (work := work) (out := out) hpre' pairChoicesP
  refine ⟨t, by simpa [P] using ht, ?_⟩
  let pairChoices : Fin t → Bool := fun i => choices ⟨i.val, by omega⟩
  let cT := pairNTM.trace t pairChoices c0
  let choicesExit : Fin (t + 1) → Bool :=
    fun i => choices (Fin.castLE (by omega : t + 1 ≤ P + 1) i)
  have hdone : (pairNTM.trace t
      (fun i => choicesExit ⟨i.val, by omega⟩) c0).state =
        TM.PairBuildPhase.done := by
    simp [P, pairNTM, choicesExit, c0, inp0]
    exact hhalt
  have hnot : ∀ s (hs : s < t),
      (pairNTM.trace s (fun i => choicesExit ⟨i.val, by omega⟩) c0).state ≠
        TM.PairBuildPhase.done := by
    intro s hs
    have hfirst_s := hfirst s hs
    simp [P, pairNTM, choicesExit, c0, inp0]
    exact hfirst_s
  have hexit :=
    satGuessVerify_pair_trace_exit M t choicesExit c0 hnot hdone
  refine ⟨?_, ?_⟩
  · simpa [P, pairNTM, pairChoices, cT, choicesExit, c0, inp0] using hexit
  · have hpair_post :
        cT.work (satPairIdx k) =
          (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right := by
      simp [pairNTM, pairChoices, cT, c0, inp0]
      exact hpost
    have hread : (cT.work (satPairIdx k)).read ≠ Γ.start := by
      rw [hpair_post]
      exact Tape.init_ofBool_move_right_read_ne_start (pair x y)
    rw [satBoundaryWork_stable_of_read_ne_start cT.work (satPairIdx k) hread]
    exact hpair_post

/-- Pair-builder exit with the verifier frame exposed. Besides the exact pair
    tape, this packages preservation of the output tape and every internal
    verifier work tape through pair construction and the boundary step. -/
theorem satGuessVerify_pair_exits_with_verifier_frames (M : TM k) (x y : List Bool)
    (work : Fin (k + 3) → Tape) (out : Tape)
    (hpre :
      work (satWitnessIdx k) = (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
      work (satPairIdx k) = (Tape.init []).move Dir3.right)
    (hout : out.read ≠ Γ.start)
    (hwork : ∀ i : Fin k, (work (satVerifierWorkIdx i)).read ≠ Γ.start)
    (choices : Fin (TM.pairBuildTime x.length y.length + 1) → Bool) :
    ∃ t, ∃ ht : t ≤ TM.pairBuildTime x.length y.length,
      let pairNTM := (TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM
      let pairChoices : Fin t → Bool := fun i => choices ⟨i.val, by omega⟩
      let c0 : Cfg (k + 3) TM.PairBuildPhase :=
        { state := TM.PairBuildPhase.init,
          input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
          work := work,
          output := out }
      let cT := pairNTM.trace t pairChoices c0
      let cVerify : Cfg (k + 3) M.Q :=
        { state := verifierStartedState M,
          input := satBoundaryInput cT.input,
          work := satBoundaryWork cT.work,
          output := satBoundaryOutput cT.output }
      (satGuessVerifyNTM M).trace (t + 1)
        (fun i => choices (Fin.castLE (by omega : t + 1 ≤
          TM.pairBuildTime x.length y.length + 1) i))
        (satPairWrap M c0) =
        satVerifyWrap M cVerify ∧
      cVerify.work (satPairIdx k) =
        (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right ∧
      cVerify.output = out ∧
      (∀ i : Fin k, cVerify.work (satVerifierWorkIdx i) =
        work (satVerifierWorkIdx i)) := by
  obtain ⟨t, ht, hpairExit⟩ :=
    satGuessVerify_pair_exits M x y work out hpre choices
  refine ⟨t, ht, ?_⟩
  let P := TM.pairBuildTime x.length y.length
  let pairNTM := (TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM
  let pairChoices : Fin t → Bool := fun i => choices ⟨i.val, by omega⟩
  let c0 : Cfg (k + 3) TM.PairBuildPhase :=
    { state := TM.PairBuildPhase.init,
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
      work := work,
      output := out }
  let cT := pairNTM.trace t pairChoices c0
  let cVerify : Cfg (k + 3) M.Q :=
    { state := verifierStartedState M,
      input := satBoundaryInput cT.input,
      work := satBoundaryWork cT.work,
      output := satBoundaryOutput cT.output }
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [P, pairNTM, pairChoices, c0, cT, cVerify] using hpairExit.1
  · simpa [P, pairNTM, pairChoices, c0, cT, cVerify] using hpairExit.2
  · have hout_cT : cT.output = out := by
      simpa [P, pairNTM, pairChoices, c0, cT] using
        TM.pairBuildTM_trace_preserves_output
          (satWitnessIdx k) (satPairIdx k) t pairChoices c0
          (by simpa [c0] using hout)
    change satBoundaryOutput cT.output = out
    rw [hout_cT]
    exact satBoundaryOutput_stable_of_read_ne_start out hout
  · intro i
    have hwork_cT :
        cT.work (satVerifierWorkIdx i) = work (satVerifierWorkIdx i) := by
      simpa [P, pairNTM, pairChoices, c0, cT] using
        TM.pairBuildTM_trace_preserves_other_work
          (satWitnessIdx k) (satPairIdx k) (satVerifierWorkIdx i) t
          pairChoices c0
          (satVerifierWorkIdx_ne_witnessIdx i)
          (satVerifierWorkIdx_ne_pairIdx i)
          (by simpa [c0] using hwork i)
    have hread_cT : (cT.work (satVerifierWorkIdx i)).read ≠ Γ.start := by
      rw [hwork_cT]
      exact hwork i
    change satBoundaryWork cT.work (satVerifierWorkIdx i) =
      work (satVerifierWorkIdx i)
    rw [satBoundaryWork_stable_of_read_ne_start cT.work (satVerifierWorkIdx i) hread_cT]
    exact hwork_cT

/-- One composed-machine step on a non-halted verifier configuration simulates
    one step of the verifier-phase machine. -/
theorem satGuessVerify_verify_trace_one (M : TM k)
    (choice : Bool) (c : Cfg (k + 3) M.Q)
    (hstate : c.state ≠ M.qhalt) :
    (satGuessVerifyNTM M).trace 1 (fun _ => choice) (satVerifyWrap M c) =
      satVerifyWrap M
        (((satVerifyPhaseTM M).toNTM).trace 1 (fun _ => choice) c) := by
  cases c with
  | mk state input work output =>
    have hstate' : state ≠ M.qhalt := by
      simpa using hstate
    simp [satVerifyWrap, satGuessVerifyNTM, satGuessVerifyDelta,
      satVerifyTransition, satVerifyPhaseTM, NTM.trace, TM.toNTM, hstate']

/-- Multi-step verifier-phase simulation up to, but not across, `M`'s halt
    state. -/
theorem satGuessVerify_verify_trace_prefix (M : TM k) :
    ∀ (T : ℕ) (choices : Fin T → Bool)
      (c : Cfg (k + 3) M.Q),
      (∀ t (ht : t < T),
        (((satVerifyPhaseTM M).toNTM).trace t
          (fun i => choices ⟨i.val, Nat.lt_trans i.isLt ht⟩) c).state ≠
            M.qhalt) →
      (satGuessVerifyNTM M).trace T choices (satVerifyWrap M c) =
        satVerifyWrap M
          (((satVerifyPhaseTM M).toNTM).trace T choices c) := by
  intro T
  induction T with
  | zero =>
      intro choices c _hnot
      rfl
  | succ T ih =>
      intro choices c hnot
      let verifyNTM := (satVerifyPhaseTM M).toNTM
      let choicesTail : Fin T → Bool := fun i => choices ⟨i.val + 1, by omega⟩
      let c1 : Cfg (k + 3) M.Q :=
        verifyNTM.trace 1 (fun _ => choices ⟨0, by omega⟩) c
      have hstate : c.state ≠ M.qhalt := by
        have h0 := hnot 0 (by omega)
        exact h0
      rw [NTM.trace_succ (satGuessVerifyNTM M) T choices (satVerifyWrap M c)]
      rw [satGuessVerify_verify_trace_one M (choices ⟨0, by omega⟩) c hstate]
      have htail : ∀ t (ht : t < T),
          (verifyNTM.trace t
            (fun i => choicesTail ⟨i.val, Nat.lt_trans i.isLt ht⟩) c1).state ≠
              M.qhalt := by
        intro t ht
        have hfull := hnot (t + 1) (by omega)
        let choicesPrefix : Fin (t + 1) → Bool := fun i => choices ⟨i.val, by omega⟩
        have hsplit :=
          NTM.trace_succ verifyNTM t choicesPrefix c
        change (verifyNTM.trace t
          (fun i => choicesTail ⟨i.val, Nat.lt_trans i.isLt ht⟩) c1).state ≠
            M.qhalt
        rw [← hsplit]
        exact hfull
      rw [ih choicesTail c1 htail]
      have hsplitFull :=
        NTM.trace_succ verifyNTM T choices c
      rw [hsplitFull]

/-- If the verifier phase has halted by time `T`, then the composed SAT
    machine, started in verifier phase, is halted by time `T` as well. -/
theorem satGuessVerify_verify_halts_of_phase_halts (M : TM k)
    (T : ℕ) (choices : Fin T → Bool) (c : Cfg (k + 3) M.Q)
    (hhalt : (satVerifyPhaseTM M).halted
      (((satVerifyPhaseTM M).toNTM).trace T choices c)) :
    (satGuessVerifyNTM M).halted
      ((satGuessVerifyNTM M).trace T choices (satVerifyWrap M c)) := by
  let verifyNTM := (satVerifyPhaseTM M).toNTM
  obtain ⟨t, ht, hhalt_t, hfirst⟩ :=
    NTM.exists_first_halt_time_of_trace_halted verifyNTM T choices c hhalt
  let choicesT : Fin t → Bool := fun i => choices (Fin.castLE ht i)
  have hprefixHyp : ∀ s (hs : s < t),
      (verifyNTM.trace s
        (fun i => choicesT ⟨i.val, Nat.lt_trans i.isLt hs⟩) c).state ≠
          M.qhalt := by
    intro s hs
    have hfirst_s := hfirst s hs
    simp [verifyNTM, choicesT]
    exact hfirst_s
  have hprefix := satGuessVerify_verify_trace_prefix M t choicesT c hprefixHyp
  have hhalt_composed_t :
      (satGuessVerifyNTM M).halted
        ((satGuessVerifyNTM M).trace t choicesT (satVerifyWrap M c)) := by
    rw [hprefix]
    exact (satGuessVerify_verify_halted_iff M _).2 hhalt_t
  have hmono := (satGuessVerifyNTM M).trace_mono ht
    (choices := choicesT) (choices' := choices) (c := satVerifyWrap M c)
    (by intro i; rfl) hhalt_composed_t
  rw [hmono]
  exact hhalt_composed_t

/-- If the projected verifier computation halts, then the full SAT machine
    started in verifier phase halts under the same time bound. -/
theorem satGuessVerify_verify_halts_of_inner_trace_halts (M : TM k)
    (T : ℕ) (choices : Fin T → Bool) (c : Cfg (k + 3) M.Q)
    (hpair : ∀ t (ht : t < T),
      let ct := ((satVerifyPhaseTM M).toNTM).trace t
        (fun i => choices ⟨i.val, Nat.lt_trans i.isLt ht⟩) c
      (ct.work (satPairIdx k)).head = 0 ∨
        (ct.work (satPairIdx k)).read ≠ Γ.start)
    (hinner : M.halted ((M.toNTM).trace T choices (satVerifyInnerCfg M c))) :
    (satGuessVerifyNTM M).halted
      ((satGuessVerifyNTM M).trace T choices (satVerifyWrap M c)) := by
  have hphase :=
    satVerifyPhaseTM_halts_of_inner_trace_halts M T choices c hpair hinner
  exact satGuessVerify_verify_halts_of_phase_halts M T choices c hphase

/-- If the projected verifier computation halts and the SAT pair tape is clean,
    then the full SAT machine started in verifier phase halts under the same
    time bound. -/
theorem satGuessVerify_verify_halts_of_inner_trace_halts_clean (M : TM k)
    (T : ℕ) (choices : Fin T → Bool) (c : Cfg (k + 3) M.Q)
    (hclean : ∀ j, j ≥ 1 → (c.work (satPairIdx k)).cells j ≠ Γ.start)
    (hinner : M.halted ((M.toNTM).trace T choices (satVerifyInnerCfg M c))) :
    (satGuessVerifyNTM M).halted
      ((satGuessVerifyNTM M).trace T choices (satVerifyWrap M c)) := by
  exact satGuessVerify_verify_halts_of_inner_trace_halts M T choices c
    (satVerifyPhaseTM_pair_guard_of_clean M T choices c hclean) hinner

/-- If the projected verifier computation halts with accepting output and the
    SAT pair tape is clean, then the full SAT machine started in verifier phase
    also halts with accepting output. -/
theorem satGuessVerify_verify_outputs_of_inner_trace_output_clean (M : TM k)
    (T : ℕ) (choices : Fin T → Bool) (c : Cfg (k + 3) M.Q)
    (hclean : ∀ j, j ≥ 1 → (c.work (satPairIdx k)).cells j ≠ Γ.start)
    (g : Γ)
    (hinnerHalt : M.halted ((M.toNTM).trace T choices (satVerifyInnerCfg M c)))
    (hinnerOut :
      (((M.toNTM).trace T choices (satVerifyInnerCfg M c)).output.cells 1) = g) :
    let cFinal := (satGuessVerifyNTM M).trace T choices (satVerifyWrap M c)
    (satGuessVerifyNTM M).halted cFinal ∧ cFinal.output.cells 1 = g := by
  let verifyNTM := (satVerifyPhaseTM M).toNTM
  let phaseT := verifyNTM.trace T choices c
  have hguard :=
    satVerifyPhaseTM_pair_guard_of_clean M T choices c hclean
  have hproj :
      satVerifyInnerCfg M phaseT =
        (M.toNTM).trace T choices (satVerifyInnerCfg M c) := by
    simpa [verifyNTM, phaseT] using
      satVerifyPhaseTM_trace_project_prefix M T choices c hguard
  have hphaseHalt : (satVerifyPhaseTM M).halted phaseT := by
    erw [satVerifyPhaseTM_halted_iff, hproj]
    exact hinnerHalt
  have hphaseOut : phaseT.output.cells 1 = g := by
    have hprojOut :=
      congrArg (fun cfg : Cfg k M.Q => cfg.output.cells 1) hproj
    exact hprojOut.trans hinnerOut
  obtain ⟨t, ht, hhalt_t, hfirst⟩ :=
    NTM.exists_first_halt_time_of_trace_halted verifyNTM T choices c
      (by simp only [verifyNTM] ; exact hphaseHalt)
  let choicesT : Fin t → Bool := fun i => choices (Fin.castLE ht i)
  have hprefixHyp : ∀ s (hs : s < t),
      (verifyNTM.trace s
        (fun i => choicesT ⟨i.val, Nat.lt_trans i.isLt hs⟩) c).state ≠
          M.qhalt := by
    intro s hs
    have hfirst_s := hfirst s hs
    simp [verifyNTM, choicesT]
    exact hfirst_s
  have hprefix := satGuessVerify_verify_trace_prefix M t choicesT c hprefixHyp
  have hcomposed_t_halt :
      (satGuessVerifyNTM M).halted
        ((satGuessVerifyNTM M).trace t choicesT (satVerifyWrap M c)) := by
    rw [hprefix]
    exact (satGuessVerify_verify_halted_iff M _).2 hhalt_t
  have hmonoComposed := (satGuessVerifyNTM M).trace_mono ht
    (choices := choicesT) (choices' := choices) (c := satVerifyWrap M c)
    (by intro i; rfl) hcomposed_t_halt
  have hmonoPhase := verifyNTM.trace_mono ht
    (choices := choicesT) (choices' := choices) (c := c)
    (by intro i; rfl) hhalt_t
  have hphaseOut_t : (verifyNTM.trace t choicesT c).output.cells 1 = g := by
    rw [← hmonoPhase]
    exact hphaseOut
  refine ⟨?_, ?_⟩
  · rw [hmonoComposed]
    exact hcomposed_t_halt
  · rw [hmonoComposed, hprefix]
    exact hphaseOut_t

/-- If the projected verifier computation halts with accepting output and the
    SAT pair tape is clean, then the full SAT machine started in verifier phase
    also halts with accepting output. -/
theorem satGuessVerify_verify_accepts_of_inner_trace_accepts_clean (M : TM k)
    (T : ℕ) (choices : Fin T → Bool) (c : Cfg (k + 3) M.Q)
    (hclean : ∀ j, j ≥ 1 → (c.work (satPairIdx k)).cells j ≠ Γ.start)
    (hinnerHalt : M.halted ((M.toNTM).trace T choices (satVerifyInnerCfg M c)))
    (hinnerOut :
      (((M.toNTM).trace T choices (satVerifyInnerCfg M c)).output.cells 1) =
        Γ.one) :
    let cFinal := (satGuessVerifyNTM M).trace T choices (satVerifyWrap M c)
    (satGuessVerifyNTM M).halted cFinal ∧ cFinal.output.cells 1 = Γ.one := by
  exact satGuessVerify_verify_outputs_of_inner_trace_output_clean M T choices c
    hclean Γ.one hinnerHalt hinnerOut

/-- If a composed SAT trace prefix has reached the verifier phase, then any
    halting projected verifier suffix gives a halting full composed trace. -/
theorem satGuessVerify_halts_after_verify_prefix (M : TM k)
    (T V : ℕ) (choices : Fin (T + V) → Bool)
    (c0 : Cfg (k + 3) (GuessVerifyPhase M.Q)) (c : Cfg (k + 3) M.Q)
    (hprefix :
      (satGuessVerifyNTM M).trace T
        (fun i => choices (Fin.castLE (Nat.le_add_right T V) i)) c0 =
          satVerifyWrap M c)
    (hclean : ∀ j, j ≥ 1 → (c.work (satPairIdx k)).cells j ≠ Γ.start)
    (hinner : M.halted
      ((M.toNTM).trace V (fun i => choices (Fin.natAdd T i))
        (satVerifyInnerCfg M c))) :
    (satGuessVerifyNTM M).halted
      ((satGuessVerifyNTM M).trace (T + V) choices c0) := by
  rw [NTM.trace_add (satGuessVerifyNTM M) T V choices c0]
  rw [hprefix]
  exact satGuessVerify_verify_halts_of_inner_trace_halts_clean M V
    (fun i => choices (Fin.natAdd T i)) c hclean hinner

/-- If a composed SAT trace prefix has reached the verifier phase, then any
    accepting projected verifier suffix gives an accepting full composed trace. -/
theorem satGuessVerify_accepts_after_verify_prefix (M : TM k)
    (T V : ℕ) (choices : Fin (T + V) → Bool)
    (c0 : Cfg (k + 3) (GuessVerifyPhase M.Q)) (c : Cfg (k + 3) M.Q)
    (hprefix :
      (satGuessVerifyNTM M).trace T
        (fun i => choices (Fin.castLE (Nat.le_add_right T V) i)) c0 =
          satVerifyWrap M c)
    (hclean : ∀ j, j ≥ 1 → (c.work (satPairIdx k)).cells j ≠ Γ.start)
    (hinnerHalt : M.halted
      ((M.toNTM).trace V (fun i => choices (Fin.natAdd T i))
        (satVerifyInnerCfg M c)))
    (hinnerOut :
      (((M.toNTM).trace V (fun i => choices (Fin.natAdd T i))
        (satVerifyInnerCfg M c)).output.cells 1) = Γ.one) :
    let cFinal := (satGuessVerifyNTM M).trace (T + V) choices c0
    (satGuessVerifyNTM M).halted cFinal ∧ cFinal.output.cells 1 = Γ.one := by
  rw [NTM.trace_add (satGuessVerifyNTM M) T V choices c0]
  rw [hprefix]
  exact satGuessVerify_verify_accepts_of_inner_trace_accepts_clean M V
    (fun i => choices (Fin.natAdd T i)) c hclean hinnerHalt hinnerOut

/-- If a composed SAT trace prefix has reached the verifier phase, then any
    projected verifier suffix preserves its final output cell through the
    composed machine. -/
theorem satGuessVerify_outputs_after_verify_prefix (M : TM k)
    (T V : ℕ) (choices : Fin (T + V) → Bool)
    (c0 : Cfg (k + 3) (GuessVerifyPhase M.Q)) (c : Cfg (k + 3) M.Q)
    (hprefix :
      (satGuessVerifyNTM M).trace T
        (fun i => choices (Fin.castLE (Nat.le_add_right T V) i)) c0 =
          satVerifyWrap M c)
    (hclean : ∀ j, j ≥ 1 → (c.work (satPairIdx k)).cells j ≠ Γ.start)
    (g : Γ)
    (hinnerHalt : M.halted
      ((M.toNTM).trace V (fun i => choices (Fin.natAdd T i))
        (satVerifyInnerCfg M c)))
    (hinnerOut :
      (((M.toNTM).trace V (fun i => choices (Fin.natAdd T i))
        (satVerifyInnerCfg M c)).output.cells 1) = g) :
    let cFinal := (satGuessVerifyNTM M).trace (T + V) choices c0
    (satGuessVerifyNTM M).halted cFinal ∧ cFinal.output.cells 1 = g := by
  rw [NTM.trace_add (satGuessVerifyNTM M) T V choices c0]
  rw [hprefix]
  exact satGuessVerify_verify_outputs_of_inner_trace_output_clean M V
    (fun i => choices (Fin.natAdd T i)) c hclean g hinnerHalt hinnerOut

/-- Generic trace composition for the composed SAT machine: if a prefix reaches
    a configuration whose suffix trace halts, then the combined trace halts. -/
theorem satGuessVerify_halts_after_prefix (M : TM k)
    (T U : ℕ) (choices : Fin (T + U) → Bool)
    (c0 c1 : Cfg (k + 3) (GuessVerifyPhase M.Q))
    (hprefix :
      (satGuessVerifyNTM M).trace T
        (fun i => choices (Fin.castLE (Nat.le_add_right T U) i)) c0 = c1)
    (hsuffix :
      (satGuessVerifyNTM M).halted
        ((satGuessVerifyNTM M).trace U (fun i => choices (Fin.natAdd T i)) c1)) :
    (satGuessVerifyNTM M).halted
      ((satGuessVerifyNTM M).trace (T + U) choices c0) := by
  rw [NTM.trace_add (satGuessVerifyNTM M) T U choices c0]
  rw [hprefix]
  exact hsuffix

/-- Generic trace composition for the composed SAT machine: if a prefix reaches
    a configuration whose suffix trace accepts, then the combined trace
    accepts. -/
theorem satGuessVerify_accepts_after_prefix (M : TM k)
    (T U : ℕ) (choices : Fin (T + U) → Bool)
    (c0 c1 : Cfg (k + 3) (GuessVerifyPhase M.Q))
    (hprefix :
      (satGuessVerifyNTM M).trace T
        (fun i => choices (Fin.castLE (Nat.le_add_right T U) i)) c0 = c1)
    (hsuffix :
      let cFinal :=
        (satGuessVerifyNTM M).trace U (fun i => choices (Fin.natAdd T i)) c1
      (satGuessVerifyNTM M).halted cFinal ∧ cFinal.output.cells 1 = Γ.one) :
    let cFinal := (satGuessVerifyNTM M).trace (T + U) choices c0
    (satGuessVerifyNTM M).halted cFinal ∧ cFinal.output.cells 1 = Γ.one := by
  rw [NTM.trace_add (satGuessVerifyNTM M) T U choices c0]
  rw [hprefix]
  exact hsuffix

/-- Guess-phase exit followed by any halting pair/verifier suffix gives a
    halting combined run. -/
theorem satGuessVerify_guess_exit_then_suffix_halts (M : TM k)
    (T U : ℕ) (choices : Fin (T + U) → Bool)
    (c0 : Cfg (k + 3) NTM.GuessBoundedPhase)
    (cPair : Cfg (k + 3) TM.PairBuildPhase)
    (hprefix :
      (satGuessVerifyNTM M).trace T
        (fun i => choices (Fin.castLE (Nat.le_add_right T U) i))
        (satGuessWrap M c0) =
          satPairWrap M cPair)
    (hsuffix :
      (satGuessVerifyNTM M).halted
        ((satGuessVerifyNTM M).trace U (fun i => choices (Fin.natAdd T i))
          (satPairWrap M cPair))) :
    (satGuessVerifyNTM M).halted
      ((satGuessVerifyNTM M).trace (T + U) choices (satGuessWrap M c0)) := by
  exact satGuessVerify_halts_after_prefix M T U choices (satGuessWrap M c0)
    (satPairWrap M cPair) hprefix hsuffix

/-- Input-rewind exit followed by any halting guess/pair/verifier suffix gives
    a halting combined run. -/
theorem satGuessVerify_rewindInput_exit_then_suffix_halts (M : TM k)
    (T U : ℕ) (choices : Fin (T + U) → Bool)
    (c0 : Cfg (k + 3) TM.RewindPhase)
    (cGuess : Cfg (k + 3) NTM.GuessBoundedPhase)
    (hprefix :
      (satGuessVerifyNTM M).trace T
        (fun i => choices (Fin.castLE (Nat.le_add_right T U) i))
        (satRewindInputWrap M c0) =
          satGuessWrap M cGuess)
    (hsuffix :
      (satGuessVerifyNTM M).halted
        ((satGuessVerifyNTM M).trace U (fun i => choices (Fin.natAdd T i))
          (satGuessWrap M cGuess))) :
    (satGuessVerifyNTM M).halted
      ((satGuessVerifyNTM M).trace (T + U) choices (satRewindInputWrap M c0)) := by
  exact satGuessVerify_halts_after_prefix M T U choices (satRewindInputWrap M c0)
    (satGuessWrap M cGuess) hprefix hsuffix

/-- Counter-setup exit followed by any halting rewind/guess/pair/verifier suffix
    gives a halting combined run. -/
theorem satGuessVerify_counter_exit_then_suffix_halts (M : TM k)
    (T U : ℕ) (choices : Fin (T + U) → Bool)
    (c0 : Cfg (k + 3) TM.LinearCounterPhase)
    (cRewind : Cfg (k + 3) TM.RewindPhase)
    (hprefix :
      (satGuessVerifyNTM M).trace T
        (fun i => choices (Fin.castLE (Nat.le_add_right T U) i))
        (satCounterWrap M c0) =
          satRewindInputWrap M cRewind)
    (hsuffix :
      (satGuessVerifyNTM M).halted
        ((satGuessVerifyNTM M).trace U (fun i => choices (Fin.natAdd T i))
          (satRewindInputWrap M cRewind))) :
    (satGuessVerifyNTM M).halted
      ((satGuessVerifyNTM M).trace (T + U) choices (satCounterWrap M c0)) := by
  exact satGuessVerify_halts_after_prefix M T U choices (satCounterWrap M c0)
    (satRewindInputWrap M cRewind) hprefix hsuffix

/-- Pair-builder-to-verifier composition: once a SAT trace prefix has exited the
    pair phase with the exact encoded `(x, y)` pair tape, a halting projected
    verifier suffix makes the full composed machine halt. -/
theorem satGuessVerify_pair_exit_then_verify_halts (M : TM k)
    (x y : List Bool) (T V : ℕ) (choices : Fin (T + V) → Bool)
    (c0 : Cfg (k + 3) TM.PairBuildPhase) (c : Cfg (k + 3) M.Q)
    (hprefix :
      (satGuessVerifyNTM M).trace T
        (fun i => choices (Fin.castLE (Nat.le_add_right T V) i))
        (satPairWrap M c0) =
          satVerifyWrap M c)
    (hpair : c.work (satPairIdx k) =
      (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right)
    (hinner : M.halted
      ((M.toNTM).trace V (fun i => choices (Fin.natAdd T i))
        (satVerifyInnerCfg M c))) :
    (satGuessVerifyNTM M).halted
      ((satGuessVerifyNTM M).trace (T + V) choices (satPairWrap M c0)) := by
  exact satGuessVerify_halts_after_verify_prefix M T V choices (satPairWrap M c0) c
    hprefix
    (satPair_cells_ne_start_of_initTape_ofBool_move_right M (pair x y) c hpair)
    hinner

/-- Pair-builder-to-verifier composition with accepting output. -/
theorem satGuessVerify_pair_exit_then_verify_accepts (M : TM k)
    (x y : List Bool) (T V : ℕ) (choices : Fin (T + V) → Bool)
    (c0 : Cfg (k + 3) TM.PairBuildPhase) (c : Cfg (k + 3) M.Q)
    (hprefix :
      (satGuessVerifyNTM M).trace T
        (fun i => choices (Fin.castLE (Nat.le_add_right T V) i))
        (satPairWrap M c0) =
          satVerifyWrap M c)
    (hpair : c.work (satPairIdx k) =
      (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right)
    (hinnerHalt : M.halted
      ((M.toNTM).trace V (fun i => choices (Fin.natAdd T i))
        (satVerifyInnerCfg M c)))
    (hinnerOut :
      (((M.toNTM).trace V (fun i => choices (Fin.natAdd T i))
        (satVerifyInnerCfg M c)).output.cells 1) = Γ.one) :
    let cFinal :=
      (satGuessVerifyNTM M).trace (T + V) choices (satPairWrap M c0)
    (satGuessVerifyNTM M).halted cFinal ∧ cFinal.output.cells 1 = Γ.one := by
  exact satGuessVerify_accepts_after_verify_prefix M T V choices (satPairWrap M c0) c
    hprefix
    (satPair_cells_ne_start_of_initTape_ofBool_move_right M (pair x y) c hpair)
    hinnerHalt hinnerOut

/-- Pair-builder-to-verifier composition preserving the projected verifier's
    final output cell. -/
theorem satGuessVerify_pair_exit_then_verify_outputs (M : TM k)
    (x y : List Bool) (T V : ℕ) (choices : Fin (T + V) → Bool)
    (c0 : Cfg (k + 3) TM.PairBuildPhase) (c : Cfg (k + 3) M.Q)
    (hprefix :
      (satGuessVerifyNTM M).trace T
        (fun i => choices (Fin.castLE (Nat.le_add_right T V) i))
        (satPairWrap M c0) =
          satVerifyWrap M c)
    (hpair : c.work (satPairIdx k) =
      (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right)
    (g : Γ)
    (hinnerHalt : M.halted
      ((M.toNTM).trace V (fun i => choices (Fin.natAdd T i))
        (satVerifyInnerCfg M c)))
    (hinnerOut :
      (((M.toNTM).trace V (fun i => choices (Fin.natAdd T i))
        (satVerifyInnerCfg M c)).output.cells 1) = g) :
    let cFinal :=
      (satGuessVerifyNTM M).trace (T + V) choices (satPairWrap M c0)
    (satGuessVerifyNTM M).halted cFinal ∧ cFinal.output.cells 1 = g := by
  exact satGuessVerify_outputs_after_verify_prefix M T V choices (satPairWrap M c0) c
    hprefix
    (satPair_cells_ne_start_of_initTape_ofBool_move_right M (pair x y) c hpair)
    g hinnerHalt hinnerOut

/-- Bounded pair-building followed by a halting verifier suffix gives a bounded
    halting run of the composed machine. The existential `t` is the first
    pair-builder halt time supplied by `satGuessVerify_pair_exits`. -/
theorem satGuessVerify_pair_exits_then_verify_halts (M : TM k)
    (x y : List Bool) (work : Fin (k + 3) → Tape) (out : Tape)
    (hpre :
      work (satWitnessIdx k) = (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
      work (satPairIdx k) = (Tape.init []).move Dir3.right)
    (V : ℕ)
    (choices : Fin (TM.pairBuildTime x.length y.length + 1 + V) → Bool)
    (hinner :
      ∀ t (ht : t ≤ TM.pairBuildTime x.length y.length),
        let pairNTM := (TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM
        let runChoices : Fin (t + 1 + V) → Bool :=
          fun i => choices (Fin.castLE (by omega :
            t + 1 + V ≤ TM.pairBuildTime x.length y.length + 1 + V) i)
        let pairChoices : Fin t → Bool :=
          fun i => runChoices ⟨i.val, by omega⟩
        let c0 : Cfg (k + 3) TM.PairBuildPhase :=
          { state := TM.PairBuildPhase.init,
            input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
            work := work,
            output := out }
        let cT := pairNTM.trace t pairChoices c0
        let cVerify : Cfg (k + 3) M.Q :=
          { state := verifierStartedState M,
            input := satBoundaryInput cT.input,
            work := satBoundaryWork cT.work,
            output := satBoundaryOutput cT.output }
        M.halted ((M.toNTM).trace V
          (fun i => runChoices (Fin.natAdd (t + 1) i))
          (satVerifyInnerCfg M cVerify))) :
    ∃ t, ∃ ht : t ≤ TM.pairBuildTime x.length y.length,
      let runChoices : Fin (t + 1 + V) → Bool :=
        fun i => choices (Fin.castLE (by omega :
          t + 1 + V ≤ TM.pairBuildTime x.length y.length + 1 + V) i)
      let c0 : Cfg (k + 3) TM.PairBuildPhase :=
        { state := TM.PairBuildPhase.init,
          input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
          work := work,
          output := out }
      (satGuessVerifyNTM M).halted
        ((satGuessVerifyNTM M).trace (t + 1 + V) runChoices
          (satPairWrap M c0)) := by
  let P := TM.pairBuildTime x.length y.length
  let choicesPair : Fin (P + 1) → Bool :=
    fun i => choices (Fin.castLE (by omega : P + 1 ≤ P + 1 + V) i)
  obtain ⟨t, ht, hpairExit⟩ :=
    satGuessVerify_pair_exits M x y work out hpre choicesPair
  refine ⟨t, by simpa [P] using ht, ?_⟩
  let runChoices : Fin (t + 1 + V) → Bool :=
    fun i => choices (Fin.castLE (by omega : t + 1 + V ≤ P + 1 + V) i)
  let pairNTM := (TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM
  let pairChoices : Fin t → Bool := fun i => runChoices ⟨i.val, by omega⟩
  let c0 : Cfg (k + 3) TM.PairBuildPhase :=
    { state := TM.PairBuildPhase.init,
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
      work := work,
      output := out }
  let cT := pairNTM.trace t pairChoices c0
  let cVerify : Cfg (k + 3) M.Q :=
    { state := verifierStartedState M,
      input := satBoundaryInput cT.input,
      work := satBoundaryWork cT.work,
      output := satBoundaryOutput cT.output }
  have hprefixChoices :
      (fun i : Fin (t + 1) =>
        runChoices (Fin.castLE (Nat.le_add_right (t + 1) V) i)) =
      (fun i : Fin (t + 1) =>
        choicesPair (Fin.castLE (by omega : t + 1 ≤ P + 1) i)) := by
    funext i
    apply congrArg choices
    exact Fin.ext rfl
  have hprefix :
      (satGuessVerifyNTM M).trace (t + 1)
        (fun i => runChoices (Fin.castLE (Nat.le_add_right (t + 1) V) i))
        (satPairWrap M c0) = satVerifyWrap M cVerify := by
    rw [hprefixChoices]
    simp [P, pairNTM, pairChoices, c0, cT, cVerify, choicesPair]
    exact hpairExit.1
  have hpairExact : cVerify.work (satPairIdx k) =
      (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right := by
    simpa [P, pairNTM, pairChoices, c0, cT, cVerify, choicesPair, runChoices]
      using hpairExit.2
  have hinner_t :
      M.halted ((M.toNTM).trace V
        (fun i => runChoices (Fin.natAdd (t + 1) i))
        (satVerifyInnerCfg M cVerify)) := by
    simpa [P, pairNTM, pairChoices, c0, cT, cVerify, runChoices] using
      hinner t (by simpa [P] using ht)
  exact satGuessVerify_pair_exit_then_verify_halts M x y (t + 1) V runChoices
    c0 cVerify hprefix hpairExact hinner_t

/-- Pair-start completeness with a real deciding verifier. If the pair phase
    starts from exact input/witness/pair tapes and blank verifier frame tapes,
    then pair construction followed by verifier simulation halts. -/
theorem satGuessVerify_pair_start_halts_of_decidesInTime (M : TM k)
    {L : Language} {f : ℕ → ℕ} (hM : M.DecidesInTime L f)
    (x y : List Bool) (work : Fin (k + 3) → Tape) (out : Tape)
    (hpre :
      work (satWitnessIdx k) = (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
      work (satPairIdx k) = (Tape.init []).move Dir3.right)
    (hout : out = (Tape.init []).move Dir3.right)
    (hwork : ∀ i : Fin k, work (satVerifierWorkIdx i) =
      (Tape.init []).move Dir3.right) :
    ∃ V, V + 1 ≤ f (pair x y).length ∧
      ∃ t, ∃ _ht : t ≤ TM.pairBuildTime x.length y.length,
        ∃ choices : Fin (t + 1 + V) → Bool,
          let c0 : Cfg (k + 3) TM.PairBuildPhase :=
            { state := TM.PairBuildPhase.init,
              input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
              work := work,
              output := out }
          (satGuessVerifyNTM M).halted
            ((satGuessVerifyNTM M).trace (t + 1 + V) choices
              (satPairWrap M c0)) := by
  obtain ⟨V, hVbound, hVhalt⟩ :=
    verifier_started_trace_halts_of_decidesInTime M hM (pair x y)
  let P := TM.pairBuildTime x.length y.length
  let pairVerifyChoices : Fin (P + 1 + V) → Bool := fun _ => false
  let pairExitChoices : Fin (P + 1) → Bool :=
    fun i => pairVerifyChoices (Fin.castLE (by omega : P + 1 ≤ P + 1 + V) i)
  have houtRead : out.read ≠ Γ.start := by
    rw [hout]
    simp [Tape.read, Tape.move, Tape.init]
  have hworkRead : ∀ i : Fin k, (work (satVerifierWorkIdx i)).read ≠ Γ.start := by
    intro i
    rw [hwork i]
    simp [Tape.read, Tape.move, Tape.init]
  obtain ⟨t, ht, hpairExit⟩ :=
    satGuessVerify_pair_exits_with_verifier_frames M x y work out hpre
      houtRead hworkRead pairExitChoices
  let pairNTM := (TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM
  let pairChoices : Fin t → Bool := fun i => pairExitChoices ⟨i.val, by omega⟩
  let c0 : Cfg (k + 3) TM.PairBuildPhase :=
    { state := TM.PairBuildPhase.init,
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
      work := work,
      output := out }
  let cT := pairNTM.trace t pairChoices c0
  let cVerify : Cfg (k + 3) M.Q :=
    { state := verifierStartedState M,
      input := satBoundaryInput cT.input,
      work := satBoundaryWork cT.work,
      output := satBoundaryOutput cT.output }
  let runChoices : Fin (t + 1 + V) → Bool :=
    fun i => pairVerifyChoices (Fin.castLE (by omega : t + 1 + V ≤ P + 1 + V) i)
  have hprefixChoices :
      (fun i : Fin (t + 1) =>
        runChoices (Fin.castLE (Nat.le_add_right (t + 1) V) i)) =
      (fun i : Fin (t + 1) =>
        pairExitChoices (Fin.castLE (by omega : t + 1 ≤ P + 1) i)) := by
    funext i
    simp [runChoices, pairExitChoices, Fin.castLE]
  have hprefix :
      (satGuessVerifyNTM M).trace (t + 1)
        (fun i => runChoices (Fin.castLE (Nat.le_add_right (t + 1) V) i))
        (satPairWrap M c0) = satVerifyWrap M cVerify := by
    rw [hprefixChoices]
    simpa [P, pairNTM, pairChoices, c0, cT, cVerify, pairExitChoices] using
      hpairExit.1
  have hpairExact : cVerify.work (satPairIdx k) =
      (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right := by
    simpa [P, pairNTM, pairChoices, c0, cT, cVerify, pairExitChoices] using
      hpairExit.2.1
  have houtputExact : cVerify.output = (Tape.init []).move Dir3.right := by
    rw [hpairExit.2.2.1, hout]
  have hworkExact : ∀ i : Fin k, cVerify.work (satVerifierWorkIdx i) =
      (Tape.init []).move Dir3.right := by
    intro i
    rw [hpairExit.2.2.2 i, hwork i]
  let hne := TM.qstart_ne_qhalt_of_decidesInTime M hM
  have hinnerEq :
      satVerifyInnerCfg M cVerify = TM.startedCfg M (pair x y) hne :=
    satVerifyInnerCfg_eq_startedCfg M (pair x y) hne cVerify rfl
      hpairExact houtputExact hworkExact
  have hinner :
      M.halted ((M.toNTM).trace V
        (fun i => runChoices (Fin.natAdd (t + 1) i))
        (satVerifyInnerCfg M cVerify)) := by
    rw [hinnerEq]
    exact hVhalt (fun i => runChoices (Fin.natAdd (t + 1) i))
  have hsuffix :
      (satGuessVerifyNTM M).halted
        ((satGuessVerifyNTM M).trace (t + 1 + V) runChoices
          (satPairWrap M c0)) :=
    satGuessVerify_pair_exit_then_verify_halts M x y (t + 1) V runChoices
      c0 cVerify hprefix hpairExact hinner
  refine ⟨V, hVbound, t, by simpa [P] using ht, runChoices, ?_⟩
  simpa [c0] using hsuffix

/-- Pair-start all-path halting under the uniform SAT witness bound. Once the
    witness tape contains any `y` with `|y| ≤ |x|+1`, every remaining choice
    sequence reaches a halt within the pair-builder worst-case plus verifier
    window budget. -/
theorem satGuessVerify_pair_start_halts_within_bound_of_decidesInTime (M : TM k)
    {L : Language} {f : ℕ → ℕ} (hM : M.DecidesInTime L f)
    (x y : List Bool) (work : Fin (k + 3) → Tape) (out : Tape)
    (hpre :
      work (satWitnessIdx k) = (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
      work (satPairIdx k) = (Tape.init []).move Dir3.right)
    (hout : out = (Tape.init []).move Dir3.right)
    (hwork : ∀ i : Fin k, work (satVerifierWorkIdx i) =
      (Tape.init []).move Dir3.right)
    (hlen : y.length ≤ x.length + 1)
    (choices : Fin (TM.pairBuildTime x.length (x.length + 1) +
      satVerifierWindowTime f x.length) → Bool) :
    let c0 : Cfg (k + 3) TM.PairBuildPhase :=
      { state := TM.PairBuildPhase.init,
        input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
        work := work,
        output := out }
    (satGuessVerifyNTM M).halted
      ((satGuessVerifyNTM M).trace
        (TM.pairBuildTime x.length (x.length + 1) +
          satVerifierWindowTime f x.length)
        choices (satPairWrap M c0)) := by
  obtain ⟨V, hVbound, hVhalt⟩ :=
    verifier_started_trace_halts_of_decidesInTime M hM (pair x y)
  let P := TM.pairBuildTime x.length y.length
  let Pmax := TM.pairBuildTime x.length (x.length + 1)
  let W := satVerifierWindowTime f x.length
  have hPbound : P ≤ Pmax := by
    dsimp [P, Pmax, TM.pairBuildTime]
    omega
  have hWbound : f (pair x y).length ≤ W := by
    simpa [W] using satVerifierWindowTime_bounds_pair f x y hlen
  let pairPrefixChoices : Fin (P + 1) → Bool :=
    fun i => choices ⟨i.val, by omega⟩
  have houtRead : out.read ≠ Γ.start := by
    rw [hout]
    simp [Tape.read, Tape.move, Tape.init]
  have hworkRead : ∀ i : Fin k, (work (satVerifierWorkIdx i)).read ≠ Γ.start := by
    intro i
    rw [hwork i]
    simp [Tape.read, Tape.move, Tape.init]
  obtain ⟨t, ht, hpairExit⟩ :=
    satGuessVerify_pair_exits_with_verifier_frames M x y work out hpre
      houtRead hworkRead pairPrefixChoices
  let pairNTM := (TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM
  let pairChoices : Fin t → Bool := fun i => pairPrefixChoices ⟨i.val, by omega⟩
  let c0 : Cfg (k + 3) TM.PairBuildPhase :=
    { state := TM.PairBuildPhase.init,
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
      work := work,
      output := out }
  let cT := pairNTM.trace t pairChoices c0
  let cVerify : Cfg (k + 3) M.Q :=
    { state := verifierStartedState M,
      input := satBoundaryInput cT.input,
      work := satBoundaryWork cT.work,
      output := satBoundaryOutput cT.output }
  let shortChoices : Fin (t + 1 + V) → Bool := fun i =>
    choices ⟨i.val, by omega⟩
  have hprefixChoices :
      (fun i : Fin (t + 1) =>
        shortChoices (Fin.castLE (Nat.le_add_right (t + 1) V) i)) =
      (fun i : Fin (t + 1) =>
        pairPrefixChoices (Fin.castLE (by omega : t + 1 ≤ P + 1) i)) := by
    funext i
    simp [shortChoices, pairPrefixChoices, Fin.castLE]
  have hprefix :
      (satGuessVerifyNTM M).trace (t + 1)
        (fun i => shortChoices (Fin.castLE (Nat.le_add_right (t + 1) V) i))
        (satPairWrap M c0) = satVerifyWrap M cVerify := by
    rw [hprefixChoices]
    simpa [P, pairNTM, pairChoices, c0, cT, cVerify, pairPrefixChoices] using
      hpairExit.1
  have hpairExact : cVerify.work (satPairIdx k) =
      (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right := by
    simpa [P, pairNTM, pairChoices, c0, cT, cVerify, pairPrefixChoices] using
      hpairExit.2.1
  have houtputExact : cVerify.output = (Tape.init []).move Dir3.right := by
    rw [hpairExit.2.2.1, hout]
  have hworkExact : ∀ i : Fin k, cVerify.work (satVerifierWorkIdx i) =
      (Tape.init []).move Dir3.right := by
    intro i
    rw [hpairExit.2.2.2 i, hwork i]
  let hne := TM.qstart_ne_qhalt_of_decidesInTime M hM
  have hinnerEq :
      satVerifyInnerCfg M cVerify = TM.startedCfg M (pair x y) hne :=
    satVerifyInnerCfg_eq_startedCfg M (pair x y) hne cVerify rfl
      hpairExact houtputExact hworkExact
  have hinner :
      M.halted ((M.toNTM).trace V
        (fun i => shortChoices (Fin.natAdd (t + 1) i))
        (satVerifyInnerCfg M cVerify)) := by
    rw [hinnerEq]
    exact hVhalt (fun i => shortChoices (Fin.natAdd (t + 1) i))
  have hshort :
      (satGuessVerifyNTM M).halted
        ((satGuessVerifyNTM M).trace (t + 1 + V) shortChoices
          (satPairWrap M c0)) :=
    satGuessVerify_pair_exit_then_verify_halts M x y (t + 1) V shortChoices
      c0 cVerify hprefix hpairExact hinner
  have hshortBound :
      t + 1 + V ≤ Pmax + W := by
    omega
  have hmono := (satGuessVerifyNTM M).trace_mono hshortBound
    (choices := shortChoices) (choices' := choices) (c := satPairWrap M c0)
    (by intro i; rfl) hshort
  change (satGuessVerifyNTM M).halted
    ((satGuessVerifyNTM M).trace (Pmax + W) choices (satPairWrap M c0))
  rw [hmono]
  exact hshort

/-- Pair-start bounded deciding suffix under the uniform SAT witness bound.
    Once setup has produced a bounded witness `y`, every remaining choice
    sequence halts within the pair/verifier window and outputs the correct
    verifier bit for `pair x y`. -/
theorem satGuessVerify_pair_start_decides_within_bound_of_decidesInTime (M : TM k)
    {L : Language} {f : ℕ → ℕ} (hM : M.DecidesInTime L f)
    (x y : List Bool) (work : Fin (k + 3) → Tape) (out : Tape)
    (hpre :
      work (satWitnessIdx k) = (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
      work (satPairIdx k) = (Tape.init []).move Dir3.right)
    (hout : out = (Tape.init []).move Dir3.right)
    (hwork : ∀ i : Fin k, work (satVerifierWorkIdx i) =
      (Tape.init []).move Dir3.right)
    (hlen : y.length ≤ x.length + 1)
    (choices : Fin (TM.pairBuildTime x.length (x.length + 1) +
      satVerifierWindowTime f x.length) → Bool) :
    let c0 : Cfg (k + 3) TM.PairBuildPhase :=
      { state := TM.PairBuildPhase.init,
        input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
        work := work,
        output := out }
    let cFinal := (satGuessVerifyNTM M).trace
      (TM.pairBuildTime x.length (x.length + 1) + satVerifierWindowTime f x.length)
      choices (satPairWrap M c0)
    (satGuessVerifyNTM M).halted cFinal ∧
      ((pair x y ∈ L → cFinal.output.cells 1 = Γ.one) ∧
        (pair x y ∉ L → cFinal.output.cells 1 = Γ.zero)) := by
  obtain ⟨V, hVbound, hVdecides⟩ :=
    verifier_started_trace_decides_of_decidesInTime M hM (pair x y)
  let P := TM.pairBuildTime x.length y.length
  let Pmax := TM.pairBuildTime x.length (x.length + 1)
  let W := satVerifierWindowTime f x.length
  have hPbound : P ≤ Pmax := by
    dsimp [P, Pmax, TM.pairBuildTime]
    omega
  have hWbound : f (pair x y).length ≤ W := by
    simpa [W] using satVerifierWindowTime_bounds_pair f x y hlen
  let pairPrefixChoices : Fin (P + 1) → Bool :=
    fun i => choices ⟨i.val, by omega⟩
  have houtRead : out.read ≠ Γ.start := by
    rw [hout]
    simp [Tape.read, Tape.move, Tape.init]
  have hworkRead : ∀ i : Fin k, (work (satVerifierWorkIdx i)).read ≠ Γ.start := by
    intro i
    rw [hwork i]
    simp [Tape.read, Tape.move, Tape.init]
  obtain ⟨t, ht, hpairExit⟩ :=
    satGuessVerify_pair_exits_with_verifier_frames M x y work out hpre
      houtRead hworkRead pairPrefixChoices
  let pairNTM := (TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM
  let pairChoices : Fin t → Bool := fun i => pairPrefixChoices ⟨i.val, by omega⟩
  let c0 : Cfg (k + 3) TM.PairBuildPhase :=
    { state := TM.PairBuildPhase.init,
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
      work := work,
      output := out }
  let cT := pairNTM.trace t pairChoices c0
  let cVerify : Cfg (k + 3) M.Q :=
    { state := verifierStartedState M,
      input := satBoundaryInput cT.input,
      work := satBoundaryWork cT.work,
      output := satBoundaryOutput cT.output }
  let shortChoices : Fin (t + 1 + V) → Bool := fun i =>
    choices ⟨i.val, by omega⟩
  have hprefixChoices :
      (fun i : Fin (t + 1) =>
        shortChoices (Fin.castLE (Nat.le_add_right (t + 1) V) i)) =
      (fun i : Fin (t + 1) =>
        pairPrefixChoices (Fin.castLE (by omega : t + 1 ≤ P + 1) i)) := by
    funext i
    simp [shortChoices, pairPrefixChoices, Fin.castLE]
  have hprefix :
      (satGuessVerifyNTM M).trace (t + 1)
        (fun i => shortChoices (Fin.castLE (Nat.le_add_right (t + 1) V) i))
        (satPairWrap M c0) = satVerifyWrap M cVerify := by
    rw [hprefixChoices]
    simpa [P, pairNTM, pairChoices, c0, cT, cVerify, pairPrefixChoices] using
      hpairExit.1
  have hpairExact : cVerify.work (satPairIdx k) =
      (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right := by
    simpa [P, pairNTM, pairChoices, c0, cT, cVerify, pairPrefixChoices] using
      hpairExit.2.1
  have houtputExact : cVerify.output = (Tape.init []).move Dir3.right := by
    rw [hpairExit.2.2.1, hout]
  have hworkExact : ∀ i : Fin k, cVerify.work (satVerifierWorkIdx i) =
      (Tape.init []).move Dir3.right := by
    intro i
    rw [hpairExit.2.2.2 i, hwork i]
  let hne := TM.qstart_ne_qhalt_of_decidesInTime M hM
  have hinnerEq :
      satVerifyInnerCfg M cVerify = TM.startedCfg M (pair x y) hne :=
    satVerifyInnerCfg_eq_startedCfg M (pair x y) hne cVerify rfl
      hpairExact houtputExact hworkExact
  have hdecide := hVdecides (fun i => shortChoices (Fin.natAdd (t + 1) i))
  have hinnerHalt :
      M.halted ((M.toNTM).trace V
        (fun i => shortChoices (Fin.natAdd (t + 1) i))
        (satVerifyInnerCfg M cVerify)) := by
    rw [hinnerEq]
    exact hdecide.1
  have hshortOutput :
      let cFinal := (satGuessVerifyNTM M).trace (t + 1 + V) shortChoices
        (satPairWrap M c0)
      (satGuessVerifyNTM M).halted cFinal ∧
        cFinal.output.cells 1 =
          (((M.toNTM).trace V
            (fun i => shortChoices (Fin.natAdd (t + 1) i))
            (satVerifyInnerCfg M cVerify)).output.cells 1) :=
    satGuessVerify_pair_exit_then_verify_outputs M x y (t + 1) V shortChoices
      c0 cVerify hprefix hpairExact
      (((M.toNTM).trace V
        (fun i => shortChoices (Fin.natAdd (t + 1) i))
        (satVerifyInnerCfg M cVerify)).output.cells 1)
      hinnerHalt rfl
  have hshortBound : t + 1 + V ≤ Pmax + W := by
    omega
  have hmono := (satGuessVerifyNTM M).trace_mono hshortBound
    (choices := shortChoices) (choices' := choices) (c := satPairWrap M c0)
    (by intro i; rfl) hshortOutput.1
  let cFinal := (satGuessVerifyNTM M).trace (Pmax + W) choices (satPairWrap M c0)
  have hhaltFinal : (satGuessVerifyNTM M).halted cFinal := by
    change (satGuessVerifyNTM M).halted
      ((satGuessVerifyNTM M).trace (Pmax + W) choices (satPairWrap M c0))
    rw [hmono]
    exact hshortOutput.1
  have houtputFinal :
      cFinal.output.cells 1 =
        (((M.toNTM).trace V
          (fun i => shortChoices (Fin.natAdd (t + 1) i))
          (satVerifyInnerCfg M cVerify)).output.cells 1) := by
    change
      ((satGuessVerifyNTM M).trace (Pmax + W) choices (satPairWrap M c0)).output.cells 1 =
        (((M.toNTM).trace V
          (fun i => shortChoices (Fin.natAdd (t + 1) i))
          (satVerifyInnerCfg M cVerify)).output.cells 1)
    rw [hmono]
    exact hshortOutput.2
  refine ⟨hhaltFinal, ?_, ?_⟩
  · intro hmem
    rw [houtputFinal]
    rw [hinnerEq]
    exact hdecide.2.1 hmem
  · intro hnotmem
    rw [houtputFinal]
    rw [hinnerEq]
    exact hdecide.2.2 hnotmem

/-- Pair-start completeness with accepting output from a real deciding
    verifier. -/
theorem satGuessVerify_pair_start_accepts_of_decidesInTime (M : TM k)
    {L : Language} {f : ℕ → ℕ} (hM : M.DecidesInTime L f)
    (x y : List Bool) (work : Fin (k + 3) → Tape) (out : Tape)
    (hpre :
      work (satWitnessIdx k) = (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
      work (satPairIdx k) = (Tape.init []).move Dir3.right)
    (hout : out = (Tape.init []).move Dir3.right)
    (hwork : ∀ i : Fin k, work (satVerifierWorkIdx i) =
      (Tape.init []).move Dir3.right)
    (hmem : pair x y ∈ L) :
    ∃ V, V + 1 ≤ f (pair x y).length ∧
      ∃ t, ∃ _ht : t ≤ TM.pairBuildTime x.length y.length,
        ∃ choices : Fin (t + 1 + V) → Bool,
          let c0 : Cfg (k + 3) TM.PairBuildPhase :=
            { state := TM.PairBuildPhase.init,
              input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
              work := work,
              output := out }
          let cFinal := (satGuessVerifyNTM M).trace (t + 1 + V) choices
            (satPairWrap M c0)
          (satGuessVerifyNTM M).halted cFinal ∧ cFinal.output.cells 1 = Γ.one := by
  obtain ⟨V, hVbound, hVdecides⟩ :=
    verifier_started_trace_decides_of_decidesInTime M hM (pair x y)
  let P := TM.pairBuildTime x.length y.length
  let pairVerifyChoices : Fin (P + 1 + V) → Bool := fun _ => false
  let pairExitChoices : Fin (P + 1) → Bool :=
    fun i => pairVerifyChoices (Fin.castLE (by omega : P + 1 ≤ P + 1 + V) i)
  have houtRead : out.read ≠ Γ.start := by
    rw [hout]
    simp [Tape.read, Tape.move, Tape.init]
  have hworkRead : ∀ i : Fin k, (work (satVerifierWorkIdx i)).read ≠ Γ.start := by
    intro i
    rw [hwork i]
    simp [Tape.read, Tape.move, Tape.init]
  obtain ⟨t, ht, hpairExit⟩ :=
    satGuessVerify_pair_exits_with_verifier_frames M x y work out hpre
      houtRead hworkRead pairExitChoices
  let pairNTM := (TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM
  let pairChoices : Fin t → Bool := fun i => pairExitChoices ⟨i.val, by omega⟩
  let c0 : Cfg (k + 3) TM.PairBuildPhase :=
    { state := TM.PairBuildPhase.init,
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
      work := work,
      output := out }
  let cT := pairNTM.trace t pairChoices c0
  let cVerify : Cfg (k + 3) M.Q :=
    { state := verifierStartedState M,
      input := satBoundaryInput cT.input,
      work := satBoundaryWork cT.work,
      output := satBoundaryOutput cT.output }
  let runChoices : Fin (t + 1 + V) → Bool :=
    fun i => pairVerifyChoices (Fin.castLE (by omega : t + 1 + V ≤ P + 1 + V) i)
  have hprefixChoices :
      (fun i : Fin (t + 1) =>
        runChoices (Fin.castLE (Nat.le_add_right (t + 1) V) i)) =
      (fun i : Fin (t + 1) =>
        pairExitChoices (Fin.castLE (by omega : t + 1 ≤ P + 1) i)) := by
    funext i
    simp [runChoices, pairExitChoices, Fin.castLE]
  have hprefix :
      (satGuessVerifyNTM M).trace (t + 1)
        (fun i => runChoices (Fin.castLE (Nat.le_add_right (t + 1) V) i))
        (satPairWrap M c0) = satVerifyWrap M cVerify := by
    rw [hprefixChoices]
    simpa [P, pairNTM, pairChoices, c0, cT, cVerify, pairExitChoices] using
      hpairExit.1
  have hpairExact : cVerify.work (satPairIdx k) =
      (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right := by
    simpa [P, pairNTM, pairChoices, c0, cT, cVerify, pairExitChoices] using
      hpairExit.2.1
  have houtputExact : cVerify.output = (Tape.init []).move Dir3.right := by
    rw [hpairExit.2.2.1, hout]
  have hworkExact : ∀ i : Fin k, cVerify.work (satVerifierWorkIdx i) =
      (Tape.init []).move Dir3.right := by
    intro i
    rw [hpairExit.2.2.2 i, hwork i]
  let hne := TM.qstart_ne_qhalt_of_decidesInTime M hM
  have hinnerEq :
      satVerifyInnerCfg M cVerify = TM.startedCfg M (pair x y) hne :=
    satVerifyInnerCfg_eq_startedCfg M (pair x y) hne cVerify rfl
      hpairExact houtputExact hworkExact
  have hdecide := hVdecides (fun i => runChoices (Fin.natAdd (t + 1) i))
  have hinner :
      M.halted ((M.toNTM).trace V
        (fun i => runChoices (Fin.natAdd (t + 1) i))
        (satVerifyInnerCfg M cVerify)) := by
    rw [hinnerEq]
    exact hdecide.1
  have hinnerOut :
      (((M.toNTM).trace V
        (fun i => runChoices (Fin.natAdd (t + 1) i))
        (satVerifyInnerCfg M cVerify)).output.cells 1) = Γ.one := by
    rw [hinnerEq]
    exact hdecide.2.1 hmem
  have hsuffix :
      let cFinal := (satGuessVerifyNTM M).trace (t + 1 + V) runChoices
        (satPairWrap M c0)
      (satGuessVerifyNTM M).halted cFinal ∧ cFinal.output.cells 1 = Γ.one :=
    satGuessVerify_pair_exit_then_verify_accepts M x y (t + 1) V runChoices
      c0 cVerify hprefix hpairExact hinner hinnerOut
  refine ⟨V, hVbound, t, by simpa [P] using ht, runChoices, ?_⟩
  simpa [c0] using hsuffix

/-- End-to-end SAT-specialized completeness spine. If a target witness `y`
    fits the SAT linear witness bound and the projected verifier suffix halts
    from every possible pair-builder first halt for the exact `(x, y)` pair
    setup, then there is a full nondeterministic run of `satGuessVerifyNTM M`
    from the real initial configuration that halts. -/
theorem satGuessVerify_init_generates_witness_then_verify_halts (M : TM k)
    (x y : List Bool) (V : ℕ) (hlen : y.length ≤ x.length + 1)
    (hinner :
      ∀ (work : Fin (k + 3) → Tape) (out : Tape),
        work (satWitnessIdx k) =
          (Tape.init (y.map Γ.ofBool)).move Dir3.right →
        work (satPairIdx k) = (Tape.init []).move Dir3.right →
        ∀ t (_ht : t ≤ TM.pairBuildTime x.length y.length),
          let pairNTM := (TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM
          let c0 : Cfg (k + 3) TM.PairBuildPhase :=
            { state := TM.PairBuildPhase.init,
              input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
              work := work,
              output := out }
          let cT := pairNTM.trace t (fun _ : Fin t => false) c0
          let cVerify : Cfg (k + 3) M.Q :=
            { state := verifierStartedState M,
              input := satBoundaryInput cT.input,
              work := satBoundaryWork cT.work,
              output := satBoundaryOutput cT.output }
          M.halted ((M.toNTM).trace V (fun _ : Fin V => false)
            (satVerifyInnerCfg M cVerify))) :
    ∃ T, ∃ choices : Fin T → Bool,
      T ≤
        (TM.inputLengthPlusOneCounterTime x.length + 1 +
          (TM.inputLengthPlusOneCounterTime x.length + 1 + 2 + 1 +
            (NTM.guessBoundedTime (x.length + 1) 0 + 1))) +
          (TM.pairBuildTime x.length y.length + 1 + V) ∧
      (satGuessVerifyNTM M).halted
        ((satGuessVerifyNTM M).trace T choices ((satGuessVerifyNTM M).initCfg x)) := by
  obtain ⟨Tsetup, setupChoices, cPair, hTsetup, hsetupTrace, hpairState,
    hpairInput, hpairWitness, hpairBlank, _hpairOutput, _hpairVerifierWork⟩ :=
    satGuessVerify_setup_generates_pair M x y hlen
  let P := TM.pairBuildTime x.length y.length
  let pairVerifyChoices : Fin (P + 1 + V) → Bool := fun _ => false
  have hpairVerifyInner :
      ∀ t (ht : t ≤ P),
        let pairNTM := (TM.pairBuildTM (satWitnessIdx k) (satPairIdx k)).toNTM
        let runChoices : Fin (t + 1 + V) → Bool :=
          fun i => pairVerifyChoices (Fin.castLE (by omega : t + 1 + V ≤ P + 1 + V) i)
        let pairChoices : Fin t → Bool :=
          fun i => runChoices ⟨i.val, by omega⟩
        let c0 : Cfg (k + 3) TM.PairBuildPhase :=
          { state := TM.PairBuildPhase.init,
            input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
            work := cPair.work,
            output := cPair.output }
        let cT := pairNTM.trace t pairChoices c0
        let cVerify : Cfg (k + 3) M.Q :=
          { state := verifierStartedState M,
            input := satBoundaryInput cT.input,
            work := satBoundaryWork cT.work,
            output := satBoundaryOutput cT.output }
        M.halted ((M.toNTM).trace V
          (fun i => runChoices (Fin.natAdd (t + 1) i))
          (satVerifyInnerCfg M cVerify)) := by
    intro t ht
    simpa [P, pairVerifyChoices] using
      hinner cPair.work cPair.output hpairWitness hpairBlank t (by simpa [P] using ht)
  obtain ⟨tpair, htpair, hsuffix⟩ :=
    satGuessVerify_pair_exits_then_verify_halts M x y cPair.work cPair.output
      ⟨hpairWitness, hpairBlank⟩ V pairVerifyChoices hpairVerifyInner
  let suffixChoices : Fin (tpair + 1 + V) → Bool :=
    fun i => pairVerifyChoices (Fin.castLE (by omega : tpair + 1 + V ≤ P + 1 + V) i)
  let cPair0 : Cfg (k + 3) TM.PairBuildPhase :=
    { state := TM.PairBuildPhase.init,
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
      work := cPair.work,
      output := cPair.output }
  have hcPair : cPair = cPair0 := by
    cases cPair with
    | mk state input work output =>
        simp [cPair0] at hpairState hpairInput ⊢
        exact ⟨hpairState, hpairInput⟩
  have hsetupTrace0 :
      (satGuessVerifyNTM M).trace Tsetup setupChoices ((satGuessVerifyNTM M).initCfg x) =
        satPairWrap M cPair0 := by
    rw [← hcPair]
    exact hsetupTrace
  have hsuffix0 :
      (satGuessVerifyNTM M).halted
        ((satGuessVerifyNTM M).trace (tpair + 1 + V) suffixChoices
          (satPairWrap M cPair0)) := by
    simpa [P, suffixChoices, cPair0] using hsuffix
  let T := Tsetup + (tpair + 1 + V)
  let choices : Fin T → Bool := fun i =>
    if hi : i.val < Tsetup then setupChoices ⟨i.val, hi⟩
    else suffixChoices ⟨i.val - Tsetup, by omega⟩
  refine ⟨T, choices, ?_, ?_⟩
  · omega
  · have hprefixChoices :
        (fun i : Fin Tsetup =>
          choices (Fin.castLE (Nat.le_add_right Tsetup (tpair + 1 + V)) i)) =
          setupChoices := by
      funext i
      unfold choices
      rw [dite_eq_left (by simp [Fin.castLE])]
      exact congrArg setupChoices (Fin.ext (by simp [Fin.castLE]))
    have hsuffixChoices :
        (fun i : Fin (tpair + 1 + V) => choices (Fin.natAdd Tsetup i)) =
          suffixChoices := by
      funext i
      unfold choices
      rw [dite_eq_right (by simp [Fin.natAdd])]
    exact satGuessVerify_halts_after_prefix M Tsetup (tpair + 1 + V) choices
      ((satGuessVerifyNTM M).initCfg x) (satPairWrap M cPair0)
      (by rw [hprefixChoices]; exact hsetupTrace0)
      (by rw [hsuffixChoices]; exact hsuffix0)

/-- End-to-end completeness halting from a real deciding verifier. For any SAT
    witness candidate `y` within the linear bound, the SAT-specialized
    guess-and-verify machine has a nondeterministic run from its real initial
    configuration that reaches a halted state. -/
theorem satGuessVerify_init_generates_witness_halts_of_decidesInTime (M : TM k)
    {L : Language} {f : ℕ → ℕ} (hM : M.DecidesInTime L f)
    (x y : List Bool) (hlen : y.length ≤ x.length + 1) :
    ∃ T, ∃ choices : Fin T → Bool,
      T ≤
        (TM.inputLengthPlusOneCounterTime x.length + 1 +
          (TM.inputLengthPlusOneCounterTime x.length + 1 + 2 + 1 +
            (NTM.guessBoundedTime (x.length + 1) 0 + 1))) +
          (TM.pairBuildTime x.length y.length + f (pair x y).length) ∧
      (satGuessVerifyNTM M).halted
        ((satGuessVerifyNTM M).trace T choices ((satGuessVerifyNTM M).initCfg x)) := by
  obtain ⟨Tsetup, setupChoices, cPair, hTsetup, hsetupTrace, hpairState,
    hpairInput, hpairWitness, hpairBlank, hpairOutput, hpairVerifierWork⟩ :=
    satGuessVerify_setup_generates_pair M x y hlen
  let setupBound :=
    TM.inputLengthPlusOneCounterTime x.length + 1 +
      (TM.inputLengthPlusOneCounterTime x.length + 1 + 2 + 1 +
        (NTM.guessBoundedTime (x.length + 1) 0 + 1))
  obtain ⟨V, hVbound, tpair, htpair, suffixChoices, hsuffix⟩ :=
    satGuessVerify_pair_start_halts_of_decidesInTime M hM x y cPair.work cPair.output
      ⟨hpairWitness, hpairBlank⟩ hpairOutput hpairVerifierWork
  let cPair0 : Cfg (k + 3) TM.PairBuildPhase :=
    { state := TM.PairBuildPhase.init,
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
      work := cPair.work,
      output := cPair.output }
  have hcPair : cPair = cPair0 := by
    cases cPair with
    | mk state input work output =>
        simp [cPair0] at hpairState hpairInput ⊢
        exact ⟨hpairState, hpairInput⟩
  have hsetupTrace0 :
      (satGuessVerifyNTM M).trace Tsetup setupChoices ((satGuessVerifyNTM M).initCfg x) =
        satPairWrap M cPair0 := by
    rw [← hcPair]
    exact hsetupTrace
  have hsuffix0 :
      (satGuessVerifyNTM M).halted
        ((satGuessVerifyNTM M).trace (tpair + 1 + V) suffixChoices
          (satPairWrap M cPair0)) := by
    simpa [cPair0] using hsuffix
  let T := Tsetup + (tpair + 1 + V)
  let choices : Fin T → Bool := fun i =>
    if hi : i.val < Tsetup then setupChoices ⟨i.val, hi⟩
    else suffixChoices ⟨i.val - Tsetup, by omega⟩
  refine ⟨T, choices, ?_, ?_⟩
  · omega
  · have hprefixChoices :
        (fun i : Fin Tsetup =>
          choices (Fin.castLE (Nat.le_add_right Tsetup (tpair + 1 + V)) i)) =
          setupChoices := by
      funext i
      unfold choices
      rw [dite_eq_left (by simp [Fin.castLE])]
      exact congrArg setupChoices (Fin.ext (by simp [Fin.castLE]))
    have hsuffixChoices :
        (fun i : Fin (tpair + 1 + V) => choices (Fin.natAdd Tsetup i)) =
          suffixChoices := by
      funext i
      unfold choices
      rw [dite_eq_right (by simp [Fin.natAdd])]
      exact congrArg suffixChoices (Fin.ext (by simp [Fin.natAdd]))
    exact satGuessVerify_halts_after_prefix M Tsetup (tpair + 1 + V) choices
      ((satGuessVerifyNTM M).initCfg x) (satPairWrap M cPair0)
      (by rw [hprefixChoices]; exact hsetupTrace0)
      (by rw [hsuffixChoices]; exact hsuffix0)

/-- End-to-end accepting completeness from a real deciding verifier. For any
    SAT witness candidate `y` within the linear bound whose encoded pair is in
    the verifier language, the SAT-specialized guess-and-verify machine has a
    nondeterministic accepting run from its real initial configuration. -/
theorem satGuessVerify_init_generates_witness_accepts_of_decidesInTime (M : TM k)
    {L : Language} {f : ℕ → ℕ} (hM : M.DecidesInTime L f)
    (x y : List Bool) (hlen : y.length ≤ x.length + 1)
    (hmem : pair x y ∈ L) :
    ∃ T, ∃ choices : Fin T → Bool,
      T ≤
        (TM.inputLengthPlusOneCounterTime x.length + 1 +
          (TM.inputLengthPlusOneCounterTime x.length + 1 + 2 + 1 +
            (NTM.guessBoundedTime (x.length + 1) 0 + 1))) +
          (TM.pairBuildTime x.length y.length + f (pair x y).length) ∧
      let cFinal :=
        (satGuessVerifyNTM M).trace T choices ((satGuessVerifyNTM M).initCfg x)
      (satGuessVerifyNTM M).halted cFinal ∧ cFinal.output.cells 1 = Γ.one := by
  obtain ⟨Tsetup, setupChoices, cPair, hTsetup, hsetupTrace, hpairState,
    hpairInput, hpairWitness, hpairBlank, hpairOutput, hpairVerifierWork⟩ :=
    satGuessVerify_setup_generates_pair M x y hlen
  let setupBound :=
    TM.inputLengthPlusOneCounterTime x.length + 1 +
      (TM.inputLengthPlusOneCounterTime x.length + 1 + 2 + 1 +
        (NTM.guessBoundedTime (x.length + 1) 0 + 1))
  obtain ⟨V, hVbound, tpair, htpair, suffixChoices, hsuffix⟩ :=
    satGuessVerify_pair_start_accepts_of_decidesInTime M hM x y
      cPair.work cPair.output ⟨hpairWitness, hpairBlank⟩ hpairOutput
      hpairVerifierWork hmem
  let cPair0 : Cfg (k + 3) TM.PairBuildPhase :=
    { state := TM.PairBuildPhase.init,
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
      work := cPair.work,
      output := cPair.output }
  have hcPair : cPair = cPair0 := by
    cases cPair with
    | mk state input work output =>
        simp [cPair0] at hpairState hpairInput ⊢
        exact ⟨hpairState, hpairInput⟩
  have hsetupTrace0 :
      (satGuessVerifyNTM M).trace Tsetup setupChoices ((satGuessVerifyNTM M).initCfg x) =
        satPairWrap M cPair0 := by
    rw [← hcPair]
    exact hsetupTrace
  have hsuffix0 :
      let cFinal := (satGuessVerifyNTM M).trace (tpair + 1 + V) suffixChoices
        (satPairWrap M cPair0)
      (satGuessVerifyNTM M).halted cFinal ∧ cFinal.output.cells 1 = Γ.one := by
    simpa [cPair0] using hsuffix
  let T := Tsetup + (tpair + 1 + V)
  let choices : Fin T → Bool := fun i =>
    if hi : i.val < Tsetup then setupChoices ⟨i.val, hi⟩
    else suffixChoices ⟨i.val - Tsetup, by omega⟩
  refine ⟨T, choices, ?_, ?_⟩
  · omega
  · have hprefixChoices :
        (fun i : Fin Tsetup =>
          choices (Fin.castLE (Nat.le_add_right Tsetup (tpair + 1 + V)) i)) =
          setupChoices := by
      funext i
      unfold choices
      rw [dite_eq_left (by simp [Fin.castLE])]
      exact congrArg setupChoices (Fin.ext (by simp [Fin.castLE]))
    have hsuffixChoices :
        (fun i : Fin (tpair + 1 + V) => choices (Fin.natAdd Tsetup i)) =
          suffixChoices := by
      funext i
      unfold choices
      rw [dite_eq_right (by simp [Fin.natAdd])]
      exact congrArg suffixChoices (Fin.ext (by simp [Fin.natAdd]))
    exact satGuessVerify_accepts_after_prefix M Tsetup (tpair + 1 + V) choices
      ((satGuessVerifyNTM M).initCfg x) (satPairWrap M cPair0)
      (by rw [hprefixChoices]; exact hsetupTrace0)
      (by rw [hsuffixChoices]; exact hsuffix0)

/-- The end-to-end accepting completeness theorem packaged in the standard
    `NTM.AcceptsInTime` interface, using the concrete witness-dependent run
    budget from the phase construction. -/
theorem satGuessVerify_acceptsInTime_of_witness_of_decidesInTime (M : TM k)
    {L : Language} {f : ℕ → ℕ} (hM : M.DecidesInTime L f)
    (x y : List Bool) (hlen : y.length ≤ x.length + 1)
    (hmem : pair x y ∈ L) :
    (satGuessVerifyNTM M).AcceptsInTime x
      ((TM.inputLengthPlusOneCounterTime x.length + 1 +
        (TM.inputLengthPlusOneCounterTime x.length + 1 + 2 + 1 +
          (NTM.guessBoundedTime (x.length + 1) 0 + 1))) +
        (TM.pairBuildTime x.length y.length + f (pair x y).length)) := by
  obtain ⟨T, choices, hT, hrun⟩ :=
    satGuessVerify_init_generates_witness_accepts_of_decidesInTime M hM x y
      hlen hmem
  exact NTM.AcceptsInTime.mono hT ⟨choices, hrun⟩

/-- The accepting witness run under the uniform SAT-specialized bound depending
    only on `|x|` and the verifier time window. -/
theorem satGuessVerify_acceptsInTime_of_witness_bound_of_decidesInTime (M : TM k)
    {L : Language} {f : ℕ → ℕ} (hM : M.DecidesInTime L f)
    (x y : List Bool) (hlen : y.length ≤ x.length + 1)
    (hmem : pair x y ∈ L) :
    (satGuessVerifyNTM M).AcceptsInTime x (satGuessVerifyTime f x.length) := by
  have hacc :=
    satGuessVerify_acceptsInTime_of_witness_of_decidesInTime M hM x y hlen hmem
  have hpair :
      TM.pairBuildTime x.length y.length ≤
        TM.pairBuildTime x.length (x.length + 1) := by
    dsimp [TM.pairBuildTime]
    omega
  have hver := satVerifierWindowTime_bounds_pair f x y hlen
  exact NTM.AcceptsInTime.mono (tm := satGuessVerifyNTM M)
    (x := x) (T' := satGuessVerifyTime f x.length) (by
      unfold satGuessVerifyTime satGuessVerifySetupTime
      omega) hacc

/-- SAT-specific accepting run from any concrete satisfying assignment, assuming
    `M` decides the SAT verifier pair language. -/
theorem satGuessVerify_acceptsInTime_of_RSAT_of_decidesInTime (M : TM k)
    {f : ℕ → ℕ} (hM : M.DecidesInTime (pairLang Witness) f)
    (x y : List Bool) (hR : Witness x y) :
    (satGuessVerifyNTM M).AcceptsInTime x
      ((TM.inputLengthPlusOneCounterTime x.length + 1 +
        (TM.inputLengthPlusOneCounterTime x.length + 1 + 2 + 1 +
        (NTM.guessBoundedTime (x.length + 1) 0 + 1))) +
        (TM.pairBuildTime x.length y.length + f (pair x y).length)) := by
  have hmem : pair x y ∈ pairLang Witness := ⟨x, y, rfl, hR⟩
  obtain ⟨_, _, hlen, _⟩ := hR
  exact satGuessVerify_acceptsInTime_of_witness_of_decidesInTime M hM x y hlen
    hmem

/-- SAT-specific accepting run from any concrete satisfying assignment under
    the uniform SAT-specialized bound. -/
theorem satGuessVerify_acceptsInTime_of_RSAT_bound_of_decidesInTime (M : TM k)
    {f : ℕ → ℕ} (hM : M.DecidesInTime (pairLang Witness) f)
    (x y : List Bool) (hR : Witness x y) :
    (satGuessVerifyNTM M).AcceptsInTime x (satGuessVerifyTime f x.length) := by
  have hmem : pair x y ∈ pairLang Witness := ⟨x, y, rfl, hR⟩
  obtain ⟨_, _, hlen, _⟩ := hR
  exact satGuessVerify_acceptsInTime_of_witness_bound_of_decidesInTime M hM x y
    hlen hmem

/-- Timed yes-instance half for `language` under the uniform SAT-specialized bound,
    assuming `M` decides the SAT verifier pair language. -/
theorem satGuessVerify_acceptsInTime_of_mem_LSAT_of_decidesInTime (M : TM k)
    {f : ℕ → ℕ} (hM : M.DecidesInTime (pairLang Witness) f)
    (x : List Bool) (hx : x ∈ language) :
    (satGuessVerifyNTM M).AcceptsInTime x (satGuessVerifyTime f x.length) := by
  obtain ⟨y, hR⟩ := (mem_language_iff_witness x).1 hx
  exact satGuessVerify_acceptsInTime_of_RSAT_bound_of_decidesInTime M hM x y hR

/-- Yes-instances of `language` are accepted by the SAT-specialized
    guess-and-verify machine, assuming `M` decides the SAT verifier pair
    language. This is the unbounded acceptance half of the final NP decision
    theorem. -/
theorem satGuessVerify_accepts_of_mem_LSAT_of_decidesInTime (M : TM k)
    {f : ℕ → ℕ} (hM : M.DecidesInTime (pairLang Witness) f)
    (x : List Bool) (hx : x ∈ language) :
    (satGuessVerifyNTM M).Accepts x := by
  exact NTM.accepts_of_acceptsInTime
    (satGuessVerify_acceptsInTime_of_mem_LSAT_of_decidesInTime M hM x hx)

/-- All computation paths of the SAT-specialized machine halt within the
    uniform bound induced by the setup budget and the verifier time window. -/
theorem satGuessVerify_allPathsHaltIn_of_decidesInTime (M : TM k)
    {L : Language} {f : ℕ → ℕ} (hM : M.DecidesInTime L f) :
    (satGuessVerifyNTM M).AllPathsHaltIn (satGuessVerifyTime f) := by
  intro x choices
  let setupChoicesAll : Fin (satGuessVerifySetupTime x.length) → Bool := fun i =>
    choices (Fin.castLE (by
      unfold satGuessVerifyTime
      omega) i)
  obtain ⟨Tsetup, hTsetup, y, hy, cPair, hsetup⟩ :=
    satGuessVerify_setup_exits_with_pair_frames M x setupChoicesAll
  let setupChoices : Fin Tsetup → Bool := fun i => setupChoicesAll (Fin.castLE hTsetup i)
  have hsetupTrace :
      (satGuessVerifyNTM M).trace Tsetup setupChoices ((satGuessVerifyNTM M).initCfg x) =
        satPairWrap M cPair := by
    simpa [setupChoicesAll, setupChoices] using hsetup.1
  have hpairState : cPair.state = TM.PairBuildPhase.init := hsetup.2.1
  have hpairInput :
      cPair.input = (Tape.init (x.map Γ.ofBool)).move Dir3.right := hsetup.2.2.1
  have hpairWitness :
      cPair.work (satWitnessIdx k) =
        (Tape.init (y.map Γ.ofBool)).move Dir3.right := hsetup.2.2.2.1
  have hpairBlank :
      cPair.work (satPairIdx k) = (Tape.init []).move Dir3.right := hsetup.2.2.2.2.1
  have hpairOutput :
      cPair.output = (Tape.init []).move Dir3.right := hsetup.2.2.2.2.2.1
  have hpairVerifierWork :
      ∀ i : Fin k, cPair.work (satVerifierWorkIdx i) =
        (Tape.init []).move Dir3.right := hsetup.2.2.2.2.2.2
  let cPair0 : Cfg (k + 3) TM.PairBuildPhase :=
    { state := TM.PairBuildPhase.init,
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
      work := cPair.work,
      output := cPair.output }
  have hcPair : cPair = cPair0 := by
    cases cPair with
    | mk state input work output =>
        simp [cPair0] at hpairState hpairInput ⊢
        exact ⟨hpairState, hpairInput⟩
  have hsetupTrace0 :
      (satGuessVerifyNTM M).trace Tsetup setupChoices ((satGuessVerifyNTM M).initCfg x) =
        satPairWrap M cPair0 := by
    rw [← hcPair]
    exact hsetupTrace
  let U := TM.pairBuildTime x.length (x.length + 1) + satVerifierWindowTime f x.length
  let suffixChoices : Fin U → Bool := fun i =>
    choices ⟨Tsetup + i.val, by
      unfold U satGuessVerifyTime
      omega⟩
  have hsuffix :
      (satGuessVerifyNTM M).halted
        ((satGuessVerifyNTM M).trace U suffixChoices (satPairWrap M cPair0)) := by
    simpa [U, cPair0] using
      satGuessVerify_pair_start_halts_within_bound_of_decidesInTime M hM x y
        cPair.work cPair.output ⟨hpairWitness, hpairBlank⟩ hpairOutput
        hpairVerifierWork hy suffixChoices
  let shortChoices : Fin (Tsetup + U) → Bool := fun i =>
    choices ⟨i.val, by
      unfold U satGuessVerifyTime
      omega⟩
  have hprefixChoices :
      (fun i : Fin Tsetup =>
        shortChoices (Fin.castLE (Nat.le_add_right Tsetup U) i)) =
      setupChoices := by
    funext i
    unfold shortChoices setupChoices setupChoicesAll
    apply congrArg choices
    exact Fin.ext (by simp [Fin.castLE])
  have hsuffixChoices :
      (fun i : Fin U => shortChoices (Fin.natAdd Tsetup i)) = suffixChoices := by
    funext i
    unfold shortChoices suffixChoices
    apply congrArg choices
    exact Fin.ext (by simp [Fin.natAdd])
  have hshort :
      (satGuessVerifyNTM M).halted
        ((satGuessVerifyNTM M).trace (Tsetup + U) shortChoices
          ((satGuessVerifyNTM M).initCfg x)) := by
    exact satGuessVerify_halts_after_prefix M Tsetup U shortChoices
      ((satGuessVerifyNTM M).initCfg x) (satPairWrap M cPair0)
      (by rw [hprefixChoices]; exact hsetupTrace0)
      (by rw [hsuffixChoices]; exact hsuffix)
  have hshortBound : Tsetup + U ≤ satGuessVerifyTime f x.length := by
    unfold U satGuessVerifyTime
    omega
  have hmono := (satGuessVerifyNTM M).trace_mono hshortBound
    (choices := shortChoices) (choices' := choices)
    (c := (satGuessVerifyNTM M).initCfg x) (by intro i; rfl) hshort
  rw [hmono]
  exact hshort

/-- Every full SAT-specialized run within the uniform bound factors through
    some bounded guessed witness `y`, and the final output bit matches the
    verifier's decision on `pair x y`. -/
theorem satGuessVerify_trace_decides_for_some_setup_witness_of_decidesInTime
    (M : TM k) {L : Language} {f : ℕ → ℕ} (hM : M.DecidesInTime L f)
    (x : List Bool) (choices : Fin (satGuessVerifyTime f x.length) → Bool) :
    ∃ y : List Bool, y.length ≤ x.length + 1 ∧
      let cFinal := (satGuessVerifyNTM M).trace (satGuessVerifyTime f x.length) choices
        ((satGuessVerifyNTM M).initCfg x)
      (satGuessVerifyNTM M).halted cFinal ∧
        ((pair x y ∈ L → cFinal.output.cells 1 = Γ.one) ∧
          (pair x y ∉ L → cFinal.output.cells 1 = Γ.zero)) := by
  let setupChoicesAll : Fin (satGuessVerifySetupTime x.length) → Bool := fun i =>
    choices (Fin.castLE (by
      unfold satGuessVerifyTime
      omega) i)
  obtain ⟨Tsetup, hTsetup, y, hy, cPair, hsetup⟩ :=
    satGuessVerify_setup_exits_with_pair_frames M x setupChoicesAll
  let setupChoices : Fin Tsetup → Bool := fun i => setupChoicesAll (Fin.castLE hTsetup i)
  have hsetupTrace :
      (satGuessVerifyNTM M).trace Tsetup setupChoices ((satGuessVerifyNTM M).initCfg x) =
        satPairWrap M cPair := by
    simpa [setupChoicesAll, setupChoices] using hsetup.1
  have hpairState : cPair.state = TM.PairBuildPhase.init := hsetup.2.1
  have hpairInput :
      cPair.input = (Tape.init (x.map Γ.ofBool)).move Dir3.right := hsetup.2.2.1
  have hpairWitness :
      cPair.work (satWitnessIdx k) =
        (Tape.init (y.map Γ.ofBool)).move Dir3.right := hsetup.2.2.2.1
  have hpairBlank :
      cPair.work (satPairIdx k) = (Tape.init []).move Dir3.right := hsetup.2.2.2.2.1
  have hpairOutput :
      cPair.output = (Tape.init []).move Dir3.right := hsetup.2.2.2.2.2.1
  have hpairVerifierWork :
      ∀ i : Fin k, cPair.work (satVerifierWorkIdx i) =
        (Tape.init []).move Dir3.right := hsetup.2.2.2.2.2.2
  let cPair0 : Cfg (k + 3) TM.PairBuildPhase :=
    { state := TM.PairBuildPhase.init,
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
      work := cPair.work,
      output := cPair.output }
  have hcPair : cPair = cPair0 := by
    cases cPair with
    | mk state input work output =>
        simp [cPair0] at hpairState hpairInput ⊢
        exact ⟨hpairState, hpairInput⟩
  have hsetupTrace0 :
      (satGuessVerifyNTM M).trace Tsetup setupChoices ((satGuessVerifyNTM M).initCfg x) =
        satPairWrap M cPair0 := by
    rw [← hcPair]
    exact hsetupTrace
  let U := TM.pairBuildTime x.length (x.length + 1) + satVerifierWindowTime f x.length
  let suffixChoices : Fin U → Bool := fun i =>
    choices ⟨Tsetup + i.val, by
      unfold U satGuessVerifyTime
      omega⟩
  have hsuffix :
      let cFinal := (satGuessVerifyNTM M).trace U suffixChoices (satPairWrap M cPair0)
      (satGuessVerifyNTM M).halted cFinal ∧
        ((pair x y ∈ L → cFinal.output.cells 1 = Γ.one) ∧
          (pair x y ∉ L → cFinal.output.cells 1 = Γ.zero)) := by
    simpa [U, cPair0] using
      satGuessVerify_pair_start_decides_within_bound_of_decidesInTime M hM x y
        cPair.work cPair.output ⟨hpairWitness, hpairBlank⟩ hpairOutput
        hpairVerifierWork hy suffixChoices
  let shortChoices : Fin (Tsetup + U) → Bool := fun i =>
    choices ⟨i.val, by
      unfold U satGuessVerifyTime
      omega⟩
  have hprefixChoices :
      (fun i : Fin Tsetup =>
        shortChoices (Fin.castLE (Nat.le_add_right Tsetup U) i)) =
      setupChoices := by
    funext i
    unfold shortChoices setupChoices setupChoicesAll
    apply congrArg choices
    exact Fin.ext (by simp [Fin.castLE])
  have hsuffixChoices :
      (fun i : Fin U => shortChoices (Fin.natAdd Tsetup i)) = suffixChoices := by
    funext i
    unfold shortChoices suffixChoices
    apply congrArg choices
    exact Fin.ext (by simp [Fin.natAdd])
  have hshortHalt :
      (satGuessVerifyNTM M).halted
        ((satGuessVerifyNTM M).trace (Tsetup + U) shortChoices
          ((satGuessVerifyNTM M).initCfg x)) := by
    exact satGuessVerify_halts_after_prefix M Tsetup U shortChoices
      ((satGuessVerifyNTM M).initCfg x) (satPairWrap M cPair0)
      (by rw [hprefixChoices]; exact hsetupTrace0)
      (by rw [hsuffixChoices]; exact hsuffix.1)
  have htraceShort :
      (satGuessVerifyNTM M).trace (Tsetup + U) shortChoices ((satGuessVerifyNTM M).initCfg x) =
        (satGuessVerifyNTM M).trace U (fun i => shortChoices (Fin.natAdd Tsetup i))
          (satPairWrap M cPair0) := by
    rw [NTM.trace_add (satGuessVerifyNTM M) Tsetup U shortChoices
      ((satGuessVerifyNTM M).initCfg x)]
    rw [hprefixChoices, hsetupTrace0]
  have hshortYes :
      pair x y ∈ L →
        ((satGuessVerifyNTM M).trace (Tsetup + U) shortChoices
          ((satGuessVerifyNTM M).initCfg x)).output.cells 1 = Γ.one := by
    intro hmem
    rw [htraceShort, hsuffixChoices]
    exact hsuffix.2.1 hmem
  have hshortNo :
      pair x y ∉ L →
        ((satGuessVerifyNTM M).trace (Tsetup + U) shortChoices
          ((satGuessVerifyNTM M).initCfg x)).output.cells 1 = Γ.zero := by
    intro hnotmem
    rw [htraceShort, hsuffixChoices]
    exact hsuffix.2.2 hnotmem
  have hshortBound : Tsetup + U ≤ satGuessVerifyTime f x.length := by
    unfold U satGuessVerifyTime
    omega
  have hmono := (satGuessVerifyNTM M).trace_mono hshortBound
    (choices := shortChoices) (choices' := choices)
    (c := (satGuessVerifyNTM M).initCfg x) (by intro i; rfl) hshortHalt
  refine ⟨y, hy, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hmono]
    exact hshortHalt
  · intro hmem
    rw [hmono]
    exact hshortYes hmem
  · intro hnotmem
    rw [hmono]
    exact hshortNo hnotmem

/-- No SAT instance outside `language` has an accepting run within the uniform
    SAT-specialized bound, assuming the verifier decides `pairLang Witness`. -/
theorem satGuessVerify_not_acceptsInTime_of_not_mem_LSAT_of_decidesInTime (M : TM k)
    {f : ℕ → ℕ} (hM : M.DecidesInTime (pairLang Witness) f)
    (x : List Bool) (hx : x ∉ language) :
    ¬ (satGuessVerifyNTM M).AcceptsInTime x (satGuessVerifyTime f x.length) := by
  intro hacc
  obtain ⟨choices, hhalt, hout⟩ := hacc
  obtain ⟨y, hy, htrace⟩ :=
    satGuessVerify_trace_decides_for_some_setup_witness_of_decidesInTime M hM x choices
  have hnotpair : pair x y ∉ pairLang Witness := by
    intro hpair
    rcases hpair with ⟨x', y', hp, hR⟩
    obtain ⟨hx', hy'⟩ := pair_inj hp
    subst hx' hy'
    exact hx ((mem_language_iff_witness x).2 ⟨y, hR⟩)
  have hzero : ((satGuessVerifyNTM M).trace (satGuessVerifyTime f x.length) choices
      ((satGuessVerifyNTM M).initCfg x)).output.cells 1 = Γ.zero :=
    htrace.2.2 hnotpair
  rw [hzero] at hout
  have hzero_ne_one : Γ.zero ≠ Γ.one := by decide
  exact hzero_ne_one hout

/-- The SAT-specialized machine decides `language` within the uniform bound
    `satGuessVerifyTime`, assuming `M` decides the SAT verifier pair language. -/
theorem satGuessVerify_decidesInTime_of_decidesInTime (M : TM k)
    {f : ℕ → ℕ} (hM : M.DecidesInTime (pairLang Witness) f) :
    (satGuessVerifyNTM M).DecidesInTime language (satGuessVerifyTime f) := by
  refine ⟨satGuessVerify_allPathsHaltIn_of_decidesInTime M hM, ?_⟩
  intro x
  constructor
  · exact satGuessVerify_acceptsInTime_of_mem_LSAT_of_decidesInTime M hM x
  · intro hacc
    by_contra hx
    exact satGuessVerify_not_acceptsInTime_of_not_mem_LSAT_of_decidesInTime M hM x hx hacc

/-- If the verifier time bound is polynomial, then the SAT-specialized
    witness-independent runtime `satGuessVerifyTime` is pointwise bounded by
    an explicit polynomial. -/
theorem satGuessVerifyTime_polynomial_bound {f : ℕ → ℕ} {c : ℕ}
    (hfO : f =O (· ^ c)) :
    ∃ q : Polynomial ℕ, ∀ n, satGuessVerifyTime f n ≤ q.eval n := by
  obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound hfO
  let lin : Polynomial ℕ := Polynomial.C 3 * Polynomial.X + Polynomial.C 3
  let q : Polynomial ℕ := (Polynomial.C 15 * Polynomial.X + Polynomial.C 44) + p.comp lin
  refine ⟨q, ?_⟩
  intro n
  have hwindow : satVerifierWindowTime f n ≤ (p.comp lin).eval n := by
    unfold satVerifierWindowTime
    refine Finset.sup_le ?_
    intro m hm
    have hfm : f (2 * n + 2 + m) ≤ p.eval (2 * n + 2 + m) := hp _
    have harg : 2 * n + 2 + m ≤ 3 * n + 3 := by
      rw [Finset.mem_range] at hm
      omega
    have hpmono : p.eval (2 * n + 2 + m) ≤ p.eval (3 * n + 3) :=
      polynomial_eval_mono_nat p harg
    exact le_trans hfm (by
      simpa [lin, Polynomial.eval_comp, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using hpmono)
  have htime : satGuessVerifyTime f n ≤ 15 * n + 44 + (p.comp lin).eval n := by
    have hwindow' := hwindow
    unfold satGuessVerifyTime satGuessVerifySetupTime
    unfold TM.inputLengthPlusOneCounterTime NTM.guessBoundedTime TM.pairBuildTime at *
    omega
  calc
    satGuessVerifyTime f n ≤ 15 * n + 44 + (p.comp lin).eval n := htime
    _ = q.eval n := by
      simp [q, lin, Polynomial.eval_comp, Nat.mul_comm, Nat.add_assoc, Nat.add_comm]

/-- If the verifier time bound is polynomial, then the SAT-specialized
    runtime `satGuessVerifyTime` is polynomial too. -/
theorem satGuessVerifyTime_bigO_of_bigO {f : ℕ → ℕ} {c : ℕ}
    (hfO : f =O (· ^ c)) :
    ∃ d : ℕ, satGuessVerifyTime f =O (· ^ d) := by
  obtain ⟨q, hq⟩ := satGuessVerifyTime_polynomial_bound hfO
  exact ⟨q.natDegree, BigO.of_polynomial_bound q hq⟩

/-- Direct SAT route: if the deterministic verifier for `Witness` is in `P`,
    then the completed SAT-specialized guess-and-verify machine puts `language`
    in `NP`. This bypasses the still-open generic witness-language interface
    and packages the concrete construction proved in this file. -/
theorem language_mem_NP_of_verifierP_direct (h : pairLang Witness ∈ P) :
    language ∈ NP := by
  obtain ⟨c, k, M, f, hM, hfO⟩ := Set.mem_iUnion.mp h
  obtain ⟨d, hgO⟩ := satGuessVerifyTime_bigO_of_bigO hfO
  refine Set.mem_iUnion.mpr ⟨d, k + 3, satGuessVerifyNTM M, satGuessVerifyTime f, ?_, hgO⟩
  exact satGuessVerify_decidesInTime_of_decidesInTime M hM

/-- The full boundary step from counter setup into input rewind. -/
theorem satGuessVerify_counter_done_trace_one (M : TM k)
    (choice : Bool) (inp : Tape) (work : Fin (k + 3) → Tape) (out : Tape) :
    (satGuessVerifyNTM M).trace 1 (fun _ => choice)
      { state := GuessVerifyPhase.counter TM.LinearCounterPhase.done,
        input := inp, work := work, output := out } =
      satRewindInputWrap M
        { state := TM.RewindPhase.moveLeft,
          input := satBoundaryInput inp,
          work := satBoundaryWork work,
          output := satBoundaryOutput out } := by
  simp [satRewindInputWrap, satGuessVerifyNTM, satGuessVerifyDelta,
    phaseBoundary, satBoundaryInput, satBoundaryOutput, NTM.trace]
  funext i
  rfl

/-- The full boundary step from input rewind into bounded guessing. -/
theorem satGuessVerify_rewind_done_trace_one (M : TM k)
    (choice : Bool) (inp : Tape) (work : Fin (k + 3) → Tape) (out : Tape) :
    (satGuessVerifyNTM M).trace 1 (fun _ => choice)
      { state := GuessVerifyPhase.rewindInput TM.RewindPhase.done,
        input := inp, work := work, output := out } =
      satGuessWrap M
        { state := NTM.GuessBoundedPhase.choose,
          input := satBoundaryInput inp,
          work := satBoundaryWork work,
          output := satBoundaryOutput out } := by
  simp [satGuessWrap, satGuessVerifyNTM, satGuessVerifyDelta,
    phaseBoundary, satBoundaryInput, satBoundaryOutput, NTM.trace]
  funext i
  rfl

/-- The full boundary step from bounded guessing into pair building. -/
theorem satGuessVerify_guess_done_trace_one (M : TM k)
    (choice : Bool) (inp : Tape) (work : Fin (k + 3) → Tape) (out : Tape) :
    (satGuessVerifyNTM M).trace 1 (fun _ => choice)
      { state := GuessVerifyPhase.guess NTM.GuessBoundedPhase.done,
        input := inp, work := work, output := out } =
      satPairWrap M
        { state := TM.PairBuildPhase.init,
          input := satBoundaryInput inp,
          work := satBoundaryWork work,
          output := satBoundaryOutput out } := by
  simp [satPairWrap, satGuessVerifyNTM, satGuessVerifyDelta,
    phaseBoundary, satBoundaryInput, satBoundaryOutput, NTM.trace]
  funext i
  rfl

/-- The full boundary step from pair building into verifier simulation. -/
theorem satGuessVerify_pair_done_trace_one (M : TM k)
    (choice : Bool) (inp : Tape) (work : Fin (k + 3) → Tape) (out : Tape) :
    (satGuessVerifyNTM M).trace 1 (fun _ => choice)
      { state := GuessVerifyPhase.pair TM.PairBuildPhase.done,
        input := inp, work := work, output := out } =
      satVerifyWrap M
        { state := verifierStartedState M,
          input := satBoundaryInput inp,
          work := satBoundaryWork work,
          output := satBoundaryOutput out } := by
  simp [satVerifyWrap, satGuessVerifyNTM, satGuessVerifyDelta,
    phaseBoundary, satBoundaryInput, satBoundaryOutput, NTM.trace]
  funext i
  rfl

/-- State-only form of the boundary step from a finished counter phase into
    input rewinding. -/
theorem satGuessVerify_counter_done_trace_one_state (M : TM k)
    (choice : Bool) (inp : Tape) (work : Fin (k + 3) → Tape) (out : Tape) :
    ((satGuessVerifyNTM M).trace 1 (fun _ => choice)
      { state := GuessVerifyPhase.counter TM.LinearCounterPhase.done,
        input := inp, work := work, output := out }).state =
      GuessVerifyPhase.rewindInput TM.RewindPhase.moveLeft := by
  simp [satGuessVerifyNTM, satGuessVerifyDelta, phaseBoundary, NTM.trace]

/-- State-only form of the boundary step from a finished rewind phase into
    bounded guessing. -/
theorem satGuessVerify_rewind_done_trace_one_state (M : TM k)
    (choice : Bool) (inp : Tape) (work : Fin (k + 3) → Tape) (out : Tape) :
    ((satGuessVerifyNTM M).trace 1 (fun _ => choice)
      { state := GuessVerifyPhase.rewindInput TM.RewindPhase.done,
        input := inp, work := work, output := out }).state =
      GuessVerifyPhase.guess NTM.GuessBoundedPhase.choose := by
  simp [satGuessVerifyNTM, satGuessVerifyDelta, phaseBoundary, NTM.trace]

/-- State-only form of the boundary step from a finished guess phase into pair
    building. -/
theorem satGuessVerify_guess_done_trace_one_state (M : TM k)
    (choice : Bool) (inp : Tape) (work : Fin (k + 3) → Tape) (out : Tape) :
    ((satGuessVerifyNTM M).trace 1 (fun _ => choice)
      { state := GuessVerifyPhase.guess NTM.GuessBoundedPhase.done,
        input := inp, work := work, output := out }).state =
      GuessVerifyPhase.pair TM.PairBuildPhase.init := by
  simp [satGuessVerifyNTM, satGuessVerifyDelta, phaseBoundary, NTM.trace]

theorem satGuessVerify_pair_done_trace_one_state (M : TM k)
    (choice : Bool) (inp : Tape) (work : Fin (k + 3) → Tape) (out : Tape) :
    ((satGuessVerifyNTM M).trace 1 (fun _ => choice)
      { state := GuessVerifyPhase.pair TM.PairBuildPhase.done,
        input := inp, work := work, output := out }).state =
      GuessVerifyPhase.verify (verifierStartedState M) := by
  simp [satGuessVerifyNTM, satGuessVerifyDelta, phaseBoundary, NTM.trace]

end SAT

end Complexity
