/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.Tseitin.Machine.Defs

/-!
# Streaming controller for the CNF-to-3CNF reduction machine

`validEmitterTM` is the concrete valid-input controller for the buffer and
emission layer. It reads the already-validated input in two-bit
tokens, keeps literal signs and the number of pending literals in finite
control, and stores all unbounded variable indices in unary work registers.

The controller invokes three families of child machines:

- `incRegTM currentReg` for every unary body bit;
- `commitLiteralTM pending` at a literal separator;
- `closeClauseTM pending` at a clause separator.

The latter two child-state types depend on `pending`, so the controller state
uses sigma types. Each child is run to its halt state before the controller
resumes reading at the next input token. `reductionTM` installs this controller
in the validation-first total assembly from `Machine.Defs`.

This file defines the machine. Its simulation invariant and polynomial-time
accounting live in proof-only internal modules and are exposed publicly by
`Complexitylib.SAT.Tseitin.Machine`.
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-! ## Controller state -/

/-- Parser mode after tokenization. A literal sign is retained in finite
control while its unary variable body accumulates in `currentReg`. -/
inductive StreamMode where
  | boundary (pending : PendingSigns)
  | literal (pending : PendingSigns) (sign : Bool)
  deriving DecidableEq, Fintype, Repr

/-- The controller alternates between the first and second bit of each token. -/
inductive ReadPhase where
  | first (mode : StreamMode)
  | second (mode : StreamMode) (firstBit : Bool)
  deriving DecidableEq, Fintype, Repr

/-- State of an in-progress unary-register increment, paired with the parser
mode to restore when the child machine halts. -/
abbrev IncrementCall :=
  StreamMode × (TM.incRegTM currentReg).Q

instance incrementCallDecidableEq : DecidableEq IncrementCall := by
  dsimp only [IncrementCall]
  infer_instance

/-- State of an in-progress literal commit. The child state type depends on
the pending-sign shape selected at the call site. -/
abbrev CommitCall :=
  Σ pending : PendingSigns, Bool × (commitLiteralTM pending).Q

/-- Equality decision for the pending-dependent commit child state. -/
local instance commitStateDecidableEq (pending : PendingSigns) :
    DecidableEq (commitLiteralTM pending).Q :=
  (commitLiteralTM pending).decEq

instance commitCallDecidableEq : DecidableEq CommitCall := by
  dsimp only [CommitCall]
  infer_instance

/-- State of an in-progress clause close. -/
abbrev CloseCall :=
  Σ pending : PendingSigns, (closeClauseTM pending).Q

/-- Equality decision for the pending-dependent clause-close child state. -/
local instance closeStateDecidableEq (pending : PendingSigns) :
    DecidableEq (closeClauseTM pending).Q :=
  (closeClauseTM pending).decEq

instance closeCallDecidableEq : DecidableEq CloseCall := by
  dsimp only [CloseCall]
  infer_instance

/-- Finite controller states: reading, one of three dependent child calls, or
the unique halt state. -/
abbrev ControllerQ :=
  ReadPhase ⊕ (IncrementCall ⊕ (CommitCall ⊕ (CloseCall ⊕ Unit)))

deriving instance DecidableEq for ControllerQ

/-- Inject a read phase into the controller state. -/
def controllerRead (phase : ReadPhase) : ControllerQ := .inl phase

/-- Inject an increment child state into the controller state. -/
def controllerIncrement (mode : StreamMode) (q : (TM.incRegTM currentReg).Q) :
    ControllerQ :=
  .inr (.inl (mode, q))

/-- Inject a pending-dependent commit child state into the controller state. -/
def controllerCommit (pending : PendingSigns) (sign : Bool)
    (q : (commitLiteralTM pending).Q) : ControllerQ :=
  .inr (.inr (.inl ⟨pending, (sign, q)⟩))

/-- Inject a pending-dependent clause-close child state. -/
def controllerClose (pending : PendingSigns) (q : (closeClauseTM pending).Q) :
    ControllerQ :=
  .inr (.inr (.inr (.inl ⟨pending, q⟩)))

/-- The unique controller halt state. -/
def controllerDone : ControllerQ := .inr (.inr (.inr (.inr ())))

/-- Schedule the operation denoted by a complete token. Invalid cases halt;
they are unreachable after the preceding successful validation pass. -/
def scheduleToken (mode : StreamMode) (token : EncToken) : ControllerQ :=
  match mode, token with
  | .boundary pending, .bit sign =>
      controllerRead (.first (.literal pending sign))
  | .boundary pending, .clauseSep =>
      controllerClose pending (closeClauseTM pending).qstart
  | .boundary _, .litSep => controllerDone
  | .literal pending sign, .bit true =>
      controllerIncrement (.literal pending sign) (TM.incRegTM currentReg).qstart
  | .literal _ _, .bit false => controllerDone
  | .literal pending sign, .litSep =>
      controllerCommit pending sign (commitLiteralTM pending).qstart
  | .literal _ _, .clauseSep => controllerDone

/-! ## Concrete controller -/

/-- Stream over a validated concrete CNF encoding and emit its exact-3 Tseitin
transformation. The input must begin at cell one, `freshReg` must hold the
first fresh variable, all literal buffers must be zero registers, and the
output must be an empty append-only accumulator. -/
def validEmitterTM : TM workTapeCount :=
  { Q := ControllerQ
    qstart := controllerRead (.first (.boundary .zero))
    qhalt := controllerDone
    δ := fun state iHead wHeads oHead =>
      match state with
      | Sum.inl readPhase =>
        match readPhase with
        | .first mode =>
          if iHead = Γ.start then
            (controllerRead (.first mode),
              fun i => TM.readBackWrite (wHeads i), TM.readBackWrite oHead,
              .right, fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
          else if iHead = Γ.blank then
            (controllerDone, fun i => TM.readBackWrite (wHeads i),
              TM.readBackWrite oHead, TM.idleDir iHead,
              fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
          else
            let firstBit : Bool := decide (iHead = Γ.one)
            (controllerRead (.second mode firstBit),
              fun i => TM.readBackWrite (wHeads i), TM.readBackWrite oHead,
              .right, fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
        | .second mode firstBit =>
          if iHead = Γ.start then
            (controllerRead (.second mode firstBit),
              fun i => TM.readBackWrite (wHeads i), TM.readBackWrite oHead,
              .right, fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
          else if iHead = Γ.blank then
            (controllerDone, fun i => TM.readBackWrite (wHeads i),
              TM.readBackWrite oHead, TM.idleDir iHead,
              fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
          else
            let secondBit : Bool := decide (iHead = Γ.one)
            let next := scheduleToken mode (tokenOfPair firstBit secondBit)
            (next, fun i => TM.readBackWrite (wHeads i), TM.readBackWrite oHead,
              .right, fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
      | Sum.inr (Sum.inl (mode, q)) =>
        let child := TM.incRegTM currentReg
        if q = child.qhalt then
          (controllerRead (.first mode), fun i => TM.readBackWrite (wHeads i),
            TM.readBackWrite oHead, TM.idleDir iHead,
            fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
        else
          let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
            child.δ q iHead wHeads oHead
          (controllerIncrement mode q', workWrites, outWrite, inDir, workDirs, outDir)
      | Sum.inr (Sum.inr (Sum.inl ⟨pending, (sign, q)⟩)) =>
        let child := commitLiteralTM pending
        if q = child.qhalt then
          (controllerRead (.first (.boundary (pending.push sign))),
            fun i => TM.readBackWrite (wHeads i), TM.readBackWrite oHead,
            TM.idleDir iHead, fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
        else
          let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
            child.δ q iHead wHeads oHead
          (controllerCommit pending sign q', workWrites, outWrite, inDir,
            workDirs, outDir)
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨pending, q⟩))) =>
        let child := closeClauseTM pending
        if q = child.qhalt then
          (controllerRead (.first (.boundary .zero)),
            fun i => TM.readBackWrite (wHeads i), TM.readBackWrite oHead,
            TM.idleDir iHead, fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
        else
          let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
            child.δ q iHead wHeads oHead
          (controllerClose pending q', workWrites, outWrite, inDir, workDirs, outDir)
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) =>
          TM.allIdle controllerDone iHead wHeads oHead
    δ_right_of_start := by
      intro state iHead wHeads oHead
      match state with
      | Sum.inl readPhase =>
        match readPhase with
        | .first _ =>
          dsimp only []
          split
          · exact ⟨fun _ => rfl, fun _ => TM.idleDir_right_of_start,
              TM.idleDir_right_of_start⟩
          · split
            · exact ⟨TM.idleDir_right_of_start,
                fun _ => TM.idleDir_right_of_start, TM.idleDir_right_of_start⟩
            · exact ⟨fun _ => rfl, fun _ => TM.idleDir_right_of_start,
                TM.idleDir_right_of_start⟩
        | .second _ _ =>
          dsimp only []
          split
          · exact ⟨fun _ => rfl, fun _ => TM.idleDir_right_of_start,
              TM.idleDir_right_of_start⟩
          · split
            · exact ⟨TM.idleDir_right_of_start,
                fun _ => TM.idleDir_right_of_start, TM.idleDir_right_of_start⟩
            · exact ⟨fun _ => rfl, fun _ => TM.idleDir_right_of_start,
                TM.idleDir_right_of_start⟩
      | Sum.inr (Sum.inl (mode, q)) =>
        dsimp only []
        split
        · exact ⟨TM.idleDir_right_of_start, fun _ => TM.idleDir_right_of_start,
            TM.idleDir_right_of_start⟩
        · exact (TM.incRegTM currentReg).δ_right_of_start q iHead wHeads oHead
      | Sum.inr (Sum.inr (Sum.inl ⟨pending, (sign, q)⟩)) =>
        dsimp only []
        split
        · exact ⟨TM.idleDir_right_of_start, fun _ => TM.idleDir_right_of_start,
            TM.idleDir_right_of_start⟩
        · exact (commitLiteralTM pending).δ_right_of_start q iHead wHeads oHead
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨pending, q⟩))) =>
        dsimp only []
        split
        · exact ⟨TM.idleDir_right_of_start, fun _ => TM.idleDir_right_of_start,
            TM.idleDir_right_of_start⟩
        · exact (closeClauseTM pending).δ_right_of_start q iHead wHeads oHead
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) =>
          exact TM.rightOfStart_allIdle iHead wHeads oHead }

/-- Final concrete machine for the total encoded reduction. It initializes the
fresh counter, validates before emission, clears the validator verdict on the
selected branch, runs `validEmitterTM` on valid inputs, and emits the fixed
fallback on malformed inputs. -/
def reductionTM : TM workTapeCount := reductionTMWith validEmitterTM

end Machine

end ThreeSAT

end SAT

end Complexity
