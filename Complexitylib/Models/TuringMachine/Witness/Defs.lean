/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.GuessStream

/-!
# Online witness machines

A `WitnessTM k` is a deterministic machine with `k` ordinary work tapes and a
separate, read-only Boolean witness stream. Its `GuessProtocol` permits reading
a witness bit only when consuming it; nonadvancing steps leave the stream alone.
The stream starts at its first bit, with no setup cost and no observable end marker.
This is an online witness model, not a two-way certificate-input model.

Time is uniform over all streams. Space excludes the witness tape but charges
ordinary work, input-tail travel, and output travel exactly as for `NTM`.
Acceptance means halting with output `1`; every other halted output rejects.
-/

@[expose] public section

namespace Complexity

namespace NTM

/-- One NTM simultaneously obeys the given time and space bounds. Every prefix
of every full-length choice sequence satisfies the decision-space convention. -/
def DecidesInTimeSpace (N : NTM k) (L : Language) (T S : ℕ → ℕ) : Prop :=
  N.DecidesInTime L T ∧
    ∀ x (choices : Fin (T x.length) → Bool) (t : ℕ) (ht : t ≤ T x.length),
      (N.trace t (fun j => choices ⟨j.val, by omega⟩) (N.initCfg x)).WithinDecisionSpace
        x.length (S x.length)

end NTM

/-- A deterministic machine with a separate online witness stream. The last
physical work tape implements the stream and is excluded from charged space. -/
structure WitnessTM (k : ℕ) where
  /-- The deterministic machine, including its last, distinguished witness tape. -/
  machine : TM (k + 1)
  /-- States in which the next witness bit is read and consumed. -/
  advancing : machine.Q → Bool
  /-- The witness is read-only and never consulted without being consumed. -/
  protocol : TM.GuessProtocol machine advancing

namespace WitnessTM

/-- Execute with input `x` and externally supplied witness stream `g`, standing
still after halting. All ordinary heads start at cell zero; the witness starts at one. -/
def run (W : WitnessTM k) (x : List Bool) (g : ℕ → Bool) (t : ℕ) :
    Cfg (k + 1) W.machine.Q :=
  W.machine.traceD t (NTM.loadCfg W.machine x g)

/-- Replace each consumed witness bit by a nondeterministic transition choice. -/
def toNTM (W : WitnessTM k) : NTM k := NTM.ofGuess W.machine

/-- A single time bound applies to every input and every witness stream. -/
def AllWitnessesHaltIn (W : WitnessTM k) (T : ℕ → ℕ) : Prop :=
  ∀ x g, W.machine.halted (W.run x g (T x.length))

/-- Some witness stream causes acceptance within the given number of steps. -/
def AcceptsInTime (W : WitnessTM k) (x : List Bool) (t : ℕ) : Prop :=
  ∃ g, W.machine.halted (W.run x g t) ∧ (W.run x g t).output.cells 1 = Γ.one

/-- All witness runs halt within `T`, and accepting witnesses characterize `L`. -/
def DecidesInTime (W : WitnessTM k) (L : Language) (T : ℕ → ℕ) : Prop :=
  W.AllWitnessesHaltIn T ∧ ∀ x, x ∈ L ↔ W.AcceptsInTime x (T x.length)

/-- Time and space bounds hold simultaneously. The witness tape is uncharged;
all visible prefixes obey the ordinary NTM decision-space convention. -/
def DecidesInTimeSpace (W : WitnessTM k) (L : Language) (T S : ℕ → ℕ) : Prop :=
  W.DecidesInTime L T ∧ ∀ x g t, t ≤ T x.length →
    (NTM.dropChoice (W.run x g t)).WithinDecisionSpace x.length (S x.length)

/-- A uniformly halting online witness machine with the given space bound. -/
def DecidesInSpace (W : WitnessTM k) (L : Language) (S : ℕ → ℕ) : Prop :=
  ∃ T, W.DecidesInTimeSpace L T S

end WitnessTM

namespace NTM

/-- Run an NTM deterministically by consuming one external witness bit per step.
The charged work tapes and finite control are unchanged. -/
def toWitnessTM (N : NTM k) : WitnessTM k where
  machine := N.choiceTM
  advancing := fun _ => true
  protocol :=
    { write := by intros; simp [choiceTM]
      dir := by intros; simp [choiceTM]
      indep := by intro q _ h; simp at h }

end NTM

end Complexity
