/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine

/-!
# Deterministic prefixes of nondeterministic traces

Many NTM constructions (guess-and-verify, deterministic preprocessing before
a nondeterministic phase) run through a *deterministic prefix*: an initial
segment of the computation on which the two transition branches agree. On
that segment the trace is independent of the choice bits and follows an
ordinary DTM run.

The stepping stone is `TM.ReachesInVia`, a run whose step *sources* are
annotated with a predicate. Annotating sources rather than imposing a
step-closed invariant matters: the last prefix step typically exits the
agreeing region (entering the nondeterministic phase), so no step-closed
predicate can describe the prefix. Phase wraps produce annotated runs via
`TM.reachesInVia_of_stepCommute`, and annotated runs concatenate with
`TM.ReachesInVia.trans`.

Main results:

- `NTM.det` — project an NTM onto the DTM that always follows branch `b`.
- `NTM.BranchesAgreeAt`, `NTM.det_step_congr` — pointwise branch agreement,
  under which the projections take the same step.
- `NTM.trace_succ_det` — one non-halted trace step is one step of the
  `det`-projection selected by the current choice bit.
- `NTM.trace_of_det_prefix` — the workhorse: a `det false` run of `t` steps
  whose sources all satisfy `BranchesAgreeAt` lets any length-`(s + t)`
  trace restart from the run's endpoint with the first `t` choices
  discarded.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n m : ℕ}

/-- A DTM run of `t` steps from `c` to `c'` all of whose step *sources*
    satisfy `A`. Unlike a step-closed invariant, this can describe a run
    whose final step leaves the region described by `A`. -/
inductive ReachesInVia (tm : TM n) (A : Cfg n tm.Q → Prop) :
    ℕ → Cfg n tm.Q → Cfg n tm.Q → Prop where
  | zero : ReachesInVia tm A 0 c c
  | step : A c → tm.step c = some c'' → ReachesInVia tm A t c'' c' →
      ReachesInVia tm A (t + 1) c c'

/-- A zero-step annotated run goes nowhere. Inversion form of
    `ReachesInVia.zero`, usable when the machine is a compound expression on
    which `cases` cannot abstract the configuration indices. -/
theorem reachesInVia_zero_iff {tm : TM n} {A : Cfg n tm.Q → Prop}
    {c c' : Cfg n tm.Q} :
    tm.ReachesInVia A 0 c c' ↔ c = c' :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ ReachesInVia.zero⟩

/-- An annotated run of `t + 1` steps factors as one step from an `A`-source
    followed by an annotated run of `t` steps. Inversion form of
    `ReachesInVia.step`. -/
theorem reachesInVia_succ_iff {tm : TM n} {A : Cfg n tm.Q → Prop} {t : ℕ}
    {c c' : Cfg n tm.Q} :
    tm.ReachesInVia A (t + 1) c c' ↔
      A c ∧ ∃ c'', tm.step c = some c'' ∧ tm.ReachesInVia A t c'' c' :=
  ⟨fun h => by cases h with | step hA hstep hrest => exact ⟨hA, _, hstep, hrest⟩,
   fun ⟨hA, _, hstep, hrest⟩ => ReachesInVia.step hA hstep hrest⟩

/-- Forget the source annotations of an annotated run. -/
theorem ReachesInVia.toReachesIn {tm : TM n} {A : Cfg n tm.Q → Prop} {t : ℕ}
    {c c' : Cfg n tm.Q} (h : tm.ReachesInVia A t c c') :
    tm.reachesIn t c c' := by
  induction h with
  | zero => exact .zero
  | step _ hstep _ ih => exact .step hstep ih

/-- Weaken the source annotation of an annotated run. -/
theorem ReachesInVia.mono {tm : TM n} {A B : Cfg n tm.Q → Prop} {t : ℕ}
    {c c' : Cfg n tm.Q} (hAB : ∀ c, A c → B c)
    (h : tm.ReachesInVia A t c c') :
    tm.ReachesInVia B t c c' := by
  induction h with
  | zero => exact .zero
  | step hA hstep _ ih => exact .step (hAB _ hA) hstep ih

/-- Concatenate annotated runs. -/
theorem ReachesInVia.trans {tm : TM n} {A : Cfg n tm.Q → Prop} {t u : ℕ}
    {c c' c'' : Cfg n tm.Q} (h₁ : tm.ReachesInVia A t c c')
    (h₂ : tm.ReachesInVia A u c' c'') :
    tm.ReachesInVia A (t + u) c c'' := by
  induction t generalizing c with
  | zero =>
    obtain rfl := reachesInVia_zero_iff.mp h₁
    simpa using h₂
  | succ t ih =>
    obtain ⟨hA, d, hstep, hrest⟩ := reachesInVia_succ_iff.mp h₁
    simpa [Nat.succ_add] using ReachesInVia.step hA hstep (ih hrest)

/-- Annotate a run with a step-closed invariant that implies the
    annotation. -/
theorem reachesInVia_of_invariant {tm : TM n} {P A : Cfg n tm.Q → Prop}
    (hPA : ∀ c, P c → A c)
    (hpres : ∀ {c c'}, P c → tm.step c = some c' → P c')
    {t : ℕ} {c c' : Cfg n tm.Q} (hreach : tm.reachesIn t c c') (hP : P c) :
    tm.ReachesInVia A t c c' := by
  induction t generalizing c with
  | zero =>
    obtain rfl := reachesIn_zero_iff.mp hreach
    exact .zero
  | succ t ih =>
    obtain ⟨c'', hstep, hrest⟩ := reachesIn_succ_iff.mp hreach
    exact .step (hPA _ hP) hstep (ih hrest (hpres hP hstep))

/-- Transport a run through a step-commuting wrap `w`, annotating every
    source with membership in the image region described by `A`. This is how
    phase embeddings (whose sources all live inside one phase of a composed
    machine) produce annotated runs. -/
theorem reachesInVia_of_stepCommute {tm₁ : TM n} {tm₂ : TM m}
    {A : Cfg m tm₂.Q → Prop} (w : Cfg n tm₁.Q → Cfg m tm₂.Q)
    (hA : ∀ {c c'}, tm₁.step c = some c' → A (w c))
    (hcomm : ∀ {c c'}, tm₁.step c = some c' → tm₂.step (w c) = some (w c'))
    {t : ℕ} {c c' : Cfg n tm₁.Q} (hreach : tm₁.reachesIn t c c') :
    tm₂.ReachesInVia A t (w c) (w c') := by
  induction t generalizing c with
  | zero =>
    obtain rfl := reachesIn_zero_iff.mp hreach
    exact .zero
  | succ t ih =>
    obtain ⟨c'', hstep, hrest⟩ := reachesIn_succ_iff.mp hreach
    exact .step (hA hstep) (hcomm hstep) (ih hrest)

end TM

namespace NTM

variable {n : ℕ}

/-- Project an NTM onto the deterministic machine that always follows
    branch `b`. The projection shares the NTM's state space, so its
    configurations coincide with the NTM's. -/
def det (N : NTM n) (b : Bool) : TM n where
  Q := N.Q
  qstart := N.qstart
  qhalt := N.qhalt
  δ := N.δ b
  δ_right_of_start := N.δ_right_of_start b

/-- The two transition branches of `N` agree at configuration `c` (on the
    symbols actually under the heads). This is the pointwise hypothesis under
    which a trace step is choice-independent. -/
def BranchesAgreeAt (N : NTM n) (c : Cfg n N.Q) : Prop :=
  N.δ true c.state c.input.read (fun i => (c.work i).read) c.output.read =
    N.δ false c.state c.input.read (fun i => (c.work i).read) c.output.read

/-- On a configuration where the branches agree, every `det`-projection takes
    the same step as `det false`. -/
theorem det_step_congr {N : NTM n} {c : Cfg n N.Q}
    (h : N.BranchesAgreeAt c) (b : Bool) :
    (N.det b).step c = (N.det false).step c := by
  cases b
  · rfl
  · simp only [TM.step, det]
    rw [show N.δ true c.state c.input.read (fun i => (c.work i).read)
      c.output.read = _ from h]
    rfl

/-- One non-halted trace step applies the `det`-projection selected by the
    current choice bit. -/
theorem trace_succ_det {N : NTM n} {c : Cfg n N.Q} {T : ℕ}
    (choices : Fin (T + 1) → Bool) (hne : c.state ≠ N.qhalt) :
    N.trace (T + 1) choices c =
      N.trace T (fun i => choices ⟨i.val + 1, by omega⟩)
        (((N.det (choices ⟨0, Nat.zero_lt_succ T⟩)).step c).get
          (by simp [TM.step, det, hne])) := by
  simp [NTM.trace, det, TM.step, hne]

/-- **Deterministic-prefix transport.** A `det false` run of `t` steps whose
    sources all satisfy `BranchesAgreeAt` is followed identically by the
    trace along *any* choice sequence: a length-`(s + t)` trace equals the
    trace of the remaining `s` steps from the run's endpoint with the first
    `t` choices discarded. -/
theorem trace_of_det_prefix {N : NTM n} {t : ℕ} {c c' : Cfg n N.Q}
    (hreach : (N.det false).ReachesInVia N.BranchesAgreeAt t c c')
    (s : ℕ) (choices : Fin (s + t) → Bool) :
    N.trace (s + t) choices c =
      N.trace s (fun i => choices ⟨i.val + t, by omega⟩) c' := by
  induction t generalizing c with
  | zero =>
    obtain rfl := TM.reachesInVia_zero_iff.mp hreach
    rfl
  | succ t ih =>
    obtain ⟨hA, c'', hstep, hrest⟩ := TM.reachesInVia_succ_iff.mp hreach
    have hne := TM.state_ne_qhalt_of_step hstep
    change N.trace ((s + t) + 1) choices c = _
    rw [trace_succ_det (N := N) (T := s + t) (c := c) choices hne]
    have hstep' :=
      (det_step_congr hA (choices ⟨0, Nat.zero_lt_succ (s + t)⟩)).trans hstep
    have hisSome : ((N.det (choices ⟨0, Nat.zero_lt_succ (s + t)⟩)).step c).isSome := by
      rw [hstep']; rfl
    have hget : ((N.det (choices ⟨0, Nat.zero_lt_succ (s + t)⟩)).step c).get hisSome = c'' :=
      Option.some_injective _ ((Option.some_get hisSome).trans hstep')
    rw [hget]
    exact ih hrest _

end NTM

end Complexity
