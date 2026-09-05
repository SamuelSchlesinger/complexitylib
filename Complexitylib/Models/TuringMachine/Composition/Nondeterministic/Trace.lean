/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Composition.Nondeterministic
public import Complexitylib.Models.TuringMachine.Composition.Internal.NondetPrefix
public import Complexitylib.Models.TuringMachine.Composition.Internal.NondetPlaced

/-!
# Trace factorization through the deterministic prefix

Every trace of `NTM.compositionNTM tmF N` — along *any* choice sequence —
first runs the deterministic pipeline (first computation, output rewind,
copy, virtual-input rewind) without consulting a single choice bit. The
trace therefore factors through the `DetPrefixBoundary` configuration in
which the virtual input holds `f x`, after which only the placed
retargeted copy of `N` runs.

The choice-independence is packaged by `NTM.compositionNTM_trace_prefix`:
the length-`(s + t)` trace equals the length-`s` trace restarted from the
boundary with the first `t` choices discarded.
-/


public section

namespace Complexity

namespace NTM

variable {nf ng : ℕ}

/-- **Trace factorization through the deterministic prefix.** There is a
    boundary configuration `E` (holding `f x` on the virtual-input tape)
    and a prefix length `t ≤ 4 * TF |x| + 10` such that every trace of the
    composite factors through `E`, with the first `t` choice bits ignored. -/
theorem compositionNTM_trace_prefix (tmF : TM nf) (N : NTM ng)
    {f : List Bool → List Bool} {TF : ℕ → ℕ}
    (hF : tmF.ComputesInTime f TF) (x : List Bool) :
    ∃ (E : Cfg (TM.compositionTapeCount nf ng) (compositionNTM tmF N).Q) (t : ℕ),
      t ≤ 4 * TF x.length + 10 ∧
      DetPrefixBoundary tmF N (f x) E ∧
      ∀ (s : ℕ) (choices : Fin (s + t) → Bool),
        (compositionNTM tmF N).trace (s + t) choices
            ((compositionNTM tmF N).initCfg x) =
          (compositionNTM tmF N).trace s
            (fun i => choices ⟨i.val + t, by omega⟩) E := by
  obtain ⟨E, t, ht, hvia, hboundary⟩ :=
    compositionNTM_detPrefix_internal tmF N hF x
  exact ⟨E, t, ht, hboundary, fun s choices => trace_of_det_prefix hvia s choices⟩

/-- **Full trace correspondence.** For a machine `N` that does not start
    halted, every composite trace of length `(s + 1) + t` is the placed
    embedding of `N`'s own length-`(s + 1)` trace on the virtual input
    `f x`: the seam step out of the prefix boundary is `N`'s first traced
    step, and thereafter the composite follows `N` bit for bit. -/
theorem compositionNTM_trace_run (tmF : TM nf) (N : NTM ng)
    {f : List Bool → List Bool} {TF : ℕ → ℕ}
    (hF : tmF.ComputesInTime f TF) (x : List Bool)
    (hne : N.qstart ≠ N.qhalt) :
    ∃ (E : Cfg (TM.compositionTapeCount nf ng) (compositionNTM tmF N).Q) (t : ℕ),
      t ≤ 4 * TF x.length + 10 ∧
      DetPrefixBoundary tmF N (f x) E ∧
      ∀ (s : ℕ) (choices : Fin ((s + 1) + t) → Bool),
        (compositionNTM tmF N).trace ((s + 1) + t) choices
            ((compositionNTM tmF N).initCfg x) =
          placedCfg tmF N E.work E.input
            (N.trace (s + 1) (fun i => choices ⟨i.val + t, by omega⟩)
              (N.initCfg (f x))) := by
  obtain ⟨E, t, ht, hB, hfactor⟩ := compositionNTM_trace_prefix tmF N hF x
  refine ⟨E, t, ht, hB, fun s choices => ?_⟩
  obtain ⟨hstate, hvinE, hscratchE, houtE, hinpInv, hinpHead, hstable⟩ := hB
  -- The boundary is not composite-halted: its state is a left injection
  -- inside the tail, while the composite halt state is a right injection.
  have hEne : E.state ≠ (compositionNTM tmF N).qhalt := by
    rw [hstate]
    exact fun h => Sum.inl_ne_inr
      (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective h)))
  -- Factor through the prefix, then take the seam step on both sides.
  rw [hfactor (s + 1) choices]
  set choices' : Fin (s + 1) → Bool := fun i => choices ⟨i.val + t, by omega⟩
    with hchoices'
  have hbne : (N.det (choices' ⟨0, Nat.zero_lt_succ s⟩)).qstart ≠
      (N.det (choices' ⟨0, Nat.zero_lt_succ s⟩)).qhalt := hne
  have hseam := compositionNTM_seam_step tmF N (choices' ⟨0, Nat.zero_lt_succ s⟩)
    ⟨hstate, hvinE, hscratchE, houtE, hinpInv, hinpHead, hstable⟩ hbne
  rw [trace_succ_det (N := compositionNTM tmF N) choices' hEne]
  have hisSome₁ : (((compositionNTM tmF N).det
      (choices' ⟨0, Nat.zero_lt_succ s⟩)).step E).isSome := by
    rw [hseam]; rfl
  have hget₁ : (((compositionNTM tmF N).det
      (choices' ⟨0, Nat.zero_lt_succ s⟩)).step E).get hisSome₁ =
      placedCfg tmF N E.work E.input
        (TM.startedCfg (N.det (choices' ⟨0, Nat.zero_lt_succ s⟩)) (f x) hbne) :=
    Option.some_injective _ ((Option.some_get hisSome₁).trans hseam)
  rw [hget₁]
  -- The remaining steps follow `N` bit for bit.
  have hread_ns : ∀ tp : Tape, tp.StartInvariant → 1 ≤ tp.head →
      tp.read ≠ Γ.start := fun tp hinv hh => hinv.2 tp.head hh
  erw [placedCfg_trace tmF N (hread_ns _ hinpInv hinpHead)
    (fun i hi => hread_ns _ (hstable i).1 (hstable i).2) s _ _
    (by
      rw [TM.startedCfg_input_eq]
      exact (Tape.StartInvariant.init_ofBool (f x)).move Dir3.right)]
  -- On `N`'s side, the first traced step is exactly the started step.
  have hNstep := TM.step_initCfg_startedCfg (N.det (choices' ⟨0, Nat.zero_lt_succ s⟩))
    (f x) hbne
  rw [trace_succ_det (N := N) choices' (show (N.initCfg (f x)).state ≠ N.qhalt from hne)]
  have hisSome₂ : ((N.det (choices' ⟨0, Nat.zero_lt_succ s⟩)).step
      (N.initCfg (f x))).isSome := by
    rw [show (N.det (choices' ⟨0, Nat.zero_lt_succ s⟩)).step (N.initCfg (f x)) =
      some (TM.startedCfg (N.det (choices' ⟨0, Nat.zero_lt_succ s⟩)) (f x) hbne)
      from hNstep]
    rfl
  have hget₂ : ((N.det (choices' ⟨0, Nat.zero_lt_succ s⟩)).step
      (N.initCfg (f x))).get hisSome₂ =
      TM.startedCfg (N.det (choices' ⟨0, Nat.zero_lt_succ s⟩)) (f x) hbne :=
    Option.some_injective _ ((Option.some_get hisSome₂).trans hNstep)
  rw [hget₂]

end NTM

end Complexity
