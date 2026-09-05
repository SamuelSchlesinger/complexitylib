/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Composition.Internal.NondetPrefix
public import Complexitylib.Models.TuringMachine.Placement

/-!
# Placed phase of the nondeterministic composition — proof internals

After the deterministic prefix, `NTM.compositionNTM tmF N` runs the placed
retargeted copy of `N` on the virtual input. This file relates that phase's
composite steps to `N`'s own steps, one choice bit at a time:

- `NTM.placedCfg` — embed an `N`-configuration into the composite's placed
  phase, given a stable frame, a stable ignored real-input tape, and the
  `N`-configuration (whose input tape becomes the virtual input).
- `NTM.placedCfg_step` — branch `b` of the composite steps `placedCfg`
  exactly as `N.det b` steps the underlying configuration.
- `NTM.placedCfg_trace` — the composite's trace from a `placedCfg` is the
  `placedCfg` of `N`'s trace, along any choice sequence.
- `NTM.compositionNTM_seam_step` — from a `DetPrefixBoundary`
  configuration, one branch-`b` step enters the placed phase exactly at
  `N`'s post-first-step configuration on the virtual input (`startedCfg`).
-/


@[expose] public section

namespace Complexity

namespace NTM

variable {nf ng : ℕ}

/-- Embed an `N`-configuration into the composite's placed phase. The
    frame `extras` supplies the tapes outside the placed block, `realInput`
    the ignored real input tape, and `c`'s input tape becomes the virtual
    input on the placed block's last tape. -/
def placedCfg (tmF : TM nf) (N : NTM ng)
    (extras : Fin (TM.compositionTapeCount nf ng) → Tape)
    (realInput : Tape) (c : Cfg ng N.Q) :
    Cfg (TM.compositionTapeCount nf ng) (compositionNTM tmF N).Q :=
  TM.phase2Wrap (TM.compositionFirstTM tmF ng)
    (TM.compositionTailTM nf ng (N.det false))
    (TM.phase2Wrap (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng))
      (TM.seqTM (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
          (TM.compositionVirtualInputIdx nf ng))
        (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
          (TM.compositionSecondTM nf (N.det false))))
      (TM.phase2Wrap (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
          (TM.compositionVirtualInputIdx nf ng))
        (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
          (TM.compositionSecondTM nf (N.det false)))
        (TM.phase2Wrap (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
          (TM.compositionSecondTM nf (N.det false))
          (TM.placeWorkCfg (TM.retargetInputStarted (N.det false))
            (0 + (nf + 1)) 0 extras
            (TM.retargetWrap (N.det false) realInput c)))))

/-- The state of a placed embedding. -/
theorem placedCfg_state (tmF : TM nf) (N : NTM ng)
    (extras : Fin (TM.compositionTapeCount nf ng) → Tape)
    (realInput : Tape) (c : Cfg ng N.Q) :
    (placedCfg tmF N extras realInput c).state =
      Sum.inr (Sum.inr (Sum.inr (Sum.inr c.state))) := rfl

/-- The output tape of a placed embedding is `c`'s output tape. -/
theorem placedCfg_output (tmF : TM nf) (N : NTM ng)
    (extras : Fin (TM.compositionTapeCount nf ng) → Tape)
    (realInput : Tape) (c : Cfg ng N.Q) :
    (placedCfg tmF N extras realInput c).output = c.output := rfl

/-- The composite is halted at a placed embedding iff `N` is halted at the
    underlying configuration. -/
theorem placedCfg_halted_iff (tmF : TM nf) (N : NTM ng)
    (extras : Fin (TM.compositionTapeCount nf ng) → Tape)
    (realInput : Tape) (c : Cfg ng N.Q) :
    (placedCfg tmF N extras realInput c).state = (compositionNTM tmF N).qhalt ↔
      c.state = N.qhalt := by
  constructor
  · intro h
    exact Sum.inr_injective (Sum.inr_injective (Sum.inr_injective
      (Sum.inr_injective h)))
  · intro h
    show Sum.inr (Sum.inr (Sum.inr (Sum.inr c.state))) = _
    rw [h]
    rfl

/-- **Placed-phase step commute.** Branch `b` of the composite steps a
    placed embedding exactly as `N.det b` steps the underlying
    configuration, provided the virtual input is start-invariant, the
    ignored real input reads off `▷`, and the frame tapes are stable. -/
theorem placedCfg_step (tmF : TM nf) (N : NTM ng) (b : Bool)
    {extras : Fin (TM.compositionTapeCount nf ng) → Tape} {realInput : Tape}
    {c c' : Cfg ng N.Q}
    (hstep : (N.det b).step c = some c')
    (hvin : c.input.StartInvariant)
    (hri : realInput.read ≠ Γ.start)
    (hex : ∀ i : Fin (TM.compositionTapeCount nf ng),
      ¬TM.placeWorkInMiddle (0 + (nf + 1)) (ng + 1) (post := 0) i →
        (extras i).read ≠ Γ.start) :
    ((compositionNTM tmF N).det b).step (placedCfg tmF N extras realInput c) =
      some (placedCfg tmF N extras realInput c') := by
  have h1 := TM.retargetInput_step_commute (N.det b) hstep realInput hvin
  have hidle : realInput.move (TM.idleDir realInput.read) = realInput := by
    unfold TM.idleDir
    rw [ite_eq_right hri]
    rfl
  rw [hidle] at h1
  have h3 := TM.placeWorkTM_step_placeWorkCfg_stable
    (TM.retargetInputStarted (N.det b)) (0 + (nf + 1)) 0 extras
    (TM.retargetWrap (N.det b) realInput c) hex
  rw [show (TM.retargetInputStarted (N.det b)).step
      (TM.retargetWrap (N.det b) realInput c) =
      some (TM.retargetWrap (N.det b) realInput c') from h1] at h3
  exact TM.seqTM_phase2_step (TM.compositionFirstTM tmF ng)
    (TM.compositionTailTM nf ng (N.det b))
    (TM.seqTM_phase2_step (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)) _
      (TM.seqTM_phase2_step (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
          (TM.compositionVirtualInputIdx nf ng)) _
        (TM.seqTM_phase2_step (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
          (TM.compositionSecondTM nf (N.det b)) h3)))

/-- **Placed-phase trace correspondence.** Along any choice sequence, the
    composite's trace from a placed embedding is the placed embedding of
    `N`'s trace. -/
theorem placedCfg_trace (tmF : TM nf) (N : NTM ng)
    {extras : Fin (TM.compositionTapeCount nf ng) → Tape} {realInput : Tape}
    (hri : realInput.read ≠ Γ.start)
    (hex : ∀ i : Fin (TM.compositionTapeCount nf ng),
      ¬TM.placeWorkInMiddle (0 + (nf + 1)) (ng + 1) (post := 0) i →
        (extras i).read ≠ Γ.start)
    (s : ℕ) (choices : Fin s → Bool) (c : Cfg ng N.Q)
    (hvin : c.input.StartInvariant) :
    (compositionNTM tmF N).trace s choices (placedCfg tmF N extras realInput c) =
      placedCfg tmF N extras realInput (N.trace s choices c) := by
  have hstep_inv : ∀ {b : Bool} {c c' : Cfg ng N.Q}, (N.det b).step c = some c' →
      c.input.StartInvariant → c'.input.StartInvariant := by
    intro b c c' h hinv
    have hne := TM.state_ne_qhalt_of_step h
    simp only [TM.step, det] at h
    erw [ite_eq_right (show ¬(c.state = N.qhalt) from hne)] at h
    have h' := Option.some_injective _ h
    subst h'
    exact hinv.move _
  induction s generalizing c with
  | zero => rfl
  | succ s ih =>
    by_cases hh : c.state = N.qhalt
    · have hcomp : (compositionNTM tmF N).halted
          (placedCfg tmF N extras realInput c) :=
        (placedCfg_halted_iff tmF N extras realInput c).mpr hh
      rw [(compositionNTM tmF N).trace_halted _ _ hcomp,
        N.trace_halted _ _ hh]
    · obtain ⟨c₀, hstep₀⟩ : ∃ c₀,
          (N.det (choices ⟨0, Nat.zero_lt_succ s⟩)).step c = some c₀ := by
        cases hcase : (N.det (choices ⟨0, Nat.zero_lt_succ s⟩)).step c with
        | none => exact absurd (TM.step_eq_none_iff_halted.mp hcase) hh
        | some d => exact ⟨d, rfl⟩
      have hcompne : (placedCfg tmF N extras realInput c).state ≠
          (compositionNTM tmF N).qhalt :=
        fun h => hh ((placedCfg_halted_iff tmF N extras realInput c).mp h)
      rw [trace_succ_det (N := compositionNTM tmF N) choices hcompne,
        trace_succ_det (N := N) choices hh]
      have hcstep := placedCfg_step tmF N (choices ⟨0, Nat.zero_lt_succ s⟩)
        hstep₀ hvin hri hex
      have hisSome₁ : (((compositionNTM tmF N).det (choices ⟨0, Nat.zero_lt_succ s⟩)).step
          (placedCfg tmF N extras realInput c)).isSome := by
        rw [hcstep]; rfl
      have hget₁ : (((compositionNTM tmF N).det (choices ⟨0, Nat.zero_lt_succ s⟩)).step
          (placedCfg tmF N extras realInput c)).get hisSome₁ =
          placedCfg tmF N extras realInput c₀ :=
        Option.some_injective _ ((Option.some_get hisSome₁).trans hcstep)
      have hisSome₂ : ((N.det (choices ⟨0, Nat.zero_lt_succ s⟩)).step c).isSome := by
        rw [hstep₀]; rfl
      have hget₂ : ((N.det (choices ⟨0, Nat.zero_lt_succ s⟩)).step c).get hisSome₂ = c₀ :=
        Option.some_injective _ ((Option.some_get hisSome₂).trans hstep₀)
      rw [hget₁, hget₂]
      exact ih _ c₀ (hstep_inv hstep₀ hvin)

/-- **The seam into the placed phase.** From a `DetPrefixBoundary`
    configuration, one branch-`b` composite step enters the placed phase at
    `N`'s post-first-step configuration on the virtual input `y`, with the
    boundary's own tapes as frame and real input. -/
theorem compositionNTM_seam_step (tmF : TM nf) (N : NTM ng) (b : Bool)
    {y : List Bool}
    {E : Cfg (TM.compositionTapeCount nf ng) (compositionNTM tmF N).Q}
    (hB : DetPrefixBoundary tmF N y E) (hne : (N.det b).qstart ≠ (N.det b).qhalt) :
    ((compositionNTM tmF N).det b).step E =
      some (placedCfg tmF N E.work E.input
        (TM.startedCfg (N.det b) y hne)) := by
  obtain ⟨hstate, hvinE, hscratchE, houtE, hinpInv, hinpHead, hstable⟩ := hB
  have hread_ns : ∀ t : Tape, t.StartInvariant → 1 ≤ t.head → t.read ≠ Γ.start :=
    fun t hinv hh => hinv.2 t.head hh
  -- The started state matches the placed machine's start state.
  have hstateEq : (TM.compositionSecondTM nf (N.det b)).qstart =
      (TM.startedCfg (N.det b) y hne).state := by
    show (if (N.det b).qstart = (N.det b).qhalt then (N.det b).qhalt
        else TM.retargetInputStartState (N.det b)) = _
    rw [ite_eq_right hne]
    simp [TM.retargetInputStartState, TM.startedCfg, TM.step, hne,
      Tape.read, Tape.init]
  -- Tape transitions at the seam are identities on the stable boundary tapes.
  have hinpTr : TM.transitionInput E.input = E.input :=
    TM.transitionInput_eq_self (hread_ns _ hinpInv hinpHead)
  have houtTr : TM.transitionTape E.output = E.output := by
    rw [houtE]
    exact TM.transitionTape_eq_self (by
      rw [← houtE]
      exact hread_ns _ (houtE ▸ Tape.StartInvariant.init_nil.move Dir3.right)
        (by rw [houtE]; simp [Tape.move]))
  have hworkTr : ∀ i, TM.transitionTape (E.work i) = E.work i := fun i =>
    TM.transitionTape_eq_self (hread_ns _ (hstable i).1 (hstable i).2)
  -- One lifted transition step into the placed phase.
  have htrans := TM.seqTM_transition_step
    (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
    (TM.compositionSecondTM nf (N.det b))
    (c₁ := { state := (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)).qhalt,
             input := E.input, work := E.work, output := E.output }) rfl
  have hlift : ((compositionNTM tmF N).det b).step E =
      some (TM.phase2Wrap (TM.compositionFirstTM tmF ng)
        (TM.compositionTailTM nf ng (N.det b))
        (TM.phase2Wrap (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng))
          (TM.seqTM (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
              (TM.compositionVirtualInputIdx nf ng))
            (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
              (TM.compositionSecondTM nf (N.det b))))
          (TM.phase2Wrap (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
              (TM.compositionVirtualInputIdx nf ng))
            (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
              (TM.compositionSecondTM nf (N.det b)))
            (TM.phase2Wrap (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
              (TM.compositionSecondTM nf (N.det b))
              { state := (TM.compositionSecondTM nf (N.det b)).qstart,
                input := TM.transitionInput E.input,
                work := fun i => TM.transitionTape (E.work i),
                output := TM.transitionTape E.output })))) := by
    have hE : E = TM.phase2Wrap (TM.compositionFirstTM tmF ng)
        (TM.compositionTailTM nf ng (N.det b))
        (TM.phase2Wrap (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng))
          (TM.seqTM (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
              (TM.compositionVirtualInputIdx nf ng))
            (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
              (TM.compositionSecondTM nf (N.det b))))
          (TM.phase2Wrap (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
              (TM.compositionVirtualInputIdx nf ng))
            (TM.seqTM (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
              (TM.compositionSecondTM nf (N.det b)))
            (TM.phase1Wrap (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng))
              (TM.compositionSecondTM nf (N.det b))
              { state := (TM.rewindWorkTM (TM.compositionVirtualInputIdx nf ng)).qhalt,
                input := E.input, work := E.work, output := E.output }))) := by
      obtain ⟨st, Ei, Ew, Eo⟩ := E
      simp only at hstate
      subst hstate
      rfl
    rw [hE]
    exact TM.seqTM_phase2_step (TM.compositionFirstTM tmF ng)
      (TM.compositionTailTM nf ng (N.det b))
      (TM.seqTM_phase2_step (TM.rewindWorkTM (TM.compositionRawOutputIdx nf ng)) _
        (TM.seqTM_phase2_step (TM.copyWorkToWorkTM (TM.compositionRawOutputIdx nf ng)
            (TM.compositionVirtualInputIdx nf ng)) _ htrans))
  refine hlift.trans (congrArg some (Cfg.ext ?_ ?_ ?_ ?_))
  · -- State: the placed start state is the started state.
    show Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (TM.compositionSecondTM nf (N.det b)).qstart))) =
      Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (TM.startedCfg (N.det b) y hne).state)))
    rw [hstateEq]
    rfl
  · -- Input: the real input idles through the seam.
    exact hinpTr
  · -- Work tapes.
    funext i
    show TM.transitionTape (E.work i) = _
    rw [hworkTr i]
    by_cases hmid : TM.placeWorkInMiddle (0 + (nf + 1)) (ng + 1) (post := 0) i
    · show E.work i =
        if h : TM.placeWorkInMiddle (0 + (nf + 1)) (ng + 1) (post := 0) i then
          (TM.retargetWrap (N.det false) E.input
            (TM.startedCfg (N.det b) y hne)).work
              (TM.placeWorkCoord (0 + (nf + 1)) (ng + 1) (post := 0) i h)
        else E.work i
      rw [dite_eq_left hmid]
      by_cases hlt : (TM.placeWorkCoord (0 + (nf + 1)) (ng + 1) (post := 0) i hmid).val < ng
      · erw [TM.retargetWrap_work_lt _ _ _ _ hlt,
          TM.startedCfg_work_eq_init_move_right]
        have hidx : TM.compositionSecondWorkIdx nf ng
            ⟨(TM.placeWorkCoord (0 + (nf + 1)) (ng + 1) (post := 0) i hmid).val, hlt⟩ = i := by
          apply Fin.ext
          simp only [TM.compositionSecondWorkIdx_val, TM.placeWorkCoord]
          obtain ⟨hlo, hhi⟩ := hmid
          omega
        rw [← hidx]
        exact hscratchE _
      · show E.work i = (TM.retargetWrap (N.det false) E.input
            (TM.startedCfg (N.det b) y hne)).work _
        rw [show (TM.retargetWrap (N.det false) E.input
            (TM.startedCfg (N.det b) y hne)).work
              (TM.placeWorkCoord (0 + (nf + 1)) (ng + 1) (post := 0) i hmid) =
          (TM.startedCfg (N.det b) y hne).input by
            show (if h : (TM.placeWorkCoord (0 + (nf + 1)) (ng + 1) (post := 0) i hmid).val < ng
              then _ else _) = _
            rw [dite_eq_right hlt],
          TM.startedCfg_input_eq]
        have hidx : i = TM.compositionVirtualInputIdx nf ng := by
          apply Fin.ext
          obtain ⟨hlo, hhi⟩ := hmid
          have := i.isLt
          simp only [TM.compositionVirtualInputIdx_val]
          simp only [TM.placeWorkCoord] at hlt
          omega
        rw [hidx]
        exact hvinE
    · show E.work i =
        if h : TM.placeWorkInMiddle (0 + (nf + 1)) (ng + 1) (post := 0) i then
          (TM.retargetWrap (N.det false) E.input
            (TM.startedCfg (N.det b) y hne)).work
              (TM.placeWorkCoord (0 + (nf + 1)) (ng + 1) (post := 0) i h)
        else E.work i
      rw [dite_eq_right hmid]
  · -- Output: parked blank on both sides.
    show TM.transitionTape E.output = (TM.startedCfg (N.det b) y hne).output
    rw [houtTr, houtE, TM.startedCfg_output_eq_init_move_right]

end NTM

end Complexity
