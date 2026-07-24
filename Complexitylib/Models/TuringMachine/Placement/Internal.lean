/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Placement.Defs
import Complexitylib.Models.TuringMachine.Internal
import Complexitylib.Models.TuringMachine.SpaceTime.Internal.Reachability

/-!
# Work-tape placement correctness internals

This file proves exact step and bounded-reachability commutation for
`TM.placeWorkTM`. The strongest one-step theorem evolves an arbitrary physical
extra-tape frame by its prescribed idle action. Stable frames and the canonical
parked frame are fixed points of that action.
-/

namespace Complexity

namespace TM

theorem placeWorkCfg_work_update_internal (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape) (c : Cfg n tm.Q)
    (idx : Fin n) (tape : Tape) :
    Function.update (placeWorkCfg tm pre post extras c).work
        (placeWorkIdx pre post idx) tape =
      (placeWorkCfg tm pre post extras
        { c with work := Function.update c.work idx tape }).work := by
  funext i
  by_cases hphysical : i = placeWorkIdx pre post idx
  · subst i
    simp
  · rw [Function.update_of_ne hphysical]
    by_cases hmiddle : placeWorkInMiddle pre n i
    · dsimp only [placeWorkCfg]
      simp only [hmiddle, dite_true]
      rw [Function.update_of_ne]
      intro hcoord
      apply hphysical
      rw [← hcoord]
      exact (placeWorkIdx_placeWorkCoord i hmiddle).symm
    · rw [placeWorkCfg_work_extra tm pre post extras c i hmiddle]
      rw [placeWorkCfg_work_extra tm pre post extras
        { c with work := Function.update c.work idx tape } i hmiddle]

variable {n pre post : ℕ}

/-- The idle extra-tape action is the identity away from the left-end marker. -/
private theorem placeWorkFrameStep_eq_self_of_read_ne_start (t : Tape)
    (hread : t.read ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read) (idleDir t.read) = t := by
  rw [writeAndMove_readBack t hread]
  simp [idleDir, hread, Tape.move]

/-- A blank tape at head zero or one is sent to the canonical parked blank tape. -/
private theorem placeWorkFrameStep_blank (t : Tape)
    (hcells : t.cells = (Tape.init []).cells) (hhead : t.head ≤ 1) :
    t.writeAndMove (readBackWrite t.read) (idleDir t.read) =
      (Tape.init []).move Dir3.right := by
  have hread : t.read = (Tape.init []).cells t.head := by rw [Tape.read, hcells]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hhead with h0 | h1
  · have ht : t = Tape.init [] := Tape.ext h0 hcells
    subst ht
    rfl
  · have hr : t.read = Γ.blank := by rw [hread, h1]; rfl
    rw [hr]
    show t.write (readBackWrite Γ.blank) = (Tape.init []).move Dir3.right
    rw [Tape.write, if_neg (show ¬t.head = 0 by omega), h1, hcells]
    rw [show (readBackWrite Γ.blank).toΓ = (Tape.init []).cells 1 from rfl,
      Function.update_eq_self]
    rfl

/-- Exact one-step commutation with an arbitrary extra-tape frame. The source
machine takes one step while every physical extra tape takes its idle action. -/
theorem placeWorkTM_step_placeWorkCfg_internal (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape) (c : Cfg n tm.Q) :
    (placeWorkTM pre post tm).step (placeWorkCfg tm pre post extras c) =
      (tm.step c).map
        (placeWorkCfg tm pre post (placeWorkFrameStep extras)) := by
  by_cases hhalt : c.state = tm.qhalt
  · simp [TM.step, placeWorkCfg, placeWorkTM, hhalt]
  · cases hstep : tm.step c with
    | none => exact absurd hstep (by simp [TM.step, hhalt])
    | some c' =>
      simp only [TM.step, hhalt, ↓reduceIte, Option.some.injEq] at hstep
      subst hstep
      have hreads :
          (fun i : Fin n =>
            ((placeWorkCfg tm pre post extras c).work (placeWorkIdx pre post i)).read) =
            (fun i => (c.work i).read) := by
        funext i
        rw [placeWorkCfg_work_middle]
      simp only [TM.step, Option.map_some,
        show (placeWorkCfg tm pre post extras c).state = c.state from rfl,
        show (placeWorkTM pre post tm).qhalt = tm.qhalt from rfl]
      split
      · rename_i heq
        exact (hhalt heq).elim
      · dsimp only [placeWorkTM]
        rw [placeWorkCfg_input, placeWorkCfg_output, hreads]
        refine congrArg some
          (Cfg.mk.injEq _ _ _ _ _ _ _ _ |>.mpr ⟨rfl, rfl, ?_, rfl⟩)
        funext i
        by_cases hmid : placeWorkInMiddle pre n i
        · simp only [hmid, ↓reduceDIte, placeWorkCfg]
        · simp only [hmid, ↓reduceDIte, placeWorkCfg, placeWorkFrameStep]

/-- If every observable extra tape is off the left-end marker, the extra frame
is fixed and one placed step commutes through the same embedding. -/
theorem placeWorkTM_step_placeWorkCfg_stable_internal (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape) (c : Cfg n tm.Q)
    (hextra : ∀ i, ¬placeWorkInMiddle pre n i → (extras i).read ≠ Γ.start) :
    (placeWorkTM pre post tm).step (placeWorkCfg tm pre post extras c) =
      (tm.step c).map (placeWorkCfg tm pre post extras) := by
  rw [placeWorkTM_step_placeWorkCfg_internal]
  cases hstep : tm.step c with
  | none => rfl
  | some c' =>
      simp only [Option.map_some]
      refine congrArg some
        (Cfg.mk.injEq _ _ _ _ _ _ _ _ |>.mpr ⟨rfl, rfl, ?_, rfl⟩)
      funext i
      by_cases hmid : placeWorkInMiddle pre n i
      · simp only [hmid, ↓reduceDIte]
      · simp only [hmid, ↓reduceDIte]
        exact placeWorkFrameStep_eq_self_of_read_ne_start _ (hextra i hmid)

/-- Bounded reachability commutes exactly while a stable arbitrary frame is
preserved around the source work tapes. -/
theorem placeWorkTM_reachesIn_placeWorkCfg_stable_internal (tm : TM n)
    (pre post : ℕ) (extras : Fin (pre + n + post) → Tape)
    {t : ℕ} {c c' : Cfg n tm.Q} (hreach : tm.reachesIn t c c')
    (hextra : ∀ i, ¬placeWorkInMiddle pre n i → (extras i).read ≠ Γ.start) :
    (placeWorkTM pre post tm).reachesIn t
      (placeWorkCfg tm pre post extras c)
      (placeWorkCfg tm pre post extras c') := by
  induction hreach with
  | zero => exact .zero
  | step hstep _ ih =>
    exact .step (by
      rw [placeWorkTM_step_placeWorkCfg_stable_internal tm pre post extras _ hextra,
        hstep]
      rfl) ih

/-- An all-prefix source-space certificate lifts through a stable placement.
The placed source tapes use `sourceSpace`; the preserved surrounding frame
uses `frameSpace`, so the combined machine uses their maximum. -/
theorem placeWorkTM_reachesIn_placeWorkCfg_stable_withinAuxSpace_internal
    (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape)
    {t inputLength sourceSpace frameSpace : ℕ} {c c' : Cfg n tm.Q}
    (hreach : tm.reachesIn t c c')
    (hextra : ∀ i, ¬placeWorkInMiddle pre n i → (extras i).read ≠ Γ.start)
    (hsource : ∀ elapsed cfg, elapsed ≤ t →
      tm.reachesIn elapsed c cfg →
      cfg.WithinAuxSpace inputLength sourceSpace)
    (hframe : ∀ i, ¬placeWorkInMiddle pre n i →
      (extras i).head ≤ frameSpace) :
    (placeWorkTM pre post tm).reachesIn t
        (placeWorkCfg tm pre post extras c)
        (placeWorkCfg tm pre post extras c') ∧
      ∀ elapsed cfg, elapsed ≤ t →
        (placeWorkTM pre post tm).reachesIn elapsed
          (placeWorkCfg tm pre post extras c) cfg →
        cfg.WithinAuxSpace inputLength (max sourceSpace frameSpace) := by
  refine ⟨placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    tm pre post extras hreach hextra, ?_⟩
  intro elapsed cfg helapsed hplaced
  have hlength : elapsed + (t - elapsed) = t :=
    Nat.add_sub_of_le helapsed
  rw [← hlength] at hreach
  obtain ⟨sourceMid, hsourceMid, _hsourceRest⟩ :=
    reachesIn_split_internal hreach
  have hplacedMid := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    tm pre post extras hsourceMid hextra
  have hcfg : cfg = placeWorkCfg tm pre post extras sourceMid :=
    (placeWorkTM pre post tm).reachesIn_right_unique hplaced hplacedMid
  subst cfg
  have hmidBound := hsource elapsed sourceMid helapsed hsourceMid
  constructor
  · intro i
    by_cases hmid : placeWorkInMiddle pre n i
    · let j := placeWorkCoord pre n i hmid
      have hindex : placeWorkIdx pre post j = i :=
        placeWorkIdx_placeWorkCoord i hmid
      rw [← hindex, placeWorkCfg_work_middle]
      exact le_trans (hmidBound.1 j) (le_max_left _ _)
    · rw [placeWorkCfg_work_extra tm pre post extras sourceMid i hmid]
      exact le_trans (hframe i hmid) (le_max_right _ _)
  · exact le_trans hmidBound.2 (by
      have := le_max_left sourceSpace frameSpace
      omega)

/-- The canonical parked frame is fixed by a placed source step. -/
theorem placeWorkTM_step_placeWorkParkedCfg_internal (tm : TM n) (pre post : ℕ)
    (c : Cfg n tm.Q) :
    (placeWorkTM pre post tm).step (placeWorkParkedCfg tm pre post c) =
      (tm.step c).map (placeWorkParkedCfg tm pre post) := by
  apply placeWorkTM_step_placeWorkCfg_stable_internal
  intro i _
  decide

/-- Bounded reachability commutes through the canonical parked embedding. -/
theorem placeWorkTM_reachesIn_placeWorkParkedCfg_internal (tm : TM n)
    (pre post : ℕ) {t : ℕ} {c c' : Cfg n tm.Q}
    (hreach : tm.reachesIn t c c') :
    (placeWorkTM pre post tm).reachesIn t
      (placeWorkParkedCfg tm pre post c)
      (placeWorkParkedCfg tm pre post c') := by
  apply placeWorkTM_reachesIn_placeWorkCfg_stable_internal tm pre post _ hreach
  intro i _
  decide

/-- The first placed step from the ordinary initial configuration performs the
source machine's first step and parks every surrounding blank tape. -/
theorem placeWorkTM_step_initCfg_internal (tm : TM n) (pre post : ℕ)
    (x : List Bool) :
    (placeWorkTM pre post tm).step ((placeWorkTM pre post tm).initCfg x) =
      (tm.step (tm.initCfg x)).map (placeWorkParkedCfg tm pre post) := by
  let initialExtras : Fin (pre + n + post) → Tape := fun _ => Tape.init []
  have hcfg : (placeWorkTM pre post tm).initCfg x =
      placeWorkCfg tm pre post initialExtras (tm.initCfg x) := by
    refine Cfg.mk.injEq _ _ _ _ _ _ _ _ |>.mpr ⟨rfl, rfl, ?_, rfl⟩
    funext i
    by_cases hmid : placeWorkInMiddle pre n i
    · simp only [hmid, ↓reduceDIte]
    · simp only [hmid, ↓reduceDIte, initialExtras]
  rw [hcfg, placeWorkTM_step_placeWorkCfg_internal]
  cases hstep : tm.step (tm.initCfg x) with
  | none => rfl
  | some c =>
      simp only [Option.map_some]
      refine congrArg some
        (Cfg.mk.injEq _ _ _ _ _ _ _ _ |>.mpr ⟨rfl, rfl, ?_, rfl⟩)
      funext i
      by_cases hmid : placeWorkInMiddle pre n i
      · simp only [hmid, ↓reduceDIte]
      · simp only [hmid, ↓reduceDIte]
        exact placeWorkFrameStep_blank _ rfl (Nat.zero_le 1)

/-- Simulation from an ordinary initial configuration. At time zero the placed
configuration is its ordinary initial configuration; every positive run ends
in the canonical parked embedding of the source configuration. -/
theorem placeWorkTM_reachesIn_init_internal (tm : TM n) (pre post : ℕ)
    (x : List Bool) {t : ℕ} {c' : Cfg n tm.Q}
    (hreach : tm.reachesIn t (tm.initCfg x) c') :
    ∃ C' : Cfg (pre + n + post) (placeWorkTM pre post tm).Q,
      (placeWorkTM pre post tm).reachesIn t ((placeWorkTM pre post tm).initCfg x) C' ∧
      C'.state = c'.state ∧ C'.input = c'.input ∧ C'.output = c'.output ∧
      (t = 0 ∨ C' = placeWorkParkedCfg tm pre post c') := by
  cases hreach with
  | zero =>
      exact ⟨(placeWorkTM pre post tm).initCfg x, .zero, rfl, rfl, rfl, Or.inl rfl⟩
  | @step _ cMid _ _ hstep hrest =>
      refine ⟨placeWorkParkedCfg tm pre post c', .step (c'' :=
        placeWorkParkedCfg tm pre post cMid) ?_ ?_, rfl, rfl, rfl, Or.inr rfl⟩
      · rw [placeWorkTM_step_initCfg_internal, hstep]
        rfl
      · exact placeWorkTM_reachesIn_placeWorkParkedCfg_internal tm pre post hrest

/-- Work-tape placement preserves deterministic function computation with the
same time bound. -/
theorem placeWorkTM_computesInTime_internal (tm : TM n) (pre post : ℕ)
    {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : tm.ComputesInTime f T) :
    (placeWorkTM pre post tm).ComputesInTime f T := by
  intro x
  obtain ⟨c', t, ht, hreach, hhalt, hout⟩ := hcomp x
  obtain ⟨C', hreach', hstate, _hinput, houtput, _hshape⟩ :=
    placeWorkTM_reachesIn_init_internal tm pre post x hreach
  refine ⟨C', t, ht, hreach', ?_, ?_⟩
  · show C'.state = (placeWorkTM pre post tm).qhalt
    rw [hstate]
    exact hhalt
  · rw [houtput]
    exact hout

/-- A stable placed frame lifts a source time-and-space Hoare contract without
time overhead and charges only the maximum source/frame space. -/
theorem placeWorkTM_hoareTimeSpace_frame_internal (tm : TM n)
    (pre post : ℕ) (extras : Fin (pre + n + post) → Tape)
    {sourcePre sourcePost : TapePred n}
    {time inputLength sourceSpace frameSpace : ℕ}
    (hsource : tm.HoareTimeSpace sourcePre sourcePost time inputLength
      sourceSpace)
    (hextras : ∀ i, ¬placeWorkInMiddle pre n i →
      (extras i).read ≠ Γ.start)
    (hframe : ∀ i, ¬placeWorkInMiddle pre n i →
      (extras i).head ≤ frameSpace) :
    (placeWorkTM pre post tm).HoareTimeSpace
      (placeWorkPred tm pre post extras sourcePre)
      (placeWorkPred tm pre post extras sourcePost)
      time inputLength (max sourceSpace frameSpace) := by
  constructor
  · rintro inp work out ⟨sourceWork, hpre, rfl⟩
    obtain ⟨done, elapsed, helapsed, hreach, hhalt, hpost⟩ :=
      hsource.1 inp sourceWork out hpre
    let sourceStart : Cfg n tm.Q :=
      { state := tm.qstart,
        input := inp,
        work := sourceWork,
        output := out }
    let placedDone := placeWorkCfg tm pre post extras done
    have hplaced : (placeWorkTM pre post tm).reachesIn elapsed
        (placeWorkCfg tm pre post extras sourceStart) placedDone := by
      exact placeWorkTM_reachesIn_placeWorkCfg_stable_internal tm pre post
        extras hreach hextras
    refine ⟨placedDone, elapsed, helapsed, ?_, ?_, ?_⟩
    · simpa only [sourceStart] using hplaced
    · exact hhalt
    · refine ⟨done.work, ?_, rfl⟩
      simpa only [placedDone, placeWorkCfg_input, placeWorkCfg_output] using
        hpost
  · rintro inp work out ⟨sourceWork, hpre, rfl⟩ current hcurrent
    obtain ⟨done, elapsed, _helapsed, hreach, hhalt, _hpost⟩ :=
      hsource.1 inp sourceWork out hpre
    let sourceStart : Cfg n tm.Q :=
      { state := tm.qstart,
        input := inp,
        work := sourceWork,
        output := out }
    have hsourcePrefix : ∀ steps cfg, steps ≤ elapsed →
        tm.reachesIn steps sourceStart cfg →
        cfg.WithinAuxSpace inputLength sourceSpace := by
      intro steps cfg _hsteps hprefix
      exact hsource.2 inp sourceWork out hpre cfg
        (tm.reaches_of_reachesIn hprefix)
    have hplaced :=
      placeWorkTM_reachesIn_placeWorkCfg_stable_withinAuxSpace_internal
        tm pre post extras hreach hextras hsourcePrefix hframe
    obtain ⟨currentTime, hcurrentRun⟩ :=
      (placeWorkTM pre post tm).reaches_to_reachesIn hcurrent
    have hdoneHalted : (placeWorkTM pre post tm).halted
        (placeWorkCfg tm pre post extras done) :=
      hhalt
    have hcurrentTime : currentTime ≤ elapsed :=
      (placeWorkTM pre post tm).reachesIn_le_halt hcurrentRun hplaced.1
        hdoneHalted
    exact hplaced.2 currentTime current hcurrentTime hcurrentRun

theorem IsTransducer.placeWorkTM_internal {tm : TM n}
    (htrans : tm.IsTransducer) (pre post : ℕ) :
    (placeWorkTM pre post tm).IsTransducer := by
  intro state inputHead workHeads outputHead
  simpa only [placeWorkTM] using htrans state inputHead
    (fun i => workHeads (placeWorkIdx pre post i)) outputHead

end TM

end Complexity
