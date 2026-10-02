/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
public import Complexitylib.Models.TuringMachine.Lift.Hoare
public import Complexitylib.Models.TuringMachine.Placement.Window
public import Complexitylib.Models.TuringMachine.Combinators.RetargetCompute
public import Complexitylib.Models.TuringMachine.Combinators.ApplyDecide

/-!
# Exact tape-layout transport regression examples

Run with `lake build --wfail TapeTransportCheck`.
The kernel checks zero-work-tape machines, empty layouts, initial marker bounces,
halted/time-zero configurations, nonblank parked frames, arbitrary evolving frames,
virtual-input invariants, exact output routing, and reflection of every reachable prefix.
The generic lifting API is available without importing any UTM module.
-/

namespace Complexity
namespace TapeTransportCheck

private abbrev tick : TM 0 where
  Q := Bool
  qstart := false
  qhalt := true
  δ := fun _ inp work out => TM.allReadBack true inp work out
  δ_right_of_start := fun _ inp work out => TM.rightOfStart_allReadBack inp work out

private def afterTick : Cfg 0 Bool :=
  ⟨true, (Tape.init []).move .right, fun _ => (Tape.init []).move .right,
    (Tape.init []).move .right⟩

private theorem tick_step : tick.step (tick.initCfg []) = some afterTick := by
  rfl

private theorem tick_run : tick.reachesIn 1 (tick.initCfg []) afterTick :=
  .step tick_step .zero

-- No source work tapes, no added work tapes, and zero-length prefix/suffix layouts.
example : (tick.liftTM 0).reachesIn 1 ((tick.liftTM 0).initCfg [])
    (tick.liftCfg 0 afterTick) :=
  TM.liftTM_reachesIn_initCfg_of_pos tick 0 [] (by decide) tick_run

example : (TM.placeWorkTM 0 0 tick).reachesIn 1
    ((TM.placeWorkTM 0 0 tick).initCfg []) (TM.placeWorkParkedCfg tick 0 0 afterTick) := by
  obtain ⟨D, hD, _, _, _, hshape⟩ := TM.placeWorkTM_reachesIn_init tick 0 0 [] tick_run
  rcases hshape with hzero | rfl
  · cases hzero
  · exact hD

-- The extra tape bounces during the one source step; there is no additional tick.
example : (tick.liftTM 1).reachesIn 1 ((tick.liftTM 1).initCfg [])
    (tick.liftCfg 1 afterTick) :=
  TM.liftTM_reachesIn_initCfg_of_pos tick 1 [] (by decide) tick_run

example : (((tick.liftTM 1).initCfg []).work 0).head = 0 ∧
    ((tick.liftCfg 1 (tick.initCfg [])).work 0).head = 1 := by
  exact ⟨rfl, rfl⟩

example : (tick.liftTM 1).reachesIn 0 ((tick.liftTM 1).initCfg [])
    ((tick.liftTM 1).initCfg []) := .zero

-- A halted source and its lifted/placed embeddings have no next step.
example : (tick.liftTM 1).step (tick.liftCfg 1 afterTick) = none := by
  rw [TM.liftTM_step_liftCfg]
  rfl

example : (TM.placeWorkTM 1 0 tick).step (TM.placeWorkParkedCfg tick 1 0 afterTick) =
    none := by
  rw [TM.placeWorkTM_step_placeWorkParkedCfg]
  rfl

private def nonblank : Tape := (Tape.init [Γ.one, Γ.zero]).move .right

-- Stable frames can contain data; preserving them includes the whole tape, not just its head.
example : (tick.liftTM 1).step (TM.liftCfgWith tick 1 (fun _ => nonblank) (tick.initCfg [])) =
    some (TM.liftCfgWith tick 1 (fun _ => nonblank) afterTick) := by
  rw [TM.liftTM_step_liftCfgWith tick 1 (fun _ => by decide), tick_step]
  rfl

example : (TM.placeWorkTM 1 1 tick).reachesIn 1
    (TM.placeWorkCfg tick 1 1 (fun _ => nonblank) (tick.initCfg []))
    (TM.placeWorkCfg tick 1 1 (fun _ => nonblank) afterTick) :=
  TM.placeWorkTM_reachesIn_placeWorkCfg_stable tick 1 1 (fun _ => nonblank) tick_run
    (fun _ _ => by decide)

-- The arbitrary-frame theorem does not silently assume StartInvariant or a stable frame.
private def markerFrame : Tape := ⟨2, fun _ => Γ.start⟩

example : ((tick.liftTM 1).step
    (TM.liftCfgWith tick 1 (fun _ => markerFrame) (tick.initCfg []))).map
      (fun c => ((c.work 0).head, (c.work 0).cells 2)) = some (3, Γ.blank) := by
  rfl

-- Even an evolving frame is not advanced after the source has halted.
example : (tick.liftTM 1).step
    (TM.liftCfgWith tick 1 (fun _ => markerFrame) afterTick) = none := by
  rw [TM.liftTM_step_liftCfgWith_frame]
  rfl

-- Non-marker stability does not secretly require well-formed cells or a positive head.
private def nonmarkerAtZero : Tape := ⟨0, fun _ => Γ.one⟩

example : (tick.liftTM 1).step
    (TM.liftCfgWith tick 1 (fun _ => nonmarkerAtZero) (tick.initCfg [])) =
      some (TM.liftCfgWith tick 1 (fun _ => nonmarkerAtZero) afterTick) := by
  rw [TM.liftTM_step_liftCfgWith tick 1 (fun _ => by decide), tick_step]
  rfl

-- The output-retargeting boundary preserves the exact virtual output tape.
example : tick.retargetOutput.reachesIn 1
    (tick.retargetCfg (tick.initCfg [])) (tick.retargetCfg afterTick) :=
  TM.retargetOutput_reachesIn_retargetCfg_frame tick tick_run

example : (tick.retargetCfg afterTick).work (Fin.last 0) = afterTick.output :=
  TM.retargetCfg_work_last tick afterTick

-- Virtual-input transport continues to require its explicit marker invariant.
example {k : ℕ} (M : TM k) {c c' : Cfg k M.Q} (hstep : M.step c = some c')
    (realInput : Tape) (hinp : Tape.StartInvariant c.input) :
    (TM.retargetInput M).step (TM.retargetWrap M realInput c) =
      some (TM.retargetWrap M (realInput.move (TM.idleDir realInput.read)) c') :=
  TM.retargetInput_step_commute M hstep realInput hinp

-- Every reachable prefix is reflected, including time zero and early halted endpoints.
example {n m : ℕ} (M : TM n) (extras : Fin m → Tape)
    (hex : ∀ j, (extras j).read ≠ Γ.start) (c₀ : Cfg n M.Q)
    (D : Cfg (n + m) M.Q)
    (hD : (M.liftTM m).reaches (TM.liftCfgWith M m extras c₀) D) :
    ∃ c, M.reaches c₀ c ∧ D = TM.liftCfgWith M m extras c :=
  TM.reaches_map_reflect (tm' := M.liftTM m) (TM.liftCfgWith M m extras)
    (TM.liftTM_step_liftCfgWith M m hex) c₀ D hD

private abbrev stopped : TM 0 where
  Q := Unit
  qstart := ()
  qhalt := ()
  δ := fun _ inp work out => TM.allReadBack () inp work out
  δ_right_of_start := fun _ inp work out => TM.rightOfStart_allReadBack inp work out

-- A constant (noninjective) map is permitted; the source already halts at time zero.
example (c₀ D : Cfg 0 Unit) (hD : stopped.reaches (stopped.initCfg []) D) :
    ∃ c, stopped.reaches c₀ c ∧ D = stopped.initCfg [] :=
  TM.reaches_map_reflect (tm := stopped) (tm' := stopped)
    (fun _ => stopped.initCfg [])
    (fun c => by
      have hc : c.state = stopped.qhalt := Subsingleton.elim _ _
      simp [TM.step, hc, stopped]) c₀ D hD

-- Successful-step transport remains weaker than halt-reflecting transport.
example {n n' : ℕ} (M : TM n) (N : TM n') (wrap : Cfg n M.Q → Cfg n' N.Q)
    (hstep : ∀ c c', M.step c = some c' → N.step (wrap c) = some (wrap c'))
    {t : ℕ} {c c' : Cfg n M.Q} (hrun : M.reachesIn t c c') :
    N.reachesIn t (wrap c) (wrap c') :=
  TM.reachesIn_map' wrap hstep hrun

-- Exact retarget-input transport permits arbitrary real-input frames, even malformed ones.
example : ∃ r, (TM.retargetInput tick).reachesIn 1
    (TM.retargetWrap tick markerFrame (tick.initCfg [])) (TM.retargetWrap tick r afterTick) :=
  TM.retargetInput_reachesIn_of_reachesIn tick tick_run Tape.StartInvariant.init_nil
    (fun _ => Tape.StartInvariant.init_nil) Tape.StartInvariant.init_nil markerFrame

example : ((TM.retargetInput tick).step
    (TM.retargetWrap tick markerFrame (tick.initCfg []))).map
      (fun c => c.input.head) = some 3 := by
  rfl

example : ((TM.retargetInput tick).step
    (TM.retargetWrap tick nonmarkerAtZero (tick.initCfg []))).map
      (fun c => c.input.head) = some 0 := by
  rfl

-- Time zero does not advance the real-input frame, including an already-halted source.
example : (TM.retargetInput stopped).reachesIn 0
    (TM.retargetWrap stopped markerFrame (stopped.initCfg []))
    (TM.retargetWrap stopped markerFrame (stopped.initCfg [])) := .zero

example : (TM.retargetInput stopped).step
    (TM.retargetWrap stopped markerFrame (stopped.initCfg [])) = none := by
  rfl

-- The virtual-input invariant is essential: a misplaced marker is rewritten on a work tape,
-- whereas the source's read-only input keeps that same cell unchanged.
private def badVirtual : Cfg 0 Bool :=
  ⟨false, markerFrame, fun _ => Tape.init [], Tape.init []⟩

example : (tick.step badVirtual).map (fun c => c.input.cells 2) = some Γ.start := by
  rfl

example : ((TM.retargetInput tick).step
    (TM.retargetWrap tick (Tape.init []) badVirtual)).map
      (fun c => (c.work (Fin.last 0)).cells 2) = some Γ.blank := by
  rfl

private theorem tick_window (c : Cfg 0 Bool) (hc : tick.reaches (tick.initCfg []) c) :
    c.WithinDecisionSpace 0 1 := by
  obtain ⟨t, ht⟩ := tick.reaches_to_reachesIn hc
  have htime : t ≤ 1 := tick.reachesIn_le_halt ht tick_run rfl
  refine ⟨⟨fun i => Fin.elim0 i, ?_⟩, ?_⟩
  · have hi := tick.input_head_reachesIn_bound ht
    change c.input.head ≤ 0 + t at hi
    omega
  · have ho := tick.output_head_reachesIn_bound ht
    change c.output.head ≤ 0 + t at ho
    omega

-- Every prefix is charged correctly, including head-zero entry and positive real-input heads.
-- The relocated source input costs m + s + 1 = 2; the real input retains its max-head bound.
example (r : Tape) (hrsi : Tape.StartInvariant r) (hr : max r.head 1 ≤ 3) :
    ∀ D, (TM.retargetInput tick).reaches (TM.retargetWrap tick r (tick.initCfg [])) D →
      D.WithinDecisionSpace 0 2 :=
  TM.retargetInput_keepsWindow_of_reaches tick r (tick.initCfg []) tick_window
    Tape.StartInvariant.init_nil (fun _ => Tape.StartInvariant.init_nil)
    Tape.StartInvariant.init_nil hrsi (by decide) hr

-- The started wrapper keeps the same reachability, even when its start state differs.
example {k : ℕ} (M : TM k) (c d : Cfg (k + 1) M.Q) :
    (TM.retargetInputStarted M).reaches c d ↔ (TM.retargetInput M).reaches c d :=
  TM.retargetInputStarted_reaches_iff M c d

end TapeTransportCheck
end Complexity
