/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Registers
import Complexitylib.Models.TuringMachine.RetargetOutputFrame.Defs
import Complexitylib.Models.TuringMachine.OutputCursor
import Complexitylib.Models.TuringMachine.SpaceTime.Internal.Reachability

/-!
# Output-retargeting frames -- proof internals
-/

namespace Complexity

namespace TM

@[simp] theorem retargetCfgFrame_state_internal (tm : TM n)
    (cfg : Cfg n tm.Q) (output : Tape) :
    (tm.retargetCfgFrame cfg output).state = cfg.state := rfl

@[simp] theorem retargetCfgFrame_input_internal (tm : TM n)
    (cfg : Cfg n tm.Q) (output : Tape) :
    (tm.retargetCfgFrame cfg output).input = cfg.input := rfl

@[simp] theorem retargetCfgFrame_output_internal (tm : TM n)
    (cfg : Cfg n tm.Q) (output : Tape) :
    (tm.retargetCfgFrame cfg output).output = output := rfl

theorem retargetCfgFrame_work_lt_internal (tm : TM n)
    (cfg : Cfg n tm.Q) (output : Tape) (i : Fin (n + 1))
    (hi : i.val < n) :
    (tm.retargetCfgFrame cfg output).work i = cfg.work ⟨i.val, hi⟩ :=
  dif_pos hi

theorem retargetCfgFrame_work_last_internal (tm : TM n)
    (cfg : Cfg n tm.Q) (output : Tape) :
    (tm.retargetCfgFrame cfg output).work (Fin.last n) = cfg.output :=
  dif_neg (Nat.lt_irrefl n)

theorem retargetOutput_step_retargetCfgFrame_internal (tm : TM n)
    (cfg : Cfg n tm.Q) (output : Tape) (houtput : Parked output) :
    tm.retargetOutput.step (tm.retargetCfgFrame cfg output) =
      (tm.step cfg).map fun next => tm.retargetCfgFrame next output := by
  let framed := tm.retargetCfgFrame cfg output
  change tm.retargetOutput.step framed =
    (tm.step cfg).map fun next => tm.retargetCfgFrame next output
  have hstate : framed.state = cfg.state := rfl
  have hinput : framed.input = cfg.input := rfl
  have hwork : ∀ (i : Fin (n + 1)) (hi : i.val < n),
      framed.work i = cfg.work ⟨i.val, hi⟩ := by
    intro i hi
    exact dif_pos hi
  have hlast : framed.work (Fin.last n) = cfg.output :=
    dif_neg (Nat.lt_irrefl n)
  by_cases hhalt : cfg.state = tm.qhalt
  · have hframed : tm.retargetOutput.step framed = none := by
      simp only [TM.step, hstate, hhalt,
        show tm.retargetOutput.qhalt = tm.qhalt from rfl, ↓reduceIte]
    have hsource : tm.step cfg = none := by
      simp only [TM.step, hhalt, ↓reduceIte]
    rw [hframed, hsource]
    rfl
  · cases hstep : tm.step cfg with
    | none => exact absurd hstep (by simp [TM.step, hhalt])
    | some next =>
      simp only [TM.step, hhalt, ↓reduceIte, Option.some.injEq] at hstep
      subst hstep
      have hworkReads :
          (fun i : Fin n => (framed.work (Fin.castSucc i)).read) =
            fun i => (cfg.work i).read := by
        funext i
        rw [hwork (Fin.castSucc i) i.isLt]
        rfl
      have hvirtualOutput :
          (framed.work (Fin.last n)).read = cfg.output.read := by
        rw [hlast]
      simp only [TM.step, Option.map_some]
      dsimp only [retargetOutput, retargetCfgFrame]
      rw [hstate, hinput, hworkReads, hvirtualOutput, if_neg hhalt]
      refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
      · funext i
        by_cases hi : i.val < n
        · rw [hwork i hi, dif_pos hi, dif_pos hi, dif_pos hi]
        · have hilast : i = Fin.last n := by
            apply Fin.ext
            have := i.isLt
            simp only [Fin.val_last]
            omega
          rw [dif_neg hi, dif_neg hi, dif_neg hi, hilast, hlast]
      · exact houtput.writeAndMove_readBack_idle

theorem retargetOutput_reachesIn_retargetCfgFrame_internal (tm : TM n)
    (output : Tape) (houtput : Parked output) {steps : ℕ}
    {start done : Cfg n tm.Q} (hreach : tm.reachesIn steps start done) :
    tm.retargetOutput.reachesIn steps
      (tm.retargetCfgFrame start output) (tm.retargetCfgFrame done output) := by
  induction hreach with
  | zero => exact .zero
  | step hstep _ ih =>
      exact .step (by
        rw [retargetOutput_step_retargetCfgFrame_internal tm _ output houtput,
          hstep]
        rfl) ih

theorem IsTransducer.retargetOutput_reachesIn_retargetCfgFrame_withinAuxSpace_internal
    {tm : TM n} (htrans : tm.IsTransducer)
    (output : Tape) (houtput : Parked output)
    {steps inputLength space : ℕ} {start done : Cfg n tm.Q}
    (hreach : tm.reachesIn steps start done)
    (hprefix : ∀ elapsed cfg, elapsed ≤ steps →
      tm.reachesIn elapsed start cfg →
      cfg.WithinAuxSpace inputLength space)
    (hdoneOutput : done.output.head ≤ space) :
    tm.retargetOutput.reachesIn steps
        (tm.retargetCfgFrame start output)
        (tm.retargetCfgFrame done output) ∧
      ∀ elapsed cfg, elapsed ≤ steps →
        tm.retargetOutput.reachesIn elapsed
          (tm.retargetCfgFrame start output) cfg →
        cfg.WithinAuxSpace inputLength space := by
  have hframed := retargetOutput_reachesIn_retargetCfgFrame_internal
    tm output houtput hreach
  refine ⟨hframed, ?_⟩
  intro elapsed cfg helapsed hretarget
  let remaining := steps - elapsed
  have htime : elapsed + remaining = steps := by
    dsimp only [remaining]
    omega
  rw [← htime] at hreach
  obtain ⟨sourceMid, hsourceMid, hsourceRest⟩ :=
    reachesIn_split_internal hreach
  have hframedMid := retargetOutput_reachesIn_retargetCfgFrame_internal
    tm output houtput hsourceMid
  have hcfg : cfg = tm.retargetCfgFrame sourceMid output :=
    tm.retargetOutput.reachesIn_right_unique hretarget hframedMid
  subst cfg
  have hsourceSpace := hprefix elapsed sourceMid helapsed hsourceMid
  have hmidOutput : sourceMid.output.head ≤ space :=
    le_trans (htrans.output_head_mono_reachesIn hsourceRest) hdoneOutput
  constructor
  · intro i
    by_cases hi : i.val < n
    · rw [retargetCfgFrame_work_lt_internal tm sourceMid output i hi]
      exact hsourceSpace.1 ⟨i.val, hi⟩
    · have hilast : i = Fin.last n := by
        apply Fin.ext
        have := i.isLt
        simp only [Fin.val_last]
        omega
      subst i
      rw [retargetCfgFrame_work_last_internal]
      exact hmidOutput
  · simpa only [retargetCfgFrame_input_internal] using hsourceSpace.2

theorem retargetOutput_halted_retargetCfgFrame_internal (tm : TM n)
    (cfg : Cfg n tm.Q) (output : Tape) :
    tm.retargetOutput.halted (tm.retargetCfgFrame cfg output) ↔
      tm.halted cfg := by
  rfl

end TM

end Complexity
