/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Hoare.Safety
public import Complexitylib.Models.TuringMachine.GuessAssembly

/-!
# Safety of witness-independent phases

Appending the distinguished witness tape to an ordinary phase preserves every
safety property of its visible tapes. In particular, decision-space bounds keep
charging output while ignoring the external stream's unbounded cursor.
-/

public section

namespace Complexity
namespace TM

/-- One lifted transition projects to the original deterministic transition. -/
private theorem dropChoice_liftLast_step (D : TM k)
    {c c' : Cfg (k + 1) D.Q} (h : (liftLast D).step c = some c') :
    D.step (NTM.dropChoice c) = some (NTM.dropChoice c') := by
  have hne : c.state ≠ D.qhalt := state_ne_qhalt_of_step h
  have hc : (liftLast D).stepCfg c = c' := by
    rw [step_of_not_halted (liftLast D) hne] at h
    exact Option.some.inj h
  subst c'
  rw [step_of_not_halted D hne]
  apply congrArg some
  simp [stepCfg, NTM.dropChoice, liftLast]

/-- Every reachable configuration of a lifted phase projects to one of the
original phase, independently of the contents or position of the added tape. -/
theorem liftLast_reaches_project (D : TM k) {c c' : Cfg (k + 1) D.Q}
    (h : (liftLast D).reaches c c') : D.reaches (NTM.dropChoice c) (NTM.dropChoice c') :=
  Relation.ReflTransGen.lift (r := (liftLast D).stepRel) (p := D.stepRel)
    (fun d : Cfg (k + 1) D.Q => NTM.dropChoice d)
    (fun _ _ hs => dropChoice_liftLast_step D hs) c c' h

/-- Lift ordinary phase safety without charging the added external tape. -/
theorem liftLast_hoareSafety (D : TM k) {pre safe : TapePred k}
    (h : D.HoareSafety pre safe) :
    (liftLast D).HoareSafety
      (fun inp work out => pre inp (fun i => work i.castSucc) out)
      (fun inp work out => safe inp (fun i => work i.castSucc) out) := by
  intro inp work out hp c hc
  exact h inp (fun i => work i.castSucc) out hp (NTM.dropChoice c)
    (liftLast_reaches_project D hc)

/-- A terminating phase has a conservative projected decision-space bound.
Only the ordinary tapes contribute; the final external tape may travel freely. -/
theorem HoareTime.projectedSafety {M : TM (k + 1)}
    {pre post : TapePred (k + 1)} {time inputLength initialSpace : ℕ}
    (h : M.HoareTime pre post time)
    (hinit : ∀ inp work out, pre inp work out →
      (⟨(), inp, (fun i => work i.castSucc), out⟩ : Cfg k Unit).WithinDecisionSpace
        inputLength initialSpace) :
    M.HoareSafety pre
      (fun inp work out =>
        (⟨(), inp, (fun i => work i.castSucc), out⟩ : Cfg k Unit).WithinDecisionSpace
          inputLength (initialSpace + time)) := by
  intro inp work out hp c hc
  obtain ⟨d, haltTime, htime, hr, hh, _⟩ := h inp work out hp
  obtain ⟨t, ht⟩ := M.reaches_to_reachesIn hc
  have hle : t ≤ haltTime := M.reachesIn_le_halt ht hr hh
  have hi := hinit inp work out hp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro j
    have hb := M.work_head_reachesIn_bound ht j.castSucc
    have hj := hi.1.1 j
    dsimp only at hb hj ⊢
    omega
  · have hb := M.input_head_reachesIn_bound ht
    have hj := hi.1.2
    dsimp only at hb hj ⊢
    omega
  · have hb := M.output_head_reachesIn_bound ht
    have hj := hi.2
    dsimp only at hb hj ⊢
    omega

end TM
end Complexity
