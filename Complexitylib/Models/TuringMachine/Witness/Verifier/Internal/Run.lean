/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Combinators.ApplyDecide
public import Complexitylib.Models.TuringMachine.Hoare.Safety.Defs
public import Complexitylib.Models.TuringMachine.Placement.Window

/-!
# Ordinary verifier phase resource contracts

Relocated inputs are charged work storage. The original verifier's time and
independent decision-space bounds transfer through a disjoint tape placement,
while its real output stays the final verdict rather than another work tape.
-/

public section

namespace Complexity
namespace TM

variable {k : ℕ}

/-- Relocating the virtual input charges its whole source input-head window.
The actual output remains output, so no extra output-work-tape cell is charged. -/
theorem retargetInputStarted_keepsWindow_of_decidesInTimeSpace (M : TM k)
    {L : Language} {T S : ℕ → ℕ} (hdec : M.DecidesInTimeSpace L T S)
    (z : List Bool) (r : Tape) (hrsi : Tape.StartInvariant r)
    {inputLength H : ℕ} (hspace : z.length + S z.length + 1 ≤ H)
    (hr : max r.head 1 ≤ inputLength + H + 1) :
    ∀ c, (retargetInputStarted M).reaches (retargetInputStartedCfg M z r) c →
      c.WithinDecisionSpace inputLength H := by
  have hne := qstart_ne_qhalt_of_decidesInTime M hdec.2
  rw [retargetInputStartedCfg_eq_retargetWrap M z r hne]
  refine retargetInputStarted_keepsWindow_of_reaches M r (startedCfg M z hne)
    ?_ ?_ ?_ ?_ hrsi hspace hr
  · intro c hc
    exact hdec.1 z c (Relation.ReflTransGen.head (step_initCfg_startedCfg M z hne) hc)
  · rw [startedCfg_input_eq M z hne]
    exact (startInvariant_initOfBool z).move Dir3.right
  · intro i
    rw [startedCfg_work_eq_init_move_right M z hne i]
    exact startInvariant_initNil.move Dir3.right
  · rw [startedCfg_output_eq_init_move_right M z hne]
    exact startInvariant_initNil.move Dir3.right

/-- The virtual-input verifier phase has the original time budget and exact verdict,
with honest decision-space safety at every reachable prefix, including time zero. -/
theorem retargetInputStarted_hoareTimeSafety_decide (M : TM k)
    {L : Language} {T S : ℕ → ℕ} (hdec : M.DecidesInTimeSpace L T S)
    (z : List Bool) (r : Tape) (hrsi : Tape.StartInvariant r)
    {inputLength H : ℕ} (hspace : z.length + S z.length + 1 ≤ H)
    (hr : max r.head 1 ≤ inputLength + H + 1) :
    (retargetInputStarted M).HoareTime
      (fun inp work out => inp = r ∧
        work = (retargetInputStartedCfg M z r).work ∧ out = parkedBlank)
      (fun _ _ out => (z ∈ L → out.cells 1 = Γ.one) ∧
        (z ∉ L → out.cells 1 = Γ.zero))
      (T z.length) ∧
    (retargetInputStarted M).HoareSafety
      (fun inp work out => inp = r ∧
        work = (retargetInputStartedCfg M z r).work ∧ out = parkedBlank)
      (fun inp work out => (⟨(), inp, work, out⟩ : Cfg (k + 1) Unit).WithinDecisionSpace
        inputLength H) := by
  constructor
  · exact (retargetInputStarted_hoareTime_decide M hdec.2 z).weaken_pre
      (fun inp work out hp => by rcases hp with ⟨rfl, hw, ho⟩; exact ⟨hw, ho⟩)
  · rintro inp work out ⟨hi, hw, ho⟩ c hc
    rw [hi, hw, ho] at hc
    exact retargetInputStarted_keepsWindow_of_decidesInTimeSpace M hdec z r hrsi
      hspace hr c hc

/-- The same verifier phase in a genuinely separate work-tape block. Extras
outside the block retain their tapes exactly and are charged against `H`. -/
theorem placeWorkTM_retargetInputStarted_hoareTimeSafety_decide (M : TM k)
    {L : Language} {T S : ℕ → ℕ} (hdec : M.DecidesInTimeSpace L T S)
    (z : List Bool) (r : Tape) (hrsi : Tape.StartInvariant r)
    (pre post : ℕ) (extras : Fin (pre + (k + 1) + post) → Tape)
    (hextraSI : ∀ i, ¬ placeWorkInMiddle pre (k + 1) i →
      Tape.StartInvariant (extras i))
    (hextraPos : ∀ i, ¬ placeWorkInMiddle pre (k + 1) i → 1 ≤ (extras i).head)
    {inputLength H : ℕ} (hspace : z.length + S z.length + 1 ≤ H)
    (hr : max r.head 1 ≤ inputLength + H + 1)
    (hextraH : ∀ i, ¬ placeWorkInMiddle pre (k + 1) i → (extras i).head ≤ H) :
    (placeWorkTM pre post (retargetInputStarted M)).HoareTime
      (fun inp work out => inp = r ∧
        work = (placeWorkCfg (retargetInputStarted M) pre post extras
          (retargetInputStartedCfg M z r)).work ∧ out = parkedBlank)
      (fun _ work out => ((z ∈ L → out.cells 1 = Γ.one) ∧
        (z ∉ L → out.cells 1 = Γ.zero)) ∧
        ∀ i, ¬ placeWorkInMiddle pre (k + 1) i → work i = extras i)
      (T z.length) ∧
    (placeWorkTM pre post (retargetInputStarted M)).HoareSafety
      (fun inp work out => inp = r ∧
        work = (placeWorkCfg (retargetInputStarted M) pre post extras
          (retargetInputStartedCfg M z r)).work ∧ out = parkedBlank)
      (fun inp work out =>
        (⟨(), inp, work, out⟩ : Cfg (pre + (k + 1) + post) Unit).WithinDecisionSpace
          inputLength H) := by
  constructor
  · rintro inp work out ⟨hi, hw, ho⟩
    rw [hi, hw, ho]
    obtain ⟨c, t, ht, hc, hh, hv⟩ := retargetInputStarted_hoareTime_decide M hdec.2 z
      r (retargetInputStartedCfg M z r).work parkedBlank ⟨rfl, rfl⟩
    refine ⟨placeWorkCfg (retargetInputStarted M) pre post extras c,
      t, ht, ?_, hh, hv, ?_⟩
    · exact placeWorkTM_reachesIn_placeWorkCfg_of_startInvariant
        (retargetInputStarted M) pre post extras hc hextraSI hextraPos
    · intro i hi
      exact placeWorkCfg_work_extra (retargetInputStarted M) pre post extras c i hi
  · rintro inp work out ⟨hi, hw, ho⟩ c hc
    rw [hi, hw, ho] at hc
    exact placeWorkTM_keepsWindow_of_reaches (retargetInputStarted M) pre post extras
      (retargetInputStartedCfg M z r) hextraSI hextraPos hextraH
      (retargetInputStarted_keepsWindow_of_decidesInTimeSpace M hdec z r hrsi hspace hr)
      c hc

end TM
end Complexity
