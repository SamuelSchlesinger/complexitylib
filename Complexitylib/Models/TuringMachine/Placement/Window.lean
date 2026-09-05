/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Placement

/-!
# A placed machine's window

⚠️ Unreviewed by Bolton

A machine placed in a block of a larger tape space runs exactly as it did, so a window it keeps
on its own tapes is a window the placed machine keeps — provided the tapes on either side are
inside that window too, which they are: they never move.

## Main results

- `TM.placeWorkTM_reaches_reflect` — every configuration a placed run reaches is a placed one
- `TM.placeWorkTM_keepsWindow_of_reaches` — and so the source's window transfers
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- **Every configuration a placed run reaches is a placed configuration.** The frame never
changes, so the run is the source's run under the embedding. -/
theorem placeWorkTM_reaches_reflect (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape) (c₀ : Cfg n tm.Q)
    (hinv : ∀ i, ¬ placeWorkInMiddle pre n i → Tape.StartInvariant (extras i))
    (hhead : ∀ i, ¬ placeWorkInMiddle pre n i → 1 ≤ (extras i).head) :
    ∀ D, (placeWorkTM pre post tm).reaches (placeWorkCfg tm pre post extras c₀) D →
      ∃ c, tm.reaches c₀ c ∧ D = placeWorkCfg tm pre post extras c := by
  intro D hD
  induction hD with
  | refl => exact ⟨c₀, Relation.ReflTransGen.refl, rfl⟩
  | @tail dmid dnext _ hstp ih =>
      obtain ⟨c, hreach, rfl⟩ := ih
      have hcomm := placeWorkTM_step_placeWorkCfg_of_startInvariant tm pre post extras c
        hinv hhead
      have hstp' : (placeWorkTM pre post tm).step (placeWorkCfg tm pre post extras c)
          = some dnext := hstp
      rw [hcomm] at hstp'
      obtain ⟨c', hstep, hD⟩ := Option.map_eq_some_iff.mp hstp'
      exact ⟨c', Relation.ReflTransGen.tail hreach hstep, hD.symm⟩

/-- **A placed machine keeps its source's window**, given that the tapes on either side sit
inside it. -/
theorem placeWorkTM_keepsWindow_of_reaches (tm : TM n) (pre post : ℕ)
    (extras : Fin (pre + n + post) → Tape) (c₀ : Cfg n tm.Q)
    (hinv : ∀ i, ¬ placeWorkInMiddle pre n i → Tape.StartInvariant (extras i))
    (hhead : ∀ i, ¬ placeWorkInMiddle pre n i → 1 ≤ (extras i).head)
    {inputLength space : ℕ}
    (hextraW : ∀ i, ¬ placeWorkInMiddle pre n i → (extras i).head ≤ space)
    (htm : ∀ c, tm.reaches c₀ c → c.WithinDecisionSpace inputLength space) :
    ∀ D, (placeWorkTM pre post tm).reaches (placeWorkCfg tm pre post extras c₀) D →
      D.WithinDecisionSpace inputLength space := by
  intro D hD
  obtain ⟨c, hreach, rfl⟩ := placeWorkTM_reaches_reflect tm pre post extras c₀ hinv hhead D hD
  obtain ⟨⟨hw, hi⟩, ho⟩ := htm c hreach
  refine ⟨⟨fun j => ?_, hi⟩, ho⟩
  have hval : (placeWorkCfg tm pre post extras c).work j
      = if h : placeWorkInMiddle pre n j then c.work (placeWorkCoord pre n j h)
        else extras j := rfl
  rw [hval]
  by_cases hj : placeWorkInMiddle pre n j
  · rw [dite_eq_left hj]
    exact hw _
  · rw [dite_eq_right hj]
    exact hextraW j hj

end TM

end Complexity
