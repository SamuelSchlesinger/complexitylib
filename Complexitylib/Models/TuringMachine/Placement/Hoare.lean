/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Placement
public import Complexitylib.Models.TuringMachine.Hoare.Defs

/-!
# Hoare contracts through work-tape placement

⚠️ Unreviewed by Bolton

A stage of a larger machine is a small machine placed in a block of the layout's tapes. Its
contract should travel with it: what it promises about its own tapes should become a promise
about the block, and the tapes on either side should come back untouched.

That is the rule below. The frame it carries is the one `TM.placeWorkTM` needs anyway — every
tape outside the block is start-invariant with its head off the marker, so the placed machine's
structurally mandatory idle writes leave it exactly as it was.

## Main results

- `TM.placeWorkTM_hoareTime` — a placed stage's contract, with the surrounding tapes framed
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- **A placed stage keeps its contract, and its neighbours.** The precondition asks that the
tapes outside the block are the given frame and that the block satisfies the stage's own
precondition; the postcondition returns the frame unchanged and the stage's postcondition on the
block. -/
theorem placeWorkTM_hoareTime (tm : TM n) {pre post : TapePred n} {b : ℕ}
    (h : tm.HoareTime pre post b) (pre₀ post₀ : ℕ)
    (extras : Fin (pre₀ + n + post₀) → Tape)
    (hinv : ∀ i, ¬ placeWorkInMiddle pre₀ n i → Tape.StartInvariant (extras i))
    (hhead : ∀ i, ¬ placeWorkInMiddle pre₀ n i → 1 ≤ (extras i).head) :
    (placeWorkTM pre₀ post₀ tm).HoareTime
      (fun inp work out =>
        (∀ i, ¬ placeWorkInMiddle pre₀ n i → work i = extras i) ∧
        pre inp (fun j => work (placeWorkIdx pre₀ post₀ j)) out)
      (fun inp work out =>
        (∀ i, ¬ placeWorkInMiddle pre₀ n i → work i = extras i) ∧
        post inp (fun j => work (placeWorkIdx pre₀ post₀ j)) out)
      b := by
  rintro inp work out ⟨hframe, hpre⟩
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ :=
    h inp (fun j => work (placeWorkIdx pre₀ post₀ j)) out hpre
  refine ⟨placeWorkCfg tm pre₀ post₀ extras c', t, ht, ?_, hhalt, ?_, ?_⟩
  · have hstart : (⟨(placeWorkTM pre₀ post₀ tm).qstart, inp, work, out⟩ :
        Cfg (pre₀ + n + post₀) (placeWorkTM pre₀ post₀ tm).Q) =
        placeWorkCfg tm pre₀ post₀ extras
          (⟨tm.qstart, inp, fun j => work (placeWorkIdx pre₀ post₀ j), out⟩ : Cfg n tm.Q) := by
      refine Cfg.ext rfl rfl (funext fun i => ?_) rfl
      show work i = if hi : placeWorkInMiddle pre₀ n i then
        work (placeWorkIdx pre₀ post₀ (placeWorkCoord pre₀ n i hi)) else extras i
      by_cases hi : placeWorkInMiddle pre₀ n i
      · rw [dite_eq_left hi, placeWorkIdx_placeWorkCoord i hi]
      · rw [dite_eq_right hi]
        exact hframe i hi
    rw [hstart]
    exact placeWorkTM_reachesIn_placeWorkCfg_of_startInvariant tm pre₀ post₀ extras hreach
      hinv hhead
  · intro i hi
    show (if h : placeWorkInMiddle pre₀ n i then _ else extras i) = extras i
    rw [dite_eq_right hi]
  · show post c'.input (fun j => (placeWorkCfg tm pre₀ post₀ extras c').work
      (placeWorkIdx pre₀ post₀ j)) c'.output
    have hw : (fun j => (placeWorkCfg tm pre₀ post₀ extras c').work
        (placeWorkIdx pre₀ post₀ j)) = c'.work := by
      funext j
      show (if hi : placeWorkInMiddle pre₀ n (placeWorkIdx pre₀ post₀ j) then
        c'.work (placeWorkCoord pre₀ n (placeWorkIdx pre₀ post₀ j) hi)
        else extras (placeWorkIdx pre₀ post₀ j)) = c'.work j
      rw [dite_eq_left (placeWorkInMiddle_placeWorkIdx pre₀ post₀ j),
        placeWorkCoord_placeWorkIdx pre₀ post₀ j]
    rw [hw]
    exact hpost

end TM

end Complexity
