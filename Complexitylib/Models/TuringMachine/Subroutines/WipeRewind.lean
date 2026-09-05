/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Subroutines.ResetTapes
public import Complexitylib.Models.TuringMachine.Subroutines.ParkRewind

/-!
# Blanking a group of tapes and putting their heads back

`TM.resetTapes_hoareTime` blanks its targets by walking a fixed height across them, which leaves
every head parked at the far end of the walk. A loop that reuses those tapes needs them back at
cell one, so the wipe is followed by one more rewind.

The wipe is content-agnostic: nothing is assumed about *where* inside the wiped region the
non-blank cells sit, only that nothing lies beyond it. That is what makes it the right tool for
cleaning up after a simulation, whose tapes can hold anything at all.

## Main results

- `TM.wipeRewindTM` — blank the named tapes and return their heads to cell one
- `TM.wipeRewindTM_hoareTime` — its contract, landing on a fully named bank
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- The blank tape parked at cell one — what a wiped-and-rewound tape becomes. -/
def blankTape : Tape := (Tape.init ([] : List Γ)).move Dir3.right

theorem blankTape_parked : Parked blankTape :=
  ⟨le_refl 1, fun j hj => by
    show ((Tape.init ([] : List Γ)).move Dir3.right).cells j ≠ Γ.start
    rw [Tape.move_cells]
    exact Tape.init_nil_cells_ne_start j hj⟩

theorem blankTape_startInvariant : Tape.StartInvariant blankTape := by
  refine ⟨?_, fun j hj => ?_⟩
  · show ((Tape.init ([] : List Γ)).move Dir3.right).cells 0 = Γ.start
    rw [Tape.move_cells]
    exact Tape.init_cells_zero []
  · exact blankTape_parked.2 j hj

/-- **Blank the named tapes, then put their heads back at cell one.** -/
def wipeRewindTM (targets : List (Fin n)) (r : Fin n) : TM n :=
  seqTM
    (seqTM (seqTM skipTM (bigSeqTM (targets.map rewindWorkTM)))
      (forRegTM (wipeStepTM targets) r))
    (bigSeqTM (targets.map rewindWorkTM))

/-- **The wipe stage's contract.** The targets come back blank and parked at cell one, the
register that drove the walk is unchanged, and every other tape is untouched. -/
theorem wipeRewindTM_hoareTime (targets : List (Fin n)) (hnodup : targets.Nodup)
    (r : Fin n) (hr : r ∉ targets) (H : ℕ)
    (I₀ : Tape) (W₀ : Fin n → Tape) (O₀ : Tape)
    (hinpSI : Tape.StartInvariant I₀) (hinpP : Parked I₀)
    (hout0 : O₀ = blankTape)
    (hworkSI : ∀ j, j ≠ r → Tape.StartInvariant (W₀ j))
    (htargetHead : ∀ j, j ∈ targets → (W₀ j).head ≤ H)
    (htargetFar : ∀ j, j ∈ targets → ∀ i, H < i → (W₀ j).cells i = Γ.blank)
    (hworkR : W₀ r = regTape H)
    (hother : ∀ j, j ≠ r → j ∉ targets → Parked (W₀ j)) :
    (wipeRewindTM targets r).HoareTime
      (fun inp work out => inp = I₀ ∧ work = W₀ ∧ out = O₀)
      (fun inp work out => inp = I₀ ∧
        work = (fun j => if j ∈ targets then blankTape else W₀ j) ∧ out = O₀)
      ((targets.length * (H + 4) + H * 4 + 8) + 1 +
        (targets.length * (H + 4) + 1)) := by
  classical
  set W1 : Fin n → Tape :=
    fun j => if j ∈ targets then (⟨H + 1, (Tape.init ([] : List Γ)).cells⟩ : Tape) else W₀ j
    with hW1def
  have hW1P : ∀ j, Parked (W1 j) := by
    intro j
    simp only [hW1def]
    split
    · exact ⟨by show (1 : ℕ) ≤ H + 1; omega, fun i hi => Tape.init_nil_cells_ne_start i hi⟩
    · by_cases hjr : j = r
      · rw [hjr, hworkR]
        exact ⟨le_refl 1, fun i hi => by
          show regCells H i ≠ Γ.start
          simp only [regCells]
          split
          · omega
          · split <;> decide⟩
      · exact hother j hjr (by assumption)
  have hO₀P : Parked O₀ := by rw [hout0]; exact blankTape_parked
  -- The wipe itself.
  have hwipe : (seqTM (seqTM skipTM (bigSeqTM (targets.map rewindWorkTM)))
      (forRegTM (wipeStepTM targets) r)).HoareTime
      (fun inp work out => inp = I₀ ∧ work = W₀ ∧ out = O₀)
      (fun inp work out => inp = I₀ ∧ work = W1 ∧ out = O₀)
      (targets.length * (H + 4) + H * 4 + 8) := by
    refine (resetTapes_hoareTime targets hnodup r hr H I₀ W₀ O₀ hinpSI hinpP
      (by rw [hout0, blankTape]) hworkSI htargetHead hworkR hother).strengthen_post ?_
    rintro inp work out ⟨rfl, rfl, hin, hreg, hout⟩
    refine ⟨rfl, funext fun j => ?_, rfl⟩
    simp only [hW1def]
    by_cases hj : j ∈ targets
    · rw [ite_eq_left hj, hin j hj]
      exact wipedTape_eq_blank H rfl (hworkSI j (fun hjr => hr (hjr ▸ hj))).1
        (fun i hi => htargetFar j hj i hi)
    · rw [ite_eq_right hj]
      by_cases hjr : j = r
      · rw [hjr, hreg, hworkR]
      · exact hout j hjr hj
  -- Phase transition, then the rewind.
  have htrans : ∀ inp work out, (inp = I₀ ∧ work = W1 ∧ out = O₀) →
      (transitionInput inp = I₀ ∧ (fun i => transitionTape (work i)) = W1 ∧
        transitionTape out = O₀) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨transitionInput_eq_self hinpP.read_ne_start,
      funext fun i => transitionTape_eq_self (hW1P i).read_ne_start,
      transitionTape_eq_self hO₀P.read_ne_start⟩
  have hrew : (bigSeqTM (targets.map rewindWorkTM)).HoareTime
      (fun inp work out => inp = I₀ ∧ work = W1 ∧ out = O₀)
      (fun inp work out => inp = I₀ ∧
        work = (fun j => if j ∈ targets then blankTape else W₀ j) ∧ out = O₀)
      (targets.length * (H + 4) + 1) := by
    refine ((rewindList_hoareTime targets hnodup (H + 1) I₀ W1 O₀ hinpP hO₀P hW1P
      ?_).strengthen_post ?_).mono_bound (by
        have : targets.length * (H + 1 + 3) = targets.length * (H + 4) := by ring
        omega)
    · intro j hj
      simp only [hW1def, ite_eq_left hj]
      exact ⟨Tape.init_cells_zero [], le_refl _⟩
    · rintro inp work out ⟨rfl, hout, hin, hkeep⟩
      refine ⟨rfl, funext fun j => ?_, hout⟩
      by_cases hj : j ∈ targets
      · rw [hin j hj]
        simp only [hW1def, ite_eq_left hj]
        exact Tape.ext rfl (by rw [blankTape, Tape.move_cells])
      · rw [hkeep j hj]
        simp only [hW1def, ite_eq_right hj]
  exact seqTM_hoareTime _ _ hwipe htrans hrew

end TM

end Complexity
