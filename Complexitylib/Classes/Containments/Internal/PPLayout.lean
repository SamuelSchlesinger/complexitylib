/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PPSim
public import Complexitylib.Classes.Containments.Internal.PPBody
public import Complexitylib.Models.TuringMachine.Subroutines.WipeRewind
public import Complexitylib.Models.TuringMachine.Subroutines.ParkRewind

/-!
# The counting machine's tape layout

⚠️ Unreviewed by Bolton

Placing the simulation with `TM.placeWorkTM 0 m` fixes where every tape sits: the simulated
machine's `k` tapes come first, then its choice tape — which is the loop's counter — then the
loop's own registers, and last the tape `TM.retargetOutput` sends the verdict to.

Six registers are needed: the two tallies, the horizon to compare the count against, a scratch
cell for that comparison, a permanently blank tape to blank the verdict slot from, and the unary
register that drives the wipe.

## Main results

- `NTM.bodyTapes` — the tape count, and the named indices into it
- `NTM.bodyIdx_distinct` — the indices are pairwise distinct
- `NTM.bodyRest` — the resting contents of every tape the tally state does not name
- `NTM.wipeTargets` — the tapes the body blanks on its way out
- `NTM.natTape_zero`, `NTM.regTape_zero` — a register holding zero is the blank tape
- `NTM.regTape_eq_natTape` — a unary register of `T` ones is the binary numeral `2 ^ T - 1`
-/

@[expose] public section

namespace Complexity

namespace NTM

variable {k : ℕ}

/-- The counting machine's tape count: the simulation's `k + 1`, six registers, and the tape the
verdict is written to. -/
abbrev bodyTapes (k : ℕ) : ℕ := 0 + (k + 1) + 6 + 1

/-- The counter, which is also the simulation's choice tape. -/
def cIdx (k : ℕ) : Fin (bodyTapes k) := ⟨k, by show k < 0 + (k + 1) + 6 + 1; omega⟩

/-- The accepting tally. -/
def aIdx (k : ℕ) : Fin (bodyTapes k) := ⟨k + 1, by show k + 1 < 0 + (k + 1) + 6 + 1; omega⟩

/-- The rejecting tally. -/
def rIdx (k : ℕ) : Fin (bodyTapes k) := ⟨k + 2, by show k + 2 < 0 + (k + 1) + 6 + 1; omega⟩

/-- The horizon the counter is compared against. -/
def nIdx (k : ℕ) : Fin (bodyTapes k) := ⟨k + 3, by show k + 3 < 0 + (k + 1) + 6 + 1; omega⟩

/-- Scratch space for that comparison. -/
def resIdx (k : ℕ) : Fin (bodyTapes k) := ⟨k + 4, by show k + 4 < 0 + (k + 1) + 6 + 1; omega⟩

/-- A permanently blank tape, read whenever the verdict slot must be blanked. -/
def zIdx (k : ℕ) : Fin (bodyTapes k) := ⟨k + 5, by show k + 5 < 0 + (k + 1) + 6 + 1; omega⟩

/-- The unary register that drives the wipe. -/
def regIdx (k : ℕ) : Fin (bodyTapes k) := ⟨k + 6, by show k + 6 < 0 + (k + 1) + 6 + 1; omega⟩

/-- The tape the simulation's output is redirected to. -/
def vIdx (k : ℕ) : Fin (bodyTapes k) := ⟨k + 7, by show k + 7 < 0 + (k + 1) + 6 + 1; omega⟩

theorem vIdx_eq_last (k : ℕ) : vIdx k = Fin.last (0 + (k + 1) + 6) := by
  apply Fin.ext
  show k + 7 = 0 + (k + 1) + 6
  omega

/-- The simulated machine's own work tapes: everything strictly left of the counter. -/
def simTapes (k : ℕ) : List (Fin (bodyTapes k)) :=
  (List.finRange (bodyTapes k)).filter (fun j => decide (j.val < k))

@[simp] theorem mem_simTapes_iff (k : ℕ) (j : Fin (bodyTapes k)) :
    j ∈ simTapes k ↔ j.val < k := by
  simp [simTapes, List.mem_filter]

theorem simTapes_nodup (k : ℕ) : (simTapes k).Nodup :=
  (List.nodup_finRange _).filter _

theorem simTapes_length_le (k : ℕ) : (simTapes k).length ≤ bodyTapes k := by
  refine le_trans (List.length_filter_le _ _) ?_
  rw [List.length_finRange]


/-- **A counter tape holding zero is the blank tape**, and so is a unary register holding zero.
The machine's initial configuration therefore already carries both, which is what a prologue can
start from. -/
theorem natTape_zero : natTape 0 = TM.blankTape := by
  refine Tape.ext rfl (funext fun j => ?_)
  show ((Tape.init ((Nat.bits 0).map Γ.ofBool)).move Dir3.right).cells j
    = ((Tape.init ([] : List Γ)).move Dir3.right).cells j
  rw [show Nat.bits 0 = [] from by simp]
  rfl

theorem regTape_zero : TM.regTape 0 = TM.blankTape := by
  refine Tape.ext rfl (funext fun j => ?_)
  show TM.regCells 0 j = ((Tape.init ([] : List Γ)).move Dir3.right).cells j
  rw [Tape.move_cells]
  by_cases hj : j = 0
  · rw [hj]
    show (if (0 : ℕ) = 0 then Γ.start else _) = _
    rw [ite_eq_left rfl, Tape.init_cells_zero]
  · show (if j = 0 then Γ.start else if j ≤ 0 then Γ.one else Γ.blank) = _
    rw [ite_eq_right hj, ite_eq_right (by omega), show j = (j - 1) + 1 from by omega,
      Tape.init_nil_cells_succ]


/-- **A unary register of `T` ones is the binary numeral `2 ^ T - 1`.** The two encodings agree
cell for cell: `regCells` writes `1` in cells `1 … T` and blanks beyond, and so do the bits of
`2 ^ T - 1`. This is what lets the prologue produce the horizon `2 ^ T` with a single increment,
instead of a doubling loop. -/
theorem bits_two_pow_sub_one : ∀ T : ℕ, (2 ^ T - 1).bits = List.replicate T true := by
  intro T
  induction T with
  | zero => simp
  | succ T ih =>
      have hrw : 2 ^ (T + 1) - 1 = 2 * (2 ^ T - 1) + 1 := by
        have h : 1 ≤ 2 ^ T := Nat.one_le_two_pow
        have : 2 ^ (T + 1) = 2 * 2 ^ T := by ring
        omega
      rw [hrw, Nat.bit1_bits, ih, List.replicate_succ]

theorem regTape_eq_natTape (T : ℕ) : TM.regTape T = natTape (2 ^ T - 1) := by
  refine Tape.ext rfl (funext fun j => ?_)
  have hbits := bits_two_pow_sub_one T
  have hlen : (2 ^ T - 1).bits.length = T := by rw [hbits, List.length_replicate]
  show TM.regCells T j = (natTape (2 ^ T - 1)).cells j
  rw [natTape, Tape.move_cells]
  by_cases hj : j = 0
  · rw [hj]
    show (if (0 : ℕ) = 0 then Γ.start else _) = _
    rw [ite_eq_left rfl, Tape.init_cells_zero]
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [Tape.init_cells_succ]
    show (if i + 1 = 0 then Γ.start else if i + 1 ≤ T then Γ.one else Γ.blank)
      = (((2 ^ T - 1).bits.map Γ.ofBool)[i]?).getD Γ.blank
    rw [ite_eq_right (by omega), hbits]
    by_cases hi : i < T
    · rw [ite_eq_left (by omega)]
      simp [hi, Γ.ofBool]
    · rw [ite_eq_right (by omega)]
      simp [hi]

/-- **The registers are pairwise distinct**, and none of them is one of the simulation's tapes. -/
theorem cIdx_lt_aIdx (k : ℕ) : (cIdx k).val < (aIdx k).val := by
  show k < k + 1; omega

theorem bodyIdx_distinct (k : ℕ) :
    cIdx k ≠ aIdx k ∧ cIdx k ≠ rIdx k ∧ aIdx k ≠ rIdx k ∧
    nIdx k ≠ cIdx k ∧ nIdx k ≠ aIdx k ∧ nIdx k ≠ rIdx k ∧
    resIdx k ≠ cIdx k ∧ resIdx k ≠ aIdx k ∧ resIdx k ≠ rIdx k ∧
    resIdx k ≠ nIdx k ∧ zIdx k ≠ cIdx k ∧ zIdx k ≠ aIdx k ∧ zIdx k ≠ rIdx k ∧
    regIdx k ≠ cIdx k ∧ vIdx k ≠ cIdx k ∧ vIdx k ≠ aIdx k ∧ vIdx k ≠ rIdx k ∧
    vIdx k ≠ zIdx k ∧ regIdx k ∉ simTapes k ∧ vIdx k ∉ simTapes k := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
      | (intro h; have := congrArg Fin.val h; simp only [cIdx, aIdx, rIdx, nIdx, resIdx,
          zIdx, regIdx, vIdx] at this; omega)
      | (rw [mem_simTapes_iff]; simp only [regIdx, vIdx]; omega)

/-- **The resting contents of every tape the tally state does not name.** The horizon sits on
`NTM.nIdx` and the wipe's unary register on `NTM.regIdx`; everything else rests blank. -/
def bodyRest (k N H : ℕ) : Fin (bodyTapes k) → Tape := fun j =>
  if j = nIdx k then natTape N
  else if j = regIdx k then TM.regTape H
  else TM.blankTape

theorem bodyRest_nIdx (k N H : ℕ) : bodyRest k N H (nIdx k) = natTape N := by
  simp only [bodyRest]
  simp

theorem bodyRest_regIdx (k N H : ℕ) : bodyRest k N H (regIdx k) = TM.regTape H := by
  have h : regIdx k ≠ nIdx k := by
    intro h
    have := congrArg Fin.val h
    simp only [regIdx, nIdx] at this
    omega
  simp only [bodyRest, ite_eq_right h]
  simp

theorem bodyRest_other (k N H : ℕ) (j : Fin (bodyTapes k))
    (hn : j ≠ nIdx k) (hr : j ≠ regIdx k) : bodyRest k N H j = TM.blankTape := by
  simp only [bodyRest, ite_eq_right hn, ite_eq_right hr]

theorem bodyRest_parked (k N H : ℕ) : ∀ j, TM.Parked (bodyRest k N H j) := by
  intro j
  simp only [bodyRest]
  split
  · exact natTape_parked N
  · split
    · exact ⟨le_refl 1, fun i hi => by
        show TM.regCells H i ≠ Γ.start
        simp only [TM.regCells]
        split
        · omega
        · split <;> decide⟩
    · exact TM.blankTape_parked

theorem bodyRest_cells_zero (k N H : ℕ) : ∀ j, (bodyRest k N H j).cells 0 = Γ.start := by
  intro j
  simp only [bodyRest]
  split
  · exact natTape_cells_zero N
  · split
    · rfl
    · show ((Tape.init ([] : List Γ)).move Dir3.right).cells 0 = Γ.start
      rw [Tape.move_cells]
      exact Tape.init_cells_zero []

theorem bodyRest_head (k N H : ℕ) : ∀ j, (bodyRest k N H j).head = 1 := by
  intro j
  simp only [bodyRest]
  split
  · rfl
  · split
    · rfl
    · rfl

theorem bodyRest_startInvariant (k N H : ℕ) :
    ∀ j, Tape.StartInvariant (bodyRest k N H j) :=
  fun j => ⟨bodyRest_cells_zero k N H j, fun i hi => (bodyRest_parked k N H j).2 i hi⟩

/-- **The named registers are distinct from each other and from the simulation's tapes.** -/
theorem bodyIdx_ne (k : ℕ) :
    (cIdx k).val = k ∧ (aIdx k).val = k + 1 ∧ (rIdx k).val = k + 2 ∧
    (nIdx k).val = k + 3 ∧ (resIdx k).val = k + 4 ∧ (zIdx k).val = k + 5 ∧
    (regIdx k).val = k + 6 ∧ (vIdx k).val = k + 7 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- The tapes the body wipes on its way out: the simulated machine's own, and the tape its
verdict was written to. -/
def wipeTargets (k : ℕ) : List (Fin (bodyTapes k)) := simTapes k ++ [vIdx k]

@[simp] theorem mem_wipeTargets_iff (k : ℕ) (j : Fin (bodyTapes k)) :
    j ∈ wipeTargets k ↔ (j.val < k ∨ j = vIdx k) := by
  simp [wipeTargets]

theorem wipeTargets_nodup (k : ℕ) : (wipeTargets k).Nodup := by
  refine List.Nodup.append (simTapes_nodup k) (List.nodup_singleton _) ?_
  intro a ha hb
  rw [mem_simTapes_iff] at ha
  rw [List.mem_singleton] at hb
  subst hb
  simp only [vIdx] at ha
  omega

theorem regIdx_not_mem_wipeTargets (k : ℕ) : regIdx k ∉ wipeTargets k := by
  rw [mem_wipeTargets_iff]
  rintro (h | h)
  · simp only [regIdx] at h
    omega
  · have := congrArg Fin.val h
    simp only [regIdx, vIdx] at this
    omega

end NTM

end Complexity
