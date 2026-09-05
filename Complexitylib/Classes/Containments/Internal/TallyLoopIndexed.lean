/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PPParts

/-!
# A counting loop whose resting tapes change with the count

⚠️ Unreviewed by Bolton

`NTM.tallyLoop_hoareTime_of_hoare` pins the tapes the tally state does not name to one bank, the
same at every index. That is right for a loop whose only state is its counters — the path-counting
machine of `PP ⊆ PSPACE` — but not for one carrying something alongside them.

The witness enumerator of `PH ⊆ PSPACE` is such a loop: its witness tape advances with the
counter, so the bank it rests in is a function of the count. These are the same two rules with
that bank indexed; the proofs are unchanged apart from the index.

## Main results

- `NTM.tallyLoop_hoareTime_of_hoare_indexed` — the loop's contract, with an indexed resting bank
- `NTM.tallyLoop_keepsWindow_of_hoare_indexed` — its window, one iteration wide
-/

@[expose] public section

namespace Complexity

namespace NTM

/-- **The counting loop, with a bank that changes with the count.** -/
theorem tallyLoop_hoareTime_of_hoare_indexed {n : ℕ} (tmBody tmTest : TM n)
    (cIdx aIdx rIdx : Fin n)
    (I : Tape) (rest : ℕ → Fin n → Tape) (P : ℕ → Bool) (mid : ℕ → TM.TapePred n)
    (N bBody bTest : ℕ) (hN : 1 ≤ N)
    (hI : TM.Parked I) (hrest : ∀ v i, TM.Parked (rest v i))
    (hbody : ∀ v, v < N →
      tmBody.HoareTime (tallyPre cIdx aIdx rIdx I (rest v) P v) (mid v) bBody)
    (hmid : ∀ v inp work out, mid v inp work out → TM.LoopParked inp work out)
    (htest : ∀ v, v < N →
      tmTest.HoareTime (mid v) (tallyPost cIdx aIdx rIdx I (rest (v + 1)) P N (v + 1)) bTest) :
    (TM.loopTM tmBody tmTest).HoareTime
      (tallyPre cIdx aIdx rIdx I (rest 0) P 0)
      (tallyPost cIdx aIdx rIdx I (rest N) P N N)
      (N * (bBody + bTest + 5)) := by
  have hsucc : N - 1 + 1 = N := by omega
  refine (TM.loopTM_hoareTime_indexed tmBody tmTest
    (E := fun j => tallyPre cIdx aIdx rIdx I (rest j) P j)
    (post := tallyPost cIdx aIdx rIdx I (rest N) P N N)
    (N := N - 1) (b := bBody + bTest + 5)
    (idx := tallyIdx cIdx) ?_ ?_ ?_).consequence
    (fun _ _ _ h => h) (fun _ _ _ h => h) (le_of_eq (by rw [hsucc]))
  · intro j inp work out h
    exact tallyIdx_tallyPre cIdx aIdx rIdx I (rest j) P j h
  · intro j hj inp work out h
    have hjN : j < N := by omega
    have hne : ∀ a b c, tallyPost cIdx aIdx rIdx I (rest (j + 1)) P N (j + 1) a b c →
        TM.LoopParked a b c ∧ c.cells 1 ≠ Γ.one := by
      intro a b c hp
      refine ⟨tallyPost_loopParked cIdx aIdx rIdx I (rest (j + 1)) P hI (hrest (j + 1)) N
        (j + 1) hp, ?_⟩
      obtain ⟨-, -, rfl⟩ := hp
      rw [ite_eq_right (show ¬ (j + 1 = N) by omega)]
      exact fun hcon => absurd (outSlot_cells_one_eq_one_iff Γw.zero |>.mp hcon) (by decide)
    obtain ⟨inp', work', out', t, -, ht, hreach, hp'⟩ :=
      TM.loopTM_continue_of_hoare tmBody tmTest (hbody j hjN) (htest j hjN)
        (fun a b c hm => hmid j a b c hm) hne inp work out h
    obtain ⟨hi', hw', ho'⟩ := hp'
    exact ⟨inp', work', out', t, ht, hreach, hi', hw', Γw.zero, by decide,
      by rw [ho', ite_eq_right (by omega)]⟩
  · intro inp work out h
    have hjN : N - 1 < N := by omega
    have hhalt : ∀ a b c, tallyPost cIdx aIdx rIdx I (rest (N - 1 + 1)) P N (N - 1 + 1) a b c →
        TM.LoopParked a b c ∧ c.cells 1 = Γ.one := by
      intro a b c hp
      refine ⟨tallyPost_loopParked cIdx aIdx rIdx I (rest (N - 1 + 1)) P hI (hrest _) N _ hp,
        ?_⟩
      obtain ⟨-, -, rfl⟩ := hp
      rw [ite_eq_left hsucc]
      exact (outSlot_cells_one_eq_one_iff Γw.one).mpr rfl
    obtain ⟨c', t, ht, hreach, hstate, hpost⟩ :=
      TM.loopTM_halt_of_hoare tmBody tmTest (hbody (N - 1) hjN) (htest (N - 1) hjN)
        (fun a b c hm => hmid (N - 1) a b c hm) hhalt inp work out h
    exact ⟨c', t, ht, hreach, hstate, by rw [hsucc] at hpost; exact hpost⟩




/-- **Its window, one iteration wide.** -/
theorem tallyLoop_keepsWindow_of_hoare_indexed {n : ℕ} (tmBody tmTest : TM n)
    (cIdx aIdx rIdx : Fin n)
    (I : Tape) (rest : ℕ → Fin n → Tape) (P : ℕ → Bool) (mid : ℕ → TM.TapePred n)
    (N bBody bTest inputLength : ℕ) (hN : 1 ≤ N)
    (hI : TM.Parked I) (hrest : ∀ v i, TM.Parked (rest v i))
    (hIhead : I.head ≤ inputLength + 1) (hrestHead : ∀ v i, (rest v i).head ≤ 1)
    (hbody : ∀ v, v < N →
      tmBody.HoareTime (tallyPre cIdx aIdx rIdx I (rest v) P v) (mid v) bBody)
    (hmid : ∀ v inp work out, mid v inp work out → TM.LoopParked inp work out)
    (htest : ∀ v, v < N →
      tmTest.HoareTime (mid v) (tallyPost cIdx aIdx rIdx I (rest (v + 1)) P N (v + 1)) bTest) :
    ∀ inp work out, tallyPre cIdx aIdx rIdx I (rest 0) P 0 inp work out →
      ∀ c, (TM.loopTM tmBody tmTest).reaches
        ⟨(TM.loopTM tmBody tmTest).qstart, inp, work, out⟩ c →
        c.WithinDecisionSpace inputLength (1 + (bBody + bTest + 5)) := by
  have hsucc : N - 1 + 1 = N := by omega
  refine TM.loopTM_keepsWindow_indexed_of_parked tmBody tmTest
    (fun j => tallyPre cIdx aIdx rIdx I (rest j) P j) (N - 1) (bBody + bTest + 5) ?_ ?_ ?_ 0
    (by omega)
  · intro j hj inp work out h
    have hjN : j < N := by omega
    have hne : ∀ a b c, tallyPost cIdx aIdx rIdx I (rest (j + 1)) P N (j + 1) a b c →
        TM.LoopParked a b c ∧ c.cells 1 ≠ Γ.one := by
      intro a b c hp
      refine ⟨tallyPost_loopParked cIdx aIdx rIdx I (rest (j + 1)) P hI (hrest (j + 1)) N
        (j + 1) hp, ?_⟩
      obtain ⟨-, -, rfl⟩ := hp
      rw [ite_eq_right (show ¬ (j + 1 = N) by omega)]
      exact fun hcon => absurd (outSlot_cells_one_eq_one_iff Γw.zero |>.mp hcon) (by decide)
    obtain ⟨inp', work', out', t, ht1, ht, hreach, hp'⟩ :=
      TM.loopTM_continue_of_hoare tmBody tmTest (hbody j hjN) (htest j hjN)
        (fun a b c hm => hmid j a b c hm) hne inp work out h
    obtain ⟨hi', hw', ho'⟩ := hp'
    exact ⟨inp', work', out', t, ht1, ht, hreach, hi', hw', Γw.zero, by decide,
      by rw [ho', ite_eq_right (by omega)]⟩
  · intro inp work out h
    have hjN : N - 1 < N := by omega
    have hhalt : ∀ a b c, tallyPost cIdx aIdx rIdx I (rest (N - 1 + 1)) P N (N - 1 + 1) a b c →
        TM.LoopParked a b c ∧ c.cells 1 = Γ.one := by
      intro a b c hp
      refine ⟨tallyPost_loopParked cIdx aIdx rIdx I (rest (N - 1 + 1)) P hI (hrest _) N _ hp,
        ?_⟩
      obtain ⟨-, -, rfl⟩ := hp
      rw [ite_eq_left hsucc]
      exact (outSlot_cells_one_eq_one_iff Γw.one).mpr rfl
    obtain ⟨c', t, ht, hreach, hstate, -⟩ :=
      TM.loopTM_halt_of_hoare tmBody tmTest (hbody (N - 1) hjN) (htest (N - 1) hjN)
        (fun a b c hm => hmid (N - 1) a b c hm) hhalt inp work out h
    exact ⟨c', t, ht, hreach, hstate⟩
  · rintro j - inp work out ⟨rfl, rfl, s, -, rfl⟩
    refine ⟨fun i => ?_, hIhead, le_of_eq rfl⟩
    simp only [tallyWork]
    split
    · exact le_of_eq rfl
    · split
      · exact le_of_eq rfl
      · split
        · exact le_of_eq rfl
        · exact hrestHead j i


end NTM

end Complexity
