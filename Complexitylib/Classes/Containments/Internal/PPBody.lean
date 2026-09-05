/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PPTest
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub
public import Complexitylib.Models.TuringMachine.Combinators.Internal.SentinelStep
public import Complexitylib.Models.TuringMachine.Delay

/-!
# The counting loop's body

⚠️ Unreviewed by Bolton

The body of the counting loop advances the count and one of the two tallies. Which tally it
advances is decided by the simulated path's verdict, and `TM.ifTM` is the combinator that reads a
verdict and branches — but it reads the *output* tape, so the verdict must already have been
published there, which is what `TM.writeOutputBitTM` is for.

This file builds the arithmetic end of the body: given the verdict in the output tape's slot,
bump the chosen tally, bump the count, and blank the slot again for the next pass.

## Main results

- `TM.binarySuccTM_hoareTime_pinned`, `TM.binaryRippleSubTM_hoareTime_pinned` — the successor and
  truncated subtraction, with fully named result banks
- `TM.condBumpTM`, `TM.condBumpTM_hoareTime` — bump one of two registers according to the
  published verdict
- `TM.tallyBumpTM`, `TM.tallyBumpTM_hoareTime` — that bump, the count's bump, and the blanking of
  the verdict slot, chained through named banks
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- **The canonical successor, with the result bank named.** `Tape.HasBinaryNat` determines a
tape outright, so the library's contract — which reports the new value rather than the new tape —
can be sharpened to a pinned one, which is what the chaining rules consume. -/
theorem binarySuccTM_hoareTime_pinned (idx : Fin n) (value : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : work₀ idx = natTape value)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    (binarySuccTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧
        work = Function.update work₀ idx (natTape (value + 1)) ∧ out = out₀)
      (binarySuccTime value) := by
  have hbn : (work₀ idx).HasBinaryNat value := by
    rw [hvalue]; exact Tape.init_move_right_hasBinaryNat value
  refine (binarySuccTM_hoareTime_frame idx value inp₀ work₀ out₀ hbn hinp hother
    hout).strengthen_post ?_
  rintro inp work out ⟨rfl, hkeep, hnew, rfl⟩
  refine ⟨rfl, funext fun j => ?_, rfl⟩
  by_cases hj : j = idx
  · subst hj
    rw [Function.update_self]
    simpa [natTape] using hnew.eq_init_move_right
  · rw [Function.update_of_ne hj]
    exact hkeep j hj

/-- **Bump one of two registers, according to the verdict already in the output slot.** The test
stage is `TM.skipTM`: the verdict is published before the branch is reached, so the conditional
has nothing left to compute. -/
def condBumpTM (aIdx rIdx : Fin n) : TM n :=
  ifTM skipTM (binarySuccTM aIdx) (binarySuccTM rIdx)


/-- **The conditional bump's contract.** The verdict `b` sitting in the output slot selects which
register grows; the slot itself is untouched, since the branch reads it and nothing writes it. -/
theorem condBumpTM_hoareTime (aIdx rIdx : Fin n) (a r : ℕ) (b : Bool) (s : Γw)
    (hb : s = Γw.one ↔ b = true)
    (I : Tape) (W : Fin n → Tape)
    (hI : Parked I) (hIz : I.cells 0 = Γ.start)
    (hW : ∀ j, Parked (W j)) (hWz : ∀ j, (W j).cells 0 = Γ.start)
    (ha : W aIdx = natTape a) (hr : W rIdx = natTape r) :
    (condBumpTM aIdx rIdx).HoareTime
      (fun inp work out => inp = I ∧ work = W ∧ out = NTM.outSlot s)
      (fun inp work out => inp = I ∧
        work = (if b then Function.update W aIdx (natTape (a + 1))
                 else Function.update W rIdx (natTape (r + 1))) ∧
        out = NTM.outSlot s)
      (1 + 1 + max (binarySuccTime a) (binarySuccTime r) + 5) := by
  set O := NTM.outSlot s with hO
  have hOP : Parked O := NTM.outSlot_parked _
  have hOne : O.cells 1 = Γ.one ↔ b = true := by
    rw [hO, NTM.outSlot_cells_one_eq_one_iff]
    exact hb
  have hIdW : ∀ i, transitionTape (W i) = W i :=
    fun i => transitionTape_eq_self (hW i).read_ne_start
  have hIdI : transitionInput I = I := transitionInput_eq_self hI.read_ne_start
  have hIdO : transitionTape O = O := transitionTape_eq_self hOP.read_ne_start
  have hOfix : (⟨1, O.cells⟩ : Tape) = O := Tape.ext rfl rfl
  refine ifTM_hoareTime skipTM (binarySuccTM aIdx) (binarySuccTM rIdx)
    (mid_then := fun inp work out => b = true ∧ (inp = I ∧ work = W ∧ out = O))
    (mid_else := fun inp work out => b = false ∧ (inp = I ∧ work = W ∧ out = O))
    (post_then := fun inp work out => b = true ∧
      (inp = I ∧ work = Function.update W aIdx (natTape (a + 1)) ∧ out = O))
    (post_else := fun inp work out => b = false ∧
      (inp = I ∧ work = Function.update W rIdx (natTape (r + 1)) ∧ out = O))
    (p_bound := 1)
    (skipTM_hoareTime_frame I W O hI hW hOP) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨hIz, fun j hj => hI.2 j hj, hWz, fun i j hj => (hW i).2 j hj,
      by rw [hO]; rfl, fun j hj => hOP.2 j hj⟩
  · rintro inp work out ⟨rfl, rfl, rfl⟩
    exact le_of_eq rfl
  · rintro inp work out ⟨rfl, rfl, rfl⟩ hone
    exact ⟨hOne.mp hone, hIdI, funext hIdW, hOfix⟩
  · rintro inp work out ⟨rfl, rfl, rfl⟩ hne
    refine ⟨?_, hIdI, funext hIdW, hOfix⟩
    cases b
    · rfl
    · exact absurd (hOne.mpr rfl) hne
  · intro inp work out h
    obtain ⟨hb, hpre⟩ := h
    obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ :=
      binarySuccTM_hoareTime_pinned aIdx a I W O ha hI.read_ne_start
        (fun i _ => (hW i).read_ne_start) hOP.read_ne_start inp work out hpre
    exact ⟨c', t, ht, hreach, hhalt, hb, hpost⟩
  · intro inp work out h
    obtain ⟨hb, hpre⟩ := h
    obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ :=
      binarySuccTM_hoareTime_pinned rIdx r I W O hr hI.read_ne_start
        (fun i _ => (hW i).read_ne_start) hOP.read_ne_start inp work out hpre
    exact ⟨c', t, ht, hreach, hhalt, hb, hpost⟩
  · rintro inp work out ⟨hb, rfl, rfl, rfl⟩
    refine ⟨hIdI, ?_, hIdO⟩
    rw [ite_eq_left hb]
    funext i
    exact transitionTape_eq_self (by
      by_cases hi : i = aIdx
      · subst hi
        rw [Function.update_self]
        exact (natTape_parked _).read_ne_start
      · rw [Function.update_of_ne hi]; exact (hW i).read_ne_start)
  · rintro inp work out ⟨hb, rfl, rfl, rfl⟩
    refine ⟨hIdI, ?_, hIdO⟩
    rw [ite_eq_right (by simp [hb])]
    funext i
    exact transitionTape_eq_self (by
      by_cases hi : i = rIdx
      · subst hi
        rw [Function.update_self]
        exact (natTape_parked _).read_ne_start
      · rw [Function.update_of_ne hi]; exact (hW i).read_ne_start)


/-- **The arithmetic end of the loop body.** Bump the selected tally, bump the count, and blank
the verdict slot so the next pass starts from the state the loop's invariant describes. -/
def tallyBumpTM (cIdx aIdx rIdx zIdx : Fin n) : TM n :=
  bigSeqTM [condBumpTM aIdx rIdx, binarySuccTM cIdx, writeOutputBitTM zIdx]

/-- **The arithmetic end of the loop body, contracted.** Every intermediate bank is named, so the
three stages chain through `TM.bigSeqTM_hoareTime_pinned` with no existential in sight. -/
theorem tallyBumpTM_hoareTime (cIdx aIdx rIdx zIdx : Fin n)
    (hca : cIdx ≠ aIdx) (hcr : cIdx ≠ rIdx)
    (hzc : zIdx ≠ cIdx) (hza : zIdx ≠ aIdx) (hzr : zIdx ≠ rIdx)
    (v a r : ℕ) (b : Bool) (s : Γw) (hb : s = Γw.one ↔ b = true)
    (I : Tape) (W : Fin n → Tape)
    (hI : Parked I) (hIz : I.cells 0 = Γ.start)
    (hW : ∀ j, Parked (W j)) (hWz : ∀ j, (W j).cells 0 = Γ.start)
    (hcv : W cIdx = natTape v) (ha : W aIdx = natTape a) (hr : W rIdx = natTape r)
    (hz : (W zIdx).read = Γ.blank) :
    (tallyBumpTM cIdx aIdx rIdx zIdx).HoareTime
      (fun inp work out => inp = I ∧ work = W ∧ out = NTM.outSlot s)
      (fun inp work out => inp = I ∧
        work = Function.update
          (if b then Function.update W aIdx (natTape (a + 1))
           else Function.update W rIdx (natTape (r + 1))) cIdx (natTape (v + 1)) ∧
        out = NTM.outSlot Γw.blank)
      (3 * (max (1 + 1 + max (binarySuccTime a) (binarySuccTime r) + 5)
        (binarySuccTime v) + 1) + 1) := by
  set W₁ := if b then Function.update W aIdx (natTape (a + 1))
    else Function.update W rIdx (natTape (r + 1)) with hW₁
  set W₂ := Function.update W₁ cIdx (natTape (v + 1)) with hW₂
  set O := NTM.outSlot s with hO
  have hW₁P : ∀ j, Parked (W₁ j) := by
    intro j
    rw [hW₁]
    split
    · by_cases hj : j = aIdx
      · rw [hj, Function.update_self]; exact natTape_parked _
      · rw [Function.update_of_ne hj]; exact hW j
    · by_cases hj : j = rIdx
      · rw [hj, Function.update_self]; exact natTape_parked _
      · rw [Function.update_of_ne hj]; exact hW j
  have hW₁z : ∀ j, (W₁ j).cells 0 = Γ.start := by
    intro j
    rw [hW₁]
    split
    · by_cases hj : j = aIdx
      · rw [hj, Function.update_self]; exact NTM.natTape_cells_zero _
      · rw [Function.update_of_ne hj]; exact hWz j
    · by_cases hj : j = rIdx
      · rw [hj, Function.update_self]; exact NTM.natTape_cells_zero _
      · rw [Function.update_of_ne hj]; exact hWz j
  have hW₁c : W₁ cIdx = natTape v := by
    rw [hW₁]
    split
    · rw [Function.update_of_ne hca]; exact hcv
    · rw [Function.update_of_ne hcr]; exact hcv
  have hW₁z' : (W₁ zIdx).read = Γ.blank := by
    rw [hW₁]
    split
    · rw [Function.update_of_ne hza]; exact hz
    · rw [Function.update_of_ne hzr]; exact hz
  have hW₂P : ∀ j, Parked (W₂ j) := by
    intro j
    rw [hW₂]
    by_cases hj : j = cIdx
    · rw [hj, Function.update_self]; exact natTape_parked _
    · rw [Function.update_of_ne hj]; exact hW₁P j
  have hW₂z : (W₂ zIdx).read = Γ.blank := by
    rw [hW₂, Function.update_of_ne hzc]; exact hW₁z'
  have hOP : Parked O := NTM.outSlot_parked _
  have hObP : Parked (NTM.outSlot Γw.blank) := NTM.outSlot_parked _
  refine (bigSeqTM_hoareTime_pinned
    [condBumpTM aIdx rIdx, binarySuccTM cIdx, writeOutputBitTM zIdx]
    I (fun k => if k = 0 then W else if k = 1 then W₁ else W₂)
    (fun k => if k ≤ 2 then O else NTM.outSlot Γw.blank)
    (max (1 + 1 + max (binarySuccTime a) (binarySuccTime r) + 5) (binarySuccTime v))
    hI ?_ ?_ ?_).consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (le_refl _)
  · intro k i
    split
    · exact hW i
    · split
      · exact hW₁P i
      · exact hW₂P i
  · intro k
    split
    · exact hOP
    · exact hObP
  · intro k hk
    match k, hk with
    | 0, _ =>
      show (condBumpTM aIdx rIdx).HoareTime _ _ _
      exact (condBumpTM_hoareTime aIdx rIdx a r b s hb I W hI hIz hW hWz ha hr).mono_bound
        (le_max_left _ _)
    | 1, _ =>
      show (binarySuccTM cIdx).HoareTime _ _ _
      exact (binarySuccTM_hoareTime_pinned cIdx v I W₁ O hW₁c hI.read_ne_start
        (fun i _ => (hW₁P i).read_ne_start) hOP.read_ne_start).mono_bound (le_max_right _ _)
    | 2, _ =>
      show (writeOutputBitTM zIdx).HoareTime _ _ _
      refine ((writeOutputBitTM_hoareTime_frame zIdx I W₂ O hI hW₂P hOP).strengthen_post
        ?_).mono_bound (le_trans (by omega) (le_max_left _ _))
      rintro inp work out ⟨rfl, rfl, rfl⟩
      refine ⟨rfl, rfl, ?_⟩
      rw [hW₂z]
      show O.write (readBackWrite Γ.blank).toΓ = _
      rw [hO]
      exact NTM.outSlot_write _ Γw.blank


/-- **Truncated subtraction, with the result bank named.** As with the successor, the library
reports the new *values*; since `Tape.HasBinaryNat` determines a tape, the operands come back
literally unchanged and only the result register moves. -/
theorem binaryRippleSubTM_hoareTime_pinned (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleSubDistinct lhsIdx rhsIdx resultIdx) (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : work₀ lhsIdx = natTape lhs) (hrhs : work₀ rhsIdx = natTape rhs)
    (hres : (work₀ resultIdx).HasBinaryNat 0)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx → Parked (work₀ i))
    (houtput : Parked out₀) :
    (binaryRippleSubTM lhsIdx rhsIdx resultIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧
        work = Function.update work₀ resultIdx (natTape (lhs - rhs)) ∧ out = out₀)
      (binaryRippleSubTime lhs rhs) := by
  have hbl : (work₀ lhsIdx).HasBinaryNat lhs := by
    rw [hlhs]; exact Tape.init_move_right_hasBinaryNat lhs
  have hbr : (work₀ rhsIdx).HasBinaryNat rhs := by
    rw [hrhs]; exact Tape.init_move_right_hasBinaryNat rhs
  refine (binaryRippleSubTM_hoareTime_frame lhsIdx rhsIdx resultIdx hdistinct lhs rhs
    inp₀ work₀ out₀ hbl hbr hres hinput hother houtput).strengthen_post ?_
  rintro inp work out ⟨hi, hl, hr, hd, hkeep, ho⟩
  refine ⟨hi, funext fun j => ?_, ho⟩
  by_cases hj : j = resultIdx
  · rw [hj, Function.update_self]
    simpa [natTape] using hd.eq_init_move_right
  by_cases hj1 : j = lhsIdx
  · rw [Function.update_of_ne hj, hj1, hlhs]
    simpa [natTape] using hl.eq_init_move_right
  by_cases hj2 : j = rhsIdx
  · rw [Function.update_of_ne hj, hj2, hrhs]
    simpa [natTape] using hr.eq_init_move_right
  · rw [Function.update_of_ne hj]
    exact hkeep j hj1 hj2 hj

end TM

end Complexity
