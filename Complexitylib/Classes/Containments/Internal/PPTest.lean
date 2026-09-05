/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PPParts
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryEq
public import Complexitylib.Models.TuringMachine.Subroutines.ResetBinary
public import Complexitylib.Models.TuringMachine.Subroutines.RewindList
public import Complexitylib.Models.TuringMachine.Subroutines.WipeRewind
public import Complexitylib.Models.TuringMachine.Combinators.Internal.SeqChain

/-!
# The counting loop's test

⚠️ Unreviewed by Bolton

`TM.loopTM` stops when its test machine leaves `1` in the output tape's verdict cell. The
counting loop stops when its counter reaches the horizon, so its test compares the counter
against a register holding that horizon and publishes the answer.

The comparison itself is `TM.binaryEqTM`, which deposits its verdict as a bit on a scratch work
tape and leaves the output alone; the remaining three stages move that bit where the loop can see
it. Two of them exist only because of where heads end up: `TM.binaryEqTM` leaves its operands'
heads wherever the scan stopped, and `TM.writeOutputBitTM` publishes whatever is *under* a head,
so the operands must be rewound before the verdict can be read off.

## Main results

- `TM.testTailTM` — rewind, publish the verdict, clear the scratch bit
- `TM.testTailTM_hoareTime` — its contract, through fully pinned tape states
- `TM.tallyTestTM`, `TM.tallyTestTM_hoareTime` — the whole test, leaving its bank as it found it
- `NTM.tallyTestTM_hoareTime_tallyPost` — the same contract in the shape
  `NTM.tallyLoop_hoareTime_of_hoare` asks for
- `TM.Parked.write_ne_start` — a frame fact the assembly needs
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- The three tapes the comparison touches, in the order the rewind visits them. -/
def testTargets (cIdx nIdx resIdx : Fin n) : List (Fin n) := [cIdx, nIdx, resIdx]

/-- The work bank after every compared tape has been rewound to cell one. -/
def rewoundBank (cIdx nIdx resIdx : Fin n) (W : Fin n → Tape) : Fin n → Tape := fun j =>
  if j ∈ testTargets cIdx nIdx resIdx then ⟨1, (W j).cells⟩ else W j

/-- **The tail of the counting loop's test.** Rewind the compared tapes, publish the scratch
bit onto the output, then clear the scratch tape for the next iteration. -/
def testTailTM (cIdx nIdx resIdx : Fin n) : TM n :=
  bigSeqTM [bigSeqTM ((testTargets cIdx nIdx resIdx).map rewindWorkTM),
    writeOutputBitTM resIdx, resetBinaryWorkTM resIdx]

theorem rewoundBank_parked {cIdx nIdx resIdx : Fin n} {W : Fin n → Tape}
    (hW : ∀ j, Parked (W j)) (j : Fin n) : Parked (rewoundBank cIdx nIdx resIdx W j) := by
  simp only [rewoundBank]
  split
  · exact ⟨le_refl 1, fun i hi => (hW j).2 i hi⟩
  · exact hW j


/-- Writing a non-marker symbol keeps a parked tape parked. -/
theorem Parked.write_ne_start {t : Tape} (h : Parked t) {s : Γ} (hs : s ≠ Γ.start) :
    Parked (t.write s) := by
  refine ⟨by rw [Tape.write_head]; exact h.1, fun j hj => ?_⟩
  rw [Tape.write]
  split
  · exact h.2 j hj
  · show Function.update t.cells t.head s j ≠ Γ.start
    by_cases hjt : j = t.head
    · rw [hjt, Function.update_self]; exact hs
    · rw [Function.update_of_ne hjt]; exact h.2 j hj

/-- **The contract of the test's tail.** From a bank in which the compared tapes carry their
markers and the scratch tape carries the verdict bit, the three stages land on a fully named bank
— every compared tape at cell one, the scratch tape blank — with the verdict on the output. -/
theorem testTailTM_hoareTime (cIdx nIdx resIdx : Fin n)
    (hd : BinaryEqDistinct cIdx nIdx resIdx) (b : Bool) (B : ℕ) (hB : 1 ≤ B)
    (I : Tape) (W : Fin n → Tape) (O : Tape)
    (hI : Parked I) (hO : Parked O) (hW : ∀ j, Parked (W j))
    (hstart : ∀ j, j ∈ testTargets cIdx nIdx resIdx →
      (W j).cells 0 = Γ.start ∧ (W j).head ≤ B)
    (hres : (W resIdx).cells 1 = Γ.ofBool b)
    (hresBlank : ∀ i, 2 ≤ i → (W resIdx).cells i = Γ.blank) :
    (testTailTM cIdx nIdx resIdx).HoareTime
      (fun inp work out => inp = I ∧ work = W ∧ out = O)
      (fun inp work out => inp = I ∧
        work = Function.update (rewoundBank cIdx nIdx resIdx W) resIdx
          ((Tape.init ([] : List Γ)).move Dir3.right) ∧
        out = O.write (Γ.ofBool b))
      (3 * (max (3 * (B + 3) + 1) (resetBinaryWorkTime B 1) + 1) + 1) := by
  have hnodup : (testTargets cIdx nIdx resIdx).Nodup := by
    have h1 := hd.lhs_rhs
    have h2 := hd.lhs_result
    have h3 := hd.rhs_result
    simp [testTargets, h1, h2, h3]
  have hresMem : resIdx ∈ testTargets cIdx nIdx resIdx := by simp [testTargets]
  set Wr := rewoundBank cIdx nIdx resIdx W with hWr
  have hWrP : ∀ j, Parked (Wr j) := rewoundBank_parked hW
  have hWrRes : Wr resIdx = ⟨1, (W resIdx).cells⟩ := by
    simp only [hWr, rewoundBank, ite_eq_left hresMem]
  have hofb : Γ.ofBool b ≠ Γ.start := by cases b <;> simp [Γ.ofBool]
  have hread : (Wr resIdx).read = Γ.ofBool b := by
    rw [hWrRes]; show (W resIdx).cells 1 = _; exact hres
  set Ow := O.write (Γ.ofBool b) with hOw
  have hOwP : Parked Ow := hO.write_ne_start hofb
  set Wf := Function.update Wr resIdx ((Tape.init ([] : List Γ)).move Dir3.right) with hWf
  have hWfP : ∀ j, Parked (Wf j) := by
    intro j
    by_cases hj : j = resIdx
    · rw [hj, hWf, Function.update_self]
      refine ⟨le_refl 1, fun i hi => ?_⟩
      rw [Tape.move_cells]
      show (if i = 0 then Γ.start else Γ.blank) ≠ Γ.start
      rw [ite_eq_right (by omega)]
      simp
    · rw [hWf, Function.update_of_ne hj]; exact hWrP j
  set bnd := max (3 * (B + 3) + 1) (resetBinaryWorkTime B 1) with hbnd
  refine (bigSeqTM_hoareTime_pinned
    [bigSeqTM ((testTargets cIdx nIdx resIdx).map rewindWorkTM),
      writeOutputBitTM resIdx, resetBinaryWorkTM resIdx]
    I (fun k => if k = 0 then W else if k ≤ 2 then Wr else Wf)
    (fun k => if k ≤ 1 then O else Ow) bnd hI ?_ ?_ ?_).consequence
    (fun _ _ _ h => h) (fun _ _ _ h => h) (le_refl _)
  · intro k i
    split
    · exact hW i
    · split
      · exact hWrP i
      · exact hWfP i
  · intro k
    split
    · exact hO
    · exact hOwP
  · intro k hk
    match k, hk with
    | 0, _ =>
      show (bigSeqTM ((testTargets cIdx nIdx resIdx).map rewindWorkTM)).HoareTime _ _ _
      refine ((rewindList_hoareTime (testTargets cIdx nIdx resIdx) hnodup B I W O hI hO hW
        hstart).strengthen_post ?_).mono_bound ?_
      · rintro inp work out ⟨rfl, rfl, hin, hout⟩
        refine ⟨rfl, funext fun j => ?_, rfl⟩
        by_cases hj : j ∈ testTargets cIdx nIdx resIdx
        · rw [hin j hj]; show _ = Wr j; rw [hWr, rewoundBank, ite_eq_left hj]
        · rw [hout j hj]; show _ = Wr j; rw [hWr, rewoundBank, ite_eq_right hj]
      · show 3 * (B + 3) + 1 ≤ bnd
        rw [hbnd]
        exact le_max_left _ _
    | 1, _ =>
      show (writeOutputBitTM resIdx).HoareTime _ _ _
      refine ((writeOutputBitTM_hoareTime_frame resIdx I Wr O hI hWrP hO).strengthen_post
        ?_).mono_bound (le_trans (by omega : (1 : ℕ) ≤ 3 * (B + 3) + 1) (le_max_left _ _))
      rintro inp work out ⟨rfl, rfl, rfl⟩
      refine ⟨rfl, rfl, ?_⟩
      show _ = Ow
      rw [hOw, hread, toΓ_readBackWrite_of_ne_start hofb]
    | 2, _ =>
      show (resetBinaryWorkTM resIdx).HoareTime _ _ _
      refine ((resetBinaryWorkTM_hoareTime_frame resIdx [b] B I Wr Ow ?_ ?_ ?_ hI ?_
        hOwP).strengthen_post ?_).mono_bound (le_max_right _ _)
      · refine ⟨fun i hi => ?_, fun i hi => ?_⟩
        · have : i = 0 := by simpa using hi
          subst this
          rw [hWrRes]; show (W resIdx).cells 1 = _; simpa using hres
        · rw [hWrRes]
          show (W resIdx).cells (i + 1) = _
          exact hresBlank (i + 1) (by simpa using hi)
      · rw [hWrRes]; show (W resIdx).cells 0 = _; exact (hstart resIdx hresMem).1
      · rw [hWrRes]; exact ⟨le_refl 1, hB⟩
      · intro i _; exact hWrP i
      · rintro inp work out ⟨rfl, rfl, rfl⟩
        exact ⟨rfl, rfl, rfl⟩


/-- **The counting loop's test.** Compare the counter against the horizon register, then move
the verdict where `TM.loopTM` looks for it. -/
def tallyTestTM (cIdx nIdx resIdx : Fin n) : TM n :=
  seqTM (binaryEqTM cIdx nIdx resIdx) (testTailTM cIdx nIdx resIdx)

/-- **The test's contract.** The bank comes back exactly as it went in — the comparison is
non-destructive and the scratch tape is cleared — and the output gains the verdict bit. -/
theorem tallyTestTM_hoareTime (cIdx nIdx resIdx : Fin n)
    (hd : BinaryEqDistinct cIdx nIdx resIdx) (v N B : ℕ)
    (I : Tape) (W : Fin n → Tape) (O : Tape)
    (hI : Parked I) (hIz : I.cells 0 = Γ.start)
    (hO : Parked O) (hOz : O.cells 0 = Γ.start)
    (hW : ∀ j, Parked (W j)) (hWz : ∀ j, (W j).cells 0 = Γ.start)
    (hc : W cIdx = natTape v) (hnn : W nIdx = natTape N)
    (hres : W resIdx = (Tape.init ([] : List Γ)).move Dir3.right)
    (hB : ∀ j, (W j).head + binaryEqTime v.bits N.bits ≤ B) :
    (tallyTestTM cIdx nIdx resIdx).HoareTime
      (fun inp work out => inp = I ∧ work = W ∧ out = O)
      (fun inp work out => inp = I ∧ work = W ∧
        out = O.write (Γ.ofBool (decide (v = N))))
      (binaryEqTime v.bits N.bits + 1 +
        (3 * (max (3 * (B + 3) + 1) (resetBinaryWorkTime B 1) + 1) + 1)) := by
  have hB1 : 1 ≤ B := le_trans (hW cIdx).1 (le_trans (Nat.le_add_right _ _) (hB cIdx))
  have hSI : ∀ j, (W j).StartInvariant := fun j => ⟨hWz j, fun i hi => (hW j).2 i hi⟩
  have hbits : (decide (v.bits = N.bits)) = decide (v = N) := by
    by_cases h : v = N
    · simp [h]
    · simp only [h, decide_false, decide_eq_false_iff_not]
      exact fun hcon => h (bits_injective hcon)
  set mid : TapePred n := fun inp work out => inp = I ∧ out = O ∧
    (∀ j, Parked (work j)) ∧ (∀ j, (work j).cells 0 = Γ.start) ∧
    (∀ j, (work j).head ≤ B) ∧
    (work cIdx).HasBinaryContent v.bits ∧ (work nIdx).HasBinaryContent N.bits ∧
    (work resIdx).cells 1 = Γ.ofBool (decide (v = N)) ∧
    (∀ i, 2 ≤ i → (work resIdx).cells i = Γ.blank) ∧
    (∀ j, j ≠ cIdx → j ≠ nIdx → j ≠ resIdx → work j = W j) with hmid
  -- The comparison itself.
  have hstep1 : (binaryEqTM cIdx nIdx resIdx).HoareTime
      (fun inp work out => inp = I ∧ work = W ∧ out = O) mid
      (binaryEqTime v.bits N.bits) := by
    intro inp work out hpre
    obtain ⟨hEi, hEw, hEo⟩ := hpre
    rw [hEi, hEw, hEo]
    have hlhs : (W cIdx).HasBinaryString v.bits := by
      rw [hc]; exact (Tape.init_move_right_hasBinaryNat v).2
    have hrhs : (W nIdx).HasBinaryString N.bits := by
      rw [hnn]; exact (Tape.init_move_right_hasBinaryNat N).2
    have hprefix : (W resIdx).HasBinaryPrefix [] := by
      refine ⟨by rw [hres]; rfl, nofun, fun i _ => ?_⟩
      rw [hres, Tape.move_cells]
      show (if i + 1 = 0 then Γ.start else Γ.blank) = Γ.blank
      rw [ite_eq_right (by omega)]
    obtain ⟨c', t, ht, hreach, hhalt, hinp', hres', hlhs', hlhsh, hrhs', hrhsh, hother',
      hout'⟩ :=
      binaryEqTM_reachesIn_frame cIdx nIdx resIdx hd v.bits N.bits I W O hlhs hrhs hprefix
        hI.read_ne_start (fun i _ _ _ => (hW i).read_ne_start) hO.read_ne_start
    obtain ⟨-, hSI', -⟩ := startInvariant_reachesIn _ hreach ⟨hIz, fun i hi => hI.2 i hi⟩ hSI
      ⟨hOz, fun i hi => hO.2 i hi⟩
    obtain ⟨-, -, hheads⟩ := head_le_start_add_of_reachesIn _ hreach
    have hheadB : ∀ j, (c'.work j).head ≤ B := by
      intro j
      have h1 : (c'.work j).head ≤ (W j).head + t := hheads j
      have h2 := hB j
      omega
    have hge1 : ∀ j, 1 ≤ (c'.work j).head := by
      intro j
      by_cases hj : j = cIdx
      · subst hj; exact hlhsh
      · by_cases hj2 : j = nIdx
        · subst hj2; exact hrhsh
        · by_cases hj3 : j = resIdx
          · subst hj3; rw [hres'.1]; omega
          · rw [hother' j hj hj2 hj3]; exact (hW j).1
    refine ⟨c', t, ht, hreach, hhalt, ?_⟩
    refine ⟨hinp', hout', fun j => ⟨hge1 j, fun i hi => (hSI' j).2 i hi⟩,
      fun j => (hSI' j).1, hheadB, hlhs', hrhs', ?_, ?_, fun j h1 h2 h3 => hother' j h1 h2 h3⟩
    · have hz := hres'.2.1 0 (by simp)
      simpa [hbits] using hz
    · intro i hi
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      exact hres'.2.2 k (by simpa using hi)
  -- Phase transitions do not disturb parked tapes.
  have htrans : ∀ inp work out, mid inp work out →
      mid (transitionInput inp) (fun i => transitionTape (work i)) (transitionTape out) := by
    intro inp work out h
    obtain ⟨hEi, hEo, hp, hz, hh, h1, h2, h3, h4, h5⟩ := h
    have heq : ∀ j, transitionTape (work j) = work j :=
      fun j => transitionTape_eq_self (hp j).read_ne_start
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hEi]; exact transitionInput_eq_self hI.read_ne_start
    · rw [hEo]; exact transitionTape_eq_self hO.read_ne_start
    · intro j; show Parked (transitionTape (work j)); rw [heq j]; exact hp j
    · intro j; show (transitionTape (work j)).cells 0 = _; rw [heq j]; exact hz j
    · intro j; show (transitionTape (work j)).head ≤ _; rw [heq j]; exact hh j
    · show (transitionTape (work cIdx)).HasBinaryContent _; rw [heq cIdx]; exact h1
    · show (transitionTape (work nIdx)).HasBinaryContent _; rw [heq nIdx]; exact h2
    · show (transitionTape (work resIdx)).cells 1 = _; rw [heq resIdx]; exact h3
    · intro i hi; show (transitionTape (work resIdx)).cells i = _; rw [heq resIdx]
      exact h4 i hi
    · intro j a b c; show transitionTape (work j) = _; rw [heq j]; exact h5 j a b c
  -- The tail, applied at the unpinned bank the comparison produced.
  have hstep2 : (testTailTM cIdx nIdx resIdx).HoareTime mid
      (fun inp work out => inp = I ∧ work = W ∧
        out = O.write (Γ.ofBool (decide (v = N))))
      (3 * (max (3 * (B + 3) + 1) (resetBinaryWorkTime B 1) + 1) + 1) := by
    intro inp work out h
    obtain ⟨hEi, hEo, hp, hz, hh, h1, h2, h3, h4, h5⟩ := h
    rw [hEi, hEo]
    refine (testTailTM_hoareTime cIdx nIdx resIdx hd (decide (v = N)) B hB1 I work O hI hO hp
      (fun j _ => ⟨hz j, hh j⟩) h3 h4).strengthen_post
      (post' := fun inp work out => inp = I ∧ work = W ∧
        out = O.write (Γ.ofBool (decide (v = N)))) ?_ I work O ⟨rfl, rfl, rfl⟩
    rintro inp' work' out' ⟨rfl, hwf, rfl⟩
    refine ⟨rfl, ?_, rfl⟩
    rw [hwf]
    funext j
    by_cases hj : j = resIdx
    · subst hj
      rw [Function.update_self, hres]
    rw [Function.update_of_ne hj]
    by_cases hj1 : j = cIdx
    · subst hj1
      have hmem : j ∈ testTargets j nIdx resIdx := by simp [testTargets]
      rw [rewoundBank, ite_eq_left hmem, hc]
      have hbn : (⟨1, (work j).cells⟩ : Tape).HasBinaryNat v := ⟨hz j, rfl, h1.1, h1.2⟩
      simpa [natTape] using hbn.eq_init_move_right
    by_cases hj2 : j = nIdx
    · subst hj2
      have hmem : j ∈ testTargets cIdx j resIdx := by simp [testTargets]
      rw [rewoundBank, ite_eq_left hmem, hnn]
      have hbn : (⟨1, (work j).cells⟩ : Tape).HasBinaryNat N := ⟨hz j, rfl, h2.1, h2.2⟩
      simpa [natTape] using hbn.eq_init_move_right
    have hmem : j ∉ testTargets cIdx nIdx resIdx := by
      simp only [testTargets, List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => h.elim hj1 (fun h => h.elim hj2 hj)
    rw [rewoundBank, ite_eq_right hmem]
    exact h5 j hj1 hj2 hj
  exact seqTM_hoareTime _ _ hstep1 htrans hstep2

end TM

namespace NTM

variable {n : ℕ}

/-- **Writing into the verdict slot replaces its symbol.** The slot's head never leaves cell one,
so a write lands exactly on the cell `TM.loopTM` inspects. -/
theorem outSlot_write (s s' : Γw) : (outSlot s).write s'.toΓ = outSlot s' := by
  refine Tape.ext ?_ ?_
  · rw [Tape.write_head]
    rfl
  · funext j
    rw [Tape.write, ite_eq_right (show ¬ ((outSlot s).head = 0) from by
      show ¬ ((1 : ℕ) = 0); omega)]
    show Function.update (outSlot s).cells 1 s'.toΓ j = _
    by_cases hj : j = 1
    · subst hj
      rw [Function.update_self]
      simp [outSlot]
    · rw [Function.update_of_ne hj]
      simp [outSlot, hj]

/-- Writing the verdict into a blank slot produces the slot holding that verdict. -/
theorem outSlot_blank_write (b : Bool) :
    (outSlot Γw.blank).write (Γ.ofBool b) = outSlot (if b then Γw.one else Γw.zero) := by
  have h : Γ.ofBool b = (if b then Γw.one else Γw.zero).toΓ := by
    cases b <;> simp [Γ.ofBool, Γw.toΓ]
  rw [h, outSlot_write]

/-- The blank verdict slot is the blank tape — the same object under two names, which is what
lets the wipe's precondition and the loop's invariant meet. -/
theorem outSlot_blank_eq_blankTape : outSlot Γw.blank = TM.blankTape := by
  refine Tape.ext rfl (funext fun j => ?_)
  show (if j = 0 then Γ.start else if j = 1 then Γw.blank.toΓ else Γ.blank)
    = ((Tape.init ([] : List Γ)).move Dir3.right).cells j
  rw [Tape.move_cells]
  by_cases hj : j = 0
  · rw [hj, ite_eq_left rfl, Tape.init_cells_zero]
  · rw [ite_eq_right hj, show j = (j - 1) + 1 from by omega, Tape.init_nil_cells_succ]
    split <;> rfl

/-- Reading a cell back as a writable symbol turns it into `1` exactly when it was `1`. -/
theorem readBackWrite_eq_one_iff (s : Γ) : TM.readBackWrite s = Γw.one ↔ s = Γ.one := by
  cases s <;> simp [TM.readBackWrite]

/-- **The body's publishing stage.** With the verdict tape rewound to cell one, its symbol is
copied into the output slot, where `TM.ifTM` can branch on it. -/
theorem publish_hoareTime {n : ℕ} (idx : Fin n) (I : Tape) (W : Fin n → Tape)
    (hI : TM.Parked I) (hW : ∀ j, TM.Parked (W j)) (hv : (W idx).head = 1) :
    (TM.writeOutputBitTM idx).HoareTime
      (fun inp work out => inp = I ∧ work = W ∧ out = TM.blankTape)
      (fun inp work out => inp = I ∧ work = W ∧
        out = outSlot (TM.readBackWrite ((W idx).cells 1)))
      1 := by
  have hblank : TM.Parked TM.blankTape := TM.blankTape_parked
  have hread : (W idx).read = (W idx).cells 1 := by
    show (W idx).cells ((W idx).head) = _
    rw [hv]
  refine (TM.writeOutputBitTM_hoareTime_frame idx I W TM.blankTape hI hW hblank).strengthen_post ?_
  rintro inp work out ⟨hi, hw, ho⟩
  refine ⟨hi, hw, ?_⟩
  rw [ho, hread, ← outSlot_blank_eq_blankTape]
  exact outSlot_write Γw.blank (TM.readBackWrite ((W idx).cells 1))

/-- The marker sits at cell zero of a counter tape. -/
theorem natTape_cells_zero (v : ℕ) : (natTape v).cells 0 = Γ.start := by
  rw [natTape, Tape.move_cells]
  exact (Tape.init_move_right_hasBinaryNat v).1

/-- **The counting loop's test meets its obligation.** With the horizon parked on `nIdx` and a
blank scratch tape on `resIdx`, `TM.tallyTestTM` carries the state the body leaves — the bank at
index `w` and a blank verdict slot — to `NTM.tallyPost` at that index. -/
theorem tallyTestTM_hoareTime_tallyPost (cIdx aIdx rIdx nIdx resIdx : Fin n)
    (hd : TM.BinaryEqDistinct cIdx nIdx resIdx)
    (hnc : nIdx ≠ cIdx) (hna : nIdx ≠ aIdx) (hnr : nIdx ≠ rIdx)
    (hsc : resIdx ≠ cIdx) (hsa : resIdx ≠ aIdx) (hsr : resIdx ≠ rIdx)
    (I : Tape) (rest : Fin n → Tape) (P : ℕ → Bool) (N w B Hr : ℕ)
    (hI : TM.Parked I) (hIz : I.cells 0 = Γ.start)
    (hrest : ∀ j, TM.Parked (rest j)) (hrestz : ∀ j, (rest j).cells 0 = Γ.start)
    (hresth : ∀ j, (rest j).head ≤ Hr)
    (hn : rest nIdx = natTape N)
    (hr : rest resIdx = (Tape.init ([] : List Γ)).move Dir3.right)
    (hB : Hr + 1 + TM.binaryEqTime w.bits N.bits ≤ B) :
    (TM.tallyTestTM cIdx nIdx resIdx).HoareTime
      (fun inp work out => inp = I ∧
        work = tallyWork cIdx aIdx rIdx rest (w, tally P w, tally (fun u => !P u) w) ∧
        out = outSlot Γw.blank)
      (tallyPost cIdx aIdx rIdx I rest P N w)
      (TM.binaryEqTime w.bits N.bits + 1 +
        (3 * (max (3 * (B + 3) + 1) (TM.resetBinaryWorkTime B 1) + 1) + 1)) := by
  set W := tallyWork cIdx aIdx rIdx rest (w, tally P w, tally (fun u => !P u) w) with hW
  have hWc : W cIdx = natTape w := by rw [hW]; simp [tallyWork]
  have hWn : W nIdx = natTape N := by
    rw [hW]
    simp only [tallyWork, ite_eq_right hnc, ite_eq_right hna, ite_eq_right hnr]
    exact hn
  have hWr : W resIdx = (Tape.init ([] : List Γ)).move Dir3.right := by
    rw [hW]
    simp only [tallyWork, ite_eq_right hsc, ite_eq_right hsa, ite_eq_right hsr]
    exact hr
  have hcases : ∀ j, W j = natTape w ∨ W j = natTape (tally P w) ∨
      W j = natTape (tally (fun u => !P u) w) ∨ W j = rest j := by
    intro j
    rw [hW]
    simp only [tallyWork]
    split
    · exact Or.inl rfl
    · split
      · exact Or.inr (Or.inl rfl)
      · split
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
  have hWP : ∀ j, TM.Parked (W j) := by
    intro j
    rcases hcases j with h | h | h | h <;> rw [h]
    exacts [natTape_parked _, natTape_parked _, natTape_parked _, hrest j]
  have hWz : ∀ j, (W j).cells 0 = Γ.start := by
    intro j
    rcases hcases j with h | h | h | h <;> rw [h]
    exacts [natTape_cells_zero _, natTape_cells_zero _, natTape_cells_zero _, hrestz j]
  have hWh : ∀ j, (W j).head + TM.binaryEqTime w.bits N.bits ≤ B := by
    intro j
    have hj : (W j).head ≤ Hr + 1 := by
      rcases hcases j with h | h | h | h
      · rw [h]; show 1 ≤ Hr + 1; omega
      · rw [h]; show 1 ≤ Hr + 1; omega
      · rw [h]; show 1 ≤ Hr + 1; omega
      · rw [h]; have := hresth j; omega
    omega
  refine (TM.tallyTestTM_hoareTime cIdx nIdx resIdx hd w N B I W (outSlot Γw.blank)
    hI hIz (outSlot_parked _) rfl hWP hWz hWc hWn hWr hWh).strengthen_post ?_
  rintro inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨rfl, rfl, ?_⟩
  rw [outSlot_blank_write]
  congr 1
  by_cases h : w = N <;> simp [h]

end NTM

end Complexity
