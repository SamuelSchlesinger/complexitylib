/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Combinators.Internal.RetargetWindow
public import Complexitylib.Models.TuringMachine.Combinators.Internal.SeqChain
public import Complexitylib.Models.TuringMachine.Combinators.Internal.LoopIndexed
public import Complexitylib.Models.TuringMachine.Delay
public import Complexitylib.Models.TuringMachine.Combinators.Internal.LoopIteration
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Window
public import Complexitylib.Models.TuringMachine.ChoiceTape
public import Complexitylib.Models.TuringMachine.Tape.Encoding
public import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc
public import Complexitylib.Models.TuringMachine.Subroutines.WriteOutputBit
public import Complexitylib.Classes.Randomized
public import Complexitylib.Classes.FiniteCounting
public import Complexitylib.Classes.Containments.Internal.WitnessEnum

/-!
# Parts of the path-counting machine

⚠️ Unreviewed by Bolton

The machine that will witness `PP ⊆ PSPACE` enumerates choice sequences, runs one path of the
probabilistic machine along each, and keeps a running count. Its inner call is
`NTM.choiceTM`, which is *time*-bounded rather than space-bounded: every path halts within the
protocol's own time bound, so the window follows from `TM.keepsWindowOn_of_haltsIn` with no space
hypothesis at all. That is simpler than the corresponding step for `PH ⊆ PSPACE`, whose inner
call is only space-bounded.

## An architectural constraint on the body

The body must clear the simulated machine's work tapes between iterations, and the only
content-agnostic reset available is `TM.resetTapesTM`, whose wipe phase (`TM.wipeLoop_hoareTime`)
*requires the real output tape blank*. The rewind phase (`TM.rewindList_hoareTime`) does not — it
asks only that the output be `TM.Parked`.

That rules out the obvious design. `TM.ifTM` branches on the real output tape's verdict cell, so
using the simulation as a conditional's test would leave the verdict sitting on the output and
block the next iteration's wipe; and there is no subroutine that clears the output tape. The
verdict therefore has to be written to a *work* tape — the simulation output-retargeted, as in
`NTM.choiceTM_placed_keepsWindow` — and republished on the output only for the moment the branch
needs it. `TM.writeOutputBitTM` is the one-transition subroutine that does the republishing; the
library had no way to move a bit from a work tape to the output, which is why the constraint
above looked fatal.

## Main results

- `NTM.acceptCount_add`, `NTM.mem_iff_polyHorizon` — the comparison is stable under enlarging
  the horizon, so the machine may use a polynomial bound in place of the protocol's own
  (uncomputable) time function
- `hasBinaryString_unique`, `hasBinaryNat_value_unique` — a binary tape determines its contents
- `tallyState`, `tallyIdx`, `tallyIdx_tallyState` — the counting machine's tape state, and the
  index read back off it
- `natTape`, `tallyWork`, `tallyState_iff` — that state, fully pinned
- `binarySucc_tallyState`, `binarySucc_tallyState_counter`, `binarySucc_tallyState_rej` — the
  three increment stages, from the library's canonical successor
- `NTM.choiceStream_of_hasBinaryString`, `NTM.choiceStream_eq_choicesOfNat` — a binary counter
  tape *is* the choice sequence of its value
- `NTM.choiceTM_choiceCells` — the path simulation leaves the counter's digits alone
- `NTM.choiceTM_dropChoice_eq`, `NTM.choiceTM_verdict` — what the simulation computes from a
  counter value, and that its verdict is the enumeration's acceptance test
- `NTM.choiceTM_haltsIn` — a path simulation halts within the protocol's time bound
- `NTM.choiceTM_keepsWindowOn` — and therefore keeps a window
- `NTM.choiceTM_placed_keepsWindow`, `NTM.choiceTM_lifted_keepsWindow` — and so does the call
  once placed in the larger machine, with or without output retargeting
- `natTape_parked` — the numeric tapes satisfy the side condition the reset subroutines demand
- `NTM.acceptCount_eq_card_range` — the accepting-path count is a count over counter values
- `NTM.tally`, `NTM.tally_eq_card` — the running accumulation computes that count
- `NTM.mem_iff_two_mul_tally` — what the counting machine decides
- `NTM.tally_add_compl`, `NTM.lt_two_mul_tally_iff`, `NTM.mem_iff_tally_lt_tally` — and the same
  as a comparison of two counters, so the machine never forms `2 ^ T`
- `NTM.acceptsAt`, `NTM.mem_iff_tally_lt_tally_poly` — **the complete machine specification**
- `NTM.tallyStep`, `NTM.tallyStep_iterate` — the loop invariant on (counter, accepting tally,
  rejecting tally)
- `NTM.mem_iff_iterate_tallyStep` — membership as one iterated function and a comparison
- `NTM.outSlot`, `NTM.tallyPre`, `NTM.tallyPost`, `NTM.tallyLoop_hoareTime_of_hoare` — the
  counting loop from a Hoare contract for the body and one for the test, chained through fully
  pinned tape states, which is the interface a machine construction meets
- `NTM.tallyLoop_keepsWindow_of_hoare` — the same loop's space bound, one iteration wide
- `NTM.delayNTM_char`, `NTM.acceptCount_eq_zero_of_qstart_eq_qhalt`,
  `NTM.not_mem_of_qstart_eq_qhalt` — the `PP` characterisation transported to
  the delayed machine, and the degenerate case that licenses it
- `NTM.choiceTM_delay_dropChoice_eq`, `NTM.choiceTM_delay_haltsIn` — what the loop body's
  simulation computes, entered where a composed machine can enter it
- `NTM.tally_eq_acceptCount`, `NTM.tally_cmp_iff` — the tally is the accepting count
- `NTM.cmp_horizon_iff`, `NTM.cmp_horizon_iff'` — the `PP` comparison does not depend on the
  horizon, past the point where every path has halted
- `NTM.tallyLoop_hoareTime`, `NTM.tallyLoop_hoareTime_of_body` — the counting loop, granted only
  that the body advances the triple
-/

@[expose] public section

namespace Complexity

/-! ## A binary tape determines its contents

The indexed loop rule reads the iteration count back off the tapes, so the counter's encoding has
to be unambiguous. It is: a tape's digits are pinned cell by cell and the first blank marks the
end, so two representations on the same tape coincide. -/

/-- A tape carries at most one binary string. -/
theorem hasBinaryString_unique {t : Tape} {b b' : List Bool}
    (h : t.HasBinaryString b) (h' : t.HasBinaryString b') : b = b' := by
  obtain ⟨-, hin, hout⟩ := h
  obtain ⟨-, hin', hout'⟩ := h'
  have hlen : b.length = b'.length := by
    by_contra hne
    rcases Nat.lt_or_ge b.length b'.length with hlt | hge
    · have h1 := hout b.length le_rfl
      have h2 := hin' b.length hlt
      rw [h1] at h2
      revert h2
      cases b'[b.length] <;> simp [Γ.ofBool]
    · have hlt' : b'.length < b.length := by omega
      have h1 := hout' b'.length le_rfl
      have h2 := hin b'.length hlt'
      rw [h1] at h2
      revert h2
      cases b[b'.length] <;> simp [Γ.ofBool]
  refine List.ext_getElem hlen fun i h1 h2 => ?_
  have e1 := hin i h1
  have e2 := hin' i h2
  rw [e1] at e2
  revert e2
  cases b[i] <;> cases b'[i] <;> simp [Γ.ofBool]

/-- A tape carries at most one natural number. -/
theorem hasBinaryNat_value_unique {t : Tape} {v v' : ℕ}
    (h : t.HasBinaryNat v) (h' : t.HasBinaryNat v') : v = v' :=
  bits_injective (hasBinaryString_unique h.2 h'.2)


/-! ## The counting machine's tape state -/

/-- **The tape state of the counting machine.** Three designated work tapes carry the counter and
the two tallies in canonical binary; every other tape, the input, and the output are pinned. -/
def tallyState {n : ℕ} (cIdx aIdx rIdx : Fin n) (I : Tape) (rest : Fin n → Tape)
    (st : ℕ × ℕ × ℕ) : TapePred n := fun inp work out =>
  inp = I ∧ out.read ≠ Γ.start ∧
  (work cIdx).HasBinaryNat st.1 ∧ (work aIdx).HasBinaryNat st.2.1 ∧
  (work rIdx).HasBinaryNat st.2.2 ∧
  ∀ i, i ≠ cIdx → i ≠ aIdx → i ≠ rIdx → work i = rest i

/-- The iteration count read back off the counter tape. The input and output tapes are ignored;
they are present because `TM.loopTM_hoareTime_indexed` takes the index as a function of the whole
tape state. -/
@[nolint unusedArguments]
noncomputable def tallyIdx {n : ℕ} (cIdx : Fin n) :
    Tape → (Fin n → Tape) → Tape → ℕ :=
  fun _ work _ => Classical.epsilon fun v => (work cIdx).HasBinaryNat v

/-- **Reading the index back is faithful.** This is the hypothesis `TM.loopTM_hoareTime_indexed`
needs: the loop's variant can be computed from the tapes it is looking at. -/
theorem tallyIdx_tallyState {n : ℕ} (cIdx aIdx rIdx : Fin n) (I : Tape)
    (rest : Fin n → Tape) (st : ℕ × ℕ × ℕ) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (h : tallyState cIdx aIdx rIdx I rest st inp work out) :
    tallyIdx cIdx inp work out = st.1 := by
  obtain ⟨-, -, hc, -, -, -⟩ := h
  have hex : ∃ v, (work cIdx).HasBinaryNat v := ⟨st.1, hc⟩
  exact hasBinaryNat_value_unique (Classical.epsilon_spec hex) hc


/-- The canonical tape for a natural number. -/
def natTape (v : ℕ) : Tape := (Tape.init (v.bits.map Γ.ofBool)).move Dir3.right

/-- The work bank of the counting machine at a given state. -/
def tallyWork {n : ℕ} (cIdx aIdx rIdx : Fin n) (rest : Fin n → Tape)
    (st : ℕ × ℕ × ℕ) : Fin n → Tape := fun i =>
  if i = cIdx then natTape st.1
  else if i = aIdx then natTape st.2.1
  else if i = rIdx then natTape st.2.2
  else rest i

/-- **The tape state is fully pinned.** `Tape.HasBinaryNat` determines a tape outright, so the
counting machine's state names every tape exactly — which is what lets the library's framed
subroutine contracts, whose preconditions pin all three tape components, be applied to it. -/
theorem tallyState_iff {n : ℕ} (cIdx aIdx rIdx : Fin n)
    (hca : cIdx ≠ aIdx) (hcr : cIdx ≠ rIdx) (har : aIdx ≠ rIdx)
    (I : Tape) (rest : Fin n → Tape) (st : ℕ × ℕ × ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) :
    tallyState cIdx aIdx rIdx I rest st inp work out ↔
      (inp = I ∧ work = tallyWork cIdx aIdx rIdx rest st ∧ out.read ≠ Γ.start) := by
  constructor
  · rintro ⟨hi, ho, hc, ha, hr, hother⟩
    refine ⟨hi, funext fun i => ?_, ho⟩
    simp only [tallyWork]
    by_cases hic : i = cIdx
    · subst hic
      simpa [natTape] using hc.eq_init_move_right
    · by_cases hia : i = aIdx
      · subst hia
        simp only [ite_eq_right hic]
        simpa [natTape] using ha.eq_init_move_right
      · by_cases hir : i = rIdx
        · subst hir
          simp only [ite_eq_right hic, ite_eq_right hia]
          simpa [natTape] using hr.eq_init_move_right
        · simp only [ite_eq_right hic, ite_eq_right hia, ite_eq_right hir]
          exact hother i hic hia hir
  · rintro ⟨hi, rfl, ho⟩
    refine ⟨hi, ho, ?_, ?_, ?_, ?_⟩
    · simpa [tallyWork, natTape] using Tape.init_move_right_hasBinaryNat st.1
    · simp only [tallyWork, ite_eq_right hca.symm]
      exact Tape.init_move_right_hasBinaryNat st.2.1
    · simp only [tallyWork, ite_eq_right hcr.symm, ite_eq_right har.symm]
      exact Tape.init_move_right_hasBinaryNat st.2.2
    · intro i hic hia hir
      simp only [tallyWork, ite_eq_right hic, ite_eq_right hia, ite_eq_right hir]


/-- Canonical number tapes read a digit or a blank, never the left marker. -/
theorem natTape_read_ne_start (v : ℕ) : (natTape v).read ≠ Γ.start := by
  have h := Tape.init_move_right_hasBinaryNat v
  show (natTape v).cells (natTape v).head ≠ Γ.start
  rw [show (natTape v).head = 1 from h.2.1]
  by_cases hb : 0 < v.bits.length
  · rw [show (natTape v).cells (0 + 1) = Γ.ofBool (v.bits[0]'hb) from h.2.2.1 0 hb]
    cases v.bits[0] <;> simp [Γ.ofBool]
  · rw [show (natTape v).cells (0 + 1) = Γ.blank from h.2.2.2 0 (by omega)]
    simp

/-- The work bank of the counting machine reads off the left marker on every tape. -/
theorem tallyWork_read_ne_start {n : ℕ} (cIdx aIdx rIdx : Fin n) (rest : Fin n → Tape)
    (hrest : ∀ i, (rest i).read ≠ Γ.start) (st : ℕ × ℕ × ℕ) (i : Fin n) :
    (tallyWork cIdx aIdx rIdx rest st i).read ≠ Γ.start := by
  simp only [tallyWork]
  split
  · exact natTape_read_ne_start _
  · split
    · exact natTape_read_ne_start _
    · split
      · exact natTape_read_ne_start _
      · exact hrest i

/-- A canonical number tape is parked: its head is off the left marker and no cell beyond the
marker holds one. This is the side condition the rewind and wipe subroutines ask of every tape
they carry along. -/
theorem natTape_parked (v : ℕ) : TM.Parked (natTape v) := by
  have h : (natTape v).HasBinaryNat v := Tape.init_move_right_hasBinaryNat v
  refine ⟨by rw [show (natTape v).head = 1 from h.2.1], fun j hj => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  by_cases hb : i < v.bits.length
  · rw [h.2.2.1 i hb]
    cases v.bits[i] <;> simp [Γ.ofBool]
  · rw [h.2.2.2 i (by omega)]
    simp

/-- **The three increment stages.** Advancing one of the numeric tapes by one is the library's
canonical successor applied to the pinned state; the output tape is carried along untouched,
whatever it holds. -/
theorem binarySucc_tallyState {n : ℕ} (cIdx aIdx rIdx : Fin n)
    (hca : cIdx ≠ aIdx) (hcr : cIdx ≠ rIdx) (har : aIdx ≠ rIdx)
    (I : Tape) (rest : Fin n → Tape) (v a r : ℕ)
    (hI : I.read ≠ Γ.start) (hrest : ∀ i, (rest i).read ≠ Γ.start) :
    (TM.binarySuccTM aIdx).HoareTime
      (tallyState cIdx aIdx rIdx I rest (v, a, r))
      (tallyState cIdx aIdx rIdx I rest (v, a + 1, r))
      (TM.binarySuccTime a) := by
  intro inp work out hpre
  rw [tallyState_iff cIdx aIdx rIdx hca hcr har] at hpre
  obtain ⟨hinp, hwork, hore⟩ := hpre
  have hval : (tallyWork cIdx aIdx rIdx rest (v, a, r) aIdx).HasBinaryNat a := by
    simp only [tallyWork, ite_eq_right hca.symm]
    exact Tape.init_move_right_hasBinaryNat a
  obtain ⟨c', t, ht, hreach, hhalt, hi, hother, hidx, ho⟩ :=
    TM.binarySuccTM_hoareTime_frame aIdx a I (tallyWork cIdx aIdx rIdx rest (v, a, r)) out
      hval hI (fun i _ => tallyWork_read_ne_start cIdx aIdx rIdx rest hrest _ i) hore
      inp work out ⟨hinp, hwork, rfl⟩
  refine ⟨c', t, ht, hreach, hhalt, hi, by rw [ho]; exact hore, ?_, hidx, ?_, ?_⟩
  · rw [hother cIdx hca]
    simpa [tallyWork, natTape] using Tape.init_move_right_hasBinaryNat v
  · rw [hother rIdx har.symm]
    simp only [tallyWork, ite_eq_right hcr.symm, ite_eq_right har.symm]
    exact Tape.init_move_right_hasBinaryNat r
  · intro i hic hia hir
    rw [hother i hia]
    simp only [tallyWork, ite_eq_right hic, ite_eq_right hia, ite_eq_right hir]

/-- The counter-increment stage. -/
theorem binarySucc_tallyState_counter {n : ℕ} (cIdx aIdx rIdx : Fin n)
    (hca : cIdx ≠ aIdx) (hcr : cIdx ≠ rIdx) (har : aIdx ≠ rIdx)
    (I : Tape) (rest : Fin n → Tape) (v a r : ℕ)
    (hI : I.read ≠ Γ.start) (hrest : ∀ i, (rest i).read ≠ Γ.start) :
    (TM.binarySuccTM cIdx).HoareTime
      (tallyState cIdx aIdx rIdx I rest (v, a, r))
      (tallyState cIdx aIdx rIdx I rest (v + 1, a, r))
      (TM.binarySuccTime v) := by
  intro inp work out hpre
  rw [tallyState_iff cIdx aIdx rIdx hca hcr har] at hpre
  obtain ⟨hinp, hwork, hore⟩ := hpre
  have hval : (tallyWork cIdx aIdx rIdx rest (v, a, r) cIdx).HasBinaryNat v := by
    simpa [tallyWork, natTape] using Tape.init_move_right_hasBinaryNat v
  obtain ⟨c', t, ht, hreach, hhalt, hi, hother, hidx, ho⟩ :=
    TM.binarySuccTM_hoareTime_frame cIdx v I (tallyWork cIdx aIdx rIdx rest (v, a, r)) out
      hval hI (fun i _ => tallyWork_read_ne_start cIdx aIdx rIdx rest hrest _ i) hore
      inp work out ⟨hinp, hwork, rfl⟩
  refine ⟨c', t, ht, hreach, hhalt, hi, by rw [ho]; exact hore, hidx, ?_, ?_, ?_⟩
  · rw [hother aIdx hca.symm]
    simp only [tallyWork, ite_eq_right hca.symm]
    exact Tape.init_move_right_hasBinaryNat a
  · rw [hother rIdx hcr.symm]
    simp only [tallyWork, ite_eq_right hcr.symm, ite_eq_right har.symm]
    exact Tape.init_move_right_hasBinaryNat r
  · intro i hic hia hir
    rw [hother i hic]
    simp only [tallyWork, ite_eq_right hic, ite_eq_right hia, ite_eq_right hir]

/-- The rejecting-tally-increment stage. -/
theorem binarySucc_tallyState_rej {n : ℕ} (cIdx aIdx rIdx : Fin n)
    (hca : cIdx ≠ aIdx) (hcr : cIdx ≠ rIdx) (har : aIdx ≠ rIdx)
    (I : Tape) (rest : Fin n → Tape) (v a r : ℕ)
    (hI : I.read ≠ Γ.start) (hrest : ∀ i, (rest i).read ≠ Γ.start) :
    (TM.binarySuccTM rIdx).HoareTime
      (tallyState cIdx aIdx rIdx I rest (v, a, r))
      (tallyState cIdx aIdx rIdx I rest (v, a, r + 1))
      (TM.binarySuccTime r) := by
  intro inp work out hpre
  rw [tallyState_iff cIdx aIdx rIdx hca hcr har] at hpre
  obtain ⟨hinp, hwork, hore⟩ := hpre
  have hval : (tallyWork cIdx aIdx rIdx rest (v, a, r) rIdx).HasBinaryNat r := by
    simp only [tallyWork, ite_eq_right hcr.symm, ite_eq_right har.symm]
    exact Tape.init_move_right_hasBinaryNat r
  obtain ⟨c', t, ht, hreach, hhalt, hi, hother, hidx, ho⟩ :=
    TM.binarySuccTM_hoareTime_frame rIdx r I (tallyWork cIdx aIdx rIdx rest (v, a, r)) out
      hval hI (fun i _ => tallyWork_read_ne_start cIdx aIdx rIdx rest hrest _ i) hore
      inp work out ⟨hinp, hwork, rfl⟩
  refine ⟨c', t, ht, hreach, hhalt, hi, by rw [ho]; exact hore, ?_, ?_, hidx, ?_⟩
  · rw [hother cIdx hcr]
    simpa [tallyWork, natTape] using Tape.init_move_right_hasBinaryNat v
  · rw [hother aIdx har]
    simp only [tallyWork, ite_eq_right hca.symm]
    exact Tape.init_move_right_hasBinaryNat a
  · intro i hic hia hir
    rw [hother i hir]
    simp only [tallyWork, ite_eq_right hic, ite_eq_right hia, ite_eq_right hir]

namespace NTM

variable {k : ℕ}

/-- **A path simulation halts within the protocol's own time bound.** All paths of `tm` halt
within `f |x|` steps, and `choiceTM` follows one of them step for step, so it halts too. -/
theorem choiceTM_haltsIn (tm : NTM k) {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f)
    (x : List Bool) (c : Cfg (k + 1) tm.Q) (hdrop : dropChoice c = tm.initCfg x)
    (hinv : (c.work (Fin.last k)).StartInvariant)
    (hhead : 1 ≤ (c.work (Fin.last k)).head) :
    ∃ c' t, t ≤ f x.length + 1 ∧ (choiceTM tm).reachesIn t c c' ∧ (choiceTM tm).halted c' := by
  obtain ⟨c', t, hle, hreach, -, heq⟩ :=
    choiceTM_simulates tm (f x.length + 1) c hinv hhead
  refine ⟨c', t, hle, hreach, ?_⟩
  have hhalted_f : tm.halted
      (tm.trace (f x.length) (fun j => choiceStream c j.val) (tm.initCfg x)) := hall x _
  have hfrozen := tm.trace_mono (T := f x.length) (T' := f x.length + 1) (by omega)
    (choices := fun j => choiceStream c j.val)
    (choices' := fun j => choiceStream c j.val)
    (c := tm.initCfg x) (fun _ => rfl) hhalted_f
  have hstate : (dropChoice c').state = tm.qhalt := by
    rw [heq, hdrop, hfrozen]
    exact hhalted_f
  exact hstate


/-- **A path simulation keeps a window.** Since every path halts within `f |x| + 1` steps and a
head moves at most one cell per step, nothing travels more than that far beyond where it started.
No space hypothesis on `tm` is needed — its time bound does the work. -/
theorem choiceTM_keepsWindowOn (tm : NTM k) {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f)
    (x : List Bool) {inputLength h₀ : ℕ} :
    (choiceTM tm).KeepsWindowOn
      (fun c => dropChoice c = tm.initCfg x ∧
        (c.work (Fin.last k)).StartInvariant ∧ 1 ≤ (c.work (Fin.last k)).head ∧
        (∀ i, (c.work i).head ≤ h₀) ∧ c.input.head ≤ inputLength + h₀ + 1 ∧
        c.output.head ≤ h₀ + 1)
      inputLength (h₀ + (f x.length + 1)) :=
  TM.keepsWindowOn_of_haltsIn
    (fun _ hc i => hc.2.2.2.1 i)
    (fun _ hc => hc.2.2.2.2.1)
    (fun _ hc => hc.2.2.2.2.2)
    (fun c hc => choiceTM_haltsIn tm hall x c hc.1 hc.2.1 hc.2.2.1)


/-- **The accepting-path count is a count over counter values.** `NTM.acceptCount` ranges over
functions `Fin T → Bool`; the counting machine ranges over the numbers below `2 ^ T`. The
correspondence of `choicesOfNat` and `natOfChoices` identifies the two counts, so the machine's
tally is the quantity `PP` compares against half. -/
theorem acceptCount_eq_card_range {k : ℕ} (tm : NTM k) (x : List Bool) (T : ℕ) :
    tm.acceptCount x T =
      ((Finset.range (2 ^ T)).filter fun v =>
        let c' := tm.trace T (choicesOfNat T v) (tm.initCfg x)
        c'.state = tm.qhalt ∧ c'.output.cells 1 = Γ.one).card := by
  classical
  refine (Finset.card_bij' (fun ch _ => natOfChoices T ch) (fun v _ => choicesOfNat T v)
    ?_ ?_ ?_ ?_).symm ▸ rfl
  · intro ch hch
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨natOfChoices_lt T ch, ?_⟩
    rw [choicesOfNat_natOfChoices]
    exact hch
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_range] at hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hv.2
  · intro ch _
    exact choicesOfNat_natOfChoices T ch
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_range] at hv
    exact natOfChoices_choicesOfNat T v hv.1


/-! ## The running tally

A counting loop does not compute a cardinality; it accumulates. `tally` is that accumulation, and
`tally_eq_card` identifies it with the cardinality — which is the loop invariant the machine's
correctness proof will carry. -/

/-- The running count of the values below `N` satisfying `P`, as a loop accumulates it. -/
def tally (P : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | N + 1 => tally P N + (if P N then 1 else 0)

/-- **The accumulation computes the cardinality.** -/
theorem tally_eq_card (P : ℕ → Bool) :
    ∀ N, tally P N = ((Finset.range N).filter fun v => P v = true).card
  | 0 => by simp [tally]
  | N + 1 => by
      have hins : Finset.range (N + 1) = insert N (Finset.range N) := by
        ext v
        simp only [Finset.mem_range, Finset.mem_insert]
        omega
      rw [tally, tally_eq_card P N, hins, Finset.filter_insert]
      by_cases h : P N = true
      · simp only [h, ↓reduceIte]
        rw [Finset.card_insert_of_notMem (by simp)]
      · simp [h]

/-- **What the counting machine decides.** Membership is a comparison between `2 ^ T` and twice a
running tally over counter values — an accumulation a loop performs and a comparison of two
binary naturals. Neither probability, nor rationals, nor a quantifier over functions remains. -/
theorem mem_iff_two_mul_tally {k : ℕ} {L : Language} {tm : NTM k} {f : ℕ → ℕ}
    (hchar : ∀ x : List Bool, x ∈ L ↔ 2 ^ f x.length < 2 * tm.acceptCount x (f x.length))
    (x : List Bool) :
    x ∈ L ↔ 2 ^ f x.length < 2 * tally (fun v =>
      decide (let c' := tm.trace (f x.length) (choicesOfNat (f x.length) v) (tm.initCfg x)
        c'.state = tm.qhalt ∧ c'.output.cells 1 = Γ.one)) (2 ^ f x.length) := by
  classical
  rw [hchar x, acceptCount_eq_card_range tm x (f x.length), tally_eq_card]
  simp


/-- A tally and its complement partition the range. -/
theorem tally_add_compl (P : ℕ → Bool) :
    ∀ N, tally P N + tally (fun v => !P v) N = N
  | 0 => rfl
  | N + 1 => by
      have ih := tally_add_compl P N
      have key : ∀ b : Bool, (if b then 1 else 0) + (if !b then 1 else 0) = 1 := by decide
      have hb := key (P N)
      simp only [tally]
      omega

/-- **The threshold is a comparison of two counters.** More than half of the range satisfies `P`
exactly when the tally of `P` exceeds the tally of its complement. The machine therefore never
has to form `2 ^ T` or multiply: it keeps two counters and compares them. -/
theorem lt_two_mul_tally_iff (P : ℕ → Bool) (N : ℕ) :
    N < 2 * tally P N ↔ tally (fun v => !P v) N < tally P N := by
  have h := tally_add_compl P N
  omega

/-- **What the counting machine decides, as a comparison of two counters.** -/
theorem mem_iff_tally_lt_tally {k : ℕ} {L : Language} {tm : NTM k} {f : ℕ → ℕ}
    (hchar : ∀ x : List Bool, x ∈ L ↔ 2 ^ f x.length < 2 * tm.acceptCount x (f x.length))
    (x : List Bool) :
    x ∈ L ↔
      tally (fun v =>
        !decide (let c' := tm.trace (f x.length) (choicesOfNat (f x.length) v) (tm.initCfg x)
          c'.state = tm.qhalt ∧ c'.output.cells 1 = Γ.one)) (2 ^ f x.length) <
      tally (fun v =>
        decide (let c' := tm.trace (f x.length) (choicesOfNat (f x.length) v) (tm.initCfg x)
          c'.state = tm.qhalt ∧ c'.output.cells 1 = Γ.one)) (2 ^ f x.length) := by
  rw [mem_iff_two_mul_tally hchar x, lt_two_mul_tally_iff]


/-! ## The counter tape is the choice sequence -/

/-- **What the path simulator reads off a binary counter tape.** `NTM.choiceStream` maps every
cell that is not `Γ.one` to `false`, including the blanks past the counter's last digit — and
those are exactly the high bits of the number, which are zero. So a tape carrying a binary string
*is* the choice sequence it encodes, padded with `false` for free. -/
theorem choiceStream_of_hasBinaryString {k : ℕ} {tm : NTM k} (c : Cfg (k + 1) tm.Q)
    (bits : List Bool) (h : (c.work (Fin.last k)).HasBinaryString bits) (j : ℕ) :
    choiceStream c j = bits.getD j false := by
  obtain ⟨hhead, hin, hout⟩ := h
  simp only [choiceStream, hhead]
  by_cases hj : j < bits.length
  · have hgd : bits.getD j false = bits[j] := by
      simp [List.getD, List.getElem?_eq_getElem hj]
    rw [show 1 + j = j + 1 from by omega, hin j hj, hgd]
    cases bits[j] <;> simp [Γ.ofBool]
  · have hgd : bits.getD j false = false := by
      simp [List.getD, List.getElem?_eq_none (show bits.length ≤ j by omega)]
    rw [show 1 + j = j + 1 from by omega, hout j (by omega), hgd]
    simp


/-! ## The count is stable under enlarging the horizon

A counting machine cannot evaluate the protocol's own time bound `f` — it is an arbitrary
function known only to be `O(n^m)`. It must therefore count over a *polynomial* horizon it can
compute. That is sound because every path has already halted: extending the horizon multiplies
both the accepting count and the total by the same factor, so the comparison is unchanged. -/

/-- **Extending the horizon multiplies the accepting count by the number of extensions.** -/
theorem acceptCount_add {k : ℕ} (tm : NTM k) {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f)
    (x : List Bool) (b : ℕ) :
    tm.acceptCount x (f x.length + b) = tm.acceptCount x (f x.length) * 2 ^ b := by
  classical
  set a := f x.length with ha
  have hfreeze : ∀ w : Fin (a + b) → Bool,
      tm.trace (a + b) w (tm.initCfg x) = tm.trace a (blockFst a b w) (tm.initCfg x) :=
    fun w => tm.trace_mono (T := a) (T' := a + b) (by omega)
      (choices := blockFst a b w) (choices' := w) (fun _ => rfl) (hall x _)
  have hset : (Finset.univ.filter fun w : Fin (a + b) → Bool =>
        (tm.trace (a + b) w (tm.initCfg x)).state = tm.qhalt ∧
        (tm.trace (a + b) w (tm.initCfg x)).output.cells 1 = Γ.one)
      = Finset.univ.filter fun w : Fin (a + b) → Bool =>
        ((fun u : Fin a → Bool =>
          (tm.trace a u (tm.initCfg x)).state = tm.qhalt ∧
          (tm.trace a u (tm.initCfg x)).output.cells 1 = Γ.one) (blockFst a b w)) ∧
        ((fun _ : Fin b → Bool => True) (blockSnd a b w)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hfreeze w, and_true]
  have hblock := card_filter_block
    (P := fun u : Fin a → Bool =>
      (tm.trace a u (tm.initCfg x)).state = tm.qhalt ∧
      (tm.trace a u (tm.initCfg x)).output.cells 1 = Γ.one)
    (Q := fun _ : Fin b → Bool => True)
  have hb : (Finset.univ.filter fun _ : Fin b → Bool => True).card = 2 ^ b := by
    simp [Finset.filter_true_of_mem]
  simp only [NTM.acceptCount]
  rw [hset]
  convert hblock.trans (by rw [hb]) using 2


/-- **The comparison is unchanged by a larger, computable horizon.** Counting over `p |x|` choice
sequences instead of `f |x|` scales both sides by the same power of two. This is what lets the
machine use a polynomial it can evaluate in place of the protocol's own time function. -/
theorem mem_iff_polyHorizon {k : ℕ} {L : Language} {tm : NTM k} {f : ℕ → ℕ}
    {p : Polynomial ℕ} (hall : tm.AllPathsHaltIn f) (hle : ∀ n, f n ≤ p.eval n)
    (hchar : ∀ x : List Bool, x ∈ L ↔ 2 ^ f x.length < 2 * tm.acceptCount x (f x.length))
    (x : List Bool) :
    x ∈ L ↔ 2 ^ p.eval x.length < 2 * tm.acceptCount x (p.eval x.length) := by
  obtain ⟨b, hb⟩ : ∃ b, p.eval x.length = f x.length + b :=
    ⟨p.eval x.length - f x.length, by have := hle x.length; omega⟩
  have hd : (0 : ℕ) < 2 ^ b := by positivity
  rw [hchar x, hb, acceptCount_add tm hall x b, pow_add,
    show 2 * (tm.acceptCount x (f x.length) * 2 ^ b)
      = (2 * tm.acceptCount x (f x.length)) * 2 ^ b from by ring]
  exact (Nat.mul_lt_mul_right hd).symm


/-- **The `PP` comparison does not depend on the horizon**, as long as the horizon is past the
point where every path has halted. Extending it multiplies both the accepting count and the total
by the same power of two. This is what lets the counting machine run to a horizon of its own
choosing rather than the one its specification names. -/
theorem cmp_horizon_iff {k : ℕ} (tm : NTM k) {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f)
    (x : List Bool) (T : ℕ) (hT : f x.length ≤ T) :
    (2 ^ T < 2 * tm.acceptCount x T) ↔
      (2 ^ f x.length < 2 * tm.acceptCount x (f x.length)) := by
  obtain ⟨b, hb⟩ : ∃ b, T = f x.length + b := ⟨T - f x.length, by omega⟩
  have hd : (0 : ℕ) < 2 ^ b := by positivity
  rw [hb, acceptCount_add tm hall x b, pow_add,
    show 2 * (tm.acceptCount x (f x.length) * 2 ^ b)
      = (2 * tm.acceptCount x (f x.length)) * 2 ^ b from by ring]
  exact Nat.mul_lt_mul_right hd

/-- Two horizons past the halting point give the same comparison. -/
theorem cmp_horizon_iff' {k : ℕ} (tm : NTM k) {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f)
    (x : List Bool) (T T' : ℕ) (hT : f x.length ≤ T) (hT' : f x.length ≤ T') :
    (2 ^ T < 2 * tm.acceptCount x T) ↔ (2 ^ T' < 2 * tm.acceptCount x T') :=
  (cmp_horizon_iff tm hall x T hT).trans (cmp_horizon_iff tm hall x T' hT').symm

/-- The per-value acceptance test the counting loop performs: run the path selected by counter
value `v` and report whether it halts accepting. -/
def acceptsAt {k : ℕ} (tm : NTM k) (x : List Bool) (T v : ℕ) : Bool :=
  decide ((tm.trace T (choicesOfNat T v) (tm.initCfg x)).state = tm.qhalt ∧
    (tm.trace T (choicesOfNat T v) (tm.initCfg x)).output.cells 1 = Γ.one)

/-- **The degenerate machine decides the empty language.** A machine that starts halted never
moves, and its output tape is blank, so no choice sequence is accepting and the `PP` comparison
fails on every input. Ruling this case out is what licenses the `qstart ≠ qhalt` hypothesis the
delay construction needs. -/
theorem acceptCount_eq_zero_of_qstart_eq_qhalt {k : ℕ} {tm : NTM k}
    (heq : tm.qstart = tm.qhalt) (x : List Bool) (T : ℕ) : tm.acceptCount x T = 0 := by
  classical
  simp only [NTM.acceptCount]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ch _
  rw [tm.trace_halted T ch heq]
  rintro ⟨-, hone⟩
  rw [show (tm.initCfg x).output = Tape.init ([] : List Γ) from rfl,
    show (1 : ℕ) = 0 + 1 from rfl, Tape.init_nil_cells_succ] at hone
  exact absurd hone (by decide)

theorem not_mem_of_qstart_eq_qhalt {k : ℕ} {L : Language} {tm : NTM k} {f : ℕ → ℕ}
    (heq : tm.qstart = tm.qhalt)
    (hchar : ∀ x : List Bool, x ∈ L ↔ 2 ^ f x.length < 2 * tm.acceptCount x (f x.length))
    (x : List Bool) : x ∉ L := by
  rw [hchar x, acceptCount_eq_zero_of_qstart_eq_qhalt heq x (f x.length)]
  simp

/-- **The `PP` characterisation survives the delay.** `NTM.delayNTM` spends two extra steps and
doubles the count of accepting paths; the horizon's own doubling absorbs exactly that, so the
comparison `2 ^ T < 2 * acceptCount` is unchanged. This is what lets the counting machine
simulate a machine whose first transition ignores its choice bit — the only kind a composed
machine can enter, since no stage can be handed a head at cell zero. -/
theorem delayNTM_char {k : ℕ} {L : Language} {tm : NTM k} {f : ℕ → ℕ}
    (hall : tm.AllPathsHaltIn f) (hne : tm.qstart ≠ tm.qhalt)
    (hchar : ∀ x : List Bool, x ∈ L ↔ 2 ^ f x.length < 2 * tm.acceptCount x (f x.length))
    (x : List Bool) :
    x ∈ L ↔ 2 ^ (f x.length + 2) <
      2 * (delayNTM tm).acceptCount x (f x.length + 2) := by
  have hcount : (delayNTM tm).acceptCount x (f x.length + 2)
      = 4 * tm.acceptCount x (f x.length) := by
    rw [delayNTM_acceptCount tm x hne (f x.length),
      show f x.length + 1 = f x.length + 1 from rfl, acceptCount_add tm hall x 1]
    ring
  have hpow : (2 : ℕ) ^ (f x.length + 2) = 4 * 2 ^ f x.length := by
    rw [pow_add]
    ring
  rw [hchar x, hcount, hpow]
  omega

/-- **The tally is the accepting count.** Enumerating the counter over `[0, 2 ^ T)` visits every
choice sequence exactly once, so accumulating the acceptance test over that range counts the
accepting paths. -/
theorem tally_eq_acceptCount {k : ℕ} (tm : NTM k) (x : List Bool) (T : ℕ) :
    tally (fun v => acceptsAt tm x T v) (2 ^ T) = tm.acceptCount x T := by
  rw [acceptCount_eq_card_range tm x T, tally_eq_card]
  simp [acceptsAt]

/-- **The comparison the machine performs is the `PP` comparison.** -/
theorem tally_cmp_iff {k : ℕ} (tm : NTM k) (x : List Bool) (T : ℕ) :
    (tally (fun v => !acceptsAt tm x T v) (2 ^ T) <
        tally (fun v => acceptsAt tm x T v) (2 ^ T))
      ↔ 2 ^ T < 2 * tm.acceptCount x T := by
  rw [← lt_two_mul_tally_iff, tally_eq_acceptCount]

/-- **The complete machine specification for `PP`.** Everything on the right is something a
machine performs: iterate a counter to a polynomial bound it can evaluate, simulate one path per
counter value, keep two tallies, and compare them. No probability, no rationals, no quantifier
over the function space, and no reference to the protocol's own time function survive. -/
theorem mem_iff_tally_lt_tally_poly {k : ℕ} {L : Language} {tm : NTM k} {f : ℕ → ℕ}
    {p : Polynomial ℕ} (hall : tm.AllPathsHaltIn f) (hle : ∀ n, f n ≤ p.eval n)
    (hchar : ∀ x : List Bool, x ∈ L ↔ 2 ^ f x.length < 2 * tm.acceptCount x (f x.length))
    (x : List Bool) :
    x ∈ L ↔
      tally (fun v => !acceptsAt tm x (p.eval x.length) v) (2 ^ p.eval x.length) <
      tally (fun v => acceptsAt tm x (p.eval x.length) v) (2 ^ p.eval x.length) := by
  rw [mem_iff_polyHorizon hall hle hchar x, ← lt_two_mul_tally_iff,
    acceptCount_eq_card_range tm x (p.eval x.length), tally_eq_card]
  simp [acceptsAt]


/-- **The inner call, fully placed.** The path simulator sits inside a machine with `m` extra
tapes and writes its verdict onto a work tape rather than the real output. Lifting is free and
the output redirection costs one cell, so the whole placed call keeps a window one wider than the
simulation's own. This is the form in which the counting machine invokes it. -/
theorem choiceTM_placed_keepsWindow {k : ℕ} (tm : NTM k) {f : ℕ → ℕ}
    (hall : tm.AllPathsHaltIn f) (x : List Bool) (m : ℕ) (c₀ : Cfg (k + 1) tm.Q)
    {inputLength h₀ : ℕ}
    (hdrop : dropChoice c₀ = tm.initCfg x)
    (hinv : (c₀.work (Fin.last k)).StartInvariant)
    (hhead : 1 ≤ (c₀.work (Fin.last k)).head)
    (hheads : ∀ i, (c₀.work i).head ≤ h₀)
    (hin : c₀.input.head ≤ inputLength + h₀ + 1)
    (hout : c₀.output.head ≤ h₀ + 1) :
    ∀ D, (((choiceTM tm).liftTM m).retargetOutput).reaches
        (((choiceTM tm).liftTM m).retargetCfg ((choiceTM tm).liftCfg m c₀)) D →
      D.WithinDecisionSpace inputLength (h₀ + (f x.length + 1) + 1) :=
  TM.retargetOutput_keepsWindow_of_reaches _ _
    (TM.liftTM_keepsWindow_of_reaches (choiceTM tm) m c₀ (by omega)
      (choiceTM_keepsWindowOn tm hall x c₀ ⟨hdrop, hinv, hhead, hheads, hin, hout⟩))


/-! ## The loop invariant

The counting machine carries three numbers on its tapes: the counter, the accepting tally, and
the rejecting tally. `tallyStep` is one iteration's effect on that triple, and `tallyStep_iterate`
is the invariant relating the state after `N` iterations to `tally` — the fact the machine's
correctness proof carries through the loop. -/

/-- One iteration of the counting loop, on the triple (counter, accepting tally, rejecting
tally). -/
def tallyStep (P : ℕ → Bool) (st : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (st.1 + 1, st.2.1 + (if P st.1 then 1 else 0), st.2.2 + (if P st.1 then 0 else 1))

/-- **The loop invariant.** After `N` iterations from the zero state, the counter reads `N` and
the two tallies read the counts of the values below `N` satisfying and failing `P`. -/
theorem tallyStep_iterate (P : ℕ → Bool) :
    ∀ N, (tallyStep P)^[N] (0, 0, 0) = (N, tally P N, tally (fun v => !P v) N)
  | 0 => rfl
  | N + 1 => by
      rw [Function.iterate_succ_apply', tallyStep_iterate P N]
      have hsplit : (if !P N then 1 else 0) = (if P N then 0 else 1) := by
        cases P N <;> simp
      simp only [tallyStep, tally, hsplit]


/-- **What the counting machine must compute, as a single iterated function.** Running the loop
`2 ^ T` times from the zero state and comparing the two tallies decides membership. This is the
form the machine's Hoare contract will take: an iteration count, one step function, and a
comparison of two components of the final state. -/
theorem mem_iff_iterate_tallyStep {k : ℕ} {L : Language} {tm : NTM k} {f : ℕ → ℕ}
    {p : Polynomial ℕ} (hall : tm.AllPathsHaltIn f) (hle : ∀ n, f n ≤ p.eval n)
    (hchar : ∀ x : List Bool, x ∈ L ↔ 2 ^ f x.length < 2 * tm.acceptCount x (f x.length))
    (x : List Bool) :
    x ∈ L ↔
      ((tallyStep (fun v => acceptsAt tm x (p.eval x.length) v))^[2 ^ p.eval x.length]
        (0, 0, 0)).2.2 <
      ((tallyStep (fun v => acceptsAt tm x (p.eval x.length) v))^[2 ^ p.eval x.length]
        (0, 0, 0)).2.1 := by
  rw [mem_iff_tally_lt_tally_poly hall hle hchar x,
    tallyStep_iterate (fun v => acceptsAt tm x (p.eval x.length) v)]


/-- **The counting loop, granted a body that realises one step.** With the tape state of
`tallyState` and the index read back by `tallyIdx`, the indexed loop rule reduces the whole run to
two obligations: one iteration advances the state by `tallyStep`, and the loop halts at the final
count. Everything about counting — the invariant, the variant, the fuel — is discharged here. -/
theorem tallyLoop_hoareTime {n : ℕ} (tmBody tmTest : TM n) (cIdx aIdx rIdx : Fin n)
    (I : Tape) (rest : Fin n → Tape) (P : ℕ → Bool) {post : TapePred n} (N b : ℕ)
    (hstep : ∀ j, j < N → ∀ inp work out,
      tallyState cIdx aIdx rIdx I rest ((tallyStep P)^[j] (0, 0, 0)) inp work out →
      ∃ inp' work' out' t, t ≤ b ∧
        (TM.loopTM tmBody tmTest).reachesIn t
          ⟨(TM.loopTM tmBody tmTest).qstart, inp, work, out⟩
          ⟨(TM.loopTM tmBody tmTest).qstart, inp', work', out'⟩ ∧
        tallyState cIdx aIdx rIdx I rest ((tallyStep P)^[j + 1] (0, 0, 0)) inp' work' out')
    (hstop : ∀ inp work out,
      tallyState cIdx aIdx rIdx I rest ((tallyStep P)^[N] (0, 0, 0)) inp work out →
      ∃ c' t, t ≤ b ∧
        (TM.loopTM tmBody tmTest).reachesIn t
          ⟨(TM.loopTM tmBody tmTest).qstart, inp, work, out⟩ c' ∧
        (TM.loopTM tmBody tmTest).halted c' ∧ post c'.input c'.work c'.output) :
    (TM.loopTM tmBody tmTest).HoareTime
      (tallyState cIdx aIdx rIdx I rest (0, 0, 0)) post ((N + 1) * b) := by
  have hzero : ((tallyStep P)^[0] (0, 0, 0)) = (0, 0, 0) := rfl
  refine TM.loopTM_hoareTime_indexed tmBody tmTest
    (E := fun j => tallyState cIdx aIdx rIdx I rest ((tallyStep P)^[j] (0, 0, 0)))
    (idx := tallyIdx cIdx) ?_ hstep hstop |>.consequence
    (fun _ _ _ h => by rw [hzero]; exact h) (fun _ _ _ h => h) le_rfl
  intro j inp work out h
  rw [tallyIdx_tallyState cIdx aIdx rIdx I rest _ inp work out h, tallyStep_iterate]


/-- The output tape as the counting loop uses it: a single verdict cell, and blanks beyond it.
`TM.loopTM` inspects exactly this cell after rewinding the output, so the loop's whole
interaction with its output tape is the choice of one symbol. -/
def outSlot (s : Γw) : Tape where
  head := 1
  cells := fun j => if j = 0 then Γ.start else if j = 1 then s.toΓ else Γ.blank

@[simp] theorem outSlot_head (s : Γw) : (outSlot s).head = 1 := rfl

@[simp] theorem outSlot_cells_zero (s : Γw) : (outSlot s).cells 0 = Γ.start := rfl

@[simp] theorem outSlot_cells_one (s : Γw) : (outSlot s).cells 1 = s.toΓ := rfl

/-- A verdict slot never carries a stray left marker, so it is parked. -/
theorem outSlot_parked (s : Γw) : TM.Parked (outSlot s) := by
  refine ⟨le_refl 1, fun j hj => ?_⟩
  show (if j = 0 then Γ.start else if j = 1 then s.toΓ else Γ.blank) ≠ Γ.start
  rw [ite_eq_right (by omega)]
  split
  · cases s <;> simp [Γw.toΓ]
  · simp

/-- The verdict cell holds `1` exactly when the slot was written with `1`. -/
theorem outSlot_cells_one_eq_one_iff (s : Γw) : (outSlot s).cells 1 = Γ.one ↔ s = Γw.one := by
  cases s <;> simp [Γw.toΓ]

/-- The tape state the counting loop sits in at its own start state. Every tape is named
outright: the three numeric registers hold the count and the two tallies, every other work tape
is back at its resting contents, and the output carries the previous check's verdict, which for a
continuing iteration is `0`. -/
def tallyPre {n : ℕ} (cIdx aIdx rIdx : Fin n) (I : Tape) (rest : Fin n → Tape) (P : ℕ → Bool)
    (v : ℕ) : TM.TapePred n := fun inp work out =>
  inp = I ∧ work = tallyWork cIdx aIdx rIdx rest (v, tally P v, tally (fun u => !P u) v) ∧
  ∃ s : Γw, s ≠ Γw.one ∧ out = outSlot s

/-- The tape state the loop's test leaves behind: the same registers, with the verdict slot
holding `1` exactly when the count has reached its horizon. -/
def tallyPost {n : ℕ} (cIdx aIdx rIdx : Fin n) (I : Tape) (rest : Fin n → Tape) (P : ℕ → Bool)
    (N v : ℕ) : TM.TapePred n := fun inp work out =>
  inp = I ∧ work = tallyWork cIdx aIdx rIdx rest (v, tally P v, tally (fun u => !P u) v) ∧
  out = outSlot (if v = N then Γw.one else Γw.zero)

/-- A pinned tally state is parked on every tape, given that the resting tapes are. -/
theorem tallyPre_loopParked {n : ℕ} (cIdx aIdx rIdx : Fin n) (I : Tape) (rest : Fin n → Tape)
    (P : ℕ → Bool) (hI : TM.Parked I) (hrest : ∀ i, TM.Parked (rest i)) (v : ℕ)
    {inp : Tape} {work : Fin n → Tape} {out : Tape}
    (h : tallyPre cIdx aIdx rIdx I rest P v inp work out) : TM.LoopParked inp work out := by
  obtain ⟨rfl, rfl, s, -, rfl⟩ := h
  refine ⟨hI, fun i => ?_, outSlot_parked _, rfl, rfl⟩
  simp only [tallyWork]
  split
  · exact natTape_parked _
  · split
    · exact natTape_parked _
    · split
      · exact natTape_parked _
      · exact hrest i

/-- The same, for the state the test leaves behind. -/
theorem tallyPost_loopParked {n : ℕ} (cIdx aIdx rIdx : Fin n) (I : Tape) (rest : Fin n → Tape)
    (P : ℕ → Bool) (hI : TM.Parked I) (hrest : ∀ i, TM.Parked (rest i)) (N v : ℕ)
    {inp : Tape} {work : Fin n → Tape} {out : Tape}
    (h : tallyPost cIdx aIdx rIdx I rest P N v inp work out) : TM.LoopParked inp work out := by
  obtain ⟨rfl, rfl, rfl⟩ := h
  refine ⟨hI, fun i => ?_, outSlot_parked _, rfl, rfl⟩
  simp only [tallyWork]
  split
  · exact natTape_parked _
  · split
    · exact natTape_parked _
    · split
      · exact natTape_parked _
      · exact hrest i

/-- **Reading the count back off a pinned tally state.** -/
theorem tallyIdx_tallyPre {n : ℕ} (cIdx aIdx rIdx : Fin n) (I : Tape) (rest : Fin n → Tape)
    (P : ℕ → Bool) (v : ℕ) {inp : Tape} {work : Fin n → Tape} {out : Tape}
    (h : tallyPre cIdx aIdx rIdx I rest P v inp work out) : tallyIdx cIdx inp work out = v := by
  obtain ⟨-, rfl, -, -, -⟩ := h
  have hc : (tallyWork cIdx aIdx rIdx rest
      (v, tally P v, tally (fun u => !P u) v) cIdx).HasBinaryNat v := by
    simp only [tallyWork, natTape]
    exact Tape.init_move_right_hasBinaryNat v
  have hex : ∃ w, (tallyWork cIdx aIdx rIdx rest
      (v, tally P v, tally (fun u => !P u) v) cIdx).HasBinaryNat w := ⟨v, hc⟩
  exact hasBinaryNat_value_unique (Classical.epsilon_spec hex) hc

/-- **The counting loop from two Hoare contracts.** This is the interface the machine
construction actually meets: a contract saying the body advances the tally by one index, and a
contract saying the test reports whether the horizon has been reached.

`TM.loopTM` is a do-while — its body runs before its first test — so a loop that halts after `N`
tallies performs its `N`-th body pass on the *terminating* iteration, not on a continuing one.
The indexed rule is therefore applied at `N - 1`, which is why the body is never asked to run at
index `N` and why `1 ≤ N` is needed. -/
theorem tallyLoop_hoareTime_of_hoare {n : ℕ} (tmBody tmTest : TM n) (cIdx aIdx rIdx : Fin n)
    (I : Tape) (rest : Fin n → Tape) (P : ℕ → Bool) (mid : ℕ → TM.TapePred n)
    (N bBody bTest : ℕ) (hN : 1 ≤ N)
    (hI : TM.Parked I) (hrest : ∀ i, TM.Parked (rest i))
    (hbody : ∀ v, v < N →
      tmBody.HoareTime (tallyPre cIdx aIdx rIdx I rest P v) (mid v) bBody)
    (hmid : ∀ v inp work out, mid v inp work out → TM.LoopParked inp work out)
    (htest : ∀ v, v < N →
      tmTest.HoareTime (mid v) (tallyPost cIdx aIdx rIdx I rest P N (v + 1)) bTest) :
    (TM.loopTM tmBody tmTest).HoareTime
      (tallyPre cIdx aIdx rIdx I rest P 0)
      (tallyPost cIdx aIdx rIdx I rest P N N)
      (N * (bBody + bTest + 5)) := by
  have hsucc : N - 1 + 1 = N := by omega
  refine (TM.loopTM_hoareTime_indexed tmBody tmTest
    (E := fun j => tallyPre cIdx aIdx rIdx I rest P j)
    (post := tallyPost cIdx aIdx rIdx I rest P N N)
    (N := N - 1) (b := bBody + bTest + 5)
    (idx := tallyIdx cIdx) ?_ ?_ ?_).consequence
    (fun _ _ _ h => h) (fun _ _ _ h => h) (le_of_eq (by rw [hsucc]))
  · intro j inp work out h
    exact tallyIdx_tallyPre cIdx aIdx rIdx I rest P j h
  · intro j hj inp work out h
    have hjN : j < N := by omega
    have hne : ∀ a b c, tallyPost cIdx aIdx rIdx I rest P N (j + 1) a b c →
        TM.LoopParked a b c ∧ c.cells 1 ≠ Γ.one := by
      intro a b c hp
      refine ⟨tallyPost_loopParked cIdx aIdx rIdx I rest P hI hrest N (j + 1) hp, ?_⟩
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
    have hhalt : ∀ a b c, tallyPost cIdx aIdx rIdx I rest P N (N - 1 + 1) a b c →
        TM.LoopParked a b c ∧ c.cells 1 = Γ.one := by
      intro a b c hp
      refine ⟨tallyPost_loopParked cIdx aIdx rIdx I rest P hI hrest N _ hp, ?_⟩
      obtain ⟨-, -, rfl⟩ := hp
      rw [ite_eq_left hsucc]
      exact (outSlot_cells_one_eq_one_iff Γw.one).mpr rfl
    obtain ⟨c', t, ht, hreach, hstate, hpost⟩ :=
      TM.loopTM_halt_of_hoare tmBody tmTest (hbody (N - 1) hjN) (htest (N - 1) hjN)
        (fun a b c hm => hmid (N - 1) a b c hm) hhalt inp work out h
    exact ⟨c', t, ht, hreach, hstate, by rw [hsucc] at hpost; exact hpost⟩


/-- **The counting loop keeps a window one iteration wide.** The loop runs exponentially many
iterations, so no bound derived from its total running time can be polynomial; what is polynomial
is a single iteration, and every state the loop returns to has all its heads at cell one. -/
theorem tallyLoop_keepsWindow_of_hoare {n : ℕ} (tmBody tmTest : TM n) (cIdx aIdx rIdx : Fin n)
    (I : Tape) (rest : Fin n → Tape) (P : ℕ → Bool) (mid : ℕ → TM.TapePred n)
    (N bBody bTest inputLength : ℕ) (hN : 1 ≤ N)
    (hI : TM.Parked I) (hrest : ∀ i, TM.Parked (rest i))
    (hIhead : I.head ≤ inputLength + 1) (hrestHead : ∀ i, (rest i).head ≤ 1)
    (hbody : ∀ v, v < N →
      tmBody.HoareTime (tallyPre cIdx aIdx rIdx I rest P v) (mid v) bBody)
    (hmid : ∀ v inp work out, mid v inp work out → TM.LoopParked inp work out)
    (htest : ∀ v, v < N →
      tmTest.HoareTime (mid v) (tallyPost cIdx aIdx rIdx I rest P N (v + 1)) bTest) :
    ∀ inp work out, tallyPre cIdx aIdx rIdx I rest P 0 inp work out →
      ∀ c, (TM.loopTM tmBody tmTest).reaches
        ⟨(TM.loopTM tmBody tmTest).qstart, inp, work, out⟩ c →
        c.WithinDecisionSpace inputLength (1 + (bBody + bTest + 5)) := by
  have hsucc : N - 1 + 1 = N := by omega
  refine TM.loopTM_keepsWindow_indexed_of_parked tmBody tmTest
    (fun j => tallyPre cIdx aIdx rIdx I rest P j) (N - 1) (bBody + bTest + 5) ?_ ?_ ?_ 0
    (by omega)
  · intro j hj inp work out h
    have hjN : j < N := by omega
    have hne : ∀ a b c, tallyPost cIdx aIdx rIdx I rest P N (j + 1) a b c →
        TM.LoopParked a b c ∧ c.cells 1 ≠ Γ.one := by
      intro a b c hp
      refine ⟨tallyPost_loopParked cIdx aIdx rIdx I rest P hI hrest N (j + 1) hp, ?_⟩
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
    have hhalt : ∀ a b c, tallyPost cIdx aIdx rIdx I rest P N (N - 1 + 1) a b c →
        TM.LoopParked a b c ∧ c.cells 1 = Γ.one := by
      intro a b c hp
      refine ⟨tallyPost_loopParked cIdx aIdx rIdx I rest P hI hrest N _ hp, ?_⟩
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
        · exact hrestHead i

/-- **The path simulation leaves the counter's digits alone.** `choiceTM` writes every choice bit
back unchanged and only advances the head, so the counter tape's contents survive the run — the
body has merely to rewind the head to restore the encoding for the next iteration. -/
theorem choiceTM_choiceCells {k : ℕ} (tm : NTM k) {c : Cfg (k + 1) tm.Q}
    (hinv : (c.work (Fin.last k)).StartInvariant)
    (hhead : 1 ≤ (c.work (Fin.last k)).head) :
    ∀ c', (choiceTM tm).reaches c c' →
      (c'.work (Fin.last k)).cells = (c.work (Fin.last k)).cells ∧
      (c'.work (Fin.last k)).StartInvariant ∧ 1 ≤ (c'.work (Fin.last k)).head := by
  intro c' h
  induction h with
  | refl => exact ⟨rfl, hinv, hhead⟩
  | @tail dmid dnext _ hstp ih =>
      obtain ⟨hcells, hsi, hhd⟩ := ih
      have hstp' : (choiceTM tm).step dmid = some dnext := hstp
      have hne : dmid.state ≠ tm.qhalt := TM.state_ne_qhalt_of_step hstp'
      have hread : (dmid.work (Fin.last k)).read ≠ Γ.start := hsi.read_ne_start hhd
      obtain ⟨c₁, hstep1, -, hchoice⟩ := choiceTM_step tm dmid hne hread
      have hnexteq : dnext = c₁ := (Option.some_inj.mp (hstp'.symm.trans hstep1))
      subst hnexteq
      refine ⟨?_, ?_, ?_⟩
      · rw [hchoice, Tape.move_cells]
        exact hcells
      · refine ⟨?_, ?_⟩
        · rw [hchoice, Tape.move_cells]
          exact hsi.1
        · intro j hj
          rw [hchoice, Tape.move_cells]
          exact hsi.2 j hj
      · rw [hchoice]
        show 1 ≤ ((dmid.work (Fin.last k)).move Dir3.right).head
        show 1 ≤ (dmid.work (Fin.last k)).head + 1
        omega


/-- **A counter tape reads exactly as the choice sequence of its value.** Combining the encoding
bridge with the bit correspondence: if the choice tape carries the canonical representation of
`v`, then the stream the path simulator consumes is `choicesOfNat T v` — no padding, no copy, and
no fixed-width counter. -/
theorem choiceStream_eq_choicesOfNat {k : ℕ} {tm : NTM k} (c : Cfg (k + 1) tm.Q) (v T : ℕ)
    (h : (c.work (Fin.last k)).HasBinaryNat v) (j : Fin T) :
    choiceStream c j.val = choicesOfNat T v j := by
  rw [choiceStream_of_hasBinaryString c v.bits h.2, choicesOfNat_apply, getD_eq_bit,
    binValLE_bits]


/-- A canonical binary tape carries its left marker and nothing else does. -/
theorem hasBinaryNat_startInvariant {t : Tape} {v : ℕ} (h : t.HasBinaryNat v) :
    t.StartInvariant := by
  obtain ⟨h0, -, hin, hout⟩ := h
  refine ⟨h0, fun j hj => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  by_cases hi : i < v.bits.length
  · rw [hin i hi]
    cases v.bits[i] <;> simp [Γ.ofBool]
  · rw [hout i (by omega)]
    simp

/-- **What the simulation computes from a counter value.** Started with the counter tape carrying
`v` and the machine's own tapes in their initial configuration, the path simulator produces
exactly the trace of `tm` along the choice sequence `choicesOfNat T v`. -/
theorem choiceTM_dropChoice_eq {k : ℕ} (tm : NTM k) (x : List Bool) (T v : ℕ)
    (c : Cfg (k + 1) tm.Q) (hdrop : dropChoice c = tm.initCfg x)
    (hv : (c.work (Fin.last k)).HasBinaryNat v) :
    ∃ c' t, t ≤ T ∧ (choiceTM tm).reachesIn t c c' ∧
      dropChoice c' = tm.trace T (choicesOfNat T v) (tm.initCfg x) := by
  have hinv := hasBinaryNat_startInvariant hv
  have hhead : 1 ≤ (c.work (Fin.last k)).head := by
    rw [hv.2.1]
  obtain ⟨c', t, hle, hreach, -, heq⟩ := choiceTM_simulates tm T c hinv hhead
  refine ⟨c', t, hle, hreach, heq.trans ?_⟩
  rw [hdrop]
  congr 1
  funext j
  exact choiceStream_eq_choicesOfNat c v T hv j

/-- **What the loop body's simulation computes.** Started from the delayed machine's
post-sentinel configuration — every head at cell one, the counter carrying `v`, the machine's own
tapes blank — the path simulator produces exactly the source machine's trace along the choice
sequence `v` encodes.

Two corrections cancel here. Entering after the sentinel step costs one step of the delayed
machine, and the delay itself costs one; together they are exactly the two steps
`NTM.delayNTM_trace_initCfg` charges, so the horizon `T` on the counter is the source machine's
own horizon, with no off-by-one left over. -/
theorem choiceTM_delay_dropChoice_eq {k : ℕ} (tm : NTM k) (x : List Bool)
    (hne : tm.qstart ≠ tm.qhalt) (T v : ℕ) (hT : 1 ≤ T)
    (c : Cfg (k + 1) (delayNTM tm).Q)
    (hdrop : dropChoice c
      = (delayNTM tm).trace 1 (fun _ => false) ((delayNTM tm).initCfg x))
    (hv : (c.work (Fin.last k)).HasBinaryNat v) :
    ∃ c' t, t ≤ T ∧ (choiceTM (delayNTM tm)).reachesIn t c c' ∧
      dropChoice c' = delayEmbed tm (tm.trace T (choicesOfNat T v) (tm.initCfg x)) := by
  obtain ⟨S, rfl⟩ : ∃ S, T = S + 1 := ⟨T - 1, by omega⟩
  have hinv := hasBinaryNat_startInvariant hv
  have hhead : 1 ≤ (c.work (Fin.last k)).head := by rw [hv.2.1]
  obtain ⟨c', t, hle, hreach, -, heq⟩ := choiceTM_simulates (delayNTM tm) (S + 1) c hinv hhead
  refine ⟨c', t, hle, hreach, ?_⟩
  have hstream : (fun j : Fin (S + 1) => choiceStream c j.val) = choicesOfNat (S + 1) v := by
    funext j
    exact choiceStream_eq_choicesOfNat c v (S + 1) hv j
  refine heq.trans ?_
  rw [hstream, hdrop]
  have hsplit := NTM.trace_succ (delayNTM tm) (S + 1)
    (Fin.cons false (choicesOfNat (S + 1) v)) ((delayNTM tm).initCfg x)
  have hA : (delayNTM tm).trace (S + 2) (Fin.cons false (choicesOfNat (S + 1) v))
        ((delayNTM tm).initCfg x)
      = (delayNTM tm).trace (S + 1) (choicesOfNat (S + 1) v)
        ((delayNTM tm).trace 1 (fun _ => false) ((delayNTM tm).initCfg x)) := by
    rw [hsplit]
    congr 1
  rw [← hA, delayNTM_trace_initCfg tm x hne S (Fin.cons false (choicesOfNat (S + 1) v)),
    Fin.tail_cons]

/-- **The loop body's simulation, run to a halt with its verdict.** The counter's value selects
a path, the simulation follows it to the end, and the halted configuration's verdict cell holds
exactly the bit the tally is counting. -/
theorem choiceTM_delay_haltsIn {k : ℕ} (tm : NTM k) (x : List Bool)
    (hne : tm.qstart ≠ tm.qhalt) {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f)
    (T v : ℕ) (hT : 1 ≤ T) (hfT : f x.length ≤ T)
    (c : Cfg (k + 1) (delayNTM tm).Q)
    (hdrop : dropChoice c
      = (delayNTM tm).trace 1 (fun _ => false) ((delayNTM tm).initCfg x))
    (hv : (c.work (Fin.last k)).HasBinaryNat v) :
    ∃ c' t, t ≤ T ∧ (choiceTM (delayNTM tm)).reachesIn t c c' ∧
      (choiceTM (delayNTM tm)).halted c' ∧
      decide (c'.output.cells 1 = Γ.one) = acceptsAt tm x T v := by
  obtain ⟨c', t, hle, hreach, heq⟩ :=
    choiceTM_delay_dropChoice_eq tm x hne T v hT c hdrop hv
  have hsrc : (tm.trace T (choicesOfNat T v) (tm.initCfg x)).state = tm.qhalt := by
    have hfrozen := tm.trace_mono (T := f x.length) (T' := T) hfT
      (choices := fun j => choicesOfNat T v ⟨j.val, by omega⟩)
      (choices' := choicesOfNat T v) (fun _ => rfl) (hall x _)
    rw [hfrozen]
    exact hall x _
  have hstate : c'.state = (dropChoice c').state := rfl
  have hout : c'.output = (dropChoice c').output := rfl
  refine ⟨c', t, hle, hreach, ?_, ?_⟩
  · show c'.state = (delayNTM tm).qhalt
    rw [hstate, heq]
    exact (delayEmbed_halted_iff tm _).mpr hsrc
  · rw [acceptsAt, hout, heq]
    have houteq : (delayEmbed tm (tm.trace T (choicesOfNat T v) (tm.initCfg x))).output
        = (tm.trace T (choicesOfNat T v) (tm.initCfg x)).output := rfl
    rw [houteq]
    refine (decide_eq_decide.mpr ?_).symm
    exact ⟨fun h => h.2, fun h => ⟨hsrc, h⟩⟩

/-- **The verdict the loop body reads is the enumeration's acceptance test.** -/
theorem choiceTM_verdict {k : ℕ} (tm : NTM k) (x : List Bool) (T v : ℕ)
    {c' : Cfg (k + 1) tm.Q}
    (heq : dropChoice c' = tm.trace T (choicesOfNat T v) (tm.initCfg x)) :
    decide (c'.state = tm.qhalt ∧ c'.output.cells 1 = Γ.one) = acceptsAt tm x T v := by
  have hstate : c'.state = (dropChoice c').state := rfl
  have hout : c'.output = (dropChoice c').output := rfl
  rw [acceptsAt, hstate, hout, heq]


/-- **The counting loop, granted only that the body advances the triple.** The body's obligation
no longer mentions iterates or tallies: from a state holding `(v, a, r)` it must reach the state
holding `(v + 1, a + [P v], r + [¬P v])`. All the counting bookkeeping is discharged here. -/
theorem tallyLoop_hoareTime_of_body {n : ℕ} (tmBody tmTest : TM n) (cIdx aIdx rIdx : Fin n)
    (I : Tape) (rest : Fin n → Tape) (P : ℕ → Bool) {post : TapePred n} (N b : ℕ)
    (hbody : ∀ v a r : ℕ, v < N → ∀ inp work out,
      tallyState cIdx aIdx rIdx I rest (v, a, r) inp work out →
      ∃ inp' work' out' t, t ≤ b ∧
        (TM.loopTM tmBody tmTest).reachesIn t
          ⟨(TM.loopTM tmBody tmTest).qstart, inp, work, out⟩
          ⟨(TM.loopTM tmBody tmTest).qstart, inp', work', out'⟩ ∧
        tallyState cIdx aIdx rIdx I rest
          (v + 1, a + (if P v then 1 else 0), r + (if P v then 0 else 1)) inp' work' out')
    (hstop : ∀ inp work out,
      tallyState cIdx aIdx rIdx I rest (N, tally P N, tally (fun v => !P v) N) inp work out →
      ∃ c' t, t ≤ b ∧
        (TM.loopTM tmBody tmTest).reachesIn t
          ⟨(TM.loopTM tmBody tmTest).qstart, inp, work, out⟩ c' ∧
        (TM.loopTM tmBody tmTest).halted c' ∧ post c'.input c'.work c'.output) :
    (TM.loopTM tmBody tmTest).HoareTime
      (tallyState cIdx aIdx rIdx I rest (0, 0, 0)) post ((N + 1) * b) := by
  refine tallyLoop_hoareTime tmBody tmTest cIdx aIdx rIdx I rest P N b ?_ ?_
  · intro j hj inp work out h
    rw [tallyStep_iterate] at h
    obtain ⟨inp', work', out', t, ht, hreach, h'⟩ :=
      hbody j (tally P j) (tally (fun v => !P v) j) hj inp work out h
    refine ⟨inp', work', out', t, ht, hreach, ?_⟩
    rw [tallyStep_iterate]
    have hflip : (if !P j then 1 else 0) = (if P j then 0 else 1) := by cases P j <;> simp
    have e1 : tally P (j + 1) = tally P j + (if P j then 1 else 0) := rfl
    have e2 : tally (fun v => !P v) (j + 1)
        = tally (fun v => !P v) j + (if P j then 0 else 1) := by
      show tally (fun v => !P v) j + (if !P j then 1 else 0) = _
      rw [hflip]
    rw [e1, e2]
    exact h'
  · intro inp work out h
    rw [tallyStep_iterate] at h
    exact hstop inp work out h


/-- **The inner call as the loop's test, placed.** `TM.ifTM` branches on the *real* output tape's
verdict cell, and the path simulator already writes `tm`'s verdict there — so the simulation can
serve directly as the conditional's test, with no output retargeting. Only the lift into the
larger tape space is needed, and that is free. -/
theorem choiceTM_lifted_keepsWindow {k : ℕ} (tm : NTM k) {f : ℕ → ℕ}
    (hall : tm.AllPathsHaltIn f) (x : List Bool) (m : ℕ) (c₀ : Cfg (k + 1) tm.Q)
    {inputLength h₀ : ℕ}
    (hdrop : dropChoice c₀ = tm.initCfg x)
    (hinv : (c₀.work (Fin.last k)).StartInvariant)
    (hhead : 1 ≤ (c₀.work (Fin.last k)).head)
    (hheads : ∀ i, (c₀.work i).head ≤ h₀)
    (hin : c₀.input.head ≤ inputLength + h₀ + 1)
    (hout : c₀.output.head ≤ h₀ + 1) :
    ∀ D, ((choiceTM tm).liftTM m).reaches ((choiceTM tm).liftCfg m c₀) D →
      D.WithinDecisionSpace inputLength (h₀ + (f x.length + 1)) :=
  TM.liftTM_keepsWindow_of_reaches (choiceTM tm) m c₀ (by omega)
    (choiceTM_keepsWindowOn tm hall x c₀ ⟨hdrop, hinv, hhead, hheads, hin, hout⟩)

end NTM

end Complexity
