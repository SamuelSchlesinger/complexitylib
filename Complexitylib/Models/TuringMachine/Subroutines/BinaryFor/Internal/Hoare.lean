/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Internal.Comparison
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Internal.Control
public import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc
public import Complexitylib.Models.TuringMachine.Hoare
public import Complexitylib.Models.TuringMachine.Registers
public import Complexitylib.Models.TuringMachine.GuessAssembly

/-!
# Canonical binary count-up loops — Hoare-style driver, internal proofs

`BinaryForLoopSpec` asks a client for a canonical configuration at every loop
index, which presumes a body whose tape effect is available in closed form.
Bodies assembled from Hoare triples do not have that shape: their contracts
only assert that *some* halting run exists. This module closes the gap by
running the loop composition directly on existential contracts, so a client
needs nothing but a per-index triple for its body.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- A canonical binary tape is parked: its head sits off the left marker and
no cell to the right of cell zero holds `▷`. -/
theorem Parked.of_hasBinaryNat {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : Parked t :=
  ⟨by rw [h.2.1], Tape.HasBinaryContent.cells_ne_start h.2.2⟩

/-- Canonical successor turns the body's postcondition back into the loop
frame at the next counter value. -/
private theorem binarySuccTM_binaryForFrame_hoareTime
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (limitValue : ℕ) (P : ℕ → TapePred n) (value : ℕ) :
    (binarySuccTM counterIdx).HoareTime
      (BinaryForBodyPost counterIdx limitIdx limitValue P value)
      (BinaryForFrame counterIdx limitIdx limitValue P (value + 1))
      (binarySuccTime value) := by
  intro inp work out hpre
  obtain ⟨hcnt, hlim, hinp, hwork, hout, hnext⟩ := hpre
  obtain ⟨c', hreach, hhalt, hinp', hother', hcnt', hout'⟩ :=
    binarySuccTM_reachesIn_frame counterIdx value inp work out hcnt hinp
      (fun i hi => hwork i) hout
  refine ⟨c', binarySuccTime value, Nat.le_refl _, hreach, hhalt, ?_⟩
  have hupd : c'.work = Function.update work counterIdx (c'.work counterIdx) := by
    funext i
    by_cases hi : i = counterIdx
    · subst hi
      rw [Function.update_self]
    · rw [Function.update_of_ne hi, hother' i hi]
  refine ⟨?_, hcnt', ?_, ?_, ?_, ?_⟩
  · rw [hinp', hout', hupd]
    exact hnext _ hcnt'
  · rw [hother' limitIdx (Ne.symm hne)]
    exact hlim
  · rw [hinp']
    exact hinp
  · intro i
    by_cases hi : i = counterIdx
    · subst hi
      exact (Parked.of_hasBinaryNat hcnt').read_ne_start
    · rw [hother' i hi]
      exact hwork i
  · rw [hout']
    exact hout

/-- The `seqTM` seam between the body and the successor preserves the body's
postcondition, since every head is off the left marker. -/
private theorem binaryForBodyPost_transition
    (counterIdx limitIdx : Fin n) (limitValue : ℕ) (P : ℕ → TapePred n)
    (value : ℕ) :
    ∀ inp work out,
      BinaryForBodyPost counterIdx limitIdx limitValue P value inp work out →
      BinaryForBodyPost counterIdx limitIdx limitValue P value
        (transitionInput inp) (fun i => transitionTape (work i))
        (transitionTape out) := by
  intro inp work out hmid
  have hinp : transitionInput inp = inp :=
    transitionInput_eq_self hmid.2.2.1
  have hwork : (fun i => transitionTape (work i)) = work :=
    funext fun i => transitionTape_eq_self (hmid.2.2.2.1 i)
  have hout : transitionTape out = out :=
    transitionTape_eq_self hmid.2.2.2.2.1
  rw [hinp, hwork, hout]
  exact hmid

/-- One composite iteration — body, seam, successor — carries the loop frame
from `value` to `value + 1` in the advertised time. -/
private theorem binaryForIterationTM_hoareTime
    (body : TM n) (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (limitValue : ℕ) (bodyTime : ℕ → ℕ) (P : ℕ → TapePred n) (value : ℕ)
    (hbody : body.HoareTime
      (BinaryForFrame counterIdx limitIdx limitValue P value)
      (BinaryForBodyPost counterIdx limitIdx limitValue P value)
      (bodyTime value)) :
    (binaryForIterationTM body counterIdx).HoareTime
      (BinaryForFrame counterIdx limitIdx limitValue P value)
      (BinaryForFrame counterIdx limitIdx limitValue P (value + 1))
      (binaryForIterationTime bodyTime value) :=
  seqTM_hoareTime body (binarySuccTM counterIdx) hbody
    (binaryForBodyPost_transition counterIdx limitIdx limitValue P value)
    (binarySuccTM_binaryForFrame_hoareTime counterIdx limitIdx hne limitValue
      P value)

/-- The remaining count-up loop runs from any frame-satisfying start. -/
private theorem binaryForTM_loop_hoareTime
    (body : TM n) (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (limitValue : ℕ) (bodyTime : ℕ → ℕ) (P : ℕ → TapePred n)
    (hbody : ∀ value, value < limitValue →
      body.HoareTime (BinaryForFrame counterIdx limitIdx limitValue P value)
        (BinaryForBodyPost counterIdx limitIdx limitValue P value)
        (bodyTime value)) :
    ∀ count value, value + count = limitValue →
      (binaryForTM body counterIdx limitIdx).HoareTime
        (BinaryForFrame counterIdx limitIdx limitValue P value)
        (BinaryForFrame counterIdx limitIdx limitValue P limitValue)
        (binaryForLoopTime bodyTime limitValue value count) := by
  intro count
  induction count with
  | zero =>
    intro value hvalue inp work out hframe
    have hval : value = limitValue := by omega
    subst hval
    obtain ⟨hP, hcnt, hlim, hinp, hwork, hout⟩ := hframe
    refine ⟨{ state := .inl .done, input := inp, work := work, output := out },
      binaryForCompareTime value, Nat.le_refl _, ?_, rfl,
      ⟨hP, hcnt, hlim, hinp, hwork, hout⟩⟩
    exact binaryForTM_compare_reachesIn_frame_of_eq_internal body counterIdx limitIdx
      hne value inp work out hcnt hlim hinp (fun i hi hj => hwork i) hout
  | succ count ih =>
    intro value hvalue inp work out hframe
    have hlt : value < limitValue := by omega
    obtain ⟨hP, hcnt, hlim, hinp, hwork, hout⟩ := hframe
    have hcompare := binaryForTM_compare_reachesIn_frame_of_lt_internal body counterIdx
      limitIdx hne value limitValue hlt inp work out hcnt hlim hinp
      (fun i hi hj => hwork i) hout
    obtain ⟨c₂, t₂, ht₂, hreach₂, hhalt₂, hframe₂⟩ :=
      binaryForIterationTM_hoareTime body counterIdx limitIdx hne limitValue
        bodyTime P value (hbody value hlt) inp work out
        ⟨hP, hcnt, hlim, hinp, hwork, hout⟩
    have hlift := binaryForTM_iteration_reachesIn_internal body counterIdx
      limitIdx hreach₂
    have hseam := binaryForTM_step_iteration_halt_internal body counterIdx
      limitIdx c₂ hhalt₂ hframe₂.2.2.2.1 hframe₂.2.2.2.2.1 hframe₂.2.2.2.2.2
    obtain ⟨c₃, t₃, ht₃, hreach₃, hhalt₃, hpost₃⟩ :=
      ih (value + 1) (by omega) c₂.input c₂.work c₂.output hframe₂
    refine ⟨c₃, binaryForCompareTime limitValue + t₂ + 1 + t₃, ?_, ?_, hhalt₃,
      hpost₃⟩
    · simp only [binaryForLoopTime]
      omega
    · have r₁ := reachesIn_trans _ hcompare hlift
      have r₂ := reachesIn_trans _ r₁ (reachesIn.step hseam reachesIn.zero)
      exact reachesIn_trans _ r₂ hreach₃

/-- **A count-up loop from a contract for its body.** A body that carries the
loop frame from `value` to the pre-successor postcondition at every index runs
the whole loop, from counter zero to the limit, within the advertised time. -/
theorem binaryForTM_hoareTime_internal
    (body : TM n) (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (limitValue : ℕ) (bodyTime : ℕ → ℕ) (P : ℕ → TapePred n)
    (hbody : ∀ value, value < limitValue →
      body.HoareTime (BinaryForFrame counterIdx limitIdx limitValue P value)
        (BinaryForBodyPost counterIdx limitIdx limitValue P value)
        (bodyTime value)) :
    (binaryForTM body counterIdx limitIdx).HoareTime
      (BinaryForFrame counterIdx limitIdx limitValue P 0)
      (BinaryForFrame counterIdx limitIdx limitValue P limitValue)
      (binaryForLoopTime bodyTime limitValue 0 limitValue) :=
  binaryForTM_loop_hoareTime body counterIdx limitIdx hne limitValue bodyTime P
    hbody limitValue 0 (Nat.zero_add limitValue)

/-- The advancing states of a count-up loop are the body's, taken inside the
composite iteration. The driver and the counter's successor never consult the
guess tape. -/
def binaryForAdv {k : ℕ} {body : TM (k + 1)} (Adv : body.Q → Bool)
    (counterIdx limitIdx : Fin (k + 1)) :
    (binaryForTM body counterIdx limitIdx).Q → Bool :=
  Sum.elim (fun _ => false) (seqAdv Adv (fun _ => false))

/-- Canonical successor never consults the guess tape. -/
theorem guessProtocol_binarySuccTM {k : ℕ} (idx : Fin (k + 1))
    (hidx : idx ≠ Fin.last k) :
    GuessProtocol (binarySuccTM idx) (fun _ => false) := by
  have hne : Fin.last k ≠ idx := fun h => hidx h.symm
  refine ⟨?_, ?_, ?_⟩
  · intro q hq iHead wHeads oHead
    cases q with
    | carry => cases hw : wHeads idx <;> simp [binarySuccTM, hw, hne]
    | rewind => by_cases hs : wHeads idx = Γ.start <;> simp [binarySuccTM, hs]
    | done => exact absurd rfl hq
  · intro q hq iHead wHeads oHead hg
    cases q with
    | carry => cases hw : wHeads idx <;> simp [binarySuccTM, hw, hne, idleDir, hg]
    | rewind =>
      by_cases hs : wHeads idx = Γ.start <;>
        simp [binarySuccTM, hs, hne, idleDir, hg]
    | done => exact absurd rfl hq
  · intro q hq _ iHead ww oHead g g'
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hidx
    cases q with
    | carry =>
      simp only [binarySuccTM, Fin.snoc_castSucc]
      cases hw : ww j <;> simp [visible, Fin.snoc_castSucc]
    | rewind =>
      by_cases hs : ww j = Γ.start <;>
        simp [binarySuccTM, visible, Fin.snoc_castSucc, hs]
    | done => simp [binarySuccTM, visible, allIdle, Fin.snoc_castSucc]

/-- **The guess protocol survives a count-up loop.** The driver reads and
rewrites only the counter, the limit, and whatever the body touches, so a body
that consumes its guesses in the advancing states keeps doing so inside the
loop. -/
theorem guessProtocol_binaryForTM_internal {k : ℕ} {body : TM (k + 1)} {Adv : body.Q → Bool}
    (hbody : GuessProtocol body Adv) (counterIdx limitIdx : Fin (k + 1))
    (hcounter : counterIdx ≠ Fin.last k) (hlimit : limitIdx ≠ Fin.last k) :
    GuessProtocol (binaryForTM body counterIdx limitIdx)
      (binaryForAdv Adv counterIdx limitIdx) := by
  have hiter : GuessProtocol (binaryForIterationTM body counterIdx)
      (seqAdv Adv (fun _ => false)) :=
    guessProtocol_seqTM hbody (guessProtocol_binarySuccTM counterIdx hcounter)
  have hc : ¬ (Fin.last k = counterIdx) := fun h => hcounter h.symm
  have hl : ¬ (Fin.last k = limitIdx) := fun h => hlimit h.symm
  refine ⟨?_, ?_, ?_⟩
  · intro q hq iHead wHeads oHead
    match q with
    | .inl (.scan e) =>
      dsimp only [binaryForTM]
      split <;> rfl
    | .inl (.rewind e) =>
      dsimp only [binaryForTM]
      split <;> rfl
    | .inl .done => exact absurd rfl hq
    | .inr q =>
      by_cases hqh : q = (binaryForIterationTM body counterIdx).qhalt
      · subst hqh
        simp [binaryForTM, allReadBack]
      · have h := hiter.write q hqh iHead wHeads oHead
        simpa [binaryForTM, hqh] using h
  · intro q hq iHead wHeads oHead hg
    match q with
    | .inl (.scan e) =>
      dsimp only [binaryForTM, binaryForAdv]
      split <;> simp [hc, hl, idleDir, hg] <;> rfl
    | .inl (.rewind e) =>
      dsimp only [binaryForTM, binaryForAdv]
      split <;> simp [hc, hl, idleDir, hg] <;> rfl
    | .inl .done => exact absurd rfl hq
    | .inr q =>
      by_cases hqh : q = (binaryForIterationTM body counterIdx).qhalt
      · subst hqh
        simp [binaryForTM, binaryForAdv, seqAdv, allReadBack, idleDir, hg,
          binaryForIterationTM, seqTM]
      · have h := hiter.dir q hqh iHead wHeads oHead hg
        simp [binaryForTM, binaryForAdv, hqh]
        exact h
  · intro q hq hadv iHead ww oHead g g'
    obtain ⟨jc, hjc⟩ := Fin.exists_castSucc_eq.mpr hcounter
    obtain ⟨jl, hjl⟩ := Fin.exists_castSucc_eq.mpr hlimit
    match q with
    | .inl (.scan e) =>
      subst hjc
      subst hjl
      by_cases hb : ww jc = Γ.blank ∧ ww jl = Γ.blank <;>
        simp [binaryForTM, visible, Fin.snoc_castSucc, hb]
    | .inl (.rewind e) =>
      subst hjc
      subst hjl
      by_cases hb : ww jc = Γ.start ∧ ww jl = Γ.start <;>
        simp [binaryForTM, visible, Fin.snoc_castSucc, hb]
    | .inl .done => exact absurd rfl hq
    | .inr q =>
      by_cases hqh : q = (binaryForIterationTM body counterIdx).qhalt
      · subst hqh
        simp [binaryForTM, visible, allReadBack, Fin.snoc_castSucc]
      · have hadv' : ¬seqAdv Adv (fun _ => false) q = true := by
          simp only [binaryForAdv, Bool.not_eq_true] at hadv ⊢
          exact hadv
        have h := hiter.indep q hqh hadv' iHead ww
          oHead g g'
        simpa [binaryForTM, visible, hqh] using h

end TM

end Complexity
