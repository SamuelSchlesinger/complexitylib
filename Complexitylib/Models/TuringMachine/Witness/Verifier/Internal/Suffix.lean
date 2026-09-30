/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Witness.Verifier.Internal.Pair
public import Complexitylib.Models.TuringMachine.Witness.Verifier.Internal.Run
public import Complexitylib.Models.TuringMachine.Witness.Verifier.Defs

/-!
# Deterministic finite-verifier suffix

Compose the framed pair builder and placed verifier without charging verifier
time as space. All ordinary scratch remains charged; the actual output stays
on the output tape throughout.
-/

@[expose] public section

namespace Complexity
namespace WitnessTM.Verifier
section
open TM
variable {k : ℕ}

private theorem witnessIdx_ne_pairIdx (r k : ℕ) : witnessIdx r k ≠ pairIdx r k := by
  intro h
  have := congrArg Fin.val h
  simp [witnessIdx, pairIdx] at this

private theorem verifier_frame_eq (r : ℕ) (M : TM k) (z : List Bool)
    (inp : Tape) (work : Fin (tapes r k) → Tape)
    (hw : ∀ i, r + 1 ≤ i.val → i.val < r + 1 + k → work i = parkedBlank)
    (hp : work (pairIdx r k) = (Tape.init (z.map Γ.ofBool)).move Dir3.right) :
    work = (placeWorkCfg (retargetInputStarted M) (r + 1) 1 work
      (retargetInputStartedCfg M z inp)).work := by
  funext i
  by_cases hi : placeWorkInMiddle (r + 1) (k + 1) (post := 1) i
  · rw [← placeWorkIdx_placeWorkCoord (pre := r + 1) (n := k + 1) (post := 1) i hi,
      placeWorkCfg_work_middle]
    let j := placeWorkCoord (r + 1) (k + 1) (post := 1) i hi
    change work (placeWorkIdx (r + 1) 1 j) = (retargetInputStartedCfg M z inp).work j
    by_cases hj : j.val < k
    · rw [retargetInputStartedCfg_work_lt M z inp j hj]
      exact hw _ (by simp) (by simp; omega)
    · have hj' : j = Fin.last k := Fin.ext (by have := j.isLt; simp; omega)
      have hpidx : placeWorkIdx (r + 1) 1 (Fin.last k) = pairIdx r k := by
        apply Fin.ext
        simp [placeWorkIdx, pairIdx]
      rw [hj', hpidx, hp]
      simp [retargetInputStartedCfg]
  · rw [placeWorkCfg_work_extra (retargetInputStarted M) (r + 1) 1 work
      (retargetInputStartedCfg M z inp) i hi]

/-- The pair endpoint and its safety bound yield the exact, fully charged
entry configuration for the placed verifier after the one-step handoff. -/
private theorem suffix_seam (r : ℕ) (M : TM k) (x y : List Bool)
    (extras : Fin (tapes r k) → Tape) {H : ℕ} (hH : 1 ≤ H)
    (hblank : ∀ i, r + 1 ≤ i.val → i.val < r + 1 + k → extras i = parkedBlank)
    {inp out : Tape} {work : Fin (tapes r k) → Tape}
    (hp : PairBuildFramePost (witnessIdx r k) (pairIdx r k) x y extras
      parkedBlank inp work out)
    (hs : (⟨(), inp, work, out⟩ : Cfg (tapes r k) Unit).WithinDecisionSpace x.length H) :
    (transitionInput inp).StartInvariant ∧
    (∀ i, (transitionTape (work i)).StartInvariant) ∧
    (∀ i, 1 ≤ (transitionTape (work i)).head) ∧
    (∀ i, (transitionTape (work i)).head ≤ H) ∧
    max (transitionInput inp).head 1 ≤ x.length + H + 1 ∧
    (fun i => transitionTape (work i)) =
      (placeWorkCfg (retargetInputStarted M) (r + 1) 1
        (fun i => transitionTape (work i))
        (retargetInputStartedCfg M (pair x y) (transitionInput inp))).work ∧
    transitionTape out = parkedBlank := by
  rcases hp with ⟨hp, ho, hf, hiSI, hwSI, hoSI⟩
  have hb : transitionTape parkedBlank = parkedBlank :=
    transitionTape_eq_self (by decide)
  refine ⟨startInvariant_transitionInput hiSI,
    fun i => startInvariant_transitionTape (hwSI i),
    fun i => one_le_head_transitionTape _ (hwSI i).1, ?_, ?_, ?_, ?_⟩
  · intro i
    exact le_trans (head_transitionTape_le_max (hwSI i)) (max_le (hs.1.1 i) hH)
  · have hh := head_transitionInput_le_max hiSI
    have hh' := hs.1.2
    exact max_le (le_trans hh (max_le hh' (by omega))) (by omega)
  · apply verifier_frame_eq r M (pair x y)
    · intro i hil hiu
      have hiy : i ≠ witnessIdx r k := by
        intro h; have := congrArg Fin.val h; simp [witnessIdx] at this; omega
      have hip : i ≠ pairIdx r k := by
        intro h; have := congrArg Fin.val h; simp [pairIdx] at this; omega
      rw [hf i hiy hip, hblank i hil hiu, hb]
    · rw [hp]
      exact transitionTape_eq_self
        (((Tape.StartInvariant.init_ofBool (pair x y)).move .right).2 _ (by
          simp [Tape.move, Tape.init]))
  · rw [ho, hb]

/-- Once a concrete finite certificate is stored, the deterministic suffix
builds the pair and produces the verifier's exact verdict within its original
time/space contract. Setup scratch is retained as ordinary charged work. -/
theorem suffix_hoareTimeSafety_decide (r : ℕ) (M : TM k)
    {L : Language} {T S : ℕ → ℕ} (hdec : M.DecidesInTimeSpace L T S)
    (x y : List Bool) (extras : Fin (tapes r k) → Tape)
    (hextraSI : ∀ i, i ≠ witnessIdx r k → i ≠ pairIdx r k → (extras i).StartInvariant)
    (hextraPos : ∀ i, i ≠ witnessIdx r k → i ≠ pairIdx r k → 1 ≤ (extras i).head)
    (hblank : ∀ i, r + 1 ≤ i.val → i.val < r + 1 + k → extras i = parkedBlank)
    {initialSpace H : ℕ} (hinit : 1 ≤ initialSpace)
    (hextraH : ∀ i, i ≠ witnessIdx r k → i ≠ pairIdx r k →
      (extras i).head ≤ initialSpace)
    (hpairH : initialSpace + pairBuildTime x.length y.length ≤ H)
    (hverifyH : (pair x y).length + S (pair x y).length + 1 ≤ H) :
    (suffix r M).HoareTime
      (PairBuildFramePre (witnessIdx r k) (pairIdx r k) x y extras parkedBlank)
      (fun _ _ out => (pair x y ∈ L → out.cells 1 = Γ.one) ∧
        (pair x y ∉ L → out.cells 1 = Γ.zero))
      (pairBuildTime x.length y.length + 1 + T (pair x y).length) ∧
    (suffix r M).HoareSafety
      (PairBuildFramePre (witnessIdx r k) (pairIdx r k) x y extras parkedBlank)
      (fun inp work out =>
        (⟨(), inp, work, out⟩ : Cfg (tapes r k) Unit).WithinDecisionSpace x.length H) := by
  let pre := PairBuildFramePre (witnessIdx r k) (pairIdx r k) x y extras parkedBlank
  let safe : TapePred (tapes r k) := fun inp work out =>
    (⟨(), inp, work, out⟩ : Cfg (tapes r k) Unit).WithinDecisionSpace x.length H
  let mid : TapePred (tapes r k) := fun inp work out =>
    PairBuildFramePost (witnessIdx r k) (pairIdx r k) x y extras parkedBlank inp work out ∧
      safe inp work out
  let mid' : TapePred (tapes r k) := fun inp work out =>
    ∃ inp₀ work₀ out₀, mid inp₀ work₀ out₀ ∧ inp = transitionInput inp₀ ∧
      work = (fun i => transitionTape (work₀ i)) ∧ out = transitionTape out₀
  have hne := witnessIdx_ne_pairIdx r k
  have htime := pairBuildTM_hoareTime_framed (witnessIdx r k) (pairIdx r k) hne
    x y extras parkedBlank (Tape.StartInvariant.init_nil.move .right) (by decide)
    hextraSI hextraPos
  have hsafety : (pairBuildTM (witnessIdx r k) (pairIdx r k)).HoareSafety pre safe := by
    refine (pairBuildTM_hoareSafety_framed (witnessIdx r k) (pairIdx r k) hne
      x y extras parkedBlank initialSpace hinit hextraH (by
        simp [parkedBlank, Tape.move, Tape.init])).consequence (fun _ _ _ h => h) ?_
    intro inp work out hs
    exact ⟨⟨fun i => le_trans (hs.1.1 i) hpairH,
      by have := hs.1.2; dsimp only at this ⊢; omega⟩,
      by have := hs.2; dsimp only at this ⊢; omega⟩
  have h₁ : (pairBuildTM (witnessIdx r k) (pairIdx r k)).HoareTime pre mid
      (pairBuildTime x.length y.length) := by
    intro inp work out hp
    obtain ⟨c, t, ht, hc, hh, hpost⟩ := htime inp work out hp
    exact ⟨c, t, ht, hc, hh, hpost, hsafety inp work out hp c
      (reaches_of_reachesIn hc)⟩
  have htrans : ∀ inp work out, mid inp work out →
      mid' (transitionInput inp) (fun i => transitionTape (work i)) (transitionTape out) :=
    fun inp work out hp => ⟨inp, work, out, hp, rfl, rfl, rfl⟩
  have hrun : ∀ inp work out, mid' inp work out →
      (placeWorkTM (r + 1) 1 (retargetInputStarted M)).HoareTime
        (fun i w o => i = inp ∧ w = work ∧ o = out)
        (fun _ _ out => (pair x y ∈ L → out.cells 1 = Γ.one) ∧
          (pair x y ∉ L → out.cells 1 = Γ.zero)) (T (pair x y).length) ∧
      (placeWorkTM (r + 1) 1 (retargetInputStarted M)).HoareSafety
        (fun i w o => i = inp ∧ w = work ∧ o = out) safe := by
    rintro inp work out ⟨inp₀, work₀, out₀, hp, rfl, rfl, rfl⟩
    obtain ⟨hiSI, hwSI, hwPos, hwH, hiH, hwEq, hoEq⟩ :=
      suffix_seam r M x y extras (by omega) hblank hp.1 hp.2
    have hv := placeWorkTM_retargetInputStarted_hoareTimeSafety_decide M hdec (pair x y)
      (transitionInput inp₀) hiSI (r + 1) 1 (fun i => transitionTape (work₀ i))
      (fun i _ => hwSI i) (fun i _ => hwPos i) hverifyH hiH (fun i _ => hwH i)
    constructor
    · exact hv.1.consequence
        (fun i w o h => ⟨h.1, h.2.1.trans hwEq, h.2.2.trans hoEq⟩)
        (fun _ _ _ h => h.1) le_rfl
    · exact hv.2.consequence
        (fun i w o h => ⟨h.1, h.2.1.trans hwEq, h.2.2.trans hoEq⟩)
        (fun _ _ _ h => h)
  have h₂ : (placeWorkTM (r + 1) 1 (retargetInputStarted M)).HoareTime mid'
      (fun _ _ out => (pair x y ∈ L → out.cells 1 = Γ.one) ∧
        (pair x y ∉ L → out.cells 1 = Γ.zero)) (T (pair x y).length) :=
    fun inp work out hp => (hrun inp work out hp).1 inp work out ⟨rfl, rfl, rfl⟩
  have hs₂ : (placeWorkTM (r + 1) 1 (retargetInputStarted M)).HoareSafety mid' safe :=
    fun inp work out hp => (hrun inp work out hp).2 inp work out ⟨rfl, rfl, rfl⟩
  exact ⟨seqTM_hoareTime _ _ h₁ htrans h₂,
    seqTM_hoareSafety _ _ h₁ htrans h₂ hsafety hs₂⟩

end
end WitnessTM.Verifier
end Complexity
