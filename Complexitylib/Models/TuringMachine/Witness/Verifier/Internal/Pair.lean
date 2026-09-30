/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
public import Complexitylib.Classes.NP.Internal.PairBuildTM
public import Complexitylib.Models.TuringMachine.Frame
public import Complexitylib.Models.TuringMachine.Hoare.Safety

/-!
# Framed pair-builder phase

The output and inactive work tapes are ghost snapshots. Their heads must be
positive for exact preservation; their start invariants supply the later seam.
Space is charged on every ordinary work tape and the output, and includes only
this pair-building phase's runtime.
-/

@[expose] public section
namespace Complexity
namespace TM

/-- Canonical active tapes together with an arbitrary inactive frame. -/
def PairBuildFramePre (yIdx pIdx : Fin k) (x y : List Bool)
    (extras : Fin k → Tape) (out₀ : Tape) : TapePred k :=
  fun inp work out =>
    inp = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
    work yIdx = (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
    work pIdx = parkedBlank ∧ out = out₀ ∧
    ∀ i, i ≠ yIdx → i ≠ pIdx → work i = extras i

/-- Pair encoding, exact frame, and marker invariants needed at the next seam. -/
def PairBuildFramePost (yIdx pIdx : Fin k) (x y : List Bool)
    (extras : Fin k → Tape) (out₀ : Tape) : TapePred k :=
  fun inp work out =>
    work pIdx = (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right ∧
    out = out₀ ∧ (∀ i, i ≠ yIdx → i ≠ pIdx → work i = extras i) ∧
    inp.StartInvariant ∧ (∀ i, (work i).StartInvariant) ∧ out.StartInvariant

/-- Ordinary deterministic pair building preserves a parked, well-formed frame. -/
theorem pairBuildTM_hoareTime_framed
    (yIdx pIdx : Fin k) (hne : yIdx ≠ pIdx) (x y : List Bool)
    (extras : Fin k → Tape) (out₀ : Tape)
    (hout : out₀.StartInvariant) (houtHead : 1 ≤ out₀.head)
    (hextras : ∀ i, i ≠ yIdx → i ≠ pIdx → (extras i).StartInvariant)
    (hextraHeads : ∀ i, i ≠ yIdx → i ≠ pIdx → 1 ≤ (extras i).head) :
    (pairBuildTM yIdx pIdx).HoareTime
      (PairBuildFramePre yIdx pIdx x y extras out₀)
      (PairBuildFramePost yIdx pIdx x y extras out₀)
      (pairBuildTime x.length y.length) := by
  rintro inp work out ⟨hinp, hy, hp, ho, hf⟩
  obtain ⟨c, t, ht, hr, hh, hc⟩ :=
    pairBuildTM_hoareTime_all_started_initTape_move_right yIdx pIdx hne x y
      inp work out ⟨hinp, hy, hp⟩
  have hi : inp.StartInvariant := hinp ▸ (Tape.StartInvariant.init_ofBool x).move .right
  have hw : ∀ i, (work i).StartInvariant := by
    intro i
    by_cases hiy : i = yIdx
    · subst i
      rw [hy]
      exact (Tape.StartInvariant.init_ofBool y).move .right
    by_cases hip : i = pIdx
    · subst i
      rw [hp]
      exact Tape.StartInvariant.init_nil.move .right
    rw [hf i hiy hip]
    exact hextras i hiy hip
  have hoSI : out.StartInvariant := ho ▸ hout
  have htrace := (pairBuildTM yIdx pIdx).toNTM_trace_of_reachesIn
    hr hh le_rfl (fun _ => false)
  refine ⟨c, t, ht, hr, hh, hc, ?_, ?_, reachesIn_startInvariant hr hi hw hoSI⟩
  · have hread : out.read ≠ Γ.start := by
      rw [ho]
      exact hout.2 _ houtHead
    have hframe := pairBuildTM_trace_preserves_output yIdx pIdx t (fun _ => false)
      ⟨(pairBuildTM yIdx pIdx).qstart, inp, work, out⟩ hread
    rw [htrace] at hframe
    exact hframe.trans ho
  · intro i hiy hip
    have hread : (work i).read ≠ Γ.start := by
      rw [hf i hiy hip]
      exact (hextras i hiy hip).2 _ (hextraHeads i hiy hip)
    have hframe := pairBuildTM_trace_preserves_other_work yIdx pIdx i t
      (fun _ => false) ⟨(pairBuildTM yIdx pIdx).qstart, inp, work, out⟩ hiy hip hread
    rw [htrace] at hframe
    exact hframe.trans (hf i hiy hip)

/-- Every head is positive after the next sequential handoff. No positivity
claim about the active tapes before this handoff is needed. -/
theorem pairBuildFramePost_seam_heads
    {yIdx pIdx : Fin k} {x y : List Bool} {extras : Fin k → Tape} {out₀ inp out : Tape}
    {work : Fin k → Tape} (h : PairBuildFramePost yIdx pIdx x y extras out₀ inp work out) :
    1 ≤ (transitionInput inp).head ∧
      (∀ i, 1 ≤ (transitionTape (work i)).head) ∧ 1 ≤ (transitionTape out).head :=
  ⟨transitionInput_head_ge inp h.2.2.2.1.1,
    fun i => one_le_head_transitionTape (work i) (h.2.2.2.2.1 i).1,
    one_le_head_transitionTape out h.2.2.2.2.2.1⟩

/-- Every reachable prefix of pair building stays within the entry space plus
`4 * |x| + 2 * |y| + 10`; output travel is charged. The frame's initial heads are
bounded explicitly, and no downstream verifier runtime occurs in this bound. -/
theorem pairBuildTM_hoareSafety_framed
    (yIdx pIdx : Fin k) (hne : yIdx ≠ pIdx) (x y : List Bool)
    (extras : Fin k → Tape) (out₀ : Tape) (initialSpace : ℕ)
    (hspace : 1 ≤ initialSpace)
    (hextraHeads : ∀ i, i ≠ yIdx → i ≠ pIdx → (extras i).head ≤ initialSpace)
    (houtHead : out₀.head ≤ initialSpace + 1) :
    (pairBuildTM yIdx pIdx).HoareSafety
      (PairBuildFramePre yIdx pIdx x y extras out₀)
      (fun inp work out => (⟨(), inp, work, out⟩ : Cfg k Unit).WithinDecisionSpace
        x.length (initialSpace + pairBuildTime x.length y.length)) := by
  rintro inp work out ⟨hinp, hy, hp, ho, hf⟩ c hc
  obtain ⟨d, haltTime, htime, hr, hh, _⟩ :=
    pairBuildTM_hoareTime_all_started_initTape_move_right yIdx pIdx hne x y
      inp work out ⟨hinp, hy, hp⟩
  obtain ⟨t, ht⟩ := (pairBuildTM yIdx pIdx).reaches_to_reachesIn hc
  have hle := (pairBuildTM yIdx pIdx).reachesIn_le_halt ht hr hh
  have hinit : ∀ i, (work i).head ≤ initialSpace := by
    intro i
    by_cases hiy : i = yIdx
    · subst i
      simpa [hy, Tape.move, Tape.init] using hspace
    by_cases hip : i = pIdx
    · subst i
      simpa [hp, parkedBlank, Tape.move, Tape.init] using hspace
    rw [hf i hiy hip]
    exact hextraHeads i hiy hip
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    have hb := (pairBuildTM yIdx pIdx).work_head_reachesIn_bound ht i
    have hi := hinit i
    dsimp only at hb ⊢
    omega
  · have hb := (pairBuildTM yIdx pIdx).input_head_reachesIn_bound ht
    have hi : inp.head = 1 := by simp [hinp, Tape.move, Tape.init]
    dsimp only at hb ⊢
    omega
  · have hb := (pairBuildTM yIdx pIdx).output_head_reachesIn_bound ht
    have hi : out.head ≤ initialSpace + 1 := ho ▸ houtHead
    dsimp only at hb ⊢
    omega

end TM
end Complexity
