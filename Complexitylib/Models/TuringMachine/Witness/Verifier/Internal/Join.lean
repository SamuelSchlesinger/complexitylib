/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Witness.Verifier.Internal.Prefix
public import Complexitylib.Models.TuringMachine.Witness.Verifier.Internal.Suffix

/-!
# Joining materialization and ordinary verification

The handoff carries a concrete stored certificate into the deterministic suffix.
The time window is a finite maximum, so verifier bounds need not be monotone.
The independent space window charges all intermediate ordinary storage.
-/

@[expose] public section

namespace Complexity
namespace WitnessTM.Verifier

/-- Entry to the deterministic suffix for one fixed finite certificate. -/
def suffixEntryFor (r k : ℕ) (x y : List Bool) (B : ℕ) : TapePred (tapes r k + 1) :=
  fun inp work out =>
    TM.PairBuildFramePre (witnessIdx r k) (pairIdx r k) x y
      (fun i => work i.castSucc) TM.parkedBlank inp (fun i => work i.castSucc) out ∧
    (∀ i, (work i).StartInvariant) ∧ (∀ i, 1 ≤ (work i).head) ∧
    (∀ i : Fin (tapes r k), r + 1 ≤ i.val → i.val < r + 1 + k →
      work i.castSucc = TM.parkedBlank) ∧
    ∀ i : Fin (tapes r k), (work i.castSucc).head ≤ 1 + NTM.guessBoundedTime B 0

/-- Materialization's endpoint passes to the suffix with all charged heads bounded. -/
theorem prefixPost_transition_for {inp out : Tape} {work : Fin (tapes r k + 1) → Tape}
    {x : List Bool} {B : ℕ} (y : List Bool)
    (h : prefixPost r k x B inp work out)
    (hw : work (witnessIdx r k).castSucc =
      (Tape.init (y.map Γ.ofBool)).move Dir3.right) :
    suffixEntryFor r k x y B (TM.transitionInput inp)
      (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
  obtain ⟨_, _, hi, ho, _, hb, _, hs, _, hh, _⟩ := h
  have hpark : ∀ z : List Bool,
      TM.transitionTape ((Tape.init (z.map Γ.ofBool)).move Dir3.right) =
        (Tape.init (z.map Γ.ofBool)).move Dir3.right := fun z =>
    TM.transitionTape_eq_self (TM.parked_init_input z).read_ne_start
  have hblank : TM.transitionTape TM.parkedBlank = TM.parkedBlank := by
    exact TM.transitionTape_eq_self (by decide)
  have hpw : work (pairIdx r k).castSucc = TM.parkedBlank := by
    apply hb
    · simp [pairIdx]
    · intro he
      have hv := congrArg Fin.val he
      simp [pairIdx, witnessIdx] at hv
  refine ⟨⟨?_, ?_, ?_, ?_, fun _ _ _ => rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [hi]
    exact TM.transitionInput_eq_self (TM.parked_init_input x).read_ne_start
  · dsimp only
    rw [hw, hpark]
  · dsimp only
    rw [hpw, hblank]
  · rw [ho, hblank]
  · intro i
    exact TM.startInvariant_transitionTape (hs i)
  · intro i
    exact TM.one_le_head_transitionTape _ (hs i).1
  · intro i hil hiu
    have hne : i ≠ witnessIdx r k := by
      intro he
      have hv := congrArg Fin.val he
      simp [witnessIdx] at hv
      omega
    dsimp only
    rw [hb i hil hne, hblank]
  · intro i
    exact (TM.head_transitionTape_le_max (hs i.castSucc)).trans
      (max_le (hh i) (by omega))

/-- The existential stored witness is retained through the phase handoff. -/
theorem prefixPost_transition {inp out : Tape} {work : Fin (tapes r k + 1) → Tape}
    {x : List Bool} {B : ℕ} (h : prefixPost r k x B inp work out) :
    ∃ y, y.length ≤ B ∧ suffixEntryFor r k x y B (TM.transitionInput inp)
      (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
  obtain ⟨y, hy, hi, ho, hw, rest⟩ := h
  exact ⟨y, hy, prefixPost_transition_for y ⟨y, hy, hi, ho, hw, rest⟩ hw⟩

/-- The finite window bounds a resource on every permitted certificate length. -/
theorem window_bounds (bound resource : ℕ → ℕ) (x y : List Bool)
    (hy : y.length ≤ bound x.length) :
    resource (pair x y).length ≤ window bound resource x.length := by
  rw [pair_length]
  exact Finset.le_sup (s := Finset.range (bound x.length + 1))
    (f := fun m => resource (2 * x.length + 2 + m)) (by simp; omega)

/-- The lifted suffix retains its ordinary verifier bounds and final exact verdict. -/
theorem liftedSuffix_for (setup : WitnessBoundSetup r bound) (M : TM k)
    {L : Language} {T S : ℕ → ℕ} (hM : M.DecidesInTimeSpace L T S)
    (x y : List Bool) (hy : y.length ≤ bound x.length) :
    (ofDeterministic (suffix r M)).machine.HoareTime
      (suffixEntryFor r k x y (bound x.length))
      (fun _ _ out => (pair x y ∈ L → out.cells 1 = Γ.one) ∧
        (pair x y ∉ L → out.cells 1 = Γ.zero))
      (TM.pairBuildTime x.length (bound x.length) + 1 + window bound T x.length) ∧
    (ofDeterministic (suffix r M)).machine.HoareSafety
      (suffixEntryFor r k x y (bound x.length))
      (fun inp work out =>
        (⟨(), inp, (fun i => work i.castSucc), out⟩ : Cfg (tapes r k) Unit).WithinDecisionSpace
          x.length (space setup S x.length)) := by
  have hpair : TM.pairBuildTime x.length y.length ≤
      TM.pairBuildTime x.length (bound x.length) := by
    simp only [TM.pairBuildTime]
    omega
  have ht := window_bounds bound T x y hy
  have hs := window_bounds bound S x y hy
  have hrun : ∀ inp work out, suffixEntryFor r k x y (bound x.length) inp work out →
      (suffix r M).HoareTime
        (TM.PairBuildFramePre (witnessIdx r k) (pairIdx r k) x y
          (fun i => work i.castSucc) TM.parkedBlank)
        (fun _ _ out => (pair x y ∈ L → out.cells 1 = Γ.one) ∧
          (pair x y ∉ L → out.cells 1 = Γ.zero))
        (TM.pairBuildTime x.length y.length + 1 + T (pair x y).length) ∧
      (suffix r M).HoareSafety
        (TM.PairBuildFramePre (witnessIdx r k) (pairIdx r k) x y
          (fun i => work i.castSucc) TM.parkedBlank)
        (fun inp work out =>
          (⟨(), inp, work, out⟩ : Cfg (tapes r k) Unit).WithinDecisionSpace
            x.length (space setup S x.length)) := by
    intro inp work out hp
    apply suffix_hoareTimeSafety_decide r M hM x y (fun i => work i.castSucc)
      (fun i _ _ => hp.2.1 i.castSucc) (fun i _ _ => hp.2.2.1 i.castSucc)
      hp.2.2.2.1 (initialSpace := 1 + NTM.guessBoundedTime (bound x.length) 0)
      (by omega) (fun i _ _ => hp.2.2.2.2 i)
    · have hle := le_trans (le_max_right (setup.space x.length)
        (1 + NTM.guessBoundedTime (bound x.length) 0 +
          TM.pairBuildTime x.length (bound x.length))) (le_max_left _
        (2 * x.length + 2 + bound x.length + window bound S x.length + 1))
      change _ ≤ space setup S x.length at hle
      omega
    · have hle := le_max_right
        (max (setup.space x.length) (1 + NTM.guessBoundedTime (bound x.length) 0 +
          TM.pairBuildTime x.length (bound x.length)))
        (2 * x.length + 2 + bound x.length + window bound S x.length + 1)
      change _ ≤ space setup S x.length at hle
      rw [pair_length] at hs ⊢
      omega
  constructor
  · intro inp work out hp
    have hread := (hp.2.1 (Fin.last (tapes r k))).read_ne_start
      (hp.2.2.1 (Fin.last (tapes r k)))
    have hlift := TM.liftLast_hoareTime (suffix r M) (hrun inp work out hp).1
      (work (Fin.last (tapes r k))) hread
    obtain ⟨c, t, htime, hr, hh, _, hv⟩ := hlift inp work out ⟨rfl, hp.1⟩
    exact ⟨c, t, by omega, hr, hh, hv⟩
  · intro inp work out hp c hc
    exact TM.liftLast_hoareSafety (suffix r M) (hrun inp work out hp).2
      inp work out hp.1 c hc

/-- Uniform suffix contract after an existentially chosen bounded certificate. -/
theorem suffixStage_contract (setup : WitnessBoundSetup r bound) (M : TM k)
    {L : Language} {T S : ℕ → ℕ} (hM : M.DecidesInTimeSpace L T S) (x : List Bool) :
    (ofDeterministic (suffix r M)).machine.HoareTime
      (fun inp work out => ∃ y, y.length ≤ bound x.length ∧
        suffixEntryFor r k x y (bound x.length) inp work out)
      (fun _ _ out => ∃ y, y.length ≤ bound x.length ∧
        (pair x y ∈ L → out.cells 1 = Γ.one) ∧ (pair x y ∉ L → out.cells 1 = Γ.zero))
      (TM.pairBuildTime x.length (bound x.length) + 1 + window bound T x.length) ∧
    (ofDeterministic (suffix r M)).machine.HoareSafety
      (fun inp work out => ∃ y, y.length ≤ bound x.length ∧
        suffixEntryFor r k x y (bound x.length) inp work out)
      (fun inp work out =>
        (⟨(), inp, (fun i => work i.castSucc), out⟩ : Cfg (tapes r k) Unit).WithinDecisionSpace
          x.length (space setup S x.length)) := by
  constructor
  · rintro inp work out ⟨y, hy, hp⟩
    obtain ⟨c, t, ht, hr, hh, hv⟩ := (liftedSuffix_for setup M hM x y hy).1 inp work out hp
    exact ⟨c, t, ht, hr, hh, y, hy, hv⟩
  · rintro inp work out ⟨y, hy, hp⟩ c hc
    exact (liftedSuffix_for setup M hM x y hy).2 inp work out hp c hc

end WitnessTM.Verifier
end Complexity
