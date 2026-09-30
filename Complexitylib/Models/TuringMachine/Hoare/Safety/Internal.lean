/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Hoare.Safety.Defs
public import Complexitylib.Models.TuringMachine.Hoare
public import Complexitylib.Models.TuringMachine.SpaceTime.Internal.Reachability

/-!
# Sequential tape safety: proof internals

The standard finite-run decomposition transports arbitrary tape predicates,
including projected resource bounds, without another control-flow hierarchy.
-/

public section

namespace Complexity
namespace TM

/-- Sequential composition preserves any common tape safety predicate.
The second contract covers the boundary configuration itself. -/
theorem seqTM_hoareSafety_internal (tm₁ tm₂ : TM n)
    {pre mid mid' post safe : TapePred n} {b₁ b₂ : ℕ}
    (h₁ : tm₁.HoareTime pre mid b₁)
    (htrans : ∀ inp work out, mid inp work out →
      mid' (transitionInput inp) (fun i => transitionTape (work i))
        (transitionTape out))
    (h₂ : tm₂.HoareTime mid' post b₂)
    (hs₁ : tm₁.HoareSafety pre safe) (hs₂ : tm₂.HoareSafety mid' safe) :
    (seqTM tm₁ tm₂).HoareSafety pre safe := by
  intro inp work out hpre c hreach
  obtain ⟨c₁, t₁, _ht₁, hreach₁, hhalt₁, hmid⟩ :=
    h₁ inp work out hpre
  have hmid' := htrans c₁.input c₁.work c₁.output hmid
  obtain ⟨c₂, t₂, _ht₂, hreach₂, hhalt₂, _hpost⟩ :=
    h₂ (transitionInput c₁.input)
      (fun i => transitionTape (c₁.work i)) (transitionTape c₁.output) hmid'
  have hfull := seqTM_reachesIn_of_reachesIn tm₁ tm₂
    hreach₁ hhalt₁ hreach₂
  have hfullHalt :
      (seqTM tm₁ tm₂).halted (phase2Wrap tm₁ tm₂ c₂) :=
    (phase2Wrap_halted_iff tm₁ tm₂ c₂).2 hhalt₂
  obtain ⟨t, hreachT⟩ := (seqTM tm₁ tm₂).reaches_to_reachesIn hreach
  have ht : t ≤ t₁ + 1 + t₂ :=
    (seqTM tm₁ tm₂).reachesIn_le_halt hreachT hfull hfullHalt
  by_cases hphase₁ : t ≤ t₁
  · obtain ⟨d, hprefix, _hsuffix⟩ :=
      reachesIn_prefix_internal hreach₁ hphase₁
    have hwrapped := seqTM_reachesIn_phase1Wrap tm₁ tm₂ hprefix
    have hwrapped' :
        (seqTM tm₁ tm₂).reachesIn t
          { state := (seqTM tm₁ tm₂).qstart, input := inp,
            work := work, output := out }
          (phase1Wrap tm₁ tm₂ d) := by
      simpa [phase1Wrap, seqTM] using hwrapped
    have hc : c = phase1Wrap tm₁ tm₂ d :=
      (seqTM tm₁ tm₂).reachesIn_right_unique hreachT hwrapped'
    rw [hc]
    have hd := hs₁ inp work out hpre d
      (TM.reaches_of_reachesIn hprefix)
    exact hd
  · have hphase₂ : t₁ + 1 ≤ t := by omega
    let u := t - (t₁ + 1)
    have hu : u ≤ t₂ := by
      dsimp only [u]
      omega
    obtain ⟨d, hprefix, _hsuffix⟩ :=
      reachesIn_prefix_internal hreach₂ hu
    have hwrapped := seqTM_reachesIn_of_reachesIn tm₁ tm₂
      hreach₁ hhalt₁ hprefix
    have htime : t₁ + 1 + u = t := by
      dsimp only [u]
      omega
    rw [htime] at hwrapped
    have hc : c = phase2Wrap tm₁ tm₂ d :=
      (seqTM tm₁ tm₂).reachesIn_right_unique hreachT hwrapped
    rw [hc]
    have hd := hs₂ (transitionInput c₁.input)
      (fun i => transitionTape (c₁.work i)) (transitionTape c₁.output)
      hmid' d (TM.reaches_of_reachesIn hprefix)
    exact hd


end TM
end Complexity
