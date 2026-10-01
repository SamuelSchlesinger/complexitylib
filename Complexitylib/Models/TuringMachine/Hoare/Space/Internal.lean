/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Hoare.Space.Defs
public import Complexitylib.Models.TuringMachine.Hoare
import Complexitylib.Models.TuringMachine.Hoare.Safety
public import Complexitylib.Models.TuringMachine.SpaceTime.Internal.Reachability

/-!
# Space-aware Hoare specifications — proof internals

This module supplies structural rules, sequential composition, and the bridge
from fresh-start contracts to `TM.ComputesInSpace`.
-/


public section

namespace Complexity

namespace Cfg

/-- Internal monotonicity of the honest auxiliary-space predicate. -/
theorem WithinAuxSpace.mono_internal {c : Cfg n Q}
    {inputLength inputLength' space space' : ℕ}
    (h : c.WithinAuxSpace inputLength space)
    (hinput : inputLength ≤ inputLength') (hspace : space ≤ space') :
    c.WithinAuxSpace inputLength' space' := by
  constructor
  · intro i
    exact (h.1 i).trans hspace
  · calc
      c.input.head ≤ inputLength + space + 1 := h.2
      _ ≤ inputLength' + space' + 1 := by omega

/-- Internal phase-boundary bound: the standard input/work tape transition
moves every head by at most one. -/
theorem WithinAuxSpace.transition_internal {c : Cfg n Q}
    {inputLength space : ℕ} (h : c.WithinAuxSpace inputLength space) :
    ({ state := c.state,
       input := TM.transitionInput c.input,
       work := fun i => TM.transitionTape (c.work i),
       output := TM.transitionTape c.output } : Cfg n Q).WithinAuxSpace
      inputLength (space + 1) := by
  constructor
  · intro i
    calc
      (TM.transitionTape (c.work i)).head ≤ (c.work i).head + 1 :=
        Tape.head_writeAndMove_le _ _ _
      _ ≤ space + 1 := Nat.add_le_add_right (h.1 i) 1
  · calc
      (TM.transitionInput c.input).head ≤ c.input.head + 1 :=
        Tape.head_move_le _ _
      _ ≤ inputLength + space + 1 + 1 := Nat.add_le_add_right h.2 1
      _ = inputLength + (space + 1) + 1 := by omega

/-- Internal reachability rule: after `time` concrete transitions, one extra
auxiliary-space cell per transition covers every input and work head. -/
theorem WithinAuxSpace.reachesIn_internal {tm : TM n}
    {c c' : Cfg n tm.Q} {time inputLength space : ℕ}
    (h : c.WithinAuxSpace inputLength space)
    (hreach : tm.reachesIn time c c') :
    c'.WithinAuxSpace inputLength (space + time) := by
  constructor
  · intro i
    calc
      (c'.work i).head ≤ (c.work i).head + time :=
        tm.work_head_reachesIn_bound hreach i
      _ ≤ space + time := Nat.add_le_add_right (h.1 i) time
  · calc
      c'.input.head ≤ c.input.head + time :=
        tm.input_head_reachesIn_bound hreach
      _ ≤ inputLength + (space + time) + 1 := by
        have hinput := h.2
        omega

end Cfg

namespace TM

variable {n : ℕ}

/-- Internal: an inductive configuration predicate discharges a space contract. -/
theorem hoareSpace_of_invariant_internal {tm : TM n} {pre : TapePred n}
    {inputLength space : ℕ} (P : Cfg n tm.Q → Prop)
    (hinit : ∀ inp work out, pre inp work out →
      P { state := tm.qstart, input := inp, work := work, output := out })
    (hstep : ∀ c c', P c → tm.step c = some c' → P c')
    (hbound : ∀ c, P c → c.WithinAuxSpace inputLength space) :
    tm.HoareSpace pre inputLength space := by
  intro inp work out hpre c' hreach
  refine hbound c' ?_
  induction hreach with
  | refl => exact hinit inp work out hpre
  | tail _ hs ih => exact hstep _ _ ih hs

/-- Internal precondition weakening for all-reachable space contracts. -/
theorem HoareSpace.weaken_pre_internal {tm : TM n}
    {pre pre' : TapePred n} {inputLength space : ℕ}
    (h : tm.HoareSpace pre inputLength space)
    (hpre : ∀ inp work out, pre' inp work out → pre inp work out) :
    tm.HoareSpace pre' inputLength space := by
  intro inp work out hpre' c' hreach
  exact h inp work out (hpre inp work out hpre') c' hreach

/-- Internal numerical monotonicity for all-reachable space contracts. -/
theorem HoareSpace.mono_internal {tm : TM n}
    {pre : TapePred n} {inputLength inputLength' space space' : ℕ}
    (h : tm.HoareSpace pre inputLength space)
    (hinput : inputLength ≤ inputLength') (hspace : space ≤ space') :
    tm.HoareSpace pre inputLength' space' := by
  intro inp work out hpre c' hreach
  exact (h inp work out hpre c' hreach).mono_internal hinput hspace

/-- Internal time-to-space bridge. Determinism bounds every reachable prefix
by the terminating run supplied by the Hoare triple, and tape heads grow by at
most one cell per step. -/
theorem HoareTime.toHoareTimeSpace_internal {tm : TM n}
    {pre post : TapePred n} {time inputLength initialSpace : ℕ}
    (htime : tm.HoareTime pre post time)
    (hinitial : ∀ inp work out, pre inp work out →
      ({ state := tm.qstart, input := inp, work := work, output := out } :
        Cfg n tm.Q).WithinAuxSpace inputLength initialSpace) :
    tm.HoareTimeSpace pre post time inputLength (initialSpace + time) := by
  refine ⟨htime, ?_⟩
  intro inp work out hpre c hreach
  obtain ⟨cHalt, haltTime, hhaltTime, hrun, hhalt, _hpost⟩ :=
    htime inp work out hpre
  obtain ⟨t, hreachIn⟩ := tm.reaches_to_reachesIn hreach
  have ht : t ≤ haltTime := tm.reachesIn_le_halt hreachIn hrun hhalt
  have hstart := hinitial inp work out hpre
  exact (hstart.reachesIn_internal hreachIn).mono_internal le_rfl (by omega)

/-- Internal consequence rule for time-and-space Hoare contracts. -/
theorem HoareTimeSpace.consequence_internal {tm : TM n}
    {pre pre' post post' : TapePred n}
    {time time' inputLength inputLength' space space' : ℕ}
    (h : tm.HoareTimeSpace pre post time inputLength space)
    (hpre : ∀ inp work out, pre' inp work out → pre inp work out)
    (hpost : ∀ inp work out, post inp work out → post' inp work out)
    (htime : time ≤ time') (hinput : inputLength ≤ inputLength')
    (hspace : space ≤ space') :
    tm.HoareTimeSpace pre' post' time' inputLength' space' := by
  constructor
  · exact h.1.consequence hpre hpost htime
  · intro inp work out hpre' c' hreach
    exact (h.2 inp work out (hpre inp work out hpre') c' hreach).mono_internal
      hinput hspace

/-- Internal transducer closure under sequential composition. -/
theorem IsTransducer.seqTM_internal {tm₁ tm₂ : TM n}
    (h₁ : tm₁.IsTransducer) (h₂ : tm₂.IsTransducer) :
    (seqTM tm₁ tm₂).IsTransducer := by
  intro state iHead wHeads oHead
  cases state with
  | inl q =>
      simp only [seqTM]
      split
      · simp only [idleDir]
        split <;> decide
      · exact h₁ q iHead wHeads oHead
  | inr q =>
      simp only [seqTM]
      split
      · simp only [allIdle, idleDir]
        split <;> decide
      · exact h₂ q iHead wHeads oHead

/-- Internal sequential composition rule.  Both phases use one shared logical
input length and auxiliary-space budget; the phase boundary is covered by the
second contract at its reflexive initial configuration. The all-reachable
component specializes the generic tape-safety composition rule. -/
theorem seqTM_hoareTimeSpace_internal (tm₁ tm₂ : TM n)
    {pre mid mid' post : TapePred n} {b₁ b₂ inputLength space₁ space₂ : ℕ}
    (h₁ : tm₁.HoareTimeSpace pre mid b₁ inputLength space₁)
    (htrans : ∀ inp work out, mid inp work out →
      mid' (transitionInput inp) (fun i => transitionTape (work i))
        (transitionTape out))
    (h₂ : tm₂.HoareTimeSpace mid' post b₂ inputLength space₂) :
    (seqTM tm₁ tm₂).HoareTimeSpace pre post (b₁ + 1 + b₂)
      inputLength (max space₁ space₂) := by
  constructor
  · exact seqTM_hoareTime tm₁ tm₂ h₁.1 htrans h₂.1
  · change (seqTM tm₁ tm₂).HoareSafety pre
      (fun inp work _ => (∀ i, (work i).head ≤ max space₁ space₂) ∧
        inp.head ≤ inputLength + max space₁ space₂ + 1)
    exact seqTM_hoareSafety tm₁ tm₂ h₁.1 htrans h₂.1
      (h₁.2.mono_internal le_rfl (le_max_left _ _))
      (h₂.2.mono_internal le_rfl (le_max_right _ _))

/-- Internal bridge from fresh-start time-and-space contracts to function
computation in space. -/
theorem computesInSpace_of_hoareTimeSpace_internal
    {tm : TM n} {f : List Bool → List Bool} {T S : ℕ → ℕ}
    (htrans : tm.IsTransducer)
    (h : ∀ x, tm.HoareTimeSpace
      (fun inp work out =>
        inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun _ _ out => out.HasOutput (f x))
      (T x.length) x.length (S x.length)) :
    tm.ComputesInSpace f S := by
  refine ⟨htrans, ?_, ?_⟩
  · intro x c' hreach
    exact (h x).2 _ _ _ ⟨rfl, rfl, rfl⟩ c' hreach
  · intro x
    obtain ⟨c', t, _ht, hreach, hhalt, hout⟩ :=
      (h x).1 _ _ _ ⟨rfl, rfl, rfl⟩
    exact ⟨c', TM.reaches_of_reachesIn hreach, hhalt, hout⟩

end TM

end Complexity
