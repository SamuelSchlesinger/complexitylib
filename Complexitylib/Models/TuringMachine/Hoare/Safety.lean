/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Hoare.Safety.Defs
public import Complexitylib.Models.TuringMachine.Hoare
import Complexitylib.Models.TuringMachine.Hoare.Safety.Internal

/-!
# Compositional tape safety

Use the existing `TM.HoareTime` for endpoints and time. This module adds only
state-independent safety and its sequential-composition rule, so resource
predicates may include output and exclude an external witness stream.
-/

public section

namespace Complexity
namespace TM

/-- Strengthen the entry condition and weaken the safety conclusion. -/
theorem HoareSafety.consequence {M : TM n} {pre pre' safe safe' : TapePred n}
    (h : M.HoareSafety pre safe)
    (hpre : ∀ inp work out, pre' inp work out → pre inp work out)
    (hsafe : ∀ inp work out, safe inp work out → safe' inp work out) :
    M.HoareSafety pre' safe' :=
  fun inp work out hp c hc => hsafe _ _ _ (h inp work out (hpre _ _ _ hp) c hc)

/-- A terminating sequential pipeline preserves a common safety predicate.
The handoff is covered by the second phase's reflexive safety obligation. -/
theorem seqTM_hoareSafety (tm₁ tm₂ : TM n)
    {pre mid mid' post safe : TapePred n} {b₁ b₂ : ℕ}
    (h₁ : tm₁.HoareTime pre mid b₁)
    (htrans : ∀ inp work out, mid inp work out →
      mid' (transitionInput inp) (fun i => transitionTape (work i))
        (transitionTape out))
    (h₂ : tm₂.HoareTime mid' post b₂)
    (hs₁ : tm₁.HoareSafety pre safe) (hs₂ : tm₂.HoareSafety mid' safe) :
    (seqTM tm₁ tm₂).HoareSafety pre safe :=
  seqTM_hoareSafety_internal tm₁ tm₂ h₁ htrans h₂ hs₁ hs₂

end TM
end Complexity
