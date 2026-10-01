/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel’s dot
-/

module
public import Complexitylib.Classes.NP.Verifier
public import Complexitylib.Classes.NP.Internal.Verifier
public import Complexitylib.Classes.NP.Internal.Verifier.Linear
public import Complexitylib.SAT.Internal.LinearGuessVerify

/-!
# Compatibility for the former internal verifier entry point

This legacy import preserves the original verifier-membership names and the
exact `guessVerify_decidesInTime` theorem about `SAT.satGuessVerifyNTM`.
New membership clients should import `Complexitylib.Classes.NP.Verifier`, whose
implementation does not depend on SAT. Clients needing the old concrete machine
should import the public `Complexitylib.SAT.GuessVerify` compatibility surface.
-/

public section

namespace Complexity

variable {k : ℕ}

/-- The guess-and-verify machine decides any language whose members are exactly
the inputs with a short certificate accepted by `M`. -/
theorem guessVerify_decidesInTime (M : TM k) {L L₀ : Language} {f : ℕ → ℕ}
    (hM : M.DecidesInTime L₀ f)
    (hchar : ∀ x, x ∈ L ↔ ∃ y : List Bool, y.length ≤ x.length + 1 ∧ pair x y ∈ L₀) :
    (SAT.satGuessVerifyNTM M).DecidesInTime L (SAT.satGuessVerifyTime f) := by
  refine ⟨SAT.satGuessVerify_allPathsHaltIn_of_decidesInTime M hM, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨y, hlen, hmem⟩ := (hchar x).1 hx
    exact SAT.satGuessVerify_acceptsInTime_of_witness_bound_of_decidesInTime M hM x y
      hlen hmem
  · intro hacc
    by_contra hx
    obtain ⟨choices, hhalt, hout⟩ := hacc
    obtain ⟨y, hy, htrace⟩ :=
      SAT.satGuessVerify_trace_decides_for_some_setup_witness_of_decidesInTime M hM x choices
    have hnot : pair x y ∉ L₀ := fun hmem => hx ((hchar x).2 ⟨y, hy, hmem⟩)
    have hzero : ((SAT.satGuessVerifyNTM M).trace (SAT.satGuessVerifyTime f x.length) choices
        ((SAT.satGuessVerifyNTM M).initCfg x)).output.cells 1 = Γ.zero :=
      htrace.2.2 hnot
    rw [hzero] at hout
    exact (by decide : Γ.zero ≠ Γ.one) hout

end Complexity
