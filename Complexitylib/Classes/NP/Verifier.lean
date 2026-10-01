/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Samuel’s dot
-/

module
public import Complexitylib.Classes.NP.Verifier.Linear
import Complexitylib.Classes.NP.Internal.Verifier

/-!
# Polynomial-time verifiers give NP membership

This is the language-independent entry point for linear and polynomially bounded
witnesses. Linear witnesses use the proved finite-certificate compiler; arbitrary
polynomial bounds reduce to the linear case by polynomial-time padding. Neither
route imports a SAT-specific machine.

Clients needing only linear witnesses can import
`Complexitylib.Classes.NP.Verifier.Linear` to avoid the padding infrastructure.
Exact theorems about the older concrete machine remain available separately in
`Complexitylib.SAT.GuessVerify`.
-/

public section

namespace Complexity

/-- **Guess and verify with polynomial witnesses.** A polynomial-time verifier
whose accepted certificates have polynomially bounded length places its
existential language in `NP`. -/
theorem mem_NP_of_poly_witness {L L₀ : Language} (p : Polynomial ℕ) (hL₀ : L₀ ∈ P)
    (hbal : ∀ x y : List Bool, pair x y ∈ L₀ → y.length ≤ p.eval x.length)
    (hchar : ∀ x, x ∈ L ↔ ∃ y : List Bool, pair x y ∈ L₀) :
    L ∈ NP :=
  mem_NP_of_poly_witness_internal p hL₀ hbal hchar

end Complexity
