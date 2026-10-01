/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Samuel’s dot
-/

module
public import Complexitylib.Classes.Pairing
public import Complexitylib.Classes.NP
public import Complexitylib.Classes.P.Defs
import Complexitylib.Classes.NP.Internal.Verifier.Linear

/-!
# Linearly bounded polynomial-time verifiers give NP membership

This language-independent entry point uses the proved finite-certificate compiler
`WitnessTM.Verifier.compile`. It imports neither SAT nor the polynomial-padding
machinery. `mem_NP_of_linear_witness` retains its established name and statement;
`NP.mem_NP_of_linear_witness` adapts it to a relation with a verifier in `P`.

For arbitrary polynomial witness bounds, import `Complexitylib.Classes.NP.Verifier`.
Exact theorems about the older `SAT.satGuessVerifyNTM` remain available separately
from `Complexitylib.SAT.GuessVerify`; the two machines are not identified.
-/

public section

namespace Complexity

/-- **Guess and verify.** A language characterized by certificates of length at
most `|x| + 1` accepted by a polynomial-time verifier is in `NP`. -/
theorem mem_NP_of_linear_witness {L L₀ : Language} (hL₀ : L₀ ∈ P)
    (hchar : ∀ x, x ∈ L ↔ ∃ y : List Bool, y.length ≤ x.length + 1 ∧ pair x y ∈ L₀) :
    L ∈ NP :=
  mem_NP_of_linear_witness_internal hL₀ hchar

/-- A linearly bounded witness relation with a polynomial-time paired verifier
places the language it characterizes in `NP`. -/
theorem NP.mem_NP_of_linear_witness
    {R : List Bool → List Bool → Prop} {L : Language}
    (hbound : ∀ x y, R x y → y.length ≤ x.length + 1)
    (hchar : ∀ x, x ∈ L ↔ ∃ y, R x y)
    (hverify : pairLang R ∈ P) : L ∈ NP := by
  apply Complexity.mem_NP_of_linear_witness hverify
  intro x
  rw [hchar x]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, hbound x y hy, (mem_pairLang_pair R x y).2 hy⟩
  · rintro ⟨y, _, hy⟩
    exact ⟨y, (mem_pairLang_pair R x y).1 hy⟩

end Complexity
