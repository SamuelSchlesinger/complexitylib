/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Samuel’s dot
-/

module
public import Complexitylib.SAT.VerifierTM
public import Complexitylib.Classes.NP.Verifier.Linear

/-!
# SAT ∈ NP — the headline theorem

This file ties together the two halves of the `SAT ∈ NP` proof:

* `SAT.VerifierTM.verifyPairTM_decidesInTime` (in `VerifierTM`) — the deterministic
  three-tape verifier decides `pairLang Witness` within the quadratic budget
  `verifyPairTMTime`, so `pairLang Witness ∈ P`.
* `NP.mem_NP_of_linear_witness` (in `Classes.NP.Verifier.Linear`) — the generic
  verifier route turns `pairLang Witness ∈ P` and the linear witness bound
  into `language ∈ NP`.

Combining them yields the unconditional theorem `SAT.language_mem_NP : language ∈ NP`.
-/


public section

namespace Complexity

namespace SAT

/-- The paired SAT verifier language is decided in polynomial (in fact
quadratic) time by `verifyPairTM`, hence `pairLang Witness ∈ P`. -/
theorem pairLang_witness_mem_P : pairLang Witness ∈ P :=
  Set.mem_iUnion.mpr
    ⟨2, 3, VerifierTM.verifyPairTM, VerifierTM.verifyPairTMTime,
      VerifierTM.verifyPairTM_decidesInTime, VerifierTM.verifyPairTMTime_bigO_quadratic⟩

/-- **SAT ∈ NP.** The Boolean satisfiability language is in `NP`, witnessed by
the generic finite-certificate compiler running over the polynomial-time
deterministic pair verifier. -/
theorem language_mem_NP : language ∈ NP :=
  NP.mem_NP_of_linear_witness
    (fun _ _ ⟨_, _, hlength, _⟩ => hlength)
    mem_language_iff_witness pairLang_witness_mem_P

end SAT

end Complexity
