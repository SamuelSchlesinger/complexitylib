/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.VerifierTM
public import Complexitylib.SAT.Internal.GuessVerify

/-!
# SAT ∈ NP — the headline theorem

This file ties together the two halves of the `SAT ∈ NP` proof:

* `SAT.VerifierTM.verifyPairTM_decidesInTime` (in `VerifierTM`) — the deterministic
  three-tape verifier decides `pairLang Witness` within the quadratic budget
  `verifyPairTMTime`, so `pairLang Witness ∈ P`.
* `SAT.language_mem_NP_of_verifierP_direct` (in `GuessVerify`) — the SAT-specialized
  guess-and-verify NTM turns `pairLang Witness ∈ P` into `language ∈ NP`.

Combining them yields the unconditional theorem `SAT.language_mem_NP : language ∈ NP`.
-/

@[expose] public section

namespace Complexity

namespace SAT

/-- The paired SAT verifier language is decided in polynomial (in fact
quadratic) time by `verifyPairTM`, hence `pairLang Witness ∈ P`. -/
theorem pairLang_witness_mem_P : pairLang Witness ∈ P :=
  Set.mem_iUnion.mpr
    ⟨2, 3, VerifierTM.verifyPairTM, VerifierTM.verifyPairTMTime,
      VerifierTM.verifyPairTM_decidesInTime, VerifierTM.verifyPairTMTime_bigO_quadratic⟩

/-- **SAT ∈ NP.** The Boolean satisfiability language is in `NP`, witnessed by
the SAT-specialized guess-and-verify NTM running over the polynomial-time
deterministic pair verifier. -/
theorem language_mem_NP : language ∈ NP :=
  language_mem_NP_of_verifierP_direct pairLang_witness_mem_P

end SAT

end Complexity
