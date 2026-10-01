/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Witness.Verifier
public import Complexitylib.Classes.NP.Internal.VerifierBounds
public import Complexitylib.Classes.NP
public import Complexitylib.Classes.P.Defs

/-!
# Linear witnesses give NP membership

The generic finite-certificate compiler computes the `|x| + 1` bound, stores a
certificate on charged work tape, builds the paired virtual input, and runs the
verifier. Online-witness equivalence supplies an NTM with the compiler's explicit
resource bounds. This module does not import SAT or polynomial-padding machinery.
-/

public section

namespace Complexity

/-- **Guess and verify.** A language whose members are exactly the inputs
carrying a certificate of length at most `|x| + 1` that a polynomial-time
verifier accepts is in `NP`. -/
theorem mem_NP_of_linear_witness_internal {L L₀ : Language} (hL₀ : L₀ ∈ P)
    (hchar : ∀ x, x ∈ L ↔ ∃ y : List Bool, y.length ≤ x.length + 1 ∧ pair x y ∈ L₀) :
    L ∈ NP := by
  obtain ⟨c, k, M, T, hM, hT⟩ := Set.mem_iUnion.mp hL₀
  obtain ⟨d, hd⟩ := WitnessTM.Verifier.time_linear_bigO_of_bigO hT
  have hcompile' := WitnessTM.Verifier.compile_decidesInTimeSpace WitnessBoundSetup.linear M
    (TM.decidesInTimeSpace_of_decidesInTime hM)
  have hlang : L = WitnessTM.Verifier.language (fun n => n + 1) L₀ := by
    ext x
    exact hchar x
  rw [← hlang] at hcompile'
  have hNTM := ((WitnessTM.Verifier.compile WitnessBoundSetup.linear M).decidesInTimeSpace_iff
    L (WitnessTM.Verifier.time WitnessBoundSetup.linear T)
      (WitnessTM.Verifier.space WitnessBoundSetup.linear T)).mp hcompile'
  exact Set.mem_iUnion.mpr ⟨d, WitnessTM.Verifier.tapes 0 k,
    (WitnessTM.Verifier.compile WitnessBoundSetup.linear M).toNTM,
    WitnessTM.Verifier.time WitnessBoundSetup.linear T, hNTM.1, hd⟩

end Complexity
