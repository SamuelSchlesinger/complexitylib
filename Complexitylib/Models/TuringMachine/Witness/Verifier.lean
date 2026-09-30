/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Witness.Verifier.Defs
import Complexitylib.Models.TuringMachine.Witness.Verifier.Internal

/-!
# Finite verification with explicit time and space

A concrete bound-setup machine and an ordinary paired-input verifier compile
to a witness machine that stores its certificate on charged work tape. Both
resource bounds include initialization and the paired virtual input. Reusing
that certificate is permitted because its stored copy is ordinary workspace.

`Verifier.compile_decidesInTimeSpace` is uniform over arbitrary realized bound
functions; finite maxima avoid monotonicity assumptions on the verifier's
resource bounds. Exact online-witness equivalence then gives the corresponding
NTM with the same compiler bounds. Polynomial witness theorems are downstream.
-/

public section

namespace Complexity

/-- A deterministic time bound also bounds every charged decision-space prefix. -/
theorem TM.decidesInTimeSpace_of_decidesInTime {M : TM k}
    {L : Language} {T : ℕ → ℕ} (hM : M.DecidesInTime L T) :
    M.DecidesInTimeSpace L T T :=
  TM.decidesInTimeSpace_of_decidesInTime_internal hM

namespace WitnessTM.Verifier

/-- An ordinary finite verifier and realized bound yield a concrete stored-
certificate witness machine, with explicit independent resource bounds. -/
theorem compile_decidesInTimeSpace (setup : WitnessBoundSetup r bound) (M : TM k)
    {L : Language} {T S : ℕ → ℕ} (hM : M.DecidesInTimeSpace L T S) :
    (compile setup M).DecidesInTimeSpace (language bound L)
      (time setup T) (space setup S) :=
  compile_decidesInTimeSpace_internal setup M hM

/-- The finite verifier compiler also applies when only time is being tracked. -/
theorem compile_decidesInTime (setup : WitnessBoundSetup r bound) (M : TM k)
    {L : Language} {T : ℕ → ℕ} (hM : M.DecidesInTime L T) :
    (compile setup M).DecidesInTime (language bound L) (time setup T) :=
  (compile_decidesInTimeSpace setup M (TM.decidesInTimeSpace_of_decidesInTime hM)).1

end WitnessTM.Verifier
end Complexity
