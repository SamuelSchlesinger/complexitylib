/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Subroutines.PairBuild

/-!
# Compatibility import for the generic pair builder

The implementation now belongs to the machine-model subroutine layer. Import
`Complexitylib.Models.TuringMachine.Subroutines.PairBuild` in new code; all
`Complexity.TM` names, exact machines, and bounds are unchanged.

This legacy path remains for downstream imports and the old SAT-specific
`GuessVerify` route. Remove it only in an announced breaking release after
those clients have migrated; it must never own a second implementation.
-/
