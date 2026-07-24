/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScanToken.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Defs

/-!
# Bounded forward postfix scan loop -- definitions

This layer gives the decoded one-token scanner its own bounded count-up loop.
The loop counter and preserved token limit are structurally separate from the
sixteen roles used by token decoding and the semantic forward-scan state. In
particular, the loop counter never aliases the semantic token count that the
body already increments once per token.
-/

namespace Complexity

namespace BPCode

namespace Machine

/-- Eighteen distinct controller roles for a bounded decoded-token scan.

The first sixteen roles are inherited by `ForwardScanTokenLayout`; roles
sixteen and seventeen are the private loop counter and preserved token limit.
-/
structure ForwardScanLoopLayout (controllerTapes : ℕ) where
  /-- Injective assignment of all token-scan and loop-control roles. -/
  roles : Fin 18 ↪ Fin controllerTapes

/-- Restrict a bounded-loop layout to the complete decoded-token scanner. -/
def ForwardScanLoopLayout.tokenLayout
    (layout : ForwardScanLoopLayout controllerTapes) :
    ForwardScanTokenLayout controllerTapes where
  roles :=
    { toFun := fun i => layout.roles ⟨i.val, by omega⟩
      inj' := by
        intro i j hij
        have hroles := congrArg Fin.val (layout.roles.injective hij)
        exact Fin.ext (by simpa using hroles) }

/-- Logical controller role of the bounded loop counter. -/
def ForwardScanLoopLayout.counterRole
    (layout : ForwardScanLoopLayout controllerTapes) : Fin controllerTapes :=
  layout.roles 16

/-- Logical controller role of the preserved token limit. -/
def ForwardScanLoopLayout.limitRole
    (layout : ForwardScanLoopLayout controllerTapes) : Fin controllerTapes :=
  layout.roles 17

/-- Physical work-tape index of the bounded loop counter. -/
def ForwardScanLoopLayout.counterIdx (n : ℕ)
    (layout : ForwardScanLoopLayout controllerTapes) :
    Fin (0 + TM.outputProbeControllerTapes n + controllerTapes) :=
  TM.outputProbeIndexedControllerIdx n layout.counterRole

/-- Physical work-tape index of the preserved token limit. -/
def ForwardScanLoopLayout.limitIdx (n : ℕ)
    (layout : ForwardScanLoopLayout controllerTapes) :
    Fin (0 + TM.outputProbeControllerTapes n + controllerTapes) :=
  TM.outputProbeIndexedControllerIdx n layout.limitRole

/-- Scan exactly the number of tokens named by the preserved binary limit.

Each iteration decodes and applies one complete token before the generic loop
driver increments its private counter.
-/
def forwardScanTokenLoopTM (tm : TM n) (controllerTapes : ℕ)
    (layout : ForwardScanLoopLayout controllerTapes) :
    TM (0 + TM.outputProbeControllerTapes n + controllerTapes) :=
  TM.binaryForTM
    (forwardScanDecodedTokenTM tm controllerTapes layout.tokenLayout)
    (layout.counterIdx n) (layout.limitIdx n)

end Machine

end BPCode

end Complexity
