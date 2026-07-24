/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonSlotQuery.Defs
import Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch.Defs

/-!
# Barrington slot-bit branch machine -- definitions

The stack-free slot cursor reduces one recursive address step to two raw
binary bits and one finite-control reflection flag. This module turns two
captured bit tapes into the corresponding four-way continuation branch.
-/

namespace Complexity

namespace BPCode

namespace Machine

/-- Select the continuation named by two raw slot bits and the pending
reflection flag. -/
def barringtonSlotContinuation {n : ℕ} (reversed low high : Bool)
    (onLeft onRight onInverseLeft onInverseRight : TM n) : TM n :=
  if high != reversed then
    if low != reversed then onInverseRight else onInverseLeft
  else if low != reversed then onRight else onLeft

/-- Branch to the selected Barrington child using two canonical one-bit work
tapes. The high bit is read first, then the low bit; both dispatch steps
preserve every tape. -/
def barringtonSlotBranchTM {n : ℕ} (lowIdx highIdx : Fin n)
    (reversed : Bool)
    (onLeft onRight onInverseLeft onInverseRight : TM n) : TM n :=
  TM.branchWorkSymbolTM highIdx Γ.one
    (TM.branchWorkSymbolTM lowIdx Γ.one
      (barringtonSlotContinuation reversed true true
        onLeft onRight onInverseLeft onInverseRight)
      (barringtonSlotContinuation reversed false true
        onLeft onRight onInverseLeft onInverseRight))
    (TM.branchWorkSymbolTM lowIdx Γ.one
      (barringtonSlotContinuation reversed true false
        onLeft onRight onInverseLeft onInverseRight)
      (barringtonSlotContinuation reversed false false
        onLeft onRight onInverseLeft onInverseRight))

end Machine

end BPCode

end Complexity
