/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.NatCode.Defs

/-!
# Machine emission of raw circuit gates — definitions

A serialized raw gate consists of a fixed three-bit header followed by two
terminated-unary wire references.  The header is baked into finite control;
the references are read from preserved canonical binary work tapes.  One
reusable zero scratch tape drives both natural-code emitters.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

/-- The fixed operation-and-negation prefix of a serialized raw gate. -/
def rawGateHeader (op : AndOrOp) (negated₀ negated₁ : Bool) : List Bool :=
  [match op with | .and => true | .or => false, negated₀, negated₁]

/-- Emit one raw gate from two canonical binary wire-reference tapes.

The scratch tape is restored to zero by each `emitNatCodeTM` call, so it can
be reused for the second reference and by the surrounding stream generator. -/
def emitRawGateTM {n : ℕ} (op : AndOrOp) (negated₀ negated₁ : Bool)
    (counterIdx input₀Idx input₁Idx : Fin n) : TM n :=
  TM.seqTM (TM.emitBitsTM (rawGateHeader op negated₀ negated₁))
    (TM.seqTM (emitNatCodeTM counterIdx input₀Idx)
      (emitNatCodeTM counterIdx input₁Idx))

/-- Concrete time bound for one serialized raw gate. -/
def emitRawGateTime (input₀ input₁ : ℕ) : ℕ :=
  emitNatCodeTime input₀ + emitNatCodeTime input₁ + 5

/-- All-prefix auxiliary-space bound for one serialized raw gate. -/
def emitRawGateSpace (initialSpace input₀ input₁ : ℕ) : ℕ :=
  initialSpace + 2 * max input₀.size input₁.size + 5

end Machine

end CircuitCode

end Complexity
