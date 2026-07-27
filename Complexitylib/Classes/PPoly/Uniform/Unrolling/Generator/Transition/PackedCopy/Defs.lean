/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.PolynomialOffset.Defs

/-!
# Delayed packed-formula copies -- definitions

The direct step generator emits every successor formula before its packed
output block. `gateCount` is a rolling cursor through those formula blocks.
This primitive advances that cursor by a fixed polynomial in the tableau
horizon and copies the final wire of the newly traversed block.

The explicit domain requires the formula-size polynomial to be positive.
That deliberately rules out empty formula blocks independently of the old
cursor value.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Advance the rolling formula cursor by `sizePolynomial(horizon)` and emit
a copy of the newly traversed formula block's output wire. -/
noncomputable def emitPackedFormulaCopy (sizePolynomial : Polynomial ℕ) :
    BinaryRoutine WorkCount :=
  let routine := BinaryRoutine.seqList
      [preparePolynomialOffset sizePolynomial,
        BinaryRoutine.add Work.temporary₃ Work.gateCount Work.addCounter,
        BinaryRoutine.binaryCopy Work.gateCount Work.reference₀
          Work.copyCounter,
        BinaryRoutine.binaryPred Work.reference₀,
        BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
          Work.available Work.reference₀ Work.reference₀,
        BinaryRoutine.clear Work.reference₀,
        BinaryRoutine.clear Work.temporary₃]
  { routine with
    requires := fun values =>
      values Work.temporary₃ = 0 ∧
        values Work.polynomialScratch = 0 ∧
        values Work.multiplyCounter = 0 ∧
        values Work.addCounter = 0 ∧
        values Work.copyCounter = 0 ∧
        values Work.emitCounter = 0 ∧
        0 < sizePolynomial.eval (values Work.horizon) }

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
