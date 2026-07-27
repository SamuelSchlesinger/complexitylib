/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Offset.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Polynomial.Defs

/-!
# Polynomial recent-wire offsets -- definitions

Nested transition wrappers refer to child outputs whose distance from the
current frontier is a fixed polynomial in the tableau horizon. These helpers
evaluate that polynomial into one scratch value, use the dynamic-offset gate
emitter, and restore every owned register.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Evaluate `polynomial(T) + extra` into the dynamic-offset register. -/
noncomputable def preparePolynomialOffset (polynomial : Polynomial ℕ)
    (extra : ℕ := 0) : BinaryRoutine WorkCount :=
  BinaryRoutine.seq
    (BinaryRoutine.evalPolynomial Work.horizon Work.temporary₃
      Work.polynomialScratch Work.multiplyCounter Work.addCounter polynomial)
    (BinaryRoutine.addConst Work.temporary₃ extra)

/-- Emit one raw gate from a polynomial recent offset and a fixed recent
offset, then clear the evaluated polynomial value. -/
noncomputable def emitPolynomialRecentGate (polynomial : Polynomial ℕ)
    (extra : ℕ) (op : AndOrOp) (negated₀ negated₁ : Bool)
    (fixedOffset₁ : ℕ) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [preparePolynomialOffset polynomial extra,
      emitDynamicRecentGate op negated₀ negated₁ Work.temporary₃
        Work.loop₃ fixedOffset₁,
      BinaryRoutine.clear Work.temporary₃]

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
