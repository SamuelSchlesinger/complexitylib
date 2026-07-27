/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Bounds.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Bounds.Internal

/-!
# Polynomial counters for direct tableau serialization

This module exposes the normalized horizon and closed polynomial counters used
by the log-space tableau serializer. Their evaluations are literal equalities
to the padded family's bounds, so the generator can compute its header and
padding frontier without first counting the emitted raw gates.

## Main results

- `directSerializerHorizonPolynomial_input_le` supplies `n + 1 ≤ T(n)`.
- `directSerializerGateBoundPolynomial_eval` identifies the padding target.
- `directSerializerFrontierPolynomial_eval` identifies the post-padding wire.
- `directSerializerGateCountPolynomial_eval` identifies the code header.
- `DecidesInTime.directSerializerHorizon` safely enlarges a time witness.
-/

@[expose] public section

namespace Complexity

namespace TM

@[simp] theorem directSerializerHorizonPolynomial_eval
    (q : Polynomial ℕ) (n : ℕ) :
    (directSerializerHorizonPolynomial q).eval n = q.eval n + n + 1 :=
  directSerializerHorizonPolynomial_eval_internal q n

theorem directSerializerHorizonPolynomial_input_le
    (q : Polynomial ℕ) (n : ℕ) :
    n + 1 ≤ (directSerializerHorizonPolynomial q).eval n :=
  directSerializerHorizonPolynomial_input_le_internal q n

@[simp] theorem directSerializerGateBoundPolynomial_eval
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) :
    (directSerializerGateBoundPolynomial tm q).eval n =
      tm.directUnrollingGateBound
        (directSerializerHorizonPolynomial q).eval n :=
  directSerializerGateBoundPolynomial_eval_internal tm q n

@[simp] theorem directSerializerFrontierPolynomial_eval
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) :
    (directSerializerFrontierPolynomial tm q).eval n =
      n + tm.directUnrollingGateBound
        (directSerializerHorizonPolynomial q).eval n :=
  directSerializerFrontierPolynomial_eval_internal tm q n

@[simp] theorem directSerializerGateCountPolynomial_eval
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) :
    (directSerializerGateCountPolynomial tm q).eval n =
      tm.directUnrollingGateBound
        (directSerializerHorizonPolynomial q).eval n + 1 :=
  directSerializerGateCountPolynomial_eval_internal tm q n

/-- Enlarging a polynomial time bound to the serializer's normalized horizon
preserves language decision correctness. -/
theorem DecidesInTime.directSerializerHorizon
    {tm : TM k} {L : Language} (q : Polynomial ℕ)
    (hdec : tm.DecidesInTime L q.eval) :
    tm.DecidesInTime L (directSerializerHorizonPolynomial q).eval :=
  hdec.directSerializerHorizon_internal q

end TM

end Complexity
