/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Bounds.Defs

/-!
# Polynomial counters for direct tableau serialization -- proof internals
-/

@[expose] public section

namespace Complexity

namespace TM

theorem directSerializerHorizonPolynomial_eval_internal
    (q : Polynomial ℕ) (n : ℕ) :
    (directSerializerHorizonPolynomial q).eval n = q.eval n + n + 1 := by
  simp [directSerializerHorizonPolynomial, Polynomial.eval_add]

theorem directSerializerHorizonPolynomial_input_le_internal
    (q : Polynomial ℕ) (n : ℕ) :
    n + 1 ≤ (directSerializerHorizonPolynomial q).eval n := by
  rw [directSerializerHorizonPolynomial_eval_internal]
  omega

theorem directSerializerGateBoundPolynomial_eval_internal
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) :
    (directSerializerGateBoundPolynomial tm q).eval n =
      tm.directUnrollingGateBound
        (directSerializerHorizonPolynomial q).eval n := by
  simp [directSerializerGateBoundPolynomial, directUnrollingGateBound,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow]

theorem directSerializerFrontierPolynomial_eval_internal
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) :
    (directSerializerFrontierPolynomial tm q).eval n =
      n + tm.directUnrollingGateBound
        (directSerializerHorizonPolynomial q).eval n := by
  simp [directSerializerFrontierPolynomial, Polynomial.eval_add,
    directSerializerGateBoundPolynomial_eval_internal]

theorem directSerializerGateCountPolynomial_eval_internal
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) :
    (directSerializerGateCountPolynomial tm q).eval n =
      tm.directUnrollingGateBound
        (directSerializerHorizonPolynomial q).eval n + 1 := by
  simp [directSerializerGateCountPolynomial, Polynomial.eval_add,
    directSerializerGateBoundPolynomial_eval_internal]

theorem DecidesInTime.directSerializerHorizon_internal
    {tm : TM k} {L : Language} (q : Polynomial ℕ)
    (hdec : tm.DecidesInTime L q.eval) :
    tm.DecidesInTime L (directSerializerHorizonPolynomial q).eval := by
  exact hdec.mono fun n => by
    rw [directSerializerHorizonPolynomial_eval_internal]
    omega

end TM

end Complexity
