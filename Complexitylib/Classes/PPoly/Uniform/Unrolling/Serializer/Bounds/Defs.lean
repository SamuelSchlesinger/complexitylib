/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Padded.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Polynomial counters for direct tableau serialization -- definitions

The streaming generator normalizes an arbitrary polynomial time bound so its
horizon contains the complete input. It also evaluates three fixed natural
polynomials: the padded gate bound, the wire frontier after that padding, and
the positive member's gate-count header. Keeping these values as polynomials
lets the binary polynomial subroutine compute them in logarithmic workspace.
-/

@[expose] public section

namespace Complexity

namespace TM

/-- Normalize a polynomial horizon so `n + 1` represented tape cells always
fit inside the bounded tableau. -/
noncomputable def directSerializerHorizonPolynomial
    (q : Polynomial ℕ) : Polynomial ℕ :=
  q + Polynomial.X + Polynomial.C 1

/-- Closed padded gate bound for the normalized horizon. -/
noncomputable def directSerializerGateBoundPolynomial
    (tm : TM k) (q : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (CircuitUnrolling.acceptanceSizeCoeff tm.toNTM) *
    (directSerializerHorizonPolynomial q + Polynomial.C 2) ^ 3

/-- First unused wire after the padded gates, before the final output copy. -/
noncomputable def directSerializerFrontierPolynomial
    (tm : TM k) (q : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.X + directSerializerGateBoundPolynomial tm q

/-- Number encoded in the positive tagged circuit header, including the
terminal output-copy gate. -/
noncomputable def directSerializerGateCountPolynomial
    (tm : TM k) (q : Polynomial ℕ) : Polynomial ℕ :=
  directSerializerGateBoundPolynomial tm q + Polynomial.C 1

end TM

end Complexity
