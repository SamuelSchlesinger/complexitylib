/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.L.PolynomialTime.Internal

/-!
# Log-space transducers run in polynomial time

The finite reduced-configuration theorem for one-way-output deterministic
transducers makes a logarithmic auxiliary-space bound into a polynomial time
bound. Consequently `L ⊆ P` and `FL ⊆ FP`.

## Main results

- `TM.transducerConfigBound_bigO_polynomial` — logarithmic space gives a
  polynomial reduced-configuration bound
- `L_subset_P` — deterministic log-space languages are polynomial-time
- `FL_subset_FP` — deterministic log-space functions are polynomial-time
- `mem_FL_polynomial_output_length` — their output length is polynomially
  bounded
- `mem_FL_output_bound_log_width` — an index into that bound fits in
  logarithmic space
-/

namespace Complexity

namespace TM

variable {k : ℕ}

/-- The reduced-configuration count of a deterministic transducer using
`O(log n)` auxiliary space is polynomial in the input length. -/
theorem transducerConfigBound_bigO_polynomial
    (tm : TM k) {S : ℕ → ℕ}
    (hS : S =O (fun n => Nat.log 2 n)) :
    ∃ c : ℕ,
      (fun n => tm.transducerConfigBound n (S n)) =O
        ((· ^ (1 + (2 * c + 1) * k)) : ℕ → ℕ) :=
  tm.transducerConfigBound_bigO_polynomial_internal hS

end TM

/-- **`L ⊆ P`: every language decided by a deterministic log-space
transducer is decidable in polynomial time.** -/
theorem L_subset_P : L ⊆ P :=
  L_subset_P_internal

/-- **`FL ⊆ FP`: every deterministic log-space transducer function is
computable in polynomial time.** -/
theorem FL_subset_FP : FL ⊆ FP :=
  FL_subset_FP_internal

/-- Every deterministic log-space transducer function has output length
bounded pointwise by a polynomial in its input length. This is the key size
fact used by recomputation-based log-space composition: an output position
needs only logarithmically many bits. -/
theorem mem_FL_polynomial_output_length
    {f : List Bool → List Bool} (hf : f ∈ FL) :
    ∃ p : Polynomial ℕ, ∀ input,
      (f input).length ≤ p.eval input.length :=
  mem_FL_polynomial_output_length_internal hf

/-- Every `FL` function admits a polynomial output bound whose binary width is
logarithmic. Thus a recomputation-based consumer can keep an output position
in `O(log n)` auxiliary space even though the output itself may be
polynomially long. -/
theorem mem_FL_output_bound_log_width
    {f : List Bool → List Bool} (hf : f ∈ FL) :
    ∃ p : Polynomial ℕ,
      (∀ input, (f input).length ≤ p.eval input.length) ∧
      (fun n => (p.eval n).size) =O (fun n => Nat.log 2 n) :=
  mem_FL_output_bound_log_width_internal hf

end Complexity
