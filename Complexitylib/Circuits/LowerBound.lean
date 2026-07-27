/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Internal.LowerBound

/-! # Gate Elimination Lower Bound

For every circuit, the number of essential input variables is at most its total
fan-in. For a bounded fan-in `k` AND/OR basis (`Basis.boundedAndOr k`), this is
at most `k` times circuit size.

The key insight: if no gate directly reads a primary input wire, then that
input cannot influence the circuit's output. By contrapositive, every
essential variable must be "covered" by at least one gate. Since each gate
reads at most `k` inputs, the circuit needs at least `⌈n'/k⌉` gates.

## Definitions (from `Complexitylib.Circuits.EssentialInput`)

* `IsEssentialInput f i` — function `f` depends on input variable `i`
  (flipping bit `i` can change some output)
* `essentialInputs f` — the `Finset` of all essential input variables

## Main results

The generic theorem is `Circuit.card_essentialInputs_le_totalFanIn`; its
bounded-fan-in corollary is `Circuit.card_essentialInputs_le_mul_size`:

    theorem Circuit.card_essentialInputs_le_mul_size {k : Nat}
        (c : Circuit (Basis.boundedAndOr k) N M G)
        (f : BitString N → BitString M)
        (hf : c.eval = f) :
        (essentialInputs f).card ≤ k * c.size

And its corollary for functions that depend on all inputs:

    theorem Circuit.le_mul_size_of_forall_isEssentialInput {k : Nat}
        (c : Circuit (Basis.boundedAndOr k) N M G)
        (f : BitString N → BitString M)
        (hf : c.eval = f)
        (hall : ∀ i : Fin N, IsEssentialInput f i) :
        N ≤ k * c.size
-/

@[expose] public section

namespace Complexity

namespace Circuit

variable {N M G : Nat} [NeZero N] [NeZero M]

/-- Over any basis, the number of essential variables of a computed function
is at most the circuit's total number of gate-input occurrences. -/
theorem card_essentialInputs_le_totalFanIn {B : Basis}
    (c : Circuit B N M G)
    (f : BitString N → BitString M)
    (hf : c.eval = f) :
    (essentialInputs f).card ≤ c.totalFanIn :=
  card_essentialInputs_le_totalFanIn_internal c f hf

/-- If a function depends on every input, every circuit computing it has total
fan-in at least `N`. -/
theorem le_totalFanIn_of_forall_isEssentialInput {B : Basis}
    (c : Circuit B N M G)
    (f : BitString N → BitString M)
    (hf : c.eval = f)
    (hall : ∀ i : Fin N, IsEssentialInput f i) :
    N ≤ c.totalFanIn :=
  le_totalFanIn_of_forall_isEssentialInput_internal c f hf hall

/-- For bounded fan-in `k`, the number of essential variables of a computed
function is at most `k` times the circuit's total gate count. -/
theorem card_essentialInputs_le_mul_size {k : Nat}
    (c : Circuit (Basis.boundedAndOr k) N M G)
    (f : BitString N → BitString M)
    (hf : c.eval = f) :
    (essentialInputs f).card ≤ k * c.size :=
  card_essentialInputs_le_mul_size_internal c f hf

/-- If a function computed by a bounded fan-in `k` circuit depends on every
input, then `N ≤ k * c.size`. -/
theorem le_mul_size_of_forall_isEssentialInput {k : Nat}
    (c : Circuit (Basis.boundedAndOr k) N M G)
    (f : BitString N → BitString M)
    (hf : c.eval = f)
    (hall : ∀ i : Fin N, IsEssentialInput f i) :
    N ≤ k * c.size :=
  le_mul_size_of_forall_isEssentialInput_internal c f hf hall

end Circuit

end Complexity
