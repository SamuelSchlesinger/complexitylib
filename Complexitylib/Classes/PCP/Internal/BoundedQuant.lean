/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.BitwiseFP
public import Complexitylib.Classes.Containments
public import Complexitylib.Classes.P.BoundedQuant

/-!
# Checking polynomially many conditions, in `P`

An algorithm that has to verify a condition at every one of polynomially many
places is a loop, and a loop of polynomial length is still polynomial time. This
module states that as closure of `P` under quantification over an index bounded
by a polynomial-time unary length function.

The loop itself is `FPPred.forall_lt` of `Complexitylib.Classes.P.BoundedQuant`,
which counts the indices at which the condition holds. What this module adds is
the passage from a language in `P` to its one-bit verdict,
`exists_decisionFn_of_mem_P`, which runs a decider inside Cobham's algebra and so
sits downstream of the simulation.

## Main results

- `Complexity.forall_unary_mem_P` — a bounded conjunction of `P` conditions
- `Complexity.exists_unary_mem_P` — a bounded disjunction of `P` conditions
-/

@[expose] public section

namespace Complexity

/-- **A bounded conjunction of polynomial-time conditions is polynomial time.**
The index runs over `0, …, len x - 1` and is passed to the condition in unary. -/
theorem forall_unary_mem_P {L : Language} (hL : L ∈ P) {len : List Bool → ℕ}
    (hlen : (fun x => List.replicate (len x) true) ∈ FP) :
    {x : List Bool | ∀ i < len x, pair x (List.replicate i true) ∈ L} ∈ P :=
  FPPred.mem_P (FPPred.forall_lt (n := len) (p := (· ∈ L)) hlen
    (exists_decisionFn_of_mem_P hL))

/-- **A bounded disjunction of polynomial-time conditions is polynomial time.** -/
theorem exists_unary_mem_P {L : Language} (hL : L ∈ P) {len : List Bool → ℕ}
    (hlen : (fun x => List.replicate (len x) true) ∈ FP) :
    {x : List Bool | ∃ i < len x, pair x (List.replicate i true) ∈ L} ∈ P :=
  FPPred.mem_P (FPPred.exists_lt (n := len) (p := (· ∈ L)) hlen
    (exists_decisionFn_of_mem_P hL))

end Complexity
