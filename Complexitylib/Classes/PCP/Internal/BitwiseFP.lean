/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Cobham.Internal
public import Complexitylib.Classes.P.Range
public import Complexitylib.Classes.P.UnaryLength
public import Complexitylib.Classes.P.PairWithInput
public import Complexitylib.Classes.P.Composition
public import Complexitylib.Classes.Containments.Internal.FPBridge
public import Complexitylib.Classes.Containments.Internal.PVerdict

/-!
# Computing an output one bit at a time, from a language in `P`

A polynomial-time function is usually easiest to describe not as a string
transformation but as a rule for each output bit: "the `i`-th bit of `f x` is
whatever this decision procedure says". `bitwise_mem_FP` in
`Complexitylib.Classes.P.Range` turns such a description, with the bit rule
given as a polynomial-time function, into `f ∈ FP`. This module takes the bit
rule as a language in `P` instead.

This is the bridge that lets a decision procedure written on the RAM surface
(where `RAM_P_eq_P` transfers it to `P`) be used to build a *function* in `FP`,
for which no direct RAM bridge exists.

## Main results

- `Complexity.bitwise_mem_FP_of_mem_P` — a bitwise description with the bit rule
  given as a language in `P`, which is the form the RAM surface produces, puts
  the function in `FP`
-/

@[expose] public section

namespace Complexity

/-- **A function described bit by bit, from a language in `P`.** This is
`bitwise_mem_FP` with the bit rule established as a decision problem ("does
position `i` of the output carry a one?"), which is the form in which
`RAM_P_eq_P` delivers it. -/
theorem bitwise_mem_FP_of_mem_P {len : List Bool → ℕ} {b : List Bool → ℕ → Bool}
    (hlen : (fun x => List.replicate (len x) true) ∈ FP)
    {L : Language} (hL : L ∈ P)
    (hLspec : ∀ x i, pair x (List.replicate i true) ∈ L ↔ b x i = true) :
    (fun x => (List.range (len x)).map (b x)) ∈ FP := by
  obtain ⟨g, hgFP, hg⟩ := exists_decisionFn_of_mem_P hL
  exact bitwise_mem_FP hlen hgFP fun x i =>
    congrArg (fun c => [c]) (Bool.eq_iff_iff.mpr ((hg _).symm.trans (hLspec x i)))

end Complexity
