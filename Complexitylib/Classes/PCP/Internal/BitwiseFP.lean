/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Cobham.Internal
public import Complexitylib.Classes.P.UnaryLength
public import Complexitylib.Classes.P.PairWithInput
public import Complexitylib.Classes.P.Composition
public import Complexitylib.Classes.Containments.Internal.FPBridge
public import Complexitylib.Classes.Containments.Internal.PVerdict

/-!
# Computing an output one bit at a time

A polynomial-time function is usually easiest to describe not as a string
transformation but as a rule for each output bit: "the `i`-th bit of `f x` is
whatever this decision procedure says". This module turns such a description
into `f ∈ FP`.

The two inputs are a unary length function — how long the output is, given in
unary so that it is itself a plausible `FP` output — and a bit oracle, a
polynomial-time function reading `pair x (unary i)` and returning the single
bit. The construction is an iteration of an append-one-bit step, run once per
output position, and `iterate_mem_FP` supplies the closure of `FP` under such
iterations.

This is the bridge that lets a decision procedure written on the RAM surface
(where `RAM_P_eq_P` transfers it to `P`) be used to build a *function* in `FP`,
for which no direct RAM bridge exists.

## Main definitions

- `Complexity.bitStep` — the append-one-bit step

## Main results

- `Complexity.bitwise_mem_FP` — a bitwise description puts the function in `FP`
- `Complexity.bitwise_mem_FP_of_mem_P` — the same with the bit rule given as a
  language in `P`, which is the form the RAM surface produces
-/

@[expose] public section

namespace Complexity

open Cobham

/-- One step of the construction: consult the oracle at the current output
length and append the bit it returns. The state is `pair (output so far) input`.
-/
def bitStep (G : List Bool → List Bool) (z : List Bool) : List Bool :=
  pair (pairFst z ++ G (pair (pairSnd z) (List.replicate (pairFst z).length true)))
    (pairSnd z)

theorem bitStep_mem_FP {G : List Bool → List Bool} (hG : G ∈ FP) : bitStep G ∈ FP := by
  have hfst : (fun z : List Bool => pairFst z) ∈ FP := fstBlock_mem_FP
  have hsnd : (fun z : List Bool => pairSnd z) ∈ FP := sndBlock_mem_FP
  have hcnt : (fun z : List Bool => List.replicate (pairFst z).length true) ∈ FP := by
    have := mem_FP_comp hfst unaryLength_mem_FP
    exact this
  have hquery : (fun z : List Bool =>
      G (pair (pairSnd z) (List.replicate (pairFst z).length true))) ∈ FP := by
    have := mem_FP_comp (pairFn_mem_FP hsnd hcnt) hG
    exact this
  exact pairFn_mem_FP (appendFn_mem_FP hfst hquery) hsnd

/-- Running the step from the empty output builds the first `n` bits. -/
theorem bitStep_iterate {G : List Bool → List Bool} {b : List Bool → ℕ → Bool}
    (hGspec : ∀ x i, G (pair x (List.replicate i true)) = [b x i]) (x : List Bool) :
    ∀ n : ℕ, (bitStep G)^[n] (pair [] x) = pair ((List.range n).map (b x)) x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, bitStep, pairFst_pair, pairSnd_pair,
        List.length_map, List.length_range, hGspec, List.range_succ, List.map_append]
      simp

/-- **A function described bit by bit is polynomial time.** If the output length
is computable in unary and each output bit is computable from the input and the
position in unary, the function itself is in `FP`. -/
theorem bitwise_mem_FP {len : List Bool → ℕ} {b : List Bool → ℕ → Bool}
    (hlen : (fun x => List.replicate (len x) true) ∈ FP)
    {G : List Bool → List Bool} (hG : G ∈ FP)
    (hGspec : ∀ x i, G (pair x (List.replicate i true)) = [b x i]) :
    (fun x => (List.range (len x)).map (b x)) ∈ FP := by
  have hinit : (fun x : List Bool => pair [] x) ∈ FP :=
    mem_FP_pairWithInput (constFn_mem_FP [])
  have hwidth : (fun x : List Bool => pair (List.replicate (len x) true) x) ∈ FP :=
    mem_FP_pairWithInput hlen
  have hbound : ∀ z : List Bool, ∀ n ≤ (List.replicate (len z) true).length,
      ((bitStep G)^[n] (pair [] z)).length
        ≤ (pair (List.replicate (len z) true) z).length := by
    intro z n hn
    rw [List.length_replicate] at hn
    rw [bitStep_iterate hGspec, pair_length, pair_length, List.length_map,
      List.length_range, List.length_replicate]
    omega
  have hiter := iterate_mem_FP (bitStep_mem_FP hG) hinit hlen hwidth hbound
  have := mem_FP_comp hiter fstBlock_mem_FP
  refine mem_FP_of_eq this ?_
  intro x
  rw [Function.comp_apply, List.length_replicate, bitStep_iterate hGspec, pairFst_pair]

/-- **The same, from a language in `P`.** The bit rule is usually established as
a decision problem — "does position `i` of the output carry a one?" — and this
is the form in which `RAM_P_eq_P` delivers it. -/
theorem bitwise_mem_FP_of_mem_P {len : List Bool → ℕ} {b : List Bool → ℕ → Bool}
    (hlen : (fun x => List.replicate (len x) true) ∈ FP)
    {L : Language} (hL : L ∈ P)
    (hLspec : ∀ x i, pair x (List.replicate i true) ∈ L ↔ b x i = true) :
    (fun x => (List.range (len x)).map (b x)) ∈ FP := by
  obtain ⟨g, hgFP, hg⟩ := exists_decisionFn_of_mem_P hL
  refine bitwise_mem_FP hlen hgFP ?_
  intro x i
  have : g (pair x (List.replicate i true)) = b x i := by
    have h1 := (hg (pair x (List.replicate i true))).symm.trans (hLspec x i)
    cases hb : b x i <;> cases hgv : g (pair x (List.replicate i true)) <;>
      simp [hb, hgv] at h1 ⊢
  rw [this]

end Complexity
