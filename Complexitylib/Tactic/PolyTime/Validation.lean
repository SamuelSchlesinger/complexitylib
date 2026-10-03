/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Tactic.PolyTime

/-!
# Polynomial-time tactic regression checks

These clients check all three supported predicates, local algorithm calls, and
the efficiency and size premises of iteration. Negative checks ensure the tactic
still fails when a required certificate is removed. The Cobham validation root
imports this module; it stays outside the public import graph.
-/

namespace Complexity.Tactic.PolyTime.Validation

private def duplicate (z : List Bool) : List Bool := z ++ z

@[polytime] private theorem duplicate_mem_FP : duplicate ∈ FP := by
  polytime [duplicate]

private def mirrored (z : List Bool) : List Bool := z ++ z.reverse

@[polytime] private theorem mirrored_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun z => mirrored (f z)) ∈ FP := by
  polytime [mirrored]

-- A closure rule also certifies the operation itself, including eta-reduced goals.
example : mirrored ∈ FP := by polytime

example : (fun z : List Bool => duplicate (z ++ [true])) ∈ FP := by
  polytime

-- Composition can expose a partially applied constructor as its input function.
example : (fun z : List Bool => duplicate (pair [] z)) ∈ FP := by
  polytime

example (r : ℕ → ℕ) (f : List Bool → List Bool) (hf : f ∈ FP)
    (hr : (fun z : List Bool => List.replicate (r z.length) true) ∈ FP) :
    UnaryFn (fun z => r (f z).length) := by
  polytime

example : (fun z : List Bool =>
    List.replicate ((pairSnd z).length / (pairFst z).length) true) ∈ FP := by
  polytime

example : UnaryFn (fun z => z.length ^ 3 + 2 * z.length + 1) := by
  polytime

-- Rounding to a variable-base power has a bilinear bound, including bases 0 and 1.
example (b n : List Bool → ℕ) (hb : UnaryFn b) (hn : UnaryFn n) :
    UnaryFn (fun z => b z ^ Nat.clog (b z) (n z)) := by
  fail_if_success (clear hb; polytime)
  fail_if_success (clear hn; polytime)
  polytime

example (n : List Bool → ℕ) (hn : (fun z => List.replicate (n z) true) ∈ FP) :
    UnaryFn (fun z => n z + 1) := by
  polytime

example : FPPred (fun z => z.length % 3 = 0 ∧ z.length < 20) := by
  polytime

example (f : List Bool → List Bool) (hf : f ∈ FP) :
    (fun z => pair ((f z).reverse.take (z.length / 2)) (f z ++ z)) ∈ FP := by
  fail_if_success (clear hf; polytime)
  polytime

example (f g : List Bool → List Bool) (hf : f ∈ FP) (hg : g ∈ FP) :
    (fun z => g (f z ++ z)) ∈ FP := by
  fail_if_success (clear hg; polytime)
  polytime

example (f : List Bool → List Bool) (hf : f ∈ FP)
    (n : List Bool → ℕ) (hn : UnaryFn n) :
    UnaryFn (fun z => n (f z ++ z) + 1) := by
  fail_if_success (clear hn; polytime)
  polytime

example (f : List Bool → List Bool) (hf : f ∈ FP)
    (p : List Bool → Prop) (hp : FPPred p) :
    FPPred (fun z => p (f z ++ z) ∧ z.length < 20) := by
  fail_if_success (clear hp; polytime)
  polytime

example (f : List Bool → List Bool) (hf : f ∈ FP) :
    (fun z => if z.length < 5 then (f z).reverse else z ++ [true]) ∈ FP := by
  polytime

example (p : List Bool → Prop) (hp : FPPred p) :
    FPPred (fun z => ∀ i < z.length, p (pair z (List.replicate i true))) := by
  fail_if_success (clear hp; polytime)
  polytime

example (f : List Bool → List Bool) (hf : f ∈ FP) (growth : ℕ)
    (hgrowth : ∀ w, (f w).length ≤ w.length + growth) :
    (fun z => f^[z.length ^ 2] z) ∈ FP := by
  fail_if_success (clear hgrowth; polytime)
  fail_if_success (clear hf; polytime)
  polytime

-- Variable powers cannot be materialized in unary without a polynomial bound.
example : True := by
  fail_if_success
    have : UnaryFn (fun z => 2 ^ z.length) := by polytime
  trivial

end Complexity.Tactic.PolyTime.Validation
