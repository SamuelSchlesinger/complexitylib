/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Encoding.Arithmetic
public import Complexitylib.DescriptiveComplexity.FirstOrder.Semantics

/-!
# First-order evaluation by arithmetic bit access

Evaluate terms and formulas directly on a bit string, with a supplied universe
size and natural-number variable values. Constants are found by bounded search
of their one-hot blocks; quantifiers enumerate the natural numbers below the
universe size. The operations are total even on malformed input. The surface
module proves correctness on encodings and combines evaluation with validation.
`Formula.tableCode` scans all free-variable assignments in the encoder's tuple
order to produce a complete relation truth table.

This is the standard fixed-formula model-checking argument for first-order
queries, following Immerman's *Descriptive Complexity*. Its polynomial-time
proof uses the library's machine-backed `UnaryFn` and `FPPred` closure rules.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

/-- Evaluate a term by its variable value or the first marked bit in its constant block. -/
def Term.evalCode {V : Vocabulary} {n : Nat} (card : Nat) (bits : List Bool)
    (σ : Fin n → Nat) : Term V n → Nat
  | .var i => σ i
  | .const c => (List.range card).findIdx fun a =>
    bits[constantAddress V card c a]?.getD false

/-- Evaluate a formula with arithmetic table reads and bounded first-order quantifiers. -/
def Formula.evalCode {V : Vocabulary} (card : Nat) (bits : List Bool) :
    {n : Nat} → Formula V n → (Fin n → Nat) → Bool
  | _, .relApp r args, σ =>
    bits[relationAddress V card r (fun i => (args i).evalCode card bits σ)]?.getD false
  | _, .eq a b, σ => decide (a.evalCode card bits σ = b.evalCode card bits σ)
  | _, .neg φ, σ => !(φ.evalCode card bits σ)
  | _, .conj φ ψ, σ => φ.evalCode card bits σ && ψ.evalCode card bits σ
  | _, .disj φ ψ, σ => φ.evalCode card bits σ || ψ.evalCode card bits σ
  | _, .exist φ, σ => (List.range card).any fun a => φ.evalCode card bits (Fin.cons a σ)
  | _, .all φ, σ => (List.range card).all fun a => φ.evalCode card bits (Fin.cons a σ)

/-- The truth table of an open formula, scanning assignments in the structure encoder's order. -/
def Formula.tableCode {V : Vocabulary} {n : Nat} (φ : Formula V n)
    (card : Nat) (bits : List Bool) : List Bool :=
  (List.range (card ^ n)).map fun index => φ.evalCode card bits (tupleDigits card n index)

end Complexity.DescriptiveComplexity
