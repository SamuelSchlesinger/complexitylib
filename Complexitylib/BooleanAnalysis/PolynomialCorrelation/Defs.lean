/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.Real.Sqrt

/-!
# Polynomial correlation: definitions

We use the set of true coordinates to encode a Boolean block. A block has odd
length `2 * m + 1`, and majority is one exactly when its cardinality exceeds `m`.
The result being formalized is Theorem 1.1 of Chattopadhyay, Hatami, Lee, Lovett,
Tal, and Viola, *Exponential Correlation Bounds for Polynomials* (2026),
https://arxiv.org/abs/2609.28839.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.PolynomialCorrelation

open Finset

/-- Boolean monomials, evaluated on the set of true coordinates. -/
def monomial {ι : Type*} [DecidableEq ι] (a x : Finset ι) : ZMod 2 :=
  if a ⊆ x then 1 else 0

/-- Squarefree monomials of degree at most `m`. -/
abbrev Low (ι : Type*) (m : ℕ) := {a : Finset ι // a.card ≤ m}

/-- The low-degree space on a single Boolean block. -/
def lowSpan {ι : Type*} [DecidableEq ι] (m : ℕ) :
    Submodule (ZMod 2) (Finset ι → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range fun a : Low ι m => monomial a.val)

/-- An input consisting of `k` disjoint blocks of odd length `2 * m + 1`. -/
abbrev BlockCube (k m : ℕ) := Fin k → Finset (Fin (2 * m + 1))

/-- Strict majority on a block of odd length. -/
def majority {m : ℕ} (x : Finset (Fin (2 * m + 1))) : ZMod 2 :=
  if m < x.card then 1 else 0

/-- XOR of the majorities of the disjoint blocks. -/
def xorMajority {k m : ℕ} (x : BlockCube k m) : ZMod 2 :=
  ∑ i, majority (x i)

/-- Read the individual bits from a block input. -/
def blockBits {k m : ℕ} (x : BlockCube k m) (ij : Fin k × Fin (2 * m + 1)) : ZMod 2 :=
  if ij.2 ∈ x ij.1 then 1 else 0

/-- Collect the true coordinates of each block of a binary assignment. -/
def bitsToBlocks {k m : ℕ} (x : Fin k × Fin (2 * m + 1) → ZMod 2) : BlockCube k m :=
  fun i => univ.filter fun j => x (i, j) = 1

/-- XOR of block majorities on ordinary `ZMod 2` bit assignments. -/
def xorMajorityBits {k m : ℕ} (x : Fin k × Fin (2 * m + 1) → ZMod 2) : ZMod 2 :=
  xorMajority (bitsToBlocks x)

/-- Evaluate a multivariate polynomial on the bits of a block input. -/
def polynomialEval {k m : ℕ}
    (p : MvPolynomial (Fin k × Fin (2 * m + 1)) (ZMod 2))
    (x : BlockCube k m) : ZMod 2 :=
  MvPolynomial.eval (blockBits x) p

/-- The number of low monomials in the top `d` levels of an odd block.
The additive inequality also handles `d > m` without truncated subtraction. -/
def middleBandCount (m d : ℕ) : ℕ :=
  (univ.filter fun a : Finset (Fin (2 * m + 1)) => a.card ≤ m ∧ m < a.card + d).card

/-- Absolute uniform correlation of two binary-valued functions. -/
noncomputable def correlation {α : Type*} [Fintype α] (f g : α → ZMod 2) : ℝ :=
  |(∑ x, if f x = g x then (1 : ℝ) else -1) / Fintype.card α|

/-- An index for the single-block interpolation family. -/
abbrev Atom (m : ℕ) := Low (Fin (2 * m + 1)) m × Bool

/-- A low monomial, optionally multiplied by majority. -/
def atomEval {m : ℕ} (a : Atom m) (x : Finset (Fin (2 * m + 1))) : ZMod 2 :=
  monomial a.1.val x * if a.2 then majority x else 1

/-- The modified degree used in the paper's multiplication argument. -/
def atomWeight {m : ℕ} (a : Atom m) : ℕ :=
  if a.2 then m + 1 else a.1.val.card

/-- A product of one interpolation generator from each block. -/
abbrev Term (k m : ℕ) := Fin k → Atom m

/-- Evaluation of a product generator. -/
def termEval {k m : ℕ} (a : Term k m) (x : BlockCube k m) : ZMod 2 :=
  ∏ i, atomEval (a i) (x i)

/-- The sum of modified degrees over the blocks. -/
def weight {k m : ℕ} (a : Term k m) : ℕ := ∑ i, atomWeight (a i)

/-- Functions spanned by generators of weight at most `r`. -/
def filtration (k m r : ℕ) : Submodule (ZMod 2) (BlockCube k m → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range fun a : {a : Term k m // weight a ≤ r} =>
    termEval a.val)

end Complexity.BooleanAnalysis.PolynomialCorrelation
