/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Rectangle
public import Mathlib.Basic.Real.Basic

/-!
# Flat-source sumset extraction

`FlatSumsetExtractor f K ν` is the finite-counting form of one-bit sumset
extraction for two independent uniform sources, each supported on at least
`K` inputs. It counts source pairs rather than distinct XORs, retaining the
multiplicity of every output. In entropy notation the threshold is `log₂ K`.

This is the part of the usual sumset-extractor contract needed by the circuit
lower bound. Xin Li's *Two Source Extractors for Asymptotically Optimal
Entropy, and (Many) More*, Theorem 7.13 (2023), supplies the intended explicit
construction with polynomial `K`. Its construction is not proved in this
module. Eshan Chattopadhyay and Jyun-Jie Liao's *Extractors for Sum of Two
Sources* (2021) supplies a sufficient subexponential threshold for the
generalized circuit theorem with sublinear source entropy.
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth

open scoped Classical

variable {n : Nat}

/-- Coordinatewise addition over the two-element field. -/
def xorInput (x y : Fin n → Bool) : Fin n → Bool := fun i => Bool.xor (x i) (y i)

/-- Source pairs whose sum is accepted. Repeated sums are counted separately. -/
noncomputable def sumsetOnes (f : Cslib.BooleanFunction n)
    (P Q : Finset (Fin n → Bool)) : Finset ((Fin n → Bool) × (Fin n → Bool)) :=
  (P ×ˢ Q).filter fun xy => f (xorInput xy.1 xy.2) = true

/-- One-bit sumset extraction from two independent uniform sources, with
support size at least `K` and statistical error at most `ν`. -/
def FlatSumsetExtractor (f : Cslib.BooleanFunction n) (K : Nat) (ν : ℝ) : Prop :=
  ∀ P Q : Finset (Fin n → Bool), K ≤ P.card → K ≤ Q.card →
    (1 / 2 - ν) * (P.card * Q.card) ≤ ((sumsetOnes f P Q).card : ℝ) ∧
      ((sumsetOnes f P Q).card : ℝ) ≤ (1 / 2 + ν) * (P.card * Q.card)

end Cutwidth
end Algebraic
