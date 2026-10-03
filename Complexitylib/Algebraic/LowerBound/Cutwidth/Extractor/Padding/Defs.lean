/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Defs
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Balanced padding of a sumset disperser

One fresh input bit balances a Boolean function exactly. Two-sided sumset
dispersion survives with twice the source-size threshold, so any fixed
extraction error below one half suffices for the circuit lower bound's density
requirement after padding.
-/

@[expose] public section

namespace Algebraic.Cutwidth

/-- Every sufficiently large pair of flat sources has both Boolean outputs
among its sums. Unlike extraction, this imposes no quantitative bias bound. -/
def FlatSumsetDisperser {n : Nat} (f : Cslib.BooleanFunction n) (K : Nat) : Prop :=
  ∀ P Q : Finset (Fin n → Bool), K ≤ P.card → K ≤ Q.card →
    ∀ b : Bool, ∃ x ∈ P, ∃ y ∈ Q, f (xorInput x y) = b

/-- XOR the original verdict with a fresh first input bit. -/
def balancePad {n : Nat} (f : Cslib.BooleanFunction n) : Cslib.BooleanFunction (n + 1) :=
  fun x => Bool.xor (f (Fin.tail x)) (x 0)

/-- The uniform list evaluator for balanced padding. The original evaluator
reads the tail, and its first output bit is XORed with the first input bit. -/
def balancePadEval (eval : List Bool → List Bool) (x : List Bool) : List Bool :=
  [Bool.xor ((eval x.tail).headD false) (x.headD false)]

end Algebraic.Cutwidth
