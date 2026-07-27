/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryAddConst.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryMulAdd.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.ClearWork.Defs

/-!
# Canonical binary evaluation of a fixed natural polynomial — definitions

A fixed polynomial is compiled into finitely many Horner layers. Each layer
multiplies the current accumulator by the preserved input, adds one hardwired
coefficient, clears the old accumulator, and swaps the two accumulator roles.
The initial orientation is chosen from coefficient-list parity so the
designated result tape holds the final value and the other accumulator is zero.
-/

@[expose] public section

namespace Complexity

namespace TM

/-- The five tape roles used by binary polynomial evaluation are pairwise
distinct. -/
structure BinaryPolynomialDistinct {n : ℕ}
    (inputIdx resultIdx scratchIdx mulCounterIdx addCounterIdx : Fin n) : Prop where
  input_ne_result : inputIdx ≠ resultIdx
  input_ne_scratch : inputIdx ≠ scratchIdx
  input_ne_mulCounter : inputIdx ≠ mulCounterIdx
  input_ne_addCounter : inputIdx ≠ addCounterIdx
  result_ne_scratch : resultIdx ≠ scratchIdx
  result_ne_mulCounter : resultIdx ≠ mulCounterIdx
  result_ne_addCounter : resultIdx ≠ addCounterIdx
  scratch_ne_mulCounter : scratchIdx ≠ mulCounterIdx
  scratch_ne_addCounter : scratchIdx ≠ addCounterIdx
  mulCounter_ne_addCounter : mulCounterIdx ≠ addCounterIdx

/-- Coefficients of `p`, highest degree first. -/
def binaryPolynomialCoeffs (p : Polynomial ℕ) : List ℕ :=
  ((List.range (p.natDegree + 1)).map p.coeff).reverse

/-- Horner evaluation of a highest-degree-first coefficient list. -/
def binaryHornerFold (x : ℕ) : List ℕ → ℕ → ℕ
  | [], acc => acc
  | coeff :: coeffs, acc =>
      binaryHornerFold x coeffs (acc * x + coeff)

/-- One Horner layer: `target := source * input + coeff`, followed by clearing
`source` to canonical zero. -/
def binaryHornerLayerTM {n : ℕ}
    (inputIdx sourceIdx targetIdx mulCounterIdx addCounterIdx : Fin n)
    (coeff : ℕ) : TM n :=
  seqTM
    (seqTM
      (binaryMulAddIntoTM sourceIdx inputIdx targetIdx mulCounterIdx
        addCounterIdx)
      (binaryAddConstTM targetIdx coeff))
    (clearWorkTM sourceIdx)

/-- Compile a coefficient list into finitely many alternating Horner layers. -/
def binaryHornerLayersTM {n : ℕ}
    (inputIdx sourceIdx targetIdx mulCounterIdx addCounterIdx : Fin n) :
    List ℕ → TM n
  | [] => binaryAddConstTM sourceIdx 0
  | coeff :: coeffs =>
      seqTM
        (binaryHornerLayerTM inputIdx sourceIdx targetIdx mulCounterIdx
          addCounterIdx coeff)
        (binaryHornerLayersTM inputIdx targetIdx sourceIdx mulCounterIdx
          addCounterIdx coeffs)

/-- Evaluate a fixed natural polynomial. Parity chooses which zero
accumulator is the initial source so the designated result is final. -/
def binaryPolynomialEvalTM {n : ℕ}
    (inputIdx resultIdx scratchIdx mulCounterIdx addCounterIdx : Fin n)
    (p : Polynomial ℕ) : TM n :=
  if Even (binaryPolynomialCoeffs p).length then
    binaryHornerLayersTM inputIdx resultIdx scratchIdx mulCounterIdx
      addCounterIdx (binaryPolynomialCoeffs p)
  else
    binaryHornerLayersTM inputIdx scratchIdx resultIdx mulCounterIdx
      addCounterIdx (binaryPolynomialCoeffs p)

/-- Runtime of one Horner layer. -/
def binaryHornerLayerTime (inputValue accValue coeff : ℕ) : ℕ :=
  binaryMulAddTime accValue inputValue 0 + 1 +
    binaryAddConstTime coeff (accValue * inputValue) + 1 +
    clearWorkTimeBound accValue.size

/-- Runtime of a finite Horner layer list. -/
def binaryHornerLayersTime (inputValue : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 1
  | coeff :: coeffs, accValue =>
      binaryHornerLayerTime inputValue accValue coeff + 1 +
        binaryHornerLayersTime inputValue coeffs
          (accValue * inputValue + coeff)

/-- Runtime of fixed-polynomial evaluation. -/
def binaryPolynomialTime (p : Polynomial ℕ) (inputValue : ℕ) : ℕ :=
  binaryHornerLayersTime inputValue (binaryPolynomialCoeffs p) 0

/-- Local all-prefix space bound for one Horner layer. -/
def binaryHornerLayerSpace
    (initialSpace inputValue accValue coeff : ℕ) : ℕ :=
  max (binaryMulAddSpace initialSpace accValue inputValue 0)
    (max (binaryAddConstSpace initialSpace coeff (accValue * inputValue))
      (initialSpace + clearWorkTimeBound accValue.size))

/-- Polynomial cap dominating every Horner prefix value. -/
def binaryPolynomialValueCap (p : Polynomial ℕ) (inputValue : ℕ) : ℕ :=
  ((binaryPolynomialCoeffs p).sum + 1) *
    (inputValue + 1) ^ (binaryPolynomialCoeffs p).length

/-- A natural polynomial whose value is exactly twice the Horner-prefix cap
used by `binaryPolynomialSpace`. -/
noncomputable def binaryPolynomialSpaceWidthPolynomial
    (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (2 * ((binaryPolynomialCoeffs p).sum + 1)) *
    (Polynomial.X + Polynomial.C 1) ^ (binaryPolynomialCoeffs p).length

/-- Public width-based all-prefix space bound for polynomial evaluation. -/
def binaryPolynomialSpace
    (initialSpace : ℕ) (p : Polynomial ℕ) (inputValue : ℕ) : ℕ :=
  initialSpace + 10 * (2 * binaryPolynomialValueCap p inputValue).size + 17

end TM

end Complexity
