/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Subroutines.BinaryPolynomial.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryPolynomial.Internal

/-!
# Canonical binary evaluation of a fixed natural polynomial

This module exposes a finite Horner program compiled from a fixed polynomial.
It preserves the input, writes the polynomial value to the designated result
tape in canonical binary, and restores the scratch accumulator and both
counters to canonical zero. Its all-prefix space bound depends on value width,
not runtime, and is logarithmic in the input value for every fixed polynomial.

## Main results

- `binaryHornerFold_polyCoeffs` identifies the compiled Horner coefficients.
- `binaryPolynomialEvalTM_hoareTime_frame` gives the endpoint and time bound.
- `binaryPolynomialEvalTM_hoareTimeSpace_frame` bounds every execution prefix.
- `binaryPolynomialSpace_bigO` proves the fixed-polynomial logarithmic bound.
- `binaryPolynomialEvalTM_isTransducer` proves append-only-output safety.
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- A fixed polynomial contributes exactly one coefficient for each degree
through its natural degree, including explicit zero coefficients. -/
@[simp] theorem binaryPolynomialCoeffs_length (p : Polynomial ℕ) :
    (binaryPolynomialCoeffs p).length = p.natDegree + 1 :=
  binaryPolynomialCoeffs_length_internal p

/-- The compiled coefficient list is never empty, including for the zero
polynomial. -/
theorem binaryPolynomialCoeffs_ne_nil (p : Polynomial ℕ) :
    binaryPolynomialCoeffs p ≠ [] :=
  binaryPolynomialCoeffs_ne_nil_internal p

/-- Horner evaluation leaves an accumulator unchanged at the empty list. -/
@[simp] theorem binaryHornerFold_nil (x acc : ℕ) :
    binaryHornerFold x [] acc = acc :=
  binaryHornerFold_nil_internal x acc

/-- One Horner step multiplies the accumulator by the input and adds the next
coefficient. -/
theorem binaryHornerFold_cons (x coeff acc : ℕ) (coeffs : List ℕ) :
    binaryHornerFold x (coeff :: coeffs) acc =
      binaryHornerFold x coeffs (acc * x + coeff) :=
  binaryHornerFold_cons_internal x coeff acc coeffs

/-- The high-degree-first coefficient list computes the polynomial's ordinary
evaluation when Horner evaluation starts from zero. -/
theorem binaryHornerFold_polyCoeffs (p : Polynomial ℕ) (x : ℕ) :
    binaryHornerFold x (binaryPolynomialCoeffs p) 0 = p.eval x :=
  binaryHornerFold_polyCoeffs_internal p x

/-- Ordinary polynomial evaluation is bounded by the explicit cap used for
every intermediate value of the compiled Horner routine. -/
theorem binaryPolynomial_eval_le_valueCap
    (p : Polynomial ℕ) (x : ℕ) :
    p.eval x ≤ binaryPolynomialValueCap p x :=
  binaryPolynomial_eval_le_valueCap_internal p x

/-- Evaluating a fixed polynomial changes only the result tape. The input is
preserved literally, and the scratch accumulator and both internal counters
are restored to their initial canonical-zero tapes. -/
theorem binaryPolynomialEvalTM_hoareTime_frame
    (inputIdx resultIdx scratchIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryPolynomialDistinct inputIdx resultIdx scratchIdx
      mulCounterIdx addCounterIdx)
    (p : Polynomial ℕ) (inputValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : (work₀ inputIdx).HasBinaryNat inputValue)
    (hresult : (work₀ resultIdx).HasBinaryNat 0)
    (hscratch : (work₀ scratchIdx).HasBinaryNat 0)
    (hmulCounter : (work₀ mulCounterIdx).HasBinaryNat 0)
    (haddCounter : (work₀ addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ inputIdx → i ≠ resultIdx → i ≠ scratchIdx →
      i ≠ mulCounterIdx → i ≠ addCounterIdx → Parked (work₀ i))
    (hout : Parked out₀) :
    (binaryPolynomialEvalTM inputIdx resultIdx scratchIdx mulCounterIdx
      addCounterIdx p).HoareTime
        (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        (fun inp work out =>
          inp = inp₀ ∧
          work = Function.update work₀ resultIdx
            ((Tape.init ((p.eval inputValue).bits.map Γ.ofBool)).move
              Dir3.right) ∧
          out = out₀)
        (binaryPolynomialTime p inputValue) :=
  binaryPolynomialEvalTM_hoareTime_frame_internal inputIdx resultIdx
    scratchIdx mulCounterIdx addCounterIdx hdistinct p inputValue inp₀ work₀
    out₀ hinput hresult hscratch hmulCounter haddCounter hinp hother hout

/-- Every prefix of fixed-polynomial evaluation respects a common bound based
on the width of a polynomial cap for all Horner intermediate values. -/
theorem binaryPolynomialEvalTM_hoareTimeSpace_frame
    (inputIdx resultIdx scratchIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryPolynomialDistinct inputIdx resultIdx scratchIdx
      mulCounterIdx addCounterIdx)
    (p : Polynomial ℕ) (inputValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : (work₀ inputIdx).HasBinaryNat inputValue)
    (hresult : (work₀ resultIdx).HasBinaryNat 0)
    (hscratch : (work₀ scratchIdx).HasBinaryNat 0)
    (hmulCounter : (work₀ mulCounterIdx).HasBinaryNat 0)
    (haddCounter : (work₀ addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ inputIdx → i ≠ resultIdx → i ≠ scratchIdx →
      i ≠ mulCounterIdx → i ≠ addCounterIdx → Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (binaryPolynomialEvalTM inputIdx resultIdx scratchIdx mulCounterIdx
      addCounterIdx p).HoareTimeSpace
        (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        (fun inp work out =>
          inp = inp₀ ∧
          work = Function.update work₀ resultIdx
            ((Tape.init ((p.eval inputValue).bits.map Γ.ofBool)).move
              Dir3.right) ∧
          out = out₀)
        (binaryPolynomialTime p inputValue) inputLength
        (binaryPolynomialSpace initialSpace p inputValue) :=
  binaryPolynomialEvalTM_hoareTimeSpace_frame_internal inputIdx resultIdx
    scratchIdx mulCounterIdx addCounterIdx hdistinct p inputValue inputLength
    initialSpace inp₀ work₀ out₀ hinput hresult hscratch hmulCounter
    haddCounter hinp hother hout hworkSpace hinputSpace

/-- For every fixed polynomial and initial-space allowance, the public
all-prefix space bound is logarithmic in the numeric input. -/
theorem binaryPolynomialSpace_bigO (initialSpace : ℕ) (p : Polynomial ℕ) :
    (fun inputValue => binaryPolynomialSpace initialSpace p inputValue) =O
      (fun inputValue => Nat.log 2 inputValue) :=
  binaryPolynomialSpace_bigO_internal initialSpace p

/-- Evaluation of the explicit width polynomial is exactly twice the
Horner-prefix value cap. -/
@[simp] theorem binaryPolynomialSpaceWidthPolynomial_eval
    (p : Polynomial ℕ) (inputValue : ℕ) :
    (binaryPolynomialSpaceWidthPolynomial p).eval inputValue =
      2 * binaryPolynomialValueCap p inputValue :=
  binaryPolynomialSpaceWidthPolynomial_eval_internal p inputValue

/-- Fixed-polynomial evaluation never moves its output head left. -/
theorem binaryPolynomialEvalTM_isTransducer
    (inputIdx resultIdx scratchIdx mulCounterIdx addCounterIdx : Fin n)
    (p : Polynomial ℕ) :
    (binaryPolynomialEvalTM inputIdx resultIdx scratchIdx mulCounterIdx
      addCounterIdx p).IsTransducer :=
  binaryPolynomialEvalTM_isTransducer_internal inputIdx resultIdx scratchIdx
    mulCounterIdx addCounterIdx p

end TM

end Complexity
