/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Defs
public import Complexitylib.Classes.P.Defs
import Complexitylib.Classes.P.BitPolynomial.BlockEval
import Complexitylib.Classes.P.BitPolynomial.Frobenius
import Complexitylib.Classes.P.BitPolynomial.Transpose
import Complexitylib.Classes.P.BitPolynomial.Trinomial
import Complexitylib.Classes.P.Range
import Complexitylib.Encoding.BitPolynomial.Remainder
import Complexitylib.Tactic.PolyTime

/-!
# Bounds and uniformity of the runtime condenser program

Every coordinate has the width of one base-field coefficient, including
degenerate dimensions. Polynomial-time composition handles the transposes,
generated trinomials, bounded modular squaring, and block evaluation. A
polynomial-time concatenation supplies all requested coordinates.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity Complexity.BitPolynomial

private theorem significantLength_trinomialBits (d : Nat) :
    significantLength (trinomialBits d) = 2 * d + 1 := by
  apply Nat.le_antisymm
  · simpa only [trinomialBits_length] using significantLength_le (trinomialBits d)
  · have hlast : (trinomialBits d)[2 * d]?.getD false = true := by
      simp [trinomialBits]
    have hmem : 2 * d ∈ Finset.range (trinomialBits d).length := by
      simp only [Finset.mem_range, trinomialBits_length]
      lia
    simpa only [significantLength, hlast, Bool.true_eq, ite_true] using
      (Finset.le_sup (f := fun i => if (trinomialBits d)[i]?.getD false then i + 1 else 0)
        hmem)

theorem condenserCoordinateBits_length
    (coeffs halfDegree extensionCount seed powerCount : List Bool) :
    (condenserCoordinateBits coeffs halfDegree extensionCount seed powerCount).length =
      2 * halfDegree.length := by
  simp only [condenserCoordinateBits, blockEvalBits_length, significantLength_trinomialBits,
    Nat.add_sub_cancel]

theorem condenserBits_length
    (coeffs halfDegree extensionCount seed stride count : List Bool) :
    (condenserBits coeffs halfDegree extensionCount seed stride count).length =
      count.length * (2 * halfDegree.length) := by
  simp [condenserBits, condenserCoordinateBits_length]

private theorem coefficientBlock_flatMap {α : Type*} (f : α → List Bool) (width : Nat)
    (l : List α) (hlen : ∀ a ∈ l, (f a).length = width) (i : Nat) (hi : i < l.length) :
    coefficientBlock (l.flatMap f) width i = f l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    have ha : (f a).length = width := hlen a (by simp)
    have hl : ∀ b ∈ l, (f b).length = width := fun b hb => hlen b (by simp [hb])
    cases i with
    | zero =>
      simp only [coefficientBlock, Nat.zero_mul, List.drop_zero, List.flatMap_cons,
        List.getElem_cons_zero]
      exact List.take_left' ha
    | succ i =>
      have hi' : i < l.length := by simpa using hi
      change ((f a ++ l.flatMap f).drop ((i + 1) * width)).take width = f l[i]
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm (i * width) width, ← ha,
        List.drop_length_add_append]
      simpa only [coefficientBlock, ← ha] using ih hl i hi'

theorem coefficientBlock_condenserBits
    (coeffs halfDegree extensionCount seed stride count : List Bool)
    (i : Nat) (hi : i < count.length) :
    coefficientBlock (condenserBits coeffs halfDegree extensionCount seed stride count)
        (2 * halfDegree.length) i =
      condenserCoordinateBits coeffs halfDegree extensionCount seed
        (List.replicate (stride.length * i) true) := by
  have h := coefficientBlock_flatMap
      (fun j => condenserCoordinateBits coeffs halfDegree extensionCount seed
        (List.replicate (stride.length * j) true))
      (2 * halfDegree.length) (List.range count.length)
      (fun j _ => condenserCoordinateBits_length _ _ _ _ _) i (by simpa using hi)
  rw [List.getElem_range] at h
  exact h

theorem condenserEval_pair
    (coeffs halfDegree extensionCount seed stride count : List Bool) :
    condenserEval
        (pair (pair (pair coeffs halfDegree) (pair extensionCount seed)) (pair stride count)) =
      condenserBits coeffs halfDegree extensionCount seed stride count := by
  simp only [condenserEval, pairFst_pair, pairSnd_pair]

theorem condenserEval_length_le (z : List Bool) :
    (condenserEval z).length ≤ 2 * z.length ^ 2 := by
  simp only [condenserEval, condenserBits_length]
  have hcount : (pairSnd (pairSnd z)).length ≤ z.length :=
    (pairSnd_length_le _).trans (pairSnd_length_le _)
  have hhalf : (pairSnd (pairFst (pairFst z))).length ≤ z.length :=
    (pairSnd_length_le _).trans ((pairFst_length_le _).trans (pairFst_length_le _))
  calc
    _ ≤ z.length * (2 * z.length) := Nat.mul_le_mul hcount (Nat.mul_le_mul_left 2 hhalf)
    _ = 2 * z.length ^ 2 := by ring

private theorem frobeniusBits_mem_FP
    {a modulus count : List Bool → List Bool}
    (ha : a ∈ FP) (hmodulus : modulus ∈ FP) (hcount : count ∈ FP) :
    (fun z => frobeniusBits (a z) (modulus z) (count z)) ∈ FP := by
  have computation : (fun z => frobeniusEval (pair (pair (a z) (modulus z)) (count z))) ∈ FP :=
    by polytime
  exact mem_FP_of_eq computation fun z => frobeniusEval_pair _ _ _

theorem condenserCoordinateBits_mem_FP
    {coeffs halfDegree extensionCount seed powerCount : List Bool → List Bool}
    (hcoeffs : coeffs ∈ FP) (hhalfDegree : halfDegree ∈ FP)
    (hextensionCount : extensionCount ∈ FP) (hseed : seed ∈ FP) (hpowerCount : powerCount ∈ FP) :
    (fun z => condenserCoordinateBits
      (coeffs z) (halfDegree z) (extensionCount z) (seed z) (powerCount z)) ∈ FP := by
  have hpacked : (fun z => transposeBits (extensionCount z).length
      (2 * (halfDegree z).length) (coeffs z)) ∈ FP := by
    polytime
  have hmodulus : (fun z =>
      trinomialBits ((halfDegree z).length * (extensionCount z).length)) ∈ FP := by
    polytime
  have hpowered := frobeniusBits_mem_FP hpacked hmodulus hpowerCount
  have hunpacked : (fun z => transposeBits (2 * (halfDegree z).length)
      (extensionCount z).length (frobeniusBits
        (transposeBits (extensionCount z).length (2 * (halfDegree z).length) (coeffs z))
        (trinomialBits ((halfDegree z).length * (extensionCount z).length)) (powerCount z))) ∈ FP :=
    by polytime
  have computation : (fun z => blockEval
      (pair (pair
        (pair (transposeBits (2 * (halfDegree z).length) (extensionCount z).length
          (frobeniusBits
            (transposeBits (extensionCount z).length (2 * (halfDegree z).length) (coeffs z))
            (trinomialBits ((halfDegree z).length * (extensionCount z).length)) (powerCount z)))
          (List.replicate (2 * (halfDegree z).length) true))
        (pair (seed z) (trinomialBits (halfDegree z).length))) (extensionCount z))) ∈ FP := by
    polytime
  refine mem_FP_of_eq computation fun z => ?_
  simp only [blockEval_pair, List.length_replicate, condenserCoordinateBits]

theorem condenserBits_mem_FP
    {coeffs halfDegree extensionCount seed stride count : List Bool → List Bool}
    (hcoeffs : coeffs ∈ FP) (hhalfDegree : halfDegree ∈ FP)
    (hextensionCount : extensionCount ∈ FP) (hseed : seed ∈ FP)
    (hstride : stride ∈ FP) (hcount : count ∈ FP) :
    (fun z => condenserBits
      (coeffs z) (halfDegree z) (extensionCount z) (seed z) (stride z) (count z)) ∈ FP := by
  have hentry : (fun w => condenserCoordinateBits
      (coeffs (pairFst w)) (halfDegree (pairFst w)) (extensionCount (pairFst w))
      (seed (pairFst w))
      (List.replicate ((stride (pairFst w)).length * (pairSnd w).length) true)) ∈ FP := by
    apply condenserCoordinateBits_mem_FP <;> polytime
  refine mem_FP_of_eq (flatMap_range_mem_FP hentry hcount) fun z => ?_
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate, condenserBits]

theorem condenserEval_mem_FP : condenserEval ∈ FP := by
  unfold condenserEval
  apply condenserBits_mem_FP <;> polytime

end Algebraic.Cutwidth.Extractor.Internal
