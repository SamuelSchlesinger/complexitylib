/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly
public import Complexitylib.Classes.PPoly.Advice.Reverse.Defs
public import Complexitylib.Circuits.Encoding.Machine
public import Complexitylib.Classes.PPoly.Advice.Defs
public import Mathlib.Tactic.SetNotationForOrder

/-!
# Nonuniform circuits as polynomial advice — proof internals

This module supplies a circuit family member's canonical code as advice to the
verified serialized evaluator. It proves polynomial advice length, evaluator
correctness on that advice, and polynomial time measured in the original input
length.
-/


public section

namespace Complexity

namespace CircuitFamily

/-- Internal proof that canonical member encodings of a polynomial-size family
form polynomial-length advice. -/
theorem polynomialAdvice_encodeAt_internal
    (F : CircuitFamily Basis.andOr2) {d : ℕ}
    (hsize : F.size =O ((· ^ d) : ℕ → ℕ)) :
    PolynomialAdvice F.encodeAt := by
  obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound
    (CircuitCode.encodeAt_length_bigO F hsize)
  exact ⟨p, hp⟩

/-- Internal correctness of the serialized evaluator when `F.encodeAt` is
used as its length-dependent advice. -/
theorem Decides.evalFamilyTM_decidesWithAdviceInTime_internal
    {F : CircuitFamily Basis.andOr2} {L : Language}
    (hdec : F.Decides L) :
    CircuitCode.Machine.evalFamilyTM.DecidesWithAdviceInTime
      F.encodeAt L F.adviceEvalTime := by
  intro x
  obtain ⟨c', t, ht, hreach, hhalt, hyes, hno⟩ :=
    CircuitCode.Machine.evalFamilyTM_decidesInTime
      (advisedInput F.encodeAt x)
  refine ⟨c', t, ?_, hreach, hhalt, ?_, ?_⟩
  · rw [advisedInput, pair_length] at ht
    exact ht
  · intro hx
    apply hyes
    rw [advisedInput]
    exact (CircuitCode.encodeAt_pair_mem_circuitEvalLanguage_iff F x).2
      ((hdec.evalList x).2 hx)
  · intro hx
    apply hno
    rw [advisedInput]
    intro hmem
    exact hx ((hdec.evalList x).1
      ((CircuitCode.encodeAt_pair_mem_circuitEvalLanguage_iff F x).1 hmem))

/-- Internal polynomial bound for evaluating the canonical member-code advice
of a polynomial-size circuit family. -/
theorem adviceEvalTime_bigO_internal
    (F : CircuitFamily Basis.andOr2) {d : ℕ}
    (hsize : F.size =O ((· ^ d) : ℕ → ℕ)) :
    F.adviceEvalTime =O ((· ^ (4 * (d + 1))) : ℕ → ℕ) := by
  let e := 2 * (d + 1)
  have hcode : (fun n => (F.encodeAt n).length) =O
      ((· ^ e) : ℕ → ℕ) := by
    simpa only [e] using CircuitCode.encodeAt_length_bigO F hsize
  have hnLinear : (fun n : ℕ => n) =O ((· ^ 1) : ℕ → ℕ) := by
    simpa only [pow_one] using BigO.refl (fun n : ℕ => n)
  have hn : (fun n : ℕ => n) =O ((· ^ e) : ℕ → ℕ) :=
    hnLinear.trans (BigO.pow_le_pow_right (by dsimp [e]; omega))
  let pairedLength : ℕ → ℕ := fun n =>
    2 * (F.encodeAt n).length + 2 + n
  have hpaired : pairedLength =O ((· ^ e) : ℕ → ℕ) := by
    unfold pairedLength
    exact BigO.add
      (BigO.add (BigO.const_mul_left 2 hcode)
        (BigO.const_le_pow 2 e)) hn
  have hpairedSquaredPower :
      (fun n : ℕ => (n ^ e) ^ 2) =O
        ((· ^ (2 * e)) : ℕ → ℕ) := by
    apply BigO.of_le
    intro n
    apply le_of_eq
    rw [← pow_mul]
    congr 1
    omega
  have hshift : (fun n => pairedLength n + 1) =O
      ((· ^ e) : ℕ → ℕ) :=
    BigO.add hpaired (BigO.const_le_pow 1 e)
  have hsquared : (fun n => (pairedLength n + 1) ^ 2) =O
      ((· ^ (2 * e)) : ℕ → ℕ) :=
    (BigO.pow hshift 2).trans hpairedSquaredPower
  have hpairedLarge : pairedLength =O
      ((· ^ (2 * e)) : ℕ → ℕ) :=
    hpaired.trans (BigO.pow_le_pow_right (by omega))
  have htime :
      (fun n => 4 * pairedLength n +
        20 * (pairedLength n + 1) ^ 2 + 17) =O
          ((· ^ (2 * e)) : ℕ → ℕ) :=
    BigO.add
      (BigO.add (BigO.const_mul_left 4 hpairedLarge)
        (BigO.const_mul_left 20 hsquared))
      (BigO.const_le_pow 17 (2 * e))
  have hexponent : 2 * e = 4 * (d + 1) := by
    dsimp [e]
    omega
  rw [hexponent] at htime
  exact htime

/-- Internal packaging of one polynomial-size deciding circuit family as a
polynomial-time advised evaluator. -/
theorem Decides.mem_PAdvice_internal
    {F : CircuitFamily Basis.andOr2} {L : Language} {d : ℕ}
    (hdec : F.Decides L)
    (hsize : F.size =O ((· ^ d) : ℕ → ℕ)) : L ∈ PAdvice := by
  exact ⟨4 * (d + 1), CircuitCode.Machine.workTapeCount,
    CircuitCode.Machine.evalFamilyTM, F.encodeAt, F.adviceEvalTime,
    F.polynomialAdvice_encodeAt_internal hsize,
    hdec.evalFamilyTM_decidesWithAdviceInTime_internal,
    F.adviceEvalTime_bigO_internal hsize⟩

end CircuitFamily

/-- Internal proof that polynomial-size nonuniform circuits can be evaluated
in polynomial time using their canonical member codes as advice. -/
theorem PPoly_subset_PAdvice_internal : PPoly ⊆ PAdvice := by
  intro L hL
  rw [mem_PPoly_iff] at hL
  obtain ⟨F, d, hdec, hsize⟩ := hL
  exact hdec.mem_PAdvice_internal hsize

end Complexity
