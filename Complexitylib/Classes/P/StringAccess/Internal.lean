/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.P.Unary
public import Complexitylib.Classes.P.Cobham.Internal.Extract

/-!
# Polynomial-time bit access and unary-prefix parsing

Relate the existing Cobham bit reader and leading-true-run loop to ordinary list
operations. These proofs include missing bits and unterminated unary prefixes.
-/

public section

namespace Complexity

theorem bitOf_eq_getElem?_internal (bits : List Bool) (i : Nat) :
    bitOf bits i = bits[i]?.getD false := by
  by_cases hi : i < bits.length
  · simp [bitOf_eq_getElem hi, List.getElem?_eq_getElem hi]
  · simp [bitOf_of_le (Nat.le_of_not_gt hi), List.getElem?_eq_none (Nat.le_of_not_gt hi)]

private theorem bitOf_before_takeWhile (bits : List Bool) (i : Nat)
    (hi : i < (bits.takeWhile id).length) : bitOf bits i = true := by
  induction bits generalizing i with
  | nil => simp at hi
  | cons b bits ih =>
    cases b with
    | false => simp at hi
    | true =>
      cases i with
      | zero => rfl
      | succ i =>
        exact ih i (by simpa using hi)

private theorem bitOf_at_takeWhile (bits : List Bool) :
    bitOf bits (bits.takeWhile id).length = false := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    cases b with
    | false => rfl
    | true => simpa [bitOf] using ih

theorem runTrue_length_takeWhile_internal (bits : List Bool) :
    (runTrue bits bits.length).length = (bits.takeWhile id).length := by
  rw [runTrue_length (bitOf_before_takeWhile bits) (bitOf_at_takeWhile bits)]
  exact Nat.min_eq_right (List.takeWhile_sublist id).length_le

end Complexity
