/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Encoding.FiniteAlphabet.Defs
import Mathlib.Tactic.Linarith

/-!
# Correctness and size of finite-alphabet codes

Delimited unary parsing is exact. Its codeword lengths are bounded by an
alphabet-dependent constant and its palindromic framing commutes with reversal.
-/

@[expose] public section

namespace Complexity.FiniteAlphabetCode

variable {α : Type} (c : FiniteAlphabetCode α)

lemma encode_nil : c.encode [] = [] := rfl

lemma encode_cons (a : α) (w : List α) : c.encode (a :: w) = c.symbol a ++ c.encode w := rfl

lemma symbol_length (a : α) : (c.symbol a).length = (c.index a).val + 2 := by
  simp [symbol, Nat.add_assoc]

lemma decodeFrom_trues (i k : ℕ) (h : i + k < c.size) (rest : List Bool) :
    c.decodeFrom (some i) (List.replicate k true ++ rest) =
      c.decodeFrom (some (i + k)) rest := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append, decodeFrom, ite_eq_left (by omega)]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (i + 1) (by omega)

lemma decodeFrom_symbol (a : α) (rest : List Bool) :
    c.decodeFrom none (c.symbol a ++ rest) =
      (c.decodeFrom none rest).map (a :: ·) := by
  simp only [symbol, List.cons_append, decodeFrom, List.append_assoc]
  rw [decodeFrom_trues c 0 (c.index a).val (by omega)]
  simp [decodeFrom]

lemma decode_encode_proof (w : List α) : c.decode (c.encode w) = some w := by
  change c.decodeFrom none (c.encode w) = some w
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [encode_cons, decodeFrom_symbol, ih]
      rfl

lemma encode_length_lower (w : List α) : w.length ≤ (c.encode w).length := by
  induction w with
  | nil => simp [encode]
  | cons a w ih =>
      rw [encode_cons, List.length_append, symbol_length]
      simp only [List.length_cons]
      omega

lemma encode_length_upper (w : List α) :
    (c.encode w).length ≤ (c.size + 1) * w.length := by
  induction w with
  | nil => simp [encode]
  | cons a w ih =>
      have ha := (c.index a).isLt
      rw [encode_cons, List.length_append, symbol_length]
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

lemma symbol_reverse (a : α) : (c.symbol a).reverse = c.symbol a := by
  simp [symbol, List.reverse_append, List.reverse_replicate]

lemma encode_append (xs ys : List α) : c.encode (xs ++ ys) = c.encode xs ++ c.encode ys := by
  simp [encode]

lemma encode_reverse (w : List α) : c.encode w.reverse = (c.encode w).reverse := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp only [List.reverse_cons, encode_append, encode_cons, encode_nil,
        List.append_nil, ih, List.reverse_append, symbol_reverse]

lemma encode_count_false (w : List α) : (c.encode w).count false = 2 * w.length := by
  induction w with
  | nil => simp [encode]
  | cons a w ih =>
      have hz : (List.replicate (c.index a).val true).count false = 0 :=
        List.count_eq_zero_of_not_mem (by simp)
      rw [encode_cons, List.count_append, ih]
      simp [symbol, List.count_append, hz, Nat.mul_add, Nat.add_comm]

/-- Prefix already consumed when the parser is inside a codeword. -/
def pendingPrefix : Option ℕ → List Bool
  | none => []
  | some i => false :: List.replicate i true

lemma decodeFrom_exact (bits : List Bool) (pending : Option ℕ) (w : List α)
    (h : c.decodeFrom pending bits = some w) :
    pendingPrefix pending ++ bits = c.encode w := by
  induction bits generalizing pending w with
  | nil =>
      cases pending with
      | none => simp only [decodeFrom, Option.some.injEq] at h; subst w; rfl
      | some i => simp [decodeFrom] at h
  | cons b bits ih =>
      cases pending with
      | none =>
          cases b with
          | true => simp [decodeFrom] at h
          | false => simpa [pendingPrefix] using ih (some 0) w h
      | some i =>
          cases b with
          | true =>
              simp only [decodeFrom] at h
              split_ifs at h with hi
              · simpa [pendingPrefix, List.replicate_add, List.append_assoc] using
                  ih (some (i + 1)) w h
          | false =>
              simp only [decodeFrom] at h
              split_ifs at h with hi
              · cases hr : c.decodeFrom none bits with
                | none => simp [hr] at h
                | some rest =>
                    simp only [hr, Option.map_some, Option.some.injEq] at h
                    subst w
                    have he := ih none rest hr
                    simpa [pendingPrefix, encode, symbol, List.append_assoc] using
                      congrArg (fun bs => (false :: List.replicate i true) ++ false :: bs) he

lemma encode_decode_proof {bits : List Bool} {w : List α}
    (h : c.decode bits = some w) : c.encode w = bits :=
  (decodeFrom_exact c bits none w h).symm

lemma decode_reverse (bits : List Bool) :
    c.decode bits.reverse = (c.decode bits).map List.reverse := by
  cases hw : c.decode bits with
  | some w =>
      rw [← encode_decode_proof c hw, ← encode_reverse, decode_encode_proof]
      rfl
  | none =>
      cases hr : c.decode bits.reverse with
      | none => rfl
      | some w =>
          have he : c.encode w.reverse = bits := by
            rw [encode_reverse, encode_decode_proof c hr, List.reverse_reverse]
          have hc := decode_encode_proof c w.reverse
          rw [he, hw] at hc
          contradiction

end Complexity.FiniteAlphabetCode
