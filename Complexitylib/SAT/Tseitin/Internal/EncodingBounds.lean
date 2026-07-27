/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.Encoding
public import Complexitylib.SAT.Tseitin.Defs
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Encoding-size support for Tseitin splitting

These internal lemmas relate syntactic clause/literal counts to the existing
unary-variable SAT bit encoding and bound exact-3 formulas whose variable
indices share a common upper bound.
-/

@[expose] public section

namespace Complexity

namespace SAT

/-- A clause has no more literal occurrences than bits in its encoding. -/
theorem Clause.length_le_encode_length_internal (c : Clause) :
    c.length ≤ c.encode.length := by
  induction c with
  | nil => rfl
  | cons ℓ ls ih =>
      rw [Clause.encode_cons]
      simp only [List.length_cons, List.length_append, doubleBits_length,
        Lit.encodeRaw_length, List.length_nil]
      omega

/-- A CNF has no more clauses than bits in its encoding. -/
theorem CNF.length_le_encode_length_internal (φ : CNF) :
    φ.length ≤ φ.encode.length := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
      rw [CNF.encode_cons]
      simp only [List.length_cons, List.length_append, List.length_nil]
      omega

/-- The total number of literal occurrences is bounded by encoded length. -/
theorem CNF.literalCount_le_encode_length_internal (φ : CNF) :
    φ.literalCount ≤ φ.encode.length := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
      change c.length + CNF.literalCount cs ≤ (CNF.encode (c :: cs)).length
      rw [CNF.encode_cons]
      simp only [List.length_append, List.length_cons, List.length_nil]
      have hc := Clause.length_le_encode_length_internal c
      omega

/-- A three-literal clause whose variables are at most `B` uses at most
`6 * B + 12` bits in the unary-variable encoding. -/
theorem Clause.encode_length_le_of_length_eq_three_internal
    {c : Clause} {B : ℕ} (hlen : c.length = 3)
    (hvar : ∀ ℓ ∈ c, ℓ.var ≤ B) :
    c.encode.length ≤ 6 * B + 12 := by
  match c with
  | [a, b, d] =>
      simp only [Clause.encode_cons, Clause.encode_nil, List.length_append,
        List.length_cons, List.length_nil, doubleBits_length,
        Lit.encodeRaw_length]
      have ha := hvar a (by simp)
      have hb := hvar b (by simp)
      have hd := hvar d (by simp)
      omega
  | [] => simp at hlen
  | [_] => simp at hlen
  | [_, _] => simp at hlen
  | _ :: _ :: _ :: _ :: _ => simp at hlen

/-- An exact-3 CNF with `M` clauses and variables at most `B` has encoded
length at most `M * (6 * B + 14)`, including clause separators. -/
theorem CNF.encode_length_le_of_is3CNF_internal {φ : CNF} {B : ℕ}
    (h3 : φ.Is3CNF)
    (hvar : ∀ c ∈ φ, ∀ ℓ ∈ c, ℓ.var ≤ B) :
    φ.encode.length ≤ φ.length * (6 * B + 14) := by
  induction φ with
  | nil => simp [CNF.encode]
  | cons c cs ih =>
      have hc3 : c.length = 3 := h3 c List.mem_cons_self
      have hcs3 : CNF.Is3CNF cs := by
        intro d hd
        exact h3 d (List.mem_cons_of_mem c hd)
      have hc := Clause.encode_length_le_of_length_eq_three_internal hc3
        (fun ℓ hℓ => hvar c List.mem_cons_self ℓ hℓ)
      have htail := ih hcs3 (fun d hd ℓ hℓ =>
        hvar d (List.mem_cons_of_mem c hd) ℓ hℓ)
      rw [CNF.encode_cons]
      simp only [List.length_append, List.length_cons, List.length_nil]
      calc
        c.encode.length + 2 + (CNF.encode cs).length ≤
            (6 * B + 14) + cs.length * (6 * B + 14) := by omega
        _ = (c :: cs).length * (6 * B + 14) := by
          simp [Nat.succ_mul, Nat.add_comm]

end SAT

end Complexity
