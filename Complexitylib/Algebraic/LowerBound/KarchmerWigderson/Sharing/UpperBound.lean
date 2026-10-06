/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing

/-!
# A matching upper bound for parity with shared gates

Cut the `n` inputs into `k + 1` blocks of `m = ⌈n / (k + 1)⌉` consecutive bits
(`SharedProgram.blockLength`). Share the parity of the first block and then, for each of the
next `k - 1` blocks, the exclusive or of the last shared value with the block's parity, and
output the exclusive or of the last shared value with the parity of the last block
(`SharedProgram.parityProgram`, built from `SharedProgram.xorChain`). This program has `k`
shared gates and computes parity (`SharedProgram.parityProgram_computes`).

A balanced formula for the parity of `m` consecutive bits (`Formula.parityRange`) has at most
`2 m²` gates (`Formula.gates_parityRange_le`), and each step `z ⊕ φ = (z ∧ ¬φ) ∨ (¬z ∧ φ)`
reads `φ` and its De Morgan dual, so `(k + 1) · gates ≤ 4 (n + k)² + 3 k (k + 1)`
(`SharedProgram.mul_gates_parityProgram_le`), which is at most `19 n²` when `k < n`
(`SharedProgram.exists_parity_mul_gates_le_of_lt`). Together with the lower bound
`n² ≤ (k + 1) · (gates + k + 1)` of `SharedProgram.parity_sq_le_gates`, the minimum number of
gates of a program with `k` shared gates computing parity is `Θ(n² / (k + 1))` whenever
`2 (k + 1)² ≤ n²`.
-/

@[expose] public section

namespace Algebraic
namespace KW

open GateElimination.Xor

namespace Formula

variable {n N : Nat}

@[simp] theorem gates_neg : ∀ F : Formula n, F.neg.gates = F.gates
  | lit _ _ => rfl
  | const _ => rfl
  | and l r => by simp [neg, gates, gates_neg l, gates_neg r]
  | or l r => by simp [neg, gates, gates_neg l, gates_neg r]

@[simp] theorem gates_mapIndex (φ : Fin n → Fin N) :
    ∀ F : Formula n, (F.mapIndex φ).gates = F.gates
  | lit _ _ => rfl
  | const _ => rfl
  | and l r => by simp [mapIndex, gates, gates_mapIndex φ l, gates_mapIndex φ r]
  | or l r => by simp [mapIndex, gates, gates_mapIndex φ l, gates_mapIndex φ r]

@[simp] theorem gates_xor (L R : Formula n) : (L.xor R).gates = 2 * (L.gates + R.gates) + 3 := by
  simp only [xor, gates, gates_neg]
  ring

/-- On `Bool`, exclusive or is the addition used by `parity`. -/
theorem xor_eq_add (a b : Bool) : (a ^^ b) = a + b := rfl

/-- A balanced formula for the parity of the inputs with index in `[a, a + m)`: split the range
in half and combine the halves with `Formula.xor`. Indices outside `Fin n` are skipped. -/
def parityRange : Nat → Nat → Formula n
  | _, 0 => const false
  | a, 1 => if h : a < n then lit ⟨a, h⟩ true else const false
  | a, m + 2 =>
    (parityRange a ((m + 2) / 2)).xor (parityRange (a + (m + 2) / 2) (m + 2 - (m + 2) / 2))
termination_by _ m => m
decreasing_by all_goals omega

theorem eval_parityRange (x : Fin n → Bool) : ∀ a m : Nat,
    (parityRange a m).eval x = ∑ i : Fin n, if a ≤ i.val ∧ i.val < a + m then x i else 0
  | a, 0 => by
    rw [parityRange]
    exact (Finset.sum_eq_zero fun i _ => ite_eq_right (by omega)).symm
  | a, 1 => by
    rw [parityRange]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨a, h⟩
        (fun i _ hi => ite_eq_right fun hc => hi (Fin.ext (show i.val = a by omega)))
        (fun h' => absurd (Finset.mem_univ _) h'), ite_eq_left (by simp)]
      simp
    · exact (Finset.sum_eq_zero fun i _ => ite_eq_right (by omega)).symm
  | a, m + 2 => by
    rw [parityRange, eval_xor, eval_parityRange x a, eval_parityRange x (a + (m + 2) / 2),
      xor_eq_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h₁ : a ≤ i.val ∧ i.val < a + (m + 2) / 2
    · rw [ite_eq_left h₁, ite_eq_right (by omega), ite_eq_left (by omega), add_zero]
    · by_cases h₂ : a + (m + 2) / 2 ≤ i.val ∧ i.val < a + (m + 2) / 2 + (m + 2 - (m + 2) / 2)
      · rw [ite_eq_right h₁, ite_eq_left h₂, ite_eq_left (by omega), zero_add]
      · rw [ite_eq_right h₁, ite_eq_right h₂, ite_eq_right (by omega), add_zero]
termination_by _ m => m
decreasing_by all_goals omega

theorem gates_parityRange_add_two_le : ∀ a m : Nat, 1 ≤ m →
    (parityRange (n := n) a m).gates + 2 ≤ 2 * m ^ 2
  | _, 0, h => absurd h (by omega)
  | a, 1, _ => by
    rw [parityRange]
    split_ifs <;> simp [gates]
  | a, m + 2, _ => by
    rw [parityRange, gates_xor]
    have h₁ := gates_parityRange_add_two_le a ((m + 2) / 2) (by omega)
    have h₂ := gates_parityRange_add_two_le (a + (m + 2) / 2) (m + 2 - (m + 2) / 2) (by omega)
    generalize hh : (m + 2) / 2 = h at h₁ h₂ ⊢
    generalize hh' : m + 2 - h = h' at h₂ ⊢
    have hm : m + 2 = h + h' := by omega
    rw [hm]
    rcases (by omega : h' = h ∨ h' = h + 1) with rfl | rfl <;> nlinarith
termination_by _ m => m
decreasing_by all_goals omega

/-- The balanced parity formula on `m` bits has at most `2 m²` gates. -/
theorem gates_parityRange_le (a m : Nat) : (parityRange (n := n) a m).gates ≤ 2 * m ^ 2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [parityRange, gates]
  · have := gates_parityRange_add_two_le (n := n) a m hm
    omega

end Formula

namespace SharedProgram

/-- The program that shares `acc`, then shares in turn the exclusive or `z ⊕ ψ i` of the last
shared value `z` with each `ψ i` but the last, and outputs `z ⊕ ψ (r - 1)`. It has `r` shared
gates and computes `acc ⊕ ψ 0 ⊕ ⋯ ⊕ ψ (r - 1)`. -/
def xorChain : {N r : Nat} → Formula N → (Fin r → Formula N) → SharedProgram N r
  | _, 0, acc, _ => output acc
  | N, _ + 1, acc, ψ =>
    share acc (xorChain ((Formula.lit (Fin.last N) true).xor ((ψ 0).mapIndex Fin.castSucc))
      fun i => (ψ i.succ).mapIndex Fin.castSucc)

theorem eval_xorChain : ∀ {N r : Nat} (acc : Formula N) (ψ : Fin r → Formula N)
    (x : Fin N → Bool), (xorChain acc ψ).eval x = acc.eval x + ∑ i, (ψ i).eval x
  | _, 0, acc, ψ, x => by simp [xorChain]
  | N, r + 1, acc, ψ, x => by
    rw [xorChain, eval_share, eval_xorChain, Fin.sum_univ_succ]
    simp only [Formula.eval_xor, Formula.eval_lit, Formula.eval_mapIndex, Fin.snoc_last,
      Fin.snoc_comp_castSucc, beq_true]
    change acc.eval x + (ψ 0).eval x + _ = _
    rw [add_assoc]

theorem gates_xorChain : ∀ {N r : Nat} (acc : Formula N) (ψ : Fin r → Formula N),
    (xorChain acc ψ).gates = acc.gates + ∑ i, (2 * (ψ i).gates + 3)
  | _, 0, acc, ψ => by simp [xorChain, gates]
  | N, r + 1, acc, ψ => by
    rw [xorChain, gates, gates_xorChain, Fin.sum_univ_succ]
    simp only [Formula.gates_xor, Formula.gates_mapIndex, Formula.gates]
    ring

/-- The block length `⌈n / (k + 1)⌉`: `k + 1` blocks of this length cover `n` inputs. -/
def blockLength (n k : Nat) : Nat :=
  (n + k) / (k + 1)

theorem le_mul_blockLength (n k : Nat) : n ≤ (k + 1) * blockLength n k := by
  have h₁ := Nat.div_add_mod (n + k) (k + 1)
  have h₂ := Nat.mod_lt (n + k) (by omega : 0 < k + 1)
  unfold blockLength
  omega

theorem mul_blockLength_le (n k : Nat) : (k + 1) * blockLength n k ≤ n + k :=
  Nat.mul_div_le (n + k) (k + 1)

/-- Parity with `k` shared gates: cut the inputs into `k + 1` blocks of `blockLength n k`
consecutive bits and chain the block parities with `xorChain`. -/
def parityProgram (n k : Nat) : SharedProgram n k :=
  xorChain (Formula.parityRange 0 (blockLength n k))
    fun i : Fin k => Formula.parityRange ((i.val + 1) * blockLength n k) (blockLength n k)

theorem parityProgram_computes (n k : Nat) : (parityProgram n k).Computes parity := by
  intro x
  set m := blockLength n k with hm_def
  have hcover := le_mul_blockLength n k
  rw [← hm_def] at hcover
  have hsplit : (parityProgram n k).eval x = ∑ j : Fin (k + 1),
      ∑ i : Fin n, if j.val * m ≤ i.val ∧ i.val < j.val * m + m then x i else 0 := by
    rw [parityProgram, eval_xorChain, Fin.sum_univ_succ]
    simp only [Formula.eval_parityRange, Fin.val_zero, zero_mul, Fin.val_succ, ← hm_def]
  rw [hsplit, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hcover
      exact absurd i.isLt (by omega)
    · exact h
  have hdiv : i.val / m < k + 1 := (Nat.div_lt_iff_lt_mul hmpos).mpr (by
    have := i.isLt
    omega)
  have hlo : i.val / m * m ≤ i.val := Nat.div_mul_le_self _ _
  have hhi : i.val < i.val / m * m + m := by
    have := Nat.lt_div_mul_add (a := i.val) hmpos
    omega
  rw [Finset.sum_eq_single ⟨i.val / m, hdiv⟩]
  · exact ite_eq_left ⟨hlo, hhi⟩
  · intro j _ hj
    refine ite_eq_right fun hc => hj (Fin.ext ?_)
    exact (Nat.div_eq_of_lt_le hc.1 (by rw [Nat.add_mul, one_mul]; exact hc.2)).symm
  · exact fun h => absurd (Finset.mem_univ _) h

theorem mul_gates_parityProgram_le (n k : Nat) :
    (k + 1) * (parityProgram n k).gates ≤ 4 * (n + k) ^ 2 + 3 * k * (k + 1) := by
  rw [parityProgram, gates_xorChain]
  set m := blockLength n k with hm_def
  have h₀ := Formula.gates_parityRange_le (n := n) 0 m
  have hs : ∑ i : Fin k, (2 * (Formula.parityRange (n := n) ((i.val + 1) * m) m).gates + 3) ≤
      ∑ _i : Fin k, (4 * m ^ 2 + 3) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have := Formula.gates_parityRange_le (n := n) ((i.val + 1) * m) m
    omega
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  have hkm : (k + 1) * m ≤ n + k := mul_blockLength_le n k
  have hsq : ((k + 1) * m) ^ 2 ≤ (n + k) ^ 2 := Nat.pow_le_pow_left hkm 2
  nlinarith

/-- **A matching upper bound.** For all `n` and `k` some program with `k` shared gates computes
the parity of `n` bits with `(k + 1) · gates ≤ 4 (n + k)² + 3 k (k + 1)`. -/
theorem exists_parity_mul_gates_le (n k : Nat) :
    ∃ P : SharedProgram n k, P.Computes parity ∧
      (k + 1) * P.gates ≤ 4 * (n + k) ^ 2 + 3 * k * (k + 1) :=
  ⟨parityProgram n k, parityProgram_computes n k, mul_gates_parityProgram_le n k⟩

/-- **A matching upper bound, for `k < n`.** Some program with `k` shared gates computes the
parity of `n` bits with at most `19 n² / (k + 1)` gates. -/
theorem exists_parity_mul_gates_le_of_lt {n k : Nat} (hk : k < n) :
    ∃ P : SharedProgram n k, P.Computes parity ∧ (k + 1) * P.gates ≤ 19 * n ^ 2 := by
  obtain ⟨P, hP, hgates⟩ := exists_parity_mul_gates_le n k
  refine ⟨P, hP, hgates.trans ?_⟩
  nlinarith

end SharedProgram

end KW
end Algebraic
