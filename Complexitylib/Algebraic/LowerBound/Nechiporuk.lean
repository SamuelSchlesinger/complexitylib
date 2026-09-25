/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Nechiporuk.Subfunctions
public import Cslib.Foundations.Data.Nat.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Nechiporuk's formula lower bound for rectangle-free functions

Nechiporuk's method bounds the leaf size of a formula from below by the
number of distinct subfunctions on the blocks of a partition of the inputs.
A rectangle-free function with many accepting inputs has nearly the maximal
number of subfunctions on every block whose size exceeds `log₂ (8 K)`
(`Nechiporuk.two_pow_card_compl_le`), while a formula with `l` leaves in a
block has at most `2 · 16 ^ l` subfunctions there
(`Nechiporuk.card_subfunctions_le`). Summing over `n / b` disjoint blocks of
size `b` gives leaf size `Ω(n² / b)`; with a polynomial threshold `K ≤ n ^ c`
the blocks have logarithmic size, and every formula over the full binary basis
computing the function has `Ω(n² / log n)` leaves.

The main statements are `sum_le_of_computes` for an arbitrary family of
disjoint blocks, `leaves_lower_bound` for consecutive blocks of a given size,
and the asymptotic `eventually_sq_le_leaves`.
-/

@[expose] public section

namespace Algebraic
namespace Nechiporuk

open scoped Classical
open Binary Cutwidth Filter

variable {n : Nat}

/-- On a block of size at least `log₂ (8 K)`, a formula computing a rectangle-free
function with many accepting inputs has at least `(n - |Y| - log₂ (16 K)) / 4`
leaves in the block. -/
theorem block_bound {f : Cslib.BooleanFunction n} {K : Nat}
    (hrect : RectangleFree f K) (hacc : 2 ^ (n - 2) ≤ (accepting f).card)
    {Y : Finset (Fin n)} (hY : 8 * K ≤ 2 ^ Y.card)
    (F : Formula n) (hF : F.Computes f) :
    n - Y.card ≤ Nat.log 2 (16 * K) + 4 * F.leavesIn Y := by
  have h1 := two_pow_card_compl_le hrect hacc hY
  have h2 : (subfunctions f Y).card ≤ 2 * 16 ^ F.leavesIn Y := by
    rw [← hF.eval_eq]
    exact card_subfunctions_le Y F
  have hc : Yᶜ.card = n - Y.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  rw [hc] at h1
  have h3 : 2 ^ (n - Y.card) ≤ 16 * K * 2 ^ (4 * F.leavesIn Y) := by
    calc 2 ^ (n - Y.card) ≤ 8 * K * (subfunctions f Y).card := h1
      _ ≤ 8 * K * (2 * 16 ^ F.leavesIn Y) := Nat.mul_le_mul_left _ h2
      _ = 16 * K * 2 ^ (4 * F.leavesIn Y) := by
          rw [pow_mul, show (2 : Nat) ^ 4 = 16 by norm_num]
          ring
  by_cases hle : n - Y.card ≤ 4 * F.leavesIn Y
  · omega
  · have hsplit : 2 ^ (n - Y.card) =
        2 ^ (n - Y.card - 4 * F.leavesIn Y) * 2 ^ (4 * F.leavesIn Y) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit] at h3
    have h4 : 2 ^ (n - Y.card - 4 * F.leavesIn Y) ≤ 16 * K :=
      Nat.le_of_mul_le_mul_right h3 (Nat.two_pow_pos _)
    have := Nat.le_log_of_pow_le one_lt_two h4
    omega

/-- **Nechiporuk's bound for rectangle-free functions.** Over `k` pairwise disjoint
blocks, each of size at least `log₂ (8 K)`, every formula computing a
`K`-rectangle-free function with at least `2 ^ (n - 2)` accepting inputs has
leaf size at least `(Σ_i (n - |Y_i|) - k · log₂ (16 K)) / 4`. -/
theorem sum_le_of_computes {f : Cslib.BooleanFunction n} {K : Nat}
    (hrect : RectangleFree f K) (hacc : 2 ^ (n - 2) ≤ (accepting f).card)
    {k : Nat} (Y : Fin k → Finset (Fin n))
    (disjoint : Pairwise fun i j => Disjoint (Y i) (Y j))
    (hY : ∀ i, 8 * K ≤ 2 ^ (Y i).card)
    (F : Formula n) (hF : F.Computes f) :
    ∑ i, (n - (Y i).card) ≤ k * Nat.log 2 (16 * K) + 4 * F.leaves := by
  calc ∑ i, (n - (Y i).card)
      ≤ ∑ i, (Nat.log 2 (16 * K) + 4 * F.leavesIn (Y i)) :=
        Finset.sum_le_sum fun i _ => block_bound hrect hacc (hY i) F hF
    _ = k * Nat.log 2 (16 * K) + 4 * ∑ i, F.leavesIn (Y i) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, Finset.mul_sum]
    _ ≤ k * Nat.log 2 (16 * K) + 4 * F.leaves := by
        have := Formula.sum_leavesIn_le_leaves Y disjoint F
        omega

/-! ### Consecutive blocks of a fixed size -/

/-- The `i`-th block of `b` consecutive coordinates, for `i < n / b`. -/
def block (n b : Nat) (i : Fin (n / b)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin b)).image fun j => ⟨b * i.val + j.val, by
    have h₁ := Nat.mul_div_le n b
    have h₂ := i.isLt
    have h₃ := j.isLt
    calc b * i.val + j.val < b * (i.val + 1) := by rw [Nat.mul_succ]; omega
      _ ≤ b * (n / b) := Nat.mul_le_mul_left _ h₂
      _ ≤ n := h₁⟩

theorem card_block {b : Nat} (i : Fin (n / b)) : (block n b i).card = b := by
  unfold block
  rw [Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fin]
  intro j j' h
  have := congrArg Fin.val h
  simp only at this
  exact Fin.ext (by omega)

theorem block_disjoint {b : Nat} (hb : 0 < b) :
    Pairwise fun i j : Fin (n / b) => Disjoint (block n b i) (block n b j) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨a', _, h⟩ := Finset.mem_image.mp hx'
  have hval := congrArg Fin.val h
  simp only at hval
  have e₁ : (b * i.val + a.val) / b = i.val := by
    rw [Nat.mul_add_div hb, Nat.div_eq_of_lt a.isLt, Nat.add_zero]
  have e₂ : (b * j.val + a'.val) / b = j.val := by
    rw [Nat.mul_add_div hb, Nat.div_eq_of_lt a'.isLt, Nat.add_zero]
  apply hij
  apply Fin.ext
  rw [← e₁, ← e₂, hval]

/-- **Nechiporuk's bound with consecutive blocks of size `b`.** With
`8 K ≤ 2 ^ b`, every formula computing a `K`-rectangle-free function with at
least `2 ^ (n - 2)` accepting inputs satisfies
`(n / b) · (n - b) ≤ (n / b) · log₂ (16 K) + 4 · leaves`. -/
theorem leaves_lower_bound {f : Cslib.BooleanFunction n} {K b : Nat}
    (hrect : RectangleFree f K) (hacc : 2 ^ (n - 2) ≤ (accepting f).card)
    (hb : 0 < b) (hK : 8 * K ≤ 2 ^ b) (F : Formula n) (hF : F.Computes f) :
    (n / b) * (n - b) ≤ (n / b) * Nat.log 2 (16 * K) + 4 * F.leaves := by
  have := sum_le_of_computes hrect hacc (block n b) (block_disjoint hb)
    (fun i => by rw [card_block]; exact hK) F hF
  simpa [card_block, Finset.sum_const, Finset.card_univ] using this

/-- A cleaner consequence: `(n - b) (n - 2 b - 1) ≤ 4 b · leaves`. -/
theorem leaves_lower_bound' {f : Cslib.BooleanFunction n} {K b : Nat}
    (hrect : RectangleFree f K) (hacc : 2 ^ (n - 2) ≤ (accepting f).card)
    (hb : 0 < b) (hK : 8 * K ≤ 2 ^ b) (F : Formula n) (hF : F.Computes f) :
    (n - b) * (n - 2 * b - 1) ≤ 4 * b * F.leaves := by
  have h := leaves_lower_bound hrect hacc hb hK F hF
  have hlog : Nat.log 2 (16 * K) ≤ b + 1 := by
    have : 16 * K ≤ 2 ^ (b + 1) := by rw [pow_succ]; omega
    exact (Nat.log_mono_right this).trans (by rw [Nat.log_pow one_lt_two])
  set q := n / b with hq
  have hqb : n < q * b + b := Nat.lt_div_mul_add hb
  -- q * (n - 2b - 1) ≤ 4 L
  have h₁ : q * (n - 2 * b - 1) ≤ 4 * F.leaves := by
    have h₂ : q * (n - b) ≤ q * (b + 1) + 4 * F.leaves :=
      h.trans (by have := Nat.mul_le_mul_left q hlog; omega)
    rcases Nat.lt_or_ge (n - b) (b + 1) with hsmall | hlarge
    · have : n - 2 * b - 1 = 0 := by omega
      rw [this, Nat.mul_zero]
      exact Nat.zero_le _
    · have : n - b = (n - 2 * b - 1) + (b + 1) := by omega
      rw [this, Nat.mul_add] at h₂
      omega
  calc (n - b) * (n - 2 * b - 1) ≤ (q * b) * (n - 2 * b - 1) :=
        Nat.mul_le_mul_right _ (by omega)
    _ = b * (q * (n - 2 * b - 1)) := by ring
    _ ≤ b * (4 * F.leaves) := Nat.mul_le_mul_left _ h₁
    _ = 4 * b * F.leaves := by ring

/-! ### The asymptotic statement -/

/-- The natural binary logarithm is at most the real one. -/
theorem natLog_le_logb (m : Nat) : (Nat.log 2 m : ℝ) ≤ Real.logb 2 m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h : (2 : ℝ) ^ Nat.log 2 m ≤ m := by exact_mod_cast Nat.pow_log_le_self 2 hm.ne'
    have := (Real.logb_le_logb one_lt_two (by positivity) (by exact_mod_cast hm)).mpr h
    rwa [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at this

/-- **Formula size `Ω(n² / log n)` for rectangle-free families.** For a family
that is `K n`-rectangle-free with `K n ≤ n ^ c` and at least `2 ^ (n - 2)`
accepting inputs, every formula over the full binary basis computing `f n`
has at least `n² / (64 (c + 3) log₂ n)` leaves, for all large `n`. -/
theorem eventually_sq_le_leaves (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) (c : Nat)
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c)
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n)) :
    ∀ᶠ n in atTop, ∀ F : Formula n, F.Computes (f n) →
      (n : ℝ) ^ 2 ≤ 64 * (c + 3) * Real.logb 2 n * F.leaves := by
  have hlog := Nat.eventually_mul_log_le (16 * (c + 3)) one_lt_two
  filter_upwards [hK, hacc, hrect, hlog, eventually_ge_atTop 4] with n hKn haccn hrectn hlogn hn4
  intro F hF
  -- The block size.
  set b := 3 + c * (Nat.log 2 n + 1) with hb
  have hb0 : 0 < b := by omega
  have hlog2 : 2 ≤ Nat.log 2 n := by
    have : 2 ^ 2 ≤ n := by omega
    exact Nat.le_log_of_pow_le one_lt_two this
  have hbK : 8 * K n ≤ 2 ^ b := by
    have hn : n ≤ 2 ^ (Nat.log 2 n + 1) := (Nat.lt_pow_succ_log_self one_lt_two n).le
    calc 8 * K n ≤ 8 * n ^ c := Nat.mul_le_mul_left _ hKn
      _ ≤ 8 * (2 ^ (Nat.log 2 n + 1)) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn c)
      _ = 2 ^ b := by
          rw [hb, ← pow_mul, pow_add, show (8 : Nat) = 2 ^ 3 by norm_num,
            Nat.mul_comm (Nat.log 2 n + 1) c]
  have hble : b ≤ 2 * (c + 3) * Nat.log 2 n := by
    have : c * (Nat.log 2 n + 1) ≤ 2 * c * Nat.log 2 n := by nlinarith
    nlinarith
  have h8b : 8 * b ≤ n := by
    calc 8 * b ≤ 8 * (2 * (c + 3) * Nat.log 2 n) := Nat.mul_le_mul_left _ hble
      _ = 16 * (c + 3) * Nat.log 2 n := by ring
      _ ≤ n := hlogn
  have main := leaves_lower_bound' hrectn haccn hb0 hbK F hF
  -- (n - b)(n - 2b - 1) ≥ 3 n² / 8, so 3 n² ≤ 32 b · leaves.
  have h₁ : 3 * n ≤ 4 * (n - b) := by omega
  have h₂ : n ≤ 2 * (n - 2 * b - 1) := by omega
  have h₃ : 3 * n * n ≤ 32 * b * F.leaves := by
    calc 3 * n * n ≤ 4 * (n - b) * (2 * (n - 2 * b - 1)) := Nat.mul_le_mul h₁ h₂
      _ = 8 * ((n - b) * (n - 2 * b - 1)) := by ring
      _ ≤ 8 * (4 * b * F.leaves) := Nat.mul_le_mul_left _ main
      _ = 32 * b * F.leaves := by ring
  have h₄ : (n : ℝ) ^ 2 ≤ 32 * b * F.leaves := by
    have : ((3 * n * n : Nat) : ℝ) ≤ ((32 * b * F.leaves : Nat) : ℝ) := by exact_mod_cast h₃
    push_cast at this
    nlinarith
  have hbR : (b : ℝ) ≤ 2 * (c + 3) * Nat.log 2 n := by exact_mod_cast hble
  have hlogR := natLog_le_logb n
  have hleaves : (0 : ℝ) ≤ F.leaves := by positivity
  calc (n : ℝ) ^ 2 ≤ 32 * b * F.leaves := h₄
    _ ≤ 32 * (2 * (c + 3) * Nat.log 2 n) * F.leaves := by gcongr
    _ ≤ 32 * (2 * (c + 3) * Real.logb 2 n) * F.leaves := by gcongr
    _ = 64 * (c + 3) * Real.logb 2 n * F.leaves := by ring

end Nechiporuk
end Algebraic
