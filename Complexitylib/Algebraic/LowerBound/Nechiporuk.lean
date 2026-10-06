/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Nechiporuk.Sharing
public import Complexitylib.Algebraic.LowerBound.Nechiporuk.Subfunctions
public import Cslib.Foundations.Data.Nat.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Nechiporuk's formula and bounded-sharing circuit lower bounds for rectangle-free functions

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

The main formula statements are `sum_le_of_computes` for an arbitrary family of
disjoint blocks, `leaves_lower_bound` for consecutive blocks of a given size,
and the asymptotic `eventually_sq_le_leaves`.

Because a rectangle-free function has `2 ^ (n - |Y|) / (8 K)` subfunctions on
each block `Y`, its binary logarithm is `Θ(n)` per block. Decomposing a
full-binary-basis circuit `c : Circuit Binary.signature n 1` at its shared
gates (`exists_sharedProgram_of_circuit`) yields both:
- **Global bounded-sharing lower bounds** (`sum_le_size_of_computes`,
  `size_lower_bound`, `size_lower_bound'`, `eventually_sq_le_size`,
  `isLittleO_size_of_rectangleFree`) when total shared fan-out
  `sharedFanOut c` is sublinear in `n`.
- **Active-block bounded-sharing lower bounds** (`SharedProgram.block_bound_active`,
  `SharedProgram.sum_le_of_computes_active`, `sum_le_size_of_computes_active`,
  `size_lower_bound_active`, `size_lower_bound_active'`,
  `eventually_sq_le_size_active`, `eventually_sq_le_size_of_gateBlockSpan_le`,
  `isLittleO_size_of_rectangleFree_active`), where a shared gate only
  contributes on blocks `Y` that intersect its syntactic input cone
  (`activeSharedGateCount c Y`, `activeSharedFanOut c Y`). Because summing
  `activeSharedFanOut c (Y i)` over blocks weights each shared gate by its
  `gateBlockSpan` rather than the total number of blocks (`sum_activeSharedFanOut`),
  circuits whose shared gates have bounded block-span admit **superlinear**
  total shared fan-out up to `o(n² / log n)` while still requiring
  `Ω(n² / log n)` gates.
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

/-! ### Programs and circuits with shared gates -/

/-- **Active-block Nechiporuk bound for programs with shared gates.** On a block `Y` of size at
least `log₂ (8 K)`, a program `P` computing a `K`-rectangle-free function with at least
`2 ^ (n - 2)` accepting inputs satisfies
`n - |Y| ≤ log₂ (16 K) + P.activeShared Y + 4 · P.activeSharedLeaves Y + 4 · P.inputLeavesIn Y`. -/
theorem SharedProgram.block_bound_active {f : Cslib.BooleanFunction n} {K k : Nat}
    (hrect : RectangleFree f K) (hacc : 2 ^ (n - 2) ≤ (accepting f).card)
    {Y : Finset (Fin n)} (hY : 8 * K ≤ 2 ^ Y.card)
    (P : SharedProgram n k) (hP : P.Computes f) :
    n - Y.card ≤
      Nat.log 2 (16 * K) + P.activeShared Y + 4 * P.activeSharedLeaves Y +
        4 * P.inputLeavesIn Y := by
  have h1 := two_pow_card_compl_le hrect hacc hY
  have h2 : (subfunctions f Y).card ≤
      2 ^ (P.activeShared Y + 1) * 16 ^ (P.inputLeavesIn Y + P.activeSharedLeaves Y) := by
    rw [← hP.eval_eq]
    exact P.card_subfunctions_le_activeSharedLeaves Y
  have hc : Yᶜ.card = n - Y.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  rw [hc] at h1
  set E := P.activeShared Y + 4 * P.activeSharedLeaves Y + 4 * P.inputLeavesIn Y
  have h3 : 2 ^ (n - Y.card) ≤ 16 * K * 2 ^ E := by
    calc 2 ^ (n - Y.card) ≤ 8 * K * (subfunctions f Y).card := h1
      _ ≤ 8 * K *
            (2 ^ (P.activeShared Y + 1) * 16 ^ (P.inputLeavesIn Y + P.activeSharedLeaves Y)) :=
          Nat.mul_le_mul_left _ h2
      _ = 16 * K * 2 ^ E := by
          have h16 : (16 : Nat) ^ (P.inputLeavesIn Y + P.activeSharedLeaves Y) =
              2 ^ (4 * P.activeSharedLeaves Y + 4 * P.inputLeavesIn Y) := by
            rw [show (16 : Nat) = 2 ^ 4 by norm_num, ← pow_mul]
            congr 1
            ring
          have hpow :
              2 ^ P.activeShared Y * 2 ^ (4 * P.activeSharedLeaves Y + 4 * P.inputLeavesIn Y) =
                2 ^ E := by
            rw [← pow_add, ← add_assoc]
          rw [h16, pow_succ]
          calc 8 * K * (2 ^ P.activeShared Y * 2 *
                2 ^ (4 * P.activeSharedLeaves Y + 4 * P.inputLeavesIn Y))
              = 16 * K * (2 ^ P.activeShared Y *
                  2 ^ (4 * P.activeSharedLeaves Y + 4 * P.inputLeavesIn Y)) := by ring
            _ = 16 * K * 2 ^ E := by rw [hpow]
  by_cases hle : n - Y.card ≤ E
  · omega
  · have hsplit : 2 ^ (n - Y.card) = 2 ^ (n - Y.card - E) * 2 ^ E := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit] at h3
    have h4 : 2 ^ (n - Y.card - E) ≤ 16 * K :=
      Nat.le_of_mul_le_mul_right h3 (Nat.two_pow_pos _)
    have := Nat.le_log_of_pow_le one_lt_two h4
    omega

/-- On a block of size at least `log₂ (8 K)`, a program with `k` shared gates computing a
`K`-rectangle-free function with at least `2 ^ (n - 2)` accepting inputs satisfies
`n - |Y| ≤ log₂ (16 K) + k + 4 · sharedLeaves + 4 · inputLeavesIn Y`. -/
theorem SharedProgram.block_bound {f : Cslib.BooleanFunction n} {K k : Nat}
    (hrect : RectangleFree f K) (hacc : 2 ^ (n - 2) ≤ (accepting f).card)
    {Y : Finset (Fin n)} (hY : 8 * K ≤ 2 ^ Y.card)
    (P : SharedProgram n k) (hP : P.Computes f) :
    n - Y.card ≤ Nat.log 2 (16 * K) + k + 4 * P.sharedLeaves n + 4 * P.inputLeavesIn Y := by
  have hact := P.block_bound_active hrect hacc hY hP
  have hk := P.activeShared_le Y
  have hs := P.activeSharedLeaves_le_sharedLeaves Y
  omega

/-- **Active-block Nechiporuk sum bound for programs with shared gates.** Over `m` pairwise
disjoint blocks of size at least `log₂ (8 K)`, every program `P` computing a `K`-rectangle-free
function with at least `2 ^ (n - 2)` accepting inputs satisfies
`∑ i, (n - |Y i|) ≤ m · log₂ (16 K) + ∑ i, (P.activeShared (Y i) + 4 · P.activeSharedLeaves (Y i))
  + 4 · P.inputLeaves n`. -/
theorem SharedProgram.sum_le_of_computes_active {f : Cslib.BooleanFunction n} {K m k : Nat}
    (hrect : RectangleFree f K) (hacc : 2 ^ (n - 2) ≤ (accepting f).card)
    (Y : Fin m → Finset (Fin n))
    (disjoint : Pairwise fun i j => Disjoint (Y i) (Y j))
    (hY : ∀ i, 8 * K ≤ 2 ^ (Y i).card)
    (P : SharedProgram n k) (hP : P.Computes f) :
    ∑ i, (n - (Y i).card) ≤
      m * Nat.log 2 (16 * K) +
        (∑ i, (P.activeShared (Y i) + 4 * P.activeSharedLeaves (Y i))) +
        4 * P.inputLeaves n := by
  calc ∑ i, (n - (Y i).card)
      ≤ ∑ i, (Nat.log 2 (16 * K) + (P.activeShared (Y i) + 4 * P.activeSharedLeaves (Y i)) +
          4 * P.inputLeavesIn (Y i)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := P.block_bound_active hrect hacc (hY i) hP
        omega
    _ = m * Nat.log 2 (16 * K) +
          (∑ i, (P.activeShared (Y i) + 4 * P.activeSharedLeaves (Y i))) +
          4 * ∑ i, P.inputLeavesIn (Y i) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul, Finset.mul_sum]
    _ ≤ m * Nat.log 2 (16 * K) +
          (∑ i, (P.activeShared (Y i) + 4 * P.activeSharedLeaves (Y i))) +
          4 * P.inputLeaves n := by
        have := P.sum_inputLeavesIn_le_inputLeaves Y disjoint
        omega

/-- **Nechiporuk's bound for programs with shared gates.** Over `m` pairwise disjoint blocks,
each of size at least `log₂ (8 K)`, every program with `k` shared gates computing a
`K`-rectangle-free function with at least `2 ^ (n - 2)` accepting inputs satisfies
`∑ i, (n - |Y i|) ≤ m · (log₂ (16 K) + k + 4 · sharedLeaves) + 4 · inputLeaves`. -/
theorem SharedProgram.sum_le_of_computes {f : Cslib.BooleanFunction n} {K m k : Nat}
    (hrect : RectangleFree f K) (hacc : 2 ^ (n - 2) ≤ (accepting f).card)
    (Y : Fin m → Finset (Fin n))
    (disjoint : Pairwise fun i j => Disjoint (Y i) (Y j))
    (hY : ∀ i, 8 * K ≤ 2 ^ (Y i).card)
    (P : SharedProgram n k) (hP : P.Computes f) :
    ∑ i, (n - (Y i).card) ≤
      m * (Nat.log 2 (16 * K) + k + 4 * P.sharedLeaves n) + 4 * P.inputLeaves n := by
  calc ∑ i, (n - (Y i).card)
      ≤ ∑ i, (Nat.log 2 (16 * K) + k + 4 * P.sharedLeaves n + 4 * P.inputLeavesIn (Y i)) :=
        Finset.sum_le_sum fun i _ => P.block_bound hrect hacc (hY i) hP
    _ = m * (Nat.log 2 (16 * K) + k + 4 * P.sharedLeaves n) + 4 * ∑ i, P.inputLeavesIn (Y i) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, Finset.mul_sum]
    _ ≤ m * (Nat.log 2 (16 * K) + k + 4 * P.sharedLeaves n) + 4 * P.inputLeaves n := by
        have := P.sum_inputLeavesIn_le_inputLeaves Y disjoint
        omega

/-- **Active-block Nechiporuk bound for full-binary-basis circuits.** Over `m` pairwise disjoint
blocks of size at least `log₂ (8 K)`, every single-output circuit `c` over `Binary.signature`
computing a `K`-rectangle-free function with at least `2 ^ (n - 2)` accepting inputs satisfies
`∑ i, (n - |Y i|) ≤ m · log₂ (16 K) + ∑ i, (activeSharedGateCount c (Y i) +
  4 · activeSharedFanOut c (Y i)) + 4 · (c.size + KW.sharedGateCount c + 1)`. -/
theorem sum_le_size_of_computes_active {f : Cslib.BooleanFunction n} {K m : Nat}
    (hrect : RectangleFree f K) (hacc : 2 ^ (n - 2) ≤ (accepting f).card)
    (Y : Fin m → Finset (Fin n))
    (disjoint : Pairwise fun i j => Disjoint (Y i) (Y j))
    (hY : ∀ i, 8 * K ≤ 2 ^ (Y i).card)
    (c : Circuit Binary.signature n 1)
    (hc : c.ComputesWith Binary.interpretation fun x _ => f x) :
    ∑ i, (n - (Y i).card) ≤
      m * Nat.log 2 (16 * K) +
        (∑ i, (activeSharedGateCount c (Y i) + 4 * activeSharedFanOut c (Y i))) +
        4 * (c.size + KW.sharedGateCount c + 1) := by
  obtain ⟨k', P, hk', hP, hgates, _, hact⟩ := exists_sharedProgram_of_circuit c hc
  have hsum := P.sum_le_of_computes_active hrect hacc Y disjoint hY hP
  have hin : P.inputLeaves n ≤ c.size + KW.sharedGateCount c + 1 := by
    have := P.inputLeaves_le_gates n
    omega
  have hact_sum : (∑ i, (P.activeShared (Y i) + 4 * P.activeSharedLeaves (Y i))) ≤
      ∑ i, (activeSharedGateCount c (Y i) + 4 * activeSharedFanOut c (Y i)) := by
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨h1, h2⟩ := hact (Y i)
    omega
  omega

/-- **Nechiporuk's bound for full-binary-basis circuits with bounded sharing.** Over `m`
pairwise disjoint blocks, each of size at least `log₂ (8 K)`, every single-output circuit `c`
over `Binary.signature` computing a `K`-rectangle-free function with at least `2 ^ (n - 2)`
accepting inputs and with `KW.sharedGateCount c ≤ k` and `sharedFanOut c ≤ s` satisfies
`∑ i, (n - |Y i|) ≤ m · (log₂ (16 K) + k + 4 s) + 4 · (c.size + k + 1)`. -/
theorem sum_le_size_of_computes {f : Cslib.BooleanFunction n} {K m k s : Nat}
    (hrect : RectangleFree f K) (hacc : 2 ^ (n - 2) ≤ (accepting f).card)
    (Y : Fin m → Finset (Fin n))
    (disjoint : Pairwise fun i j => Disjoint (Y i) (Y j))
    (hY : ∀ i, 8 * K ≤ 2 ^ (Y i).card)
    (c : Circuit Binary.signature n 1)
    (hc : c.ComputesWith Binary.interpretation fun x _ => f x)
    (hk : KW.sharedGateCount c ≤ k) (hs : sharedFanOut c ≤ s) :
    ∑ i, (n - (Y i).card) ≤
      m * (Nat.log 2 (16 * K) + k + 4 * s) + 4 * (c.size + k + 1) := by
  obtain ⟨k', P, hk', hP, hgates, hshared, _⟩ := exists_sharedProgram_of_circuit c hc
  have hsum := P.sum_le_of_computes hrect hacc Y disjoint hY hP
  have hin : P.inputLeaves n ≤ c.size + k + 1 := by
    have := P.inputLeaves_le_gates n
    omega
  have hm : m * (Nat.log 2 (16 * K) + k' + 4 * P.sharedLeaves n) ≤
      m * (Nat.log 2 (16 * K) + k + 4 * s) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- **Active-block Nechiporuk circuit bound with consecutive blocks of size `b`.** With
`8 K ≤ 2 ^ b`, every single-output circuit `c` over `Binary.signature` computing a
`K`-rectangle-free function with at least `2 ^ (n - 2)` accepting inputs satisfies
`(n / b) · (n - b) ≤ (n / b) · log₂ (16 K) +
  ∑ i, (activeSharedGateCount c (block n b i) + 4 · activeSharedFanOut c (block n b i)) +
  4 · (c.size + KW.sharedGateCount c + 1)`. -/
theorem size_lower_bound_active {f : Cslib.BooleanFunction n} {K b : Nat}
    (hrect : RectangleFree f K) (hacc : 2 ^ (n - 2) ≤ (accepting f).card)
    (hb : 0 < b) (hK : 8 * K ≤ 2 ^ b)
    (c : Circuit Binary.signature n 1)
    (hc : c.ComputesWith Binary.interpretation fun x _ => f x) :
    (n / b) * (n - b) ≤
      (n / b) * Nat.log 2 (16 * K) +
        (∑ i, (activeSharedGateCount c (block n b i) +
          4 * activeSharedFanOut c (block n b i))) +
        4 * (c.size + KW.sharedGateCount c + 1) := by
  have := sum_le_size_of_computes_active hrect hacc (block n b) (block_disjoint hb)
    (fun i => by rw [card_block]; exact hK) c hc
  simpa [card_block, Finset.sum_const, Finset.card_univ] using this

/-- A multiplicative consequence of `size_lower_bound_active`:
`(n - b) · (n - 2 b - 1) ≤ 5 b · (∑ i, activeSharedFanOut c (block n b i)) +
  4 b · (c.size + KW.sharedGateCount c + 1)`. -/
theorem size_lower_bound_active' {f : Cslib.BooleanFunction n} {K b : Nat}
    (hrect : RectangleFree f K) (hacc : 2 ^ (n - 2) ≤ (accepting f).card)
    (hb : 0 < b) (hK : 8 * K ≤ 2 ^ b)
    (c : Circuit Binary.signature n 1)
    (hc : c.ComputesWith Binary.interpretation fun x _ => f x) :
    (n - b) * (n - 2 * b - 1) ≤
      5 * b * (∑ i, activeSharedFanOut c (block n b i)) +
        4 * b * (c.size + KW.sharedGateCount c + 1) := by
  have h := size_lower_bound_active hrect hacc hb hK c hc
  have hlog : Nat.log 2 (16 * K) ≤ b + 1 := by
    have : 16 * K ≤ 2 ^ (b + 1) := by rw [pow_succ]; omega
    exact (Nat.log_mono_right this).trans (by rw [Nat.log_pow one_lt_two])
  have hact : (∑ i, (activeSharedGateCount c (block n b i) +
      4 * activeSharedFanOut c (block n b i))) ≤
        5 * ∑ i, activeSharedFanOut c (block n b i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := activeSharedGateCount_le_activeSharedFanOut c (block n b i)
    omega
  have hqb : n < (n / b) * b + b := Nat.lt_div_mul_add hb
  have h₁ : (n / b) * (n - 2 * b - 1) ≤
      5 * (∑ i, activeSharedFanOut c (block n b i)) +
        4 * (c.size + KW.sharedGateCount c + 1) := by
    have h₂ : (n / b) * (n - b) ≤
        (n / b) * (b + 1) + 5 * (∑ i, activeSharedFanOut c (block n b i)) +
          4 * (c.size + KW.sharedGateCount c + 1) := by
      have := Nat.mul_le_mul_left (n / b) hlog
      omega
    rcases Nat.lt_or_ge (n - b) (b + 1) with hsmall | hlarge
    · have : n - 2 * b - 1 = 0 := by omega
      rw [this, Nat.mul_zero]
      exact Nat.zero_le _
    · have : n - b = (n - 2 * b - 1) + (b + 1) := by omega
      rw [this, Nat.mul_add] at h₂
      omega
  calc (n - b) * (n - 2 * b - 1)
      ≤ ((n / b) * b) * (n - 2 * b - 1) := Nat.mul_le_mul_right _ (by omega)
    _ = b * ((n / b) * (n - 2 * b - 1)) := by ring
    _ ≤ b * (5 * (∑ i, activeSharedFanOut c (block n b i)) +
          4 * (c.size + KW.sharedGateCount c + 1)) := Nat.mul_le_mul_left _ h₁
    _ = 5 * b * (∑ i, activeSharedFanOut c (block n b i)) +
          4 * b * (c.size + KW.sharedGateCount c + 1) := by ring

/-- **Nechiporuk's circuit bound with consecutive blocks of size `b`.** With `8 K ≤ 2 ^ b`,
every single-output circuit `c` over `Binary.signature` computing a `K`-rectangle-free function
with at least `2 ^ (n - 2)` accepting inputs and with `KW.sharedGateCount c ≤ k` and
`sharedFanOut c ≤ s` satisfies
`(n / b) · (n - b) ≤ (n / b) · (log₂ (16 K) + k + 4 s) + 4 · (c.size + k + 1)`. -/
theorem size_lower_bound {f : Cslib.BooleanFunction n} {K b k s : Nat}
    (hrect : RectangleFree f K) (hacc : 2 ^ (n - 2) ≤ (accepting f).card)
    (hb : 0 < b) (hK : 8 * K ≤ 2 ^ b)
    (c : Circuit Binary.signature n 1)
    (hc : c.ComputesWith Binary.interpretation fun x _ => f x)
    (hk : KW.sharedGateCount c ≤ k) (hs : sharedFanOut c ≤ s) :
    (n / b) * (n - b) ≤
      (n / b) * (Nat.log 2 (16 * K) + k + 4 * s) + 4 * (c.size + k + 1) := by
  have := sum_le_size_of_computes hrect hacc (block n b) (block_disjoint hb)
    (fun i => by rw [card_block]; exact hK) c hc hk hs
  simpa [card_block, Finset.sum_const, Finset.card_univ] using this

/-- A multiplicative consequence of `size_lower_bound`:
`(n - b) · (n - 2 b - 1 - k - 4 s) ≤ 4 b · (c.size + k + 1)`. -/
theorem size_lower_bound' {f : Cslib.BooleanFunction n} {K b k s : Nat}
    (hrect : RectangleFree f K) (hacc : 2 ^ (n - 2) ≤ (accepting f).card)
    (hb : 0 < b) (hK : 8 * K ≤ 2 ^ b)
    (c : Circuit Binary.signature n 1)
    (hc : c.ComputesWith Binary.interpretation fun x _ => f x)
    (hk : KW.sharedGateCount c ≤ k) (hs : sharedFanOut c ≤ s) :
    (n - b) * (n - 2 * b - 1 - k - 4 * s) ≤ 4 * b * (c.size + k + 1) := by
  have h := size_lower_bound hrect hacc hb hK c hc hk hs
  have hlog : Nat.log 2 (16 * K) ≤ b + 1 := by
    have : 16 * K ≤ 2 ^ (b + 1) := by rw [pow_succ]; omega
    exact (Nat.log_mono_right this).trans (by rw [Nat.log_pow one_lt_two])
  set q := n / b
  have hqb : n < q * b + b := Nat.lt_div_mul_add hb
  have h₁ : q * (n - 2 * b - 1 - k - 4 * s) ≤ 4 * (c.size + k + 1) := by
    have h₂ : q * (n - b) ≤ q * (b + 1 + k + 4 * s) + 4 * (c.size + k + 1) := by
      have := Nat.mul_le_mul_left q
        (show Nat.log 2 (16 * K) + k + 4 * s ≤ b + 1 + k + 4 * s by omega)
      omega
    rcases Nat.lt_or_ge (n - b) (b + 1 + k + 4 * s) with hsmall | hlarge
    · have : n - 2 * b - 1 - k - 4 * s = 0 := by omega
      rw [this, Nat.mul_zero]
      exact Nat.zero_le _
    · have : n - b = (n - 2 * b - 1 - k - 4 * s) + (b + 1 + k + 4 * s) := by omega
      rw [this, Nat.mul_add] at h₂
      omega
  calc (n - b) * (n - 2 * b - 1 - k - 4 * s)
      ≤ (q * b) * (n - 2 * b - 1 - k - 4 * s) := Nat.mul_le_mul_right _ (by omega)
    _ = b * (q * (n - 2 * b - 1 - k - 4 * s)) := by ring
    _ ≤ b * (4 * (c.size + k + 1)) := Nat.mul_le_mul_left _ h₁
    _ = 4 * b * (c.size + k + 1) := by ring

/-- The logarithmic block size `3 + c * (Nat.log 2 n + 1)` used in Nechiporuk's asymptotic lower
bounds for `K n`-rectangle-free functions with `K n ≤ n ^ c`. -/
def nechiporukBlockSize (c n : Nat) : Nat :=
  3 + c * (Nat.log 2 n + 1)

/-- **Active-block `Ω(n² / log n)` circuit lower bound for rectangle-free families.**
For a family that is `K n`-rectangle-free with `K n ≤ n ^ c` and at least `2 ^ (n - 2)`
accepting inputs, every full-binary-basis circuit `cir` computing `f n` whose active shared
fan-out summed across the `n / b` logarithmic blocks (`b = nechiporukBlockSize c n`) satisfies
`20 b · (∑ i, activeSharedFanOut cir (block n b i)) ≤ n²` (an `O(n² / log n)` total active
shared fan-out budget) obeys `n² ≤ 64 (c + 3) log₂ n · (2 · cir.size + 1)` for all large `n`. -/
theorem eventually_sq_le_size_active (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) (c : Nat)
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c)
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n)) :
    ∀ᶠ n in atTop, ∀ cir : Circuit Binary.signature n 1,
      cir.ComputesWith Binary.interpretation (fun x _ => f n x) →
      20 * nechiporukBlockSize c n *
        (∑ i, activeSharedFanOut cir (block n (nechiporukBlockSize c n) i)) ≤ n * n →
      (n : ℝ) ^ 2 ≤ 64 * (c + 3) * Real.logb 2 n * (2 * cir.size + 1) := by
  have hlog := Nat.eventually_mul_log_le (16 * (c + 3)) one_lt_two
  filter_upwards [hK, hacc, hrect, hlog, eventually_ge_atTop 4] with
    n hKn haccn hrectn hlogn hn4
  intro cir hcir hact
  set b := nechiporukBlockSize c n with hb
  have hb0 : 0 < b := by rw [hb, nechiporukBlockSize]; omega
  have hlog2 : 2 ≤ Nat.log 2 n := by
    have : 2 ^ 2 ≤ n := by omega
    exact Nat.le_log_of_pow_le one_lt_two this
  have hbK : 8 * K n ≤ 2 ^ b := by
    have hn : n ≤ 2 ^ (Nat.log 2 n + 1) := (Nat.lt_pow_succ_log_self one_lt_two n).le
    calc 8 * K n ≤ 8 * n ^ c := Nat.mul_le_mul_left _ hKn
      _ ≤ 8 * (2 ^ (Nat.log 2 n + 1)) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn c)
      _ = 2 ^ b := by
          rw [hb, nechiporukBlockSize, ← pow_mul, pow_add, show (8 : Nat) = 2 ^ 3 by norm_num,
            Nat.mul_comm (Nat.log 2 n + 1) c]
  have hble : b ≤ 2 * (c + 3) * Nat.log 2 n := by
    rw [hb, nechiporukBlockSize]
    have : c * (Nat.log 2 n + 1) ≤ 2 * c * Nat.log 2 n := by nlinarith
    nlinarith
  have h8b : 8 * b ≤ n := by
    calc 8 * b ≤ 8 * (2 * (c + 3) * Nat.log 2 n) := Nat.mul_le_mul_left _ hble
      _ = 16 * (c + 3) * Nat.log 2 n := by ring
      _ ≤ n := hlogn
  have main := size_lower_bound_active' hrectn haccn hb0 hbK cir hcir
  have hksize := sharedGateCount_le_size cir
  set A := ∑ i, activeSharedFanOut cir (block n b i)
  have h₁ : 3 * n ≤ 4 * (n - b) := by omega
  have h₂ : 2 * n ≤ 4 * (n - 2 * b - 1) := by omega
  have h₃ : 6 * (n * n) ≤ 4 * (n * n) + 64 * b * (2 * cir.size + 1) := by
    calc 6 * (n * n)
        = (3 * n) * (2 * n) := by ring
      _ ≤ (4 * (n - b)) * (4 * (n - 2 * b - 1)) := Nat.mul_le_mul h₁ h₂
      _ = 16 * ((n - b) * (n - 2 * b - 1)) := by ring
      _ ≤ 16 * (5 * b * A + 4 * b * (cir.size + KW.sharedGateCount cir + 1)) :=
          Nat.mul_le_mul_left _ main
      _ = 4 * (20 * b * A) + 64 * b * (cir.size + KW.sharedGateCount cir + 1) := by ring
      _ ≤ 4 * (n * n) + 64 * b * (2 * cir.size + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hact)
            (Nat.mul_le_mul_left _ (by omega))
  have h₄ : n * n ≤ 32 * b * (2 * cir.size + 1) := by nlinarith
  have h₅ : (n : ℝ) ^ 2 ≤ 32 * b * (2 * cir.size + 1) := by
    have : ((n * n : Nat) : ℝ) ≤ ((32 * b * (2 * cir.size + 1) : Nat) : ℝ) := by
      exact_mod_cast h₄
    push_cast at this
    nlinarith
  have hbR : (b : ℝ) ≤ 2 * (c + 3) * Nat.log 2 n := by exact_mod_cast hble
  have hlogR := natLog_le_logb n
  have hsize : (0 : ℝ) ≤ (2 * cir.size + 1 : ℝ) := by positivity
  calc (n : ℝ) ^ 2 ≤ 32 * b * (2 * cir.size + 1) := h₅
    _ ≤ 32 * (2 * (c + 3) * Nat.log 2 n) * (2 * cir.size + 1) := by gcongr
    _ ≤ 32 * (2 * (c + 3) * Real.logb 2 n) * (2 * cir.size + 1) := by gcongr
    _ = 64 * (c + 3) * Real.logb 2 n * (2 * cir.size + 1) := by ring

/-- **Bounded-block-span `Ω(n² / log n)` circuit lower bound with superlinear shared fan-out.**
If every shared gate of `cir` is active on at most `span n` of the logarithmic Nechiporuk blocks
and `40 (c + 3) log₂ n · span n · s n ≤ n²` (so for bounded block-span `span n = O(1)`, the total
shared fan-out `s n` may be **superlinear** up to `Θ(n² / log n)`), then
`n² ≤ 64 (c + 3) log₂ n · (2 · cir.size + 1)` for all large `n`. -/
theorem eventually_sq_le_size_of_gateBlockSpan_le (f : ∀ n, Cslib.BooleanFunction n)
    (K span s : Nat → Nat) (c : Nat)
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c)
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    (hspan : ∀ᶠ n in atTop, 40 * (c + 3) * Nat.log 2 n * span n * s n ≤ n * n) :
    ∀ᶠ n in atTop, ∀ cir : Circuit Binary.signature n 1,
      cir.ComputesWith Binary.interpretation (fun x _ => f n x) →
      sharedFanOut cir ≤ s n →
      (∀ g : Fin cir.size, 2 ≤ KW.gateFanOut cir g →
        gateBlockSpan (block n (nechiporukBlockSize c n)) cir.program g ≤ span n) →
      (n : ℝ) ^ 2 ≤ 64 * (c + 3) * Real.logb 2 n * (2 * cir.size + 1) := by
  filter_upwards [eventually_sq_le_size_active f K c hK hacc hrect, hspan,
    eventually_ge_atTop 4] with n hmain hspann hn4
  intro cir hcir hfan hgate
  apply hmain cir hcir
  set b := nechiporukBlockSize c n with hb
  have hlog2 : 2 ≤ Nat.log 2 n := by
    have : 2 ^ 2 ≤ n := by omega
    exact Nat.le_log_of_pow_le one_lt_two this
  have hble : b ≤ 2 * (c + 3) * Nat.log 2 n := by
    rw [hb, nechiporukBlockSize]
    have : c * (Nat.log 2 n + 1) ≤ 2 * c * Nat.log 2 n := by nlinarith
    nlinarith
  have hsum : ∑ i, activeSharedFanOut cir (block n b i) ≤ span n * s n :=
    (sum_activeSharedFanOut_le_of_gateBlockSpan_le cir (block n b) hgate).trans
      (Nat.mul_le_mul_left _ hfan)
  calc 20 * b * (∑ i, activeSharedFanOut cir (block n b i))
      ≤ 20 * (2 * (c + 3) * Nat.log 2 n) * (span n * s n) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hble) hsum
    _ = 40 * (c + 3) * Nat.log 2 n * span n * s n := by ring
    _ ≤ n * n := hspann

/-- For any multiplier `M`, a rectangle-free family requires at least `M · n` gates in any
full-binary-basis circuit whose active shared fan-out on the logarithmic blocks satisfies
`20 b · (∑ i, activeSharedFanOut cir (block n b i)) ≤ n²`. -/
theorem eventually_mul_le_size_of_rectangleFree_active (f : ∀ n, Cslib.BooleanFunction n)
    (K : Nat → Nat) (c : Nat)
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c)
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n)) (M : Nat) :
    ∀ᶠ n in atTop, ∀ cir : Circuit Binary.signature n 1,
      cir.ComputesWith Binary.interpretation (fun x _ => f n x) →
      20 * nechiporukBlockSize c n *
        (∑ i, activeSharedFanOut cir (block n (nechiporukBlockSize c n) i)) ≤ n * n →
      M * n ≤ cir.size := by
  have hlog := Nat.eventually_mul_log_le (128 * (c + 3) * (M + 1)) one_lt_two
  filter_upwards [hK, hacc, hrect, hlog, eventually_ge_atTop 4] with
    n hKn haccn hrectn hlogn hn4
  intro cir hcir hact
  set b := nechiporukBlockSize c n with hb
  have hb0 : 0 < b := by rw [hb, nechiporukBlockSize]; omega
  have hlog2 : 2 ≤ Nat.log 2 n := by
    have : 2 ^ 2 ≤ n := by omega
    exact Nat.le_log_of_pow_le one_lt_two this
  have hbK : 8 * K n ≤ 2 ^ b := by
    have hn : n ≤ 2 ^ (Nat.log 2 n + 1) := (Nat.lt_pow_succ_log_self one_lt_two n).le
    calc 8 * K n ≤ 8 * n ^ c := Nat.mul_le_mul_left _ hKn
      _ ≤ 8 * (2 ^ (Nat.log 2 n + 1)) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn c)
      _ = 2 ^ b := by
          rw [hb, nechiporukBlockSize, ← pow_mul, pow_add, show (8 : Nat) = 2 ^ 3 by norm_num,
            Nat.mul_comm (Nat.log 2 n + 1) c]
  have hble : b ≤ 2 * (c + 3) * Nat.log 2 n := by
    rw [hb, nechiporukBlockSize]
    have : c * (Nat.log 2 n + 1) ≤ 2 * c * Nat.log 2 n := by nlinarith
    nlinarith
  have h8b : 8 * b ≤ n := by
    calc 8 * b ≤ 8 * (2 * (c + 3) * Nat.log 2 n) := Nat.mul_le_mul_left _ hble
      _ = 16 * (c + 3) * Nat.log 2 n := by ring
      _ ≤ 128 * (c + 3) * (M + 1) * Nat.log 2 n := by nlinarith
      _ ≤ n := hlogn
  have main := size_lower_bound_active' hrectn haccn hb0 hbK cir hcir
  have hksize := sharedGateCount_le_size cir
  set A := ∑ i, activeSharedFanOut cir (block n b i)
  have h₁ : 3 * n ≤ 4 * (n - b) := by omega
  have h₂ : 2 * n ≤ 4 * (n - 2 * b - 1) := by omega
  have h₃ : 6 * (n * n) ≤ 4 * (n * n) + 64 * b * (2 * cir.size + 1) := by
    calc 6 * (n * n)
        = (3 * n) * (2 * n) := by ring
      _ ≤ (4 * (n - b)) * (4 * (n - 2 * b - 1)) := Nat.mul_le_mul h₁ h₂
      _ = 16 * ((n - b) * (n - 2 * b - 1)) := by ring
      _ ≤ 16 * (5 * b * A + 4 * b * (cir.size + KW.sharedGateCount cir + 1)) :=
          Nat.mul_le_mul_left _ main
      _ = 4 * (20 * b * A) + 64 * b * (cir.size + KW.sharedGateCount cir + 1) := by ring
      _ ≤ 4 * (n * n) + 64 * b * (2 * cir.size + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hact)
            (Nat.mul_le_mul_left _ (by omega))
  have h₄ : n * n ≤ 32 * b * (2 * cir.size + 1) := by nlinarith
  have h64b : 64 * b * (M + 1) ≤ n := by
    calc 64 * b * (M + 1)
        ≤ 64 * (2 * (c + 3) * Nat.log 2 n) * (M + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hble)
      _ = 128 * (c + 3) * (M + 1) * Nat.log 2 n := by ring
      _ ≤ n := hlogn
  have h₅ : n * (2 * (M + 1) * n) ≤ n * (2 * cir.size + 1) := by
    calc n * (2 * (M + 1) * n)
        = 2 * (M + 1) * (n * n) := by ring
      _ ≤ 2 * (M + 1) * (32 * b * (2 * cir.size + 1)) := Nat.mul_le_mul_left _ h₄
      _ = (64 * b * (M + 1)) * (2 * cir.size + 1) := by ring
      _ ≤ n * (2 * cir.size + 1) := Nat.mul_le_mul_right _ h64b
  have h₆ : 2 * (M + 1) * n ≤ 2 * cir.size + 1 :=
    Nat.le_of_mul_le_mul_left h₅ (by omega)
  nlinarith

/-- **Superlinear circuit size for rectangle-free families under `O(n² / log n)` active-block
shared fan-out.** If `cir n` is a family of circuits over `Binary.signature` computing a
`K n`-rectangle-free family `f n` (`K n ≤ n ^ c`, `2 ^ (n - 2) ≤ |(accepting (f n))|`) whose
active shared fan-out on the logarithmic blocks satisfies
`20 b · (∑ i, activeSharedFanOut (cir n) (block n b i)) ≤ n²` eventually, then `(cir n).size`
grows faster than `n`. -/
theorem isLittleO_size_of_rectangleFree_active (f : ∀ n, Cslib.BooleanFunction n)
    (K : Nat → Nat) (c : Nat)
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c)
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    (cir : ∀ n, Circuit Binary.signature n 1)
    (hcir : ∀ n, (cir n).ComputesWith Binary.interpretation (fun x _ => f n x))
    (hact : ∀ᶠ n in atTop, 20 * nechiporukBlockSize c n *
      (∑ i, activeSharedFanOut (cir n) (block n (nechiporukBlockSize c n) i)) ≤ n * n) :
    (fun n : ℕ => (n : ℝ)) =o[atTop] fun n => ((cir n).size : ℝ) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_ge (1 / ε)
  have hMpos : 0 < M := by
    have : (0 : ℝ) < 1 / ε := by positivity
    have : (0 : ℝ) < M := this.trans_le hM
    exact_mod_cast this
  filter_upwards [eventually_mul_le_size_of_rectangleFree_active f K c hK hacc hrect M, hact] with
    n hmain hactn
  simp only [Real.norm_natCast]
  have hsize : (M * n : ℝ) ≤ (cir n).size := by
    exact_mod_cast hmain (cir n) (hcir n) hactn
  have hM' : (M : ℝ)⁻¹ ≤ ε := by
    rw [inv_le_comm₀ (by positivity) hε]
    simpa [one_div] using hM
  calc (n : ℝ) = (M : ℝ)⁻¹ * (M * n) := by field_simp
    _ ≤ ε * (cir n).size := by gcongr

/-- **Circuit size `Ω(n² / log n)` for rectangle-free families with bounded shared fan-out.**
For a family that is `K n`-rectangle-free with `K n ≤ n ^ c` and at least `2 ^ (n - 2)`
accepting inputs, every full-binary-basis circuit `cir` computing `f n` with
`sharedFanOut cir ≤ s n` (where `20 · s n ≤ n` eventually) satisfies
`n² ≤ 128 (c + 3) log₂ n · (cir.size + s n + 1)` for all large `n`. -/
theorem eventually_sq_le_size (f : ∀ n, Cslib.BooleanFunction n) (K s : Nat → Nat) (c : Nat)
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c)
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    (hs : ∀ᶠ n in atTop, 20 * s n ≤ n) :
    ∀ᶠ n in atTop, ∀ cir : Circuit Binary.signature n 1,
      cir.ComputesWith Binary.interpretation (fun x _ => f n x) →
      sharedFanOut cir ≤ s n →
      (n : ℝ) ^ 2 ≤ 128 * (c + 3) * Real.logb 2 n * (cir.size + s n + 1) := by
  have hlog := Nat.eventually_mul_log_le (16 * (c + 3)) one_lt_two
  filter_upwards [hK, hacc, hrect, hs, hlog, eventually_ge_atTop 4] with
    n hKn haccn hrectn hsn hlogn hn4
  intro cir hcir hfan
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
  have hk : KW.sharedGateCount cir ≤ s n :=
    (sharedGateCount_le_sharedFanOut cir).trans hfan
  have main := size_lower_bound' hrectn haccn hb0 hbK cir hcir hk hfan
  have h₁ : 3 * n ≤ 4 * (n - b) := by omega
  have h₂ : n ≤ 4 * (n - 2 * b - 1 - s n - 4 * s n) := by omega
  have h₃ : 3 * n * n ≤ 64 * b * (cir.size + s n + 1) := by
    calc 3 * n * n
        ≤ 4 * (n - b) * (4 * (n - 2 * b - 1 - s n - 4 * s n)) := Nat.mul_le_mul h₁ h₂
      _ = 16 * ((n - b) * (n - 2 * b - 1 - s n - 4 * s n)) := by ring
      _ ≤ 16 * (4 * b * (cir.size + s n + 1)) := Nat.mul_le_mul_left _ main
      _ = 64 * b * (cir.size + s n + 1) := by ring
  have h₄ : (n : ℝ) ^ 2 ≤ 64 * b * (cir.size + s n + 1) := by
    have : ((3 * n * n : Nat) : ℝ) ≤ ((64 * b * (cir.size + s n + 1) : Nat) : ℝ) := by
      exact_mod_cast h₃
    push_cast at this
    nlinarith
  have hbR : (b : ℝ) ≤ 2 * (c + 3) * Nat.log 2 n := by exact_mod_cast hble
  have hlogR := natLog_le_logb n
  have hsize : (0 : ℝ) ≤ (cir.size + s n + 1 : ℝ) := by positivity
  calc (n : ℝ) ^ 2 ≤ 64 * b * (cir.size + s n + 1) := h₄
    _ ≤ 64 * (2 * (c + 3) * Nat.log 2 n) * (cir.size + s n + 1) := by gcongr
    _ ≤ 64 * (2 * (c + 3) * Real.logb 2 n) * (cir.size + s n + 1) := by gcongr
    _ = 128 * (c + 3) * Real.logb 2 n * (cir.size + s n + 1) := by ring

/-- For any multiplier `M`, a rectangle-free family with `20 · s n ≤ n` eventually requires at
least `M · n` gates in any full-binary-basis circuit with `sharedFanOut ≤ s n`. -/
theorem eventually_mul_le_size_of_rectangleFree (f : ∀ n, Cslib.BooleanFunction n)
    (K s : Nat → Nat) (c : Nat)
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c)
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    (hs : ∀ᶠ n in atTop, 20 * s n ≤ n) (M : Nat) :
    ∀ᶠ n in atTop, ∀ cir : Circuit Binary.signature n 1,
      cir.ComputesWith Binary.interpretation (fun x _ => f n x) →
      sharedFanOut cir ≤ s n →
      M * n ≤ cir.size := by
  have hlog := Nat.eventually_mul_log_le (128 * (c + 3) * (M + 2)) one_lt_two
  filter_upwards [hK, hacc, hrect, hs, hlog, eventually_ge_atTop 4] with
    n hKn haccn hrectn hsn hlogn hn4
  intro cir hcir hfan
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
      _ ≤ 128 * (c + 3) * (M + 2) * Nat.log 2 n := by nlinarith
      _ ≤ n := hlogn
  have hk : KW.sharedGateCount cir ≤ s n :=
    (sharedGateCount_le_sharedFanOut cir).trans hfan
  have main := size_lower_bound' hrectn haccn hb0 hbK cir hcir hk hfan
  have h₁ : 3 * n ≤ 4 * (n - b) := by omega
  have h₂ : n ≤ 4 * (n - 2 * b - 1 - s n - 4 * s n) := by omega
  have h₃ : 3 * n * n ≤ 64 * b * (cir.size + s n + 1) := by
    calc 3 * n * n
        ≤ 4 * (n - b) * (4 * (n - 2 * b - 1 - s n - 4 * s n)) := Nat.mul_le_mul h₁ h₂
      _ = 16 * ((n - b) * (n - 2 * b - 1 - s n - 4 * s n)) := by ring
      _ ≤ 16 * (4 * b * (cir.size + s n + 1)) := Nat.mul_le_mul_left _ main
      _ = 64 * b * (cir.size + s n + 1) := by ring
  have h64b : 64 * b * (M + 2) ≤ n := by
    calc 64 * b * (M + 2)
        ≤ 64 * (2 * (c + 3) * Nat.log 2 n) * (M + 2) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hble)
      _ = 128 * (c + 3) * (M + 2) * Nat.log 2 n := by ring
      _ ≤ n := hlogn
  have h₄ : n * (3 * (M + 2) * n) ≤ n * (3 * (cir.size + s n + 1)) := by
    calc n * (3 * (M + 2) * n)
        = (M + 2) * (3 * n * n) := by ring
      _ ≤ (M + 2) * (64 * b * (cir.size + s n + 1)) := Nat.mul_le_mul_left _ h₃
      _ = (64 * b * (M + 2)) * (cir.size + s n + 1) := by ring
      _ ≤ n * (cir.size + s n + 1) := Nat.mul_le_mul_right _ h64b
      _ ≤ n * (3 * (cir.size + s n + 1)) := Nat.mul_le_mul_left _ (by omega)
  have h₅ : 3 * (M + 2) * n ≤ 3 * (cir.size + s n + 1) :=
    Nat.le_of_mul_le_mul_left h₄ (by omega)
  nlinarith

/-- **Rectangle-free families need superlinear full-binary-basis circuits when `sharedFanOut =
o(n)`.** If `s n = o(n)` and `cir n` is a family of circuits over `Binary.signature` computing a
`K n`-rectangle-free family `f n` (`K n ≤ n ^ c`, `2 ^ (n - 2) ≤ |(accepting (f n))|`) with
`sharedFanOut (cir n) ≤ s n`, then `(cir n).size` grows faster than `n`. -/
theorem isLittleO_size_of_rectangleFree (f : ∀ n, Cslib.BooleanFunction n)
    (K s : Nat → Nat) (c : Nat)
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c)
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    (hs : (fun n => (s n : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ))
    (cir : ∀ n, Circuit Binary.signature n 1)
    (hcir : ∀ n, (cir n).ComputesWith Binary.interpretation (fun x _ => f n x))
    (hfan : ∀ n, sharedFanOut (cir n) ≤ s n) :
    (fun n : ℕ => (n : ℝ)) =o[atTop] fun n => ((cir n).size : ℝ) := by
  have hs20 : ∀ᶠ n in atTop, 20 * s n ≤ n := by
    have hε : (0 : ℝ) < 1 / 20 := by positivity
    filter_upwards [hs.bound hε] with n hsn
    simp only [Real.norm_natCast] at hsn
    have hR : ((20 * s n : ℕ) : ℝ) ≤ n :=
      calc ((20 * s n : ℕ) : ℝ) = 20 * (s n : ℝ) := by push_cast; ring
        _ ≤ 20 * (1 / 20 * n) := by gcongr
        _ = n := by ring
    exact_mod_cast hR
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_ge (1 / ε)
  have hMpos : 0 < M := by
    have : (0 : ℝ) < 1 / ε := by positivity
    have : (0 : ℝ) < M := this.trans_le hM
    exact_mod_cast this
  filter_upwards [eventually_mul_le_size_of_rectangleFree f K s c hK hacc hrect hs20 M] with
    n hmain
  simp only [Real.norm_natCast]
  have hsize : (M * n : ℝ) ≤ (cir n).size := by
    exact_mod_cast hmain (cir n) (hcir n) (hfan n)
  have hM' : (M : ℝ)⁻¹ ≤ ε := by
    rw [inv_le_comm₀ (by positivity) hε]
    simpa [one_div] using hM
  calc (n : ℝ) = (M : ℝ)⁻¹ * (M * n) := by field_simp
    _ ≤ ε * (cir n).size := by gcongr

end Nechiporuk
end Algebraic
