/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.Materialize

/-!
# A ruler of logarithmic length

Amplification runs logarithmically many rounds, and the bounded-iteration rule
counts rounds by the *length* of a string. So an algorithm needs to write a
string whose length is the logarithm of its input's — the one shrinking step the
rest of the development never needed.

The construction folds over the input carrying two counters: a ruler, and a
threshold that doubles. Every time the number of bits read reaches the
threshold, the ruler gains a mark and the threshold doubles, so the ruler counts
the doublings.

## Main definitions

- `Complexity.logStep` — one step of that fold
- `Complexity.logRuler` — the ruler itself

## Main results

- `Complexity.logRuler_mem_FP` — it is an `FP` function
-/

@[expose] public section

namespace Complexity

/-- How long the ruler is after reading `n` bits: it gains a mark exactly when
the count reaches the next power of two. -/
def rulerLen : ℕ → ℕ
  | 0 => 0
  | n + 1 => if n + 1 < 2 ^ rulerLen n then rulerLen n else rulerLen n + 1

/-- One step of the ruler fold, on `pair (pair W acc) t` where `acc` is
`pair ruler threshold`: on reaching the threshold, add a mark and double. -/
noncomputable def logStep (z : List Bool) : List Bool :=
  ifLtLen (pairSnd z) (dropOne (pairSnd (pairSnd
      (pairFst z))))
    (pairSnd (pairFst z))
    (pair (pairFst (pairSnd (pairFst z)) ++ [true])
      (pairSnd (pairSnd (pairFst z))
        ++ pairSnd (pairSnd (pairFst z))))

theorem logStep_mem_FP : logStep ∈ FP := by
  have hacc : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hr : (fun z : List Bool =>
      pairFst (pairSnd (pairFst z))) ∈ FP :=
    mem_FP_comp hacc Cobham.fstBlock_mem_FP
  have hth : (fun z : List Bool =>
      pairSnd (pairSnd (pairFst z))) ∈ FP :=
    mem_FP_comp hacc Cobham.sndBlock_mem_FP
  exact ifLtLen_mem_FP Cobham.sndBlock_mem_FP (dropOneFn_mem_FP hth) hacc
    (Cobham.pairFn_mem_FP (Cobham.appendFn_mem_FP hr (constFn_mem_FP [true]))
      (Cobham.appendFn_mem_FP hth hth))

theorem rulerLen_le (n : ℕ) : rulerLen n ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [rulerLen]
      split <;> omega

theorem two_pow_rulerLen_le (n : ℕ) : 2 ^ rulerLen n ≤ 2 * n + 1 := by
  induction n with
  | zero => simp [rulerLen]
  | succ n ih =>
      rw [rulerLen]
      by_cases h : n + 1 < 2 ^ rulerLen n
      · rw [ite_eq_left h]
        omega
      · rw [ite_eq_right h, pow_succ]
        omega

theorem lt_two_pow_rulerLen (n : ℕ) : n < 2 ^ rulerLen n := by
  induction n with
  | zero => simp [rulerLen]
  | succ n ih =>
      rw [rulerLen]
      by_cases h : n + 1 < 2 ^ rulerLen n
      · rw [ite_eq_left h]
        exact h
      · rw [ite_eq_right h, pow_succ]
        omega

/-- **The ruler is at least the binary logarithm.** -/
theorem log_lt_rulerLen (n : ℕ) (hn : n ≠ 0) : Nat.log 2 n < rulerLen n :=
  Nat.log_lt_of_lt_pow hn (lt_two_pow_rulerLen n)

theorem rulerLen_pos {n : ℕ} (hn : 0 < n) : 0 < rulerLen n := by
  cases n with
  | zero => omega
  | succ n =>
      rw [rulerLen]
      split
      · rename_i h
        by_contra hc
        have h0 : rulerLen n = 0 := by omega
        rw [h0] at h
        simp at h
      · omega

/-- The ruler is at most a logarithm: `2 ^ rulerLen n ≤ 2n + 1`. -/
theorem rulerLen_le_log (n : ℕ) : rulerLen n ≤ Nat.log 2 (2 * n + 1) := by
  refine le_trans (le_of_eq (Nat.log_pow (b := 2) (by omega) (rulerLen n)).symm) ?_
  exact Nat.log_mono_right (two_pow_rulerLen_le n)

/-- **A ruler over a polynomially bounded quantity is logarithmic.** -/
theorem rulerLen_bigO_log {N : ℕ → ℕ} {A B : ℕ} (hN : ∀ n, N n ≤ A * (n + 1) ^ B) :
    (fun n => rulerLen (N n)) =O (fun n => Nat.log 2 n) := by
  refine Asymptotics.IsBigO.of_bound (Nat.log 2 A + 2 * B + 6) ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  simp only [Real.norm_natCast]
  have hlog : 1 ≤ Nat.log 2 n := Nat.log_pos (by omega) hn
  have hA : A ≤ 2 ^ (Nat.log 2 A + 1) := le_of_lt (Nat.lt_pow_succ_log_self (by omega) A)
  have hn1 : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by omega) n
    omega
  have hpow : (n + 1) ^ B ≤ 2 ^ ((Nat.log 2 n + 1) * B) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hn1 B
  have hbound : 2 * N n + 1 ≤ 2 ^ (Nat.log 2 A + 3 + (Nat.log 2 n + 1) * B) := by
    have h1 : N n ≤ 2 ^ (Nat.log 2 A + 1) * 2 ^ ((Nat.log 2 n + 1) * B) :=
      le_trans (hN n) (Nat.mul_le_mul hA hpow)
    have h2 : 2 ^ (Nat.log 2 A + 3 + (Nat.log 2 n + 1) * B)
        = 4 * (2 ^ (Nat.log 2 A + 1) * 2 ^ ((Nat.log 2 n + 1) * B)) := by
      rw [← pow_add, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
      congr 1
      ring
    have h3 : 0 < 2 ^ (Nat.log 2 A + 1) * 2 ^ ((Nat.log 2 n + 1) * B) :=
      Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    omega
  have hle : rulerLen (N n) ≤ Nat.log 2 A + 3 + (Nat.log 2 n + 1) * B := by
    refine le_trans (rulerLen_le_log (N n)) ?_
    refine le_trans (Nat.log_mono_right hbound) ?_
    rw [Nat.log_pow (by omega)]
  have hfin : rulerLen (N n) ≤ (Nat.log 2 A + 2 * B + 6) * Nat.log 2 n := by
    have hmul : (Nat.log 2 n + 1) * B ≤ 2 * B * Nat.log 2 n := by
      have : Nat.log 2 n + 1 ≤ 2 * Nat.log 2 n := by omega
      calc (Nat.log 2 n + 1) * B ≤ (2 * Nat.log 2 n) * B := Nat.mul_le_mul_right _ this
        _ = 2 * B * Nat.log 2 n := by ring
    have hconst : Nat.log 2 A + 3 ≤ (Nat.log 2 A + 6) * Nat.log 2 n := by
      calc Nat.log 2 A + 3 ≤ (Nat.log 2 A + 6) * 1 := by omega
        _ ≤ (Nat.log 2 A + 6) * Nat.log 2 n := Nat.mul_le_mul_left _ hlog
    calc rulerLen (N n) ≤ Nat.log 2 A + 3 + (Nat.log 2 n + 1) * B := hle
      _ ≤ (Nat.log 2 A + 6) * Nat.log 2 n + 2 * B * Nat.log 2 n := by omega
      _ = (Nat.log 2 A + 2 * B + 6) * Nat.log 2 n := by ring
  exact_mod_cast hfin

/-- **The fold's value after reading a list.** -/
theorem logFold_eq (bound : ℕ) : ∀ z : List Bool, 4 * z.length + 4 ≤ bound →
    Cobham.recFoldClamp logStep logStep bound (pair [] [true]) [] z
      = pair (List.replicate (rulerLen z.length) true)
        (List.replicate (2 ^ rulerLen z.length) true) := by
  intro z
  induction z with
  | nil =>
      intro _
      rw [Cobham.recFoldClamp]
      show (pair [] [true]).take bound = pair (List.replicate (rulerLen 0) true)
        (List.replicate (2 ^ rulerLen 0) true)
      rw [show rulerLen 0 = 0 from rfl]
      simp only [pow_zero, List.replicate_zero, List.replicate_one]
      rw [List.take_of_length_le]
      simp
      omega
  | cons b t ih =>
      intro hb
      have hbt : 4 * t.length + 4 ≤ bound := by simp at hb ⊢; omega
      rw [Cobham.recFoldClamp]
      simp only [Bool.cond_self]
      rw [ih hbt, logStep]
      simp only [pairFst_pair, pairSnd_pair, dropOne]
      have hb' : 4 * t.length + 8 ≤ bound := by simp at hb; omega
      by_cases h : t.length < 2 ^ rulerLen t.length - 1
      · rw [ifLtLen_pos (by simpa using h), List.length_cons,
          show rulerLen (t.length + 1) = rulerLen t.length from by
            rw [rulerLen]
            exact ite_eq_left (by omega)]
        refine List.take_of_length_le ?_
        rw [pair_length, List.length_replicate, List.length_replicate]
        have h1 := rulerLen_le t.length
        have h2 := two_pow_rulerLen_le t.length
        omega
      · rw [ifLtLen_neg (by simpa using h), List.length_cons,
          show rulerLen (t.length + 1) = rulerLen t.length + 1 from by
            rw [rulerLen]
            exact ite_eq_right (by omega),
          ← List.replicate_add, ← two_mul, ← pow_succ', ← List.replicate_succ']
        refine List.take_of_length_le ?_
        rw [pair_length, List.length_replicate, List.length_replicate]
        have h1 := rulerLen_le (t.length + 1)
        have h2 := two_pow_rulerLen_le (t.length + 1)
        rw [show rulerLen (t.length + 1) = rulerLen t.length + 1 from by
          rw [rulerLen]
          exact ite_eq_right (by omega)] at h1 h2
        omega

/-- The fold itself, on `pair W z`. -/
noncomputable def logRulerRaw (w : List Bool) : List Bool :=
  Cobham.recFoldClamp logStep logStep (4 * w.length + 4) (pair [] [true])
    (pairFst w) (pairSnd w)

theorem logRulerRaw_mem_FP : logRulerRaw ∈ FP := by
  refine mem_FP_of_eq (Cobham.recFoldClamp_mem_FP logStep_mem_FP logStep_mem_FP
    (constFn_mem_FP (pair [] [true])) (4 * Polynomial.X + 4)) fun w => ?_
  rw [logRulerRaw]
  simp

/-- **A ruler of logarithmic length.** -/
noncomputable def logRuler (z : List Bool) : List Bool :=
  pairFst (logRulerRaw (pair [] z))

theorem logRuler_mem_FP : logRuler ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP (constFn_mem_FP []) id_mem_FP)
    (mem_FP_comp logRulerRaw_mem_FP Cobham.fstBlock_mem_FP)) fun _ => rfl

/-- **The ruler is as long as the fold says.** -/
theorem logRuler_eq (z : List Bool) :
    logRuler z = List.replicate (rulerLen z.length) true := by
  rw [logRuler, logRulerRaw, pairFst_pair, pairSnd_pair,
    logFold_eq _ z (by rw [pair_length]; simp), pairFst_pair]

@[simp] theorem length_logRuler (z : List Bool) :
    (logRuler z).length = rulerLen z.length := by
  rw [logRuler_eq, List.length_replicate]

end Complexity
