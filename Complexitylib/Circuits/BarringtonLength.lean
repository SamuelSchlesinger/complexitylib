/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.BarringtonBridge
public import Complexitylib.Circuits.Formula
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Nat.Log

/-!
# Barrington's theorem with a length bound

`Circuits/BarringtonRepr.lean` proves the *existence* of a width-`5` permutation
branching program for every Boolean formula, but discards the program's length.
This module tracks both the original wrapper-based construction and the optimized
textbook construction. Pointwise conjugation retargets a program without changing
its length, while compact negation folds the final constant into the last
instruction. The resulting binary-gate recurrence is exactly fourfold and proves
the classical `4 ^ depth` bound.

## Main results

- `Complexity.BP.length_inverse` — program inversion preserves length.
- `Complexity.BP.Computes_retarget_len`, `Complexity.BP.Computes_and5_len` —
  compatibility bounds for the original wrapper construction.
- `Complexity.BP.Computes_and5_tight` — the exact additive-free commutator
  length recurrence.
- `Complexity.barringtonBound`, `Complexity.barringtonBound_le` — the explicit
  original length recurrence and its `13 ^ size` closed form.
- `Complexity.Computes_formula_len` — the length-tracked formula recursion.
- `Complexity.Computes_formula_depth_four` — optimized formula recursion with
  the textbook `4 ^ depth` bound.
- `Complexity.barrington_representation_len` — Barrington's theorem with the
  `13 ^ size` length bound.
- `Complexity.barrington_representation_depth_four` — Barrington's theorem with
  the textbook `4 ^ depth` length bound.
-/

@[expose] public section

open scoped commutatorElement
open Equiv

set_option maxRecDepth 100000

namespace Complexity

/-- Inverting a branching program preserves its length. -/
theorem BP.length_inverse {w : ℕ} (p : BP w) : (BP.inverse p).length = p.length := by
  simp [BP.inverse]

/-- Compatibility retargeting bound. Pointwise conjugation actually preserves
length exactly, which is stronger than the historical two-instruction bound. -/
theorem BP.Computes_retarget_len {p : BP 5} {f : (ℕ → Bool) → Bool} {σ : Perm (Fin 5)}
    (hp : BP.Computes σ p f) (hσc : σ.IsCycle) (hσo : orderOf σ = 5)
    {a : Perm (Fin 5)} (hac : a.IsCycle) (hao : orderOf a = 5) :
    ∃ r : BP 5, BP.Computes a r f ∧ r.length ≤ p.length + 2 := by
  obtain ⟨r, hr, hlen⟩ :=
    BP.Computes_retarget_length hp hσc hσo hac hao
  exact ⟨r, hr, by omega⟩

/-- Length-tracked `AND` gate: the commutator construction at most doubles the two
    subprograms and adds a constant from the two retargetings. -/
theorem BP.Computes_and5_len {p q : BP 5} {f g : (ℕ → Bool) → Bool} {σ τ : Perm (Fin 5)}
    (hp : BP.Computes σ p f) (hσc : σ.IsCycle) (hσo : orderOf σ = 5)
    (hq : BP.Computes τ q g) (hτc : τ.IsCycle) (hτo : orderOf τ = 5)
    {c : Perm (Fin 5)} (hcc : c.IsCycle) (hco : orderOf c = 5) :
    ∃ r : BP 5, BP.Computes c r (fun α => f α && g α) ∧
      r.length ≤ 2 * p.length + 2 * q.length + 8 := by
  obtain ⟨a, b, hac, hao, hbc, hbo, hab⟩ := every_fiveCycle_is_commutator c hcc hco
  obtain ⟨p', hp', hlp'⟩ := BP.Computes_retarget_len hp hσc hσo hac hao
  obtain ⟨q', hq', hlq'⟩ := BP.Computes_retarget_len hq hτc hτo hbc hbo
  have hand := BP.Computes_and hp' hq'
  rw [hab] at hand
  refine ⟨p' ++ q' ++ BP.inverse p' ++ BP.inverse q', hand, ?_⟩
  simp only [List.length_append, BP.length_inverse]; omega

/-- **Tight Barrington `AND` gate.** Pointwise retargeting has zero overhead, so
the commutator program has exactly twice the sum of the two input lengths. -/
theorem BP.Computes_and5_tight {p q : BP 5}
    {f g : (ℕ → Bool) → Bool} {σ τ : Perm (Fin 5)}
    (hp : BP.Computes σ p f) (hσc : σ.IsCycle) (hσo : orderOf σ = 5)
    (hq : BP.Computes τ q g) (hτc : τ.IsCycle) (hτo : orderOf τ = 5)
    {c : Perm (Fin 5)} (hcc : c.IsCycle) (hco : orderOf c = 5) :
    ∃ r : BP 5, BP.Computes c r (fun α => f α && g α) ∧
      r.length = 2 * p.length + 2 * q.length := by
  obtain ⟨a, b, hac, hao, hbc, hbo, hab⟩ :=
    every_fiveCycle_is_commutator c hcc hco
  obtain ⟨p', hp', hlp'⟩ :=
    BP.Computes_retarget_length hp hσc hσo hac hao
  obtain ⟨q', hq', hlq'⟩ :=
    BP.Computes_retarget_length hq hτc hτo hbc hbo
  have hand := BP.Computes_and hp' hq'
  rw [hab] at hand
  refine ⟨p' ++ q' ++ BP.inverse p' ++ BP.inverse q', hand, ?_⟩
  simp only [List.length_append, BP.length_inverse, hlp', hlq']
  omega

/-- Explicit length bound for the Barrington branching-program construction,
    following its recurrence: leaves cost `≤ 1`, negation adds `1`, and the `AND`
    / `OR` steps double the children and add a constant. -/
def barringtonBound : BoolFormula → ℕ
  | .var _ => 1
  | .tru => 1
  | .fls => 0
  | .neg φ => barringtonBound φ + 1
  | .conj φ ψ => 2 * barringtonBound φ + 2 * barringtonBound ψ + 8
  | .disj φ ψ => 2 * barringtonBound φ + 2 * barringtonBound ψ + 13

/-- The construction bound is dominated by `13 ^ (size φ)`. -/
theorem barringtonBound_le (φ : BoolFormula) : barringtonBound φ ≤ 13 ^ φ.size := by
  induction φ with
  | var i => simp [barringtonBound, BoolFormula.size]
  | tru => simp [barringtonBound, BoolFormula.size]
  | fls => simp [barringtonBound, BoolFormula.size]
  | neg φ ih =>
    have h1 : 1 ≤ 13 ^ φ.size := Nat.one_le_pow _ _ (by norm_num)
    simp only [barringtonBound, BoolFormula.size, pow_succ]; omega
  | conj φ ψ ihφ ihψ =>
    have hφ : (13 : ℕ) ≤ 13 ^ φ.size :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (BoolFormula.one_le_size φ))
    have hψ : (13 : ℕ) ≤ 13 ^ ψ.size :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (BoolFormula.one_le_size ψ))
    simp only [barringtonBound, BoolFormula.size, pow_succ, pow_add]
    nlinarith [ihφ, ihψ, hφ, hψ]
  | disj φ ψ ihφ ihψ =>
    have hφ : (13 : ℕ) ≤ 13 ^ φ.size :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (BoolFormula.one_le_size φ))
    have hψ : (13 : ℕ) ≤ 13 ^ ψ.size :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (BoolFormula.one_le_size ψ))
    simp only [barringtonBound, BoolFormula.size, pow_succ, pow_add]
    nlinarith [ihφ, ihψ, hφ, hψ]

/-- The construction bound is also dominated by `17 ^ (depth φ)`. Because depth is
    the `NC¹` measure, this is the load-bearing bound: a formula of depth
    `d = O(log n)` compiles to a width-`5` program of length `17^d = poly(n)` — the
    `NC¹ ⊆` polynomial-size width-`5` branching programs direction of Barrington. -/
theorem barringtonBound_le_pow_depth (φ : BoolFormula) : barringtonBound φ ≤ 17 ^ φ.depth := by
  induction φ with
  | var i => simp [barringtonBound, BoolFormula.depth]
  | tru => simp [barringtonBound, BoolFormula.depth]
  | fls => simp [barringtonBound, BoolFormula.depth]
  | neg φ ih =>
    have h1 : 1 ≤ 17 ^ φ.depth := Nat.one_le_pow _ _ (by omega)
    simp only [barringtonBound, BoolFormula.depth, Nat.pow_succ]; omega
  | conj φ ψ ihφ ihψ =>
    have h0 : (17 : ℕ) ^ φ.depth ≤ 17 ^ max φ.depth ψ.depth :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have h1 : (17 : ℕ) ^ ψ.depth ≤ 17 ^ max φ.depth ψ.depth :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    have hp : 1 ≤ 17 ^ max φ.depth ψ.depth := Nat.one_le_pow _ _ (by omega)
    simp only [barringtonBound, BoolFormula.depth, Nat.pow_succ]; omega
  | disj φ ψ ihφ ihψ =>
    have h0 : (17 : ℕ) ^ φ.depth ≤ 17 ^ max φ.depth ψ.depth :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have h1 : (17 : ℕ) ^ ψ.depth ≤ 17 ^ max φ.depth ψ.depth :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    have hp : 1 ≤ 17 ^ max φ.depth ψ.depth := Nat.one_le_pow _ _ (by omega)
    simp only [barringtonBound, BoolFormula.depth, Nat.pow_succ]; omega

/-- **Length-tracked formula representability.** Every Boolean formula `φ` is
    computed through any target `5`-cycle by a program of length at most
    `barringtonBound φ`. Same recursion as `Computes_formula`, carrying the length
    bound through the length-tracked moves. -/
theorem Computes_formula_len (φ : BoolFormula) :
    ∀ (c : Perm (Fin 5)), c.IsCycle → orderOf c = 5 →
      ∃ r : BP 5, BP.Computes c r (fun α => BoolFormula.eval α φ) ∧
        r.length ≤ barringtonBound φ := by
  induction φ with
  | var i => intro c hcc hco; exact ⟨_, BP.Computes_var c i, by simp [barringtonBound]⟩
  | tru => intro c hcc hco; exact ⟨_, BP.Computes_true c, by simp [barringtonBound]⟩
  | fls => intro c hcc hco; exact ⟨_, BP.Computes_false c, by simp [barringtonBound]⟩
  | neg φ ih =>
    intro c hcc hco
    have hci : c⁻¹.IsCycle := hcc.inv
    have hoi : orderOf c⁻¹ = 5 := by rw [orderOf_inv]; exact hco
    obtain ⟨p, hp, hlp⟩ := ih c⁻¹ hci hoi
    have h := BP.Computes_not hp
    rw [inv_inv] at h
    refine ⟨_, h, ?_⟩
    simp only [barringtonBound, List.length_append, List.length_cons, List.length_nil]; omega
  | conj φ ψ ihφ ihψ =>
    intro c hcc hco
    obtain ⟨p, hp, hlp⟩ := ihφ c hcc hco
    obtain ⟨q, hq, hlq⟩ := ihψ c hcc hco
    obtain ⟨r, hr, hlr⟩ := BP.Computes_and5_len hp hcc hco hq hcc hco hcc hco
    refine ⟨r, hr, ?_⟩
    simp only [barringtonBound]; omega
  | disj φ ψ ihφ ihψ =>
    intro c hcc hco
    have hci : c⁻¹.IsCycle := hcc.inv
    have hoi : orderOf c⁻¹ = 5 := by rw [orderOf_inv]; exact hco
    obtain ⟨p, hp, hlp⟩ := ihφ c hcc hco
    obtain ⟨q, hq, hlq⟩ := ihψ c hcc hco
    obtain ⟨s, hs, hls⟩ :=
      BP.Computes_and5_len (BP.Computes_not hp) hci hoi (BP.Computes_not hq) hci hoi hci hoi
    have h := BP.Computes_not hs
    rw [inv_inv] at h
    have hfun : (fun α => !((!BoolFormula.eval α φ) && (!BoolFormula.eval α ψ)))
              = (fun α => BoolFormula.eval α φ || BoolFormula.eval α ψ) := by
      funext α; simp [Bool.not_and, Bool.not_not]
    rw [hfun] at h
    refine ⟨_, h, ?_⟩
    simp only [barringtonBound, List.length_append, List.length_cons, List.length_nil] at hls ⊢
    omega

/-- **Textbook depth-tracked formula representability.** Every Boolean formula
`φ` is represented through any target `5`-cycle by a program of length at most
`4 ^ depth φ`. Pointwise retargeting contributes no instructions, compact
negation contributes no length beyond `max 1`, and each binary gate uses the
four copies in the commutator construction. -/
theorem Computes_formula_depth_four (φ : BoolFormula) :
    ∀ (c : Perm (Fin 5)), c.IsCycle → orderOf c = 5 →
      ∃ r : BP 5, BP.Computes c r (fun α => BoolFormula.eval α φ) ∧
        r.length ≤ 4 ^ φ.depth := by
  induction φ with
  | var i =>
      intro c hcc hco
      exact ⟨_, BP.Computes_var c i, by simp [BoolFormula.depth]⟩
  | tru =>
      intro c hcc hco
      exact ⟨_, BP.Computes_true c, by simp [BoolFormula.depth]⟩
  | fls =>
      intro c hcc hco
      exact ⟨_, BP.Computes_false c, by simp [BoolFormula.depth]⟩
  | neg φ ih =>
      intro c hcc hco
      have hci : c⁻¹.IsCycle := hcc.inv
      have hoi : orderOf c⁻¹ = 5 := by rw [orderOf_inv]; exact hco
      obtain ⟨p, hp, hlp⟩ := ih c⁻¹ hci hoi
      have h := BP.Computes_not_compact hp
      rw [inv_inv] at h
      refine ⟨BP.postMul p (c⁻¹)⁻¹, h, ?_⟩
      rw [BP.length_postMul]
      apply le_trans (max_le (Nat.one_le_pow _ _ (by omega)) hlp)
      exact Nat.pow_le_pow_right (by omega) (by simp [BoolFormula.depth])
  | conj φ ψ ihφ ihψ =>
      intro c hcc hco
      obtain ⟨p, hp, hlp⟩ := ihφ c hcc hco
      obtain ⟨q, hq, hlq⟩ := ihψ c hcc hco
      obtain ⟨r, hr, hlr⟩ :=
        BP.Computes_and5_tight hp hcc hco hq hcc hco hcc hco
      refine ⟨r, hr, ?_⟩
      have hlp' : p.length ≤ 4 ^ max φ.depth ψ.depth :=
        le_trans hlp (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
      have hlq' : q.length ≤ 4 ^ max φ.depth ψ.depth :=
        le_trans hlq (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
      rw [hlr]
      simp only [BoolFormula.depth, Nat.pow_succ]
      omega
  | disj φ ψ ihφ ihψ =>
      intro c hcc hco
      have hci : c⁻¹.IsCycle := hcc.inv
      have hoi : orderOf c⁻¹ = 5 := by rw [orderOf_inv]; exact hco
      obtain ⟨p, hp, hlp⟩ := ihφ c hcc hco
      obtain ⟨q, hq, hlq⟩ := ihψ c hcc hco
      let p' := BP.postMul p c⁻¹
      let q' := BP.postMul q c⁻¹
      have hp' : BP.Computes c⁻¹ p'
          (fun α => !BoolFormula.eval α φ) := by
        exact BP.Computes_not_compact hp
      have hq' : BP.Computes c⁻¹ q'
          (fun α => !BoolFormula.eval α ψ) := by
        exact BP.Computes_not_compact hq
      have hlp' : p'.length ≤ 4 ^ φ.depth := by
        simp only [p', BP.length_postMul]
        exact max_le (Nat.one_le_pow _ _ (by omega)) hlp
      have hlq' : q'.length ≤ 4 ^ ψ.depth := by
        simp only [q', BP.length_postMul]
        exact max_le (Nat.one_le_pow _ _ (by omega)) hlq
      obtain ⟨s, hs, hls⟩ :=
        BP.Computes_and5_tight hp' hci hoi hq' hci hoi hci hoi
      have h := BP.Computes_not_compact hs
      rw [inv_inv] at h
      have hfun :
          (fun α => !((!BoolFormula.eval α φ) &&
            (!BoolFormula.eval α ψ))) =
          (fun α => BoolFormula.eval α φ || BoolFormula.eval α ψ) := by
        funext α
        simp [Bool.not_and, Bool.not_not]
      rw [hfun] at h
      refine ⟨BP.postMul s (c⁻¹)⁻¹, h, ?_⟩
      have hlpMax : p'.length ≤ 4 ^ max φ.depth ψ.depth :=
        le_trans hlp' (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
      have hlqMax : q'.length ≤ 4 ^ max φ.depth ψ.depth :=
        le_trans hlq' (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
      have hls' : s.length ≤ 4 ^ (max φ.depth ψ.depth + 1) := by
        rw [hls]
        simp only [Nat.pow_succ]
        omega
      rw [BP.length_postMul]
      exact max_le (Nat.one_le_pow _ _ (by omega)) hls'

/-- **Barrington's theorem with a length bound.** Every Boolean formula `φ` is
    computed by a width-`5` permutation branching program (a nonidentity `σ ∈ S₅`
    with program-value `= σ ↔ φ` true) whose length is at most `13 ^ (size φ)`. -/
theorem barrington_representation_len (φ : BoolFormula) :
    ∃ (r : BP 5) (σ : Perm (Fin 5)), σ ≠ 1 ∧
      (∀ α, BP.eval α r = if BoolFormula.eval α φ then σ else 1) ∧
      r.length ≤ 13 ^ φ.size := by
  obtain ⟨hc, ho⟩ := isCycle_orderOf_five_of_pow (g := finRotate 5) (by decide) (by decide)
  obtain ⟨r, hr, hlr⟩ := Computes_formula_len φ (finRotate 5) hc ho
  refine ⟨r, finRotate 5, ?_, fun α => hr α, le_trans hlr (barringtonBound_le φ)⟩
  rw [Ne, ← orderOf_eq_one_iff, ho]; norm_num

/-- **Barrington's theorem, textbook finite form.** Every Boolean formula `φ`
of depth `d` is computed by a width-`5` permutation branching program of length
at most `4 ^ d`. -/
theorem barrington_representation_depth_four (φ : BoolFormula) :
    ∃ (r : BP 5) (σ : Perm (Fin 5)), σ ≠ 1 ∧
      (∀ α, BP.eval α r = if BoolFormula.eval α φ then σ else 1) ∧
      r.length ≤ 4 ^ φ.depth := by
  obtain ⟨hc, ho⟩ :=
    isCycle_orderOf_five_of_pow (g := finRotate 5) (by decide) (by decide)
  obtain ⟨r, hr, hlr⟩ :=
    Computes_formula_depth_four φ (finRotate 5) hc ho
  refine ⟨r, finRotate 5, ?_, fun α => hr α, hlr⟩
  rw [Ne, ← orderOf_eq_one_iff, ho]
  norm_num

/-- Compatibility form of the earlier depth bound. The textbook theorem
`barrington_representation_depth_four` now gives the stronger base `4`; this
corollary retains the former base-`17` API. -/
theorem barrington_representation_depth (φ : BoolFormula) :
    ∃ (r : BP 5) (σ : Perm (Fin 5)), σ ≠ 1 ∧
      (∀ α, BP.eval α r = if BoolFormula.eval α φ then σ else 1) ∧
      r.length ≤ 17 ^ φ.depth := by
  obtain ⟨r, σ, hσ, hr, hlr⟩ :=
    barrington_representation_depth_four φ
  exact ⟨r, σ, hσ, hr,
    le_trans hlr (Nat.pow_le_pow_left (by omega) φ.depth)⟩

/-- `4 ^ (log₂ n) ≤ n ^ 2`: the arithmetic specialization of the textbook
Barrington bound to logarithmic depth. -/
theorem pow_four_log_le (n : ℕ) (hn : n ≠ 0) :
    4 ^ Nat.log 2 n ≤ n ^ 2 := by
  calc
    4 ^ Nat.log 2 n = (2 ^ Nat.log 2 n) ^ 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_mul,
        Nat.mul_comm]
    _ ≤ n ^ 2 := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn) 2

/-- **Log-depth formulas have quadratic-length width-`5` programs.** A formula
of depth at most `log₂ n` compiles to a program of length at most `n²`. -/
theorem barrington_quadratic_of_log_depth (φ : BoolFormula) (n : ℕ)
    (hn : n ≠ 0) (hd : φ.depth ≤ Nat.log 2 n) :
    ∃ (r : BP 5) (σ : Perm (Fin 5)), σ ≠ 1 ∧
      (∀ α, BP.eval α r = if BoolFormula.eval α φ then σ else 1) ∧
      r.length ≤ n ^ 2 := by
  obtain ⟨r, σ, hσ, hev, hlen⟩ :=
    barrington_representation_depth_four φ
  refine ⟨r, σ, hσ, hev, ?_⟩
  calc
    r.length ≤ 4 ^ φ.depth := hlen
    _ ≤ 4 ^ Nat.log 2 n := Nat.pow_le_pow_right (by omega) hd
    _ ≤ n ^ 2 := pow_four_log_le n hn

/-- `17 ^ (log₂ n) ≤ n ^ 5`: since `17 ≤ 2⁵`, `17^{log₂ n} ≤ (2^{log₂ n})⁵ ≤ n⁵`.
    This is the arithmetic behind "logarithmic depth gives polynomial size". -/
theorem pow_seventeen_log_le (n : ℕ) (hn : n ≠ 0) : 17 ^ Nat.log 2 n ≤ n ^ 5 := by
  calc 17 ^ Nat.log 2 n ≤ 32 ^ Nat.log 2 n := Nat.pow_le_pow_left (by omega) _
    _ = (2 ^ Nat.log 2 n) ^ 5 := by
        rw [show (32 : ℕ) = 2 ^ 5 from rfl, ← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ n ^ 5 := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn) 5

/-- **`NC¹ ⟹` polynomial size (concrete form).** A formula of depth at most `log₂ n`
    is computed by a width-`5` permutation branching program of length at most
    `n ^ 5` — the polynomial-size direction of Barrington made explicit: the program
    is polynomial-size in `n` whenever the formula's depth is logarithmic. -/
theorem barrington_poly_of_log_depth (φ : BoolFormula) (n : ℕ) (hn : n ≠ 0)
    (hd : φ.depth ≤ Nat.log 2 n) :
    ∃ (r : BP 5) (σ : Perm (Fin 5)), σ ≠ 1 ∧
      (∀ α, BP.eval α r = if BoolFormula.eval α φ then σ else 1) ∧
      r.length ≤ n ^ 5 := by
  obtain ⟨r, σ, hσ, hev, hlen⟩ := barrington_representation_depth φ
  refine ⟨r, σ, hσ, hev, ?_⟩
  calc r.length ≤ 17 ^ φ.depth := hlen
    _ ≤ 17 ^ Nat.log 2 n := Nat.pow_le_pow_right (by omega) hd
    _ ≤ n ^ 5 := pow_seventeen_log_le n hn

end Complexity
