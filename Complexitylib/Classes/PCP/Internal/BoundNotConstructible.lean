/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Defs
public import Complexitylib.Classes.PCP.Internal.LengthMod

/-!
# The randomness bound has to be constructible

`Complexitylib.Classes.PCP` defines `PCP r q` for an arbitrary pair of functions
`r q : ℕ → ℕ`, with no requirement that either be computable. That makes the
union over all `r =O Nat.log 2` far too large to be `NP`, and this module shows
it: for *every* set `A ⊆ ℕ`, the language of inputs whose length lies in `A`
belongs to the union.

One fixed verifier does it for all `A` at once. It queries nothing, so its
transcript is `pair (pair x ρ) []`, of length `4|x| + 2|ρ| + 6`; accepting when
that is divisible by four means accepting exactly when `|ρ| = 1`. Feeding it one
coin when `|x| ∈ A` and none otherwise makes it accept certainly on `A` and
never off it. The bound `r` used to do that is the indicator of `A`, which is
`O(1)` and so certainly `O(log n)` — but it is as uncomputable as `A` is.

Since `NP` is countable and there are `2^𝔠` sets `A`, the union cannot equal
`NP`: the `⊆ NP` half of the statement is false as written. The remedy is the
usual one, to require the bounds to be constructible; the `NP ⊆ PCP` half — the
Dinur half — is untouched.

## Main definitions

- `Complexity.coinLenVerifier` — the verifier that only counts its coins

## Main results

- `Complexity.lengthLang_mem_iUnion_PCP` — every length-determined language,
  computable or not, is in the union
-/

@[expose] public section

namespace Complexity

/-- A verifier that reads nothing and accepts exactly when it was given one
coin. -/
def coinLenVerifier : PCPVerifier where
  positions := fun _ _ => []
  positions_mem :=
    ⟨fun _ => DataEncode.bitstringEncode ([] : List ℕ), constFn_mem_FP _, fun _ _ => rfl⟩
  verdict := lenMod4
  verdict_mem := lenMod4_mem_P

@[simp] theorem positions_coinLenVerifier (x r : List Bool) :
    coinLenVerifier.positions x r = [] := rfl

theorem length_delimit (w : List Bool) : (delimit w).length = 2 * w.length + 2 := by
  rw [delimit, List.length_append, List.length_flatMap]
  simp [Nat.mul_comm]

theorem length_transcript (x ρ : List Bool) :
    (pair (pair x ρ) []).length = 4 * x.length + 2 * ρ.length + 6 := by
  rw [pair, List.append_nil, length_delimit, pair, List.length_append, length_delimit]
  ring

/-- **The verifier accepts exactly on one coin.** -/
theorem accepts_coinLenVerifier_iff (x π ρ : List Bool) :
    coinLenVerifier.Accepts x π ρ ↔ (2 * ρ.length + 2) % 4 = 0 := by
  rw [PCPVerifier.Accepts, positions_coinLenVerifier]
  show pair (pair x ρ) [] ∈ lenMod4 ↔ _
  rw [lenMod4]
  show (pair (pair x ρ) []).length % 4 = 0 ↔ _
  rw [length_transcript]
  constructor
  · intro h; omega
  · intro h; omega

theorem accepts_of_length_one {x π ρ : List Bool} (h : ρ.length = 1) :
    coinLenVerifier.Accepts x π ρ := by
  rw [accepts_coinLenVerifier_iff, h]

theorem not_accepts_of_length_zero {x π ρ : List Bool} (h : ρ.length = 0) :
    ¬ coinLenVerifier.Accepts x π ρ := by
  rw [accepts_coinLenVerifier_iff, h]
  decide

/-! ### Every length-determined language is in the union -/

open Classical in
/-- The indicator of `A`, used as a randomness bound. -/
noncomputable def indicatorBound (A : Set ℕ) : ℕ → ℕ := fun n => if n ∈ A then 1 else 0

theorem indicatorBound_le_one (A : Set ℕ) (n : ℕ) : indicatorBound A n ≤ 1 := by
  rw [indicatorBound]
  split <;> norm_num

theorem indicatorBound_bigO (A : Set ℕ) : indicatorBound A =O Nat.log 2 := by
  rw [BigO]
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hlog : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn
  have h1 : (indicatorBound A n : ℝ) ≤ 1 := by
    exact_mod_cast indicatorBound_le_one A n
  have h2 : (1 : ℝ) ≤ (Nat.log 2 n : ℝ) := by exact_mod_cast hlog
  rw [Real.norm_natCast, Real.norm_natCast, one_mul]
  linarith

/-- **The union of `PCP` classes contains every length-determined language.**
Since `A` is arbitrary it may be uncomputable, so the union is not contained in
`NP`. -/
theorem lengthLang_mem_iUnion_PCP (A : Set ℕ) :
    {x : List Bool | x.length ∈ A} ∈
      ⋃ (r : ℕ → ℕ) (_ : r =O Nat.log 2) (q : ℕ → ℕ) (_ : q =O fun _ => 1), PCP r q := by
  classical
  refine Set.mem_iUnion.2 ⟨indicatorBound A, Set.mem_iUnion.2 ⟨indicatorBound_bigO A,
    Set.mem_iUnion.2 ⟨fun _ => 0, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩⟩⟩
  · rw [BigO]
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards with n
    norm_num
  refine ⟨coinLenVerifier, fun x r => by simp, ?_, ?_⟩
  · intro x hx
    refine ⟨[], ?_⟩
    have hxA : x.length ∈ A := hx
    have hr : indicatorBound A x.length = 1 := by
      rw [indicatorBound]
      exact ite_eq_left hxA
    rw [hr]
    have huniv : coinLenVerifier.acceptEvent 1 x [] = Finset.univ := by
      refine Finset.eq_univ_iff_forall.2 fun ρ => ?_
      rw [PCPVerifier.acceptEvent, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, accepts_of_length_one (by simp)⟩
    rw [huniv, eventProb, Finset.card_univ, card_finArrowBool]
    norm_num
  · intro x hx π
    have hxA : x.length ∉ A := hx
    have hr : indicatorBound A x.length = 0 := by
      rw [indicatorBound]
      exact ite_eq_right hxA
    rw [hr]
    have hempty : coinLenVerifier.acceptEvent 0 x π = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.2 fun ρ hρ => ?_
      rw [PCPVerifier.acceptEvent, Finset.mem_filter] at hρ
      exact not_accepts_of_length_zero (by simp) hρ.2
    rw [hempty, eventProb]
    norm_num

end Complexity
