/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Cslib.Circuit
public import Complexitylib.Asymptotics
import Complexitylib.Classes.PPoly
import Complexitylib.Circuits.Family
import Cslib.Computability.Circuit.Boolean.Lupanov
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Circuit size classes and CSLib circuits

This module lifts the per-function bridge of `Complexitylib.Interop.Cslib.Circuit`
to the language classes `SIZE s`. The key device is `sliceSizeComplexity L`, the
fan-in-two AND/OR size complexity of each length slice of `L`: a language lies in
`SIZE s` exactly when these slice complexities are pointwise below `s`.

## Main results

- `Complexity.mem_SIZE_iff_sliceSizeComplexity_le` — `SIZE s` membership is a
  pointwise bound on slice size complexity
- `Complexity.exists_cslib_of_mem_SIZE`, `Complexity.mem_SIZE_of_cslib` — `SIZE`
  in CSLib's De Morgan circuit model
- `Complexity.lupanov_sliceSizeComplexity`,
  `Complexity.exists_mem_SIZE_bigO_two_pow_div` — every language has circuits of
  size `(1 + ε) 2ⁿ / n` for large `n`, hence of size `O(2ⁿ / n)`
- `Complexity.exists_language_not_mem_SIZE` — some language is outside `SIZE s`
  whenever `n + 2 s(n) ≤ 2ⁿ / n` eventually; in particular
  (`Complexity.exists_language_not_mem_SIZE_littleO`) whenever `s = o(2ⁿ / n)`
-/


public section

namespace Complexity

open Cslib.Circuits Filter Topology

open Classical in
/-- The fan-in-two AND/OR size complexity of the length-`n` slice of `L`, with
value `0` on the empty length (which circuit families answer by a stored bit). -/
@[expose] noncomputable def sliceSizeComplexity (L : Language) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Circuit.sizeComplexity Basis.andOr2
      fun x : BitString (n + 1) => decide (List.ofFn x ∈ L)

open Classical in
/-- At a positive length, `sliceSizeComplexity` is the size complexity of the
slice. -/
theorem sliceSizeComplexity_succ (L : Language) (m : ℕ) :
    sliceSizeComplexity L (m + 1) = Circuit.sizeComplexity Basis.andOr2
      fun x : BitString (m + 1) => decide (List.ofFn x ∈ L) :=
  rfl

open Classical in
/-- **`SIZE` via slice complexity.** A language lies in `SIZE s` exactly when
every length slice has fan-in-two AND/OR size complexity at most `s n`. -/
theorem mem_SIZE_iff_sliceSizeComplexity_le {L : Language} {s : ℕ → ℕ} :
    L ∈ SIZE s ↔ ∀ n, sliceSizeComplexity L n ≤ s n := by
  constructor
  · rintro ⟨F, hdec, hsize⟩ n
    have hF : ∀ n (x : BitString n), F.function n x = decide (List.ofFn x ∈ L) := by
      intro n x
      rw [← F.evalList_ofFn x]
      have hmem : List.ofFn x ∈ L ↔ F.evalList (List.ofFn x) = true := by
        rw [← hdec]
        rfl
      cases h : F.evalList (List.ofFn x) <;> simp_all
    rcases n with _ | m
    · exact Nat.zero_le _
    · exact (Circuit.sizeComplexity_le (F.circuit (m + 1)) _
        (funext fun x => hF (m + 1) x)).trans (hsize (m + 1))
  · intro h
    have hw := fun (n : ℕ) [NeZero n] => Circuit.sizeComplexity_witness
      (B := Basis.andOr2) fun x : BitString n => decide (List.ofFn x ∈ L)
    choose G c hc hf using hw
    let F : CircuitFamily Basis.andOr2 :=
      { emptyOutput := decide ([] ∈ L)
        circuits := fun n _ => ⟨G n, c n⟩ }
    have hF : ∀ n (x : BitString n), F.function n x = decide (List.ofFn x ∈ L) := by
      intro n x
      rcases n with _ | m
      · simp [F, CircuitFamily.function]
      · exact congrFun (hf (m + 1)) x
    refine ⟨F, ?_, fun n => ?_⟩
    · ext y
      show F.function y.length y.get = true ↔ y ∈ L
      rw [hF, List.ofFn_get, decide_eq_true_iff]
    · rcases n with _ | m
      · simp [CircuitFamily.size]
      · show (c (m + 1)).size ≤ s (m + 1)
        rw [hc]
        exact h (m + 1)

/-- Every language lies in `SIZE` of its own slice complexity, the least size
bound it admits. -/
theorem mem_SIZE_sliceSizeComplexity (L : Language) : L ∈ SIZE (sliceSizeComplexity L) :=
  mem_SIZE_iff_sliceSizeComplexity_le.mpr fun _ => le_rfl

open Classical in
/-- **`SIZE` in CSLib terms, forward.** If `L ∈ SIZE s`, then at every length
`n` some CSLib De Morgan circuit with at most `n + 2 s(n) + 1` gates decides the
length-`n` slice of `L`. -/
theorem exists_cslib_of_mem_SIZE {L : Language} {s : ℕ → ℕ} (hL : L ∈ SIZE s) (n : ℕ) :
    ∃ g ≤ n + 2 * s n + 1, ∃ c : Cslib.Circuits.Circuit Boolean.signature n g 1,
      c.Computes Boolean.interpretation fun x => decide (List.ofFn x ∈ L) := by
  have h := mem_SIZE_iff_sliceSizeComplexity_le.mp hL n
  rcases n with _ | m
  · obtain ⟨g, hg, c, hc⟩ :=
      (Synthesis.const (n := 0) (s := inputs 0) (decide ([] ∈ L))).exists_circuit
    exact ⟨g, by omega, c, fun x => (hc x).trans (by simp)⟩
  · obtain ⟨g, hg, c, hc⟩ := Circuit.exists_cslib_of_sizeComplexity
      fun x : BitString (m + 1) => decide (List.ofFn x ∈ L)
    rw [sliceSizeComplexity_succ] at h
    exact ⟨g, by omega, c, hc⟩

open Classical in
/-- **`SIZE` in CSLib terms, backward.** If at every positive length `n` some
CSLib De Morgan circuit with at most `s(n)` gates decides the length-`n` slice of
`L`, then `L ∈ SIZE (s + 1)`. -/
theorem mem_SIZE_of_cslib {L : Language} {s : ℕ → ℕ}
    (h : ∀ (n : ℕ) [NeZero n], ∃ g ≤ s n,
      ∃ c : Cslib.Circuits.Circuit Boolean.signature n g 1,
        c.Computes Boolean.interpretation fun x => decide (List.ofFn x ∈ L)) :
    L ∈ SIZE fun n => s n + 1 := by
  refine mem_SIZE_iff_sliceSizeComplexity_le.mpr fun n => ?_
  rcases n with _ | m
  · exact Nat.zero_le _
  · obtain ⟨g, hg, c, hc⟩ := h (m + 1)
    exact (Circuit.sizeComplexity_le_of_cslib c hc).trans (by omega)

/-- **Lupanov's bound for languages.** For every `ε > 0` there is `N₀` such that
every language's slices of length `n ≥ N₀` have fan-in-two AND/OR size
complexity at most `(1 + ε) 2ⁿ / n`. -/
theorem lupanov_sliceSizeComplexity {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (L : Language) (n : ℕ), N₀ ≤ n →
      (sliceSizeComplexity L n : ℝ) ≤ (1 + ε) * 2 ^ n / n := by
  classical
  obtain ⟨N₀, h⟩ := lupanov_sizeComplexity hε
  refine ⟨max N₀ 1, fun L n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [sliceSizeComplexity_succ]
  exact h (m + 1) (le_of_max_le_left hn) _

/-- **Every language has near-optimal circuits.** For every `ε > 0`, every
language lies in `SIZE s` for some `s` with `s(n) ≤ (1 + ε) 2ⁿ / n` for all large
`n`. -/
theorem exists_mem_SIZE_lupanov {ε : ℝ} (hε : 0 < ε) (L : Language) :
    ∃ s : ℕ → ℕ, (∀ᶠ n : ℕ in atTop, (s n : ℝ) ≤ (1 + ε) * 2 ^ n / n) ∧ L ∈ SIZE s := by
  obtain ⟨N₀, h⟩ := lupanov_sliceSizeComplexity hε
  exact ⟨sliceSizeComplexity L, eventually_atTop.mpr ⟨N₀, h L⟩,
    mem_SIZE_sliceSizeComplexity L⟩

/-- **Every language has circuits of size `O(2ⁿ / n)`** (with `2ⁿ / n` the
natural-number quotient). -/
theorem exists_mem_SIZE_bigO_two_pow_div (L : Language) :
    ∃ s : ℕ → ℕ, s =O (fun n => 2 ^ n / n) ∧ L ∈ SIZE s := by
  refine ⟨sliceSizeComplexity L, ?_, mem_SIZE_sliceSizeComplexity L⟩
  obtain ⟨N₀, h⟩ := lupanov_sliceSizeComplexity (ε := 1) one_pos
  refine Asymptotics.IsBigO.of_bound 4 (eventually_atTop.mpr ⟨max N₀ 1, fun n hn => ?_⟩)
  have h1 := h L n (le_of_max_le_left hn)
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hfloor : (2 ^ n / n : ℝ) < ((2 ^ n / n : ℕ) : ℝ) + 1 := by
    have := Nat.lt_floor_add_one ((2 ^ n : ℝ) / n)
    rw [show ((2 : ℝ) ^ n / n) = ((2 ^ n : ℕ) : ℝ) / (n : ℕ) by push_cast; rfl,
      Nat.floor_div_eq_div] at this
    push_cast at this
    exact this
  have hge : 1 ≤ 2 ^ n / n := (Nat.one_le_div_iff (by omega)).mpr Nat.lt_two_pow_self.le
  have hge' : (1 : ℝ) ≤ ((2 ^ n / n : ℕ) : ℝ) := by exact_mod_cast hge
  simp only [Real.norm_natCast]
  calc (sliceSizeComplexity L n : ℝ) ≤ (1 + 1) * 2 ^ n / n := h1
    _ = 2 * (2 ^ n / n) := by ring
    _ ≤ 2 * (((2 ^ n / n : ℕ) : ℝ) + 1) := by linarith
    _ ≤ 4 * ((2 ^ n / n : ℕ) : ℝ) := by linarith

open Classical in
/-- **A hard language.** Some language has slice size complexity above
`(2ⁿ / n - n) / 2` at every large length `n`. -/
theorem exists_language_sliceSizeComplexity_gt :
    ∃ L : Language, ∀ᶠ n : ℕ in atTop,
      (2 ^ n / n : ℝ) < n + 2 * (sliceSizeComplexity L n : ℝ) := by
  obtain ⟨N₀, h⟩ := exists_sizeComplexity_gt_cslib
  have h' : ∀ m : ℕ, ∃ f : BitString (m + 1) → Bool, N₀ ≤ m + 1 →
      (2 : ℝ) ^ (m + 1) / ((m + 1 : ℕ) : ℝ) <
        ((m + 1 : ℕ) : ℝ) + 2 * (Circuit.sizeComplexity Basis.andOr2 f : ℝ) := by
    intro m
    by_cases hm : N₀ ≤ m + 1
    · obtain ⟨f, hf⟩ := h (m + 1) hm
      exact ⟨f, fun _ => hf⟩
    · exact ⟨fun _ => false, fun h => absurd h hm⟩
  choose f hf using h'
  let F : BoolFunFamily := fun n => match n with
    | 0 => fun _ => false
    | m + 1 => f m
  refine ⟨F.toLanguage, eventually_atTop.mpr ⟨max N₀ 1, fun n hn => ?_⟩⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hslice : (fun x : BitString (m + 1) => decide (List.ofFn x ∈ F.toLanguage)) = f m := by
    funext x
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact BoolFunFamily.mem_toLanguage_toList (f := F) x
  rw [sliceSizeComplexity_succ, hslice]
  exact hf m (le_of_max_le_left hn)

/-- **Hard languages outside small `SIZE` classes.** Some language lies outside
`SIZE s` for every `s` with `n + 2 s(n) ≤ 2ⁿ / n` for all large `n`. -/
theorem exists_language_not_mem_SIZE :
    ∃ L : Language, ∀ s : ℕ → ℕ,
      (∀ᶠ n : ℕ in atTop, (n : ℝ) + 2 * s n ≤ 2 ^ n / n) → L ∉ SIZE s := by
  obtain ⟨L, hL⟩ := exists_language_sliceSizeComplexity_gt
  refine ⟨L, fun s hs hmem => ?_⟩
  have hle := mem_SIZE_iff_sliceSizeComplexity_le.mp hmem
  obtain ⟨n, h1, h2⟩ := (hL.and hs).exists
  have : (sliceSizeComplexity L n : ℝ) ≤ s n := by exact_mod_cast hle n
  linarith

/-- **`SIZE(o(2ⁿ / n))` misses a language.** Some language lies outside `SIZE s`
for every `s = o(2ⁿ / n)` (with `2ⁿ / n` the natural-number quotient). -/
theorem exists_language_not_mem_SIZE_littleO :
    ∃ L : Language, ∀ s : ℕ → ℕ, s =o (fun n => 2 ^ n / n) → L ∉ SIZE s := by
  obtain ⟨L, hL⟩ := exists_language_not_mem_SIZE
  refine ⟨L, fun s hs => hL s ?_⟩
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 / 2 ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 2)
  have h1 := hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have h2 := Asymptotics.IsLittleO.bound hs (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [h1, h2, eventually_ge_atTop 1] with n hn1 hn2 hn3
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn3
  have hdiv : ((2 ^ n / n : ℕ) : ℝ) ≤ 2 ^ n / n := by
    have := Nat.cast_div_le (α := ℝ) (m := 2 ^ n) (n := n)
    push_cast at this
    exact this
  simp only [Real.norm_natCast] at hn2
  rw [div_le_iff₀ (by positivity)] at hn1
  have hsq : (n : ℝ) ≤ 1 / 2 * (2 ^ n / n) := by
    rw [show (1 : ℝ) / 2 * (2 ^ n / n) = (1 / 2 * 2 ^ n) / n by ring, le_div_iff₀ hpos]
    nlinarith [hn1]
  linarith

end Complexity
