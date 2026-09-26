/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Cslib.Circuit
public import Complexitylib.Asymptotics
public import Cslib.Computability.Circuit.Boolean.Family
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
- `Complexity.SIZE_subset_cslib_SIZE`, `Complexity.cslib_SIZE_subset_SIZE` — our
  `SIZE` classes versus CSLib's De Morgan classes `Cslib.Circuits.Boolean.SIZE`
- `Complexity.PPoly_eq_cslib_PPoly` — our `PPoly` is CSLib's
  `Cslib.Circuits.Boolean.PPoly`; hence (`Complexity.exists_not_mem_PPoly`) some
  language lies outside `PPoly`

## Relation to CSLib's family-level results

CSLib states Lupanov's and Shannon's bounds for De Morgan circuit families
(`Cslib.Circuits.Boolean.exists_decides_size_le`,
`Cslib.Circuits.Boolean.exists_language_lt_size`) and derives
`Cslib.Circuits.Boolean.exists_not_mem_PPoly`. Our hard language
(`Complexity.exists_language_sliceSizeComplexity_gt`) is CSLib's, and our
`exists_not_mem_PPoly` is CSLib's through `PPoly_eq_cslib_PPoly`. The Lupanov
results here are the fan-in-two AND/OR slice form of CSLib's family bound; they
come from the per-function transfer `Complexity.lupanov_sizeComplexity`, which
absorbs the extra output gate of `Circuit.ofCslib`.

## Provenance of CSLib's family-level classes

CSLib's circuit families and the classes `Cslib.Circuits.Boolean.SIZE` and
`Cslib.Circuits.Boolean.PPoly` (with their family-level Lupanov and Shannon
bounds and `Cslib.Circuits.Boolean.exists_not_mem_PPoly`), together with
`Language.slice`, are not yet in upstream CSLib. They are pending CSLib work by
this library's author, pinned here from the integration branch of the
`SamuelSchlesinger/cslib` fork. The comparisons with them in this file are
therefore consistency checks against those definitions, not corroboration by
independently reviewed ones, and they may need revisiting if the definitions
change before merging. The counting argument behind the hard language,
`Cslib.Circuits.Boolean.Shannon.exists_hard_function`, is merged upstream
(CSLib PR #891), but the pinned version restates it for the bundled circuit
size `Circuit.size` of the pending CSLib PR #949, so the statement used here is
itself part of the pending work.
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
`n` some CSLib De Morgan circuit of size at most `n + 2 s(n) + 1` decides the
length-`n` slice of `L`. -/
theorem exists_cslib_of_mem_SIZE {L : Language} {s : ℕ → ℕ} (hL : L ∈ SIZE s) (n : ℕ) :
    ∃ c : Cslib.Circuits.Circuit Boolean.signature n 1, c.size ≤ n + 2 * s n + 1 ∧
      c.Computes Boolean.interpretation fun x _ => decide (List.ofFn x ∈ L) := by
  have h := mem_SIZE_iff_sliceSizeComplexity_le.mp hL n
  rcases n with _ | m
  · obtain ⟨c, hc, hg⟩ :=
      (Synthesis.const (n := 0) (s := inputs 0) (decide ([] ∈ L))).exists_circuit
    exact ⟨c, by omega, fun x => (hc x).trans (by simp)⟩
  · obtain ⟨c, hg, hc⟩ := Circuit.exists_cslib_of_sizeComplexity
      fun x : BitString (m + 1) => decide (List.ofFn x ∈ L)
    rw [sliceSizeComplexity_succ] at h
    exact ⟨c, by omega, hc⟩

open Classical in
/-- **`SIZE` in CSLib terms, backward.** If at every positive length `n` some
CSLib De Morgan circuit of size at most `s(n)` decides the length-`n` slice of
`L`, then `L ∈ SIZE (s + 1)`. -/
theorem mem_SIZE_of_cslib {L : Language} {s : ℕ → ℕ}
    (h : ∀ (n : ℕ) [NeZero n], ∃ c : Cslib.Circuits.Circuit Boolean.signature n 1,
      c.size ≤ s n ∧ c.Computes Boolean.interpretation fun x _ => decide (List.ofFn x ∈ L)) :
    L ∈ SIZE fun n => s n + 1 := by
  refine mem_SIZE_iff_sliceSizeComplexity_le.mpr fun n => ?_
  rcases n with _ | m
  · exact Nat.zero_le _
  · obtain ⟨c, hg, hc⟩ := h (m + 1)
    exact (Circuit.sizeComplexity_le_of_cslib c hc).trans (by omega)

open Classical in
/-- CSLib's length-`n` slice of a language is its classical characteristic
function on words of length `n`. -/
theorem slice_eq_decide (L : Language) (n : ℕ) :
    Language.slice L n = fun x => decide (List.ofFn x ∈ L) :=
  rfl

/-- **Our `SIZE` inside CSLib's.** A language with fan-in-two AND/OR circuits of
size `s(n)` has De Morgan circuits of size `n + 2 s(n) + 1`.

`Cslib.Circuits.Boolean.SIZE` comes from the author's pending CSLib work, pinned
from the integration branch of the `SamuelSchlesinger/cslib` fork, so this
inclusion is a consistency check with that definition (see the module
docstring). -/
theorem SIZE_subset_cslib_SIZE (s : ℕ → ℕ) :
    SIZE s ⊆ Cslib.Circuits.Boolean.SIZE fun n => n + 2 * s n + 1 := by
  intro L hL
  choose c hsize hc using exists_cslib_of_mem_SIZE hL
  exact ⟨c, Cslib.Circuits.CircuitFamily.decides_id_iff.mpr hc, hsize⟩

/-- **CSLib's `SIZE` inside ours.** A language with De Morgan circuits of size
`s(n)` has fan-in-two AND/OR circuits of size `s(n) + 1`.

`Cslib.Circuits.Boolean.SIZE` comes from the author's pending CSLib work, pinned
from the integration branch of the `SamuelSchlesinger/cslib` fork, so this
inclusion is a consistency check with that definition (see the module
docstring). -/
theorem cslib_SIZE_subset_SIZE (s : ℕ → ℕ) :
    Cslib.Circuits.Boolean.SIZE s ⊆ SIZE fun n => s n + 1 := by
  rintro L ⟨F, hF, hsize⟩
  exact mem_SIZE_of_cslib fun n _ =>
    ⟨F n, hsize n, Cslib.Circuits.CircuitFamily.decides_id_iff.mp hF n⟩

/-- Every natural-coefficient polynomial is bounded by `a * n ^ k + a` for some
`a` and `k`. -/
private theorem exists_eval_le_mul_pow_add (p : Polynomial ℕ) :
    ∃ a k : ℕ, ∀ n, p.eval n ≤ a * n ^ k + a := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i, p.natDegree, fun n => ?_⟩
  rw [Polynomial.eval_eq_sum_range, ← Nat.mul_add_one, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ ?_
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases i with _ | i <;> simp
  · exact (Nat.pow_le_pow_right hn hi').trans (Nat.le_succ _)

/-- **Our `P/poly` is CSLib's.** Fan-in-two AND/OR circuits with free negations
and De Morgan circuits counting every gate define the same class `P/poly`: the
two size measures agree up to `n + 2s + 1`, and CSLib's bounds `n ^ k + k` are
cofinal among polynomials.

`Cslib.Circuits.Boolean.PPoly` and the `Cslib.Circuits.Boolean.SIZE` classes it
is built from come from the author's pending CSLib work, pinned from the
integration branch of the `SamuelSchlesinger/cslib` fork and not yet reviewed
upstream. The equality is therefore a consistency check between this library's
`PPoly` and those definitions (see the module docstring). -/
theorem PPoly_eq_cslib_PPoly : PPoly = Cslib.Circuits.Boolean.PPoly := by
  apply Set.Subset.antisymm
  · intro L hL
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hL
    obtain ⟨a, k, hk⟩ := exists_eval_le_mul_pow_add (Polynomial.X + 2 * p + 1)
    refine Cslib.Circuits.Boolean.mem_PPoly_of_le (SIZE_subset_cslib_SIZE _ hp) a k a
      fun n => ?_
    simpa using hk n
  · intro L hL
    obtain ⟨k, hk⟩ := Cslib.Circuits.Boolean.mem_PPoly_iff.mp hL
    refine Set.mem_iUnion.mpr ⟨Polynomial.X ^ k + Polynomial.C (k + 1), ?_⟩
    exact SIZE_mono (fun n => by simp [add_assoc]) (cslib_SIZE_subset_SIZE _ hk)

/-- **Some language is not in `P/poly`.** This is CSLib's
`Cslib.Circuits.Boolean.exists_not_mem_PPoly`, through `PPoly_eq_cslib_PPoly`.

That theorem and `Cslib.Circuits.Boolean.PPoly` come from the author's pending
CSLib work, pinned from the integration branch of the `SamuelSchlesinger/cslib`
fork. The counting argument underneath,
`Cslib.Circuits.Boolean.Shannon.exists_hard_function`, is merged upstream, but
the pinned version is restated for the bundled circuit size of the pending CSLib
PR #949 (see the module docstring). -/
theorem exists_not_mem_PPoly : ∃ L : Language, L ∉ PPoly := by
  rw [PPoly_eq_cslib_PPoly]
  exact Cslib.Circuits.Boolean.exists_not_mem_PPoly

/-- **Lupanov's bound for languages.** For every `ε > 0` there is `N₀` such that
every language's slices of length `n ≥ N₀` have fan-in-two AND/OR size
complexity at most `(1 + ε) 2ⁿ / n`. This is the fan-in-two AND/OR form of
CSLib's family bound `Cslib.Circuits.Boolean.exists_decides_size_le`. -/
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
`(2ⁿ / n - n) / 2` at every large length `n`. The language is the one of CSLib's
family-level Shannon bound `Cslib.Circuits.Boolean.exists_language_lt_size`. -/
theorem exists_language_sliceSizeComplexity_gt :
    ∃ L : Language, ∀ᶠ n : ℕ in atTop,
      (2 ^ n / n : ℝ) < n + 2 * (sliceSizeComplexity L n : ℝ) := by
  obtain ⟨L, N₀, hL⟩ := Cslib.Circuits.Boolean.exists_language_lt_size
  have h : ∀ n, ∃ c : Cslib.Circuits.Circuit Boolean.signature n 1,
      c.Computes Boolean.interpretation (fun x _ => Language.slice L n x) ∧
        (0 < n → c.size ≤ n + 2 * sliceSizeComplexity L n) := by
    intro n
    rcases n with _ | m
    · obtain ⟨c, hc⟩ := Interpretation.IsComplete.exists_computes
        (I := Boolean.interpretation) fun x (_ : Fin 1) => Language.slice L 0 x
      exact ⟨c, hc, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨c, hg, hc⟩ := Circuit.exists_cslib_of_sizeComplexity
        fun x : BitString (m + 1) => decide (List.ofFn x ∈ L)
      exact ⟨c, hc, fun _ => hg⟩
  choose F hF hsize using h
  refine ⟨L, eventually_atTop.mpr ⟨max N₀ 1, fun n hn => ?_⟩⟩
  have hlt := hL F (Cslib.Circuits.CircuitFamily.decides_id_iff.mpr hF) n
    (le_of_max_le_left hn)
  have hle : ((F n).size : ℝ) ≤ n + 2 * (sliceSizeComplexity L n : ℝ) := by
    exact_mod_cast hsize n (by have := le_of_max_le_right hn; omega)
  exact hlt.trans_le hle

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
