/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Cslib.Circuit.Defs
public import Complexitylib.Circuits.AndOrNot
public import Complexitylib.Classes.PPoly.Defs
public import Mathlib.Basic.Real.Basic
import Complexitylib.Interop.Cslib.Circuit.Internal
import Complexitylib.Circuits.Family
import Cslib.Computability.Circuit.Boolean.Lupanov
import Cslib.Computability.Circuit.Boolean.Shannon

/-!
# Complexitylib circuits and CSLib circuits

CSLib's circuit model counts every gate of its De Morgan basis (constants,
negation, binary conjunction and disjunction) toward size. Our fan-in-two
AND/OR circuits (`Basis.andOr2`) make negation free and count their output
gates. The two sizes agree up to a factor of two and an additive `N`:

- `Circuit.ofCslib` turns a CSLib circuit of size `g` with `M` outputs into
  one of ours of size `g + M` (`Circuit.eval_ofCslib`, `Circuit.size_ofCslib`);
- `Circuit.exists_cslib` turns one of ours with `G` internal gates into a CSLib
  circuit of size at most `N + 2G + M`.

CSLib proves the sharp counting bounds for its model, and they transfer here
with different losses. Lupanov's upper bound, previously missing from this
library, transfers sharply: `Circuit.sizeComplexity` is at most
`(1 + ε) 2ⁿ / n` for large `n`. Shannon's lower bound pays the factor of two of
`Circuit.exists_cslib`: some function has `2ⁿ / n < n + 2 · sizeComplexity`,
that is, size complexity above `(2ⁿ / n - n) / 2`, about half the sharp bound
`2ⁿ / n`.

## Main results

- `Complexity.Circuit.sizeComplexity_le_of_cslib`,
  `Complexity.Circuit.exists_cslib_of_sizeComplexity` — size complexity versus
  CSLib gate counts
- `Complexity.lupanov_sizeComplexity` — every function on `n` bits has size
  complexity at most `(1 + ε) 2ⁿ / n` for large `n`
- `Complexity.exists_sizeComplexity_gt_cslib` — some function on `n` bits has
  size complexity above `(2ⁿ / n - n) / 2` for large `n`
- `Complexity.mem_PPoly_iff_cslib` — `P/poly` is exactly the class of languages
  with polynomial-size CSLib De Morgan circuits at every input length; see
  `Complexity.PPoly_eq_cslib_PPoly` for the equality with CSLib's own class
-/


public section

namespace Complexity

open Cslib.Circuits Filter Topology

namespace Circuit

/-- A single-output CSLib circuit computes `f` exactly when its only output
agrees with `f` on every input. -/
theorem cslib_computes_iff {σ : Signature} {U : Type*} {I : Interpretation σ U} {N : ℕ}
    {c : Cslib.Circuits.Circuit σ N 1} {f : (Fin N → U) → U} :
    c.Computes I (fun x _ => f x) ↔ ∀ x, c.eval I x 0 = f x := by
  simp only [Cslib.Circuits.Circuit.Computes, funext_iff, Fin.forall_fin_one]

variable {N M G : ℕ} [NeZero N]

/-- **CSLib circuits run as ours.** The translation computes what the CSLib
circuit computes. -/
theorem eval_ofCslib [NeZero M] (c : Cslib.Circuits.Circuit Boolean.signature N M)
    (x : BitString N) : (ofCslib c).eval x = c.eval Boolean.interpretation x :=
  eval_ofCslib_internal c x

/-- The translation of a CSLib circuit of size `g` with `M` outputs has size
`g + M`. -/
theorem size_ofCslib [NeZero M] (c : Cslib.Circuits.Circuit Boolean.signature N M) :
    (ofCslib c).size = c.size + M :=
  rfl

/-- **Our circuits run as CSLib's.** A fan-in-two AND/OR circuit with `G`
internal gates and `M` outputs has a CSLib De Morgan circuit of size at most
`N + 2G + M` computing the same outputs. -/
theorem exists_cslib [NeZero M] (c : Circuit Basis.andOr2 N M G) :
    ∃ c' : Cslib.Circuits.Circuit Boolean.signature N M, c'.size ≤ N + 2 * G + M ∧
      ∀ x j, c'.eval Boolean.interpretation x j = c.eval x j :=
  exists_cslib_internal c

/-- A CSLib De Morgan circuit computing `f` bounds its fan-in-two AND/OR size
complexity by its size plus one. -/
theorem sizeComplexity_le_of_cslib (c : Cslib.Circuits.Circuit Boolean.signature N 1)
    {f : BitString N → Bool} (hc : c.Computes Boolean.interpretation fun x _ => f x) :
    sizeComplexity Basis.andOr2 f ≤ c.size + 1 :=
  sizeComplexity_le (ofCslib c) f (funext fun x => by
    rw [eval_ofCslib]
    exact cslib_computes_iff.mp hc x)

/-- Every function has a CSLib De Morgan circuit of size at most
`N + 2 · sizeComplexity f`. -/
theorem exists_cslib_of_sizeComplexity (f : BitString N → Bool) :
    ∃ c : Cslib.Circuits.Circuit Boolean.signature N 1,
      c.size ≤ N + 2 * sizeComplexity Basis.andOr2 f ∧
        c.Computes Boolean.interpretation fun x _ => f x := by
  obtain ⟨G, c, hsize, hf⟩ := sizeComplexity_witness (B := Basis.andOr2) f
  obtain ⟨c', hg, hc'⟩ := exists_cslib c
  refine ⟨c', ?_, cslib_computes_iff.mpr fun x => by rw [hc' x 0, ← hf]⟩
  rw [← hsize, Circuit.size]
  omega

end Circuit

/-- **Lupanov's upper bound.** For every `ε > 0` and all sufficiently large `n`,
every Boolean function on `n` bits has fan-in-two AND/OR size complexity at
most `(1 + ε) 2ⁿ / n`. Transferred from CSLib's De Morgan bound. -/
theorem lupanov_sizeComplexity {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∀ f : BitString n → Bool,
      (Circuit.sizeComplexity Basis.andOr2 f : ℝ) ≤ (1 + ε) * 2 ^ n / n := by
  obtain ⟨N₁, h₁⟩ := Cslib.Circuits.Boolean.Lupanov.exists_circuit (ε / 2) (by positivity)
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) / 2 ^ n) atTop (𝓝 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
  obtain ⟨N₂, h₂⟩ :=
    eventually_atTop.mp (hlim.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < ε / 2)))
  refine ⟨max N₁ N₂, fun n _ hn f => ?_⟩
  obtain ⟨c, hc, hsize⟩ := h₁ n (le_of_max_le_left hn) f
  have hle := Circuit.sizeComplexity_le_of_cslib c hc
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have h1 : (1 : ℝ) ≤ ε / 2 * 2 ^ n / n := by
    have h2 : (n : ℝ) / 2 ^ n ≤ ε / 2 := h₂ n (le_of_max_le_right hn)
    rw [div_le_iff₀ (by positivity)] at h2
    rw [le_div_iff₀ hpos, one_mul]
    exact h2
  calc (Circuit.sizeComplexity Basis.andOr2 f : ℝ) ≤ (c.size : ℝ) + 1 := by exact_mod_cast hle
    _ ≤ (1 + ε / 2) * 2 ^ n / n + ε / 2 * 2 ^ n / n := add_le_add hsize h1
    _ = (1 + ε) * 2 ^ n / n := by ring

/-- **Shannon's lower bound, transferred from CSLib.** For all sufficiently
large `n`, some Boolean function on `n` bits has fan-in-two AND/OR size
complexity above `(2ⁿ / n - n) / 2`. -/
theorem exists_sizeComplexity_gt_cslib :
    ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∃ f : BitString n → Bool,
      (2 ^ n / n : ℝ) < n + 2 * (Circuit.sizeComplexity Basis.andOr2 f : ℝ) := by
  obtain ⟨N₀, h⟩ := Cslib.Circuits.Boolean.Shannon.exists_hard_function
  refine ⟨N₀, fun n _ hn => ?_⟩
  obtain ⟨f, hf⟩ := h n hn
  obtain ⟨c, hg, hc⟩ := Circuit.exists_cslib_of_sizeComplexity f
  exact ⟨f, (hf c hc).trans_le (by exact_mod_cast hg)⟩

open Classical in
/-- **`P/poly` in CSLib's circuit model.** A language is in `P/poly` exactly
when, for some polynomial `p` and every input length `n`, a CSLib De Morgan
circuit of size at most `p(n)` decides its length-`n` slice. -/
theorem mem_PPoly_iff_cslib {L : Language} :
    L ∈ PPoly ↔ ∃ p : Polynomial ℕ, ∀ n, ∃ c : Cslib.Circuits.Circuit Boolean.signature n 1,
      c.size ≤ p.eval n ∧
        c.Computes Boolean.interpretation fun x _ => decide (List.ofFn x ∈ L) := by
  constructor
  · intro hL
    obtain ⟨p, F, hdec, hsize⟩ := Set.mem_iUnion.mp hL
    have hF : ∀ n (x : BitString n), F.function n x = decide (List.ofFn x ∈ L) := by
      intro n x
      rw [← F.evalList_ofFn x]
      have hmem : List.ofFn x ∈ L ↔ F.evalList (List.ofFn x) = true := by
        rw [← hdec]
        rfl
      cases h : F.evalList (List.ofFn x) <;> simp_all
    refine ⟨Polynomial.X + 2 * p + 1, fun n => ?_⟩
    rcases n with _ | m
    · obtain ⟨c, hc, hg⟩ :=
        (Synthesis.const (n := 0) (s := inputs 0) F.emptyOutput).exists_circuit
      exact ⟨c, by simp; omega, Circuit.cslib_computes_iff.mpr fun x =>
        (Circuit.cslib_computes_iff.mp hc x).trans (hF 0 x)⟩
    · obtain ⟨c, hg, hc⟩ := Circuit.exists_cslib (F.circuit (m + 1))
      refine ⟨c, ?_, Circuit.cslib_computes_iff.mpr fun x => (hc x 0).trans (hF (m + 1) x)⟩
      have hs := hsize (m + 1)
      simp only [CircuitFamily.size, Circuit.size] at hs
      simp
      omega
  · rintro ⟨p, h⟩
    choose c hg hc using h
    let F : CircuitFamily Basis.andOr2 :=
      { emptyOutput := decide ([] ∈ L)
        circuits := fun n _ => ⟨(c n).size, Circuit.ofCslib (c n)⟩ }
    have hF : ∀ n (x : BitString n), F.function n x = decide (List.ofFn x ∈ L) := by
      intro n x
      rcases n with _ | m
      · simp [F, CircuitFamily.function]
      · show (Circuit.ofCslib (c (m + 1))).eval x 0 = _
        rw [Circuit.eval_ofCslib]
        exact Circuit.cslib_computes_iff.mp (hc (m + 1)) x
    refine Set.mem_iUnion.mpr ⟨p + 1, F, ?_, fun n => ?_⟩
    · ext y
      show F.function y.length y.get = true ↔ y ∈ L
      rw [hF, List.ofFn_get, decide_eq_true_iff]
    · rcases n with _ | m
      · simp [CircuitFamily.size]
      · show (c (m + 1)).size + 1 ≤ (p + 1).eval (m + 1)
        simpa using hg (m + 1)

end Complexity
