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

- `Circuit.ofCslib` turns a CSLib circuit with `g` gates and `M` outputs into
  one of ours of size `g + M` (`Circuit.eval_ofCslib`, `Circuit.size_ofCslib`);
- `Circuit.exists_cslib` turns one of ours with `G` internal gates into a CSLib
  circuit with at most `N + 2G + M` gates.

CSLib proves the sharp counting bounds for its model, so they transfer here. In
particular Lupanov's upper bound, previously missing from this library, now
holds for `Circuit.sizeComplexity`.

## Main results

- `Complexity.Circuit.sizeComplexity_le_of_cslib`,
  `Complexity.Circuit.exists_cslib_of_sizeComplexity` — size complexity versus
  CSLib gate counts
- `Complexity.lupanov_sizeComplexity` — every function on `n` bits has size
  complexity at most `(1 + ε) 2ⁿ / n` for large `n`
- `Complexity.exists_sizeComplexity_gt_cslib` — some function on `n` bits has
  size complexity above `(2ⁿ / n - n) / 2` for large `n`
- `Complexity.mem_PPoly_iff_cslib` — `P/poly` is exactly the class of languages
  with polynomial-size CSLib De Morgan circuits at every input length
-/


public section

namespace Complexity

open Cslib.Circuits Filter Topology

namespace Circuit

variable {N M G g : ℕ} [NeZero N]

/-- **CSLib circuits run as ours.** The translation computes what the CSLib
circuit computes. -/
theorem eval_ofCslib [NeZero M] (c : Cslib.Circuits.Circuit Boolean.signature N g M)
    (x : BitString N) : (ofCslib c).eval x = c.eval Boolean.interpretation x :=
  eval_ofCslib_internal c x

/-- The translation of a CSLib circuit with `g` gates and `M` outputs has size
`g + M`. -/
theorem size_ofCslib [NeZero M] (c : Cslib.Circuits.Circuit Boolean.signature N g M) :
    (ofCslib c).size = g + M :=
  rfl

/-- **Our circuits run as CSLib's.** A fan-in-two AND/OR circuit with `G`
internal gates and `M` outputs has a CSLib De Morgan circuit with at most
`N + 2G + M` gates computing the same outputs. -/
theorem exists_cslib [NeZero M] (c : Circuit Basis.andOr2 N M G) :
    ∃ g ≤ N + 2 * G + M, ∃ c' : Cslib.Circuits.Circuit Boolean.signature N g M,
      ∀ x j, c'.eval Boolean.interpretation x j = c.eval x j :=
  exists_cslib_internal c

/-- A CSLib De Morgan circuit with `g` gates computing `f` bounds its fan-in-two
AND/OR size complexity by `g + 1`. -/
theorem sizeComplexity_le_of_cslib (c : Cslib.Circuits.Circuit Boolean.signature N g 1)
    {f : BitString N → Bool} (hc : c.Computes Boolean.interpretation f) :
    sizeComplexity Basis.andOr2 f ≤ g + 1 :=
  sizeComplexity_le (ofCslib c) f (funext fun x => by rw [eval_ofCslib]; exact hc x)

/-- Every function has a CSLib De Morgan circuit with at most
`N + 2 · sizeComplexity f` gates. -/
theorem exists_cslib_of_sizeComplexity (f : BitString N → Bool) :
    ∃ g ≤ N + 2 * sizeComplexity Basis.andOr2 f,
      ∃ c : Cslib.Circuits.Circuit Boolean.signature N g 1,
        c.Computes Boolean.interpretation f := by
  obtain ⟨G, c, hsize, hf⟩ := sizeComplexity_witness (B := Basis.andOr2) f
  obtain ⟨g, hg, c', hc'⟩ := exists_cslib c
  refine ⟨g, ?_, c', fun x => by rw [hc' x 0, ← hf]⟩
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
  obtain ⟨g, c, hc, hsize⟩ := h₁ n (le_of_max_le_left hn) f
  have hle := Circuit.sizeComplexity_le_of_cslib c hc
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have h1 : (1 : ℝ) ≤ ε / 2 * 2 ^ n / n := by
    have h2 : (n : ℝ) / 2 ^ n ≤ ε / 2 := h₂ n (le_of_max_le_right hn)
    rw [div_le_iff₀ (by positivity)] at h2
    rw [le_div_iff₀ hpos, one_mul]
    exact h2
  calc (Circuit.sizeComplexity Basis.andOr2 f : ℝ) ≤ (g : ℝ) + 1 := by exact_mod_cast hle
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
  obtain ⟨g, hg, c, hc⟩ := Circuit.exists_cslib_of_sizeComplexity f
  refine ⟨f, (hf c hc).trans_le ?_⟩
  show (g : ℝ) ≤ _
  exact_mod_cast hg

open Classical in
/-- **`P/poly` in CSLib's circuit model.** A language is in `P/poly` exactly
when, for some polynomial `p` and every input length `n`, a CSLib De Morgan
circuit with at most `p(n)` gates decides its length-`n` slice. -/
theorem mem_PPoly_iff_cslib {L : Language} :
    L ∈ PPoly ↔ ∃ p : Polynomial ℕ, ∀ n, ∃ g ≤ p.eval n,
      ∃ c : Cslib.Circuits.Circuit Boolean.signature n g 1,
        c.Computes Boolean.interpretation fun x => decide (List.ofFn x ∈ L) := by
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
    · obtain ⟨g, hg, c, hc⟩ :=
        (Synthesis.const (n := 0) (s := inputs 0) F.emptyOutput).exists_circuit
      exact ⟨g, by simp; omega, c, fun x => (hc x).trans (hF 0 x)⟩
    · obtain ⟨g, hg, c, hc⟩ := Circuit.exists_cslib (F.circuit (m + 1))
      refine ⟨g, ?_, c, fun x => (hc x 0).trans (hF (m + 1) x)⟩
      have hs := hsize (m + 1)
      simp only [CircuitFamily.size, Circuit.size] at hs
      simp
      omega
  · rintro ⟨p, h⟩
    choose g hg c hc using h
    let F : CircuitFamily Basis.andOr2 :=
      { emptyOutput := decide ([] ∈ L)
        circuits := fun n _ => ⟨g n, Circuit.ofCslib (c n)⟩ }
    have hF : ∀ n (x : BitString n), F.function n x = decide (List.ofFn x ∈ L) := by
      intro n x
      rcases n with _ | m
      · simp [F, CircuitFamily.function]
      · show (Circuit.ofCslib (c (m + 1))).eval x 0 = _
        rw [Circuit.eval_ofCslib]
        exact hc (m + 1) x
    refine Set.mem_iUnion.mpr ⟨p + 1, F, ?_, fun n => ?_⟩
    · ext y
      show F.function y.length y.get = true ↔ y ∈ L
      rw [hF, List.ofFn_get, decide_eq_true_iff]
    · rcases n with _ | m
      · simp [CircuitFamily.size]
      · show g (m + 1) + 1 ≤ (p + 1).eval (m + 1)
        simpa using hg (m + 1)

end Complexity
