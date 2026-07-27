/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.UTM.Diagonal
public import Complexitylib.Models.TuringMachine.UTM.Universal
public import Complexitylib.Classes.Containments

/-!
# The deterministic time hierarchy theorem (weak form)

**Arora–Barak Theorem 3.1** (weak form). If `g` is clock-constructible and
`(f(n) + n + 1)² = o(g(n))`, then some language is decidable in time
`O((n + 1)² · (g n + 1))` but not in time `O(f)`.

The witness is the diagonal language `diagLang clk` of the diagonalizer
`diagTM clk` built from a clock-constructibility witness `clk` for `g`:

* **Upper bound** — `diagTM clk` itself decides `diagLang clk` within
  `diagTime C g`, which `diagTime_le_poly` bounds pointwise by
  `(C + 786) · (n + 1)² · (g n + 1)`.
* **Lower bound** — if some `TM k` decided `diagLang clk` in time `O(f)`,
  the single-tape reduction would give a decider `M₁ : TM 1` at quadratic
  cost, and padding its description `encodeDesc (descOfTM M₁)` with junk
  produces an input `x` long enough that the simulation budget
  `16(k+1)(f₀ |x| + |x| + 1)²` falls below `g |x|`. On such an `x` the
  diagonalizer flips `M₁`'s verdict on `x` itself (`diagTM_flips`) —
  contradiction.

## Main results

  threshold from a big-O bound
- `time_hierarchy_weak` — the separation, existential form
- `time_hierarchy_weak_ssubset` — the separation as a strict inclusion
  `DTIME f ⊂ DTIME ((n + 1)² · (g n + 1))`
- `DTIME_pow_ssubset` — concrete polynomial corollary:
  `DTIME((n + 1)^a) ⊂ DTIME((n + 1)^(2a + 5))` for `a ≥ 1`
-/

@[expose] public section

namespace Complexity

open Asymptotics Filter Complexity

-- ════════════════════════════════════════════════════════════════════════
-- Bridges: big-O / little-o versus pointwise bounds
-- ════════════════════════════════════════════════════════════════════════


-- ════════════════════════════════════════════════════════════════════════
-- The hierarchy theorem
-- ════════════════════════════════════════════════════════════════════════

/-- **The deterministic time hierarchy theorem** (weak form, AB Theorem
    3.1). For clock-constructible `g ≥ 1` with `(f n + n + 1)² = o(g n)`,
    there is a language decidable in time `O((n + 1)² · (g n + 1))` but not
    in time `O(f)`. The `(·)²` slack absorbs the single-tape reduction; the
    `(n + 1)²` factor is the universal machine's per-step cost. -/
theorem time_hierarchy_weak {f g : ℕ → ℕ}
    (hg : TM.ClockConstructible g) (hg1 : ∀ n, 1 ≤ g n)
    (hfg : Complexity.LittleO (fun n => (f n + n + 1) ^ 2) g) :
    ∃ L : Language, L ∈ DTIME (fun n => (n + 1) ^ 2 * (g n + 1)) ∧
      L ∉ DTIME f := by
  obtain ⟨clk, C, hclk⟩ := TM.clockConstructible_iff.mp hg
  refine ⟨TM.diagLang clk, ⟨8, TM.diagTM clk, TM.diagTime C g,
    TM.diagTM_decidesInTime clk C g hclk hg1,
    (BigO.of_le (TM.diagTime_le_poly C g)).trans
      (BigO.const_mul_left (C + 786) (BigO.refl _))⟩, ?_⟩
  intro hL
  -- Step 1: a hypothetical O(f) decider, reduced to a single tape.
  obtain ⟨k, M, f₀, hM, hf₀⟩ := hL
  obtain ⟨M₁, hM₁⟩ := TM.exists_singleTape_decidesInTime M hM
  have hwf := TM.descOfTM_wf M₁
  -- Step 3: constants — f₀ ≤ c·f eventually, and the scaled square ≤ g.
  obtain ⟨c, N₀, hc⟩ := Complexity.BigO.exists_nat_bound hf₀
  obtain ⟨N₁, hN₁⟩ := hfg.nat_mul_le (16 * (k + 1) * (c + 1) ^ 2)
  -- Step 4: the padded diagonal input.
  set x : List Bool :=
    encodeDesc (TM.descOfTM M₁) ++ List.replicate (N₀ + N₁) false with hxdef
  have hxlen : x.length = (encodeDesc (TM.descOfTM M₁)).length + (N₀ + N₁) := by
    rw [hxdef]; simp
  -- Step 5: the padded description is well-formed for the interpreter.
  have hterm : TM.UTMBody.TerminatedRegion x :=
    TM.UTMBody.terminatedRegion_encodeDesc hwf
      (TM.UTMBody.descOfTM_entries_ne_nil M₁) (List.replicate (N₀ + N₁) false)
  -- Step 2: the decoded machine still decides `diagLang clk`.
  have hdec : (decodeDesc x).toTM.DecidesInTime (TM.diagLang clk)
      (NTM.singleTapeSimTime k f₀) := by
    rw [hxdef, decodeDesc_encodeDesc_append hwf]
    exact TM.descOfTM_decidesInTime M₁ hM₁
  -- Step 6: run it on `x` itself; the budget falls below the clock.
  obtain ⟨mcF, t', ht', hrun, hhalt, hmem, hnmem⟩ := hdec x
  have harith : ∀ n, N₀ ≤ n → N₁ ≤ n → NTM.singleTapeSimTime k f₀ n ≤ g n := by
    intro n hn₀ hn₁
    have h1 : f₀ n ≤ c * f n := hc n hn₀
    have h2 : f₀ n + n + 1 ≤ (c + 1) * (f n + n + 1) := by nlinarith
    have h3 : (f₀ n + n + 1) ^ 2 ≤ (c + 1) ^ 2 * (f n + n + 1) ^ 2 :=
      calc (f₀ n + n + 1) ^ 2
          ≤ ((c + 1) * (f n + n + 1)) ^ 2 := Nat.pow_le_pow_left h2 2
        _ = (c + 1) ^ 2 * (f n + n + 1) ^ 2 := mul_pow ..
    calc NTM.singleTapeSimTime k f₀ n
        = 16 * (k + 1) * (f₀ n + n + 1) ^ 2 := rfl
      _ ≤ 16 * (k + 1) * ((c + 1) ^ 2 * (f n + n + 1) ^ 2) :=
          Nat.mul_le_mul_left _ h3
      _ = 16 * (k + 1) * (c + 1) ^ 2 * (f n + n + 1) ^ 2 := (mul_assoc ..).symm
      _ ≤ g n := hN₁ n hn₁
  have hT : t' ≤ g x.length :=
    le_trans ht' (harith x.length (by omega) (by omega))
  -- Step 7: the diagonal flip contradicts the decider's own verdict.
  have hflip :=
    TM.diagTM_flips_of_halts clk C g hclk x hterm t' mcF hT hrun hhalt
  by_cases hxmem : x ∈ TM.diagLang clk
  · exact hflip.mp hxmem (hmem hxmem)
  · exact hxmem (hflip.mpr (by rw [hnmem hxmem]; decide))

/-- **The time hierarchy theorem as a strict inclusion**:
    `DTIME f ⊂ DTIME ((n + 1)² · (g n + 1))` under the same hypotheses. -/
theorem time_hierarchy_weak_ssubset {f g : ℕ → ℕ}
    (hg : TM.ClockConstructible g) (hg1 : ∀ n, 1 ≤ g n)
    (hfg : Complexity.LittleO (fun n => (f n + n + 1) ^ 2) g) :
    DTIME f ⊂ DTIME (fun n => (n + 1) ^ 2 * (g n + 1)) := by
  obtain ⟨L, hLmem, hLnot⟩ := time_hierarchy_weak hg hg1 hfg
  have hsub : DTIME f ⊆ DTIME (fun n => (n + 1) ^ 2 * (g n + 1)) := by
    refine DTIME_mono ?_
    have h1 : f =O (fun n => (f n + n + 1) ^ 2) :=
      BigO.of_le fun n =>
        le_trans (by omega) (Nat.le_self_pow (by omega) (f n + n + 1))
    have h2 : g =O (fun n => (n + 1) ^ 2 * (g n + 1)) :=
      BigO.of_le fun n => by
        have hp : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
        nlinarith
    exact ((h1.trans_littleO hfg).isBigO).trans h2
  rw [Set.ssubset_def]
  exact ⟨hsub, fun hsup => hLnot (hsup hLmem)⟩

-- ════════════════════════════════════════════════════════════════════════
-- Concrete polynomial corollary
-- ════════════════════════════════════════════════════════════════════════

/-- **Polynomial time hierarchy**: `DTIME((n+1)^a) ⊂ DTIME((n+1)^(2a+5))`
    for every `a ≥ 1`. Instantiates the hierarchy theorem at the
    clock-constructible bound `g = (n+1)^(2a+3)`. -/
theorem DTIME_pow_ssubset (a : ℕ) (ha : 1 ≤ a) :
    DTIME (fun n => (n + 1) ^ a) ⊂ DTIME (fun n => (n + 1) ^ (2 * a + 5)) := by
  have hg : TM.ClockConstructible (fun n => (n + 1) ^ (2 * a + 3)) :=
    TM.clockConstructible_pow (2 * a + 3) (by omega)
  have hg1 : ∀ n, 1 ≤ (n + 1) ^ (2 * a + 3) :=
    fun n => Nat.one_le_pow _ _ (by omega)
  have hfg : Complexity.LittleO (fun n => ((n + 1) ^ a + n + 1) ^ 2)
      (fun n => (n + 1) ^ (2 * a + 3)) := by
    have hle : ∀ n, ((n + 1) ^ a + n + 1) ^ 2 ≤ 4 * (n + 1) ^ (2 * a) := by
      intro n
      have hbase : n + 1 ≤ (n + 1) ^ a := Nat.le_self_pow (by omega) (n + 1)
      have h2 : (n + 1) ^ a + n + 1 ≤ 2 * (n + 1) ^ a := by omega
      calc ((n + 1) ^ a + n + 1) ^ 2
          ≤ (2 * (n + 1) ^ a) ^ 2 := Nat.pow_le_pow_left h2 2
        _ = 4 * (n + 1) ^ (2 * a) := by ring
    exact (BigO.of_le hle).trans_littleO
      (LittleO.const_mul_left 4 (Complexity.LittleO.pow_lt_pow (by omega)))
  have hstep := time_hierarchy_weak_ssubset hg hg1 hfg
  have hsub : DTIME (fun n => (n + 1) ^ 2 * ((n + 1) ^ (2 * a + 3) + 1))
      ⊆ DTIME (fun n => (n + 1) ^ (2 * a + 5)) := by
    refine DTIME_mono ?_
    have hle : ∀ n, (n + 1) ^ 2 * ((n + 1) ^ (2 * a + 3) + 1)
        ≤ 2 * (n + 1) ^ (2 * a + 5) := by
      intro n
      have h1 : 1 ≤ (n + 1) ^ (2 * a + 3) := Nat.one_le_pow _ _ (by omega)
      calc (n + 1) ^ 2 * ((n + 1) ^ (2 * a + 3) + 1)
          ≤ (n + 1) ^ 2 * (2 * (n + 1) ^ (2 * a + 3)) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = 2 * (n + 1) ^ (2 * a + 5) := by ring
    exact (BigO.of_le hle).trans (BigO.const_mul_left 2 (BigO.refl _))
  exact hstep.trans_subset hsub

end Complexity
