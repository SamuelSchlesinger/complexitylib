/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Reduction
public import Complexitylib.Circuits.Frontier.Demand

/-!
# The lower bound

**Main theorem** (`Frontier.lowerBound`). Fix a fan-in bound `r ≥ 2`, and suppose that graphs
of maximum degree `r + 1` have layouts of width `(A + o(1)) β₁ + o(|V|)` (`LayoutBound (r + 1) A`).
Let `S_n ⊆ U^n` be `K_n`-rectangle-free sets over a finite alphabet `U`, with `log K_n = o(n)`
and `|S_n| ≥ |U| ^ (n - o(n))`. Then for every `ε > 0` and all large `n`, every circuit deciding
`S_n` over any basis of fan-in at most `r` on `U` has `s` inner gates with

`(r - 1) s > (1 + 1/A - ε) n`.

Gates of arity zero, the constants, are not counted. For fan-in two
(`Frontier.lowerBound_fanInTwo`) the graphs are subcubic and the bound reads
`s > (1 + 1/A - ε) n`.

The proof is the reduction theorem followed by the comparison of demand and supply
(`Frontier.eventually_lt_of_demand`). A circuit with `s` gates gives a graph of cycle rank about
`(r - 1) s - n`, all of whose layouts have width about `n`: that is the demand. The layout
hypothesis provides a layout of width about `A ((r - 1) s - n)`: that is the supply. So
`n ≤ A ((r - 1) s - n) + o(n)`, that is, `(r - 1) s ≥ (1 + 1/A - o(1)) n`.

## Instances

For fan-in two the layout hypothesis is proved (`Frontier.Layouts`) with
`A = (3/π) arccos((1 + 2√2)/4) ≈ 0.2807`, from Gaussian edge-score layouts, giving the
coefficient `1 + π/(3 arccos((1 + 2√2)/4)) ≈ 4.5625`, and with the weaker `A = 1/3`, giving the
coefficient `4` (`Frontier.Main`).
-/

@[expose] public section

namespace Complexity.Frontier

open Cslib.Circuits Set Filter Asymptotics

universe u v

variable {U : Type u} [Finite U] [Nontrivial U]

/-- A set of inputs has at most `|U| ^ n` elements: `log_q |S| ≤ n`. -/
theorem logb_ncard_le_self {n : ℕ} (S : Set (Fin n → U)) (hS : S.Nonempty) :
    Real.logb (Nat.card U) S.ncard ≤ n := by
  have hq : (1 : ℝ) < Nat.card U := by exact_mod_cast Finite.one_lt_card
  have hle : (S.ncard : ℝ) ≤ (Nat.card U : ℝ) ^ n := by
    have := ncard_le_card S
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at this
    exact_mod_cast this
  have hpos : (0 : ℝ) < S.ncard := by exact_mod_cast (ncard_pos (toFinite S)).mpr hS
  calc Real.logb (Nat.card U) S.ncard ≤ Real.logb (Nat.card U) ((Nat.card U : ℝ) ^ n) :=
        Real.logb_le_logb_of_le hq hpos hle
    _ = n := by rw [Real.logb_pow, Real.logb_self_eq_one hq, mul_one]

/-- A dense set has `n - log_q |S_n| = o(n)`. -/
theorem isLittleO_sub_logb_ncard (S : ∀ n, Set (Fin n → U))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ)) :
    (fun n : ℕ => (n : ℝ) - Real.logb (Nat.card U) (S n).ncard) =o[atTop] fun n => (n : ℝ) := by
  have hL : 0 < Real.log (Nat.card U) := Real.log_pos (by exact_mod_cast Finite.one_lt_card)
  refine (hdense.const_mul_left (1 / Real.log (Nat.card U))).congr_left fun n => ?_
  simp only [Real.logb]; field_simp

/-- Eventually a dense rectangle-free set is large enough for the reduction: `q K^2 ≤ |S|`. -/
theorem eventually_card_mul_sq_le_ncard (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ)) :
    ∀ᶠ n in atTop, Nat.card U * K n ^ 2 ≤ (S n).ncard := by
  set q := Nat.card U
  have hq : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  have hL : 0 < Real.log q := Real.log_pos hq
  have hlog : (fun n : ℕ => Real.log q + 2 * Real.log (K n) +
      (n * Real.log q - Real.log (S n).ncard)) =o[atTop] fun n => (n : ℝ) :=
    ((isLittleO_const_left.mpr
      (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop))).add
      (hK.const_mul_left 2)).add hdense
  filter_upwards [hlog.bound (show 0 < Real.log q / 2 by positivity), hfree,
    eventually_ge_atTop 1] with n hn hfreen hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hK1 : (1 : ℝ) ≤ K n := by exact_mod_cast hfreen.pos
  have hlogK : 0 ≤ Real.log (K n) := Real.log_nonneg hK1
  simp only [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)] at hn
  have hb := (le_abs_self _).trans hn
  -- `log |S| ≥ log q + 2 log K + (n / 2) log q > log (q K^2)`.
  have hSlog : Real.log q + 2 * Real.log (K n) < Real.log (S n).ncard := by nlinarith
  have hSpos : (0 : ℝ) < (S n).ncard := by
    by_contra! h0
    have : ((S n).ncard : ℝ) = 0 := le_antisymm h0 (Nat.cast_nonneg _)
    rw [this, Real.log_zero] at hSlog
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ q by linarith)]
  have : Real.log (q * K n ^ 2 : ℝ) ≤ Real.log (S n).ncard := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; linarith
  exact_mod_cast (Real.log_le_log_iff (by positivity) hSpos).mp this

/-- The numerical demand--supply comparison, exposed independently of the compiler.
Any graph with the reduction's size, cycle, and frontier-demand bounds gives the same
lower bound on its gate budget. -/
theorem lowerBound_of_graph {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A)
    (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (gates : ℕ) (V E : Type) [Finite V] [Finite E] (G : Multigraph V E),
      G.Connected → G.Loopless → G.MaxDegreeLE (r + 1) →
      Nat.card V ≤ 2 * r * gates + 3 →
      (G.cycleRank : ℝ) ≤ ((r - 1) * gates : ℕ) - n + Real.logb (Nat.card U) (K n) + 1 →
      (∀ (π : Layout V) (w : ℕ), (∀ t, (G.cut (π.initial t)).ncard ≤ w) →
        Real.logb (Nat.card U) (S n).ncard ≤
          w + (r + 2) + 3 * Real.logb (Nat.card U) (K n) +
            Real.logb (Nat.card U) (Nat.card V + 1)) →
      (1 + 1 / A - ε) * n < (r - 1) * gates := by
  set q := Nat.card U
  have hq : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  have hL : 0 < Real.log q := Real.log_pos hq
  have hL2 : Real.log 2 ≤ Real.log q :=
    Real.log_le_log two_pos (by exact_mod_cast Finite.one_lt_card)
  -- The error of the problem: the density defect, the threshold, and constants.
  set e : ℕ → ℝ := fun n => (n - Real.logb q (S n).ncard) + 4 * Real.logb q (K n) + (r + 3)
  have he : e =o[atTop] fun n => (n : ℝ) := by
    have h1 := isLittleO_sub_logb_ncard S hdense
    have h2 : (fun n : ℕ => 4 * Real.logb q (K n)) =o[atTop] fun n => (n : ℝ) :=
      (hK.const_mul_left (4 / Real.log q)).congr_left fun n => by
        simp only [Real.logb]; ring
    have h3 : (fun _ : ℕ => ((r : ℝ) + 3)) =o[atTop] fun n => (n : ℝ) :=
      isLittleO_const_left.mpr (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop))
    exact (h1.add h2).add h3
  -- The constant bounding the size of the graph and the base change of its logarithm.
  set κ : ℝ := 4 + 1 / Real.log 2
  have hκ : 0 ≤ κ := by positivity
  obtain ⟨η, hη, H⟩ := eventually_lt_of_demand hA hκ hε
  obtain ⟨C, hC⟩ := hlayout η hη
  replace H := H η hη le_rfl
  have hbig := eventually_card_mul_sq_le_ncard S K hfree hK hdense
  filter_upwards [H C e he, hfree, hbig] with n hn hfreen hbign
  intro gates V E _ _ G hconn hloop hdeg hV hrank hwidth
  obtain ⟨π, hπ⟩ := hC V E G hconn hloop hdeg
  set B := (A + η) * G.cycleRank + η * Nat.card V + C
  have hB : 0 ≤ B := by simpa [Layout.initial_zero] using hπ 0
  have hwidth := hwidth π ⌊B⌋₊ fun t => Nat.le_floor (hπ t)
  -- The quantities of the comparison.
  set s : ℝ := (((r - 1) * gates : ℕ) : ℝ)
  have hs : s = (r - 1) * gates := by
    simp only [s]; rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
  have hK1 : (1 : ℝ) ≤ K n := by exact_mod_cast hfreen.pos
  have hlogK : 0 ≤ Real.logb q (K n) := Real.logb_nonneg hq hK1
  have hSne : (S n).Nonempty := by
    rw [← ncard_pos (toFinite _)]
    have : 0 < q := Nat.card_pos
    exact lt_of_lt_of_le (Nat.mul_pos this (pow_pos hfreen.pos 2)) hbign
  have hlogS := logb_ncard_le_self (S n) hSne
  have hlogV : Real.logb q (Nat.card V + 1) ≤ κ * Real.log (Nat.card V + 1) := by
    have h0 : 0 ≤ Real.log (Nat.card V + 1) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (Nat.card V)])
    have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    calc Real.logb q (Nat.card V + 1) ≤ Real.log (Nat.card V + 1) / Real.log 2 :=
          div_le_div_of_nonneg_left h0 h2 hL2
      _ ≤ κ * Real.log (Nat.card V + 1) := by
          rw [div_eq_mul_one_div, mul_comm]
          exact mul_le_mul_of_nonneg_right (by simp [κ]) h0
  have hVs : (Nat.card V : ℝ) ≤ κ * (n + s + 1) := by
    have : 2 * r * gates + 3 ≤ 4 * ((r - 1) * gates) + 4 := by
      have : 2 * r ≤ 4 * (r - 1) := by omega
      nlinarith
    have h4 : (Nat.card V : ℝ) ≤ 4 * ((r - 1) * gates : ℕ) + 4 := by
      exact_mod_cast hV.trans this
    have hκ4 : 4 ≤ κ := by simp only [κ]; linarith [show 0 ≤ 1 / Real.log 2 by positivity]
    have hns : 0 ≤ (n : ℝ) + s + 1 := by positivity
    simp only [s] at hns ⊢
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  rw [← hs]
  refine hn s (Nat.card V) ⌊B⌋₊ (Nat.cast_nonneg _) (Nat.cast_nonneg _) hVs ?_ ?_
  · -- The demand: `n ≤ w + e(n) + κ log (|V| + 1)`.
    simp only [e]
    linarith
  · -- The supply: the layout hypothesis, with the cycle rank of the reduction.
    have hfloor : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le hB
    have hrank' : (G.cycleRank : ℝ) ≤ s - n + e n := by
      simp only [e]; simp only [s]; linarith
    have := mul_le_mul_of_nonneg_left hrank' (by linarith : 0 ≤ A + η)
    linarith

/-- **The frontier lower bound.** Let `r ≥ 2` and assume the layout hypothesis for maximum
degree `r + 1` with coefficient `A > 0`. Let `S_n ⊆ U^n` be `K_n`-rectangle-free sets over a
finite alphabet `U` with at least two symbols, with `log K_n = o(n)` and
`n log |U| - log |S_n| = o(n)`. Then for every `ε > 0`, for all large `n`, every circuit with
fan-in at most `r` deciding `S_n`, over any basis and interpretation on `U`, has `s` inner gates
with `(r - 1) s > (1 + 1/A - ε) n`. -/
theorem lowerBound {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound (r + 1) A)
    (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → Decides c I Acc (S n) →
        (1 + 1 / A - ε) * n < (r - 1) * c.innerSize := by
  filter_upwards [lowerBound_of_graph hr hA hlayout S K hfree hK hdense hε,
    hfree, eventually_card_mul_sq_le_ncard S K hfree hK hdense] with n hn hf hb
  intro σ I Acc c hfan hS
  obtain ⟨V, E, _, _, G, hc, hl, hd, hV, hrank, hw⟩ :=
    exists_graph_of_decides hr hfan hS hf hb
  exact hn c.innerSize V E G hc hl hd hV hrank hw

/-- **The frontier lower bound for fan-in two.** Assume the layout hypothesis for subcubic graphs
with coefficient `A > 0`. Under the hypotheses of `Frontier.lowerBound`, for every `ε > 0` and all
large `n`, every circuit with fan-in at most two deciding `S_n`, over any basis and
interpretation on `U`, has more than `(1 + 1/A - ε) n` inner gates. -/
theorem lowerBound_fanInTwo {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound 3 A)
    (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → Decides c I Acc (S n) →
        (1 + 1 / A - ε) * n < c.innerSize := by
  filter_upwards [lowerBound le_rfl hA hlayout S K hfree hK hdense hε] with n hn
  intro σ I Acc c hfan hS
  have h := hn σ I Acc c hfan hS
  norm_num at h ⊢
  exact h

end Complexity.Frontier
