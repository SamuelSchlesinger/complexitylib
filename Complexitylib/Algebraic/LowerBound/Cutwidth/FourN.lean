/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Wiring
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Expansion
public import Cslib.Foundations.Data.Nat.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# The `(4 - ε) n` lower bound

Assembling the cut-counting lemma, the wiring graph, and the graph-ordering
hypothesis gives the circuit lower bound. A `K`-rectangle-free function with
at least `2 ^ (n - 2)` accepting inputs and `K` polynomial in `n` needs more
than `(4 - ε) n` gates over the full binary basis, for every `ε > 0` and all
sufficiently large `n`.

Two statements enter as hypotheses rather than being proved here:

* `Multigraph.OrderingBound η C` for every `η > 0` and some `C`, the
  graph-ordering hypothesis on multigraphs of maximum degree three, which
  `eventually_lt_size_of_pathwidthBound` derives from the pathwidth
  hypothesis `PathwidthBound` for simple cubic graphs;
* a family `f n` with threshold `K n ≤ n ^ c` satisfying `RectangleFree` and
  the accepting-input bound.

The main theorem is `eventually_lt_size`. The fixed-`n` core is
`lt_size_of_bounds`, whose numeric hypotheses are discharged asymptotically.
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth

open scoped Classical
open Filter

/-- Increasing the additive constant weakens the ordering hypothesis. -/
theorem Multigraph.OrderingBound.mono {η C C' : ℝ} (h : Multigraph.OrderingBound η C)
    (hC : C ≤ C') : Multigraph.OrderingBound η C' := by
  intro V E _ _ G loopless degree connected
  obtain ⟨inst, bound⟩ := h V E G loopless degree connected
  exact ⟨inst, fun L hL => (bound L hL).trans (by linarith)⟩

/-- A rectangle-free function with many accepting inputs cannot ignore
`⌈log₂ K⌉` coordinates. -/
theorem sub_card_lt_clog {n : Nat} {f : Cslib.BooleanFunction n} {K : Nat} (hK : 1 < K)
    (hrect : RectangleFree f K) (hacc : 2 ^ (n - 2) ≤ (accepting f).card)
    (hbig : 2 * K ^ 2 ≤ 2 ^ (n - 2)) {R : Finset (Fin n)} (hR : DependsOnlyOn f R) :
    n - R.card < Nat.clog 2 K := by
  by_contra h
  rw [not_lt] at h
  have hcompl : Nat.clog 2 K ≤ Rᶜ.card := by
    rwa [Finset.card_compl, Fintype.card_fin]
  obtain ⟨U, hU, hcard⟩ := Finset.exists_subset_card_eq hcompl
  have disjoint : Disjoint U R :=
    Finset.disjoint_of_subset_left hU disjoint_compl_left
  have hpos : 1 ≤ Nat.clog 2 K := Nat.clog_pos one_lt_two hK
  have hlow : 2 ^ (Nat.clog 2 K - 1) < K := Nat.pow_pred_clog_lt_self one_lt_two hK
  have hpow : 2 ^ Nat.clog 2 K < 2 * K := by
    calc 2 ^ Nat.clog 2 K = 2 * 2 ^ (Nat.clog 2 K - 1) := by
          rw [← Nat.pow_succ']
          congr 1
          omega
      _ < 2 * K := by omega
  rcases two_pow_lt_or_card_accepting_lt hrect hR disjoint with small | small
  · rw [hcard] at small
    exact absurd (Nat.le_pow_clog one_lt_two K) (not_le.mpr small)
  · rw [hcard] at small
    have : (accepting f).card < 2 * K * K :=
      small.trans_le (Nat.mul_le_mul_right K hpow.le)
    have : 2 * K ^ 2 = 2 * K * K := by ring
    omega

/-- The circuit-level bound: for a circuit with output gate `out`, either the
final past set is small, so that fewer than `K · 2 ^ (n - n')` inputs are
accepted, or the accepted inputs are bounded through the ordering hypothesis.
Here `n'` is the number of inputs with a path to the output. -/
theorem card_accepting_le_of_orderingBound {η C : ℝ} (hη : 0 ≤ η) (hC : 0 ≤ C)
    (order : Multigraph.OrderingBound η C)
    {n s : Nat} (p : Program Binary.signature n s) (out : Fin s) {K : Nat} (hK : 1 < K)
    (hrect : RectangleFree (fun x => p.eval Binary.interpretation x out) K) :
    (accepting fun x => p.eval Binary.interpretation x out).card <
        K * 2 ^ (n - (Wiring.read p out).card) ∨
      ((accepting fun x => p.eval Binary.interpretation x out).card : ℝ) ≤
        (n + 3 * s) * (2 : ℝ) ^ ((1 / 3 + η) * max ((s : ℝ) - (Wiring.read p out).card) 0 +
          3 * Real.logb 2 (n + 3 * s) + C + 3) * K ^ 2 := by
  obtain ⟨inst, hcut⟩ := order (Wiring.Vertex p out) (Wiring.Edge p out)
    (Wiring.network p out).toMultigraph (Wiring.loopless p out)
    (Wiring.maxDegreeLE_three p out) (Wiring.connected p out)
  set bound : ℝ := (1 / 3 + η) *
      max ((Fintype.card (Wiring.Edge p out) : ℝ) - Fintype.card (Wiring.Vertex p out)) 0 +
    3 * Real.logb 2 (Fintype.card (Wiring.Vertex p out)) + C with hbound_def
  have hVpos : (0 : ℝ) < Fintype.card (Wiring.Vertex p out) := by
    exact_mod_cast Fintype.card_pos
  have hlogV : 0 ≤ Real.logb 2 (Fintype.card (Wiring.Vertex p out)) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast Fintype.card_pos)
  have bound_nonneg : 0 ≤ bound := by
    have : 0 ≤ (1 / 3 + η) *
        max ((Fintype.card (Wiring.Edge p out) : ℝ) - Fintype.card (Wiring.Vertex p out)) 0 :=
      mul_nonneg (by linarith) (le_max_right _ _)
    linarith
  have hw : ∀ v, ((Wiring.network p out).cut (Network.below v)).card ≤ ⌊bound⌋₊ :=
    fun v => Nat.le_floor (hcut _ (Network.isLowerSet_below v))
  rcases (Wiring.network p out).card_accepting_le (Wiring.network_computes p out)
    (Wiring.maxDegreeLE_three p out) hw hK hrect with h | h
  · exact Or.inl h
  right
  have hV : (Fintype.card (Wiring.Vertex p out) : ℝ) ≤ n + 3 * s := by
    exact_mod_cast Wiring.card_vertex_le p out
  have hdiff : (Fintype.card (Wiring.Edge p out) : ℝ) - Fintype.card (Wiring.Vertex p out) ≤
      (s : ℝ) - (Wiring.read p out).card := by
    rw [Wiring.card_edge_sub_card_vertex]
    have : (Fintype.card (Wiring.ReachableGate p out) : ℝ) ≤ s := by
      exact_mod_cast Wiring.card_reachableGate_le p out
    linarith
  have hbound : bound ≤ (1 / 3 + η) * max ((s : ℝ) - (Wiring.read p out).card) 0 +
      3 * Real.logb 2 (n + 3 * s) + C := by
    have h₁ : (1 / 3 + η) *
        max ((Fintype.card (Wiring.Edge p out) : ℝ) - Fintype.card (Wiring.Vertex p out)) 0 ≤
        (1 / 3 + η) * max ((s : ℝ) - (Wiring.read p out).card) 0 :=
      mul_le_mul_of_nonneg_left (max_le_max hdiff le_rfl) (by linarith)
    have h₂ : Real.logb 2 (Fintype.card (Wiring.Vertex p out)) ≤ Real.logb 2 (n + 3 * s) :=
      (Real.logb_le_logb one_lt_two hVpos (hVpos.trans_le hV)).mpr hV
    linarith
  have hexp : ((2 : ℝ) ^ (⌊bound⌋₊ + 3) : ℝ) ≤
      (2 : ℝ) ^ ((1 / 3 + η) * max ((s : ℝ) - (Wiring.read p out).card) 0 +
        3 * Real.logb 2 (n + 3 * s) + C + 3) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    push_cast
    linarith [Nat.floor_le bound_nonneg]
  have hK' : (((K - 1 : Nat) : ℝ)) ^ 2 ≤ (K : ℝ) ^ 2 := by
    gcongr
    exact_mod_cast Nat.sub_le K 1
  calc ((accepting fun x => p.eval Binary.interpretation x out).card : ℝ)
      ≤ (Fintype.card (Wiring.Vertex p out) : ℝ) * (2 : ℝ) ^ (⌊bound⌋₊ + 3) *
          ((K - 1 : Nat) : ℝ) ^ 2 := by exact_mod_cast h
    _ ≤ (n + 3 * s) * (2 : ℝ) ^ ((1 / 3 + η) * max ((s : ℝ) - (Wiring.read p out).card) 0 +
          3 * Real.logb 2 (n + 3 * s) + C + 3) * K ^ 2 := by
        apply mul_le_mul (mul_le_mul hV hexp (by positivity) (by positivity)) hK'
          (by positivity) (by positivity)

/-- Every fixed multiple of the binary logarithm, plus a constant, is
eventually below every positive multiple of the input. -/
theorem eventually_mul_logb_add_lt (A B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : Nat in atTop, A * Real.logb 2 n + B < δ * n := by
  have hlog : (fun n : Nat => Real.log n) =o[atTop] (fun n : Nat => (n : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * |A| / (δ * Real.log 2))
  have key := (Asymptotics.isLittleO_iff_nat_mul_le.mp hlog) m
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * B / δ)
  filter_upwards [key, eventually_ge_atTop 1, eventually_ge_atTop N] with n hn hn1 hnN
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1'
  rw [Real.norm_of_nonneg hlogn, Real.norm_of_nonneg (by positivity)] at hn
  have hmA : 2 * |A| < m * (δ * Real.log 2) := by
    rwa [div_lt_iff₀ (by positivity)] at hm
  have h₁ : 2 * (A * Real.logb 2 n) ≤ δ * n := by
    rw [Real.logb]
    have step : 2 * A * Real.log n ≤ (m * (δ * Real.log 2)) * Real.log n := by
      apply mul_le_mul_of_nonneg_right _ hlogn
      have := le_abs_self A
      linarith
    have step' : (m * (δ * Real.log 2)) * Real.log n ≤ δ * Real.log 2 * n := by
      have : (m : ℝ) * Real.log n ≤ n := hn
      calc (m * (δ * Real.log 2)) * Real.log n = δ * Real.log 2 * (m * Real.log n) := by ring
        _ ≤ δ * Real.log 2 * n := mul_le_mul_of_nonneg_left this (by positivity)
    have : 2 * A * Real.log n ≤ δ * Real.log 2 * n := step.trans step'
    calc 2 * (A * (Real.log n / Real.log 2)) = (2 * A * Real.log n) / Real.log 2 := by ring
      _ ≤ (δ * Real.log 2 * n) / Real.log 2 := by gcongr
      _ = δ * n := by field_simp
  have h₂ : 2 * B < δ * n := by
    have hnN' : (N : ℝ) ≤ n := by exact_mod_cast hnN
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  linarith

/-- **The fixed-`n` core of the lower bound.** With the graph-ordering
hypothesis for slack `η ≤ 1/18`, a `K`-rectangle-free function with at least
`2 ^ (n - 2)` accepting inputs and `K ≤ n ^ c` needs more than `(4 - 18 η) n`
binary gates, once `n` satisfies two explicit numeric conditions. -/
theorem lt_size_of_bounds {η C : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 18) (hC : 0 ≤ C)
    (order : Multigraph.OrderingBound η C)
    {n : Nat} (hn : 2 ≤ n) {f : Cslib.BooleanFunction n} {K c : Nat} (hK : K ≤ n ^ c)
    (hacc : 2 ^ (n - 2) ≤ (accepting f).card) (hrect : RectangleFree f K)
    (hpow : 8 * n ^ (2 * c) ≤ 2 ^ n)
    (hlog : (4 + 3 * c) * Real.logb 2 n + (C + 22) < 3 * η * n)
    {s : Nat} (circuit : Circuit Binary.signature n s 1)
    (computes : circuit.Computes Binary.interpretation f) :
    (4 - 18 * η) * n < s := by
  by_contra hs
  rw [not_lt] at hs
  -- Basic facts about `K` and `⌈log₂ K⌉`.
  have hacc_pos : 0 < (accepting f).card := lt_of_lt_of_le (Nat.two_pow_pos _) hacc
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp hacc_pos
  have hK1 : 1 < K := hrect.one_lt (mem_accepting.mp hx₀)
  have hpow' : 2 ^ n = 4 * 2 ^ (n - 2) := by
    calc 2 ^ n = 2 ^ (n - 2 + 2) := by rw [Nat.sub_add_cancel hn]
      _ = 4 * 2 ^ (n - 2) := by rw [pow_add]; ring
  have hbig : 2 * K ^ 2 ≤ 2 ^ (n - 2) := by
    have : K ^ 2 ≤ n ^ (2 * c) := by
      rw [mul_comm, pow_mul]
      exact Nat.pow_le_pow_left hK 2
    omega
  set k := Nat.clog 2 K with hk_def
  have hk1 : 1 ≤ k := Nat.clog_pos one_lt_two hK1
  have hlow : 2 ^ (k - 1) < K := Nat.pow_pred_clog_lt_self one_lt_two hK1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlogn : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two hn1
  have hkR : (k : ℝ) < c * Real.logb 2 n + 1 := by
    have h₁ : ((2 : ℝ) ^ (k - 1)) < (n : ℝ) ^ c := by
      have : (2 ^ (k - 1) : Nat) < n ^ c := hlow.trans_le hK
      exact_mod_cast this
    have h₂ := (Real.logb_lt_logb one_lt_two (by positivity) h₁)
    rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at h₂
    have : ((k - 1 : Nat) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk1]
      simp
    linarith
  have hlogK : Real.logb 2 K ≤ c * Real.logb 2 n := by
    have h := (Real.logb_le_logb one_lt_two (by exact_mod_cast (by omega : 0 < K))
      (by positivity)).mpr (show (K : ℝ) ≤ (n : ℝ) ^ c by exact_mod_cast hK)
    rwa [Real.logb_pow] at h
  -- The circuit's output wire.
  set g := circuit.outputs 0 with hg
  have eval_eq : ∀ x, f x = circuit.program.trace Binary.interpretation x g := by
    intro x
    rw [← computes x]
    rfl
  -- The function depends only on the inputs read by the output cone, and
  -- that cone must contain all but fewer than `k` inputs.
  have support : ∀ R : Finset (Fin n), DependsOnlyOn f R → n - R.card < k :=
    fun R hR => sub_card_lt_clog hK1 hrect hacc hbig hR
  revert eval_eq
  refine Fin.addCases (fun j => ?_) (fun out => ?_) g
  · -- The output is an input wire: the function ignores all but one coordinate.
    intro eval_eq
    have hR : DependsOnlyOn f {j} := by
      intro x y agree
      rw [eval_eq, eval_eq, Program.trace_input, Program.trace_input]
      exact agree j (Finset.mem_singleton_self j)
    have := support {j} hR
    rw [Finset.card_singleton] at this
    have h' : ((n - 1 : Nat) : ℝ) < k := by exact_mod_cast (by omega : n - 1 < k)
    rw [Nat.cast_sub (by omega), Nat.cast_one] at h'
    linarith
  · intro eval_eq
    set p := circuit.program with hp
    have feq : f = fun x => p.eval Binary.interpretation x out := by
      funext x
      rw [eval_eq]
      simp [Program.trace_gateWire]
    have hrect' : RectangleFree (fun x => p.eval Binary.interpretation x out) K := feq ▸ hrect
    have hacc' : 2 ^ (n - 2) ≤ (accepting fun x => p.eval Binary.interpretation x out).card :=
      feq ▸ hacc
    set n' := (Wiring.read p out).card with hn'
    have hread : n - n' < k := by
      have hR : DependsOnlyOn (fun x => p.eval Binary.interpretation x out) (Wiring.read p out) :=
        (Wiring.network_computes p out).dependsOnlyOn
      exact support _ (by rw [feq]; exact hR)
    have hn'le : n' ≤ n := Wiring.card_read_le p out
    rcases card_accepting_le_of_orderingBound hη.le hC order p out hK1 hrect' with small | large
    · -- Few inputs are read: the count is below `K ^ 2`, contradicting the accepting bound.
      have h₁ : 2 ^ (n - n') ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right two_pos (by omega)
      have h₂ : (accepting fun x => p.eval Binary.interpretation x out).card < K * K :=
        small.trans_le ((Nat.mul_le_mul_left K h₁).trans (Nat.mul_le_mul_left K hlow.le))
      have : K * K = K ^ 2 := by ring
      omega
    · -- The main case: compare exponents.
      have hs' : (s : ℝ) ≤ (4 - 18 * η) * n := hs
      have hreadR : (n : ℝ) - n' < k := by
        have : n - n' < k := hread
        have : ((n - n' : Nat) : ℝ) < k := by exact_mod_cast this
        rwa [Nat.cast_sub hn'le] at this
      have hmax : max ((s : ℝ) - n') 0 ≤ (3 - 18 * η) * n + k := by
        apply max_le
        · linarith
        · nlinarith
      have hprod : (1 / 3 + η) * max ((s : ℝ) - n') 0 ≤
          (1 - 3 * η) * n + (c * Real.logb 2 n + 1) / 2 := by
        have h₁ := mul_le_mul_of_nonneg_left hmax (by linarith : (0 : ℝ) ≤ 1 / 3 + η)
        have hk0 : (0 : ℝ) ≤ k := by positivity
        have h₂ : (1 / 3 + η) * k ≤ k / 2 := by nlinarith
        have h₃ : (1 / 3 + η) * ((3 - 18 * η) * n) ≤ (1 - 3 * η) * n := by nlinarith
        nlinarith
      have hlogS : Real.logb 2 (n + 3 * s) ≤ 4 + Real.logb 2 n := by
        have hpos : (0 : ℝ) < n + 3 * s := by positivity
        have hle : (n : ℝ) + 3 * s ≤ 16 * n := by nlinarith
        calc Real.logb 2 (n + 3 * s) ≤ Real.logb 2 (16 * n) :=
              (Real.logb_le_logb one_lt_two hpos (by positivity)).mpr hle
          _ = 4 + Real.logb 2 n := by
              rw [Real.logb_mul (by norm_num) (by positivity),
                show (16 : ℝ) = 2 ^ (4 : Nat) by norm_num, Real.logb_pow,
                Real.logb_self_eq_one one_lt_two]
              ring
      -- Take binary logarithms of the main inequality.
      have hM : ((accepting fun x => p.eval Binary.interpretation x out).card : ℝ) > 0 := by
        exact_mod_cast (feq ▸ hacc_pos)
      have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
      have hSpos : (0 : ℝ) < n + 3 * s := by positivity
      set X : ℝ := (1 / 3 + η) * max ((s : ℝ) - n') 0 + 3 * Real.logb 2 (n + 3 * s) + C + 3
        with hX
      have hlower : (2 : ℝ) ^ ((n : ℝ) - 2) ≤
          (accepting fun x => p.eval Binary.interpretation x out).card := by
        have : ((2 : ℝ) ^ (n - 2 : Nat)) ≤
            (accepting fun x => p.eval Binary.interpretation x out).card := by
          exact_mod_cast hacc'
        rwa [← Real.rpow_natCast, Nat.cast_sub hn] at this
      have hupper : ((accepting fun x => p.eval Binary.interpretation x out).card : ℝ) ≤
          (2 : ℝ) ^ (Real.logb 2 (n + 3 * s) + X + 2 * Real.logb 2 K) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num)
          (by norm_num) hSpos, show (2 : ℝ) ^ (2 * Real.logb 2 K) = ((2 : ℝ) ^ Real.logb 2 K) ^ 2 by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            push_cast
            ring_nf, Real.rpow_logb (by norm_num) (by norm_num) hKpos]
        exact large
      have hexp := (Real.rpow_le_rpow_left_iff one_lt_two).mp (hlower.trans hupper)
      linarith

/-- **Theorem 1.** Assume the graph-ordering lemma for every slack `η > 0` and
a family of functions `f n` that is `K n`-rectangle-free with `K n ≤ n ^ c`
and at least `2 ^ (n - 2)` accepting inputs, for all large `n`. Then for every
`ε > 0` and all sufficiently large `n`, every binary circuit computing `f n`
has more than `(4 - ε) n` gates. -/
theorem eventually_lt_size
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound η C)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) (c : Nat)
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c)
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ {s : Nat} (circuit : Circuit Binary.signature n s 1),
      circuit.Computes Binary.interpretation (f n) → (4 - ε) * n < s := by
  set ε' := min ε 1 with hε'
  have hε'pos : 0 < ε' := lt_min hε one_pos
  have hε'le : ε' ≤ ε := min_le_left _ _
  set η := ε' / 18 with hη
  have hηpos : 0 < η := by positivity
  have hη1 : η ≤ 1 / 18 := by
    have : ε' ≤ 1 := min_le_right _ _
    rw [hη]
    linarith
  obtain ⟨C, hC⟩ := order η hηpos
  have order' : Multigraph.OrderingBound η (max C 0) := hC.mono (le_max_left _ _)
  have hlog := eventually_mul_logb_add_lt (4 + 3 * c) (max C 0 + 22) (by positivity : 0 < 3 * η)
  have hpow := Nat.eventually_mul_pow_le_pow 8 (2 * c) one_lt_two
  filter_upwards [hK, hacc, hrect, hlog, hpow, eventually_ge_atTop 2] with n hKn haccn
    hrectn hlogn hpown hn2
  intro s circuit computes
  have key := lt_size_of_bounds hηpos hη1 (le_max_right C 0) order' hn2 hKn haccn hrectn hpown
    hlogn circuit computes
  have : (4 - ε) * n ≤ (4 - 18 * η) * n := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [hη]
    linarith
  linarith

/-- **Theorem 1 from the pathwidth hypothesis.** The graph-ordering hypothesis
is replaced by the pathwidth bound for simple cubic graphs: for every `ξ > 0`
there is a threshold beyond which every simple 3-regular graph on `h`
vertices has a path decomposition of width at most `(1/6 + ξ) h`. -/
theorem eventually_lt_size_of_pathwidthBound
    (pathwidth : ∀ ξ : ℝ, 0 < ξ → ∃ N₀ : Nat, PathwidthBound ξ N₀)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) (c : Nat)
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c)
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ {s : Nat} (circuit : Circuit Binary.signature n s 1),
      circuit.Computes Binary.interpretation (f n) → (4 - ε) * n < s := by
  refine eventually_lt_size (fun η hη => ?_) f K c hK hacc hrect hε
  obtain ⟨N₀, hN₀⟩ := pathwidth (η / 2) (by positivity)
  refine ⟨N₀ + 9, ?_⟩
  have := Multigraph.orderingBound_of_pathwidthBound (by positivity) hN₀
  rwa [show 2 * (η / 2) = η by ring] at this

end Cutwidth
end Algebraic
