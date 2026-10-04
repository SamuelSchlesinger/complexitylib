/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Wiring
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Expansion
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Asymptotics
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Helpful

/-!
# The `(4 - ε) n` lower bound

Assembling the cut-counting lemma, the wiring graph, and the proved cubic
bisection and pathwidth bounds gives the circuit lower bound. A `K`-rectangle-free function with
at least `2 ^ (n - 2)` accepting inputs and `log₂ K = o(n)` needs more than
`(4 - ε) n` gates over the full binary basis, for every `ε > 0` and all
sufficiently large `n`. Polynomial thresholds are a special case.

`eventually_lt_size_of_rectangleFree` has no graph hypothesis. Its remaining
application obligation is a family `f n` with `log₂ K(n) = o(n)` satisfying
`RectangleFree` and the accepting-input bound. The downstream module
`Extractor.SourceReduction.Construction.Hardness` supplies a concrete uniform
polynomial-time family and proves its unconditional coefficient-four lower bound.

The counting argument is generic in the graph-ordering coefficient: with
`Multigraph.OrderingBound A η C` for every slack `η > 0`, where `A > 0`, the
circuit coefficient is `1 + 1/A` (`eventually_lt_size_of_orderingBound`, with
fixed-`n` core `lt_size_of_orderingBound` and numeric core
`false_of_accepting_bound_of_log_coefficient`). A cubic cutwidth or pathwidth
bound with coefficient `c` gives `A = 2 c` and hence `1 + 1/(2c)`
(`eventually_lt_size_of_cutwidthBound`,
`eventually_lt_size_of_pathwidthCoefficient`). The proved Monien–Preis and
Fomin–Høie bounds give `c = 1/6`, `A = 1/3`, and the coefficient four.

The coefficient-four graph-ordering interface remains
`eventually_lt_size_of_log_sublinear`, with fixed-`n` core
`lt_size_of_log_bounds`. The original `eventually_lt_size` and
`lt_size_of_bounds` specialize these to polynomial thresholds.

The proof organization, the threshold-edge charging, the application of a
sumset extractor as the hard family, and the merge-tree restoration argument
follow Ryan Williams's private working note *A (4 − ε)n lower bound for
Boolean circuits* (September 2026), which uses the circuit-to-read-once
compiler of the author's counting note. The formalization is the author's.
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth

open scoped Classical
open Filter

/-- Increasing the total coefficient `A + η` or the additive constant weakens
the ordering hypothesis. -/
theorem Multigraph.OrderingBound.mono {A η C A' η' C' : ℝ}
    (h : Multigraph.OrderingBound A η C) (hAη : A + η ≤ A' + η') (hC : C ≤ C') :
    Multigraph.OrderingBound A' η' C' := by
  intro V E _ _ G loopless degree connected
  obtain ⟨inst, bound⟩ := h V E G loopless degree connected
  refine ⟨inst, fun L hL => (bound L hL).trans ?_⟩
  have := mul_le_mul_of_nonneg_right hAη
    (le_max_right ((Fintype.card E : ℝ) - Fintype.card V) 0)
  linarith

/-- The coefficient-four ordering hypothesis from a cubic pathwidth bound with
coefficient `1/6` at every positive slack. -/
theorem Multigraph.exists_orderingBound_one_third_of_pathwidthBound
    (pathwidth : ∀ ξ : ℝ, 0 < ξ → ∃ N₀ : Nat, PathwidthBound (1 / 6) ξ N₀) :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound (1 / 3) η C := by
  have := Multigraph.exists_orderingBound_of_pathwidthBound (by norm_num) pathwidth
  rwa [show (2 : ℝ) * (1 / 6) = 1 / 3 by norm_num] at this

/-- **The graph-ordering hypothesis with coefficient `1/3`.** It follows from
the proved Fomin–Høie cubic pathwidth bound. -/
theorem Multigraph.exists_orderingBound_one_third :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound (1 / 3) η C :=
  Multigraph.exists_orderingBound_one_third_of_pathwidthBound fun _ h => exists_pathwidthBound h

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
theorem card_accepting_le_of_orderingBound {A η C : ℝ} (hAη : 0 ≤ A + η) (hC : 0 ≤ C)
    (order : Multigraph.OrderingBound A η C)
    {n s : Nat} (p : Program Binary.signature n s) (out : Fin s) {K : Nat} (hK : 1 < K)
    (hrect : RectangleFree (fun x => p.eval Binary.interpretation x out) K) :
    (accepting fun x => p.eval Binary.interpretation x out).card <
        K * 2 ^ (n - (Wiring.read p out).card) ∨
      ((accepting fun x => p.eval Binary.interpretation x out).card : ℝ) ≤
        (n + 3 * s) * (2 : ℝ) ^ ((A + η) * max ((s : ℝ) - (Wiring.read p out).card) 0 +
          3 * Real.logb 2 (n + 3 * s) + C + 3) * K ^ 2 := by
  obtain ⟨inst, hcut⟩ := order (Wiring.Vertex p out) (Wiring.Edge p out)
    (Wiring.network p out).toMultigraph (Wiring.loopless p out)
    (Wiring.maxDegreeLE_three p out) (Wiring.connected p out)
  set bound : ℝ := (A + η) *
      max ((Fintype.card (Wiring.Edge p out) : ℝ) - Fintype.card (Wiring.Vertex p out)) 0 +
    3 * Real.logb 2 (Fintype.card (Wiring.Vertex p out)) + C with hbound_def
  have hVpos : (0 : ℝ) < Fintype.card (Wiring.Vertex p out) := by
    exact_mod_cast Fintype.card_pos
  have hlogV : 0 ≤ Real.logb 2 (Fintype.card (Wiring.Vertex p out)) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast Fintype.card_pos)
  have bound_nonneg : 0 ≤ bound := by
    have : 0 ≤ (A + η) *
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
  have hbound : bound ≤ (A + η) * max ((s : ℝ) - (Wiring.read p out).card) 0 +
      3 * Real.logb 2 (n + 3 * s) + C := by
    have h₁ : (A + η) *
        max ((Fintype.card (Wiring.Edge p out) : ℝ) - Fintype.card (Wiring.Vertex p out)) 0 ≤
        (A + η) * max ((s : ℝ) - (Wiring.read p out).card) 0 :=
      mul_le_mul_of_nonneg_left (max_le_max hdiff le_rfl) (by linarith)
    have h₂ : Real.logb 2 (Fintype.card (Wiring.Vertex p out)) ≤ Real.logb 2 (n + 3 * s) :=
      (Real.logb_le_logb one_lt_two hVpos (hVpos.trans_le hV)).mpr hV
    linarith
  have hexp : ((2 : ℝ) ^ (⌊bound⌋₊ + 3) : ℝ) ≤
      (2 : ℝ) ^ ((A + η) * max ((s : ℝ) - (Wiring.read p out).card) 0 +
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
    _ ≤ (n + 3 * s) * (2 : ℝ) ^ ((A + η) * max ((s : ℝ) - (Wiring.read p out).card) 0 +
          3 * Real.logb 2 (n + 3 * s) + C + 3) * K ^ 2 := by
        apply mul_le_mul (mul_le_mul hV hexp (by positivity) (by positivity)) hK'
          (by positivity) (by positivity)

/-- The slack conditions of the general cores force a nonnegative circuit
slack: an ordering slack `0 ≤ η ≤ A² θ / 2` with `A > 0` gives `0 ≤ θ`. -/
theorem circuit_slack_nonneg {A η θ : ℝ} (hA : 0 < A) (hη : 0 ≤ η)
    (hηθ : η ≤ A ^ 2 * θ / 2) : 0 ≤ θ :=
  nonneg_of_mul_nonneg_right (by linarith : 0 ≤ A ^ 2 * θ) (by positivity)

/-- **The numeric core with a general ordering coefficient.** Let `A > 0`
be the ordering coefficient, `θ ≤ 1/A` the circuit slack, and
`0 ≤ η ≤ A² θ / 2` the ordering slack. A `K`-rectangle-free function with at
least `2 ^ (n - 2)` accepting inputs cannot satisfy the accepting-input bound
of the cut-counting lemma for a circuit with `s ≤ (1 + 1/A - θ) n` gates
reading `n'` inputs, when `n - n' < ⌈log₂ K⌉`, the wiring graph has at most
`M n` vertices, and `n` is large enough. The bound is taken as a hypothesis so
that the deterministic and nondeterministic assemblies share this argument. -/
theorem false_of_accepting_bound_of_log_coefficient {A η θ C M : ℝ} (hA : 0 < A)
    (hη : 0 ≤ η) (hηθ : η ≤ A ^ 2 * θ / 2) (hθA : θ ≤ 1 / A)
    {n : Nat} (hn : 2 ≤ n) {f : Cslib.BooleanFunction n} {K : Nat}
    (hacc : 2 ^ (n - 2) ≤ (accepting f).card) (hK1 : 1 < K)
    (hbig : 2 * K ^ 2 ≤ 2 ^ (n - 2))
    (hlog : (A + η + 2) * Real.logb 2 K + 4 * Real.logb 2 n +
      (A + η + 4 * Real.logb 2 M + C + 5) < A * θ / 2 * n)
    {s n' : Nat} (hs : (s : ℝ) ≤ (1 + 1 / A - θ) * n) (hn'le : n' ≤ n)
    (hread : n - n' < Nat.clog 2 K)
    {Vb : ℝ} (hVpos : 0 < Vb) (hVb : Vb ≤ M * n)
    (bound : (accepting f).card < K * 2 ^ (n - n') ∨
      ((accepting f).card : ℝ) ≤ Vb * (2 : ℝ) ^ ((A + η) * max ((s : ℝ) - n') 0 +
        3 * Real.logb 2 Vb + C + 3) * K ^ 2) : False := by
  have hacc_pos : 0 < (accepting f).card := lt_of_lt_of_le (Nat.two_pow_pos _) hacc
  set k := Nat.clog 2 K with hk_def
  have hlow : 2 ^ (k - 1) < K := Nat.pow_pred_clog_lt_self one_lt_two hK1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by lia : 1 ≤ n)
  have hlogK : 0 ≤ Real.logb 2 K :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast hK1.le)
  have hkR : (k : ℝ) < Real.logb 2 K + 1 := by
    rw [hk_def, ← Real.natCeil_logb_natCast 2 K]
    exact Nat.ceil_lt_add_one hlogK
  rcases bound with small | large
  · -- Few inputs are read: the count is below `K ^ 2`, contradicting the accepting bound.
    have h₁ : 2 ^ (n - n') ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right two_pos (by lia)
    have h₂ : (accepting f).card < K * K :=
      small.trans_le ((Nat.mul_le_mul_left K h₁).trans (Nat.mul_le_mul_left K hlow.le))
    have : K * K = K ^ 2 := by ring
    lia
  · -- The main case: compare exponents.
    have hreadR : (n : ℝ) - n' < k := by
      have : n - n' < k := hread
      have : ((n - n' : Nat) : ℝ) < k := by exact_mod_cast this
      rwa [Nat.cast_sub hn'le] at this
    have hθ := circuit_slack_nonneg hA hη hηθ
    have hAη : 0 ≤ A + η := by linarith
    -- The excess is at most `(1/A - θ) n + k`.
    have hmax : max ((s : ℝ) - n') 0 ≤ (1 / A - θ) * n + k := by
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hrest : 0 ≤ (1 / A - θ) * n := mul_nonneg (by linarith) (by positivity)
      have hsplit : (1 + 1 / A - θ) * (n : ℝ) = n + (1 / A - θ) * n := by ring
      exact max_le (by linarith) (by linarith)
    -- The ordering coefficient times the circuit slack leaves `A θ / 2` per input.
    have hcoef : (A + η) * (1 / A - θ) ≤ 1 - A * θ / 2 := by
      have h₁ : (A + η) * (1 / A - θ) = 1 - A * θ + η / A - η * θ := by
        field_simp
        ring
      have h₂ : η / A ≤ A * θ / 2 := by
        rw [div_le_iff₀ hA]
        nlinarith
      have h₃ : 0 ≤ η * θ := mul_nonneg hη hθ
      linarith
    have hprod : (A + η) * max ((s : ℝ) - n') 0 ≤
        (1 - A * θ / 2) * n + (A + η) * (Real.logb 2 K + 1) := by
      have h₁ := mul_le_mul_of_nonneg_left hmax hAη
      have h₂ : (A + η) * (1 / A - θ) * n ≤ (1 - A * θ / 2) * n :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      have h₃ : (A + η) * k ≤ (A + η) * (Real.logb 2 K + 1) :=
        mul_le_mul_of_nonneg_left hkR.le hAη
      have h₄ : (A + η) * ((1 / A - θ) * n + k) = (A + η) * (1 / A - θ) * n + (A + η) * k := by
        ring
      linarith
    have hMpos : 0 < M := by
      by_contra hM
      have : M * n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hM) (by positivity)
      linarith
    have hlogS : Real.logb 2 Vb ≤ Real.logb 2 M + Real.logb 2 n := by
      calc Real.logb 2 Vb ≤ Real.logb 2 (M * n) :=
            (Real.logb_le_logb one_lt_two hVpos (by positivity)).mpr hVb
        _ = Real.logb 2 M + Real.logb 2 n :=
            Real.logb_mul hMpos.ne' (by positivity)
    -- Take binary logarithms of the main inequality.
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (by lia : 0 < K)
    set X : ℝ := (A + η) * max ((s : ℝ) - n') 0 + 3 * Real.logb 2 Vb + C + 3
      with hX
    have hlower : (2 : ℝ) ^ ((n : ℝ) - 2) ≤ (accepting f).card := by
      have : ((2 : ℝ) ^ (n - 2 : Nat)) ≤ (accepting f).card := by exact_mod_cast hacc
      rwa [← Real.rpow_natCast, Nat.cast_sub hn] at this
    have hupper : ((accepting f).card : ℝ) ≤
        (2 : ℝ) ^ (Real.logb 2 Vb + X + 2 * Real.logb 2 K) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num)
        (by norm_num) hVpos, show (2 : ℝ) ^ (2 * Real.logb 2 K) = ((2 : ℝ) ^ Real.logb 2 K) ^ 2 by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          push_cast
          ring_nf, Real.rpow_logb (by norm_num) (by norm_num) hKpos]
      exact large
    have hexp := (Real.rpow_le_rpow_left_iff one_lt_two).mp (hlower.trans hupper)
    linarith

/-- **The numeric core.** A `K`-rectangle-free function with at least
`2 ^ (n - 2)` accepting inputs cannot satisfy the accepting-input bound of
the cut-counting lemma for a circuit with `s ≤ (4 - 18 η) n` gates reading
`n'` inputs, when `n - n' < ⌈log₂ K⌉` and `n` is large enough. This is the
general core at coefficient `A = 1/3` with `θ = 18 η`. -/
theorem false_of_accepting_bound_of_log {η C : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 18)
    {n : Nat} (hn : 2 ≤ n) {f : Cslib.BooleanFunction n} {K : Nat}
    (hacc : 2 ^ (n - 2) ≤ (accepting f).card) (hK1 : 1 < K)
    (hbig : 2 * K ^ 2 ≤ 2 ^ (n - 2))
    (hlog : 4 * Real.logb 2 n + 3 * Real.logb 2 K + (C + 22) < 3 * η * n)
    {s n' : Nat} (hs : (s : ℝ) ≤ (4 - 18 * η) * n) (hn'le : n' ≤ n)
    (hread : n - n' < Nat.clog 2 K)
    {Vb : ℝ} (hVpos : 0 < Vb) (hVb : Vb ≤ 16 * n)
    (bound : (accepting f).card < K * 2 ^ (n - n') ∨
      ((accepting f).card : ℝ) ≤ Vb * (2 : ℝ) ^ ((1 / 3 + η) * max ((s : ℝ) - n') 0 +
        3 * Real.logb 2 Vb + C + 3) * K ^ 2) : False := by
  have hlogK : 0 ≤ Real.logb 2 K :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast hK1.le)
  have h16 : Real.logb 2 16 = 4 := by
    rw [show (16 : ℝ) = 2 ^ (4 : Nat) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one one_lt_two]
    norm_num
  have hηK := mul_le_mul_of_nonneg_right hη1 hlogK
  refine false_of_accepting_bound_of_log_coefficient (A := 1 / 3) (θ := 18 * η) (M := 16)
    (by norm_num) hη.le (le_of_eq (by ring)) (by norm_num; linarith) hn hacc hK1 hbig ?_
    (by rw [show (1 : ℝ) + 1 / (1 / 3) - 18 * η = 4 - 18 * η by ring]; exact hs)
    hn'le hread hVpos hVb bound
  rw [h16]
  linarith

/-- The polynomial-threshold numeric core follows from the logarithmic core;
this preserves the original deterministic and nondeterministic interface. -/
theorem false_of_accepting_bound {η C : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 18)
    {n : Nat} (hn : 2 ≤ n) {f : Cslib.BooleanFunction n} {K c : Nat} (hK : K ≤ n ^ c)
    (hacc : 2 ^ (n - 2) ≤ (accepting f).card) (hK1 : 1 < K)
    (hpow : 8 * n ^ (2 * c) ≤ 2 ^ n)
    (hlog : (4 + 3 * c) * Real.logb 2 n + (C + 22) < 3 * η * n)
    {s n' : Nat} (hs : (s : ℝ) ≤ (4 - 18 * η) * n) (hn'le : n' ≤ n)
    (hread : n - n' < Nat.clog 2 K)
    {Vb : ℝ} (hVpos : 0 < Vb) (hVb : Vb ≤ 16 * n)
    (bound : (accepting f).card < K * 2 ^ (n - n') ∨
      ((accepting f).card : ℝ) ≤ Vb * (2 : ℝ) ^ ((1 / 3 + η) * max ((s : ℝ) - n') 0 +
        3 * Real.logb 2 Vb + C + 3) * K ^ 2) : False := by
  have hpow' : 2 ^ n = 4 * 2 ^ (n - 2) := by
    calc 2 ^ n = 2 ^ (n - 2 + 2) := by rw [Nat.sub_add_cancel hn]
      _ = 4 * 2 ^ (n - 2) := by rw [pow_add]; ring
  have hbig : 2 * K ^ 2 ≤ 2 ^ (n - 2) := by
    have : K ^ 2 ≤ n ^ (2 * c) := by
      rw [mul_comm, pow_mul]
      exact Nat.pow_le_pow_left hK 2
    lia
  have hlogK : Real.logb 2 K ≤ c * Real.logb 2 n := by
    have h := (Real.logb_le_logb one_lt_two (by exact_mod_cast (by lia : 0 < K))
      (by positivity)).mpr (show (K : ℝ) ≤ (n : ℝ) ^ c by exact_mod_cast hK)
    rwa [Real.logb_pow] at h
  exact false_of_accepting_bound_of_log hη hη1 hn hacc hK1 hbig
    (by linarith) hs hn'le hread hVpos hVb bound

/-- **The fixed-`n` core with a general ordering coefficient.** With the
graph-ordering hypothesis for coefficient `A > 0` and slack `0 ≤ η ≤ A² θ / 2`,
where `θ ≤ 1/A`, a `K`-rectangle-free function with at least `2 ^ (n - 2)`
accepting inputs needs more than `(1 + 1/A - θ) n` binary gates, provided its
threshold and the logarithmic overhead satisfy the stated numeric conditions. -/
theorem lt_size_of_orderingBound {A η θ C : ℝ} (hA : 0 < A) (hη : 0 ≤ η)
    (hηθ : η ≤ A ^ 2 * θ / 2) (hθA : θ ≤ 1 / A) (hC : 0 ≤ C)
    (order : Multigraph.OrderingBound A η C)
    {n : Nat} (hn : 2 ≤ n) {f : Cslib.BooleanFunction n} {K : Nat}
    (hacc : 2 ^ (n - 2) ≤ (accepting f).card) (hrect : RectangleFree f K)
    (hbig : 2 * K ^ 2 ≤ 2 ^ (n - 2))
    (hlog : (A + η + 2) * Real.logb 2 K + 4 * Real.logb 2 n +
      (A + η + 4 * Real.logb 2 (4 + 3 / A) + C + 5) < A * θ / 2 * n)
    (circuit : Circuit Binary.signature n 1)
    (computes : circuit.Computes Binary.interpretation fun x _ => f x) :
    (1 + 1 / A - θ) * n < circuit.size := by
  rcases circuit with @⟨s, program, outputs⟩
  by_contra hs
  rw [not_lt] at hs
  -- Basic facts about `K`, `⌈log₂ K⌉`, and the slack.
  have hacc_pos : 0 < (accepting f).card := lt_of_lt_of_le (Nat.two_pow_pos _) hacc
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp hacc_pos
  have hK1 : 1 < K := hrect.one_lt (mem_accepting.mp hx₀)
  set k := Nat.clog 2 K with hk_def
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by lia : 1 ≤ n)
  have hlogn : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two hn1
  have hlogK : 0 ≤ Real.logb 2 K :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast hK1.le)
  have hkR : (k : ℝ) < Real.logb 2 K + 1 := by
    rw [hk_def, ← Real.natCeil_logb_natCast 2 K]
    exact Nat.ceil_lt_add_one hlogK
  have hθ := circuit_slack_nonneg hA hη hηθ
  have hAθ : A * θ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hθA hA.le
    rwa [mul_one_div_cancel hA.ne'] at this
  have hAη : 0 ≤ A + η := by linarith
  have hlogM : 0 ≤ Real.logb 2 (4 + 3 / A) :=
    Real.logb_nonneg one_lt_two (by have : 0 ≤ 3 / A := (by positivity); linarith)
  -- The circuit's output wire.
  obtain ⟨g, hg⟩ : ∃ g, outputs 0 = g := ⟨_, rfl⟩
  have eval_eq : ∀ x, f x = program.trace Binary.interpretation x g := by
    intro x
    rw [← hg]
    exact (congrFun (computes x) 0).symm
  -- The function depends only on the inputs read by the output cone, and
  -- that cone must contain all but fewer than `k` inputs.
  have support : ∀ R : Finset (Fin n), DependsOnlyOn f R → n - R.card < k :=
    fun R hR => sub_card_lt_clog hK1 hrect hacc hbig hR
  revert eval_eq
  cases g with
  | input j =>
    -- The output is an input wire: the function ignores all but one coordinate.
    intro eval_eq
    have hR : DependsOnlyOn f {j} := by
      intro x y agree
      rw [eval_eq, eval_eq, Program.trace_input, Program.trace_input]
      exact agree j (Finset.mem_singleton_self j)
    have := support {j} hR
    rw [Finset.card_singleton] at this
    have h' : ((n - 1 : Nat) : ℝ) < k := by exact_mod_cast (by lia : n - 1 < k)
    rw [Nat.cast_sub (by lia), Nat.cast_one] at h'
    have hAηK : 0 ≤ (A + η) * Real.logb 2 K := mul_nonneg hAη hlogK
    have hhalf : A * θ / 2 * n ≤ 1 / 2 * n :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  | gate out =>
    intro eval_eq
    set p := program with hp
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
    have hVb : ((n : ℝ) + 3 * s) ≤ (4 + 3 / A) * n := by
      have hs' : (s : ℝ) ≤ (1 + 1 / A - θ) * n := hs
      have h₁ : (1 + 1 / A - θ) * (n : ℝ) ≤ (1 + 1 / A) * n :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h₂ : (4 + 3 / A) * (n : ℝ) = n + 3 * ((1 + 1 / A) * n) := by ring
      linarith
    exact false_of_accepting_bound_of_log_coefficient hA hη hηθ hθA hn hacc' hK1 hbig hlog hs
      hn'le hread (by positivity) hVb (card_accepting_le_of_orderingBound hAη hC order p out hK1
        hrect')

/-- The coefficient-four logarithmic condition implies the condition of the
general cores at `A = 1/3` and `θ = 18 η`. -/
theorem log_condition_one_third {η C : ℝ} (hη1 : η ≤ 1 / 18) {n K : ℝ}
    (hlogK : 0 ≤ Real.logb 2 K)
    (hlog : 4 * Real.logb 2 n + 3 * Real.logb 2 K + (C + 22) < 3 * η * n) :
    (1 / 3 + η + 2) * Real.logb 2 K + 4 * Real.logb 2 n +
      (1 / 3 + η + 4 * Real.logb 2 (4 + 3 / (1 / 3)) + C + 5) < 1 / 3 * (18 * η) / 2 * n := by
  have h13 : Real.logb 2 (4 + 3 / (1 / 3)) ≤ 4 := by
    rw [show (4 : ℝ) + 3 / (1 / 3) = 13 by norm_num]
    calc Real.logb 2 13 ≤ Real.logb 2 16 :=
          (Real.logb_le_logb one_lt_two (by norm_num) (by norm_num)).mpr (by norm_num)
      _ = 4 := by
          rw [show (16 : ℝ) = 2 ^ (4 : Nat) by norm_num, Real.logb_pow,
            Real.logb_self_eq_one one_lt_two]
          norm_num
  have hηK := mul_le_mul_of_nonneg_right hη1 hlogK
  linarith

/-- **The fixed-`n` core of the lower bound.** With the graph-ordering
hypothesis for slack `η ≤ 1/18`, a `K`-rectangle-free function with at least
`2 ^ (n - 2)` accepting inputs needs more than `(4 - 18 η) n` binary gates,
provided its threshold and the logarithmic overhead satisfy the stated
numeric conditions. No polynomial-threshold assumption is needed. -/
theorem lt_size_of_log_bounds {η C : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 18) (hC : 0 ≤ C)
    (order : Multigraph.OrderingBound (1 / 3) η C)
    {n : Nat} (hn : 2 ≤ n) {f : Cslib.BooleanFunction n} {K : Nat}
    (hacc : 2 ^ (n - 2) ≤ (accepting f).card) (hrect : RectangleFree f K)
    (hbig : 2 * K ^ 2 ≤ 2 ^ (n - 2))
    (hlog : 4 * Real.logb 2 n + 3 * Real.logb 2 K + (C + 22) < 3 * η * n)
    (circuit : Circuit Binary.signature n 1)
    (computes : circuit.Computes Binary.interpretation fun x _ => f x) :
    (4 - 18 * η) * n < circuit.size := by
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp (lt_of_lt_of_le (Nat.two_pow_pos _) hacc)
  have hK1 : 1 < K := hrect.one_lt (mem_accepting.mp hx₀)
  have hlogK : 0 ≤ Real.logb 2 K :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast hK1.le)
  have key := lt_size_of_orderingBound (A := 1 / 3) (θ := 18 * η) (by norm_num) hη.le
    (le_of_eq (by ring)) (by norm_num; linarith) hC order hn hacc hrect hbig
    (log_condition_one_third hη1 hlogK hlog) circuit computes
  rwa [show (1 : ℝ) + 1 / (1 / 3) - 18 * η = 4 - 18 * η by ring] at key

/-- The original polynomial-threshold circuit bound, obtained by bounding
the logarithm of the threshold in `lt_size_of_log_bounds`. -/
theorem lt_size_of_bounds {η C : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 18) (hC : 0 ≤ C)
    (order : Multigraph.OrderingBound (1 / 3) η C)
    {n : Nat} (hn : 2 ≤ n) {f : Cslib.BooleanFunction n} {K c : Nat} (hK : K ≤ n ^ c)
    (hacc : 2 ^ (n - 2) ≤ (accepting f).card) (hrect : RectangleFree f K)
    (hpow : 8 * n ^ (2 * c) ≤ 2 ^ n)
    (hlog : (4 + 3 * c) * Real.logb 2 n + (C + 22) < 3 * η * n)
    (circuit : Circuit Binary.signature n 1)
    (computes : circuit.Computes Binary.interpretation fun x _ => f x) :
    (4 - 18 * η) * n < circuit.size := by
  have hacc_pos : 0 < (accepting f).card := lt_of_lt_of_le (Nat.two_pow_pos _) hacc
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hacc_pos
  have hK1 : 1 < K := hrect.one_lt (mem_accepting.mp hx)
  have hpow' : 2 ^ n = 4 * 2 ^ (n - 2) := by
    calc 2 ^ n = 2 ^ (n - 2 + 2) := by rw [Nat.sub_add_cancel hn]
      _ = 4 * 2 ^ (n - 2) := by rw [pow_add]; ring
  have hbig : 2 * K ^ 2 ≤ 2 ^ (n - 2) := by
    have : K ^ 2 ≤ n ^ (2 * c) := by
      rw [mul_comm, pow_mul]
      exact Nat.pow_le_pow_left hK 2
    lia
  have hlogK : Real.logb 2 K ≤ c * Real.logb 2 n := by
    have h := (Real.logb_le_logb one_lt_two (by exact_mod_cast (by lia : 0 < K))
      (by positivity)).mpr (show (K : ℝ) ≤ (n : ℝ) ^ c by exact_mod_cast hK)
    rwa [Real.logb_pow] at h
  exact lt_size_of_log_bounds hη hη1 hC order hn hacc hrect hbig
    (by linarith) circuit computes

/-- A sublinear logarithmic threshold eventually satisfies the finite
square bound needed to recover almost all input coordinates. -/
theorem eventually_two_mul_sq_le_pow_of_log {K : Nat → Nat}
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ))) :
    ∀ᶠ n in atTop, 2 * K n ^ 2 ≤ 2 ^ (n - 2) := by
  filter_upwards [hK.def (by norm_num : (0 : ℝ) < 1 / 4), eventually_ge_atTop 6]
    with n hlog hn
  by_cases hzero : K n = 0
  · simp [hzero]
  have hpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero hzero
  have hlogK : Real.logb 2 (K n) ≤ (n : ℝ) / 4 := by
    have h := (le_abs_self (Real.logb 2 (K n))).trans
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using hlog)
    linarith
  have hlogs : Real.logb 2 (2 * (K n : ℝ) ^ 2) ≤ Real.logb 2 ((2 : ℝ) ^ (n - 2)) := by
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow, Real.logb_pow,
      Real.logb_self_eq_one one_lt_two, mul_one]
    rw [Nat.cast_sub (by lia : 2 ≤ n)]
    push_cast
    have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h := (Real.logb_le_logb one_lt_two (by positivity) (by positivity)).mp hlogs
  exact_mod_cast h

/-- A subexponential threshold fits in either half of the input cube for
all sufficiently large input lengths. -/
theorem eventually_le_pow_half_of_log {K : Nat → Nat}
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ))) :
    ∀ᶠ n in atTop, K n ≤ 2 ^ (n / 2) := by
  filter_upwards [eventually_two_mul_sq_le_pow_of_log hK] with n hn
  have hp : 2 ^ (n - 2) ≤ (2 ^ (n / 2)) ^ 2 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right two_pos (by lia)
  have hsq : K n ^ 2 ≤ (2 ^ (n / 2)) ^ 2 := (by lia : K n ^ 2 ≤ 2 ^ (n - 2)).trans hp
  exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hsq

/-- **Slack selection for the general asymptotic bounds.** Given the
graph-ordering hypothesis with coefficient `A > 0` at every positive slack, a
threshold with `log₂ K(n) = o(n)`, and `ε > 0`, some circuit slack
`θ ≤ min(ε, 1/A)`, ordering slack `η`, and constant `C ≥ 0` satisfy the
hypotheses of the general fixed-`n` cores, and their logarithmic condition
holds for all sufficiently large `n`. -/
theorem exists_slack_eventually_log_condition {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) (K : Nat → Nat)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ))) {ε : ℝ} (hε : 0 < ε) :
    ∃ θ η C : ℝ, 0 ≤ η ∧ η ≤ A ^ 2 * θ / 2 ∧ θ ≤ 1 / A ∧ θ ≤ ε ∧ 0 ≤ C ∧
      Multigraph.OrderingBound A η C ∧
      ∀ᶠ n : Nat in atTop, (A + η + 2) * Real.logb 2 (K n) + 4 * Real.logb 2 n +
        (A + η + 4 * Real.logb 2 (4 + 3 / A) + C + 5) < A * θ / 2 * n := by
  obtain ⟨θ, hθ, hθA, hθε⟩ : ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / A ∧ θ ≤ ε :=
    ⟨min ε (1 / A), lt_min hε (by positivity), min_le_right _ _, min_le_left _ _⟩
  obtain ⟨η, hη, hηθ⟩ : ∃ η : ℝ, 0 < η ∧ η = A ^ 2 * θ / 2 := ⟨_, by positivity, rfl⟩
  obtain ⟨C, hC⟩ := order η hη
  refine ⟨θ, η, max C 0, hη.le, hηθ.le, hθA, hθε, le_max_right C 0,
    hC.mono le_rfl (le_max_left _ _), ?_⟩
  have hAη : 0 < A + η + 2 := by positivity
  filter_upwards [eventually_mul_logb_add_lt 4
      (A + η + 4 * Real.logb 2 (4 + 3 / A) + max C 0 + 5) (by positivity : 0 < A * θ / 4),
    hK.def (by positivity : 0 < A * θ / (4 * (A + η + 2)))] with n hlogn hKn
  have hlogK : Real.logb 2 (K n) ≤ A * θ / (4 * (A + η + 2)) * n :=
    (le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using hKn)
  have hlogK' : (A + η + 2) * Real.logb 2 (K n) ≤ A * θ / 4 * n := by
    calc (A + η + 2) * Real.logb 2 (K n) ≤
          (A + η + 2) * (A * θ / (4 * (A + η + 2)) * n) :=
          mul_le_mul_of_nonneg_left hlogK hAη.le
      _ = A * θ / 4 * n := by
          field_simp
  linarith

/-- **The circuit bound with a general ordering coefficient.** Assume the
graph-ordering hypothesis with coefficient `A > 0` for every slack `η > 0`,
and a family `f n` that is `K n`-rectangle-free with `log₂ K(n) = o(n)` and
has at least `2 ^ (n - 2)` accepting inputs for all large `n`. Then for every
`ε > 0` and all sufficiently large `n`, every binary circuit computing `f n`
has more than `(1 + 1/A - ε) n` gates. -/
theorem eventually_lt_size_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => f n x) →
        (1 + 1 / A - ε) * n < circuit.size := by
  obtain ⟨θ, η, C, hη, hηθ, hθA, hθε, hC, order', hlog⟩ :=
    exists_slack_eventually_log_condition hA order K hK hε
  filter_upwards [hacc, hrect, hlog, eventually_two_mul_sq_le_pow_of_log hK, eventually_ge_atTop 2]
    with n haccn hrectn hlogn hbign hn circuit computes
  have key := lt_size_of_orderingBound hA hη hηθ hθA hC order' hn haccn hrectn hbign hlogn
    circuit computes
  have : (1 + 1 / A - ε) * n ≤ (1 + 1 / A - θ) * n :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  exact this.trans_lt key

/-- **The circuit bound from a cubic cutwidth bound.** If for every slack
`ξ > 0` all sufficiently large simple cubic graphs on `h` vertices have
orderings whose prefix cuts have at most `(c + ξ) h` edges, then the
hypotheses of `eventually_lt_size_of_orderingBound` give more than
`(1 + 1/(2c) - ε) n` gates. -/
theorem eventually_lt_size_of_cutwidthBound {c : ℝ} (hc : 0 < c)
    (cutwidth : ∀ ξ : ℝ, 0 < ξ → ∃ N₀ : Nat, CutwidthBound c ξ N₀)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => f n x) →
        (1 + 1 / (2 * c) - ε) * n < circuit.size :=
  eventually_lt_size_of_orderingBound (by positivity)
    (Multigraph.exists_orderingBound_of_cutwidthBound hc.le cutwidth) f K hK hacc hrect hε

/-- **The circuit bound from a cubic pathwidth bound with coefficient `p`.**
If for every slack `ξ > 0` all sufficiently large simple cubic graphs on `h`
vertices have path decompositions of width at most `(p + ξ) h`, then the
hypotheses of `eventually_lt_size_of_orderingBound` give more than
`(1 + 1/(2p) - ε) n` gates. -/
theorem eventually_lt_size_of_pathwidthCoefficient {p : ℝ} (hp : 0 < p)
    (pathwidth : ∀ ξ : ℝ, 0 < ξ → ∃ N₀ : Nat, PathwidthBound p ξ N₀)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => f n x) →
        (1 + 1 / (2 * p) - ε) * n < circuit.size :=
  eventually_lt_size_of_orderingBound (by positivity)
    (Multigraph.exists_orderingBound_of_pathwidthBound hp.le pathwidth) f K hK hacc hrect hε

/-- **Subexponential-threshold circuit bound.** The coefficient four only
needs `log₂ K(n) = o(n)`; the threshold itself need not be polynomial.
The graph-ordering theorem and the hard-family properties are still explicit
hypotheses. This is `eventually_lt_size_of_orderingBound` at `A = 1/3`. -/
theorem eventually_lt_size_of_log_sublinear
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound (1 / 3) η C)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => f n x) →
        (4 - ε) * n < circuit.size := by
  filter_upwards [eventually_lt_size_of_orderingBound (by norm_num) order f K hK hacc hrect hε]
    with n hn circuit computes
  have := hn circuit computes
  rwa [show (1 : ℝ) + 1 / (1 / 3) = 4 by norm_num] at this

/-- Polynomial thresholds have sublinear binary logarithms. This includes
the value zero, whose real logarithm is defined to be zero. -/
theorem logb_isLittleO_of_eventually_le_pow {K : Nat → Nat} {c : Nat}
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c) :
    (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)) := by
  apply Asymptotics.IsLittleO.of_bound
  intro δ hδ
  filter_upwards [hK, eventually_mul_logb_add_lt c 0 hδ, eventually_ge_atTop 1]
    with n hKn hlog hn
  by_cases hzero : K n = 0
  · simp only [hzero, Nat.cast_zero, Real.logb_zero, norm_zero]
    positivity
  have hpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero hzero
  have hnonneg : 0 ≤ Real.logb 2 (K n) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero)
  have hbound : Real.logb 2 (K n) ≤ c * Real.logb 2 n := by
    have h := (Real.logb_le_logb one_lt_two hpos (by positivity)).mpr
      (show (K n : ℝ) ≤ (n : ℝ) ^ c by exact_mod_cast hKn)
    rwa [Real.logb_pow] at h
  rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (Nat.cast_nonneg n)]
  linarith

/-- **Theorem 1.** Assume the graph-ordering lemma for every slack `η > 0` and
a family of functions `f n` that is `K n`-rectangle-free with `K n ≤ n ^ c`
and at least `2 ^ (n - 2)` accepting inputs, for all large `n`. Then for every
`ε > 0` and all sufficiently large `n`, every binary circuit computing `f n`
has more than `(4 - ε) n` gates. -/
theorem eventually_lt_size
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound (1 / 3) η C)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) (c : Nat)
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c)
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => f n x) →
        (4 - ε) * n < circuit.size := by
  exact eventually_lt_size_of_log_sublinear order f K
    (logb_isLittleO_of_eventually_le_pow hK) hacc hrect hε

/-- The subexponential-threshold lower bound from the cubic pathwidth theorem. -/
theorem eventually_lt_size_of_pathwidthBound_of_log_sublinear
    (pathwidth : ∀ ξ : ℝ, 0 < ξ → ∃ N₀ : Nat, PathwidthBound (1 / 6) ξ N₀)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => f n x) →
        (4 - ε) * n < circuit.size :=
  eventually_lt_size_of_log_sublinear
    (Multigraph.exists_orderingBound_one_third_of_pathwidthBound pathwidth) f K hK hacc hrect hε

/-- The coefficient-four lower bound with only the cubic bisection theorem
and the hard-family properties as hypotheses. The pathwidth reduction is proved. -/
theorem eventually_lt_size_of_bisectionBound_of_log_sublinear
    (bisection : ∀ ξ : ℝ, 0 < ξ → ∃ N₀ : Nat, BisectionBound ξ N₀)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => f n x) →
        (4 - ε) * n < circuit.size :=
  eventually_lt_size_of_pathwidthBound_of_log_sublinear
    (pathwidthBound_of_bisectionBound bisection) f K hK hacc hrect hε

/-- **Theorem 1 from the pathwidth hypothesis.** The graph-ordering hypothesis
is replaced by the pathwidth bound for simple cubic graphs: for every `ξ > 0`
there is a threshold beyond which every simple 3-regular graph on `h`
vertices has a path decomposition of width at most `(1/6 + ξ) h`. -/
theorem eventually_lt_size_of_pathwidthBound
    (pathwidth : ∀ ξ : ℝ, 0 < ξ → ∃ N₀ : Nat, PathwidthBound (1 / 6) ξ N₀)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) (c : Nat)
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c)
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => f n x) →
        (4 - ε) * n < circuit.size :=
  eventually_lt_size (Multigraph.exists_orderingBound_one_third_of_pathwidthBound pathwidth)
    f K c hK hacc hrect hε

/-- A dense rectangle-free family with sublinear logarithmic threshold has
the coefficient-four circuit lower bound. The graph bounds are proved;
only the stated hard-family properties remain to be supplied. -/
theorem eventually_lt_size_of_rectangleFree
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => f n x) →
        (4 - ε) * n < circuit.size :=
  eventually_lt_size_of_bisectionBound_of_log_sublinear
    (fun _ h => Bisection.exists_bisectionBound h) f K hK hacc hrect hε

end Cutwidth
end Algebraic
