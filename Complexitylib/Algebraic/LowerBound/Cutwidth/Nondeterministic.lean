/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.FourN
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Forget

/-!
# The `(4 - ε) n` bound for nondeterministic circuits

A nondeterministic circuit for `f : {0,1}ⁿ → {0,1}` is a circuit on `n + m`
inputs whose accepted inputs `x` are exactly those with some witness `y` for
which the output is `1`. Witness inputs are read by the wiring graph but carry
no port of the function computed, so the cut-counting lemma applies to the
forgotten network (`Network.forget`) with the same multigraph. The excess of
the wiring graph is the number of reachable gates minus the number of
reachable inputs, ordinary and witness alike, which is at most the number of
gates minus the number of ordinary inputs read. Hence the same bound holds:
nondeterminism does not reduce the size below `(4 - ε) n` for any dense
rectangle-free family with sublinear logarithmic threshold. The bound
`Wiring.card_vertex_le_two_mul_size` makes the graph size independent of the
number of declared inputs, so the witness count `m` is unrestricted.
`nondet_eventually_lt_size_of_rectangleFree` instantiates the proved graph
bounds and only needs `log₂ K(n) = o(n)`, rectangle-freeness, and the
accepting-input bound. The explicit family `Extractor.sourceReductionHardFamily`
meets these hypotheses through balanced padding, but no nondeterministic
corollary for it is stated; `SourceReduction.Construction.Hardness` states its
deterministic bounds. The generic graph-ordering interfaces are retained; as
in the deterministic case, an ordering coefficient `A > 0` gives the
circuit coefficient `1 + 1/A` (`nondet_eventually_lt_size_of_orderingBound`),
and a cubic cutwidth coefficient `c` gives `1 + 1/(2c)`.

The proof organization, the threshold-edge charging, the extractor
application, and the graph restoration argument of the deterministic bound
follow Ryan Williams's private working note (September 2026); this module
only replaces the wiring network by its forgotten version.
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth

open scoped Classical
open Filter

/-- The Boolean function computed nondeterministically by a circuit on
`n + m` inputs: `x` is accepted when some witness `y` makes the output `1`. -/
noncomputable def nondetFunction {n m : Nat} (circuit : Circuit Binary.signature (n + m) 1) :
    Cslib.BooleanFunction n :=
  fun x => decide (∃ y : Fin m → Bool, circuit.eval Binary.interpretation (Fin.append x y) 0 = true)

/-- A circuit on `n + m` inputs computes `f` nondeterministically when `f x = 1`
exactly when some witness makes the output `1`. -/
def NondetComputes {n m : Nat} (circuit : Circuit Binary.signature (n + m) 1)
    (f : Cslib.BooleanFunction n) : Prop :=
  ∀ x, f x = true ↔ ∃ y : Fin m → Bool, circuit.eval Binary.interpretation (Fin.append x y) 0 = true

theorem NondetComputes.eq_nondetFunction {n m : Nat} {circuit : Circuit Binary.signature (n + m) 1}
    {f : Cslib.BooleanFunction n} (h : NondetComputes circuit f) : f = nondetFunction circuit := by
  funext x
  rw [nondetFunction, Bool.eq_iff_iff, decide_eq_true_iff]
  exact h x

/-- The function computed nondeterministically by a program with `m` witness
inputs and output gate `out`. -/
noncomputable def nondetGateFunction {n m s : Nat} (p : Program Binary.signature (n + m) s)
    (out : Fin s) : Cslib.BooleanFunction n :=
  fun x => decide (∃ y : Fin m → Bool, p.eval Binary.interpretation (Fin.append x y) out = true)

/-- The forgotten wiring network computes the nondeterministic gate function. -/
theorem forget_network_computes {n m s : Nat} (p : Program Binary.signature (n + m) s)
    (out : Fin s) : (Wiring.network p out).forget.Computes (nondetGateFunction p out) :=
  (Wiring.network_computes p out).forget

/-- The nondeterministic version of the circuit-level bound: the ordinary
inputs read are those of the forgotten network, and the excess of the wiring
graph is at most `s` minus their number. -/
theorem nondet_card_accepting_le_of_orderingBound {A η C : ℝ} (hAη : 0 ≤ A + η)
    (hC : 0 ≤ C) (order : Multigraph.OrderingBound A η C)
    {n m s : Nat} (p : Program Binary.signature (n + m) s) (out : Fin s) {K : Nat} (hK : 1 < K)
    (hrect : RectangleFree (nondetGateFunction p out) K) :
    (accepting (nondetGateFunction p out)).card <
        K * 2 ^ (n - (Wiring.network p out).forget.read.card) ∨
      ((accepting (nondetGateFunction p out)).card : ℝ) ≤
        (2 * s + 1) * (2 : ℝ) ^ ((A + η) *
          max ((s : ℝ) - (Wiring.network p out).forget.read.card) 0 +
          3 * Real.logb 2 (2 * s + 1) + C + 3) * K ^ 2 := by
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
  have hw : ∀ v, ((Wiring.network p out).forget.cut (Network.below v)).card ≤ ⌊bound⌋₊ :=
    fun v => Nat.le_floor (hcut _ (Network.isLowerSet_below v))
  rcases (Wiring.network p out).forget.card_accepting_le (forget_network_computes p out)
    (Wiring.maxDegreeLE_three p out) hw hK hrect with h | h
  · exact Or.inl h
  right
  have hV : (Fintype.card (Wiring.Vertex p out) : ℝ) ≤ 2 * s + 1 := by
    exact_mod_cast Wiring.card_vertex_le_two_mul_size p out
  have hdiff : (Fintype.card (Wiring.Edge p out) : ℝ) - Fintype.card (Wiring.Vertex p out) ≤
      (s : ℝ) - (Wiring.network p out).forget.read.card := by
    rw [Wiring.card_edge_sub_card_vertex]
    have h₁ : (Fintype.card (Wiring.ReachableGate p out) : ℝ) ≤ s := by
      exact_mod_cast Wiring.card_reachableGate_le p out
    have h₂ : ((Wiring.network p out).forget.read.card : ℝ) ≤ (Wiring.read p out).card := by
      exact_mod_cast (Wiring.network p out).card_forget_read_le
    linarith
  have hbound : bound ≤ (A + η) * max ((s : ℝ) - (Wiring.network p out).forget.read.card) 0 +
      3 * Real.logb 2 (2 * s + 1) + C := by
    have h₁ : (A + η) *
        max ((Fintype.card (Wiring.Edge p out) : ℝ) - Fintype.card (Wiring.Vertex p out)) 0 ≤
        (A + η) * max ((s : ℝ) - (Wiring.network p out).forget.read.card) 0 :=
      mul_le_mul_of_nonneg_left (max_le_max hdiff le_rfl) (by linarith)
    have h₂ : Real.logb 2 (Fintype.card (Wiring.Vertex p out)) ≤ Real.logb 2 (2 * s + 1) :=
      (Real.logb_le_logb one_lt_two hVpos (hVpos.trans_le hV)).mpr hV
    linarith
  have hexp : ((2 : ℝ) ^ (⌊bound⌋₊ + 3) : ℝ) ≤
      (2 : ℝ) ^ ((A + η) * max ((s : ℝ) - (Wiring.network p out).forget.read.card) 0 +
        3 * Real.logb 2 (2 * s + 1) + C + 3) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    push_cast
    linarith [Nat.floor_le bound_nonneg]
  have hK' : (((K - 1 : Nat) : ℝ)) ^ 2 ≤ (K : ℝ) ^ 2 := by
    gcongr
    exact_mod_cast Nat.sub_le K 1
  calc ((accepting (nondetGateFunction p out)).card : ℝ)
      ≤ (Fintype.card (Wiring.Vertex p out) : ℝ) * (2 : ℝ) ^ (⌊bound⌋₊ + 3) *
          ((K - 1 : Nat) : ℝ) ^ 2 := by exact_mod_cast h
    _ ≤ (2 * s + 1) * (2 : ℝ) ^ ((A + η) *
          max ((s : ℝ) - (Wiring.network p out).forget.read.card) 0 +
          3 * Real.logb 2 (2 * s + 1) + C + 3) * K ^ 2 := by
        apply mul_le_mul (mul_le_mul hV hexp (by positivity) (by positivity)) hK'
          (by positivity) (by positivity)

/-- **The fixed-`n` nondeterministic core with a general ordering
coefficient.** The hypotheses are those of `lt_size_of_orderingBound`. The
number of witness inputs is unrestricted: only the reachable graph, with at
most `2 s + 1` vertices, enters the counting argument. -/
theorem nondet_lt_size_of_orderingBound {A η θ C : ℝ} (hA : 0 < A) (hη : 0 ≤ η)
    (hηθ : η ≤ A ^ 2 * θ / 2) (hθA : θ ≤ 1 / A) (hC : 0 ≤ C)
    (order : Multigraph.OrderingBound A η C)
    {n : Nat} (hn : 2 ≤ n) {f : Cslib.BooleanFunction n} {K : Nat}
    (hacc : 2 ^ (n - 2) ≤ (accepting f).card) (hrect : RectangleFree f K)
    (hbig : 2 * K ^ 2 ≤ 2 ^ (n - 2))
    (hlog : (A + η + 2) * Real.logb 2 K + 4 * Real.logb 2 n +
      (A + η + 4 * Real.logb 2 (4 + 3 / A) + C + 5) < A * θ / 2 * n)
    {m : Nat} (circuit : Circuit Binary.signature (n + m) 1)
    (computes : NondetComputes circuit f) :
    (1 + 1 / A - θ) * n < circuit.size := by
  have feq := computes.eq_nondetFunction
  by_contra hs
  rw [not_lt] at hs
  have hacc_pos : 0 < (accepting f).card := lt_of_lt_of_le (Nat.two_pow_pos _) hacc
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp hacc_pos
  have hK1 : 1 < K := hrect.one_lt (mem_accepting.mp hx₀)
  set k := Nat.clog 2 K with hk_def
  have hkn : k < n := by
    have : K ≤ 2 ^ (n - 2) := by nlinarith
    have : Nat.clog 2 K ≤ n - 2 := (Nat.clog_le_iff_le_pow one_lt_two).mpr this
    omega
  have hθ := circuit_slack_nonneg hA hη hηθ
  -- The circuit's output wire.
  obtain ⟨g, hg⟩ : ∃ g, circuit.outputs 0 = g := ⟨_, rfl⟩
  have eval_eq : ∀ z, circuit.eval Binary.interpretation z 0 =
      circuit.program.trace Binary.interpretation z g := by
    intro z
    rw [← hg]
    rfl
  have fdef : f = fun x => decide (∃ y : Fin m → Bool,
      circuit.program.trace Binary.interpretation (Fin.append x y) g = true) := by
    rw [feq]
    funext x
    simp only [nondetFunction, eval_eq]
  have support : ∀ R : Finset (Fin n), DependsOnlyOn f R → n - R.card < k :=
    fun R hR => sub_card_lt_clog hK1 hrect hacc hbig hR
  revert fdef
  cases g with
  | input j =>
    intro fdef
    induction j using Fin.addCases with
    | left j =>
      -- The output is an ordinary input: the function depends on one coordinate.
      have hR : DependsOnlyOn f {j} := by
        intro x y agree
        rw [fdef]
        simp only [Program.trace_input, Fin.append_left]
        rw [agree j (Finset.mem_singleton_self j)]
      have := support {j} hR
      rw [Finset.card_singleton] at this
      omega
    | right j =>
      -- The output is a witness input: the function is constantly `1`.
      have hR : DependsOnlyOn f ∅ := by
        intro x y _
        rw [fdef]
        simp only [Program.trace_input, Fin.append_right]
      have := support ∅ hR
      rw [Finset.card_empty] at this
      omega
  | gate out =>
    intro fdef
    set p := circuit.program with hp
    have feq' : f = nondetGateFunction p out := by
      rw [fdef]
      funext x
      simp only [nondetGateFunction, Program.trace_gateWire, Program.gateFunction_apply]
      rfl
    have hrect' : RectangleFree (nondetGateFunction p out) K := feq' ▸ hrect
    have hacc' : 2 ^ (n - 2) ≤ (accepting (nondetGateFunction p out)).card := feq' ▸ hacc
    set n' := (Wiring.network p out).forget.read.card with hn'
    have hread : n - n' < k := by
      have hR : DependsOnlyOn (nondetGateFunction p out) (Wiring.network p out).forget.read :=
        (forget_network_computes p out).dependsOnlyOn
      exact support _ (by rw [feq']; exact hR)
    have hn'le : n' ≤ n := by
      simpa using Finset.card_le_univ (Wiring.network p out).forget.read
    have hs' : (circuit.size : ℝ) ≤ (1 + 1 / A - θ) * n := hs
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hVb : ((2 : ℝ) * circuit.size + 1) ≤ (4 + 3 / A) * n := by
      have hA' : 0 ≤ 1 / A := by positivity
      have h₁ : (1 + 1 / A - θ) * (n : ℝ) ≤ (1 + 1 / A) * n :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h₂ : 0 ≤ 1 / A * n := by positivity
      have h₃ : (4 + 3 / A) * (n : ℝ) = 2 * ((1 + 1 / A) * n) + 2 * n + 1 / A * n := by ring
      linarith
    exact false_of_accepting_bound_of_log_coefficient hA hη hηθ hθA hn hacc' hK1 hbig hlog hs'
      hn'le hread (by positivity) hVb
      (nondet_card_accepting_le_of_orderingBound (by linarith) hC order p out hK1 hrect')

/-- **The fixed-`n` core for nondeterministic circuits.** The logarithmic
conditions are those of `lt_size_of_log_bounds`. The number of witness inputs
is unrestricted: only the reachable graph, with at most `2 s + 1` vertices,
enters the counting argument. -/
theorem nondet_lt_size_of_log_bounds {η C : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 18) (hC : 0 ≤ C)
    (order : Multigraph.OrderingBound (1 / 3) η C)
    {n : Nat} (hn : 2 ≤ n) {f : Cslib.BooleanFunction n} {K : Nat}
    (hacc : 2 ^ (n - 2) ≤ (accepting f).card) (hrect : RectangleFree f K)
    (hbig : 2 * K ^ 2 ≤ 2 ^ (n - 2))
    (hlog : 4 * Real.logb 2 n + 3 * Real.logb 2 K + (C + 22) < 3 * η * n)
    {m : Nat} (circuit : Circuit Binary.signature (n + m) 1)
    (computes : NondetComputes circuit f) :
    (4 - 18 * η) * n < circuit.size := by
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp (lt_of_lt_of_le (Nat.two_pow_pos _) hacc)
  have hK1 : 1 < K := hrect.one_lt (mem_accepting.mp hx₀)
  have hlogK : 0 ≤ Real.logb 2 K :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast hK1.le)
  have key := nondet_lt_size_of_orderingBound (A := 1 / 3) (θ := 18 * η) (by norm_num) hη.le
    (le_of_eq (by ring)) (by norm_num; linarith) hC order hn hacc hrect hbig
    (log_condition_one_third hη1 hlogK hlog) circuit computes
  rwa [show (1 : ℝ) + 1 / (1 / 3) - 18 * η = 4 - 18 * η by ring] at key

/-- The polynomial-threshold nondeterministic bound with an arbitrary
number of witness inputs. -/
theorem nondet_lt_size_of_bounds {η C : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 18) (hC : 0 ≤ C)
    (order : Multigraph.OrderingBound (1 / 3) η C)
    {n : Nat} (hn : 2 ≤ n) {f : Cslib.BooleanFunction n} {K c : Nat} (hK : K ≤ n ^ c)
    (hacc : 2 ^ (n - 2) ≤ (accepting f).card) (hrect : RectangleFree f K)
    (hpow : 8 * n ^ (2 * c) ≤ 2 ^ n)
    (hlog : (4 + 3 * c) * Real.logb 2 n + (C + 22) < 3 * η * n)
    {m : Nat} (circuit : Circuit Binary.signature (n + m) 1)
    (computes : NondetComputes circuit f) :
    (4 - 18 * η) * n < circuit.size := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (lt_of_lt_of_le (Nat.two_pow_pos _) hacc)
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
  exact nondet_lt_size_of_log_bounds hη hη1 hC order hn hacc hrect hbig
    (by linarith) circuit computes

/-- **Nondeterministic circuits with a general ordering coefficient.** Under
the hypotheses of `eventually_lt_size_of_orderingBound`, for every `ε > 0` and
all sufficiently large `n`, every circuit on `n + m` inputs that computes
`f n` nondeterministically has more than `(1 + 1/A - ε) n` gates, uniformly
over every number `m` of witness inputs. -/
theorem nondet_eventually_lt_size_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (m : Nat) (circuit : Circuit Binary.signature (n + m) 1),
      NondetComputes circuit (f n) → (1 + 1 / A - ε) * n < circuit.size := by
  obtain ⟨θ, η, C, hη, hηθ, hθA, hθε, hC, order', hlog⟩ :=
    exists_slack_eventually_log_condition hA order K hK hε
  filter_upwards [hacc, hrect, hlog, eventually_two_mul_sq_le_pow_of_log hK, eventually_ge_atTop 2]
    with n haccn hrectn hlogn hbign hn m circuit computes
  have key := nondet_lt_size_of_orderingBound hA hη hηθ hθA hC order' hn haccn hrectn hbign hlogn
    circuit computes
  have : (1 + 1 / A - ε) * n ≤ (1 + 1 / A - θ) * n :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  exact this.trans_lt key

/-- **Nondeterministic circuits from a cubic cutwidth bound.** A cutwidth
coefficient `c > 0` at every positive slack gives the nondeterministic
coefficient `1 + 1/(2c)`. -/
theorem nondet_eventually_lt_size_of_cutwidthBound {c : ℝ} (hc : 0 < c)
    (cutwidth : ∀ ξ : ℝ, 0 < ξ → ∃ N₀ : Nat, CutwidthBound c ξ N₀)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (m : Nat) (circuit : Circuit Binary.signature (n + m) 1),
      NondetComputes circuit (f n) → (1 + 1 / (2 * c) - ε) * n < circuit.size :=
  nondet_eventually_lt_size_of_orderingBound (by positivity)
    (Multigraph.exists_orderingBound_of_cutwidthBound hc.le cutwidth) f K hK hacc hrect hε

/-- **Nondeterministic circuits from a cubic pathwidth bound with coefficient
`p`.** A pathwidth coefficient `p > 0` at every positive slack gives the
nondeterministic coefficient `1 + 1/(2p)`. -/
theorem nondet_eventually_lt_size_of_pathwidthCoefficient {p : ℝ} (hp : 0 < p)
    (pathwidth : ∀ ξ : ℝ, 0 < ξ → ∃ N₀ : Nat, PathwidthBound p ξ N₀)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (m : Nat) (circuit : Circuit Binary.signature (n + m) 1),
      NondetComputes circuit (f n) → (1 + 1 / (2 * p) - ε) * n < circuit.size :=
  nondet_eventually_lt_size_of_orderingBound (by positivity)
    (Multigraph.exists_orderingBound_of_pathwidthBound hp.le pathwidth) f K hK hacc hrect hε

/-- Sublinear source entropy suffices for the nondeterministic coefficient-four
bound, uniformly over every number of witness inputs. This is
`nondet_eventually_lt_size_of_orderingBound` at `A = 1/3`. -/
theorem nondet_eventually_lt_size_of_log_sublinear
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound (1 / 3) η C)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (m : Nat) (circuit : Circuit Binary.signature (n + m) 1),
      NondetComputes circuit (f n) → (4 - ε) * n < circuit.size := by
  filter_upwards [nondet_eventually_lt_size_of_orderingBound (by norm_num) order f K hK hacc
    hrect hε] with n hn m circuit computes
  have := hn m circuit computes
  rwa [show (1 : ℝ) + 1 / (1 / 3) = 4 by norm_num] at this

/-- **Nondeterministic circuits.** Under the graph-ordering hypothesis and the
hypotheses of `eventually_lt_size` on the family `f n`, for every `ε > 0` and
all sufficiently large `n`, every circuit on `n + m` inputs that
computes `f n` nondeterministically has more than `(4 - ε) n` gates. -/
theorem nondet_eventually_lt_size
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound (1 / 3) η C)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) (c : Nat)
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c)
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (m : Nat) (circuit : Circuit Binary.signature (n + m) 1),
      NondetComputes circuit (f n) → (4 - ε) * n < circuit.size := by
  exact nondet_eventually_lt_size_of_log_sublinear order f K
    (logb_isLittleO_of_eventually_le_pow hK) hacc hrect hε

/-- **Nondeterministic circuits from the pathwidth hypothesis.** -/
theorem nondet_eventually_lt_size_of_pathwidthBound
    (pathwidth : ∀ ξ : ℝ, 0 < ξ → ∃ N₀ : Nat, PathwidthBound (1 / 6) ξ N₀)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) (c : Nat)
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c)
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (m : Nat) (circuit : Circuit Binary.signature (n + m) 1),
      NondetComputes circuit (f n) → (4 - ε) * n < circuit.size :=
  nondet_eventually_lt_size (Multigraph.exists_orderingBound_one_third_of_pathwidthBound pathwidth)
    f K c hK hacc hrect hε

/-- A dense rectangle-free family with sublinear logarithmic threshold
requires more than `(4 - ε) n` gates even with arbitrarily many witness
inputs. All graph bounds are instantiated by the proved cubic theorem. -/
theorem nondet_eventually_lt_size_of_rectangleFree
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (m : Nat) (circuit : Circuit Binary.signature (n + m) 1),
      NondetComputes circuit (f n) → (4 - ε) * n < circuit.size :=
  nondet_eventually_lt_size_of_log_sublinear Multigraph.exists_orderingBound_one_third
    f K hK hacc hrect hε

end Cutwidth
end Algebraic
