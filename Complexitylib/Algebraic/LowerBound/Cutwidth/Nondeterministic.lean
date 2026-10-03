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
nondeterminism does not reduce the size below `(4 - ε) n` for any
rectangle-free family with the hypotheses of `eventually_lt_size`. The bound
`Wiring.card_vertex_le_two_mul_size` makes the graph size independent of the
number of declared inputs, so the witness count `m` is unrestricted.
`nondet_eventually_lt_size_of_log_sublinear` only needs `log₂ K(n) = o(n)`.

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
theorem nondet_card_accepting_le_of_orderingBound {η C : ℝ} (hη : 0 ≤ η) (hC : 0 ≤ C)
    (order : Multigraph.OrderingBound η C)
    {n m s : Nat} (p : Program Binary.signature (n + m) s) (out : Fin s) {K : Nat} (hK : 1 < K)
    (hrect : RectangleFree (nondetGateFunction p out) K) :
    (accepting (nondetGateFunction p out)).card <
        K * 2 ^ (n - (Wiring.network p out).forget.read.card) ∨
      ((accepting (nondetGateFunction p out)).card : ℝ) ≤
        (2 * s + 1) * (2 : ℝ) ^ ((1 / 3 + η) *
          max ((s : ℝ) - (Wiring.network p out).forget.read.card) 0 +
          3 * Real.logb 2 (2 * s + 1) + C + 3) * K ^ 2 := by
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
  have hbound : bound ≤ (1 / 3 + η) * max ((s : ℝ) - (Wiring.network p out).forget.read.card) 0 +
      3 * Real.logb 2 (2 * s + 1) + C := by
    have h₁ : (1 / 3 + η) *
        max ((Fintype.card (Wiring.Edge p out) : ℝ) - Fintype.card (Wiring.Vertex p out)) 0 ≤
        (1 / 3 + η) * max ((s : ℝ) - (Wiring.network p out).forget.read.card) 0 :=
      mul_le_mul_of_nonneg_left (max_le_max hdiff le_rfl) (by linarith)
    have h₂ : Real.logb 2 (Fintype.card (Wiring.Vertex p out)) ≤ Real.logb 2 (2 * s + 1) :=
      (Real.logb_le_logb one_lt_two hVpos (hVpos.trans_le hV)).mpr hV
    linarith
  have hexp : ((2 : ℝ) ^ (⌊bound⌋₊ + 3) : ℝ) ≤
      (2 : ℝ) ^ ((1 / 3 + η) * max ((s : ℝ) - (Wiring.network p out).forget.read.card) 0 +
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
    _ ≤ (2 * s + 1) * (2 : ℝ) ^ ((1 / 3 + η) *
          max ((s : ℝ) - (Wiring.network p out).forget.read.card) 0 +
          3 * Real.logb 2 (2 * s + 1) + C + 3) * K ^ 2 := by
        apply mul_le_mul (mul_le_mul hV hexp (by positivity) (by positivity)) hK'
          (by positivity) (by positivity)

/-- **The fixed-`n` core for nondeterministic circuits.** The logarithmic
conditions are those of `lt_size_of_log_bounds`. The number of witness inputs
is unrestricted: only the reachable graph, with at most `2 s + 1` vertices,
enters the counting argument. -/
theorem nondet_lt_size_of_log_bounds {η C : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 18) (hC : 0 ≤ C)
    (order : Multigraph.OrderingBound η C)
    {n : Nat} (hn : 2 ≤ n) {f : Cslib.BooleanFunction n} {K : Nat}
    (hacc : 2 ^ (n - 2) ≤ (accepting f).card) (hrect : RectangleFree f K)
    (hbig : 2 * K ^ 2 ≤ 2 ^ (n - 2))
    (hlog : 4 * Real.logb 2 n + 3 * Real.logb 2 K + (C + 22) < 3 * η * n)
    {m : Nat} (circuit : Circuit Binary.signature (n + m) 1)
    (computes : NondetComputes circuit f) :
    (4 - 18 * η) * n < circuit.size := by
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
    have hs' : (circuit.size : ℝ) ≤ (4 - 18 * η) * n := hs
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hVb : ((2 : ℝ) * circuit.size + 1) ≤ 16 * n := by nlinarith
    exact false_of_accepting_bound_of_log hη hη1 hC hn hacc' hK1 hbig hlog hs' hn'le hread
      (by positivity) hVb (nondet_card_accepting_le_of_orderingBound hη.le hC order p out hK1 hrect')

/-- The polynomial-threshold nondeterministic bound with an arbitrary
number of witness inputs. -/
theorem nondet_lt_size_of_bounds {η C : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 18) (hC : 0 ≤ C)
    (order : Multigraph.OrderingBound η C)
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

/-- Sublinear source entropy suffices for the nondeterministic coefficient-four
bound, uniformly over every number of witness inputs. -/
theorem nondet_eventually_lt_size_of_log_sublinear
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound η C)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (m : Nat) (circuit : Circuit Binary.signature (n + m) 1),
      NondetComputes circuit (f n) → (4 - ε) * n < circuit.size := by
  let η := min ε 1 / 18
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 / 18 := by dsimp [η]; linarith [min_le_right ε 1]
  obtain ⟨C, hC⟩ := order η hη
  have order' : Multigraph.OrderingBound η (max C 0) := hC.mono (le_max_left _ _)
  have hlog := eventually_mul_logb_add_lt 4 (max C 0 + 22)
    (by positivity : 0 < 3 * η / 2)
  filter_upwards [hacc, hrect, hlog, hK.def (by positivity : 0 < η / 2),
    eventually_two_mul_sq_le_pow_of_log hK, eventually_ge_atTop 2]
    with n haccn hrectn hlogn hKn hbign hn
  intro m circuit computes
  have hlogK : Real.logb 2 (K n) ≤ η / 2 * n :=
    (le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using hKn)
  have key := nondet_lt_size_of_log_bounds hη hη1 (le_max_right C 0) order' hn
    haccn hrectn hbign (by linarith) circuit computes
  have : (4 - ε) * n ≤ (4 - 18 * η) * n := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp [η]
    linarith [min_le_left ε 1]
  exact this.trans_lt key

/-- **Nondeterministic circuits.** Under the graph-ordering hypothesis and the
hypotheses of `eventually_lt_size` on the family `f n`, for every `ε > 0` and
all sufficiently large `n`, every circuit on `n + m` inputs that
computes `f n` nondeterministically has more than `(4 - ε) n` gates. -/
theorem nondet_eventually_lt_size
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound η C)
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
    (pathwidth : ∀ ξ : ℝ, 0 < ξ → ∃ N₀ : Nat, PathwidthBound ξ N₀)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) (c : Nat)
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c)
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (m : Nat) (circuit : Circuit Binary.signature (n + m) 1),
      NondetComputes circuit (f n) → (4 - ε) * n < circuit.size := by
  refine nondet_eventually_lt_size (fun η hη => ?_) f K c hK hacc hrect hε
  obtain ⟨N₀, hN₀⟩ := pathwidth (η / 2) (by positivity)
  refine ⟨N₀ + 9, ?_⟩
  have := Multigraph.orderingBound_of_pathwidthBound (by positivity) hN₀
  rwa [show 2 * (η / 2) = η by ring] at this

end Cutwidth
end Algebraic
