/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Compiler
public import Complexitylib.Circuits.Frontier.Demand
public import Complexitylib.Circuits.Frontier.Linear.TotallyRegular
public import Complexitylib.Circuits.Frontier.Linear.Linearize

/-!
# Lower bounds for linear maps

The frontier method applies to circuits with many outputs. Here the demand comes from linear
algebra instead of from counting rectangles.

Let a circuit over a field `F` compute `x ↦ M x` for an `N × N` matrix `M`, and compile it into
a network that accepts every value at every output. Cut the network along a set `P` of vertices:
`P` reads the inputs `X` and holds the outputs `Y`. If the runs on two inputs agree on the cut,
then splicing them (`Frontier.Compiler.trace_out_of_cut`) shows that the outputs in `Y` do not
see the inputs outside `X`, and the outputs outside `Y` do not see the inputs in `X`. When `M` is
totally regular and `|X| + |Y| = N`, both blocks `M[Y, X^c]` and `M[Y^c, X]` are square and
nonsingular, so the input is determined by the values on the cut
(`Frontier.exists_injective_cut`). Every layout passes through such a `P`, since `|X| + |Y|`
grows by at most one per vertex, from `0` to `2 N`.

How many values can a cut of `k` edges carry? A circuit has *linear capacity*
(`Frontier.LinearCapacity`) when `k` wires never determine more than `k` coordinates of the
input. This holds

* over a finite field, for every basis: `k` wires take at most `|F| ^ k` values
  (`Frontier.linearCapacity_of_finite`);
* over any field, for the affine basis: the values of `k` wires are an affine function of the
  input (`Frontier.linearCapacity_affine`);
* over an infinite field, for polynomial operations, after linearizing the circuit
  (`Frontier.exists_affine_circuit`).

It fails over infinite fields for arbitrary operations: a bijection `F × F → F` lets one wire
carry everything.

So every layout of the graph of the circuit has a frontier of at least `N` edges: the demand is
exactly `N`. The graph has cycle rank at most `(r - 1) s + 1 - N` for `s` inner gates of
fan-in `r`, and the comparison of demand and supply gives the same coefficient as for decision
problems.

**Main theorem** (`Frontier.lowerBound_linear`). Under `LayoutBound (r + 1) A`, for every
`ε > 0` and all large `N`, every circuit of fan-in at most `r` with linear capacity computing a
totally regular map `F^N → F^N` has `s` inner gates with `(r - 1) s > (1 + 1/A - ε) N`, uniformly
in the field. Constants are free.

## Main results

* `Frontier.exists_injective_cut`: some frontier of every layout determines the input.
* `Frontier.lowerBound_linear`: the lower bound, for circuits with linear capacity.
* `Frontier.lowerBound_linear_finite`, `Frontier.lowerBound_linear_affine`,
  `Frontier.lowerBound_linear_polynomial`: over finite fields with any basis, over any field with
  the affine basis, and over infinite fields with polynomial operations.
-/

@[expose] public section

namespace Complexity.Frontier

open Cslib.Circuits Set Filter Asymptotics Matrix

universe u v

/-! ### Linear capacity -/

section Capacity

variable {F : Type u} [Field F] {σ : Signature.{v}} {N m : ℕ}

/-- A circuit has *linear capacity* when its wires carry at most one element of the field each:
whenever the values of `k` wires determine the input, `N ≤ k`. -/
def LinearCapacity (I : Interpretation σ F) (c : Circuit σ N m) : Prop :=
  ∀ (T : Type) [Finite T] (w : T → Wire N c.size),
    Function.Injective (fun x : Fin N → F => fun t => c.program.trace I x (w t)) →
      N ≤ Nat.card T

/-- Over a finite field every circuit has linear capacity: `k` wires take at most `|F| ^ k`
values. -/
theorem linearCapacity_of_finite [Finite F] (I : Interpretation σ F) (c : Circuit σ N m) :
    LinearCapacity I c := by
  intro T _ w hw
  have h := Nat.card_le_card_of_injective _ hw
  rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin N), Fintype.card_fin] at h
  exact (Nat.pow_le_pow_iff_right Finite.one_lt_card).mp h

/-- Circuits over the affine basis have linear capacity: the values of `k` wires are an affine
function of the input, which is injective only if `N ≤ k`. -/
theorem linearCapacity_affine (c : Circuit (affineSignature F) N m) :
    LinearCapacity (affineInterpretation F) c := by
  intro T _ w hw
  have := Fintype.ofFinite T
  choose L b hL using fun t => exists_affine_trace c.program (w t)
  let Φ : (Fin N → F) →ₗ[F] (T → F) := LinearMap.pi L
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    refine hw (funext fun t => ?_)
    have := congrFun hxy t
    simp only [LinearMap.pi_apply, Φ] at this
    simp only [hL, this]
  have := LinearMap.finrank_le_finrank_of_injective hΦ
  simpa [Nat.card_eq_fintype_card] using this

end Capacity

/-! ### Every layout has a frontier that determines the input -/

/-- **A discrete intermediate value theorem.** A sequence of naturals that starts at `0` and
grows by at most one per step takes every value up to its final one. -/
theorem exists_eq_of_le_succ {a : ℕ → ℕ} (h0 : a 0 = 0) {m : ℕ} :
    ∀ {T : ℕ}, m ≤ a T → (∀ t < T, a (t + 1) ≤ a t + 1) → ∃ t ≤ T, a t = m
  | 0, hT, _ => ⟨0, le_rfl, by omega⟩
  | T + 1, hT, hstep => by
    by_cases h : m ≤ a T
    · obtain ⟨t, ht, hat⟩ := exists_eq_of_le_succ h0 h fun t ht => hstep t (by omega)
      exact ⟨t, by omega, hat⟩
    · exact ⟨T + 1, le_rfl, by have := hstep T (by omega); omega⟩

section Graph

variable {F : Type u} [Field F] {σ : Signature.{v}} {I : Interpretation σ F} {N : ℕ}
  {M : Matrix (Fin N) (Fin N) F} {c : Circuit σ N N}

/-- The network of a circuit computing a function: every value is accepted at every output. -/
noncomputable abbrev functionNetwork (I : Interpretation σ F) (c : Circuit σ N N) :=
  Compiler.network c.program c.outputs I fun _ => univ

theorem trace_outputs (hc : c.Computes I fun x => M *ᵥ x) (x : Fin N → F)
    (o : Fin N) : c.program.trace I x (c.outputs o) = (M *ᵥ x) o :=
  congrFun (hc x) o

/-- **Every output of a totally regular map depends on every input**, so every input is
upstream of every output. -/
theorem upstream_of_totallyRegular (hM : TotallyRegular M) (hc : c.Computes I fun x => M *ᵥ x)
    (o i : Fin N) : c.program.Upstream (c.outputs o) (.input i) := by
  classical
  by_contra h
  have hagree : ∀ j, c.program.Upstream (c.outputs o) (.input j) →
      (0 : Fin N → F) j = (Pi.single i (1 : F) : Fin N → F) j := fun j hj => by
    have : j ≠ i := fun hji => h (hji ▸ hj)
    simp [this]
  have heq : c.program.trace I 0 (c.outputs o) = c.program.trace I (Pi.single i 1) (c.outputs o) :=
    c.program.trace_congr_of_upstream I hagree _ .refl
  rw [trace_outputs hc, trace_outputs hc, mulVec_zero, mulVec_single_one] at heq
  have hMoi : M o i ≠ 0 := by
    have := hM 1 (fun _ => o) (fun _ => i) (Function.injective_of_subsingleton _)
      (Function.injective_of_subsingleton _)
    simpa [det_unique] using this
  exact hMoi (by simpa using heq.symm)

/-- In the network of a circuit for a totally regular map, an input is read in `P` exactly when
its vertex lies in `P`. -/
theorem mem_readIn_functionNetwork (hM : TotallyRegular M) (hc : c.Computes I fun x => M *ᵥ x)
    (P : Set (Compiler.Vertex c.program c.outputs)) (i : Fin N) :
    i ∈ (functionNetwork I c).readIn P ↔
      Compiler.Vertex.signal ⟨.input i, Compiler.reach_of_upstream
        (upstream_of_totallyRegular hM hc i i)⟩ ∈ P := by
  constructor
  · rintro ⟨v, hv, hiv⟩
    obtain ⟨_, rfl⟩ := Compiler.site_eq_some hiv
    exact hv
  · exact fun h => ⟨_, h, Compiler.site_of_reach _⟩

/-- **Some frontier of every layout determines the input.** For a circuit computing a totally
regular map, every layout of its network has a time at which the values on the frontier
determine the input. -/
theorem exists_injective_cut (hM : TotallyRegular M) (hc : c.Computes I fun x => M *ᵥ x)
    (π : Layout (Compiler.Vertex c.program c.outputs)) :
    ∃ t, Function.Injective fun (x : Fin N → F)
      (e : ↥((functionNetwork I c).cut (π.initial t))) => c.program.trace I x e.1.signal.1 := by
  classical
  set G := functionNetwork I c
  -- `a t` counts the inputs read and the outputs held by the first `t` vertices.
  let outs : Set (Compiler.Vertex c.program c.outputs) → Set (Fin N) :=
    fun P => {o | Compiler.Vertex.output o ∈ P}
  let a : ℕ → ℕ := fun t => (G.readIn (π.initial t)).ncard + (outs (π.initial t)).ncard
  have h0 : a 0 = 0 := by simp [a, outs, Network.readIn]
  have hT : N ≤ a (Nat.card (Compiler.Vertex c.program c.outputs)) := by
    have hread : G.readIn (π.initial (Nat.card (Compiler.Vertex c.program c.outputs))) = univ := by
      rw [π.initial_of_card_le le_rfl]
      exact eq_univ_of_forall fun i => (mem_readIn_functionNetwork hM hc univ i).mpr trivial
    simp only [a, hread, ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hstep : ∀ t < Nat.card (Compiler.Vertex c.program c.outputs), a (t + 1) ≤ a t + 1 := by
    intro t ht
    set v := π.symm ⟨t, ht⟩
    have hsucc := π.initial_succ ht
    have hread : G.readIn (π.initial (t + 1)) ⊆ G.readIn (π.initial t) ∪ G.readAt v := by
      rintro i ⟨u, hu, hiu⟩
      rw [hsucc] at hu
      rcases hu with rfl | hu
      · exact Or.inr hiu
      · exact Or.inl ⟨u, hu, hiu⟩
    have houts : outs (π.initial (t + 1)) ⊆ outs (π.initial t) ∪ {o | .output o = v} := by
      intro o ho
      simp only [outs, mem_ofPred_eq, hsucc, mem_insert_iff] at ho
      rcases ho with ho | ho
      · exact Or.inr ho
      · exact Or.inl ho
    -- The vertex processed reads one input, or holds one output, or neither.
    have hv : (G.readAt v).ncard + {o | Compiler.Vertex.output o = v}.ncard ≤ 1 := by
      rcases hvv : v with w | j | o
      · have h1 := Compiler.ncard_readAt_le I (fun _ => univ) (Compiler.Vertex.signal w)
        have h2 : {o | (Compiler.Vertex.output o : Compiler.Vertex c.program c.outputs) =
            Compiler.Vertex.signal w}.ncard = 0 := by
          simp
        unfold G functionNetwork at *
        omega
      · have h1 : G.readAt (.junction j) = ∅ := by
          ext i
          simp only [Network.readAt, mem_ofPred_eq, mem_empty_iff_false, iff_false]
          intro hi
          obtain ⟨_, h⟩ := Compiler.site_eq_some hi
          cases h
        simp [h1]
      · have h1 : G.readAt (.output o) = ∅ := by
          ext i
          simp only [Network.readAt, mem_ofPred_eq, mem_empty_iff_false, iff_false]
          intro hi
          obtain ⟨_, h⟩ := Compiler.site_eq_some hi
          cases h
        have h2 : {o' | (Compiler.Vertex.output o' : Compiler.Vertex c.program c.outputs) =
            Compiler.Vertex.output o}.ncard ≤ 1 :=
          (ncard_le_one (toFinite _)).mpr fun o₁ h₁ o₂ h₂ => by
            simp only [mem_ofPred_eq, Compiler.Vertex.output.injEq] at h₁ h₂
            rw [h₁, h₂]
        simp only [h1, ncard_empty, zero_add]
        exact h2
    have := ncard_le_ncard hread (toFinite _)
    have := ncard_le_ncard houts (toFinite _)
    have := ncard_union_le (G.readIn (π.initial t)) (G.readAt v)
    have := ncard_union_le (outs (π.initial t)) {o | Compiler.Vertex.output o = v}
    simp only [a]
    omega
  obtain ⟨t, -, hat⟩ := exists_eq_of_le_succ h0 hT hstep
  refine ⟨t, fun x x' hxx' => ?_⟩
  set P := π.initial t
  set X := G.readIn P
  set Y := outs P
  have hXY : X.ncard + Y.ncard = N := hat
  have hcut : ∀ e ∈ G.cut P, c.program.trace I x e.signal.1 = c.program.trace I x' e.signal.1 :=
    fun e he => congrFun hxx' ⟨e, he⟩
  have hcard : ∀ S : Set (Fin N), S.toFinset.card + Sᶜ.toFinset.card = N ∧
      S.toFinset.card = S.ncard := fun S => by
    rw [← ncard_eq_toFinset_card', ← ncard_eq_toFinset_card', ncard_add_ncard_compl,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    exact ⟨rfl, rfl⟩
  have hX := hcard X
  have hY := hcard Y
  -- Off `X`: splice `x` at `P` with `x'` elsewhere.
  have hoff : ∀ j ∉ X, x' j = x j := by
    set z := X.piecewise x x'
    have hzx : EqOn z x X := X.piecewise_eqOn x x'
    have hzy : EqOn z x' Xᶜ := X.piecewise_eqOn_compl x x'
    have hv := hM.eq_zero (R := Y.toFinset) (C := Xᶜ.toFinset) (v := z - x) (by omega)
      (fun j hj => by
        have : j ∈ X := by simpa using hj
        simp [hzx this])
      (fun o ho => by
        have ho : Compiler.Vertex.output o ∈ P := by simpa [Y, outs] using ho
        have := (Compiler.trace_out_of_cut I (P := P) hcut hzx hzy o).1 ho
        rw [trace_outputs hc, trace_outputs hc] at this
        rw [mulVec_sub, Pi.sub_apply, this, sub_self])
    intro j hj
    have := congrFun hv j
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
    rw [← this, hzy hj]
  -- On `X`: splice `x'` at `P` with `x` elsewhere.
  have hon : ∀ j ∈ X, x' j = x j := by
    set z := X.piecewise x' x
    have hzx : EqOn z x' X := X.piecewise_eqOn x' x
    have hzy : EqOn z x Xᶜ := X.piecewise_eqOn_compl x' x
    have hv := hM.eq_zero (R := Yᶜ.toFinset) (C := X.toFinset) (v := z - x) (by omega)
      (fun j hj => by
        have : j ∉ X := by simpa using hj
        simp [hzy this])
      (fun o ho => by
        have ho : Compiler.Vertex.output o ∉ P := by simpa [Y, outs] using ho
        have := (Compiler.trace_out_of_cut I (P := P) (fun e he => (hcut e he).symm) hzx hzy
          o).2 ho
        rw [trace_outputs hc, trace_outputs hc] at this
        rw [mulVec_sub, Pi.sub_apply, this, sub_self])
    intro j hj
    have := congrFun hv j
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
    rw [← this, hzx hj]
  funext j
  by_cases hj : j ∈ X
  · exact (hon j hj).symm
  · exact (hoff j hj).symm

/-- **The graph of a circuit for a totally regular map.** A circuit with `s` inner gates of
fan-in at most `r ≥ 2` and linear capacity, computing a totally regular map `F^N → F^N` with
`N ≥ 1`, yields a connected, loopless multigraph of maximum degree `r + 1` with at most
`2 r s + 3 N` vertices and cycle rank at most `(r - 1) s + 1 - N`, every layout of which has a
frontier of at least `N` edges. -/
theorem exists_graph_of_totallyRegular (hN : 1 ≤ N) {r : ℕ} (hr : 2 ≤ r)
    (hfan : c.FanInAtMost r) (hM : TotallyRegular M) (hc : c.Computes I fun x => M *ᵥ x)
    (hcap : LinearCapacity I c) :
    ∃ (V E : Type) (_ : Finite V) (_ : Finite E) (G : Multigraph V E),
      G.Connected ∧ G.Loopless ∧ G.MaxDegreeLE (r + 1) ∧
      Nat.card V ≤ 2 * r * c.innerSize + 3 * N ∧
      G.cycleRank + N ≤ (r - 1) * c.innerSize + 1 ∧
      ∀ π : Layout V, ∃ t, N ≤ (G.cut (π.initial t)).ncard := by
  have hconn : (functionNetwork I c).Connected :=
    Compiler.connected_of_upstream I _ (w₀ := .input ⟨0, hN⟩) fun o =>
      upstream_of_totallyRegular hM hc o _
  have hread : (functionNetwork I c).read.ncard = N := by
    have : (functionNetwork I c).read = univ := by
      rw [Compiler.read_network]
      exact eq_univ_of_forall fun i =>
        Compiler.reach_of_upstream (upstream_of_totallyRegular hM hc i i)
    rw [this, ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨_, _, inferInstance, inferInstance, (functionNetwork I c).toMultigraph, hconn,
    Compiler.loopless I _, Compiler.maxDegreeLE I _ hr hfan, ?_, ?_, fun π => ?_⟩
  · simpa [Circuit.innerSize] using Compiler.card_vertex_le (out := c.outputs) hfan
  · have := Compiler.cycleRank_add_ncard_read_le I _ hfan hconn
    rw [hread] at this
    exact this
  · obtain ⟨t, ht⟩ := exists_injective_cut hM hc π
    exact ⟨t, (hcap _ (fun e => e.1.signal.1) ht).trans_eq (Nat.card_coe_set_eq _)⟩

end Graph

/-! ### The lower bound -/

/-- **The frontier lower bound for linear maps.** Let `r ≥ 2` and assume the layout hypothesis
for maximum degree `r + 1` with coefficient `A > 0`. For every `ε > 0` and all large `N`, every
circuit of fan-in at most `r` with linear capacity, over any field and any basis, that computes
`x ↦ M x` for a totally regular `N × N` matrix `M`, has `s` inner gates with
`(r - 1) s > (1 + 1/A - ε) N`. -/
theorem lowerBound_linear {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] (σ : Signature.{v}) (I : Interpretation σ F)
      (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N), TotallyRegular M →
        c.FanInAtMost r → c.Computes I (fun x => M *ᵥ x) → LinearCapacity I c →
          (1 + 1 / A - ε) * N < (r - 1) * c.innerSize := by
  obtain ⟨η, hη, H⟩ := eventually_lt_of_demand hA (κ := 4) (by norm_num) hε
  obtain ⟨C, hC⟩ := hlayout η hη
  replace H := H η hη le_rfl
  filter_upwards [H C (fun _ => 1) (isLittleO_const_left.mpr
      (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop))),
    eventually_ge_atTop 1] with N hN hN1
  intro F _ σ I M c hM hfan hc hcap
  obtain ⟨V, E, _, _, G, hconn, hloop, hdeg, hV, hrank, hwidth⟩ :=
    exists_graph_of_totallyRegular hN1 hr hfan hM hc hcap
  obtain ⟨π, hπ⟩ := hC V E G hconn hloop hdeg
  set B := (A + η) * G.cycleRank + η * Nat.card V + C
  obtain ⟨t, ht⟩ := hwidth π
  have hB : (N : ℝ) ≤ B := (by exact_mod_cast ht : (N : ℝ) ≤ _).trans (hπ t)
  set s : ℝ := (((r - 1) * c.innerSize : ℕ) : ℝ)
  have hs : s = (r - 1) * c.innerSize := by
    simp only [s]; rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
  have hVs : (Nat.card V : ℝ) ≤ 4 * (N + s + 1) := by
    have : 2 * r * c.innerSize + 3 * N ≤ 4 * ((r - 1) * c.innerSize) + 4 * N := by
      have : 2 * r ≤ 4 * (r - 1) := by omega
      nlinarith
    have h4 : (Nat.card V : ℝ) ≤ 4 * ((r - 1) * c.innerSize : ℕ) + 4 * N := by
      exact_mod_cast hV.trans this
    simp only [s]
    linarith
  rw [← hs]
  refine hN s (Nat.card V) B (Nat.cast_nonneg _) (Nat.cast_nonneg _) hVs ?_ ?_
  · have : 0 ≤ Real.log (Nat.card V + 1) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (Nat.card V)])
    linarith
  · have hrank' : (G.cycleRank : ℝ) ≤ s - N + 1 := by
      have : (G.cycleRank : ℝ) + N ≤ ((r - 1) * c.innerSize : ℕ) + 1 := by exact_mod_cast hrank
      simp only [s]; linarith
    have := mul_le_mul_of_nonneg_left hrank' (by linarith : 0 ≤ A + η)
    linarith

/-- **Linear maps over finite fields**, over any basis. -/
theorem lowerBound_linear_finite {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Finite F] (σ : Signature.{v})
      (I : Interpretation σ F) (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N),
        TotallyRegular M → c.FanInAtMost r → c.Computes I (fun x => M *ᵥ x) →
          (1 + 1 / A - ε) * N < (r - 1) * c.innerSize := by
  filter_upwards [lowerBound_linear.{u, v} hr hA hlayout hε] with N hN
  intro F _ _ σ I M c hM hfan hc
  exact hN F σ I M c hM hfan hc (linearCapacity_of_finite I c)

/-- **Linear maps over any field**, over the affine basis. -/
theorem lowerBound_linear_affine {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] (M : Matrix (Fin N) (Fin N) F)
      (c : Circuit (affineSignature F) N N), TotallyRegular M → c.FanInAtMost r →
        c.Computes (affineInterpretation F) (fun x => M *ᵥ x) →
          (1 + 1 / A - ε) * N < (r - 1) * c.innerSize := by
  filter_upwards [lowerBound_linear.{u, u} hr hA hlayout hε] with N hN
  intro F _ M c hM hfan hc
  exact hN F _ _ M c hM hfan hc (linearCapacity_affine c)

/-- **Linear maps over infinite fields**, over any basis of polynomial operations: the
coefficients and degrees of the operations are arbitrary. -/
theorem lowerBound_linear_polynomial {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Infinite F] (σ : Signature.{v})
      (I : Interpretation σ F), IsPolynomial I → ∀ (M : Matrix (Fin N) (Fin N) F)
        (c : Circuit σ N N), TotallyRegular M → c.FanInAtMost r →
          c.Computes I (fun x => M *ᵥ x) → (1 + 1 / A - ε) * N < (r - 1) * c.innerSize := by
  filter_upwards [lowerBound_linear_affine.{u} hr hA hlayout hε] with N hN
  intro F _ _ σ I hI M c hM hfan hc
  obtain ⟨c', -, hinner, hfan', hc'⟩ := exists_affine_circuit hI c M hc
  rw [← hinner]
  exact hN F M c' hM (hfan' r hfan) hc'

end Complexity.Frontier
