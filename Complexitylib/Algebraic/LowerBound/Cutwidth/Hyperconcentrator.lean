/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Hyperconcentrator.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian
public import Complexitylib.Algebraic.LowerBound.Cutwidth.FourN
import Complexitylib.Algebraic.LowerBound.Cutwidth.Hyperconcentrator.Internal

/-!
# Hyperconcentrators need `(3.78 - o(1)) N` edges

Every `N`-hyperconcentrator (`Multigraph.Hyperconcentrator`) has at least
`(2 + κ/2 - ε) N ≈ (3.78 - ε) N` edges for all large `N`, where
`κ = π/(3 arccos((1 + 2√2)/4)) ≈ 3.5625` is `1/(2p)` for the Gaussian edge-score pathwidth
coefficient `p` (`eventually_le_card_edges`), and at least `(34/9 - ε) N`. When the inputs have
in-degree zero and every vertex has in-degree at most two, as in a network of fan-in-two nodes,
at least `(1 + κ/2 - ε) N ≈ (2.78 - ε) N` vertices are not inputs
(`eventually_le_card_vertices`). Every superconcentrator is a hyperconcentrator
(`Superconcentrator.hyperconcentrator`).

The argument follows the superconcentrator bound (`Multigraph.Superconcentrator`).

* **Cut lemma** (`exists_le_card_cut`). In any linear order of the vertices, take a lower set
  `L` with exactly `h = ⌊N/2⌋` inputs, and let `c` of the first `h` outputs lie in `L`. The `h`
  inputs in `L` are joined to the first `h` outputs, and at least `h - c` of these walks leave
  `L`, each along an edge of its own. The `N - h ≥ h` inputs outside `L` are joined to the first
  `N - h` outputs, among them the first `h`, and the `c` walks ending in `L` enter it along
  distinct edges. So the cut of `L` has at least `h` edges.
* **Degree reduction and ordering bound.** All terminals lie in one undirected component, which
  splits into a connected loopless hyperconcentrator of maximum degree three with the same
  edges minus vertices, and the graph-ordering hypothesis `OrderingBound A η C` gives
  `⌊N/2⌋ ≤ (A + η) (M - 2 N)⁺ + 3 log₂ (2 M) + C` (`le_of_orderingBound`), so
  `M ≥ (2 + 1/(2A) - ε) N` for large `N`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Multigraph

open Filter

variable {V E : Type} {G : Multigraph V E} {N : ℕ} {input output : Fin N → V}

/-- **Every superconcentrator is a hyperconcentrator.** -/
theorem Superconcentrator.hyperconcentrator (h : G.Superconcentrator input output) :
    G.Hyperconcentrator input output :=
  Cutwidth.Hyperconcentrator.Internal.hyperconcentrator_of_superconcentrator h

namespace Hyperconcentrator

/-- **The cut lemma.** Every linear order of the vertices of an `N`-hyperconcentrator has a
lower set whose cut has at least `⌊N/2⌋` edges. -/
theorem exists_le_card_cut [Fintype V] [Fintype E] [LinearOrder V]
    (h : G.Hyperconcentrator input output) :
    ∃ L : Finset V, IsLowerSet (L : Set V) ∧ N / 2 ≤ (G.cut L).card :=
  Cutwidth.Hyperconcentrator.Internal.exists_le_card_cut h

/-- **The finite edge bound.** Under the graph-ordering hypothesis `OrderingBound A η C` with
`A + η ≥ 0`, an `N`-hyperconcentrator with `N > 0` and `M` edges satisfies
`⌊N/2⌋ ≤ (A + η) (M - 2 N)⁺ + 3 log₂ (2 M) + C`. -/
theorem le_of_orderingBound [Fintype V] [Fintype E] {A η C : ℝ} (hord : OrderingBound A η C)
    (hAη : 0 ≤ A + η) (h : G.Hyperconcentrator input output) (hN : 0 < N) :
    ((N / 2 : ℕ) : ℝ) ≤ (A + η) * max ((Fintype.card E : ℝ) - 2 * N) 0 +
      3 * Real.logb 2 (2 * Fintype.card E) + C :=
  Cutwidth.Hyperconcentrator.Internal.le_of_orderingBound hord hAη h hN

/-- **The finite vertex bound under in-degree two.** Under `OrderingBound A η C` with
`A + η ≥ 0`, an `N`-hyperconcentrator with `N > 0` and `V` vertices, whose inputs have in-degree
zero and whose vertices have in-degree at most two, satisfies
`⌊N/2⌋ ≤ (A + η) ((V - N) - N)⁺ + 3 log₂ (4 (V - N)) + C`. -/
theorem le_of_orderingBound_of_inDegree [Fintype V] [Fintype E] {A η C : ℝ}
    (hord : OrderingBound A η C) (hAη : 0 ≤ A + η) (h : G.Hyperconcentrator input output)
    (hN : 0 < N) (hsrc : ∀ i, G.inDegree (input i) = 0) (hdeg : ∀ w, G.inDegree w ≤ 2) :
    ((N / 2 : ℕ) : ℝ) ≤ (A + η) * max (((Fintype.card V : ℝ) - N) - N) 0 +
      3 * Real.logb 2 (4 * ((Fintype.card V : ℝ) - N)) + C :=
  Cutwidth.Hyperconcentrator.Internal.le_of_orderingBound_of_inDegree hord hAη h hN hsrc hdeg

/-- **Edges from a general ordering coefficient.** If `A > 0` and every slack `η > 0` admits a
constant `C` with `OrderingBound A η C`, then for every `ε > 0` and all large `N`, every
`N`-hyperconcentrator has at least `(2 + 1/(2A) - ε) N` edges. -/
theorem eventually_le_card_edges_of_orderingBound {A : ℝ} (hA : 0 < A)
    (hord : ∀ η : ℝ, 0 < η → ∃ C : ℝ, OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input output : Fin N → V), G.Hyperconcentrator input output →
        (2 + 1 / (2 * A) - ε) * N ≤ Fintype.card E :=
  Cutwidth.Hyperconcentrator.Internal.eventually_le_card_edges_of_orderingBound hA hord hε

/-- **Vertices from a general ordering coefficient, under in-degree two.** If `A > 0` and every
slack `η > 0` admits a constant `C` with `OrderingBound A η C`, then for every `ε > 0` and all
large `N`, every `N`-hyperconcentrator whose inputs have in-degree zero and whose vertices have
in-degree at most two has at least `(1 + 1/(2A) - ε) N` vertices that are not inputs. -/
theorem eventually_le_card_vertices_of_orderingBound {A : ℝ} (hA : 0 < A)
    (hord : ∀ η : ℝ, 0 < η → ∃ C : ℝ, OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input output : Fin N → V), G.Hyperconcentrator input output →
        (∀ i, G.inDegree (input i) = 0) → (∀ w, G.inDegree w ≤ 2) →
          (1 + 1 / (2 * A) - ε) * N ≤ (Fintype.card V : ℝ) - N :=
  Cutwidth.Hyperconcentrator.Internal.eventually_le_card_vertices_of_orderingBound hA hord hε

/-- The edge-score coefficient: `1/(2 · 2p) = κ/2` for `κ = π/(3 arccos((1 + 2√2)/4))`. -/
private theorem one_div_two_mul_frontier :
    1 / (2 * (2 * Gaussian.frontierCoefficient)) =
      Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) / 2 := by
  have := Gaussian.one_add_inv_two_mul_frontierCoefficient
  have hp := Gaussian.frontierCoefficient_pos
  rw [show 1 / (2 * (2 * Gaussian.frontierCoefficient)) =
    1 / (2 * Gaussian.frontierCoefficient) / 2 by field_simp]
  linarith

/-- The edge-score coefficient is at least `16/9`. -/
private theorem sixteen_div_nine_le_frontier :
    16 / 9 ≤ 1 / (2 * (2 * Gaussian.frontierCoefficient)) := by
  have hp := mul_pos two_pos Gaussian.frontierCoefficient_pos
  have := one_div_le_one_div_of_le hp Gaussian.two_mul_frontierCoefficient_le
  rw [show 1 / (2 * (2 * Gaussian.frontierCoefficient)) =
    1 / (2 * Gaussian.frontierCoefficient) / 2 by field_simp]
  norm_num at this ⊢
  linarith

/-- **Hyperconcentrators need `(3.78 - ε) N` edges.** For every `ε > 0` and all large `N`,
every `N`-hyperconcentrator has at least `(2 + κ/2 - ε) N` edges, where
`κ = π/(3 arccos((1 + 2√2)/4)) ≈ 3.5625`. -/
theorem eventually_le_card_edges {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input output : Fin N → V), G.Hyperconcentrator input output →
        (2 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) / 2 - ε) * N ≤
          Fintype.card E := by
  have key := eventually_le_card_edges_of_orderingBound
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) exists_orderingBound_frontier hε
  rwa [one_div_two_mul_frontier] at key

/-- **Hyperconcentrators need `(34/9 - ε) N` edges.** For every `ε > 0` and all large `N`,
every `N`-hyperconcentrator has at least `(34/9 - ε) N` edges; `34/9 ≈ 3.78`. -/
theorem eventually_thirtyFour_div_nine_sub_mul_le_card_edges {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input output : Fin N → V), G.Hyperconcentrator input output →
        (34 / 9 - ε) * N ≤ Fintype.card E := by
  filter_upwards [eventually_le_card_edges_of_orderingBound
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) exists_orderingBound_frontier hε]
    with N hN V E _ _ G input output h
  have := hN V E G input output h
  have : (34 / 9 - ε) * N ≤ (2 + 1 / (2 * (2 * Gaussian.frontierCoefficient)) - ε) * N :=
    mul_le_mul_of_nonneg_right (by linarith [sixteen_div_nine_le_frontier]) (Nat.cast_nonneg N)
  linarith

/-- **Hyperconcentrators of in-degree two need `(2.78 - ε) N` non-input vertices.** For every
`ε > 0` and all large `N`, every `N`-hyperconcentrator whose inputs have in-degree zero and whose
vertices have in-degree at most two has at least `(1 + κ/2 - ε) N` vertices that are not inputs,
where `κ = π/(3 arccos((1 + 2√2)/4)) ≈ 3.5625`. -/
theorem eventually_le_card_vertices {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input output : Fin N → V), G.Hyperconcentrator input output →
        (∀ i, G.inDegree (input i) = 0) → (∀ w, G.inDegree w ≤ 2) →
          (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) / 2 - ε) * N ≤
            (Fintype.card V : ℝ) - N := by
  have key := eventually_le_card_vertices_of_orderingBound
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) exists_orderingBound_frontier hε
  rwa [one_div_two_mul_frontier] at key

/-- **Hyperconcentrators of in-degree two need `(25/9 - ε) N` non-input vertices.** -/
theorem eventually_twentyFive_div_nine_sub_mul_le_card_vertices {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input output : Fin N → V), G.Hyperconcentrator input output →
        (∀ i, G.inDegree (input i) = 0) → (∀ w, G.inDegree w ≤ 2) →
          (25 / 9 - ε) * N ≤ (Fintype.card V : ℝ) - N := by
  filter_upwards [eventually_le_card_vertices_of_orderingBound
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) exists_orderingBound_frontier hε]
    with N hN V E _ _ G input output h hsrc hdeg
  have := hN V E G input output h hsrc hdeg
  have : (25 / 9 - ε) * N ≤ (1 + 1 / (2 * (2 * Gaussian.frontierCoefficient)) - ε) * N :=
    mul_le_mul_of_nonneg_right (by linarith [sixteen_div_nine_le_frontier]) (Nat.cast_nonneg N)
  linarith

/-- **The cubic pathwidth coefficient.** For every `ε > 0` and all large `N`, every
`N`-hyperconcentrator has at least `(7/2 - ε) N` edges: the ordering coefficient `1/3`. -/
theorem eventually_seven_div_two_sub_mul_le_card_edges {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input output : Fin N → V), G.Hyperconcentrator input output →
        (7 / 2 - ε) * N ≤ Fintype.card E := by
  have key := eventually_le_card_edges_of_orderingBound (by norm_num)
    exists_orderingBound_one_third hε
  rwa [show (2 + 1 / (2 * (1 / 3)) : ℝ) = 7 / 2 by norm_num] at key

end Hyperconcentrator

end Algebraic.Cutwidth.Multigraph
