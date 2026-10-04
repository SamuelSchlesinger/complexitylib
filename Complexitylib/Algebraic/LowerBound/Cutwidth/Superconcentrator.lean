/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Superconcentrator.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian
import Complexitylib.Algebraic.LowerBound.Cutwidth.Superconcentrator.Internal.Bound

/-!
# Superconcentrators need `(5.5625 - o(1)) N` edges

Every `N`-superconcentrator (`Multigraph.Superconcentrator`) has at least
`(2 + π/(3 arccos((1 + 2√2)/4)) - ε) N ≈ (5.5625 - ε) N` edges for all large `N`. The constant
is `2 + 1/(2p)` for the Gaussian edge-score pathwidth coefficient
`p = (3/(2π)) arccos((1 + 2√2)/4)`. Lev and Valiant (*Size bounds for superconcentrators*,
1983) proved `5 N` by the same argument with the cubic pathwidth coefficient `1/6`, which this
file recovers as `eventually_five_sub_mul_le_card_edges`.

The argument has three steps.

* **Cut lemma** (`exists_le_card_cut`). In any linear order of the vertices, take a prefix
  containing exactly `N` of the `2 N` terminals, say `a` inputs and `N - a` outputs. The
  superconcentrator joins those `a` inputs to the `a` outputs after the prefix, and the
  `N - a` inputs after the prefix to those `N - a` outputs, by vertex-disjoint directed walks.
  Each walk of the first family leaves the prefix along an edge directed out of it, each walk
  of the second enters it along an edge directed into it, and vertex-disjoint walks use
  distinct edges, so the prefix cut has at least `N` edges. No Menger theorem is needed.
* **Degree reduction.** Every vertex of the component of the terminals is replaced by a
  directed path with one vertex per edge end: the ends of entering edges first, then those of
  leaving edges. The result is a connected loopless superconcentrator of maximum degree
  three, and its edges minus vertices equal those of the component.
* **Ordering bound.** The graph-ordering hypothesis `OrderingBound A η C` gives an ordering
  of the reduced graph whose prefix cuts have at most `(A + η) (M - V)⁺ + 3 log₂ V + C` edges.
  With the cut lemma, `N ≤ (A + η) (M - 2 N)⁺ + 3 log₂ (2 M) + C` for a superconcentrator with
  `M` edges (`le_of_orderingBound`), since the component has at least the `2 N` terminals as
  vertices. For a connected superconcentrator with `V` vertices the bound holds with
  `(M - V)⁺` (`le_of_orderingBound_of_connected`).

The asymptotic bound `(2 + 1/A - ε) N` follows for every `A > 0` such that every slack admits
an ordering constant (`eventually_le_card_edges_of_orderingBound`). The edge-score
decomposition supplies `A = 2 p ≤ 9/32`, giving `eventually_le_card_edges` and the rational
form `(50/9 - ε) N` (`eventually_fifty_div_nine_sub_mul_le_card_edges`).

When the inputs have in-degree zero and every vertex has in-degree at most two, the same argument
bounds the vertices: at least `(1 + 1/A - ε) N` of them are not inputs
(`eventually_le_card_vertices_of_orderingBound`), which is `(4 - ε) N` for `A = 1/3`, the
corresponding bound of Lev and Valiant, and about `(4.5625 - ε) N` for the edge-score
coefficient (`eventually_le_card_vertices`).
-/

@[expose] public section

namespace Algebraic.Cutwidth.Multigraph.Superconcentrator

open Filter

variable {V E : Type} {G : Multigraph V E} {N : ℕ} {input output : Fin N → V}

/-- **The cut lemma.** Every linear order of the vertices of an `N`-superconcentrator has a
lower set whose cut has at least `N` edges. -/
theorem exists_le_card_cut [Fintype V] [Fintype E] [LinearOrder V]
    (h : G.Superconcentrator input output) :
    ∃ L : Finset V, IsLowerSet (L : Set V) ∧ N ≤ (G.cut L).card :=
  Cutwidth.Superconcentrator.Internal.exists_le_card_cut h

/-- **The finite bound.** Under the graph-ordering hypothesis `OrderingBound A η C` with
`A + η ≥ 0`, an `N`-superconcentrator with `N > 0` and `M` edges satisfies
`N ≤ (A + η) (M - 2 N)⁺ + 3 log₂ (2 M) + C`. -/
theorem le_of_orderingBound [Fintype V] [Fintype E] {A η C : ℝ} (hord : OrderingBound A η C)
    (hAη : 0 ≤ A + η) (h : G.Superconcentrator input output) (hN : 0 < N) :
    (N : ℝ) ≤ (A + η) * max ((Fintype.card E : ℝ) - 2 * N) 0 +
      3 * Real.logb 2 (2 * Fintype.card E) + C :=
  Cutwidth.Superconcentrator.Internal.le_of_orderingBound hord hAη h hN

/-- **The finite bound for connected superconcentrators.** Under `OrderingBound A η C`, a
connected `N`-superconcentrator with `N > 0`, `V` vertices, and `M` edges satisfies
`N ≤ (A + η) (M - V)⁺ + 3 log₂ (2 M) + C`. -/
theorem le_of_orderingBound_of_connected [Fintype V] [Fintype E] {A η C : ℝ}
    (hord : OrderingBound A η C) (h : G.Superconcentrator input output) (hN : 0 < N)
    (hconn : G.Connected) :
    (N : ℝ) ≤ (A + η) * max ((Fintype.card E : ℝ) - Fintype.card V) 0 +
      3 * Real.logb 2 (2 * Fintype.card E) + C :=
  Cutwidth.Superconcentrator.Internal.le_of_orderingBound_of_connected hord h hN hconn

/-- **The finite bound under in-degree two.** Under `OrderingBound A η C` with `A + η ≥ 0`, an
`N`-superconcentrator with `N > 0` and `V` vertices, whose inputs have in-degree zero and
whose vertices have in-degree at most two, satisfies
`N ≤ (A + η) ((V - N) - N)⁺ + 3 log₂ (4 (V - N)) + C`. -/
theorem le_of_orderingBound_of_inDegree [Fintype V] [Fintype E] {A η C : ℝ}
    (hord : OrderingBound A η C) (hAη : 0 ≤ A + η) (h : G.Superconcentrator input output)
    (hN : 0 < N) (hsrc : ∀ i, G.inDegree (input i) = 0) (hdeg : ∀ w, G.inDegree w ≤ 2) :
    (N : ℝ) ≤ (A + η) * max (((Fintype.card V : ℝ) - N) - N) 0 +
      3 * Real.logb 2 (4 * ((Fintype.card V : ℝ) - N)) + C :=
  Cutwidth.Superconcentrator.Internal.le_of_orderingBound_of_inDegree hord hAη h hN hsrc hdeg

/-- **Edges from a general ordering coefficient.** If `A > 0` and every slack `η > 0` admits
a constant `C` with `OrderingBound A η C`, then for every `ε > 0` and all large `N`, every
`N`-superconcentrator has at least `(2 + 1/A - ε) N` edges. -/
theorem eventually_le_card_edges_of_orderingBound {A : ℝ} (hA : 0 < A)
    (hord : ∀ η : ℝ, 0 < η → ∃ C : ℝ, OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input output : Fin N → V), G.Superconcentrator input output →
        (2 + 1 / A - ε) * N ≤ Fintype.card E :=
  Cutwidth.Superconcentrator.Internal.eventually_le_card_edges_of_orderingBound hA hord hε

/-- **Superconcentrators need `(5.5625 - ε) N` edges.** For every `ε > 0` and all large `N`,
every `N`-superconcentrator has at least `(2 + π/(3 arccos((1 + 2√2)/4)) - ε) N` edges. The
constant `2 + π/(3 arccos((1 + 2√2)/4)) ≈ 5.5625` is `2 + 1/(2p)` for the edge-score
pathwidth coefficient `p`. -/
theorem eventually_le_card_edges {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input output : Fin N → V), G.Superconcentrator input output →
        (2 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * N ≤
          Fintype.card E := by
  have key := eventually_le_card_edges_of_orderingBound
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) exists_orderingBound_frontier hε
  have hc : 1 / (2 * Gaussian.frontierCoefficient) =
      Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) := by
    linarith [Gaussian.one_add_inv_two_mul_frontierCoefficient]
  rwa [hc] at key

/-- **Superconcentrators need `(50/9 - ε) N` edges.** For every `ε > 0` and all large `N`,
every `N`-superconcentrator has at least `(50/9 - ε) N` edges; `50/9 ≈ 5.556`. -/
theorem eventually_fifty_div_nine_sub_mul_le_card_edges {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input output : Fin N → V), G.Superconcentrator input output →
        (50 / 9 - ε) * N ≤ Fintype.card E := by
  have hp := mul_pos two_pos Gaussian.frontierCoefficient_pos
  have hc : 32 / 9 ≤ 1 / (2 * Gaussian.frontierCoefficient) := by
    have := one_div_le_one_div_of_le hp Gaussian.two_mul_frontierCoefficient_le
    norm_num at this ⊢
    linarith
  filter_upwards [eventually_le_card_edges_of_orderingBound hp exists_orderingBound_frontier hε]
    with N hN V E _ _ G input output h
  have := hN V E G input output h
  have : (50 / 9 - ε) * N ≤ (2 + 1 / (2 * Gaussian.frontierCoefficient) - ε) * N :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg N)
  linarith

/-- **The Lev–Valiant bound.** For every `ε > 0` and all large `N`, every
`N`-superconcentrator has at least `(5 - ε) N` edges. This is the ordering coefficient `1/3`
of the Fomin–Høie cubic pathwidth bound. -/
theorem eventually_five_sub_mul_le_card_edges {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input output : Fin N → V), G.Superconcentrator input output →
        (5 - ε) * N ≤ Fintype.card E := by
  have key := eventually_le_card_edges_of_orderingBound (by norm_num)
    exists_orderingBound_one_third hε
  norm_num at key
  convert key using 4
  norm_num

/-- **Vertices from a general ordering coefficient, under in-degree two.** If `A > 0` and
every slack `η > 0` admits a constant `C` with `OrderingBound A η C`, then for every `ε > 0`
and all large `N`, every `N`-superconcentrator whose inputs have in-degree zero and whose
vertices have in-degree at most two has at least `(1 + 1/A - ε) N` vertices that are not
inputs. -/
theorem eventually_le_card_vertices_of_orderingBound {A : ℝ} (hA : 0 < A)
    (hord : ∀ η : ℝ, 0 < η → ∃ C : ℝ, OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input output : Fin N → V), G.Superconcentrator input output →
        (∀ i, G.inDegree (input i) = 0) → (∀ w, G.inDegree w ≤ 2) →
          (1 + 1 / A - ε) * N ≤ (Fintype.card V : ℝ) - N :=
  Cutwidth.Superconcentrator.Internal.eventually_le_card_vertices_of_orderingBound hA hord hε

/-- **Superconcentrators of in-degree two need `(4.5625 - ε) N` non-input vertices.** For every
`ε > 0` and all large `N`, every `N`-superconcentrator whose inputs have in-degree zero and
whose vertices have in-degree at most two has at least
`(1 + π/(3 arccos((1 + 2√2)/4)) - ε) N` vertices that are not inputs. -/
theorem eventually_le_card_vertices {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input output : Fin N → V), G.Superconcentrator input output →
        (∀ i, G.inDegree (input i) = 0) → (∀ w, G.inDegree w ≤ 2) →
          (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * N ≤
            (Fintype.card V : ℝ) - N := by
  have key := eventually_le_card_vertices_of_orderingBound
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) exists_orderingBound_frontier hε
  rwa [Gaussian.one_add_inv_two_mul_frontierCoefficient] at key

end Algebraic.Cutwidth.Multigraph.Superconcentrator
