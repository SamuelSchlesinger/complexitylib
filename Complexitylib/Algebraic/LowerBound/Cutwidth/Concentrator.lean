/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Concentrator.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian
public import Complexitylib.Algebraic.LowerBound.Cutwidth.FourN
import Complexitylib.Algebraic.LowerBound.Cutwidth.Concentrator.Internal

/-!
# Concentrators need `n + m + (3.5625 - o(1)) min(m, n - m)` edges

Every `(n, m)`-concentrator (`Multigraph.Concentrator`) with `1 ≤ m < n` and `M` edges has
`M ≥ n + m + κ min(m, n - m) - ε n` for every `ε > 0` and all large `n`, uniformly in `m`, where
`κ = π/(3 arccos((1 + 2√2)/4)) ≈ 3.5625` is `1/(2p)` for the Gaussian edge-score pathwidth
coefficient `p = (3/(2π)) arccos((1 + 2√2)/4)` (`eventually_le_card_edges`). With `⌊n/2⌋` outputs
this is `(3/2 + κ/2 - ε) n ≈ (3.28 - ε) n` edges (`eventually_le_card_edges_half`), and at least
`(59/18 - ε) n`. Pinsker (*On the complexity of a concentrator*, 7th International Teletraffic
Congress, 1973) proved that every `(n, m)`-concentrator with `m ≥ 2` has at least `2 n - 2`
edges; the bound here is larger, up to `ε n`, whenever `m ≥ n/(1 + κ) ≈ 0.22 n`. The cubic pathwidth coefficient of Fomin and Høie, ordering
coefficient `1/3`, gives `n + m + 3 min(m, n - m) - ε n`, that is `(3 - ε) n` for `⌊n/2⌋`
outputs (`eventually_three_sub_mul_le_card_edges`).

The argument follows the superconcentrator bound (`Multigraph.Superconcentrator`).

* **Cut lemma** (`exists_le_card_cut`). In any linear order of the vertices, take a lower set
  `L` with exactly `h = min(m, n - m)` inputs, and let `b` outputs lie in `L`. The `h` inputs in
  `L` are joined to distinct outputs; at most `b` walks end in `L`, and each of the others
  leaves `L` along an edge of its own. Some `m` inputs outside `L` are joined to all `m`
  outputs, and each of the `b` walks ending in `L` enters it along an edge of its own. So the
  cut of `L` has at least `h` edges.
* **Connectivity.** All terminals lie in one undirected component: a component holding `a`
  inputs holds at least `min(a, m)` outputs, and if no component held all outputs, there would
  be no more inputs than outputs.
* **Degree reduction and ordering bound.** The component of the terminals splits into a
  connected loopless concentrator of maximum degree three with the same edges minus vertices,
  and the graph-ordering hypothesis `OrderingBound A η C` gives
  `h ≤ (A + η) (M - n - m)⁺ + 3 log₂ (2 M) + C` (`le_of_orderingBound`). A connected graph on the
  `n + m` terminals has at least `n + m - 1` edges (`add_le_card_edges_add_one`), which handles
  small `h`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Multigraph.Concentrator

open Filter

variable {V E : Type} {G : Multigraph V E} {n m : ℕ} {input : Fin n → V} {output : Fin m → V}

/-- **The cut lemma.** Every linear order of the vertices of an `(n, m)`-concentrator has a
lower set whose cut has at least `min(m, n - m)` edges. -/
theorem exists_le_card_cut [Fintype V] [Fintype E] [LinearOrder V]
    (h : G.Concentrator input output) :
    ∃ L : Finset V, IsLowerSet (L : Set V) ∧ min m (n - m) ≤ (G.cut L).card :=
  Cutwidth.Concentrator.Internal.exists_le_card_cut h

/-- **The edge baseline.** An `(n, m)`-concentrator with `1 ≤ m < n` has at least `n + m - 1`
edges: its terminals lie in one undirected component. -/
theorem add_le_card_edges_add_one [Fintype V] [Fintype E] (h : G.Concentrator input output)
    (hm : 1 ≤ m) (hmn : m < n) : n + m ≤ Fintype.card E + 1 :=
  Cutwidth.Concentrator.Internal.add_le_card_add_one h hm hmn

/-- **The finite bound.** Under the graph-ordering hypothesis `OrderingBound A η C` with
`A + η ≥ 0`, an `(n, m)`-concentrator with `1 ≤ m < n` and `M` edges satisfies
`min(m, n - m) ≤ (A + η) (M - n - m)⁺ + 3 log₂ (2 M) + C`. -/
theorem le_of_orderingBound [Fintype V] [Fintype E] {A η C : ℝ} (hord : OrderingBound A η C)
    (hAη : 0 ≤ A + η) (h : G.Concentrator input output) (hm : 1 ≤ m) (hmn : m < n) :
    ((min m (n - m) : ℕ) : ℝ) ≤ (A + η) * max ((Fintype.card E : ℝ) - (n + m)) 0 +
      3 * Real.logb 2 (2 * Fintype.card E) + C :=
  Cutwidth.Concentrator.Internal.le_of_orderingBound hord hAη h hm hmn

/-- **Edges from a general ordering coefficient.** If `A > 0` and every slack `η > 0` admits a
constant `C` with `OrderingBound A η C`, then for every `ε > 0` and all large `n`, every
`(n, m)`-concentrator with `1 ≤ m < n` has at least `n + m + min(m, n - m)/A - ε n` edges. -/
theorem eventually_le_card_edges_of_orderingBound {A : ℝ} (hA : 0 < A)
    (hord : ∀ η : ℝ, 0 < η → ∃ C : ℝ, OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 1 ≤ m → m < n → ∀ (V E : Type) [Fintype V] [Fintype E]
      (G : Multigraph V E) (input : Fin n → V) (output : Fin m → V),
        G.Concentrator input output →
          (n : ℝ) + m + ((min m (n - m) : ℕ) : ℝ) / A - ε * n ≤ Fintype.card E :=
  Cutwidth.Concentrator.Internal.eventually_le_card_edges_of_orderingBound hA hord hε

/-- **Balanced concentrators from a general ordering coefficient.** Under the hypotheses of
`eventually_le_card_edges_of_orderingBound`, every `(n, ⌊n/2⌋)`-concentrator has at least
`(3/2 + 1/(2A) - ε) n` edges for all large `n`. -/
theorem eventually_le_card_edges_half_of_orderingBound {A : ℝ} (hA : 0 < A)
    (hord : ∀ η : ℝ, 0 < η → ∃ C : ℝ, OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input : Fin n → V) (output : Fin (n / 2) → V), G.Concentrator input output →
        (3 / 2 + 1 / (2 * A) - ε) * n ≤ Fintype.card E :=
  Cutwidth.Concentrator.Internal.eventually_le_card_edges_half_of_orderingBound hA hord hε

/-- **Concentrators need `n + m + (3.5625 - o(1)) min(m, n - m)` edges.** For every `ε > 0`
and all large `n`, every `(n, m)`-concentrator with `1 ≤ m < n` has at least
`n + m + κ min(m, n - m) - ε n` edges, where `κ = π/(3 arccos((1 + 2√2)/4)) ≈ 3.5625`. -/
theorem eventually_le_card_edges {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 1 ≤ m → m < n → ∀ (V E : Type) [Fintype V] [Fintype E]
      (G : Multigraph V E) (input : Fin n → V) (output : Fin m → V),
        G.Concentrator input output →
          (n : ℝ) + m + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) *
            ((min m (n - m) : ℕ) : ℝ) - ε * n ≤ Fintype.card E := by
  have hc : 1 / (2 * Gaussian.frontierCoefficient) =
      Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) := by
    linarith [Gaussian.one_add_inv_two_mul_frontierCoefficient]
  filter_upwards [eventually_le_card_edges_of_orderingBound
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) exists_orderingBound_frontier hε]
    with n hn m hm hmn V E _ _ G input output h
  have := hn m hm hmn V E G input output h
  rwa [div_eq_mul_one_div, mul_comm, hc] at this

/-- **Balanced concentrators need `(3.28 - o(1)) n` edges.** For every `ε > 0` and all large
`n`, every `(n, ⌊n/2⌋)`-concentrator has at least `(3/2 + κ/2 - ε) n` edges, where
`κ = π/(3 arccos((1 + 2√2)/4)) ≈ 3.5625`. -/
theorem eventually_le_card_edges_half {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input : Fin n → V) (output : Fin (n / 2) → V), G.Concentrator input output →
        (3 / 2 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) / 2 - ε) * n ≤
          Fintype.card E := by
  have hc : 1 / (2 * (2 * Gaussian.frontierCoefficient)) =
      Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) / 2 := by
    have := Gaussian.one_add_inv_two_mul_frontierCoefficient
    have hp := Gaussian.frontierCoefficient_pos
    rw [show 1 / (2 * (2 * Gaussian.frontierCoefficient)) =
      1 / (2 * Gaussian.frontierCoefficient) / 2 by field_simp]
    linarith
  have key := eventually_le_card_edges_half_of_orderingBound
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) exists_orderingBound_frontier hε
  rwa [hc] at key

/-- **Balanced concentrators need `(59/18 - ε) n` edges.** For every `ε > 0` and all large `n`,
every `(n, ⌊n/2⌋)`-concentrator has at least `(59/18 - ε) n` edges; `59/18 ≈ 3.278`. -/
theorem eventually_fiftyNine_div_eighteen_sub_mul_le_card_edges {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input : Fin n → V) (output : Fin (n / 2) → V), G.Concentrator input output →
        (59 / 18 - ε) * n ≤ Fintype.card E := by
  have hp := mul_pos two_pos Gaussian.frontierCoefficient_pos
  have hc : 16 / 9 ≤ 1 / (2 * (2 * Gaussian.frontierCoefficient)) := by
    have := one_div_le_one_div_of_le hp Gaussian.two_mul_frontierCoefficient_le
    rw [show 1 / (2 * (2 * Gaussian.frontierCoefficient)) =
      1 / (2 * Gaussian.frontierCoefficient) / 2 by field_simp]
    norm_num at this ⊢
    linarith
  filter_upwards [eventually_le_card_edges_half_of_orderingBound hp
    exists_orderingBound_frontier hε] with n hn V E _ _ G input output h
  have := hn V E G input output h
  have : (59 / 18 - ε) * n ≤ (3 / 2 + 1 / (2 * (2 * Gaussian.frontierCoefficient)) - ε) * n :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
  linarith

/-- **The cubic pathwidth coefficient.** For every `ε > 0` and all large `n`, every
`(n, m)`-concentrator with `1 ≤ m < n` has at least `n + m + 3 min(m, n - m) - ε n` edges. This
is the ordering coefficient `1/3` of the Fomin–Høie cubic pathwidth bound. -/
theorem eventually_add_three_mul_le_card_edges {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 1 ≤ m → m < n → ∀ (V E : Type) [Fintype V] [Fintype E]
      (G : Multigraph V E) (input : Fin n → V) (output : Fin m → V),
        G.Concentrator input output →
          (n : ℝ) + m + 3 * ((min m (n - m) : ℕ) : ℝ) - ε * n ≤ Fintype.card E := by
  filter_upwards [eventually_le_card_edges_of_orderingBound (by norm_num)
    exists_orderingBound_one_third hε] with n hn m hm hmn V E _ _ G input output h
  have := hn m hm hmn V E G input output h
  rwa [div_eq_mul_one_div, one_div_one_div, mul_comm] at this

/-- **Balanced concentrators need `(3 - ε) n` edges by the cubic pathwidth coefficient.** -/
theorem eventually_three_sub_mul_le_card_edges {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E)
      (input : Fin n → V) (output : Fin (n / 2) → V), G.Concentrator input output →
        (3 - ε) * n ≤ Fintype.card E := by
  have key := eventually_le_card_edges_half_of_orderingBound (by norm_num)
    exists_orderingBound_one_third hε
  rwa [show (3 / 2 + 1 / (2 * (1 / 3)) : ℝ) = 3 by norm_num] at key

end Algebraic.Cutwidth.Multigraph.Concentrator
