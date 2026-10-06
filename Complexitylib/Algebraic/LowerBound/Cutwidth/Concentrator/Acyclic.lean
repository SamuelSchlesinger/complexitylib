/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Concentrator.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian
public import Complexitylib.Algebraic.LowerBound.Cutwidth.FourN
import Complexitylib.Algebraic.LowerBound.Cutwidth.Concentrator.Acyclic.Internal

/-!
# Acyclic concentrators need `2 n + (2.5625 - o(1)) min(m, n - m)` edges

Let `G` be an acyclic (`Multigraph.Acyclic`) `(n, m)`-concentrator whose inputs are sources (of
in-degree zero), as in Pinsker's model, with `2 ≤ m < n`. For every `ε > 0` and all large `n`,
uniformly in `m`, it has at least `2 n + (κ - 1) min(m, n - m) - ε n` edges, where
`κ = π/(3 arccos((1 + 2√2)/4)) ≈ 3.5625` (`eventually_le_card_edges_of_acyclic`). For
`m ≥ n/2` this is the general concentrator bound `n + m + κ (n - m) - ε n`
(`Concentrator.eventually_le_card_edges`); for `m < n/2` it is larger, for instance about
`2.64 n` rather than `2.14 n` at `m = n/4`, and it exceeds Pinsker's `2 n - 2` whenever
`min(m, n - m)` grows linearly. Acyclicity is the absence of directed cycles
(`acyclic_iff_forall_not_transGen`).

* **Elimination** (`Concentrator.exists_eliminate`). Removing at least two edges, an acyclic
  `(n + 1, m)`-concentrator with source inputs and `2 ≤ m ≤ n` turns into an acyclic
  `(n, m)`-concentrator with source inputs on the same vertices and outputs. If an input has two
  edges, drop it. Otherwise every input has a single edge, to its head, and distinct inputs have
  distinct heads. A head entered only by the edge from its input replaces that input. Failing
  that, a first non-input vertex at an edge in the topological order is entered by no edge, and
  its edges are removed.
* **The bound** (`le_of_orderingBound_of_acyclic`). For `m < n/2`, eliminating `n - 2 m` inputs
  leaves a `(2 m, m)`-concentrator with at least `2 (n - 2 m)` fewer edges, to which the
  concentrator bound applies. With `h = min(m, n - m)` this gives
  `h ≤ (A + η) (M - (2 n - h))⁺ + 3 log₂ (2 M) + C` and `M ≥ 2 n - h - 1`, hence
  `M ≥ 2 n + (1/A - 1) h - ε n` for all large `n`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Multigraph

open Filter

variable {V E : Type} {G : Multigraph V E}

/-- **Acyclicity is the absence of directed cycles.** A finite multigraph has a vertex numbering
increasing along every edge exactly when no vertex reaches itself along a directed walk of
positive length. -/
theorem acyclic_iff_forall_not_transGen [Fintype V] :
    G.Acyclic ↔ ∀ v, ¬ Relation.TransGen G.DirAdj v v :=
  Cutwidth.Concentrator.Internal.acyclic_iff_forall_not_transGen

namespace Concentrator

variable {n m : ℕ} {input : Fin n → V} {output : Fin m → V}

/-- **Elimination.** An acyclic `(n + 1, m)`-concentrator whose inputs are sources, with
`2 ≤ m ≤ n`, can be turned, by removing at least two edges, into an acyclic `(n, m)`-concentrator
on the same vertices and outputs whose inputs are sources. -/
theorem exists_eliminate [Fintype E] {input : Fin (n + 1) → V}
    (h : G.Concentrator input output) (hacyc : G.Acyclic)
    (hsrc : ∀ i, G.inDegree (input i) = 0) (hm : 2 ≤ m) (hmn : m ≤ n) :
    ∃ (E' : Type) (_ : Fintype E') (G' : Multigraph V E') (input' : Fin n → V),
      G'.Concentrator input' output ∧ G'.Acyclic ∧ (∀ i, G'.inDegree (input' i) = 0) ∧
        Fintype.card E' + 2 ≤ Fintype.card E :=
  Cutwidth.Concentrator.Internal.exists_eliminate hm _ G input le_rfl h hacyc hsrc hmn

/-- **The finite bound for acyclic concentrators.** Under the graph-ordering hypothesis
`OrderingBound A η C` with `A + η ≥ 0`, an acyclic `(n, m)`-concentrator with `M` edges whose
inputs are sources, with `2 ≤ m < n`, satisfies
`min(m, n - m) ≤ (A + η) (M - (2 n - min(m, n - m)))⁺ + 3 log₂ (2 M) + C`. -/
theorem le_of_orderingBound_of_acyclic [Fintype V] [Fintype E] {A η C : ℝ}
    (hord : OrderingBound A η C) (hAη : 0 ≤ A + η) (h : G.Concentrator input output)
    (hacyc : G.Acyclic) (hsrc : ∀ i, G.inDegree (input i) = 0) (hm : 2 ≤ m) (hmn : m < n) :
    ((min m (n - m) : ℕ) : ℝ) ≤ (A + η) * max ((Fintype.card E : ℝ) -
        (2 * n - ((min m (n - m) : ℕ) : ℝ))) 0 + 3 * Real.logb 2 (2 * Fintype.card E) + C :=
  Cutwidth.Concentrator.Internal.le_of_orderingBound_of_acyclic hord hAη h hacyc hsrc hm hmn

/-- **The edge baseline for acyclic concentrators.** An acyclic `(n, m)`-concentrator whose
inputs are sources, with `2 ≤ m < n`, has at least `2 n - min(m, n - m) - 1` edges. -/
theorem two_mul_le_card_edges_add_min [Fintype V] [Fintype E] (h : G.Concentrator input output)
    (hacyc : G.Acyclic) (hsrc : ∀ i, G.inDegree (input i) = 0) (hm : 2 ≤ m) (hmn : m < n) :
    2 * n ≤ Fintype.card E + min m (n - m) + 1 :=
  Cutwidth.Concentrator.Internal.two_mul_le_card_add_min_of_acyclic h hacyc hsrc hm hmn

/-- **Edges of acyclic concentrators from a general ordering coefficient.** If `A > 0` and every
slack `η > 0` admits a constant `C` with `OrderingBound A η C`, then for every `ε > 0` and all
large `n`, every acyclic `(n, m)`-concentrator whose inputs are sources, with `2 ≤ m < n`, has at
least `2 n + (1/A - 1) min(m, n - m) - ε n` edges. -/
theorem eventually_le_card_edges_of_acyclic_of_orderingBound {A : ℝ} (hA : 0 < A)
    (hord : ∀ η : ℝ, 0 < η → ∃ C : ℝ, OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 2 ≤ m → m < n → ∀ (V E : Type) [Fintype V] [Fintype E]
      (G : Multigraph V E) (input : Fin n → V) (output : Fin m → V),
        G.Concentrator input output → G.Acyclic → (∀ i, G.inDegree (input i) = 0) →
          2 * (n : ℝ) + (1 / A - 1) * ((min m (n - m) : ℕ) : ℝ) - ε * n ≤ Fintype.card E :=
  Cutwidth.Concentrator.Internal.eventually_le_card_edges_of_acyclic_of_orderingBound hA hord hε

/-- **Acyclic concentrators need `2 n + (2.5625 - o(1)) min(m, n - m)` edges.** For every
`ε > 0` and all large `n`, every acyclic `(n, m)`-concentrator whose inputs are sources, with
`2 ≤ m < n`, has at least `2 n + (κ - 1) min(m, n - m) - ε n` edges, where
`κ = π/(3 arccos((1 + 2√2)/4)) ≈ 3.5625`. -/
theorem eventually_le_card_edges_of_acyclic {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 2 ≤ m → m < n → ∀ (V E : Type) [Fintype V] [Fintype E]
      (G : Multigraph V E) (input : Fin n → V) (output : Fin m → V),
        G.Concentrator input output → G.Acyclic → (∀ i, G.inDegree (input i) = 0) →
          2 * (n : ℝ) + (Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - 1) *
            ((min m (n - m) : ℕ) : ℝ) - ε * n ≤ Fintype.card E := by
  have hc : 1 / (2 * Gaussian.frontierCoefficient) =
      Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) := by
    linarith [Gaussian.one_add_inv_two_mul_frontierCoefficient]
  have key := eventually_le_card_edges_of_acyclic_of_orderingBound
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) exists_orderingBound_frontier hε
  rwa [hc] at key

/-- **The cubic pathwidth coefficient for acyclic concentrators.** For every `ε > 0` and all
large `n`, every acyclic `(n, m)`-concentrator whose inputs are sources, with `2 ≤ m < n`, has at
least `2 n + 2 min(m, n - m) - ε n` edges: the ordering coefficient `1/3`. -/
theorem eventually_two_mul_add_two_mul_le_card_edges_of_acyclic {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 2 ≤ m → m < n → ∀ (V E : Type) [Fintype V] [Fintype E]
      (G : Multigraph V E) (input : Fin n → V) (output : Fin m → V),
        G.Concentrator input output → G.Acyclic → (∀ i, G.inDegree (input i) = 0) →
          2 * (n : ℝ) + 2 * ((min m (n - m) : ℕ) : ℝ) - ε * n ≤ Fintype.card E := by
  have key := eventually_le_card_edges_of_acyclic_of_orderingBound (by norm_num)
    exists_orderingBound_one_third hε
  rwa [show (1 / (1 / 3) - 1 : ℝ) = 2 by norm_num] at key

end Concentrator

end Algebraic.Cutwidth.Multigraph
