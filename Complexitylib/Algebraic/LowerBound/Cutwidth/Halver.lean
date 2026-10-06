/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Halver.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian
public import Complexitylib.Algebraic.LowerBound.Cutwidth.FourN
import Complexitylib.Algebraic.LowerBound.Cutwidth.Halver.Internal

/-!
# ε-halvers need `(1 + κ (1 - 2ε)/2 - o(1)) n` comparators

A comparator network (`ComparatorNetwork n s`) on `n` wires applies `s` comparators in order;
comparator `c` puts the smaller of the values on its two distinct wires on `minWire c` and the
larger on `maxWire c`. It is an *`ε`-halver* (`ComparatorNetwork.IsHalver`) when on every input
in `{0, 1}ⁿ` with `k ≤ n/2` ones at most `ε k` ones end in the bottom half (the wires
`w < ⌊n/2⌋`), and on every input with `k ≤ n/2` zeros at most `ε k` zeros end in the top half.

For every `0 ≤ ε < 1/2` and `δ > 0`, and all large `n`, every `ε`-halver on `n` wires has at least
`(1 + κ (1 - 2ε)/2 - δ) n` comparators (`eventually_le_size_of_isHalver`), where
`κ = π/(3 arccos((1 + 2√2)/4)) ≈ 3.5625` is `1/(2p)` for the Gaussian edge-score pathwidth
coefficient `p`. As `ε → 0` this is about `2.78 n`; at `ε = 1/10` about `2.43 n`. With the rational
ordering coefficient `9/32 ≥ 2p` it is at least `(1 + 16 (1 - 2ε)/9 - δ) n`, and with the
Fomin–Høie coefficient `1/3` it is `(1 + 3 (1 - 2ε)/2 - δ) n`. Ajtai, Komlós and Szemerédi (1983)
build ε-halvers of linear size from expanders, and Seiferas (*Sorting networks of logarithmic
depth, further simplified*, Algorithmica 53, 2009) and Paterson (*Improved sorting networks with
O(log N) depth*, Algorithmica 5, 1990) study their depth and size from above; no size lower bound
for ε-halvers beyond the trivial `n - 1` of connectivity (`IsHalver.le_add_one`) was found in the
literature.

* **The wire graph** (`ComparatorNetwork.wireGraph`). Every wire runs from an input terminal
  through the ends of the comparators acting on it to an output terminal; each comparator adds a
  link between its two ends. The graph is loopless with maximum degree three
  (`wireGraph_loopless`, `wireGraph_maxDegreeLE`), with `2 n + 2 s` vertices and `n + 3 s` edges,
  so edges minus vertices is `s - n`.
* **Token conservation** (`sub_le_card_cut`). On a `0`-`1` input, a wire segment carries the
  value of its wire and a link carries the one that moves from `minWire c` to `maxWire c`. The
  flow is conserved at every comparator end, so for every vertex set `L` and inputs `x`, `x'`,
  the cut of `L` has at least `net x - net x'` edges, where `net y` counts the ones of `y` at
  input terminals in `L` minus the ones of the output at output terminals in `L`.
* **Connectivity** (`IsHalver.wireGraph_connected`). A set of `0 < k ≤ n/2` wires closed under
  the comparators would keep its indicator input, and that of its complement, fixed, so an
  `ε`-halver would put at most `ε k` of its wires in each half; for `ε < 1/2` the closed sets are
  trivial (`IsHalver.eq_empty_or_eq_univ_of_closed`) and the wire graph is connected.
* **The cut lemma** (`IsHalver.exists_le_card_cut`). In any linear order of the vertices, take
  the lower set `L` with exactly `h = ⌊n/2⌋` input terminals, and let `τ` top output terminals lie
  in `L`. Ones on the inputs in `L` leave at most `ε h` ones in the bottom half, so
  `net ≥ h - τ - ε h`; zeros on the inputs in `L` leave at most `ε h` zeros in the top half, so
  `net ≤ ε h - τ`. The cut of `L` has at least `(1 - 2 ε) h` edges.
* **Ordering bound.** The graph-ordering hypothesis `OrderingBound A η C` then gives
  `(1 - 2ε) ⌊n/2⌋ ≤ (A + η) (s - n)⁺ + 3 log₂ (2 n + 2 s) + C` (`IsHalver.le_of_orderingBound`),
  and so `s ≥ (1 + (1 - 2ε)/(2A) - δ) n` for large `n`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.ComparatorNetwork

open Filter Multigraph

variable {n s : ℕ}

/-- **The network commutes with monotone maps.** For a monotone `f`, evaluating on `f ∘ x` gives
`f` applied to the output on `x`. Taking `f` a threshold map to `Bool`, this is the `0`-`1`
principle behind the `0`-`1` form of the halver property. -/
theorem eval_comp (N : ComparatorNetwork n s) {α β : Type*} [LinearOrder α] [LinearOrder β]
    {f : α → β} (hf : Monotone f) (x : Fin n → α) : N.eval (f ∘ x) = f ∘ N.eval x :=
  Halver.Internal.eval_comp N hf x

/-- The wire graph has `2 n + 2 s` vertices: two terminals per wire and two ends per
comparator. -/
theorem card_wireVertex : Fintype.card (WireVertex n s) = 2 * n + 2 * s :=
  Halver.Internal.card_wireVertex

/-- The wire graph has `n + 3 s` edges: `n + 2 s` wire segments and `s` links. -/
theorem card_wireEdge : Fintype.card (WireEdge n s) = n + 3 * s :=
  Halver.Internal.card_wireEdge

/-- The wire graph has no loops. -/
theorem wireGraph_loopless (N : ComparatorNetwork n s) : N.wireGraph.Loopless :=
  Halver.Internal.wireGraph_loopless N

/-- The wire graph has maximum degree three. -/
theorem wireGraph_maxDegreeLE (N : ComparatorNetwork n s) : N.wireGraph.MaxDegreeLE 3 :=
  Halver.Internal.wireGraph_maxDegreeLE N

/-- **Token conservation.** For inputs `x` and `x'` in `{0, 1}ⁿ` and a vertex set `L`, the cut of
`L` in the wire graph has at least `net x - net x'` edges, where `net y` is the number of ones of
`y` at input terminals in `L` minus the number of ones of `N.eval y` at output terminals in
`L`. -/
theorem sub_le_card_cut (N : ComparatorNetwork n s) (x x' : Fin n → Bool)
    (L : Finset (WireVertex n s)) :
    (((Finset.univ.filter fun w => .input w ∈ L ∧ x w = true).card : ℤ) -
        (Finset.univ.filter fun w => .output w ∈ L ∧ N.eval x w = true).card) -
      (((Finset.univ.filter fun w => .input w ∈ L ∧ x' w = true).card : ℤ) -
        (Finset.univ.filter fun w => .output w ∈ L ∧ N.eval x' w = true).card) ≤
      (N.wireGraph.cut L).card :=
  Halver.Internal.sub_le_card_cut N x x' L

namespace IsHalver

variable {N : ComparatorNetwork n s} {ε : ℝ}

/-- **Closed sets of wires are trivial.** For an `ε`-halver with `ε < 1/2`, every set of wires
closed under the comparators (each comparator has both wires in it or neither) is empty or all
wires. -/
theorem eq_empty_or_eq_univ_of_closed (hN : N.IsHalver ε) (hε : ε < 1 / 2)
    {S : Finset (Fin n)} (hS : ∀ c, N.minWire c ∈ S ↔ N.maxWire c ∈ S) :
    S = ∅ ∨ S = Finset.univ :=
  Halver.Internal.eq_empty_or_eq_univ_of_closed N hN hε hS

/-- **The wire graph of an `ε`-halver with `ε < 1/2` is connected.** -/
theorem wireGraph_connected (hN : N.IsHalver ε) (hε : ε < 1 / 2) : N.wireGraph.Connected :=
  Halver.Internal.wireGraph_connected N hN hε

/-- **The trivial bound.** An `ε`-halver with `ε < 1/2` on `n` wires has at least `n - 1`
comparators. -/
theorem le_add_one (hN : N.IsHalver ε) (hε : ε < 1 / 2) : n ≤ s + 1 :=
  Halver.Internal.le_add_one N hN hε

/-- **The cut lemma.** Every linear order of the vertices of the wire graph of an `ε`-halver has
a lower set whose cut has at least `(1 - 2 ε) ⌊n/2⌋` edges. -/
theorem exists_le_card_cut (hN : N.IsHalver ε) [LinearOrder (WireVertex n s)] :
    ∃ L : Finset (WireVertex n s), IsLowerSet (L : Set (WireVertex n s)) ∧
      (1 - 2 * ε) * ((n / 2 : ℕ) : ℝ) ≤ (N.wireGraph.cut L).card :=
  Halver.Internal.exists_le_card_cut N hN

/-- **The finite bound.** Under the graph-ordering hypothesis `OrderingBound A η C`, an
`ε`-halver with `ε < 1/2` on `n` wires with `s` comparators satisfies
`(1 - 2 ε) ⌊n/2⌋ ≤ (A + η) (s - n)⁺ + 3 log₂ (2 n + 2 s) + C`. -/
theorem le_of_orderingBound {A η C : ℝ} (hord : OrderingBound A η C) (hN : N.IsHalver ε)
    (hε : ε < 1 / 2) :
    (1 - 2 * ε) * ((n / 2 : ℕ) : ℝ) ≤
      (A + η) * max ((s : ℝ) - n) 0 + 3 * Real.logb 2 (2 * n + 2 * s) + C :=
  Halver.Internal.le_of_orderingBound N hord hN hε

end IsHalver

/-- **Comparators from a general ordering coefficient.** If `A > 0` and every slack `η > 0`
admits a constant `C` with `OrderingBound A η C`, then for every `0 ≤ ε < 1/2`, every `δ > 0`,
and all large `n`, every `ε`-halver on `n` wires has at least `(1 + (1 - 2ε)/(2A) - δ) n`
comparators. -/
theorem eventually_le_size_of_isHalver_of_orderingBound {A : ℝ} (hA : 0 < A)
    (hord : ∀ η : ℝ, 0 < η → ∃ C : ℝ, OrderingBound A η C) {ε δ : ℝ} (hε₀ : 0 ≤ ε)
    (hε : ε < 1 / 2) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ (s : ℕ) (N : ComparatorNetwork n s), N.IsHalver ε →
      (1 + (1 - 2 * ε) / (2 * A) - δ) * n ≤ s :=
  Halver.Internal.eventually_le_size_of_orderingBound hA hord hε₀ hε hδ

/-- **ε-halvers need `(1 + κ (1 - 2ε)/2 - o(1)) n` comparators.** For every `0 ≤ ε < 1/2`, every
`δ > 0`, and all large `n`, every `ε`-halver on `n` wires has at least `(1 + κ (1 - 2ε)/2 - δ) n`
comparators, where `κ = π/(3 arccos((1 + 2√2)/4)) ≈ 3.5625`: about `2.78 n` as `ε → 0`. -/
theorem eventually_le_size_of_isHalver {ε δ : ℝ} (hε₀ : 0 ≤ ε) (hε : ε < 1 / 2) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ (s : ℕ) (N : ComparatorNetwork n s), N.IsHalver ε →
      (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) * (1 - 2 * ε) / 2 - δ) * n ≤
        s := by
  have hp := Gaussian.frontierCoefficient_pos
  have hκ : 1 / (2 * Gaussian.frontierCoefficient) =
      Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) := by
    linarith [Gaussian.one_add_inv_two_mul_frontierCoefficient]
  have e : (1 - 2 * ε) / (2 * (2 * Gaussian.frontierCoefficient)) =
      Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) * (1 - 2 * ε) / 2 := by
    rw [← hκ]
    field_simp
  have key := eventually_le_size_of_isHalver_of_orderingBound (mul_pos two_pos hp)
    exists_orderingBound_frontier hε₀ hε hδ
  rwa [e] at key

/-- **ε-halvers need `(1 + 16 (1 - 2ε)/9 - o(1)) n` comparators.** The rational form of
`eventually_le_size_of_isHalver`, from the ordering coefficient `9/32 ≥ 2p`: at least
`(25/9 - δ) n` comparators as `ε → 0`. -/
theorem eventually_one_add_sixteen_div_nine_mul_le_size_of_isHalver {ε δ : ℝ} (hε₀ : 0 ≤ ε)
    (hε : ε < 1 / 2) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ (s : ℕ) (N : ComparatorNetwork n s), N.IsHalver ε →
      (1 + 16 * (1 - 2 * ε) / 9 - δ) * n ≤ s := by
  have key := eventually_le_size_of_isHalver_of_orderingBound (by norm_num : (0 : ℝ) < 9 / 32)
    exists_orderingBound_nine_div_thirtyTwo hε₀ hε hδ
  rwa [show (1 - 2 * ε) / (2 * (9 / 32 : ℝ)) = 16 * (1 - 2 * ε) / 9 by ring] at key

/-- **The cubic pathwidth coefficient.** With the Fomin–Høie ordering coefficient `1/3`, every
`ε`-halver on `n` wires has at least `(1 + 3 (1 - 2ε)/2 - δ) n` comparators for all large `n`. -/
theorem eventually_one_add_three_div_two_mul_le_size_of_isHalver {ε δ : ℝ} (hε₀ : 0 ≤ ε)
    (hε : ε < 1 / 2) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ (s : ℕ) (N : ComparatorNetwork n s), N.IsHalver ε →
      (1 + 3 * (1 - 2 * ε) / 2 - δ) * n ≤ s := by
  have key := eventually_le_size_of_isHalver_of_orderingBound (by norm_num : (0 : ℝ) < 1 / 3)
    exists_orderingBound_one_third hε₀ hε hδ
  rwa [show (1 - 2 * ε) / (2 * (1 / 3 : ℝ)) = 3 * (1 - 2 * ε) / 2 by ring] at key

end Algebraic.Cutwidth.ComparatorNetwork
