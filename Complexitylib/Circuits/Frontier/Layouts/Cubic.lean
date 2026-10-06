/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Mathlib.Frontier.SimpleGraph
public import Mathlib.Basic.Real.Basic

/-!
# Layouts of cubic graphs

The graph-theoretic input to the lower bound is a layout bound for subcubic multigraphs,
`Frontier.LayoutBound 3 A`. Compressing a subcubic multigraph to its cubic core reduces it to
laying out simple cubic graphs (`Frontier.Layouts.Compression`).

`CubicLayoutBound c` says that for every `ξ > 0`, every sufficiently large simple cubic graph on
`h` vertices has a layout, given as an injective vertex key, all of whose prefixes are crossed by
at most `(c + ξ) h + 2` edges. A cubic graph on `h` vertices has cycle rank `h/2 + 1`, which is
why a cubic coefficient `c` becomes the layout coefficient `2c`.
-/

@[expose] public section

namespace Complexity.Frontier

/-- **The cubic layout bound** with coefficient `c`: for every `ξ > 0`, every simple cubic graph
on `h` vertices, for `h` large enough, has an injective vertex key all of whose prefixes
`{w | key w < t}` are crossed by at most `(c + ξ) h + 2` edges. -/
def CubicLayoutBound (c : ℝ) : Prop :=
  ∀ ξ > 0, ∃ N₀ : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj], H.IsRegularOfDegree 3 → N₀ < Fintype.card W →
    ∃ key : W → ℕ, Function.Injective key ∧ ∀ t : ℕ,
      ((H.crossingFinset (Finset.univ.filter fun w => key w < t)).card : ℝ) ≤
        (c + ξ) * Fintype.card W + 2

end Complexity.Frontier
