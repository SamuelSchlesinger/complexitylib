/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic

/-!
# Vertices straddling an edge-score threshold

A real score on the edges of a graph orders them, and a threshold `t` splits them into the
edges scoring below `t` and those scoring at least `t`. `EdgeStraddles H score t v` says that
the vertex `v` has incident edges on both sides of this split.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- Some edge at `v` scores below `t` and another scores at least `t`. -/
def EdgeStraddles (score : Sym2 W → ℝ) (t : ℝ) (v : W) : Prop :=
  ∃ e ∈ H.incidenceFinset v, score e < t ∧ ∃ e' ∈ H.incidenceFinset v, t ≤ score e'

end Algebraic.Cutwidth.Gaussian
