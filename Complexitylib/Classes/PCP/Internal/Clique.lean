/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.WalkPath

/-!
# The complete graph with self-loops

The simplest nontrivial `RegGraph`: `n` vertices, degree `n`, with the `i`-th
neighbour of every vertex being `i`. Its rotation map is the swap, so every
vertex is joined to every vertex including itself.

It is a *perfect* expander: one step of its walk lands on the uniform
distribution, so the walk operator annihilates mean-zero functions and
`SpectralBound 0` holds. This validates the definitions in `RegularGraph` on a
case where the answer is known, and supplies the loops that `WalkPath` needs.

## Main definitions

- `RegGraph.cliqueLoops` — the complete graph with all self-loops
- `RegGraph.cliqueLoopsLoops` — its canonical self-loop at each vertex

## Main results

- `RegGraph.nbr_cliqueLoops`, `RegGraph.step_cliqueLoops`
- `RegGraph.spectralBound_cliqueLoops` — a spectral bound of `0`
-/

@[expose] public section

namespace Complexity

namespace RegGraph

/-- The complete graph on `n` vertices with a self-loop at every vertex,
presented by the swap rotation map: the `i`-th neighbour of `v` is `i`. -/
def cliqueLoops (n : ℕ) (hn : 0 < n) : RegGraph where
  V := Fin n
  D := Fin n
  decEqV := inferInstance
  decEqD := inferInstance
  fintypeV := inferInstance
  fintypeD := inferInstance
  nonemptyD := ⟨⟨0, hn⟩⟩
  rot p := (p.2, p.1)
  rot_involutive _ := rfl

@[simp] theorem V_cliqueLoops (n : ℕ) (hn : 0 < n) : (cliqueLoops n hn).V = Fin n := rfl

@[simp] theorem D_cliqueLoops (n : ℕ) (hn : 0 < n) : (cliqueLoops n hn).D = Fin n := rfl

@[simp] theorem deg_cliqueLoops (n : ℕ) (hn : 0 < n) : (cliqueLoops n hn).deg = n :=
  Fintype.card_fin n

@[simp] theorem order_cliqueLoops (n : ℕ) (hn : 0 < n) : (cliqueLoops n hn).order = n :=
  Fintype.card_fin n

@[simp] theorem nbr_cliqueLoops {n : ℕ} (hn : 0 < n) (v : (cliqueLoops n hn).V)
    (i : (cliqueLoops n hn).D) : (cliqueLoops n hn).nbr v i = i := rfl

/-- Every vertex of the complete graph with loops has a self-loop, namely its
own index. -/
def cliqueLoopsLoops (n : ℕ) (hn : 0 < n) : (cliqueLoops n hn).Loops where
  loop v := v
  rot_loop _ := rfl

/-- One step of the walk lands on the uniform distribution: the average of `f`
over all vertices, whatever the current vertex. -/
theorem step_cliqueLoops {n : ℕ} (hn : 0 < n) (f : (cliqueLoops n hn).V → ℝ)
    (v : (cliqueLoops n hn).V) :
    (cliqueLoops n hn).step f v
      = (∑ w : (cliqueLoops n hn).V, f w) / ((cliqueLoops n hn).deg : ℝ) := by
  simp only [step]
  rfl

/-- The complete graph with loops is a perfect expander. -/
theorem spectralBound_cliqueLoops {n : ℕ} (hn : 0 < n) :
    (cliqueLoops n hn).SpectralBound 0 := by
  intro f hf
  have hstep : ∀ v : (cliqueLoops n hn).V, (cliqueLoops n hn).step f v = 0 := by
    intro v
    rw [step_cliqueLoops hn f v, hf, zero_div]
  simp only [hstep, zero_pow two_ne_zero, Finset.sum_const_zero, zero_mul, le_refl]

end RegGraph

end Complexity
