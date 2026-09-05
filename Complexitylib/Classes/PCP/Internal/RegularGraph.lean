/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Regular graphs, their walk operator, and the spectral gap

The graph-theoretic substrate of Dinur's proof: regular multigraphs given by a
**rotation map**, the associated random-walk averaging operator, and a
square-norm formulation of the spectral gap.

A `RegGraph` carries a finite vertex type `V`, a finite nonempty label type `D`,
and an involution `rot : V × D → V × D` on *darts* (a vertex together with one
of its outgoing edge labels). The involution pairs each dart with its reverse,
which is what makes the graph undirected and `|D|`-regular, with parallel edges
and self-loops allowed — all three are needed, since powering and
expanderization produce them. The neighbour function is `nbr v i = (rot (v,i)).1`.

## Why `V` and `D` are types, not numbers

Dinur's constructions build new graphs whose vertices and labels are *structured*:
powering takes the label type to walk tuples `Fin t → D`, and degree reduction
takes the vertex type to the dart type `V × D`. Carrying `V` and `D` as types
lets those constructions be written directly, with no encoding bijections; the
translation to `Fin`-indexed data is deferred to the one place that needs it,
the encoded reduction at the very end.

## The spectral gap, without square roots

Rather than second eigenvalues, `SpectralBound G lam` says directly that the
walk operator contracts *mean-zero* functions by `lam` in the Euclidean norm,
stated on **squared** norms:

`∑ v, (step f v) ^ 2 ≤ lam ^ 2 * ∑ v, (f v) ^ 2` whenever `∑ v, f v = 0`.

This avoids `Real.sqrt` and eigenvalue machinery entirely, and it is exactly
the form the walk analysis needs: `step` preserves sums (so it preserves
mean-zero-ness), hence the bound self-composes and `t` steps contract by
`lam ^ t`.

## Main definitions

- `RegGraph`, `RegGraph.deg`, `RegGraph.order`, `RegGraph.nbr`,
  `RegGraph.step`, `RegGraph.stepIter`
- `RegGraph.SpectralBound`

## Main results

- `RegGraph.sum_nbr` — summing over darts is summing over vertices, `deg` times
- `RegGraph.sum_step` — the walk operator preserves sums
- `RegGraph.step_symm` — it is self-adjoint
- `RegGraph.sum_sq_step_le` — it is a contraction, with no spectral hypothesis
- `RegGraph.sum_sq_stepIter_le` — `t` steps contract mean-zero functions by
  `lam ^ (2 * t)` in squared norm
-/

@[expose] public section

namespace Complexity

/-- A regular multigraph, presented by a rotation map: an involution on darts
`(vertex, edge label)` sending each dart to its reverse. Every vertex has
exactly one dart per label, so the graph is `|D|`-regular; parallel edges and
self-loops are allowed. -/
structure RegGraph where
  /-- The vertex type. -/
  V : Type
  /-- The edge-label type; each vertex has one outgoing dart per label. -/
  D : Type
  /-- Vertices have decidable equality, so assignments form a `Fintype`. -/
  decEqV : DecidableEq V
  /-- Labels have decidable equality, so label tuples form a `Fintype`. -/
  decEqD : DecidableEq D
  /-- The vertex type is finite. -/
  fintypeV : Fintype V
  /-- The label type is finite. -/
  fintypeD : Fintype D
  /-- The label type is nonempty, i.e. the degree is positive. -/
  nonemptyD : Nonempty D
  /-- The rotation map, sending a dart to its reverse. -/
  rot : V × D → V × D
  /-- Reversing a dart twice is the identity. -/
  rot_involutive : Function.Involutive rot

attribute [instance] RegGraph.decEqV RegGraph.decEqD RegGraph.fintypeV RegGraph.fintypeD
  RegGraph.nonemptyD

namespace RegGraph

variable (G : RegGraph)

/-- The degree: the number of darts at each vertex. -/
def deg : ℕ := Fintype.card G.D

/-- The number of vertices. -/
def order : ℕ := Fintype.card G.V

theorem deg_pos : 0 < G.deg := Fintype.card_pos

@[simp] theorem card_eq_order : Fintype.card G.V = G.order := rfl

@[simp] theorem card_eq_deg : Fintype.card G.D = G.deg := rfl

theorem deg_ne_zero : (G.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr G.deg_pos.ne'

/-- The `i`-th neighbour of `v`. -/
def nbr (v : G.V) (i : G.D) : G.V := (G.rot (v, i)).1

/-- The rotation map is a bijection of darts. -/
theorem rot_bijective : Function.Bijective G.rot := G.rot_involutive.bijective

/-- Summing a function of the neighbour over all darts is summing it over all
vertices, each counted `deg` times. This is the rotation-map form of
regularity, and it is the source of every counting identity below. Stated for an
arbitrary `AddCommMonoid`, since the walk analysis needs it both for real
averages and for counting in `ℕ`. -/
theorem sum_nbr_nsmul {M : Type*} [AddCommMonoid M] (f : G.V → M) :
    ∑ v : G.V, ∑ i : G.D, f (G.nbr v i) = G.deg • ∑ v : G.V, f v := by
  have hprod : ∑ p : G.V × G.D, f (G.rot p).1 = ∑ p : G.V × G.D, f p.1 :=
    Fintype.sum_bijective G.rot G.rot_bijective _ _ fun _ => rfl
  calc ∑ v : G.V, ∑ i : G.D, f (G.nbr v i)
      = ∑ p : G.V × G.D, f (G.rot p).1 :=
        (Fintype.sum_prod_type (fun p : G.V × G.D => f (G.rot p).1)).symm
    _ = ∑ p : G.V × G.D, f p.1 := hprod
    _ = ∑ v : G.V, ∑ _i : G.D, f v := Fintype.sum_prod_type (fun p : G.V × G.D => f p.1)
    _ = ∑ v : G.V, G.deg • f v := by simp
    _ = G.deg • ∑ v : G.V, f v := Finset.sum_nsmul _ _ _

theorem sum_nbr (f : G.V → ℝ) :
    ∑ v : G.V, ∑ i : G.D, f (G.nbr v i) = (G.deg : ℝ) * ∑ v : G.V, f v := by
  rw [G.sum_nbr_nsmul f, nsmul_eq_mul]

/-- One step of the random walk, as an averaging operator on real-valued
functions on the vertices. -/
noncomputable def step (f : G.V → ℝ) (v : G.V) : ℝ :=
  (∑ i : G.D, f (G.nbr v i)) / (G.deg : ℝ)

/-- The walk operator preserves sums: it is doubly stochastic. -/
theorem sum_step (f : G.V → ℝ) : ∑ v : G.V, G.step f v = ∑ v : G.V, f v := by
  have hd : (G.deg : ℝ) ≠ 0 := G.deg_ne_zero
  calc ∑ v : G.V, G.step f v
      = (∑ v : G.V, ∑ i : G.D, f (G.nbr v i)) / (G.deg : ℝ) := by
        rw [Finset.sum_div]; rfl
    _ = ((G.deg : ℝ) * ∑ v : G.V, f v) / (G.deg : ℝ) := by rw [G.sum_nbr f]
    _ = ∑ v : G.V, f v := by field_simp

/-- The walk operator is self-adjoint for the standard inner product. -/
theorem step_symm (f g : G.V → ℝ) :
    ∑ v : G.V, G.step f v * g v = ∑ v : G.V, f v * G.step g v := by
  have key : ∑ p : G.V × G.D, f (G.rot p).1 * g p.1
      = ∑ p : G.V × G.D, f p.1 * g (G.rot p).1 := by
    refine Fintype.sum_bijective G.rot G.rot_bijective _ _ fun p => ?_
    rw [G.rot_involutive p]
  have hL : ∑ v : G.V, G.step f v * g v
      = (∑ p : G.V × G.D, f (G.rot p).1 * g p.1) / (G.deg : ℝ) := by
    rw [Fintype.sum_prod_type, Finset.sum_div]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [step, div_mul_eq_mul_div, Finset.sum_mul]
    rfl
  have hR : ∑ v : G.V, f v * G.step g v
      = (∑ p : G.V × G.D, f p.1 * g (G.rot p).1) / (G.deg : ℝ) := by
    rw [Fintype.sum_prod_type, Finset.sum_div]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [step, mul_div_assoc', Finset.mul_sum]
    rfl
  rw [hL, hR, key]

/-- The `t`-step walk operator. -/
noncomputable def stepIter (t : ℕ) (f : G.V → ℝ) : G.V → ℝ := G.step^[t] f

@[simp] theorem stepIter_zero (f : G.V → ℝ) : G.stepIter 0 f = f := rfl

theorem stepIter_succ (t : ℕ) (f : G.V → ℝ) :
    G.stepIter (t + 1) f = G.step (G.stepIter t f) :=
  Function.iterate_succ_apply' _ _ _

theorem stepIter_succ' (t : ℕ) (f : G.V → ℝ) :
    G.stepIter (t + 1) f = G.stepIter t (G.step f) :=
  Function.iterate_succ_apply _ _ _

theorem sum_stepIter (t : ℕ) (f : G.V → ℝ) :
    ∑ v : G.V, G.stepIter t f v = ∑ v : G.V, f v := by
  induction t with
  | zero => simp
  | succ t ih => rw [stepIter_succ, G.sum_step, ih]

/-- **The walk operator is a contraction.** Averaging can only shrink the
Euclidean norm — this is Cauchy–Schwarz on each vertex's average, summed with
`sum_nbr`. It holds for *every* regular graph, with no spectral assumption, and
is what lets a graph be combined with an expander: the graph's own part of the
combined walk contributes at most its full weight. -/
theorem sum_sq_step_le (f : G.V → ℝ) :
    (∑ v : G.V, (G.step f v) ^ 2) ≤ ∑ v : G.V, (f v) ^ 2 := by
  have hd : (0 : ℝ) < (G.deg : ℝ) := by
    have := G.deg_pos
    positivity
  have hpt : ∀ v : G.V, (G.step f v) ^ 2 ≤ (∑ i : G.D, (f (G.nbr v i)) ^ 2) / (G.deg : ℝ) := by
    intro v
    have hcs : (∑ i : G.D, f (G.nbr v i)) ^ 2
        ≤ (G.deg : ℝ) * ∑ i : G.D, (f (G.nbr v i)) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset G.D))
        (f := fun i => f (G.nbr v i))
      rwa [Finset.card_univ, card_eq_deg] at h
    rw [step, div_pow, div_le_div_iff₀ (by positivity) hd]
    calc (∑ i : G.D, f (G.nbr v i)) ^ 2 * (G.deg : ℝ)
        ≤ ((G.deg : ℝ) * ∑ i : G.D, (f (G.nbr v i)) ^ 2) * (G.deg : ℝ) := by
          exact mul_le_mul_of_nonneg_right hcs (le_of_lt hd)
      _ = (∑ i : G.D, (f (G.nbr v i)) ^ 2) * (G.deg : ℝ) ^ 2 := by ring
  calc ∑ v : G.V, (G.step f v) ^ 2
      ≤ ∑ v : G.V, (∑ i : G.D, (f (G.nbr v i)) ^ 2) / (G.deg : ℝ) :=
        Finset.sum_le_sum fun v _ => hpt v
    _ = (∑ v : G.V, ∑ i : G.D, (f (G.nbr v i)) ^ 2) / (G.deg : ℝ) := by
        rw [Finset.sum_div]
    _ = ((G.deg : ℝ) * ∑ v : G.V, (f v) ^ 2) / (G.deg : ℝ) := by
        rw [G.sum_nbr (fun v => (f v) ^ 2)]
    _ = ∑ v : G.V, (f v) ^ 2 := by field_simp

/-- `G` has spectral gap at least `1 - lam`: the walk operator contracts every
mean-zero function by a factor `lam` in the Euclidean norm, stated on squared
norms so that no square roots are needed. -/
def SpectralBound (G : RegGraph) (lam : ℝ) : Prop :=
  ∀ f : G.V → ℝ, (∑ v : G.V, f v) = 0 →
    (∑ v : G.V, (G.step f v) ^ 2) ≤ lam ^ 2 * ∑ v : G.V, (f v) ^ 2

/-- A weaker contraction factor is still a contraction factor. -/
theorem SpectralBound.mono {G : RegGraph} {lam lam' : ℝ} (h : G.SpectralBound lam)
    (h0 : 0 ≤ lam) (hle : lam ≤ lam') : G.SpectralBound lam' := by
  intro f hf
  refine le_trans (h f hf) (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact pow_le_pow_left₀ h0 hle 2

/-- Every graph contracts the empty family of mean-zero functions: a graph with
no vertices has any contraction factor. -/
theorem spectralBound_of_isEmpty {G : RegGraph} (h : IsEmpty G.V) (lam : ℝ) :
    G.SpectralBound lam := by
  intro f _
  have he : (Finset.univ : Finset G.V) = ∅ := Finset.univ_eq_empty
  rw [he, Finset.sum_empty, Finset.sum_empty, mul_zero]

/-- The contraction self-composes: `t` steps contract a mean-zero function by
`lam ^ t`, i.e. `lam ^ (2 * t)` in squared norm. -/
theorem sum_sq_stepIter_le {lam : ℝ} (h : G.SpectralBound lam) (t : ℕ) (f : G.V → ℝ)
    (hf : (∑ v : G.V, f v) = 0) :
    (∑ v : G.V, (G.stepIter t f v) ^ 2) ≤ lam ^ (2 * t) * ∑ v : G.V, (f v) ^ 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hzero : (∑ v : G.V, G.stepIter t f v) = 0 := by rw [G.sum_stepIter, hf]
      have hstep := h (G.stepIter t f) hzero
      have hpow : (0 : ℝ) ≤ lam ^ 2 := by positivity
      calc ∑ v : G.V, (G.stepIter (t + 1) f v) ^ 2
          = ∑ v : G.V, (G.step (G.stepIter t f) v) ^ 2 := by rw [stepIter_succ]
        _ ≤ lam ^ 2 * ∑ v : G.V, (G.stepIter t f v) ^ 2 := hstep
        _ ≤ lam ^ 2 * (lam ^ (2 * t) * ∑ v : G.V, (f v) ^ 2) :=
            mul_le_mul_of_nonneg_left ih hpow
        _ = lam ^ (2 * (t + 1)) * ∑ v : G.V, (f v) ^ 2 := by
            rw [← mul_assoc, ← pow_add]; ring_nf

end RegGraph

end Complexity
