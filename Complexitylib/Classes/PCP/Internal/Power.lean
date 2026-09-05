/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.WalkPath

/-!
# Walk reversal and the powered graph

The graph-theoretic half of Dinur's powering step. The `t`-th power of a
regular graph `G` has the same vertices, and one edge for each **walk** of
length `t` in `G`, joining the walk's two ends.

Making that a `RegGraph` means exhibiting the rotation map: an involution on
darts. A dart of the power is a vertex together with a tuple of `t` labels, and
its reverse is the *reversed walk* — starting at the far end and retracing the
same edges backwards. So the work here is to define reversal and prove it is an
involution.

## How reversal is defined

The `k`-th dart of the walk `(v, s)` is `(walkAt k, s k)`; reversing it with
`G.rot` yields the next vertex together with the label that points *back*,
called `backLabel`. The reversed walk reads those back-labels in reverse order,
using `Fin.rev` — whose own involutivity (`Fin.rev_rev`) carries most of the
index bookkeeping.

`rot_dart` is the one computational fact everything rests on: reversing the
`k`-th dart gives `(walkAt (k+1), backLabel k)`. Applying `G.rot_involutive` to
it turns each step of the reversed walk back into a step of the original.

## Why the power's spectral bound is `lam ^ t`

The power's walk operator *is* the `t`-fold operator of `G`: averaging over all
`deg ^ t` walks out of a vertex is exactly `stepIter t` (`sum_walkEnd`). So the
squared-norm contraction of `RegularGraph` applies verbatim, and a graph with
`SpectralBound lam` powers up to one with `SpectralBound (lam ^ t)`. This is
what makes powering amplify the gap.

## Main definitions

- `RegGraph.backLabel` — the label pointing back along a dart of a walk
- `RegGraph.revWalk` — the reversed walk
- `RegGraph.power` — the `t`-th power as a `RegGraph`

## Main results

- `RegGraph.rot_dart` — reversing the `k`-th dart of a walk
- `RegGraph.walkAt_revWalk` — the reversed walk retraces the trajectory
- `RegGraph.walkEnd_revWalk`, `RegGraph.revWalk_revWalk` — reversal is an
  involution
- `RegGraph.step_power` — the power's walk operator is `stepIter t`
- `RegGraph.spectralBound_power` — `SpectralBound lam` powers to
  `SpectralBound (lam ^ t)`
- `RegGraph.deg_power`, `RegGraph.order_power`
-/

@[expose] public section

namespace Complexity

namespace RegGraph

variable (G : RegGraph)

/-! ### Reversing the darts of a walk -/

/-- The label at `walkAt (k+1)` that points back along the `k`-th dart of the
walk `(v, s)`. -/
def backLabel {t : ℕ} (v : G.V) (s : Fin t → G.D) (k : Fin t) : G.D :=
  (G.rot (G.walkAt t v s k.val, s k)).2

/-- **The computational core.** Reversing the `k`-th dart of the walk `(v, s)`
gives the next vertex on the walk, together with the label pointing back. -/
theorem rot_dart {t : ℕ} (v : G.V) (s : Fin t → G.D) (k : Fin t) :
    G.rot (G.walkAt t v s k.val, s k)
      = (G.walkAt t v s (k.val + 1), G.backLabel v s k) := by
  refine Prod.ext ?_ rfl
  exact (G.walkAt_succ_of_lt v s k.isLt).symm

/-- The walk `(v, s)` reversed: it starts at the far end and reads the
back-labels of the original darts in reverse order. -/
def revWalk {t : ℕ} (v : G.V) (s : Fin t → G.D) : Fin t → G.D :=
  fun j => G.backLabel v s (Fin.rev j)

/-- The reversed walk retraces the original trajectory backwards. -/
theorem walkAt_revWalk {t : ℕ} (v : G.V) (s : Fin t → G.D) :
    ∀ k : ℕ, k ≤ t →
      G.walkAt t (G.walkEnd t v s) (G.revWalk v s) k = G.walkAt t v s (t - k) := by
  intro k
  induction k with
  | zero => intro _; simpa using (G.walkAt_self_eq_walkEnd v s).symm
  | succ k ih =>
      intro hk
      have hkt : k < t := by omega
      have hk' : k ≤ t := le_of_lt hkt
      have hrev : (Fin.rev (⟨k, hkt⟩ : Fin t)).val = t - (k + 1) := by
        rw [Fin.val_rev]
      have hrot := G.rot_dart v s (Fin.rev (⟨k, hkt⟩ : Fin t))
      have hinv := G.rot_involutive
        (G.walkAt t v s (Fin.rev (⟨k, hkt⟩ : Fin t)).val, s (Fin.rev (⟨k, hkt⟩ : Fin t)))
      rw [hrot] at hinv
      rw [G.walkAt_succ_of_lt _ _ hkt, ih hk']
      have harith : t - k = (t - (k + 1)) + 1 := by omega
      have hstep : G.revWalk v s ⟨k, hkt⟩ = G.backLabel v s (Fin.rev (⟨k, hkt⟩ : Fin t)) := rfl
      rw [hstep, harith, nbr, ← hrev, hinv, hrev]

/-- Reversing a walk lands back at its start. -/
theorem walkEnd_revWalk {t : ℕ} (v : G.V) (s : Fin t → G.D) :
    G.walkEnd t (G.walkEnd t v s) (G.revWalk v s) = v := by
  have h := G.walkAt_revWalk v s t le_rfl
  rw [G.walkAt_self_eq_walkEnd] at h
  simpa using h

/-- Reversal is an involution on walks. -/
theorem revWalk_revWalk {t : ℕ} (v : G.V) (s : Fin t → G.D) :
    G.revWalk (G.walkEnd t v s) (G.revWalk v s) = s := by
  funext j
  have hj : (Fin.rev j).val ≤ t := le_of_lt (Fin.rev j).isLt
  have hwalk : G.walkAt t (G.walkEnd t v s) (G.revWalk v s) (Fin.rev j).val
      = G.walkAt t v s (t - (Fin.rev j).val) := G.walkAt_revWalk v s _ hj
  have harith : t - (Fin.rev j).val = j.val + 1 := by
    rw [Fin.val_rev]; omega
  have hlabel : G.revWalk v s (Fin.rev j) = G.backLabel v s j := by
    rw [revWalk, Fin.rev_rev]
  have hrot := G.rot_dart v s j
  have hinv := G.rot_involutive (G.walkAt t v s j.val, s j)
  rw [hrot] at hinv
  calc G.revWalk (G.walkEnd t v s) (G.revWalk v s) j
      = (G.rot (G.walkAt t (G.walkEnd t v s) (G.revWalk v s) (Fin.rev j).val,
          G.revWalk v s (Fin.rev j))).2 := rfl
    _ = (G.rot (G.walkAt t v s (j.val + 1), G.backLabel v s j)).2 := by
        rw [hwalk, harith, hlabel]
    _ = s j := by rw [hinv]

/-! ### The powered graph -/

/-- The `t`-th power of `G`: same vertices, one edge per walk of length `t`. -/
def power (G : RegGraph) (t : ℕ) : RegGraph where
  V := G.V
  D := Fin t → G.D
  decEqV := G.decEqV
  decEqD := inferInstance
  fintypeV := G.fintypeV
  fintypeD := inferInstance
  nonemptyD := inferInstance
  rot p := (G.walkEnd t p.1 p.2, G.revWalk p.1 p.2)
  rot_involutive p := by
    refine Prod.ext ?_ ?_
    · exact G.walkEnd_revWalk p.1 p.2
    · exact G.revWalk_revWalk p.1 p.2

@[simp] theorem V_power (t : ℕ) : (G.power t).V = G.V := rfl

@[simp] theorem D_power (t : ℕ) : (G.power t).D = (Fin t → G.D) := rfl

@[simp] theorem order_power (t : ℕ) : (G.power t).order = G.order := rfl

@[simp] theorem deg_power (t : ℕ) : (G.power t).deg = G.deg ^ t := by
  show Fintype.card (Fin t → G.D) = G.deg ^ t
  rw [Fintype.card_fun, Fintype.card_fin]
  rfl

theorem nbr_power (t : ℕ) (v : G.V) (s : Fin t → G.D) :
    (G.power t).nbr v s = G.walkEnd t v s := rfl

/-- The power's walk operator is the `t`-fold walk operator of `G`. -/
theorem step_power (t : ℕ) (f : G.V → ℝ) (v : G.V) :
    (G.power t).step f v = G.stepIter t f v := by
  have hd : ((G.deg : ℝ)) ^ t ≠ 0 := pow_ne_zero _ G.deg_ne_zero
  calc (G.power t).step f v
      = (∑ s : Fin t → G.D, f (G.walkEnd t v s)) / ((G.deg ^ t : ℕ) : ℝ) := by
        simp only [step, deg_power]
        rfl
    _ = ((G.deg : ℝ) ^ t * G.stepIter t f v) / ((G.deg : ℝ) ^ t) := by
        rw [G.sum_walkEnd f t v]
        push_cast
        ring_nf
    _ = G.stepIter t f v := by
        field_simp

/-- **Powering amplifies the spectral gap.** -/
theorem spectralBound_power {lam : ℝ} (h : G.SpectralBound lam) (t : ℕ) :
    (G.power t).SpectralBound (lam ^ t) := by
  intro f hf
  show (∑ v : G.V, ((G.power t).step f v) ^ 2) ≤ (lam ^ t) ^ 2 * ∑ v : G.V, (f v) ^ 2
  have hsum : (∑ v : G.V, f v) = 0 := hf
  have hbound := G.sum_sq_stepIter_le h t f hsum
  have hstep : ∀ v : G.V, (G.power t).step f v = G.stepIter t f v := G.step_power t f
  calc ∑ v : G.V, ((G.power t).step f v) ^ 2
      = ∑ v : G.V, (G.stepIter t f v) ^ 2 :=
        Finset.sum_congr rfl fun v _ => by rw [hstep v]
    _ ≤ lam ^ (2 * t) * ∑ v : G.V, (f v) ^ 2 := hbound
    _ = (lam ^ t) ^ 2 * ∑ v : G.V, (f v) ^ 2 := by
        rw [← pow_mul, mul_comm 2 t]

end RegGraph

end Complexity
