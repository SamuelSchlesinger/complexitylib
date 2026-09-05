/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.Expander
public import Complexitylib.Classes.PCP.Internal.Mixing

/-!
# The pieces a merge is built from

Explicit expander constructions come in special sizes — squares, powers — but
`ExpanderFamily` wants a member on *every* `n`. An expander on `N` vertices is
folded onto `n` of them by identifying `u` with `u mod n`, with self-loops
padding the fibres that come up short. `MergeGen` carries out that fold at an
arbitrary width; this module holds the two ingredients it rests on.

The first is the estimate on the old steps. Write `f` for a function on the
merged graph and `F = f ∘ π` for its lift. Splitting `F` into its mean and its
centred part and applying the base's spectral bound to the latter gives
`λ² ‖F‖² + (1 - λ²) N c²`, where `c` is the mean of `F` — nonzero, because the
heavier fibres weigh more.

The second is that the fibres stay *balanced*: with `(m - 1) n ≤ N` at most one
of a vertex's `m` slots is empty, so however large the width, the padding costs
one loop per vertex.

## Main definitions

- `Complexity.RegGraph.proj` — the new vertex an old one lands on
- `Complexity.RegGraph.liftN` — the old vertex in a given slot of a fibre

## Main results

- `Complexity.RegGraph.sum_sq_step_lift_le` — the old steps, with the mean
  corrected
- `Complexity.RegGraph.card_liftN_none_le_one` — the balanced fibres a general
  merge needs
-/

@[expose] public section

namespace Complexity

namespace RegGraph

variable {N d n : ℕ}

/-! ### The fibres of a merge -/

/-- The new vertex an old vertex lands on. -/
def proj (n : ℕ) (hn : 0 < n) (u : Fin N) : Fin n := ⟨u.val % n, Nat.mod_lt _ hn⟩

/-! ### The spectral bound -/

section Spectral

/-- The base graph, on `Fin N`. -/
abbrev base (hd : 0 < d) (rot : Fin N × Fin d → Fin N × Fin d)
    (hrot : Function.Involutive rot) : RegGraph := ofRot d hd N rot hrot

/-- **The old steps of the lift**, with the mean corrected. -/
theorem sum_sq_step_lift_le (hn : 0 < n) (hd : 0 < d) (rot : Fin N × Fin d → Fin N × Fin d)
    (hrot : Function.Involutive rot) {lam : ℝ} (hspec : (base hd rot hrot).SpectralBound lam)
    (hN0 : 0 < N) (f : Fin n → ℝ) :
    ∑ u : Fin N, ((base hd rot hrot).step (fun w => f (proj n hn w)) u) ^ 2
      ≤ lam ^ 2 * ∑ u : Fin N, (f (proj n hn u)) ^ 2
        + (1 - lam ^ 2) * ((∑ u : Fin N, f (proj n hn u)) ^ 2 / (N : ℝ)) := by
  classical
  set G := base hd rot hrot with hG
  set F : Fin N → ℝ := fun w => f (proj n hn w) with hF
  have hord : (G.order : ℝ) = N := by rw [hG, order_ofRot]
  have hordpos : 0 < G.order := by rw [hG, order_ofRot]; exact hN0
  -- decompose `F` into its mean and its centred part
  have hdec : F = fun v => G.mean F + G.center F v := G.eq_mean_add_center F
  have hstep : ∀ u, G.step F u = G.mean F + G.step (G.center F) u := by
    intro u
    conv_lhs => rw [hdec]
    rw [G.step_add (fun _ => G.mean F) (G.center F) u, step_const]
  have hcsum : ∑ u, G.center F u = 0 := G.sum_center hordpos F
  have hstepsum : ∑ u, G.step (G.center F) u = 0 := by rw [G.sum_step, hcsum]
  have hspec' := hspec (G.center F) hcsum
  have hsq : ∑ u, (G.step F u) ^ 2
      = ∑ u, (G.step (G.center F) u) ^ 2 + (N : ℝ) * (G.mean F) ^ 2 := by
    rw [Finset.sum_congr rfl fun u _ => by rw [hstep u]]
    have : ∀ u, (G.mean F + G.step (G.center F) u) ^ 2
        = (G.step (G.center F) u) ^ 2 + 2 * G.mean F * G.step (G.center F) u
          + (G.mean F) ^ 2 := fun u => by ring
    have hcardV : Fintype.card (base hd rot hrot).V = N := Fintype.card_fin N
    rw [Finset.sum_congr rfl fun u _ => this u, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, hstepsum, Finset.sum_const, Finset.card_univ,
      hcardV, nsmul_eq_mul]
    ring
  have hFsq := G.sum_sq_center hordpos F
  rw [hord] at hFsq
  have hmean : (N : ℝ) * (G.mean F) ^ 2 = (∑ u, F u) ^ 2 / (N : ℝ) := by
    unfold mean
    rw [hord]
    field_simp
    rfl
  show ∑ u, G.step F u ^ 2 ≤ lam ^ 2 * ∑ u, F u ^ 2 + (1 - lam ^ 2) * ((∑ u, F u) ^ 2 / (N : ℝ))
  rw [hsq, hmean]
  have hsub : ∑ u, (G.center F u) ^ 2 = ∑ u, (F u) ^ 2 - (∑ u, F u) ^ 2 / (N : ℝ) := hFsq
  rw [hsub] at hspec'
  have hnn : 0 ≤ (∑ u, F u) ^ 2 / (N : ℝ) := by positivity
  nlinarith [hspec', hnn]

end Spectral

/-! ### Balanced fibres, for a merge of any width

With `(m - 1) n ≤ N ≤ m n` every fibre has `m - 1` or `m` elements, so at most
one of the `m` slots is empty and the padding costs one loop per vertex however
large `m` is.

These are the two facts a general merge rests on; they are stated for a
natural-number slot index, which is the form the general construction needs. -/

/-- The old vertex in slot `i` of the fibre over `v`, if there is one. -/
def liftN (N n : ℕ) (v : Fin n) (i : ℕ) : Option (Fin N) :=
  if h : v.val + i * n < N then some ⟨v.val + i * n, h⟩ else none

/-- **Every slot but the last is filled**, when `(m - 1) n ≤ N`. -/
theorem liftN_isSome {N n m : ℕ} (hm : (m - 1) * n ≤ N) (v : Fin n) {i : ℕ}
    (hi : i + 1 < m) : (liftN N n v i).isSome := by
  rw [liftN]
  have hle : v.val + i * n < (m - 1) * n := by
    have h1 : i + 1 ≤ m - 1 := by omega
    calc v.val + i * n < n + i * n := by omega
      _ = (i + 1) * n := by ring
      _ ≤ (m - 1) * n := Nat.mul_le_mul_right _ h1
  rw [dite_eq_left (lt_of_lt_of_le hle hm)]
  rfl

/-- **So at most one slot is empty.** -/
theorem card_liftN_none_le_one {N n m : ℕ} (hm : (m - 1) * n ≤ N) (v : Fin n) :
    ((Finset.range m).filter fun i => liftN N n v i = none).card ≤ 1 := by
  classical
  refine Finset.card_le_one.2 fun i hi j hj => ?_
  rw [Finset.mem_filter, Finset.mem_range] at hi hj
  by_contra hne
  have hlast : ∀ k : ℕ, k < m → liftN N n v k = none → k + 1 = m := by
    intro k hk hnone
    by_contra hcon
    have : k + 1 < m := by omega
    have := liftN_isSome hm v this
    rw [hnone] at this
    exact absurd this (by simp)
  have h1 := hlast i hi.1 hi.2
  have h2 := hlast j hj.1 hj.2
  omega

end RegGraph

end Complexity
