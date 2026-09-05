/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.Walk

/-!
# Trajectories of walks, and self-loops

`Walk` gives the *endpoint* of a walk, which is all the spectral estimates
need. Dinur's powering step also needs the walk's whole **trajectory**: the
constraint attached to a length-`t` walk talks about the graph constraints on
each intermediate edge, and about what the two endpoints of the walk claim the
intermediate vertices are labelled.

This module adds the trajectory `walkAt`, indexed by `ℕ` and constant once the
walk is exhausted, and identifies its final position with `walkEnd`. The bridge
runs through `walkEnd_snoc`: extending a walk by one label at the *end* takes
one more step from its endpoint, whereas `walkEnd` recurses on the *first*
label.

It also introduces `Loops`, a choice of self-loop at each vertex. Dinur's
construction needs these to pad a short walk out to a fixed length without
moving: a vertex within distance `k ≤ h` of `v` is the endpoint of a length-`h`
walk from `v` that follows `k` real steps and then stays put.

## Main definitions

- `RegGraph.walkAt` — the position of the walk after `k` steps (`k > t` stays)
- `RegGraph.Loops` — a self-loop at every vertex
- `RegGraph.Loops.padWalk` — a short walk padded out to a fixed length

## Main results

- `RegGraph.walkEnd_snoc` — appending a label takes one further step
- `RegGraph.walkAt_eq_walkEnd_prefix`, `RegGraph.walkAt_self_eq_walkEnd`
- `RegGraph.walkAt_of_le` — the trajectory is constant past its length
- `RegGraph.Loops.nbr_loop` — a loop label does not move
- `RegGraph.Loops.walkEnd_padWalk` — a padded walk of length `h` ends at the
  `k`-th vertex of the walk it pads, so every vertex within distance `h` is
  named by some length-`h` walk
-/

@[expose] public section

namespace Complexity

namespace RegGraph

variable (G : RegGraph)

/-! ### Extending a walk at its end -/

theorem walkEnd_snoc : ∀ (t : ℕ) (v : G.V) (s : Fin t → G.D) (i : G.D),
    G.walkEnd (t + 1) v (Fin.snoc s i) = G.nbr (G.walkEnd t v s) i := by
  intro t
  induction t with
  | zero =>
      intro v s i
      have h0 : (0 : Fin 1) = Fin.last 0 := rfl
      rw [walkEnd_succ, h0, Fin.snoc_last]
      simp
  | succ t ih =>
      intro v s i
      have hcs : (Fin.snoc s i : Fin (t + 2) → G.D)
          = Fin.cons (s 0) (Fin.snoc (α := fun _ => G.D) (fun j => s j.succ) i) := by
        rw [Fin.cons_snoc_eq_snoc_cons]
        congr 1
        exact (Fin.cons_self_tail s).symm
      rw [hcs, walkEnd_cons, ih, walkEnd_succ]

/-! ### The trajectory -/

/-- The position of the walk `(v, s)` after `k` steps. Once the label tuple is
exhausted the walk stays where it is, so this is defined for every `k : ℕ`. -/
def walkAt (G : RegGraph) (t : ℕ) (v : G.V) (s : Fin t → G.D) : ℕ → G.V
  | 0 => v
  | k + 1 => if h : k < t then G.nbr (walkAt G t v s k) (s ⟨k, h⟩) else walkAt G t v s k

@[simp] theorem walkAt_zero (t : ℕ) (v : G.V) (s : Fin t → G.D) :
    G.walkAt t v s 0 = v := rfl

theorem walkAt_succ_of_lt {t : ℕ} (v : G.V) (s : Fin t → G.D) {k : ℕ} (h : k < t) :
    G.walkAt t v s (k + 1) = G.nbr (G.walkAt t v s k) (s ⟨k, h⟩) := by
  rw [walkAt]
  simp [h]

theorem walkAt_succ_of_ge {t : ℕ} (v : G.V) (s : Fin t → G.D) {k : ℕ} (h : t ≤ k) :
    G.walkAt t v s (k + 1) = G.walkAt t v s k := by
  rw [walkAt]
  simp [Nat.not_lt.mpr h]

/-- Past its length the trajectory is constant. -/
theorem walkAt_of_le {t : ℕ} (v : G.V) (s : Fin t → G.D) :
    ∀ {k : ℕ}, t ≤ k → G.walkAt t v s k = G.walkAt t v s t := by
  intro k
  induction k with
  | zero =>
      intro h
      have ht : t = 0 := Nat.le_zero.mp h
      subst ht
      rfl
  | succ k ih =>
      intro h
      rcases Nat.lt_or_ge t (k + 1) with hlt | hge
      · have htk : t ≤ k := by omega
        rw [G.walkAt_succ_of_ge v s htk, ih htk]
      · have ht : t = k + 1 := by omega
        subst ht
        rfl

/-- The trajectory after `k ≤ t` steps is the endpoint of the length-`k` prefix
of the walk. -/
theorem walkAt_eq_walkEnd_prefix {t : ℕ} (v : G.V) (s : Fin t → G.D) :
    ∀ (k : ℕ) (hk : k ≤ t),
      G.walkAt t v s k = G.walkEnd k v (fun j : Fin k => s (Fin.castLE hk j)) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hkt : k < t := by omega
      have hk' : k ≤ t := le_of_lt hkt
      have hsnoc : (fun j : Fin (k + 1) => s (Fin.castLE hk j))
          = Fin.snoc (α := fun _ => G.D)
              (fun j : Fin k => s (Fin.castLE hk' j)) (s ⟨k, hkt⟩) := by
        funext j
        refine Fin.lastCases ?_ ?_ j
        · rw [Fin.snoc_last]
          congr 1
        · intro j'
          rw [Fin.snoc_castSucc]
          congr 1
      rw [G.walkAt_succ_of_lt v s hkt, ih hk', hsnoc, G.walkEnd_snoc]

/-- The trajectory ends where `walkEnd` says it does. -/
theorem walkAt_self_eq_walkEnd {t : ℕ} (v : G.V) (s : Fin t → G.D) :
    G.walkAt t v s t = G.walkEnd t v s := by
  rw [G.walkAt_eq_walkEnd_prefix v s t le_rfl]
  congr 1

/-! ### Self-loops -/

/-- A choice of self-loop at every vertex: an edge label that fixes the dart,
hence does not move. Dinur's construction needs these to pad short walks out to
a fixed length. -/
structure Loops (G : RegGraph) where
  /-- The self-loop label at each vertex. -/
  loop : G.V → G.D
  /-- The chosen dart is fixed by reversal, so it is a self-loop. -/
  rot_loop : ∀ v, G.rot (v, loop v) = (v, loop v)

namespace Loops

variable {G} (L : G.Loops)

/-- Following a loop label does not move. -/
@[simp] theorem nbr_loop (v : G.V) : G.nbr v (L.loop v) = v := by
  rw [nbr, L.rot_loop v]

/-- The length-`h` label tuple that follows `s` for `k` steps and then stays
put, taking self-loops. This is how a vertex within distance `k ≤ h` of `v` is
named by a walk of length exactly `h` out of `v`. -/
def padWalk {t : ℕ} (v : G.V) (s : Fin t → G.D) (k h : ℕ) : Fin h → G.D :=
  fun j => if hj : j.val < min k t then s ⟨j.val, lt_of_lt_of_le hj (min_le_right k t)⟩
    else L.loop (G.walkAt t v s k)

theorem padWalk_of_lt {t : ℕ} (v : G.V) (s : Fin t → G.D) {k h : ℕ} (j : Fin h)
    (hj : j.val < min k t) :
    L.padWalk v s k h j = s ⟨j.val, lt_of_lt_of_le hj (min_le_right k t)⟩ :=
  dite_eq_left hj

theorem padWalk_of_ge {t : ℕ} (v : G.V) (s : Fin t → G.D) {k h : ℕ} (j : Fin h)
    (hj : ¬ j.val < min k t) :
    L.padWalk v s k h j = L.loop (G.walkAt t v s k) :=
  dite_eq_right hj

/-- Below `k` the padded walk follows the original. -/
theorem walkAt_padWalk_of_le {t : ℕ} (v : G.V) (s : Fin t → G.D) {k h : ℕ}
    (hkh : k ≤ h) (hkt : k ≤ t) :
    ∀ m : ℕ, m ≤ k → G.walkAt h v (L.padWalk v s k h) m = G.walkAt t v s m := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
      intro hm
      have hmh : m < h := by omega
      have hmt : m < t := by omega
      have hmin : m < min k t := by omega
      rw [G.walkAt_succ_of_lt _ _ hmh, G.walkAt_succ_of_lt _ _ hmt, ih (by omega)]
      congr 1
      exact L.padWalk_of_lt v s ⟨m, hmh⟩ hmin

/-- At and past `k` the padded walk stays at the `k`-th vertex. -/
theorem walkAt_padWalk_of_ge {t : ℕ} (v : G.V) (s : Fin t → G.D) {k h : ℕ}
    (hkh : k ≤ h) (hkt : k ≤ t) :
    ∀ m : ℕ, k ≤ m → m ≤ h → G.walkAt h v (L.padWalk v s k h) m = G.walkAt t v s k := by
  intro m
  induction m with
  | zero =>
      intro hk _
      have : k = 0 := by omega
      subst this
      simp
  | succ m ih =>
      intro hkm hmh
      rcases Nat.lt_or_ge m k with hlt | hge
      · have hk : k = m + 1 := by omega
        subst hk
        exact L.walkAt_padWalk_of_le v s hkh hkt (m + 1) le_rfl
      · have hmh' : m < h := by omega
        rw [G.walkAt_succ_of_lt _ _ hmh', ih hge (by omega)]
        have hmin : ¬ (m < min k t) := by omega
        rw [L.padWalk_of_ge v s ⟨m, hmh'⟩ hmin, L.nbr_loop]

/-- **The naming property.** A padded walk of length `h` ends exactly at the
`k`-th vertex of the original walk. -/
theorem walkEnd_padWalk {t : ℕ} (v : G.V) (s : Fin t → G.D) {k h : ℕ}
    (hkh : k ≤ h) (hkt : k ≤ t) :
    G.walkEnd h v (L.padWalk v s k h) = G.walkAt t v s k := by
  rw [← G.walkAt_self_eq_walkEnd]
  exact L.walkAt_padWalk_of_ge v s hkh hkt h hkh le_rfl

end Loops

end RegGraph

end Complexity
