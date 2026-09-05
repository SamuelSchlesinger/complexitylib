/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.ExpanderMerge
public import Mathlib.Analysis.Real.Sqrt

/-!
# Merging at an arbitrary width

`ExpanderMerge` folds `N ≤ 3 n` vertices onto `n`. The zig-zag tower produces
sizes far more widely spaced than that, so the fold has to work at any width:
`N` vertices onto `n`, with `(m - 1) n ≤ N ≤ m n`.

What keeps the estimate under control at every width is that the fibres stay
balanced — `ExpanderMerge.card_liftN_none_le_one` — so however large `m` is,
each new vertex needs at most one padding loop.

This module carries the combinatorial layer: the rotation map and the graph.

## Main definitions

- `Complexity.RegGraph.mergeRotN` — the rotation map of the wide merge
- `Complexity.RegGraph.mergedN` — the merged graph

## Main results

- `Complexity.RegGraph.mergeRotN_involutive`
- `Complexity.RegGraph.order_mergedN`, `Complexity.RegGraph.deg_mergedN`
- `Complexity.RegGraph.step_mergedN` — the merged walk averages the `m` slots
- `Complexity.RegGraph.sq_step_mergedN_le` — and Jensen bounds its square
- `Complexity.RegGraph.sum_over_liftN` — the filled slots enumerate the old
  vertices
- `Complexity.RegGraph.sum_sq_termN_le` — the split into old steps and padding
- `Complexity.RegGraph.spectralBound_mergedN` — **the spectral bound at any
  width**
- `Complexity.mergeWidth` — a width that always works
-/

@[expose] public section

namespace Complexity

namespace RegGraph

variable {N d n m : ℕ}

/-- The new vertex an old one folds onto. -/
def projN (n : ℕ) (hn : 0 < n) (u : Fin N) : Fin n := ⟨u.val % n, Nat.mod_lt _ hn⟩

/-- Which slot of its fibre an old vertex occupies. -/
def slotN (n m : ℕ) (hN : N ≤ m * n) (u : Fin N) : Fin m :=
  ⟨u.val / n, by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have := u.isLt
      omega
    · have := u.isLt
      rw [Nat.div_lt_iff_lt_mul h0]
      omega⟩

theorem liftN_projN_slotN (hn : 0 < n) (hN : N ≤ m * n) (u : Fin N) :
    liftN N n (projN n hn u) (slotN n m hN u).val = some u := by
  rw [liftN, projN, slotN]
  have h : u.val % n + u.val / n * n = u.val := by
    rw [mul_comm]
    exact Nat.mod_add_div u.val n
  rw [dite_eq_left (by rw [h]; exact u.isLt)]
  congr 1
  exact Fin.ext h

theorem projN_liftN (hn : 0 < n) (v : Fin n) (i : ℕ) (u : Fin N)
    (h : liftN N n v i = some u) : projN n hn u = v := by
  rw [liftN] at h
  split_ifs at h with hlt
  · simp only [Option.some.injEq] at h
    rw [← h, projN]
    apply Fin.ext
    show (v.val + i * n) % n = v.val
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt v.isLt]

theorem slotN_liftN (hn : 0 < n) (hN : N ≤ m * n) (v : Fin n) (i : ℕ) (u : Fin N)
    (h : liftN N n v i = some u) : (slotN n m hN u).val = i := by
  rw [liftN] at h
  split_ifs at h with hlt
  · simp only [Option.some.injEq] at h
    rw [← h, slotN]
    show (v.val + i * n) / n = i
    rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt v.isLt, zero_add]

/-- The rotation map of the wide merge. -/
def mergeRotN (hn : 0 < n) (hN : N ≤ m * n) (rot : Fin N × Fin d → Fin N × Fin d)
    (x : Fin n × (Fin m × Fin d)) : Fin n × (Fin m × Fin d) :=
  match liftN N n x.1 x.2.1.val with
  | some u =>
      let y := rot (u, x.2.2)
      (projN n hn y.1, (slotN n m hN y.1, y.2))
  | none => x

theorem mergeRotN_involutive (hn : 0 < n) (hN : N ≤ m * n)
    (rot : Fin N × Fin d → Fin N × Fin d) (hrot : Function.Involutive rot) :
    Function.Involutive (mergeRotN hn hN rot) := by
  intro x
  obtain ⟨v, i, s⟩ := x
  simp only [mergeRotN]
  cases hl : liftN N n v i.val with
  | none => simp [hl]
  | some u =>
      simp only
      have hs : (slotN n m hN u).val = i.val := slotN_liftN hn hN v i.val u hl
      have hslot : slotN n m hN u = i := Fin.ext hs
      rw [liftN_projN_slotN hn hN]
      simp only
      rcases hrs : rot (u, s) with ⟨u', s'⟩
      have hy : rot (u', s') = (u, s) := by
        rw [← hrs]
        exact hrot (u, s)
      simp only [hy, Prod.mk.injEq]
      exact ⟨projN_liftN hn v i.val u hl, hslot, trivial⟩

/-- **The wide merge.** -/
def mergedN (hn : 0 < n) (hd : 0 < d) (hm : 0 < m) (hN : N ≤ m * n)
    (rot : Fin N × Fin d → Fin N × Fin d) (hrot : Function.Involutive rot) : RegGraph where
  V := Fin n
  D := Fin m × Fin d
  decEqV := inferInstance
  decEqD := inferInstance
  fintypeV := inferInstance
  fintypeD := inferInstance
  nonemptyD := ⟨(⟨0, hm⟩, ⟨0, hd⟩)⟩
  rot := mergeRotN hn hN rot
  rot_involutive := mergeRotN_involutive hn hN rot hrot

@[simp] theorem order_mergedN (hn : 0 < n) (hd : 0 < d) (hm : 0 < m) (hN : N ≤ m * n)
    (rot : Fin N × Fin d → Fin N × Fin d) (hrot : Function.Involutive rot) :
    (mergedN hn hd hm hN rot hrot).order = n := Fintype.card_fin n

@[simp] theorem deg_mergedN (hn : 0 < n) (hd : 0 < d) (hm : 0 < m) (hN : N ≤ m * n)
    (rot : Fin N × Fin d → Fin N × Fin d) (hrot : Function.Involutive rot) :
    (mergedN hn hd hm hN rot hrot).deg = m * d := by
  show Fintype.card (Fin m × Fin d) = m * d
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-! ### The walk of the wide merge -/

/-- A term of the merged step at `v`: the old step at the vertex in slot `i`, or
`f v` where the slot is empty. -/
noncomputable def termN (hn : 0 < n) (hd : 0 < d)
    (rot : Fin N × Fin d → Fin N × Fin d) (hrot : Function.Involutive rot)
    (f : Fin n → ℝ) (v : Fin n) (i : ℕ) : ℝ :=
  match liftN N n v i with
  | some u => (base hd rot hrot).step (fun w => f (projN n hn w)) u
  | none => f v

/-- **The merged walk is the average over the slots.** -/
theorem step_mergedN (hn : 0 < n) (hd : 0 < d) (hm : 0 < m) (hN : N ≤ m * n)
    (rot : Fin N × Fin d → Fin N × Fin d) (hrot : Function.Involutive rot)
    (f : Fin n → ℝ) (v : Fin n) :
    (mergedN hn hd hm hN rot hrot).step f v
      = (∑ i ∈ Finset.range m, termN hn hd rot hrot f v i) / (m : ℝ) := by
  have hd' : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    exact ne_of_gt this
  have hm' : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    exact ne_of_gt this
  have hdeg : ((mergedN hn hd hm hN rot hrot).deg : ℝ) = (m : ℝ) * (d : ℝ) := by
    rw [deg_mergedN]
    push_cast
    ring
  have hsum : (∑ x : (mergedN hn hd hm hN rot hrot).D,
        f ((mergedN hn hd hm hN rot hrot).nbr v x))
      = ∑ i : Fin m, ∑ s : Fin d, f ((mergeRotN hn hN rot (v, (i, s))).1) :=
    Fintype.sum_prod_type
      (f := fun x : Fin m × Fin d => f ((mergeRotN hn hN rot (v, x)).1))
  simp only [RegGraph.step]; rw [hdeg, hsum]
  have hinner : ∀ i : Fin m, ∑ s : Fin d, f ((mergeRotN hn hN rot (v, (i, s))).1)
      = (d : ℝ) * termN hn hd rot hrot f v i.val := by
    intro i
    rw [termN]
    simp only [mergeRotN]
    cases hl : liftN N n v i.val with
    | none =>
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    | some u =>
        simp only
        simp only [RegGraph.step]; rw [deg_ofRot]
        show _ = (d : ℝ) * ((∑ j : Fin d, f (projN n hn (rot (u, j)).1)) / (d : ℝ))
        field_simp
  rw [Finset.sum_congr rfl fun i _ => hinner i, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun i => termN hn hd rot hrot f v i) m]
  field_simp

/-- **Jensen**: the square of the average is at most the average of the
squares. -/
theorem sq_step_mergedN_le (hn : 0 < n) (hd : 0 < d) (hm : 0 < m) (hN : N ≤ m * n)
    (rot : Fin N × Fin d → Fin N × Fin d) (hrot : Function.Involutive rot)
    (f : Fin n → ℝ) (v : Fin n) :
    ((mergedN hn hd hm hN rot hrot).step f v) ^ 2
      ≤ (∑ i ∈ Finset.range m, (termN hn hd rot hrot f v i) ^ 2) / (m : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [step_mergedN, div_pow]
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.range m)
    (f := fun i => termN hn hd rot hrot f v i)
  rw [Finset.card_range] at h
  rw [div_le_div_iff₀ (by positivity) hm']
  nlinarith [h, hm']

/-! ### Summing over the slots -/

/-- **The filled slots are exactly the old vertices.** -/
theorem sum_over_liftN (hn : 0 < n) (hN : N ≤ m * n) (g : Fin N → ℝ) :
    ∑ p : Fin n × Fin m,
        (match liftN N n p.1 p.2.val with | some u => g u | none => 0)
      = ∑ u : Fin N, g u := by
  classical
  have hinj : Function.Injective fun u : Fin N => (projN n hn u, slotN n m hN u) := by
    intro u u' h
    have h1 := liftN_projN_slotN hn hN u
    have h2 := liftN_projN_slotN hn hN u'
    simp only [Prod.mk.injEq] at h
    rw [h.1, h.2, h2] at h1
    exact (Option.some.inj h1).symm
  symm
  calc ∑ u : Fin N, g u
      = ∑ u : Fin N, (match liftN N n (projN n hn u) (slotN n m hN u).val with
          | some u' => g u' | none => 0) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [liftN_projN_slotN hn hN]
    _ = ∑ p ∈ Finset.univ.image (fun u : Fin N => (projN n hn u, slotN n m hN u)),
          (match liftN N n p.1 p.2.val with | some u' => g u' | none => 0) := by
        rw [Finset.sum_image (fun u _ u' _ h => hinj h)]
    _ = ∑ p : Fin n × Fin m,
          (match liftN N n p.1 p.2.val with | some u' => g u' | none => 0) := by
        refine Finset.sum_subset (Finset.subset_univ _) fun p _ hp => ?_
        cases hl : liftN N n p.1 p.2.val with
        | none => rfl
        | some u =>
            exfalso
            apply hp
            rw [Finset.mem_image]
            refine ⟨u, Finset.mem_univ _, ?_⟩
            have h1 := projN_liftN hn p.1 p.2.val u hl
            have h2 := slotN_liftN hn hN p.1 p.2.val u hl
            exact Prod.ext h1 (Fin.ext h2)

/-- **Splitting the slot terms**: the old steps, plus at most one padding per
vertex — this is where balance of the fibres is used. -/
theorem sum_sq_termN_le (hn : 0 < n) (hd : 0 < d) (hN : N ≤ m * n)
    (hm1 : (m - 1) * n ≤ N) (rot : Fin N × Fin d → Fin N × Fin d)
    (hrot : Function.Involutive rot) (f : Fin n → ℝ) :
    ∑ v : Fin n, ∑ i : Fin m, (termN hn hd rot hrot f v i.val) ^ 2
      ≤ (∑ u : Fin N, ((base hd rot hrot).step (fun w => f (projN n hn w)) u) ^ 2)
        + ∑ v : Fin n, (f v) ^ 2 := by
  classical
  have hsplit : ∀ (v : Fin n) (i : Fin m), (termN hn hd rot hrot f v i.val) ^ 2
      = (match liftN N n v i.val with
          | some u => ((base hd rot hrot).step (fun w => f (projN n hn w)) u) ^ 2
          | none => 0)
        + (match liftN N n v i.val with | some _ => 0 | none => (f v) ^ 2) := by
    intro v i
    simp only [termN]
    cases liftN N n v i.val <;> simp
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [← Fintype.sum_prod_type', sum_over_liftN hn hN]
  refine add_le_add le_rfl (Finset.sum_le_sum fun v _ => ?_)
  -- at most one empty slot per vertex
  have hone : ∑ i : Fin m,
      (match liftN N n v i.val with | some _ => (0 : ℝ) | none => (f v) ^ 2)
      ≤ (f v) ^ 2 := by
    have hcard := card_liftN_none_le_one (N := N) (n := n) (m := m) hm1 v
    have hstep : ∑ i : Fin m,
        (match liftN N n v i.val with | some _ => (0 : ℝ) | none => (f v) ^ 2)
        = ∑ i ∈ (Finset.range m).filter fun i => liftN N n v i = none, (f v) ^ 2 := by
      have hconv : ∑ i : Fin m,
          (match liftN N n v i.val with | some _ => (0 : ℝ) | none => (f v) ^ 2)
          = ∑ i ∈ Finset.range m,
            (match liftN N n v i with | some _ => (0 : ℝ) | none => (f v) ^ 2) :=
        Fin.sum_univ_eq_sum_range
          (fun i => (match liftN N n v i with | some _ => (0 : ℝ) | none => (f v) ^ 2)) m
      rw [hconv, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      cases liftN N n v i <;> simp
    rw [hstep, Finset.sum_const, nsmul_eq_mul]
    have hc : ((((Finset.range m).filter fun i => liftN N n v i = none).card : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast hcard
    nlinarith [hc, sq_nonneg (f v)]
  exact hone

/-! ### The spectral bound at any width -/

/-- The wide projection is the one `ExpanderMerge` already used. -/
theorem projN_eq_proj (hn : 0 < n) : projN (N := N) n hn = proj n hn := rfl

theorem sum_sq_liftN_le (hn : 0 < n) (hN : N ≤ m * n) (f : Fin n → ℝ) :
    ∑ u : Fin N, (f (projN n hn u)) ^ 2 ≤ (m : ℝ) * ∑ v : Fin n, (f v) ^ 2 := by
  classical
  rw [← sum_over_liftN hn hN (fun u => (f (projN n hn u)) ^ 2), Fintype.sum_prod_type,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  have hterm : ∀ i : Fin m,
      (match liftN N n v i.val with | some u => (f (projN n hn u)) ^ 2 | none => 0)
      ≤ (f v) ^ 2 := by
    intro i
    cases hl : liftN N n v i.val with
    | none => show (0 : ℝ) ≤ (f v) ^ 2; exact sq_nonneg _
    | some u =>
        show (f (projN n hn u)) ^ 2 ≤ (f v) ^ 2
        rw [projN_liftN hn v i.val u hl]
  calc ∑ i : Fin m,
      (match liftN N n v i.val with | some u => (f (projN n hn u)) ^ 2 | none => 0)
      ≤ ∑ _i : Fin m, (f v) ^ 2 := Finset.sum_le_sum fun i _ => hterm i
    _ = (m : ℝ) * (f v) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The lift's total**, for a mean-zero `f`: only the last slot survives. -/
theorem sum_liftN_eq (hn : 0 < n) (hN : N ≤ m * n) (hm1 : (m - 1) * n ≤ N) (hm : 0 < m)
    (f : Fin n → ℝ) (hf : ∑ v : Fin n, f v = 0) :
    ∑ u : Fin N, f (projN n hn u)
      = ∑ v : Fin n, (match liftN N n v (m - 1) with | some _ => f v | none => 0) := by
  classical
  rw [← sum_over_liftN hn hN (fun u => f (projN n hn u)), Fintype.sum_prod_type]
  have hv : ∀ v : Fin n, ∑ i : Fin m,
      (match liftN N n v i.val with | some u => f (projN n hn u) | none => 0)
      = ((m : ℝ) - 1) * f v
        + (match liftN N n v (m - 1) with | some _ => f v | none => 0) := by
    intro v
    have hval : ∀ i : Fin m,
        (match liftN N n v i.val with | some u => f (projN n hn u) | none => 0)
        = (match liftN N n v i.val with | some _ => f v | none => 0) := by
      intro i
      cases hl : liftN N n v i.val with
      | none => rfl
      | some u =>
          show f (projN n hn u) = f v
          rw [projN_liftN hn v i.val u hl]
    rw [Finset.sum_congr rfl fun i _ => hval i]
    have hsplit : ∀ i : Fin m,
        (match liftN N n v i.val with | some _ => f v | none => 0)
        = f v - (match liftN N n v i.val with | some _ => 0 | none => f v) := by
      intro i
      cases liftN N n v i.val <;> simp
    rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnone : ∑ i : Fin m,
        (match liftN N n v i.val with | some _ => (0 : ℝ) | none => f v)
        = (match liftN N n v (m - 1) with | some _ => (0 : ℝ) | none => f v) := by
      have hconv : ∑ i : Fin m,
          (match liftN N n v i.val with | some _ => (0 : ℝ) | none => f v)
          = ∑ i ∈ Finset.range m,
            (match liftN N n v i with | some _ => (0 : ℝ) | none => f v) :=
        Fin.sum_univ_eq_sum_range
          (fun i => (match liftN N n v i with | some _ => (0 : ℝ) | none => f v)) m
      rw [hconv, Finset.sum_eq_single (m - 1)]
      · intro b hb hbne
        rw [Finset.mem_range] at hb
        have : b + 1 < m := by omega
        have hsome := liftN_isSome hm1 v this
        cases hl : liftN N n v b with
        | none => rw [hl] at hsome; exact absurd hsome (by simp)
        | some _ => rfl
      · intro hcon
        exact absurd (Finset.mem_range.2 (by omega)) hcon
    rw [hnone]
    cases liftN N n v (m - 1) <;> · simp; ring
  rw [Finset.sum_congr rfl fun v _ => hv v, Finset.sum_add_distrib, ← Finset.mul_sum, hf,
    mul_zero, zero_add]

/-- **The mean of the lift is small.** -/
theorem sq_sum_liftN_le (hn : 0 < n) (hN : N ≤ m * n) (hm1 : (m - 1) * n ≤ N) (hm : 0 < m)
    (f : Fin n → ℝ) (hf : ∑ v : Fin n, f v = 0) :
    (∑ u : Fin N, f (projN n hn u)) ^ 2 ≤ (n : ℝ) * ∑ v : Fin n, (f v) ^ 2 := by
  classical
  rw [sum_liftN_eq hn hN hm1 hm f hf]
  set Hv : Finset (Fin n) :=
    Finset.univ.filter fun v => (liftN N n v (m - 1)).isSome with hH
  have hsum : ∑ v : Fin n, (match liftN N n v (m - 1) with | some _ => f v | none => 0)
      = ∑ v ∈ Hv, f v := by
    rw [hH, Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    cases liftN N n v (m - 1) <;> simp
  rw [hsum]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Hv) (f := f)
  have hcard : (Hv.card : ℝ) ≤ (n : ℝ) := by
    have : Hv.card ≤ Fintype.card (Fin n) := Finset.card_le_univ Hv
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hsub : ∑ v ∈ Hv, (f v) ^ 2 ≤ ∑ v : Fin n, (f v) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun v _ _ => sq_nonneg _
  have h0 : 0 ≤ ∑ v ∈ Hv, (f v) ^ 2 := Finset.sum_nonneg fun v _ => sq_nonneg _
  calc (∑ v ∈ Hv, f v) ^ 2 ≤ Hv.card * ∑ v ∈ Hv, (f v) ^ 2 := hcs
    _ ≤ (n : ℝ) * ∑ v : Fin n, (f v) ^ 2 := by
        exact mul_le_mul hcard hsub h0 (by positivity)

/-- **The spectral bound of the wide merge.** The width enters only through the
`1 / m` terms, so the bound stays below one however far apart the sizes are. -/
theorem spectralBound_mergedN (hn : 0 < n) (hd : 0 < d) (hm : 0 < m) (hN : N ≤ m * n)
    (hm1 : (m - 1) * n ≤ N) (h2 : 2 * n ≤ N)
    (rot : Fin N × Fin d → Fin N × Fin d) (hrot : Function.Involutive rot)
    {lam : ℝ} (hlam : lam ^ 2 ≤ 1) (hspec : (base hd rot hrot).SpectralBound lam) :
    (mergedN hn hd hm hN rot hrot).SpectralBound
      (Real.sqrt (lam ^ 2 + (1 - lam ^ 2) / (2 * m) + 1 / m)) := by
  intro f hf
  have hN0 : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hl1 : 0 ≤ 1 - lam ^ 2 := by linarith
  have hl0 : 0 ≤ lam ^ 2 := sq_nonneg _
  have hsq : Real.sqrt (lam ^ 2 + (1 - lam ^ 2) / (2 * m) + 1 / m) ^ 2
      = lam ^ 2 + (1 - lam ^ 2) / (2 * m) + 1 / m :=
    Real.sq_sqrt (by positivity)
  rw [hsq]
  have hf' : ∑ v : Fin n, f v = 0 := hf
  have hS : 0 ≤ ∑ v : Fin n, (f v) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hjensen : ∑ v : Fin n, ((mergedN hn hd hm hN rot hrot).step f v) ^ 2
      ≤ (∑ v : Fin n, ∑ i ∈ Finset.range m, (termN hn hd rot hrot f v i) ^ 2) / (m : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun v _ => sq_step_mergedN_le hn hd hm hN rot hrot f v
  have hconv : ∀ v : Fin n, ∑ i ∈ Finset.range m, (termN hn hd rot hrot f v i) ^ 2
      = ∑ i : Fin m, (termN hn hd rot hrot f v i.val) ^ 2 := fun v =>
    (Fin.sum_univ_eq_sum_range (fun i => (termN hn hd rot hrot f v i) ^ 2) m).symm
  rw [Finset.sum_congr rfl fun v _ => hconv v] at hjensen
  have hterms := sum_sq_termN_le hn hd hN hm1 rot hrot f
  have hold := sum_sq_step_lift_le hn hd rot hrot hspec hN0 f
  rw [← projN_eq_proj hn] at hold
  have hlift := sum_sq_liftN_le hn hN f
  have hmean := sq_sum_liftN_le hn hN hm1 hm f hf'
  have hmeanN : (∑ u : Fin N, f (projN n hn u)) ^ 2 / (N : ℝ)
      ≤ (1 / 2) * ∑ v : Fin n, (f v) ^ 2 := by
    rw [div_le_iff₀ hN']
    have h2' : (2 : ℝ) * n ≤ N := by exact_mod_cast h2
    nlinarith [hmean, h2', hS]
  have hA := mul_le_mul_of_nonneg_left hlift hl0
  have hB := mul_le_mul_of_nonneg_left hmeanN hl1
  have hT : ∑ v : Fin n, ∑ i : Fin m, (termN hn hd rot hrot f v i.val) ^ 2
      ≤ (lam ^ 2 * (m : ℝ) + (1 - lam ^ 2) / 2 + 1) * ∑ v : Fin n, (f v) ^ 2 := by
    nlinarith [hterms, hold, hA, hB, hS]
  have hfin : (∑ v : Fin n, ∑ i : Fin m, (termN hn hd rot hrot f v i.val) ^ 2) / (m : ℝ)
      ≤ (lam ^ 2 + (1 - lam ^ 2) / (2 * m) + 1 / m) * ∑ v : Fin n, (f v) ^ 2 := by
    rw [div_le_iff₀ hm']
    have hexp : (lam ^ 2 + (1 - lam ^ 2) / (2 * m) + 1 / m)
        * (∑ v : Fin n, (f v) ^ 2) * (m : ℝ)
        = (lam ^ 2 * (m : ℝ) + (1 - lam ^ 2) / 2 + 1) * ∑ v : Fin n, (f v) ^ 2 := by
      field_simp
    rw [hexp]
    exact hT
  show ∑ v : Fin n, ((mergedN hn hd hm hN rot hrot).step f v) ^ 2 ≤ _
  exact le_trans hjensen hfin

/-! ### Choosing the width -/

/-- A width that always works for folding `N ≥ 2 n` vertices onto `n`. -/
def mergeWidth (N n : ℕ) : ℕ := N / n + 1

theorem le_mergeWidth_mul (N : ℕ) {n : ℕ} (hn : 0 < n) : N ≤ mergeWidth N n * n := by
  rw [mergeWidth]
  have h := Nat.div_add_mod N n
  have hlt := Nat.mod_lt N hn
  calc N = n * (N / n) + N % n := h.symm
    _ ≤ n * (N / n) + n := by omega
    _ = (N / n + 1) * n := by ring

theorem mergeWidth_sub_one_mul_le (N n : ℕ) : (mergeWidth N n - 1) * n ≤ N := by
  rw [mergeWidth, Nat.add_sub_cancel]
  exact Nat.div_mul_le_self N n

theorem three_le_mergeWidth {N n : ℕ} (hn : 0 < n) (h2 : 2 * n ≤ N) :
    3 ≤ mergeWidth N n := by
  rw [mergeWidth]
  have h : 2 ≤ N / n := (Nat.le_div_iff_mul_le hn).2 (by omega)
  omega

/-- The width is bounded whenever the overshoot is. -/
theorem mergeWidth_le {N n C : ℕ} (hn : 0 < n) (h : N ≤ C * n) :
    mergeWidth N n ≤ C + 1 := by
  rw [mergeWidth]
  have : N / n ≤ C := (Nat.div_le_iff_le_mul_add_pred hn).2 (by
    have : C * n = n * C := by ring
    omega)
  omega

end RegGraph

end Complexity
