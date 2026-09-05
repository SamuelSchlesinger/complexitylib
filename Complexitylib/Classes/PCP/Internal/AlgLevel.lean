/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.TowerFin
public import Complexitylib.Classes.PCP.Internal.Materialize

/-!
# Finding the tower level

The expander family answers a request for `n` vertices with the first tower
member of at least `2 n` of them. An algorithm finds that member by counting: it
walks up the tower, multiplying the size by `deg ^ 4` at each level, and stops
at the first level large enough.

The walk is one step of a loop, so `Cobham.iterate_mem_FP` runs it; the state is
the level so far and the size so far, carried beside the requested count.

## Main definitions

- `Complexity.levelStep` — one tick of the search

## Main results

- `Complexity.levelStep_iterate` — what the loop has found after `j` ticks
- `Complexity.levelStep_mem_FP` — the tick is polynomial time
- `Complexity.levelAfter_of_lt`, `Complexity.levelAfter_stable` — the loop
  climbs until it is large enough, and then stays
- `Complexity.levelAfter_snd_le` — and never overshoots by more than a factor
- `Complexity.levelFn_mem_FP` — the search is polynomial time
- `Complexity.levelFn_length` — and finds the first level that is large enough
- `Complexity.pow_levelFn_le` — whatever level it reports, that level's size is
  polynomially bounded
-/

@[expose] public section

namespace Complexity

/-- The loop's own model: after `j` ticks, the level and the size reached. -/
def levelAfter (d n : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, p => p
  | j + 1, p =>
      let q := levelAfter d n j p
      if q.2 < 2 * n then (q.1 + 1, q.2 * d) else q

/-- One tick: if the size so far is below twice the request, take another
level. The state is `pair (pair (level so far) (size so far)) (the request)`. -/
noncomputable def levelStep (d : ℕ) (st : List Bool) : List Bool :=
  ifLtLen (pairSnd (pairFst st))
    (pairSnd st ++ pairSnd st)
    (pair (pair (pairFst (pairFst st) ++ [true])
      ((marks (mulC d (pairSnd (pairFst st)))).take
        (List.replicate d true ++ mulC (2 * d) (pairSnd st)).length))
      (pairSnd st))
    st

theorem levelStep_mem_FP (d : ℕ) : levelStep d ∈ FP := by
  have hk : (fun st : List Bool => pairFst (pairFst st)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP
  have hs : (fun st : List Bool => pairSnd (pairFst st)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hn : (fun st : List Bool => pairSnd st) ∈ FP := Cobham.sndBlock_mem_FP
  have hbound : (fun st : List Bool =>
      List.replicate d true ++ mulC (2 * d) (pairSnd st)) ∈ FP :=
    Cobham.appendFn_mem_FP (constFn_mem_FP (List.replicate d true)) (mulC_mem_FP hn (2 * d))
  have hadv : (fun st : List Bool =>
      pair (pair (pairFst (pairFst st) ++ [true])
        ((marks (mulC d (pairSnd (pairFst st)))).take
          (List.replicate d true ++ mulC (2 * d) (pairSnd st)).length))
        (pairSnd st)) ∈ FP :=
    Cobham.pairFn_mem_FP
      (Cobham.pairFn_mem_FP (Cobham.appendFn_mem_FP hk (constFn_mem_FP [true]))
        (Cobham.takeLenFn_mem_FP hbound (marks_mem_FP (mulC_mem_FP hs d)))) hn
  exact ifLtLen_mem_FP hs (Cobham.appendFn_mem_FP hn hn) hadv id_mem_FP

theorem levelStep_apply (d k s : ℕ) (Z : List Bool) :
    levelStep d (pair (pair (List.replicate k true) (List.replicate s true)) Z)
      = if s < 2 * Z.length then
          pair (pair (List.replicate (k + 1) true) (List.replicate (s * d) true)) Z
        else pair (pair (List.replicate k true) (List.replicate s true)) Z := by
  set n := Z.length with hn
  rw [levelStep, pairFst_pair, pairSnd_pair, pairFst_pair,
    pairSnd_pair]
  have hlen : (Z ++ Z).length = 2 * n := by
    simp only [List.length_append]
    omega
  by_cases h : s < 2 * n
  · rw [ite_eq_left h, ifLtLen_pos (by rw [List.length_replicate, hlen]; exact h),
      marks_eq, length_mulC, List.length_replicate, ← List.replicate_succ']
    congr 2
    refine List.take_of_length_le ?_
    rw [List.length_replicate, List.length_append, List.length_replicate, length_mulC, ← hn]
    nlinarith [h]
  · rw [ite_eq_right h, ifLtLen_neg (by rw [List.length_replicate, hlen]; exact h)]

/-- **The loop's model runs the loop.** -/
theorem levelStep_iterate (d : ℕ) (Z : List Bool) :
    ∀ (j k s : ℕ), (levelStep d)^[j]
        (pair (pair (List.replicate k true) (List.replicate s true)) Z)
      = pair (pair (List.replicate (levelAfter d Z.length j (k, s)).1 true)
          (List.replicate (levelAfter d Z.length j (k, s)).2 true)) Z := by
  intro j
  induction j with
  | zero => intro k s; rfl
  | succ j ih =>
      intro k s
      rw [Function.iterate_succ_apply', ih k s, levelStep_apply, levelAfter]
      by_cases h : (levelAfter d Z.length j (k, s)).2 < 2 * Z.length
      · rw [ite_eq_left h, ite_eq_left h]
      · rw [ite_eq_right h, ite_eq_right h]

/-! ### What the loop settles on -/

/-- Until it is large enough, the loop is at level `j` with size `d ^ (j + 1)`. -/
theorem levelAfter_of_lt (d n : ℕ) :
    ∀ j, (∀ i < j, ¬ (2 * n ≤ d ^ (i + 1))) → levelAfter d n j (0, d) = (j, d ^ (j + 1)) := by
  intro j
  induction j with
  | zero => intro _; simp [levelAfter]
  | succ j ih =>
      intro h
      have hj := ih fun i hi => h i (by omega)
      rw [levelAfter, hj]
      have hlt : d ^ (j + 1) < 2 * n := by
        have := h j (by omega)
        omega
      rw [ite_eq_left hlt]
      refine Prod.ext rfl ?_
      show d ^ j * d * d = d ^ (j + 1 + 1)
      rw [pow_succ, pow_succ]

/-- Once it is large enough, the loop stays put. -/
theorem levelAfter_stable (d n : ℕ) (p : ℕ × ℕ) (j : ℕ) (h : 2 * n ≤ (levelAfter d n j p).2) :
    ∀ i, levelAfter d n (j + i) p = levelAfter d n j p := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
      have hji : j + (i + 1) = (j + i) + 1 := by omega
      rw [hji, levelAfter, ih, ite_eq_right (by omega)]

/-- The loop never overshoots by more than a factor of `d`. -/
theorem levelAfter_snd_le (d n : ℕ) :
    ∀ j, (levelAfter d n j (0, d)).2 ≤ d + 2 * n * d := by
  intro j
  induction j with
  | zero => simp [levelAfter]
  | succ j ih =>
      rw [levelAfter]
      by_cases h : (levelAfter d n j (0, d)).2 < 2 * n
      · rw [ite_eq_left h]
        have : (levelAfter d n j (0, d)).2 * d ≤ 2 * n * d := Nat.mul_le_mul_right _ (by omega)
        simpa using by omega
      · rw [ite_eq_right h]
        exact ih

/-- The size the loop carries is always the power the level names. -/
theorem levelAfter_pow (d n : ℕ) :
    ∀ j, (levelAfter d n j (0, d)).2 = d ^ ((levelAfter d n j (0, d)).1 + 1) := by
  intro j
  induction j with
  | zero => simp [levelAfter]
  | succ j ih =>
      rw [levelAfter]
      by_cases h : (levelAfter d n j (0, d)).2 < 2 * n
      · rw [ite_eq_left h]
        show (levelAfter d n j (0, d)).2 * d = d ^ ((levelAfter d n j (0, d)).1 + 1 + 1)
        rw [ih]
        ring
      · rw [ite_eq_right h]
        exact ih

/-- **The level the loop reaches names a size below `d + 2 n d`.** -/
theorem pow_levelAfter_le (d n : ℕ) (j : ℕ) :
    d ^ ((levelAfter d n j (0, d)).1 + 1) ≤ d + 2 * n * d := by
  rw [← levelAfter_pow d n j]
  exact levelAfter_snd_le d n j

/-! ### The search as one function -/

/-- The shape of the state after `j` ticks: a level of at most `j` marks and a
size the clamp keeps below `d + 2 |z| d`, beside the request. -/
theorem levelStep_iterate_shape (d : ℕ) (z : List Bool) :
    ∀ j, ∃ K S : List Bool,
      (levelStep d)^[j] (pair (pair [] (List.replicate d true)) z) = pair (pair K S) z
        ∧ K.length ≤ j ∧ S.length ≤ d + 2 * z.length * d := by
  intro j
  induction j with
  | zero =>
      refine ⟨[], List.replicate d true, rfl, by simp, ?_⟩
      rw [List.length_replicate]
      omega
  | succ j ih =>
      obtain ⟨K, S, hst, hK, hS⟩ := ih
      rw [Function.iterate_succ_apply', hst, levelStep, pairFst_pair,
        pairSnd_pair, pairFst_pair, pairSnd_pair]
      by_cases h : S.length < (z ++ z).length
      · refine ⟨K ++ [true],
          (marks (mulC d S)).take (List.replicate d true ++ mulC (2 * d) z).length, ?_, ?_, ?_⟩
        · rw [ifLtLen_pos h]
        · rw [List.length_append, List.length_cons, List.length_nil]
          omega
        · rw [List.length_take, List.length_append, List.length_replicate, length_mulC,
            show d + z.length * (2 * d) = d + 2 * z.length * d from by ring]
          exact Nat.min_le_left _ _
      · exact ⟨K, S, by rw [ifLtLen_neg h], by omega, hS⟩

theorem levelStep_iterate_length_le (d : ℕ) (z : List Bool) (j : ℕ) :
    ((levelStep d)^[j] (pair (pair [] (List.replicate d true)) z)).length
      ≤ 2 * (2 * j + 2 + (d + 2 * z.length * d)) + 2 + z.length := by
  obtain ⟨K, S, hst, hK, hS⟩ := levelStep_iterate_shape d z j
  rw [hst, pair_length, pair_length]
  omega

/-- The polynomial that bounds the loop's state. -/
noncomputable def levelWidth (d : ℕ) (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 4 * p + Polynomial.C (2 * d + 6)
    + Polynomial.C (4 * d + 1) * Polynomial.X

/-- **The tower level for a requested count**, as one function: run the search
for polynomially many ticks and read off the level. -/
noncomputable def levelFn (d : ℕ) (p : Polynomial ℕ) (z : List Bool) : List Bool :=
  pairFst (pairFst
    ((levelStep d)^[(polyRuler p z).length] (pair (pair [] (List.replicate d true)) z)))

theorem levelFn_mem_FP (d : ℕ) (p : Polynomial ℕ) : levelFn d p ∈ FP := by
  have hinit : (fun z : List Bool => pair (pair [] (List.replicate d true)) z) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP (pair [] (List.replicate d true))) id_mem_FP
  have hruler : (fun z : List Bool => polyRuler p z) ∈ FP := polyRulerFn_mem_FP p id_mem_FP
  have hwidth : (fun z : List Bool => polyRuler (levelWidth d p) z) ∈ FP :=
    polyRulerFn_mem_FP _ id_mem_FP
  have hbound : ∀ z : List Bool, ∀ j ≤ (polyRuler p z).length,
      ((levelStep d)^[j] (pair (pair [] (List.replicate d true)) z)).length
        ≤ (polyRuler (levelWidth d p) z).length := by
    intro z j hj
    rw [polyRuler_length] at hj ⊢
    refine le_trans (levelStep_iterate_length_le d z j) ?_
    have heval : (levelWidth d p).eval z.length
        = 4 * p.eval z.length + (2 * d + 6) + (4 * d + 1) * z.length := by
      simp only [levelWidth, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
    rw [heval]
    nlinarith [hj]
  have hiter := Cobham.iterate_mem_FP (levelStep_mem_FP d) hinit hruler hwidth hbound
  have hproj := mem_FP_comp (mem_FP_comp hiter Cobham.fstBlock_mem_FP) Cobham.fstBlock_mem_FP
  exact mem_FP_of_eq hproj fun z => rfl

/-- The size at the level the search reports. -/
noncomputable def sizeFn (d : ℕ) (p : Polynomial ℕ) (z : List Bool) : List Bool :=
  pairSnd (pairFst
    ((levelStep d)^[(polyRuler p z).length] (pair (pair [] (List.replicate d true)) z)))

theorem sizeFn_mem_FP (d : ℕ) (p : Polynomial ℕ) : sizeFn d p ∈ FP := by
  have hinit : (fun z : List Bool => pair (pair [] (List.replicate d true)) z) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP (pair [] (List.replicate d true))) id_mem_FP
  have hruler : (fun z : List Bool => polyRuler p z) ∈ FP := polyRulerFn_mem_FP p id_mem_FP
  have hwidth : (fun z : List Bool => polyRuler (levelWidth d p) z) ∈ FP :=
    polyRulerFn_mem_FP _ id_mem_FP
  have hbound : ∀ z : List Bool, ∀ j ≤ (polyRuler p z).length,
      ((levelStep d)^[j] (pair (pair [] (List.replicate d true)) z)).length
        ≤ (polyRuler (levelWidth d p) z).length := by
    intro z j hj
    rw [polyRuler_length] at hj ⊢
    refine le_trans (levelStep_iterate_length_le d z j) ?_
    have heval : (levelWidth d p).eval z.length
        = 4 * p.eval z.length + (2 * d + 6) + (4 * d + 1) * z.length := by
      simp only [levelWidth, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
    rw [heval]
    nlinarith [hj]
  have hiter := Cobham.iterate_mem_FP (levelStep_mem_FP d) hinit hruler hwidth hbound
  have hproj := mem_FP_comp (mem_FP_comp hiter Cobham.fstBlock_mem_FP) Cobham.sndBlock_mem_FP
  exact mem_FP_of_eq hproj fun z => rfl

/-- **The size the search reports is the power its level names.** -/
theorem sizeFn_length (d : ℕ) (p : Polynomial ℕ) (z : List Bool) :
    (sizeFn d p z).length = d ^ ((levelFn d p z).length + 1) := by
  have hinit : (pair ([] : List Bool) (List.replicate d true))
      = pair (List.replicate 0 true) (List.replicate d true) := rfl
  rw [sizeFn, levelFn, hinit, levelStep_iterate d z _ 0 d, pairFst_pair,
    pairFst_pair, pairSnd_pair, List.length_replicate, List.length_replicate]
  exact levelAfter_pow d z.length _

/-- **The search finds the first level that is large enough.** -/
theorem levelFn_length (d : ℕ) (p : Polynomial ℕ) (z : List Bool) (L : ℕ)
    (hL : 2 * z.length ≤ d ^ (L + 1)) (hmin : ∀ i < L, ¬ (2 * z.length ≤ d ^ (i + 1)))
    (hp : L ≤ p.eval z.length) :
    (levelFn d p z).length = L := by
  have hinit : (pair ([] : List Bool) (List.replicate d true))
      = pair (List.replicate 0 true) (List.replicate d true) := rfl
  have hL' : levelAfter d z.length L (0, d) = (L, d ^ (L + 1)) := levelAfter_of_lt d z.length L hmin
  have hstable : ∀ i, levelAfter d z.length (L + i) (0, d) = (L, d ^ (L + 1)) := by
    intro i
    rw [levelAfter_stable d z.length (0, d) L (by rw [hL']; exact hL) i, hL']
  obtain ⟨i, hi⟩ : ∃ i, p.eval z.length = L + i := ⟨p.eval z.length - L, by omega⟩
  rw [levelFn, hinit, polyRuler_length, hi, levelStep_iterate d z (L + i) 0 d, hstable i,
    pairFst_pair, pairFst_pair, List.length_replicate]

/-- **Whatever level the search reports, its size is bounded** — which is what
lets the table at that level be written down. -/
theorem pow_levelFn_le (d : ℕ) (p : Polynomial ℕ) (z : List Bool) :
    d ^ ((levelFn d p z).length + 1) ≤ d + 2 * z.length * d := by
  have hinit : (pair ([] : List Bool) (List.replicate d true))
      = pair (List.replicate 0 true) (List.replicate d true) := rfl
  have hlen : (levelFn d p z).length
      = (levelAfter d z.length (polyRuler p z).length (0, d)).1 := by
    rw [levelFn, hinit, levelStep_iterate d z _ 0 d, pairFst_pair,
      pairFst_pair, List.length_replicate]
  rw [hlen]
  exact pow_levelAfter_le d z.length _

end Complexity
