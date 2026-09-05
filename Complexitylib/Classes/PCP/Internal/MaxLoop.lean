/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.UnaryDivMod
public import Complexitylib.Classes.PCP.Internal.PositionsFP

/-!
# The largest of polynomially many values

An algorithm reading a formula has to know how many variables it mentions, which
is the largest index any literal names. More generally: given a rule that
computes a value for each index, take the largest over a bounded range.

Values are carried in unary, so "largest" is "longest", and the comparison is
the length test already in the toolkit.

## Main definitions

- `Complexity.maxStep` — one step of the running maximum
- `Complexity.maxOver` — the value it computes

## Main results

- `Complexity.maxStep_iterate` — the loop takes the maximum
- `Complexity.maxFn_mem_FP`, `Complexity.maxFn_eq` — the packaged loop
- `Complexity.le_maxOver`, `Complexity.maxOver_attained` — it is the maximum
-/

@[expose] public section

namespace Complexity

/-- The largest of the first `n` values, as a length. -/
def maxOver (f : List Bool → List Bool) (z : List Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => max (maxOver f z n) (f (pair z (List.replicate n true))).length

/-- One step of the running maximum. The state is
`pair (pair largest counter) input`. -/
def maxStep (f : List Bool → List Bool) (st : List Bool) : List Bool :=
  pair
    (pair
      (Cobham.selectHead
        (Cobham.lenLeFlag (pairFst (pairFst st))
          (f (pair (pairSnd st) (pairSnd (pairFst st)))))
        (pairFst (pairFst st))
        (f (pair (pairSnd st) (pairSnd (pairFst st)))))
      (true :: pairSnd (pairFst st)))
    (pairSnd st)

theorem maxStep_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) : maxStep f ∈ FP := by
  have hm : (fun st : List Bool => pairFst (pairFst st)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP
  have hi : (fun st : List Bool => pairSnd (pairFst st)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hz : (fun st : List Bool => pairSnd st) ∈ FP := Cobham.sndBlock_mem_FP
  have hv : (fun st : List Bool =>
      f (pair (pairSnd st) (pairSnd (pairFst st)))) ∈ FP := by
    have := mem_FP_comp (Cobham.pairFn_mem_FP hz hi) hf
    exact this
  exact Cobham.pairFn_mem_FP
    (Cobham.pairFn_mem_FP
      (Cobham.selectHeadFn_mem_FP (lenLeFlagFn_mem_FP hm hv) hm hv)
      (mem_FP_comp hi (Cobham.cons_mem_FP true))) hz

/-- **The loop takes the maximum.** -/
theorem maxStep_iterate (f : List Bool → List Bool) (z : List Bool) : ∀ n : ℕ,
    ∃ M, (maxStep f)^[n] (pair (pair [] []) z)
        = pair (pair M (List.replicate n true)) z
      ∧ M.length = maxOver f z n := by
  intro n
  induction n with
  | zero => exact ⟨[], rfl, rfl⟩
  | succ n ih =>
      obtain ⟨M, hM, hlen⟩ := ih
      rw [Function.iterate_succ_apply', hM, maxStep, pairFst_pair,
        pairFst_pair, pairSnd_pair, pairSnd_pair]
      set v := f (pair z (List.replicate n true)) with hv
      rcases Cobham.lenLeFlag_flag M v with hf | hf
      · rw [hf, selectHead_cons_true]
        refine ⟨M, by rw [List.replicate_succ], ?_⟩
        rw [Cobham.lenLeFlag_eq_true_iff] at hf
        rw [maxOver, ← hlen, ← hv]
        omega
      · rw [hf, selectHead_cons_false]
        refine ⟨v, by rw [List.replicate_succ], ?_⟩
        have hgt : M.length < v.length := by
          by_contra hcon
          have : Cobham.lenLeFlag M v = [true] :=
            (Cobham.lenLeFlag_eq_true_iff M v).mpr (by omega)
          rw [hf] at this
          simp at this
        rw [maxOver, ← hlen, ← hv]
        omega

/-- Every value is at most the maximum. -/
theorem le_maxOver {f : List Bool → List Bool} {z : List Bool} :
    ∀ (n i : ℕ), i < n → (f (pair z (List.replicate i true))).length ≤ maxOver f z n := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
      intro i hi
      rw [maxOver]
      rcases Nat.lt_or_ge i n with h | h
      · exact le_trans (ih i h) (le_max_left _ _)
      · have : i = n := by omega
        subst this
        exact le_max_right _ _

/-- The maximum is attained, when there is anything to maximise over. -/
theorem maxOver_attained {f : List Bool → List Bool} {z : List Bool} :
    ∀ n : ℕ, 0 < n →
      ∃ i < n, (f (pair z (List.replicate i true))).length = maxOver f z n := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
      intro _
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        refine ⟨0, by omega, ?_⟩
        rw [maxOver, maxOver]
        simp
      · obtain ⟨i, hi, hval⟩ := ih hn
        rw [maxOver]
        rcases Nat.lt_or_ge (maxOver f z n) (f (pair z (List.replicate n true))).length with h | h
        · refine ⟨n, by omega, ?_⟩
          rw [max_eq_right (le_of_lt h)]
        · refine ⟨i, by omega, ?_⟩
          rw [hval, max_eq_left h]

theorem maxOver_le {f : List Bool → List Bool} {z : List Bool} {B : ℕ} :
    ∀ n, (∀ i < n, (f (pair z (List.replicate i true))).length ≤ B) → maxOver f z n ≤ B := by
  intro n
  induction n with
  | zero => intro _; simp [maxOver]
  | succ n ih =>
      intro h
      rw [maxOver, max_le_iff]
      exact ⟨ih fun i hi => h i (by omega), h n (by omega)⟩

/-- **The packaged loop**, on `pair (unary count) input`. -/
noncomputable def maxFn (f : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairFst (pairFst ((maxStep f)^[(pairFst w).length]
    (pair (pair [] []) (pairSnd w))))

theorem maxFn_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) : maxFn f ∈ FP := by
  obtain ⟨pf, hpf⟩ := Cobham.output_length_poly_of_mem_FP hf
  have hinit : (fun w : List Bool => pair (pair [] []) (pairSnd w)) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP _) Cobham.sndBlock_mem_FP
  set q : Polynomial ℕ :=
    Polynomial.C 4 * (pf.comp (Polynomial.C 3 * Polynomial.X + Polynomial.C 2))
      + Polynomial.C 3 * Polynomial.X + Polynomial.C 6 with hq
  have hwidth : (fun w : List Bool => polyRuler q (id w)) ∈ FP :=
    polyRulerFn_mem_FP q id_mem_FP
  have hbound : ∀ w : List Bool, ∀ k ≤ (pairFst w).length,
      ((maxStep f)^[k] (pair (pair [] []) (pairSnd w))).length
        ≤ (polyRuler q (id w)).length := by
    intro w k hk
    obtain ⟨M, hM, hlen⟩ := maxStep_iterate f (pairSnd w) k
    have hfw : (pairFst w).length ≤ w.length := fstBlock_length_le w
    have hzw : (pairSnd w).length ≤ w.length := sndBlock_length_le w
    have hMB : M.length ≤ pf.eval (3 * w.length + 2) := by
      rw [hlen]
      refine maxOver_le k fun i hi => ?_
      refine le_trans (hpf _) (polynomial_eval_mono_nat pf ?_)
      rw [pair_length, List.length_replicate]
      omega
    rw [hM, pair_length, pair_length, polyRuler_length, List.length_replicate, hq]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp, id]
    omega
  have hiter := Cobham.iterate_mem_FP (maxStep_mem_FP hf) hinit
    Cobham.fstBlock_mem_FP hwidth hbound
  have := mem_FP_comp (mem_FP_comp hiter Cobham.fstBlock_mem_FP) Cobham.fstBlock_mem_FP
  exact this

theorem maxFn_eq (f : List Bool → List Bool) {n : ℕ} {z : List Bool} :
    (maxFn f (pair (List.replicate n true) z)).length = maxOver f z n := by
  obtain ⟨M, hM, hlen⟩ := maxStep_iterate f z n
  rw [maxFn, pairFst_pair, pairSnd_pair, List.length_replicate, hM,
    pairFst_pair, pairFst_pair, hlen]

end Complexity
