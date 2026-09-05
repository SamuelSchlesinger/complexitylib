/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.UnaryDivMod
public import Complexitylib.Classes.Containments.Internal.NLSearchAssemble

/-!
# Counting the clauses of an encoded formula

A formula's encoding is a stream of two-bit tokens, one of which marks the end
of a clause. Counting those tokens counts the clauses, and an algorithm that has
to loop over the clauses needs that count in unary.

The scan consumes two bits per step, so it is an iteration rather than a fold:
the state is the count so far paired with the unread suffix.

## Main definitions

- `Complexity.sepCount` — how many clause markers a bit string carries
- `Complexity.ccStep` — one two-bit step

## Main results

- `Complexity.ccStep_iterate` — the scan counts
- `Complexity.clauseCountFn_mem_FP`, `Complexity.clauseCountFn_eq` — counting is
  polynomial time
-/

@[expose] public section

namespace Complexity

/-- How many clause markers — the token `10` — a bit string carries. -/
def sepCount : List Bool → ℕ
  | true :: false :: r => sepCount r + 1
  | _ :: _ :: r => sepCount r
  | _ => 0

@[simp] theorem sepCount_nil : sepCount [] = 0 := rfl

theorem sepCount_cons₂ (b0 b1 : Bool) (r : List Bool) :
    sepCount (b0 :: b1 :: r) = if b0 = true ∧ b1 = false then sepCount r + 1 else sepCount r := by
  cases b0 <;> cases b1 <;> simp [sepCount]

theorem selectHead_cons (b : Bool) (t x y : List Bool) :
    Cobham.selectHead (b :: t) x y = if b then x else y := by
  cases b <;> simp [Cobham.selectHead]

/-- One step: read the next token, and count it if it marks a clause. The state
is `pair count unread`. -/
def ccStep (z : List Bool) : List Bool :=
  pair
    (Cobham.selectHead (emptyFlag (pairSnd z)) (pairFst z)
      (Cobham.selectHead (pairSnd z)
        (Cobham.selectHead (dropOne (pairSnd z)) (pairFst z)
          (true :: pairFst z))
        (pairFst z)))
    (dropOne (dropOne (pairSnd z)))

theorem ccStep_mem_FP : ccStep ∈ FP := by
  have hc : (fun z : List Bool => pairFst z) ∈ FP := Cobham.fstBlock_mem_FP
  have hs : (fun z : List Bool => pairSnd z) ∈ FP := Cobham.sndBlock_mem_FP
  have hd : (fun z : List Bool => dropOne (pairSnd z)) ∈ FP := dropOneFn_mem_FP hs
  refine Cobham.pairFn_mem_FP ?_ (dropOneFn_mem_FP hd)
  refine Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hs) hc ?_
  exact Cobham.selectHeadFn_mem_FP hs
    (Cobham.selectHeadFn_mem_FP hd hc (mem_FP_comp hc (Cobham.cons_mem_FP true))) hc

@[simp] theorem ccStep_nil (c : List Bool) : ccStep (pair c []) = pair c [] := by
  rw [ccStep, pairFst_pair, pairSnd_pair, emptyFlag_nil,
    selectHead_cons_true]
  rfl

theorem ccStep_cons₂ (c : List Bool) (b0 b1 : Bool) (r : List Bool) :
    ccStep (pair c (b0 :: b1 :: r))
      = pair (if b0 = true ∧ b1 = false then true :: c else c) r := by
  rw [ccStep, pairFst_pair, pairSnd_pair, emptyFlag_cons,
    selectHead_cons_false]
  cases b0
  · rw [selectHead_cons]
    simp [dropOne]
  · cases b1
    · rw [selectHead_cons]
      simp only [dropOne, List.drop_succ_cons, List.drop_zero, ite_eq_left]
      rw [selectHead_cons]
      simp
    · rw [selectHead_cons]
      simp only [dropOne, List.drop_succ_cons, List.drop_zero, ite_eq_left]
      rw [selectHead_cons]
      simp

theorem replicate_true_append_cons (n : ℕ) (c : List Bool) :
    List.replicate n true ++ true :: c = true :: (List.replicate n true ++ c) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

/-- **The scan counts.** -/
theorem ccStep_iterate : ∀ (k : ℕ) (c s : List Bool), s.length ≤ 2 * k → Even s.length →
    ccStep^[k] (pair c s) = pair (List.replicate (sepCount s) true ++ c) [] := by
  intro k
  induction k with
  | zero =>
      intro c s hs _
      have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      simp
  | succ k ih =>
      intro c s hs hev
      rw [Function.iterate_succ_apply]
      match s with
      | [] => rw [ccStep_nil, ih c [] (by simp) (by simp)]
      | [b] => exact absurd hev (by simp [Nat.even_add_one])
      | b0 :: b1 :: r =>
          rw [ccStep_cons₂]
          have hr : r.length ≤ 2 * k := by
            simp only [List.length_cons] at hs
            omega
          have hrev : Even r.length := by
            simp only [List.length_cons] at hev
            rcases hev with ⟨m, hm⟩
            exact ⟨m - 1, by omega⟩
          rw [ih _ r hr hrev, sepCount_cons₂]
          by_cases hcase : b0 = true ∧ b1 = false
          · rw [ite_eq_left hcase, ite_eq_left hcase, List.replicate_succ,
              List.cons_append, ← replicate_true_append_cons]
          · rw [ite_eq_right hcase, ite_eq_right hcase]

/-! ### The scan as one function -/

theorem ccStep_one (c s : List Bool) :
    ∃ X Y, ccStep (pair c s) = pair X Y
      ∧ X.length ≤ c.length + 1 ∧ Y.length ≤ s.length := by
  rw [ccStep, pairFst_pair, pairSnd_pair]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · refine le_trans (length_selectHead_le _ _ _) ?_
    simp only [max_le_iff]
    refine ⟨by omega, ?_⟩
    refine le_trans (length_selectHead_le _ _ _) ?_
    simp only [max_le_iff]
    refine ⟨?_, by omega⟩
    refine le_trans (length_selectHead_le _ _ _) ?_
    simp
  · rw [dropOne, dropOne, List.length_drop, List.length_drop]
    omega

theorem ccStep_shape : ∀ (k : ℕ) (c s : List Bool),
    ∃ c' s', ccStep^[k] (pair c s) = pair c' s'
      ∧ c'.length ≤ c.length + k ∧ s'.length ≤ s.length := by
  intro k
  induction k with
  | zero => intro c s; exact ⟨c, s, rfl, by omega, le_refl _⟩
  | succ k ih =>
      intro c s
      rw [Function.iterate_succ_apply]
      obtain ⟨X, Y, hXY, hX, hY⟩ := ccStep_one c s
      rw [hXY]
      obtain ⟨c', s', h1, h2, h3⟩ := ih X Y
      exact ⟨c', s', h1, by omega, by omega⟩

/-- **The clause count**, in unary. -/
noncomputable def clauseCountFn (z : List Bool) : List Bool :=
  pairFst (ccStep^[z.length] (pair [] z))

theorem clauseCountFn_mem_FP : clauseCountFn ∈ FP := by
  have hinit : (fun z : List Bool => pair [] z) ∈ FP :=
    mem_FP_pairWithInput (constFn_mem_FP [])
  have hwidth : (fun z : List Bool => polyRuler (Polynomial.C 3 * Polynomial.X
      + Polynomial.C 2) (id z)) ∈ FP :=
    polyRulerFn_mem_FP _ id_mem_FP
  have hbound : ∀ z : List Bool, ∀ k ≤ z.length,
      (ccStep^[k] (pair [] z)).length
        ≤ (polyRuler (Polynomial.C 3 * Polynomial.X + Polynomial.C 2) (id z)).length := by
    intro z k hk
    obtain ⟨c', s', h1, h2, h3⟩ := ccStep_shape k [] z
    rw [h1, pair_length, polyRuler_length]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, id]
    simp only [List.length_nil, Nat.zero_add] at h2
    omega
  have hiter := Cobham.iterate_mem_FP ccStep_mem_FP hinit id_mem_FP hwidth hbound
  have := mem_FP_comp hiter Cobham.fstBlock_mem_FP
  exact this

theorem clauseCountFn_eq {z : List Bool} (h : Even z.length) :
    clauseCountFn z = List.replicate (sepCount z) true := by
  rw [clauseCountFn, ccStep_iterate z.length [] z (by omega) h, pairFst_pair]
  simp

end Complexity
