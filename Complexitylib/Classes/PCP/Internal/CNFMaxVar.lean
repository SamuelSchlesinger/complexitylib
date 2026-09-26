/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.CNFTokens
public import Complexitylib.SAT.ThreeCNF
public import Complexitylib.Classes.PCP.Internal.MaxLoop

/-!
# The largest variable index, by slot

`CNF.maxVar` folds over clauses and then over literals. An algorithm instead
loops over a flat slot index and takes the largest value it sees. The two are
the same number, and this module says why: each bounds the family of variable
indices and each is attained by it.

## Main results

- `Complexity.var_le_maxVar` — every literal's index is at most `maxVar`
- `Complexity.exists_slot_eq_maxVar` — and some literal attains it
- `Complexity.maxOver_slotVar` — the loop computes `maxVar`
-/

@[expose] public section

namespace Complexity

open SAT

theorem clause_maxVar_le : ∀ (φ : CNF) {c : Clause}, c ∈ φ → c.maxVar ≤ φ.maxVar := by
  intro φ
  induction φ with
  | nil => intro c hc; simp at hc
  | cons c' cs ih =>
      intro c hc
      rw [CNF.maxVar]
      rcases List.mem_cons.mp hc with h | h
      · rw [h]
        exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

/-- Every literal's index is at most the formula's largest. -/
theorem var_le_maxVar (φ : CNF) {j : ℕ} (hj : j < φ.length) {p : ℕ}
    (hp : p < (φ[j]'hj).length) : ((φ[j]'hj)[p]'hp).var ≤ φ.maxVar :=
  le_trans (Clause.var_le_maxVar (List.getElem_mem hp))
    (clause_maxVar_le φ (List.getElem_mem hj))

/-- Some literal of a nonempty clause attains its largest index. -/
theorem exists_lit_eq_maxVar : ∀ (c : Clause), 0 < c.length →
    ∃ p, ∃ hp : p < c.length, ((c[p]'hp).var) = c.maxVar := by
  intro c
  induction c with
  | nil => intro h; simp at h
  | cons l ls ih =>
      intro _
      rcases Nat.eq_zero_or_pos ls.length with hz | hpos
      · have hnil : ls = [] := List.eq_nil_of_length_eq_zero hz
        subst hnil
        exact ⟨0, by simp, by simp⟩
      · obtain ⟨p, hp, hval⟩ := ih hpos
        rcases Nat.lt_or_ge (Clause.maxVar ls) l.var with h | h
        · refine ⟨0, by simp, ?_⟩
          rw [Clause.maxVar_cons, max_eq_left (le_of_lt h)]
          simp
        · refine ⟨p + 1, by simp; omega, ?_⟩
          rw [Clause.maxVar_cons, max_eq_right h, ← hval]
          simp

/-- Some clause of a nonempty formula attains its largest index. -/
theorem exists_clause_eq_maxVar : ∀ (φ : CNF), 0 < φ.length →
    ∃ j, ∃ hj : j < φ.length, (φ[j]'hj).maxVar = φ.maxVar := by
  intro φ
  induction φ with
  | nil => intro h; simp at h
  | cons c cs ih =>
      intro _
      rcases Nat.eq_zero_or_pos cs.length with hz | hpos
      · have hnil : cs = [] := List.eq_nil_of_length_eq_zero hz
        subst hnil
        exact ⟨0, by simp, by simp [CNF.maxVar]⟩
      · obtain ⟨j, hj, hval⟩ := ih hpos
        rcases Nat.lt_or_ge (CNF.maxVar cs) c.maxVar with h | h
        · refine ⟨0, by simp, ?_⟩
          rw [CNF.maxVar, max_eq_left (le_of_lt h)]
          simp
        · refine ⟨j + 1, by simp; omega, ?_⟩
          rw [CNF.maxVar, max_eq_right h, ← hval]
          simp

/-- **Some literal attains the formula's largest index.** -/
theorem exists_slot_eq_maxVar (φ : CNF) (h3 : CNF.Is3CNF φ) (h : 0 < φ.length) :
    ∃ j, ∃ hj : j < φ.length, ∃ p, ∃ hp : p < (φ[j]'hj).length,
      ((φ[j]'hj)[p]'hp).var = φ.maxVar := by
  obtain ⟨j, hj, hval⟩ := exists_clause_eq_maxVar φ h
  have hlen : (φ[j]'hj).length = 3 := h3 _ (List.getElem_mem hj)
  obtain ⟨p, hp, hval'⟩ := exists_lit_eq_maxVar (φ[j]'hj) (by omega)
  exact ⟨j, hj, p, hp, by rw [hval', hval]⟩

/-! ### The loop computes `maxVar` -/

/-- The variable index at a flat slot, read off the encoding. -/
noncomputable def slotVar (w : List Bool) : List Bool :=
  litVarFn (pair (pair (divFn [false, false, false] (pairSnd w))
    (modFn [false, false, false] (pairSnd w))) (pairFst w))

theorem slotVar_mem_FP : slotVar ∈ FP := by
  have hs : (fun w : List Bool => pairSnd w) ∈ FP := Cobham.sndBlock_mem_FP
  have hf : (fun w : List Bool => pairFst w) ∈ FP := Cobham.fstBlock_mem_FP
  have hd : (fun w : List Bool => divFn [false, false, false] (pairSnd w)) ∈ FP := by
    have := mem_FP_comp hs (divFn_mem_FP [false, false, false])
    refine mem_FP_of_eq this fun w => ?_
    rw [Function.comp_apply]
  have hm : (fun w : List Bool => modFn [false, false, false] (pairSnd w)) ∈ FP := by
    have := mem_FP_comp hs (modFn_mem_FP [false, false, false])
    refine mem_FP_of_eq this fun w => ?_
    rw [Function.comp_apply]
  have := mem_FP_comp (Cobham.pairFn_mem_FP (Cobham.pairFn_mem_FP hd hm) hf) litVarFn_mem_FP
  refine mem_FP_of_eq this fun w => ?_
  rw [Function.comp_apply, slotVar]

theorem slotVar_eq (φ : CNF) {i j p : ℕ} (hj : j < φ.length) (hp : p < (φ[j]'hj).length)
    (hdj : i / 3 = j) (hdp : i % 3 = p) :
    (slotVar (pair φ.encode (List.replicate i true))).length = ((φ[j]'hj)[p]'hp).var := by
  rw [slotVar, pairSnd_pair, pairFst_pair,
    divFn_eq (List.replicate i true), modFn_eq (List.replicate i true)]
  simp only [List.length_replicate,
    show ([false, false, false] : List Bool).length = 3 from rfl, hdj, hdp]
  rw [litVarFn_encode φ hj hp, List.length_replicate]

/-- **The loop computes `maxVar`.** -/
theorem maxOver_slotVar (φ : CNF) (h3 : CNF.Is3CNF φ) :
    maxOver slotVar φ.encode (3 * φ.length) = φ.maxVar := by
  rcases Nat.eq_zero_or_pos φ.length with hz | hpos
  · have hnil : φ = [] := List.eq_nil_of_length_eq_zero hz
    subst hnil
    simp [maxOver]
  · refine Nat.le_antisymm ?_ ?_
    · refine maxOver_le _ fun i hi => ?_
      have hj : i / 3 < φ.length := by omega
      have hp : i % 3 < (φ[i / 3]'hj).length := by
        rw [h3 _ (List.getElem_mem hj)]
        omega
      rw [slotVar_eq φ hj hp rfl rfl]
      exact var_le_maxVar φ _ _
    · obtain ⟨j, hj, p, hp, hval⟩ := exists_slot_eq_maxVar φ h3 hpos
      have hp3 : p < 3 := by
        rw [h3 _ (List.getElem_mem hj)] at hp
        exact hp
      have hi : 3 * j + p < 3 * φ.length := by omega
      have hdiv : (3 * j + p) / 3 = j := by omega
      have hmod : (3 * j + p) % 3 = p := by omega
      have hstep := le_maxOver (f := slotVar) (z := φ.encode) (3 * φ.length) (3 * j + p) hi
      rw [slotVar_eq φ hj hp hdiv hmod] at hstep
      rw [← hval]
      exact hstep

end Complexity
