/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.Tseitin.Defs

/-!
# Structural properties of Tseitin clause splitting

This internal module proves that the fresh-variable-threaded splitter produces
exact-width-three clauses, accounts exactly for its fresh counter, keeps every
generated variable below the first unused counter, and has linear structural
size in the source literal and clause counts.
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace CNF

/-- Exact-width-three shape is preserved by concatenating formulas. -/
theorem is3CNF_append_internal {φ ψ : CNF} (hφ : φ.Is3CNF) (hψ : ψ.Is3CNF) :
    (φ ++ ψ).Is3CNF := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hφ c hc
  · exact hψ c hc

end CNF

namespace Clause

/-- On a nonempty clause, the fresh count is exactly `length - 3`. -/
theorem tseitinFreshCount_eq_length_sub_three_internal {c : Clause} (hc : c ≠ []) :
    c.tseitinFreshCount = c.length - 3 := by
  simp [tseitinFreshCount, hc]

/-- One wide-clause split consumes one variable and leaves the remaining count
to the recursive suffix. -/
theorem tseitinFreshCount_wide_internal (next : ℕ) (a b c d : Lit) (rest : List Lit) :
    Clause.tseitinFreshCount (a :: b :: c :: d :: rest) =
      Clause.tseitinFreshCount (Lit.negVar next :: c :: d :: rest) + 1 := by
  simp [Clause.tseitinFreshCount]

/-- A clause never consumes more than one plus its number of literals. -/
theorem tseitinFreshCount_le_length_add_one_internal (c : Clause) :
    c.tseitinFreshCount ≤ c.length + 1 := by
  by_cases hc : c = []
  · subst c
    simp [tseitinFreshCount]
  · rw [tseitinFreshCount_eq_length_sub_three_internal hc]
    omega

/-- Every clause emitted by the single-clause splitter has exactly three literals. -/
theorem to3CNF_is3CNF_internal (next : ℕ) (c : Clause) :
    (c.to3CNF next).Is3CNF := by
  induction next, c using Clause.to3CNF.induct with
  | case1 next => simp [Clause.to3CNF, CNF.Is3CNF]
  | case2 next a => simp [Clause.to3CNF, CNF.Is3CNF]
  | case3 next a b => simp [Clause.to3CNF, CNF.Is3CNF]
  | case4 next a b c => simp [Clause.to3CNF, CNF.Is3CNF]
  | case5 next a b c d rest ih =>
      rw [Clause.to3CNF.eq_5, CNF.is3CNF_cons]
      exact ⟨rfl, ih⟩

/-- The splitter emits exactly one more clause than the number of fresh variables
that it consumes. -/
theorem length_to3CNF_internal (next : ℕ) (c : Clause) :
    (c.to3CNF next).length = c.tseitinFreshCount + 1 := by
  induction next, c using Clause.to3CNF.induct with
  | case1 next => simp [Clause.to3CNF, tseitinFreshCount]
  | case2 next a => simp [Clause.to3CNF, tseitinFreshCount]
  | case3 next a b => simp [Clause.to3CNF, tseitinFreshCount]
  | case4 next a b c => simp [Clause.to3CNF, tseitinFreshCount]
  | case5 next a b c d rest ih =>
      rw [Clause.to3CNF.eq_5, List.length_cons, ih,
        tseitinFreshCount_wide_internal next a b c d rest]

/-- Coarse clause-count bound for one split clause. -/
theorem length_to3CNF_le_internal (next : ℕ) (c : Clause) :
    (c.to3CNF next).length ≤ c.length + 2 := by
  rw [length_to3CNF_internal]
  exact Nat.add_le_add_right (tseitinFreshCount_le_length_add_one_internal c) 1

/-- Assuming all source variables precede `next`, every literal emitted for one
clause precedes the returned fresh counter. -/
theorem var_lt_of_mem_to3CNF_internal (next : ℕ) (c : Clause)
    : (∀ ℓ ∈ c, ℓ.var < next) → ∀ {out : Clause},
      out ∈ c.to3CNF next → ∀ {ℓ : Lit}, ℓ ∈ out →
        ℓ.var < next + c.tseitinFreshCount := by
  induction next, c using Clause.to3CNF.induct with
  | case1 next =>
      intro _ out hout ℓ hℓ
      simp only [Clause.to3CNF.eq_1, List.mem_cons, List.not_mem_nil,
        or_false] at hout
      rcases hout with rfl | rfl
      all_goals
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
        rcases hℓ with hℓ | hℓ | hℓ <;> subst ℓ <;>
          simp [tseitinFreshCount, Lit.pos, Lit.negVar]
  | case2 next a =>
      intro hsource out hout ℓ hℓ
      simp only [Clause.to3CNF.eq_2, List.mem_singleton] at hout
      subst out
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
      rcases hℓ with hℓ | hℓ | hℓ <;> subst ℓ
      all_goals
        simpa [tseitinFreshCount] using hsource a (by simp)
  | case3 next a b =>
      intro hsource out hout ℓ hℓ
      simp only [Clause.to3CNF.eq_3, List.mem_singleton] at hout
      subst out
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
      rcases hℓ with hℓ | hℓ | hℓ
      · subst ℓ
        simpa [tseitinFreshCount] using hsource a (by simp)
      · subst ℓ
        simpa [tseitinFreshCount] using hsource b (by simp)
      · subst ℓ
        simpa [tseitinFreshCount] using hsource b (by simp)
  | case4 next a b c =>
      intro hsource out hout ℓ hℓ
      simp only [Clause.to3CNF.eq_4, List.mem_singleton] at hout
      subst out
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
      rcases hℓ with hℓ | hℓ | hℓ
      · subst ℓ
        simpa [tseitinFreshCount] using hsource a (by simp)
      · subst ℓ
        simpa [tseitinFreshCount] using hsource b (by simp)
      · subst ℓ
        simpa [tseitinFreshCount] using hsource c (by simp)
  | case5 next a b c d rest ih =>
      intro hsource out hout ℓ hℓ
      rw [Clause.to3CNF.eq_5] at hout
      rcases List.mem_cons.mp hout with rfl | hout
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
        rcases hℓ with hℓ | hℓ | hℓ
        · subst ℓ
          have ha := hsource a (by simp)
          have hcount := tseitinFreshCount_wide_internal next a b c d rest
          omega
        · subst ℓ
          have hb := hsource b (by simp)
          have hcount := tseitinFreshCount_wide_internal next a b c d rest
          omega
        · subst ℓ
          simp only [Lit.pos]
          have hcount := tseitinFreshCount_wide_internal next a b c d rest
          omega
      · have hrecursive :
            ∀ ℓ ∈ Lit.negVar next :: c :: d :: rest, ℓ.var < next + 1 := by
          intro ℓ hmem
          rcases List.mem_cons.mp hmem with rfl | hmem
          · simp [Lit.negVar]
          · have hs := hsource ℓ (by simp only [List.mem_cons]; aesop)
            omega
        have hbound := ih hrecursive hout hℓ
        have hcount := tseitinFreshCount_wide_internal next a b c d rest
        omega

end Clause

namespace CNF

/-- Splitting every clause preserves exact-width-three shape. -/
theorem to3Aux_is3CNF_internal (next : ℕ) (φ : CNF) :
    (to3Aux next φ).1.Is3CNF := by
  induction φ generalizing next with
  | nil => simp [to3Aux]
  | cons c cs ih =>
      simp only [to3Aux]
      exact is3CNF_append_internal (Clause.to3CNF_is3CNF_internal next c)
        (ih (next + c.tseitinFreshCount))

/-- The top-level transformation produces exact 3-CNF. -/
theorem to3_is3CNF_internal (φ : CNF) : φ.to3.Is3CNF := by
  exact to3Aux_is3CNF_internal (φ.maxVar + 1) φ

/-- `to3Aux` returns exactly the first counter after all fresh variables. -/
theorem to3Aux_counter_internal (next : ℕ) (φ : CNF) :
    (to3Aux next φ).2 = next + φ.tseitinFreshCount := by
  induction φ generalizing next with
  | nil => simp [to3Aux, tseitinFreshCount]
  | cons c cs ih =>
      simp only [to3Aux]
      rw [ih]
      simp [tseitinFreshCount, Nat.add_assoc]

/-- Total fresh-variable use is bounded by source literals plus source clauses. -/
theorem tseitinFreshCount_le_literalCount_add_length_internal (φ : CNF) :
    φ.tseitinFreshCount ≤ φ.literalCount + φ.length := by
  induction φ with
  | nil => simp [tseitinFreshCount, literalCount]
  | cons c cs ih =>
      have hc := Clause.tseitinFreshCount_le_length_add_one_internal c
      change c.tseitinFreshCount + CNF.tseitinFreshCount cs ≤
        c.length + CNF.literalCount cs + (cs.length + 1)
      omega

/-- The output clause count is exactly fresh variables plus source clauses. -/
theorem length_to3Aux_internal (next : ℕ) (φ : CNF) :
    (to3Aux next φ).1.length = φ.tseitinFreshCount + φ.length := by
  induction φ generalizing next with
  | nil => simp [to3Aux, tseitinFreshCount]
  | cons c cs ih =>
      simp only [to3Aux, List.length_append]
      rw [Clause.length_to3CNF_internal, ih]
      simp [tseitinFreshCount]
      omega

/-- Coarse output clause-count bound in source literals and clauses. -/
theorem length_to3Aux_le_internal (next : ℕ) (φ : CNF) :
    (to3Aux next φ).1.length ≤ φ.literalCount + 2 * φ.length := by
  rw [length_to3Aux_internal]
  have h := tseitinFreshCount_le_literalCount_add_length_internal φ
  omega

/-- Exact 3-CNF has three literal occurrences per clause. -/
theorem literalCount_eq_three_mul_length_of_is3CNF_internal {φ : CNF}
    (hφ : φ.Is3CNF) : φ.literalCount = 3 * φ.length := by
  induction φ with
  | nil => simp [literalCount]
  | cons c cs ih =>
      have hc : c.length = 3 := hφ c List.mem_cons_self
      have hcs : CNF.Is3CNF cs := by
        intro d hd
        exact hφ d (List.mem_cons_of_mem c hd)
      change c.length + CNF.literalCount cs = 3 * (cs.length + 1)
      rw [hc, ih hcs]
      omega

/-- Exact literal count of the transformed formula. -/
theorem literalCount_to3Aux_internal (next : ℕ) (φ : CNF) :
    (to3Aux next φ).1.literalCount = 3 * (φ.tseitinFreshCount + φ.length) := by
  rw [literalCount_eq_three_mul_length_of_is3CNF_internal
    (to3Aux_is3CNF_internal next φ), length_to3Aux_internal]

/-- Coarse transformed literal-count bound used by the later encoded-size proof. -/
theorem literalCount_to3Aux_le_internal (next : ℕ) (φ : CNF) :
    (to3Aux next φ).1.literalCount ≤ 3 * (φ.literalCount + 2 * φ.length) := by
  rw [literalCount_to3Aux_internal]
  have h := tseitinFreshCount_le_literalCount_add_length_internal φ
  omega

/-- Assuming source variables precede `next`, every transformed literal precedes
the returned fresh counter. -/
theorem var_lt_of_mem_to3Aux_internal (next : ℕ) (φ : CNF)
    (hsource : ∀ c ∈ φ, ∀ ℓ ∈ c, ℓ.var < next) {out : Clause}
    (hout : out ∈ (to3Aux next φ).1) {ℓ : Lit} (hℓ : ℓ ∈ out) :
    ℓ.var < next + φ.tseitinFreshCount := by
  induction φ generalizing next out with
  | nil => simp [to3Aux] at hout
  | cons c cs ih =>
      simp only [to3Aux] at hout
      rcases List.mem_append.mp hout with hout | hout
      · have hbound := Clause.var_lt_of_mem_to3CNF_internal next c
          (hsource c List.mem_cons_self) hout hℓ
        change ℓ.var < next + (c.tseitinFreshCount + CNF.tseitinFreshCount cs)
        omega
      · have htailSource :
            ∀ d ∈ cs, ∀ l ∈ d, l.var < next + c.tseitinFreshCount := by
          intro d hd l hl
          have hs := hsource d (List.mem_cons_of_mem c hd) l hl
          omega
        have hbound := ih (next + c.tseitinFreshCount) htailSource hout hℓ
        change ℓ.var < next + (c.tseitinFreshCount + CNF.tseitinFreshCount cs)
        omega

/-- Every literal produced by `to3` lies below its final fresh counter. -/
theorem var_lt_of_mem_to3_internal (φ : CNF) {out : Clause} (hout : out ∈ φ.to3)
    {ℓ : Lit} (hℓ : ℓ ∈ out) :
    ℓ.var < φ.maxVar + 1 + φ.tseitinFreshCount := by
  apply var_lt_of_mem_to3Aux_internal (φ.maxVar + 1) φ ?_ hout hℓ
  intro c hc l hl
  have hlc := Clause.var_le_maxVar hl
  have hcφ := CNF.clause_maxVar_le_maxVar hc
  omega

end CNF

end SAT

end Complexity
