/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.Tseitin.Internal.FunctionSemantics
public import Complexitylib.SAT.Tseitin.Internal.Shape

/-!
# Correctness of Tseitin clause splitting

The backward direction holds under every total assignment: the emitted chain
logically implies its source clause. For the forward direction, fresh variables
are chosen recursively while preserving all earlier variable values. The CNF
proof threads those extensions across disjoint fresh ranges.
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace CNF

/-- Total-assignment evaluation distributes over CNF concatenation. -/
private theorem evalTotal_append (α : TotalAssignment) (φ ψ : CNF) :
    evalTotal α (φ ++ ψ) = (evalTotal α φ && evalTotal α ψ) := by
  simp [evalTotal, List.all_append]

end CNF

namespace Clause

/-- Every assignment satisfying a split clause chain satisfies the original
clause, independently of freshness. -/
theorem evalTotal_to3CNF_sound_internal (α : TotalAssignment) (next : ℕ)
    (c : Clause) (h : CNF.evalTotal α (c.to3CNF next) = true) :
    Clause.evalTotal α c = true := by
  induction next, c using Clause.to3CNF.induct with
  | case1 next =>
      simp [Clause.to3CNF, CNF.evalTotal, Clause.evalTotal] at h
  | case2 next a =>
      simpa [Clause.to3CNF, CNF.evalTotal, Clause.evalTotal] using h
  | case3 next a b =>
      simpa [Clause.to3CNF, CNF.evalTotal, Clause.evalTotal] using h
  | case4 next a b c =>
      simpa [Clause.to3CNF, CNF.evalTotal, Clause.evalTotal] using h
  | case5 next a b c d rest ih =>
      rw [Clause.to3CNF.eq_5] at h
      simp only [CNF.evalTotal, List.all_cons, Bool.and_eq_true] at h
      obtain ⟨hhead, htail⟩ := h
      have hrec := ih htail
      simp only [Clause.evalTotal, List.any_cons, List.any_nil,
        Bool.or_false, Lit.evalTotal_pos_internal,
        Lit.evalTotal_negVar_internal] at hhead hrec ⊢
      cases ha : Lit.evalTotal α a <;>
        cases hb : Lit.evalTotal α b <;>
        cases hz : α next <;> simp_all

/-- If every source variable precedes `next`, a satisfying assignment for one
source clause extends to a satisfying assignment for its exact-3 split while
preserving every variable below `next`. -/
theorem exists_evalTotal_to3CNF_internal (next : ℕ) (c : Clause)
    (α : TotalAssignment) (hsource : ∀ ℓ ∈ c, ℓ.var < next)
    (h : Clause.evalTotal α c = true) :
    ∃ β : TotalAssignment,
      (∀ v, v < next → β v = α v) ∧
      CNF.evalTotal β (c.to3CNF next) = true := by
  induction next, c using Clause.to3CNF.induct generalizing α with
  | case1 next =>
      simp [Clause.evalTotal] at h
  | case2 next a =>
      refine ⟨α, fun _ _ => rfl, ?_⟩
      simpa [Clause.to3CNF, CNF.evalTotal, Clause.evalTotal] using h
  | case3 next a b =>
      refine ⟨α, fun _ _ => rfl, ?_⟩
      simpa [Clause.to3CNF, CNF.evalTotal, Clause.evalTotal] using h
  | case4 next a b c =>
      refine ⟨α, fun _ _ => rfl, ?_⟩
      simpa [Clause.to3CNF, CNF.evalTotal, Clause.evalTotal] using h
  | case5 next a b c d rest ih =>
      let y : Bool := !(Lit.evalTotal α a || Lit.evalTotal α b)
      let α₁ : TotalAssignment := Function.update α next y
      have hrecursiveSource :
          Clause.evalTotal α₁ (Lit.negVar next :: c :: d :: rest) = true := by
        rw [show Clause.evalTotal α₁ (Lit.negVar next :: c :: d :: rest) =
          (!(α₁ next) || Clause.evalTotal α₁ (c :: d :: rest)) by
            simp [Clause.evalTotal]]
        have hnext : α₁ next = y := by
          exact TotalAssignment.update_same_internal α next y
        rw [hnext]
        simp only [y]
        have hcSource : ∀ ℓ ∈ c :: d :: rest, ℓ.var < next := by
          intro ℓ hℓ
          exact hsource ℓ (by simp only [List.mem_cons]; aesop)
        have hrestEval : Clause.evalTotal α₁ (c :: d :: rest) =
            Clause.evalTotal α (c :: d :: rest) := by
          apply Clause.evalTotal_eq_of_agree_internal
          intro ℓ hℓ
          exact TotalAssignment.update_of_lt_internal α next ℓ.var y
            (hcSource ℓ hℓ)
        rw [hrestEval]
        change (Lit.evalTotal α a ||
          (Lit.evalTotal α b || Clause.evalTotal α (c :: d :: rest))) = true at h
        cases ha : Lit.evalTotal α a <;>
          cases hb : Lit.evalTotal α b <;> simp_all
      have hrecursiveVars :
          ∀ ℓ ∈ Lit.negVar next :: c :: d :: rest, ℓ.var < next + 1 := by
        intro ℓ hℓ
        rcases List.mem_cons.mp hℓ with rfl | hℓ
        · simp [Lit.negVar]
        · have := hsource ℓ (by simp only [List.mem_cons]; aesop)
          omega
      obtain ⟨β, hβ, htail⟩ := ih α₁ hrecursiveVars hrecursiveSource
      refine ⟨β, ?_, ?_⟩
      · intro v hv
        rw [hβ v (by omega)]
        exact TotalAssignment.update_of_lt_internal α next v y hv
      · rw [Clause.to3CNF.eq_5]
        simp only [CNF.evalTotal, List.all_cons, Bool.and_eq_true]
        refine ⟨?_, htail⟩
        simp only [Clause.evalTotal, List.any_cons, List.any_nil,
          Bool.or_false, Lit.evalTotal_pos_internal]
        have haVar := hsource a (by simp)
        have hbVar := hsource b (by simp)
        have hβa : β a.var = α a.var := by
          rw [hβ a.var (by omega)]
          exact TotalAssignment.update_of_lt_internal α next a.var y haVar
        have hβb : β b.var = α b.var := by
          rw [hβ b.var (by omega)]
          exact TotalAssignment.update_of_lt_internal α next b.var y hbVar
        have hβnext : β next = y := by
          rw [hβ next (by omega)]
          exact TotalAssignment.update_same_internal α next y
        rw [Lit.evalTotal_eq_of_agree_internal a hβa,
          Lit.evalTotal_eq_of_agree_internal b hβb, hβnext]
        simp only [y]
        cases Lit.evalTotal α a <;> cases Lit.evalTotal α b <;> rfl

end Clause

namespace CNF

/-- A satisfying assignment for a transformed CNF satisfies the source CNF. -/
theorem evalTotal_to3Aux_sound_internal (α : TotalAssignment) (next : ℕ)
    (φ : CNF) (h : evalTotal α (to3Aux next φ).1 = true) :
    evalTotal α φ = true := by
  induction φ generalizing next with
  | nil => rfl
  | cons c cs ih =>
      simp only [to3Aux] at h
      rw [evalTotal_append, Bool.and_eq_true] at h
      obtain ⟨hc, hcs⟩ := h
      have hc' := Clause.evalTotal_to3CNF_sound_internal α next c hc
      have hcs' := ih (next + c.tseitinFreshCount) hcs
      simpa [evalTotal] using And.intro hc' hcs'

/-- A satisfying assignment for a source CNF extends across all fresh ranges
to satisfy the transformed CNF, preserving every variable below `next`. -/
theorem exists_evalTotal_to3Aux_internal (next : ℕ) (φ : CNF)
    (α : TotalAssignment)
    (hsource : ∀ c ∈ φ, ∀ ℓ ∈ c, ℓ.var < next)
    (h : evalTotal α φ = true) :
    ∃ β : TotalAssignment,
      (∀ v, v < next → β v = α v) ∧
      evalTotal β (to3Aux next φ).1 = true := by
  induction φ generalizing next α with
  | nil => exact ⟨α, fun _ _ => rfl, rfl⟩
  | cons c cs ih =>
      simp only [evalTotal, List.all_cons, Bool.and_eq_true] at h
      obtain ⟨hc, hcs⟩ := h
      obtain ⟨β, hβα, hβc⟩ := Clause.exists_evalTotal_to3CNF_internal
        next c α (hsource c List.mem_cons_self) hc
      have hcsβ : evalTotal β cs = true := by
        rw [evalTotal_eq_of_agree_internal (α := β) (β := α) cs]
        · exact hcs
        · intro d hd ℓ hℓ
          exact hβα ℓ.var (hsource d (List.mem_cons_of_mem c hd) ℓ hℓ)
      have htailVars :
          ∀ d ∈ cs, ∀ ℓ ∈ d, ℓ.var < next + c.tseitinFreshCount := by
        intro d hd ℓ hℓ
        have := hsource d (List.mem_cons_of_mem c hd) ℓ hℓ
        omega
      obtain ⟨γ, hγβ, hγtail⟩ := ih
        (next + c.tseitinFreshCount) β htailVars hcsβ
      refine ⟨γ, ?_, ?_⟩
      · intro v hv
        rw [hγβ v (by omega), hβα v hv]
      · simp only [to3Aux]
        rw [evalTotal_append, Bool.and_eq_true]
        refine ⟨?_, hγtail⟩
        rw [evalTotal_eq_of_agree_internal (α := γ) (β := β)
          (c.to3CNF next)]
        · exact hβc
        · intro out hout ℓ hℓ
          apply hγβ ℓ.var
          exact Clause.var_lt_of_mem_to3CNF_internal next c
            (hsource c List.mem_cons_self) hout hℓ

/-- Function-valued satisfiability is preserved and reflected by `to3Aux`
whenever its initial counter is fresh for every source variable. -/
theorem functionSatisfiable_to3Aux_iff_internal (next : ℕ) (φ : CNF)
    (hsource : ∀ c ∈ φ, ∀ ℓ ∈ c, ℓ.var < next) :
    (to3Aux next φ).1.FunctionSatisfiable ↔ φ.FunctionSatisfiable := by
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨α, evalTotal_to3Aux_sound_internal α next φ hα⟩
  · rintro ⟨α, hα⟩
    obtain ⟨β, _hβ, hout⟩ := exists_evalTotal_to3Aux_internal
      next φ α hsource hα
    exact ⟨β, hout⟩

/-- Existing finite-list satisfiability is preserved and reflected by `to3Aux`
whenever its initial counter is fresh for every source variable. -/
theorem satisfiable_to3Aux_iff_internal (next : ℕ) (φ : CNF)
    (hsource : ∀ c ∈ φ, ∀ ℓ ∈ c, ℓ.var < next) :
    (to3Aux next φ).1.Satisfiable ↔ φ.Satisfiable := by
  rw [satisfiable_iff_functionSatisfiable_internal,
    satisfiable_iff_functionSatisfiable_internal,
    functionSatisfiable_to3Aux_iff_internal next φ hsource]

/-- Function-valued satisfiability is preserved and reflected by `to3`. -/
theorem functionSatisfiable_to3_iff_internal (φ : CNF) :
    φ.to3.FunctionSatisfiable ↔ φ.FunctionSatisfiable := by
  apply functionSatisfiable_to3Aux_iff_internal
  intro c hc ℓ hℓ
  have hclause := CNF.clause_maxVar_le_maxVar hc
  have hlit := Clause.var_le_maxVar hℓ
  omega

/-- Existing finite-list satisfiability is preserved and reflected by `to3`. -/
theorem satisfiable_to3_iff_internal (φ : CNF) :
    φ.to3.Satisfiable ↔ φ.Satisfiable := by
  apply satisfiable_to3Aux_iff_internal
  intro c hc ℓ hℓ
  have hclause := CNF.clause_maxVar_le_maxVar hc
  have hlit := Clause.var_le_maxVar hℓ
  omega

end CNF

end SAT

end Complexity
