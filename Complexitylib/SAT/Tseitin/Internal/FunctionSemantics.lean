/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.Tseitin.Defs

/-!
# Total-function semantics for Tseitin splitting

The public SAT semantics use finite Boolean lists, with out-of-range variables
defaulting to `false`. Fresh-variable arguments are simpler with total assignments
`ℕ → Bool`, since a fresh variable can be set with `Function.update` without changing
any earlier variable.

This internal module defines total-assignment evaluation for literals, clauses, and
CNFs. It relates that evaluation to the existing list semantics, proves the two
satisfiability notions equivalent, and records the congruence and update lemmas used
by the recursive Tseitin correctness proof.
-/

@[expose] public section

namespace Complexity

namespace SAT

/-- A total Boolean assignment, used internally while choosing fresh variables. -/
abbrev TotalAssignment := ℕ → Bool

namespace Lit

/-- Evaluate a literal under a total assignment. -/
@[inline] def evalTotal (α : TotalAssignment) (ℓ : Lit) : Bool :=
  α ℓ.var == ℓ.sign

/-- Total evaluation through the `Assignment.get` view of a finite assignment agrees
with the public list semantics. -/
@[simp] theorem evalTotal_get_internal (α : Assignment) (ℓ : Lit) :
    evalTotal α.get ℓ = eval α ℓ := rfl

/-- Negating a literal complements its value under a total assignment. -/
@[simp] theorem evalTotal_neg_internal (α : TotalAssignment) (ℓ : Lit) :
    evalTotal α ℓ.neg = !(evalTotal α ℓ) := by
  rcases ℓ with ⟨sign, var⟩
  cases hα : α var <;> cases sign <;> simp [evalTotal, neg, hα]

/-- A positive literal evaluates to the value of its variable. -/
@[simp] theorem evalTotal_pos_internal (α : TotalAssignment) (v : ℕ) :
    evalTotal α (pos v) = α v := by
  simp [evalTotal, pos]

/-- A negative literal evaluates to the complement of its variable. -/
@[simp] theorem evalTotal_negVar_internal (α : TotalAssignment) (v : ℕ) :
    evalTotal α (negVar v) = !(α v) := by
  cases hα : α v <;> simp [evalTotal, negVar, hα]

/-- A literal has the same value under assignments that agree at its variable. -/
theorem evalTotal_eq_of_agree_internal {α β : TotalAssignment} (ℓ : Lit)
    (h : α ℓ.var = β ℓ.var) :
    evalTotal α ℓ = evalTotal β ℓ := by
  simp only [evalTotal, h]

end Lit

namespace Clause

/-- Evaluate a clause under a total assignment. -/
@[inline] def evalTotal (α : TotalAssignment) (c : Clause) : Bool :=
  c.any (Lit.evalTotal α)

/-- Total evaluation through the `Assignment.get` view of a finite assignment agrees
with the public list semantics. -/
@[simp] theorem evalTotal_get_internal (α : Assignment) (c : Clause) :
    evalTotal α.get c = eval α c := rfl

/-- Clause evaluation is invariant when assignments agree on every occurring
variable. -/
theorem evalTotal_eq_of_agree_internal {α β : TotalAssignment} (c : Clause)
    (h : ∀ ℓ ∈ c, α ℓ.var = β ℓ.var) :
    evalTotal α c = evalTotal β c := by
  induction c with
  | nil => rfl
  | cons ℓ c ih =>
      simp only [evalTotal, List.any_cons]
      rw [Lit.evalTotal_eq_of_agree_internal ℓ (h ℓ List.mem_cons_self)]
      exact congrArg (fun value => Lit.evalTotal β ℓ || value)
        (ih (fun ℓ' hℓ' => h ℓ' (List.mem_cons_of_mem ℓ hℓ')))

end Clause

namespace CNF

/-- Evaluate a CNF under a total assignment. -/
@[inline] def evalTotal (α : TotalAssignment) (φ : CNF) : Bool :=
  φ.all (Clause.evalTotal α)

/-- A CNF is satisfiable by a total Boolean assignment. -/
def FunctionSatisfiable (φ : CNF) : Prop :=
  ∃ α : TotalAssignment, evalTotal α φ = true

/-- Total evaluation through the `Assignment.get` view of a finite assignment agrees
with the public list semantics. -/
@[simp] theorem evalTotal_get_internal (α : Assignment) (φ : CNF) :
    evalTotal α.get φ = eval α φ := rfl

/-- CNF evaluation is invariant when assignments agree on every occurring
variable. -/
theorem evalTotal_eq_of_agree_internal {α β : TotalAssignment} (φ : CNF)
    (h : ∀ c ∈ φ, ∀ ℓ ∈ c, α ℓ.var = β ℓ.var) :
    evalTotal α φ = evalTotal β φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      simp only [evalTotal, List.all_cons]
      rw [Clause.evalTotal_eq_of_agree_internal c (h c List.mem_cons_self)]
      exact congrArg (fun value => Clause.evalTotal β c && value)
        (ih (fun c' hc' => h c' (List.mem_cons_of_mem c hc')))

end CNF

namespace TotalAssignment

/-- Updating a total assignment sets the selected variable to the new value. -/
theorem update_same_internal (α : TotalAssignment) (i : ℕ) (b : Bool) :
    Function.update α i b i = b := by
  simp

/-- Updating one variable leaves every distinct variable unchanged. -/
theorem update_of_ne_internal (α : TotalAssignment) {fresh i : ℕ} (b : Bool)
    (h : fresh ≠ i) :
    Function.update α fresh b i = α i := by
  simp [Function.update, Ne.symm h]

/-- Updating a total assignment at `fresh` leaves every smaller variable unchanged. -/
theorem update_of_lt_internal (α : TotalAssignment) (fresh i : ℕ)
    (b : Bool) (h : i < fresh) :
    Function.update α fresh b i = α i := by
  apply update_of_ne_internal
  omega

end TotalAssignment

namespace Lit

/-- Updating a later variable preserves a literal's value. -/
theorem evalTotal_update_of_var_lt_internal (α : TotalAssignment) (fresh : ℕ)
    (b : Bool) (ℓ : Lit) (h : ℓ.var < fresh) :
    evalTotal (Function.update α fresh b) ℓ = evalTotal α ℓ := by
  apply evalTotal_eq_of_agree_internal
  exact TotalAssignment.update_of_lt_internal α fresh ℓ.var b h

end Lit

namespace Clause

/-- Updating a variable above a clause's maximum variable preserves its value. -/
theorem evalTotal_update_of_maxVar_lt_internal (α : TotalAssignment) (fresh : ℕ)
    (b : Bool) (c : Clause) (h : c.maxVar < fresh) :
    evalTotal (Function.update α fresh b) c = evalTotal α c := by
  apply evalTotal_eq_of_agree_internal
  intro ℓ hℓ
  exact TotalAssignment.update_of_lt_internal α fresh ℓ.var b
    (lt_of_le_of_lt (Clause.var_le_maxVar hℓ) h)

end Clause

namespace CNF

/-- Updating a variable above a CNF's maximum variable preserves its value. -/
theorem evalTotal_update_of_maxVar_lt_internal (α : TotalAssignment) (fresh : ℕ)
    (b : Bool) (φ : CNF) (h : φ.maxVar < fresh) :
    evalTotal (Function.update α fresh b) φ = evalTotal α φ := by
  apply evalTotal_eq_of_agree_internal
  intro c hc ℓ hℓ
  exact TotalAssignment.update_of_lt_internal α fresh ℓ.var b
    (lt_of_le_of_lt
      (le_trans (Clause.var_le_maxVar hℓ) (CNF.clause_maxVar_le_maxVar hc)) h)

/-- List satisfiability is equivalent to satisfiability by a total Boolean function. -/
theorem satisfiable_iff_functionSatisfiable_internal (φ : CNF) :
    φ.Satisfiable ↔ φ.FunctionSatisfiable := by
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨α.get, by simpa using hα⟩
  · rintro ⟨α, hα⟩
    let β := Assignment.ofFn (φ.maxVar + 1) α
    refine ⟨β, ?_⟩
    calc
      CNF.eval β φ = CNF.evalTotal β.get φ := by rw [CNF.evalTotal_get_internal]
      _ = CNF.evalTotal α φ := by
        apply CNF.evalTotal_eq_of_agree_internal
        intro c hc ℓ hℓ
        change (Assignment.ofFn (φ.maxVar + 1) α).get ℓ.var = α ℓ.var
        apply Assignment.ofFn_get
        have hvar := le_trans (Clause.var_le_maxVar hℓ)
          (CNF.clause_maxVar_le_maxVar hc)
        omega
      _ = true := hα

end CNF

end SAT

end Complexity
