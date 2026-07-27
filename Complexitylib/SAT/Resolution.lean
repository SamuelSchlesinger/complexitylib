/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.Semantics

/-!
# Resolution

The single resolution step on CNF clauses and its **soundness** (roadmap track
L5). The resolvent of `c₁` and `c₂` on a variable `v` drops the positive literal
`x_v` from `c₁` and the negative literal `¬x_v` from `c₂` and disjoins the
remainder. Soundness — any assignment satisfying both parents satisfies the
resolvent — is the semantic core underlying resolution proof systems.

## Main definitions and results

- `Clause.resolvent` — the resolvent of two clauses on a variable
- `Clause.resolvent_sound` — soundness of one resolution step
- `CNF.Derives` — the resolution proof system as an inductive derivation relation
- `CNF.refutation_sound` — **soundness of resolution**: a derivation of the empty
  clause proves the formula unsatisfiable
-/

@[expose] public section

namespace Complexity

namespace SAT

/-- The **resolvent** of clauses `c₁` and `c₂` on variable `v`: drop the positive
    literal `x_v` from `c₁` and the negative literal `¬x_v` from `c₂`, then take
    the disjunction of what remains. -/
def Clause.resolvent (c₁ c₂ : Clause) (v : ℕ) : Clause :=
  c₁.filter (· ≠ ⟨true, v⟩) ++ c₂.filter (· ≠ ⟨false, v⟩)

/-- **Soundness of one resolution step.** Any assignment satisfying both parent
    clauses satisfies their resolvent: whichever way the assignment sets `x_v`,
    the pivot literal it kills off in one parent forces a surviving literal there. -/
theorem Clause.resolvent_sound (α : Assignment) (c₁ c₂ : Clause) (v : ℕ)
    (h₁ : Clause.eval α c₁ = true) (h₂ : Clause.eval α c₂ = true) :
    Clause.eval α (Clause.resolvent c₁ c₂ v) = true := by
  simp only [Clause.eval] at h₁ h₂ ⊢
  simp only [Clause.resolvent, List.any_append, Bool.or_eq_true]
  rcases hv : α.get v with _ | _
  · -- α.get v = false: the positive pivot x_v is false, so a literal of c₁ survives.
    left
    rw [List.any_eq_true] at h₁ ⊢
    obtain ⟨ℓ, hmem, hval⟩ := h₁
    refine ⟨ℓ, ?_, hval⟩
    rw [List.mem_filter]
    refine ⟨hmem, ?_⟩
    simp only [decide_eq_true_eq]
    rintro rfl
    simp [Lit.eval, hv] at hval
  · -- α.get v = true: the negative pivot ¬x_v is false, so a literal of c₂ survives.
    right
    rw [List.any_eq_true] at h₂ ⊢
    obtain ⟨ℓ, hmem, hval⟩ := h₂
    refine ⟨ℓ, ?_, hval⟩
    rw [List.mem_filter]
    refine ⟨hmem, ?_⟩
    simp only [decide_eq_true_eq]
    rintro rfl
    simp [Lit.eval, hv] at hval

/-! ### Entailment and refutation soundness

A resolution refutation of a CNF `φ` derives the empty clause from `φ`'s clauses
by repeated resolution. The following three facts — axioms are entailed,
resolvents preserve entailment, and the empty clause is entailed only by an
unsatisfiable formula — are the semantic core: any such derivation of the empty
clause proves `φ` unsatisfiable. -/

/-- `φ` **entails** clause `c` when every satisfying assignment of `φ` satisfies
    `c`. -/
def CNF.Entails (φ : CNF) (c : Clause) : Prop :=
  ∀ α : Assignment, CNF.eval α φ = true → Clause.eval α c = true

/-- Every clause of `φ` is entailed by `φ` (resolution axioms are sound). -/
theorem CNF.entails_of_mem {φ : CNF} {c : Clause} (hc : c ∈ φ) : CNF.Entails φ c := by
  intro α hα
  rw [CNF.eval, List.all_eq_true] at hα
  exact hα c hc

/-- Resolution preserves entailment: if `φ` entails both parents, it entails the
    resolvent. -/
theorem CNF.entails_resolvent {φ : CNF} {c₁ c₂ : Clause} {v : ℕ}
    (h₁ : CNF.Entails φ c₁) (h₂ : CNF.Entails φ c₂) :
    CNF.Entails φ (Clause.resolvent c₁ c₂ v) :=
  fun α hα => Clause.resolvent_sound α c₁ c₂ v (h₁ α hα) (h₂ α hα)

/-- **Refutation soundness.** If `φ` entails the empty clause — as it does when
    the empty clause is derivable from `φ` by resolution — then `φ` is
    unsatisfiable (the empty clause is false under every assignment). -/
theorem CNF.not_satisfiable_of_entails_nil {φ : CNF} (h : CNF.Entails φ []) :
    ¬ CNF.Satisfiable φ := by
  rintro ⟨α, hα⟩
  have hnil := h α hα
  simp [Clause.eval] at hnil

/-- **Width bound for one resolution step.** The resolvent has at most as many
    literals as its two parents combined (dropping the pivot only shrinks each
    parent) — the basic width fact behind width-based resolution lower bounds. -/
theorem Clause.resolvent_length_le (c₁ c₂ : Clause) (v : ℕ) :
    (Clause.resolvent c₁ c₂ v).length ≤ c₁.length + c₂.length := by
  unfold Clause.resolvent
  rw [List.length_append]
  exact add_le_add (List.length_filter_le _ _) (List.length_filter_le _ _)

/-- Entailment is monotone under adding clauses: a stronger formula still entails
    everything the weaker one did. Lets a resolution derivation carry its axioms
    along as the clause set grows. -/
theorem CNF.entails_cons {φ : CNF} {c c' : Clause} (h : CNF.Entails φ c) :
    CNF.Entails (c' :: φ) c := by
  intro α hα
  rw [CNF.eval_cons, Bool.and_eq_true] at hα
  exact h α hα.2

/-! ### The resolution proof system

Packaging the resolution steps as a derivation relation makes a resolution
*proof* a first-class object: `CNF.Derives φ c` holds when `c` is derivable from
the clauses of `φ` by resolution. Its soundness (`entails_of_derives`) collapses
an entire derivation to a single entailment, and refuting via the empty clause
(`refutation_sound`) is then a certificate of unsatisfiability. -/

/-- The **resolution proof system**: `CNF.Derives φ c` holds when the clause `c`
    is derivable from the clauses of `φ` by resolution — either `c` is an axiom (a
    clause of `φ`) or it is the resolvent of two already-derived clauses. -/
inductive CNF.Derives (φ : CNF) : Clause → Prop
  /-- A clause of `φ` is derivable (an axiom). -/
  | axm {c : Clause} (hc : c ∈ φ) : CNF.Derives φ c
  /-- The resolvent of two derivable clauses is derivable. -/
  | res {c₁ c₂ : Clause} {v : ℕ} (h₁ : CNF.Derives φ c₁) (h₂ : CNF.Derives φ c₂) :
      CNF.Derives φ (Clause.resolvent c₁ c₂ v)

/-- **Soundness of resolution derivations.** Everything derivable from `φ` by
    resolution is entailed by `φ` — proved by induction on the derivation, using
    axiom soundness at the leaves and resolvent soundness at each step. -/
theorem CNF.entails_of_derives {φ : CNF} {c : Clause} (h : CNF.Derives φ c) :
    CNF.Entails φ c := by
  induction h with
  | axm hc => exact CNF.entails_of_mem hc
  | res _ _ ih₁ ih₂ => exact CNF.entails_resolvent ih₁ ih₂

/-- **Resolution refutation soundness.** A resolution derivation of the empty
    clause from `φ` proves that `φ` is unsatisfiable. This is the correctness of
    resolution as a refutation system. -/
theorem CNF.refutation_sound {φ : CNF} (h : CNF.Derives φ []) : ¬ CNF.Satisfiable φ :=
  CNF.not_satisfiable_of_entails_nil (CNF.entails_of_derives h)

/-- Derivations survive the addition of clauses: anything derivable from `φ` is
    derivable from any extension `c' :: φ`. (Weakening / monotonicity of the proof
    system.) -/
theorem CNF.derives_cons {φ : CNF} {c c' : Clause} (h : CNF.Derives φ c) :
    CNF.Derives (c' :: φ) c := by
  induction h with
  | axm hc => exact CNF.Derives.axm (List.mem_cons_of_mem _ hc)
  | res _ _ ih₁ ih₂ => exact CNF.Derives.res ih₁ ih₂

/-! ### The unit contradiction

The smallest resolution refutation: resolving the complementary unit clauses
`[x_v]` and `[¬x_v]` on `v` yields the empty clause in a single step. A formula
containing both is therefore refutable, hence unsatisfiable. -/

/-- Resolving the complementary unit clauses `[x_v]` and `[¬x_v]` on `v` yields the
    empty clause. -/
theorem Clause.resolvent_units_nil (v : ℕ) :
    Clause.resolvent [⟨true, v⟩] [⟨false, v⟩] v = [] := by
  simp [Clause.resolvent]

/-- A formula containing both unit clauses `[x_v]` and `[¬x_v]` refutes to the
    empty clause in one resolution step. -/
theorem CNF.derives_nil_of_units {φ : CNF} (v : ℕ)
    (h₁ : [⟨true, v⟩] ∈ φ) (h₂ : [⟨false, v⟩] ∈ φ) : CNF.Derives φ [] := by
  have h := CNF.Derives.res (CNF.Derives.axm h₁) (CNF.Derives.axm h₂) (v := v)
  rwa [Clause.resolvent_units_nil] at h

/-- **Complementary unit clauses are unsatisfiable.** Any formula containing both
    `[x_v]` and `[¬x_v]` is unsatisfiable, certified by the one-step resolution
    refutation. -/
theorem CNF.not_satisfiable_of_units {φ : CNF} (v : ℕ)
    (h₁ : [⟨true, v⟩] ∈ φ) (h₂ : [⟨false, v⟩] ∈ φ) : ¬ CNF.Satisfiable φ :=
  CNF.refutation_sound (CNF.derives_nil_of_units v h₁ h₂)

end SAT

end Complexity
