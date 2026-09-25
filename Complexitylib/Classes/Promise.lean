/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Promise.Defs
public import Complexitylib.Classes.Promise.Internal

/-!
# Promise problems and promise complexity classes

This module exposes disjoint yes/no promise problems, semantic Boolean solvers,
side-preserving maps, polynomial-time many-one reductions, complements, and the
total embedding of ordinary languages. `PromiseClass` lifts an ordinary
language class by completions, yielding `PromiseP`, `PromiseNP`, and
`PromiseCoNP` without assigning semantics outside the promise.
-/


public section

namespace Complexity

namespace PromiseProblem

/-- A promised yes-instance cannot also be a promised no-instance. -/
theorem not_mem_no_of_mem_yes (problem : PromiseProblem)
    {x : List Bool} (hyes : x ∈ problem.yesInstances) :
    x ∉ problem.noInstances :=
  not_mem_no_of_mem_yes_internal problem hyes

/-- A promised no-instance cannot also be a promised yes-instance. -/
theorem not_mem_yes_of_mem_no (problem : PromiseProblem)
    {x : List Bool} (hno : x ∈ problem.noInstances) :
    x ∉ problem.yesInstances :=
  not_mem_yes_of_mem_no_internal problem hno

/-- The promise is exactly the union of the two constrained sides. -/
theorem mem_promise_iff (problem : PromiseProblem) (x : List Bool) :
    x ∈ problem.promise ↔
      x ∈ problem.yesInstances ∨ x ∈ problem.noInstances :=
  mem_promise_iff_internal problem x

/-- Complementing a promise problem twice recovers it. -/
@[simp] theorem complement_complement (problem : PromiseProblem) :
    problem.complement.complement = problem :=
  complement_complement_internal problem

/-- Complementing a problem does not change its promised input set. -/
@[simp] theorem promise_complement (problem : PromiseProblem) :
    problem.complement.promise = problem.promise :=
  promise_complement_internal problem

/-- Solving the complemented promise is equivalent to complementing the
Boolean output of a solver for the original problem. -/
theorem solvedBy_complement_iff (problem : PromiseProblem)
    (decide : List Bool → Bool) :
    problem.complement.SolvedBy decide ↔
      problem.SolvedBy (fun x => !(decide x)) :=
  solvedBy_complement_iff_internal problem decide

/-- The ordinary-language embedding promises every input. -/
@[simp] theorem promise_ofLanguage (L : Language) :
    (ofLanguage L).promise = Set.univ :=
  promise_ofLanguage_internal L

/-- Solving an embedded ordinary language is exactly deciding it everywhere. -/
theorem solvedBy_ofLanguage_iff (L : Language)
    (decide : List Bool → Bool) :
    (ofLanguage L).SolvedBy decide ↔
      ∀ x, decide x = true ↔ x ∈ L :=
  solvedBy_ofLanguage_iff_internal L decide

/-- Identity preserves both sides of every promise problem. -/
theorem mapReducesVia_refl (problem : PromiseProblem) :
    problem.MapReducesVia problem id :=
  mapReducesVia_refl_internal problem

/-- Side-preserving maps compose. -/
theorem MapReducesVia.trans {first second third : PromiseProblem}
    {f g : List Bool → List Bool}
    (hfirst : first.MapReducesVia second f)
    (hsecond : second.MapReducesVia third g) :
    first.MapReducesVia third (g ∘ f) :=
  hfirst.trans_internal hsecond

/-- Polynomial-time promise reducibility is reflexive. -/
theorem mapReducesPoly_refl (problem : PromiseProblem) :
    problem.MapReducesPoly problem :=
  mapReducesPoly_refl_internal problem

/-- Polynomial-time promise reductions compose. -/
theorem MapReducesPoly.trans {first second third : PromiseProblem}
    (hfirst : first.MapReducesPoly second)
    (hsecond : second.MapReducesPoly third) :
    first.MapReducesPoly third :=
  hfirst.trans_internal hsecond

/-- On total embedded languages, preserving both promised sides is equivalent
to the usual membership equivalence. -/
theorem mapReducesVia_ofLanguage_iff (first second : Language)
    (f : List Bool → List Bool) :
    (ofLanguage first).MapReducesVia (ofLanguage second) f ↔
      ∀ x, x ∈ first ↔ f x ∈ second :=
  mapReducesVia_ofLanguage_iff_internal first second f

/-- Promise-class membership transports backward along a polynomial-time
side-preserving reduction whenever the underlying language class is closed
under polynomial-time preimages. -/
theorem MapReducesPoly.mem_promiseClass
    {C : Set Language} {source target : PromiseProblem}
    (hpreimage : ∀ {f : List Bool → List Bool} {L : Language},
      f ∈ FP → L ∈ C → f ⁻¹' L ∈ C)
    (hred : source.MapReducesPoly target)
    (htarget : target ∈ PromiseClass C) :
    source ∈ PromiseClass C :=
  hred.mem_promiseClass_internal hpreimage htarget

/-- `PromiseP` is closed backward under polynomial-time promise reductions. -/
theorem MapReducesPoly.mem_PromiseP
    {source target : PromiseProblem}
    (hred : source.MapReducesPoly target) (htarget : target ∈ PromiseP) :
    source ∈ PromiseP :=
  hred.mem_PromiseP_internal htarget

/-- `PromiseNP` is closed backward under polynomial-time promise reductions. -/
theorem MapReducesPoly.mem_PromiseNP
    {source target : PromiseProblem}
    (hred : source.MapReducesPoly target) (htarget : target ∈ PromiseNP) :
    source ∈ PromiseNP :=
  hred.mem_PromiseNP_internal htarget

/-- A promise problem belongs to `PromiseNP` whenever its yes-instance
language itself belongs to `NP`. -/
theorem mem_PromiseNP_of_yesInstances_mem_NP
    (problem : PromiseProblem) (hyes : problem.yesInstances ∈ NP) :
    problem ∈ PromiseNP :=
  mem_PromiseNP_of_yesInstances_mem_NP_internal problem hyes

/-- An FNP relation characterizing the promised yes-instances yields
`PromiseNP` membership. -/
theorem mem_PromiseNP_of_FNP_witness
    (problem : PromiseProblem)
    {R : List Bool → List Bool → Prop} (hR : R ∈ FNP)
    (hchar : ∀ x, x ∈ problem.yesInstances ↔ ∃ y, R x y) :
    problem ∈ PromiseNP :=
  mem_PromiseNP_of_FNP_witness_internal problem hR hchar

/-- A total embedded language lies in a lifted promise class exactly when the
language lies in the underlying class. -/
@[simp] theorem ofLanguage_mem_promiseClass_iff
    (C : Set Language) (L : Language) :
    ofLanguage L ∈ PromiseClass C ↔ L ∈ C :=
  ofLanguage_mem_promiseClass_iff_internal C L

/-- Total-language embedding preserves and reflects `P`. -/
@[simp] theorem ofLanguage_mem_PromiseP_iff (L : Language) :
    ofLanguage L ∈ PromiseP ↔ L ∈ P := by
  exact ofLanguage_mem_promiseClass_iff P L

/-- Total-language embedding preserves and reflects `NP`. -/
@[simp] theorem ofLanguage_mem_PromiseNP_iff (L : Language) :
    ofLanguage L ∈ PromiseNP ↔ L ∈ NP := by
  exact ofLanguage_mem_promiseClass_iff NP L

/-- Total-language embedding preserves and reflects `coNP`. -/
@[simp] theorem ofLanguage_mem_PromiseCoNP_iff (L : Language) :
    ofLanguage L ∈ PromiseCoNP ↔ L ∈ coNP := by
  exact ofLanguage_mem_promiseClass_iff coNP L

/-- Every completion induces an identity reduction from the promise problem to
the corresponding total embedded language. -/
theorem mapReducesPoly_to_ofLanguage
    {problem : PromiseProblem} {completion : Language}
    (hyes : problem.yesInstances ⊆ completion)
    (hno : Disjoint completion problem.noInstances) :
    problem.MapReducesPoly (ofLanguage completion) :=
  mapReducesPoly_to_ofLanguage_internal hyes hno

/-- Embedding a total language is promise-NP-complete exactly when the
original language is NP-complete. -/
@[simp] theorem ofLanguage_promiseNPComplete_iff (L : Language) :
    PromiseNPComplete (ofLanguage L) ↔ NPComplete L :=
  ofLanguage_promiseNPComplete_iff_internal L

end PromiseProblem

/-- Inclusion of ordinary language classes lifts to their completion-based
promise classes. -/
theorem promiseClass_mono {C D : Set Language} (hsubset : C ⊆ D) :
    PromiseClass C ⊆ PromiseClass D :=
  promiseClass_mono_internal hsubset

/-- Deterministic polynomial-time promise problems lie in `PromiseNP`. -/
theorem PromiseP_subset_PromiseNP : PromiseP ⊆ PromiseNP :=
  PromiseP_subset_PromiseNP_internal

/-- Hardness against all total languages in `C` is equivalent to hardness
against every problem in the completion-based promise lift of `C`. -/
theorem promiseHardFor_iff_forall_promiseClass
    (C : Set Language) (target : PromiseProblem) :
    PromiseHardFor C target ↔
      ∀ source ∈ PromiseClass C, source.MapReducesPoly target :=
  promiseHardFor_iff_forall_promiseClass_internal C target

/-- In particular, NP-hardness of a promise target may equivalently quantify
over every source problem in `PromiseNP`. -/
theorem promiseNPHard_iff_forall_promiseNP (target : PromiseProblem) :
    PromiseNPHard target ↔
      ∀ source ∈ PromiseNP, source.MapReducesPoly target :=
  promiseHardFor_iff_forall_promiseClass NP target

/-- Promise hardness transfers forward along a side-preserving polynomial
reduction. -/
theorem PromiseHardFor.of_reduction
    {C : Set Language} {first second : PromiseProblem}
    (hfirst : PromiseHardFor C first)
    (hred : first.MapReducesPoly second) :
    PromiseHardFor C second :=
  hfirst.of_reduction_internal hred

/-- `PromiseP` is closed under swapping its promised yes and no sides. -/
theorem PromiseP.complement {problem : PromiseProblem}
    (hproblem : problem ∈ PromiseP) :
    problem.complement ∈ PromiseP :=
  PromiseP_complement_internal hproblem

/-- Complementing a promise problem preserves `PromiseP` in both directions. -/
@[simp] theorem complement_mem_PromiseP_iff (problem : PromiseProblem) :
    problem.complement ∈ PromiseP ↔ problem ∈ PromiseP := by
  constructor
  · intro hcomplement
    simpa using PromiseP.complement hcomplement
  · exact PromiseP.complement

/-- The completion-based promise classes collapse exactly when `P = NP`. -/
theorem promiseP_eq_promiseNP_iff : PromiseP = PromiseNP ↔ P = NP :=
  promiseP_eq_promiseNP_iff_internal

/-- If an NP-hard promise target has a deterministic polynomial-time
completion, then `P = NP`. -/
theorem PromiseNPHard.P_eq_NP_of_mem_PromiseP
    {target : PromiseProblem} (hhard : PromiseNPHard target)
    (hmembership : target ∈ PromiseP) :
    P = NP :=
  hhard.P_eq_NP_of_mem_PromiseP_internal hmembership

/-- Assuming `P ≠ NP`, no NP-hard promise target can have a deterministic
polynomial-time completion. -/
theorem PromiseNPHard.not_mem_PromiseP_of_P_ne_NP
    {target : PromiseProblem} (hhard : PromiseNPHard target)
    (hne : P ≠ NP) :
    target ∉ PromiseP :=
  fun hmembership => hne (hhard.P_eq_NP_of_mem_PromiseP hmembership)

/-- A promise-NP-complete problem lies in `PromiseP` exactly if `P = NP`. -/
theorem PromiseNPComplete.mem_PromiseP_iff_P_eq_NP
    {target : PromiseProblem} (hcomplete : PromiseNPComplete target) :
    target ∈ PromiseP ↔ P = NP :=
  hcomplete.mem_PromiseP_iff_P_eq_NP_internal

end Complexity
