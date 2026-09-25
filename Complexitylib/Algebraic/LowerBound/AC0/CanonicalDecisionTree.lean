/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.DecisionTree

/-!
# Canonical decision trees for DNF formulas

This module formalizes the dynamic canonical decision tree used in the
decision-tree form of Hastad's switching lemma. At each partial assignment it
restricts the whole DNF, selects the first surviving term, and queries every
remaining variable of that term in input-coordinate order. A satisfying
branch returns `true`; every other branch repeats the construction after the
new assignments have simplified the entire formula.

The recursion is structural in the number of live variables. It is not an
optimal-tree search. The distinguished tree makes the eventual switching
event concrete and decidable while its correctness gives an ordinary
existential decision-tree depth bound as a corollary.
-/

@[expose] public section

namespace Algebraic
namespace AC0

namespace LiteralSet

/-- The support of a literal set in the canonical input-coordinate order. -/
def orderedSupport (set : LiteralSet n) : List (Fin n) :=
  (List.finRange n).filter fun index => index ∈ set.support

@[simp] theorem mem_orderedSupport
    (set : LiteralSet n)
    (index : Fin n) :
    index ∈ set.orderedSupport ↔ index ∈ set.support := by
  simp [orderedSupport]

/-- Canonical support lists contain no repeated coordinate. -/
theorem nodup_orderedSupport (set : LiteralSet n) :
    set.orderedSupport.Nodup := by
  exact (List.nodup_finRange n).filter _

end LiteralSet

namespace DNF

/-- The first source term not already falsified by a partial assignment. -/
def firstSurvivingIn
    (rho : PartialAssignment n) : List (Term n) → Option (Term n)
  | [] => none
  | term :: rest =>
      if term.ConflictsWith rho then firstSurvivingIn rho rest
      else some term

/-- The first term of an ordered DNF not falsified by the assignment. -/
def firstSurviving
    (formula : DNF n)
    (rho : PartialAssignment n) : Option (Term n) :=
  firstSurvivingIn rho formula.terms

/-- Failure to find a surviving term means that every source term conflicts
with the assignment. -/
theorem firstSurvivingIn_eq_none_iff
    (rho : PartialAssignment n)
    (terms : List (Term n)) :
    firstSurvivingIn rho terms = none ↔
      ∀ term, term ∈ terms → term.ConflictsWith rho := by
  induction terms with
  | nil => simp [firstSurvivingIn]
  | cons term rest inductionHypothesis =>
      by_cases conflict : term.ConflictsWith rho
      · simp [firstSurvivingIn, conflict, inductionHypothesis]
      · simp [firstSurvivingIn, conflict]

/-- A term returned by `firstSurvivingIn` occurs in the source list. -/
theorem firstSurvivingIn_mem
    (rho : PartialAssignment n)
    (terms : List (Term n))
    {term : Term n}
    (found : firstSurvivingIn rho terms = some term) :
    term ∈ terms := by
  induction terms with
  | nil => simp [firstSurvivingIn] at found
  | cons head rest inductionHypothesis =>
      by_cases conflict : head.ConflictsWith rho
      · simp only [firstSurvivingIn, ite_eq_left conflict] at found
        exact List.mem_cons_of_mem head (inductionHypothesis found)
      · simp only [firstSurvivingIn, ite_eq_right conflict,
          Option.some.injEq] at found
        subst head
        simp

/-- A term returned by `firstSurvivingIn` is not falsified. -/
theorem firstSurvivingIn_not_conflicts
    (rho : PartialAssignment n)
    (terms : List (Term n))
    {term : Term n}
    (found : firstSurvivingIn rho terms = some term) :
    ¬term.ConflictsWith rho := by
  induction terms with
  | nil => simp [firstSurvivingIn] at found
  | cons head rest inductionHypothesis =>
      by_cases conflict : head.ConflictsWith rho
      · simp only [firstSurvivingIn, ite_eq_left conflict] at found
        exact inductionHypothesis found
      · simp only [firstSurvivingIn, ite_eq_right conflict,
          Option.some.injEq] at found
        subst head
        exact conflict

/-- A first surviving term remains first after refinement whenever that term
itself remains nonconflicting. -/
theorem firstSurvivingIn_refine
    (rho extension : PartialAssignment n)
    (terms : List (Term n))
    {term : Term n}
    (found : firstSurvivingIn rho terms = some term)
    (survives : ¬term.ConflictsWith (rho.refine extension)) :
    firstSurvivingIn (rho.refine extension) terms = some term := by
  induction terms with
  | nil => simp [firstSurvivingIn] at found
  | cons head rest inductionHypothesis =>
      by_cases conflict : head.ConflictsWith rho
      · have refinedConflict := conflict.refine extension
        simp only [firstSurvivingIn, ite_eq_left conflict] at found
        simp only [firstSurvivingIn, ite_eq_left refinedConflict]
        exact inductionHypothesis found
      · simp only [firstSurvivingIn, ite_eq_right conflict,
          Option.some.injEq] at found
        subst head
        simp [firstSurvivingIn, survives]

/-- Variables of `term` still live under `rho`, retained in canonical input
order. -/
def liveSupport
    (term : Term n)
    (rho : PartialAssignment n) : List (Fin n) :=
  term.orderedSupport.filter fun index => decide (rho index = none)

@[simp] theorem mem_liveSupport
    (term : Term n)
    (rho : PartialAssignment n)
    (index : Fin n) :
    index ∈ liveSupport term rho ↔
      index ∈ term.support ∧ rho index = none := by
  simp [liveSupport]

/-- Live-support lists contain no repeated coordinate. -/
theorem nodup_liveSupport
    (term : Term n)
    (rho : PartialAssignment n) :
    (liveSupport term rho).Nodup :=
  (LiteralSet.nodup_orderedSupport term).filter _

/-- Computing live support from the source term agrees with first taking its
residual literal set. -/
theorem orderedSupport_residual
    (term : Term n)
    (rho : PartialAssignment n) :
    (term.residual rho).orderedSupport = liveSupport term rho := by
  simp only [LiteralSet.orderedSupport, liveSupport, List.filter_filter]
  apply List.filter_congr
  intro index _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  rw [LiteralSet.mem_support, LiteralSet.mem_support]
  cases fixed : rho index <;>
    simp [LiteralSet.residual, fixed]

/-- A first surviving source term remains first after a refinement whenever
that term itself remains nonconflicting. -/
theorem firstSurviving_refine
    (formula : DNF n)
    (rho extension : PartialAssignment n)
    {term : Term n}
    (found : formula.firstSurviving rho = some term)
    (survives : ¬term.ConflictsWith (rho.refine extension)) :
    formula.firstSurviving (rho.refine extension) = some term := by
  exact firstSurvivingIn_refine rho extension formula.terms found survives

/-- If no source term survives, the restricted DNF is constantly false. -/
theorem eval_apply_eq_false_of_firstSurviving_eq_none
    (formula : DNF n)
    (rho : PartialAssignment n)
    (input : Fin n → Bool)
    (noneSurvives : formula.firstSurviving rho = none) :
    formula.eval (rho.apply input) = false := by
  apply Bool.eq_false_iff.mpr
  intro formulaTrue
  obtain ⟨term, present, satisfied⟩ :=
    (eval_eq_true formula (rho.apply input)).1 formulaTrue
  have conflict : term.ConflictsWith rho :=
    (firstSurvivingIn_eq_none_iff rho formula.terms).1 noneSurvives
      term present
  have termTrue : term.eval (rho.apply input) = true :=
    (Term.eval_eq_true term (rho.apply input)).2 satisfied
  rw [Term.eval_apply_eq_false_of_conflicts term rho input conflict] at termTrue
  contradiction

/-- A surviving term with no live variable makes the restricted DNF
constantly true. -/
theorem eval_apply_eq_true_of_firstSurviving_liveSupport_eq_nil
    (formula : DNF n)
    (rho : PartialAssignment n)
    {term : Term n}
    (found : formula.firstSurviving rho = some term)
    (supportEmpty : liveSupport term rho = [])
    (input : Fin n → Bool) :
    formula.eval (rho.apply input) = true := by
  have noConflict : ¬term.ConflictsWith rho :=
    firstSurvivingIn_not_conflicts rho formula.terms found
  have residualTrue : Term.eval (term.residual rho) input = true := by
    apply (Term.eval_eq_true (term.residual rho) input).2
    intro index value required
    have supportPresent : index ∈ (term.residual rho).support :=
      (LiteralSet.mem_support (term.residual rho) index).2 (by
        simp [required])
    have orderedPresent : index ∈ (term.residual rho).orderedSupport :=
      (LiteralSet.mem_orderedSupport (term.residual rho) index).2
        supportPresent
    rw [orderedSupport_residual, supportEmpty] at orderedPresent
    simp at orderedPresent
  apply (eval_eq_true formula (rho.apply input)).2
  refine ⟨term, firstSurvivingIn_mem rho formula.terms found, ?_⟩
  apply (Term.eval_eq_true term (rho.apply input)).1
  rw [← Term.eval_residual_eq_eval_apply_of_not_conflicts
    term rho input noConflict]
  exact residualTrue

/-- Every term returned by DNF restriction uses only variables left live by
the restriction. -/
theorem support_subset_live_of_mem_restrict
    (formula : DNF n)
    (rho : PartialAssignment n)
    {term : Term n}
    (present : term ∈ (formula.restrict rho).terms) :
    term.support ⊆ rho.liveVariables := by
  obtain ⟨source, _, restricted⟩ := List.mem_filterMap.1 present
  by_cases conflict : source.ConflictsWith rho
  · simp [Term.restrict, conflict] at restricted
  · rw [Term.restrict, ite_eq_right conflict] at restricted
    injection restricted with equal
    subst term
    exact LiteralSet.support_residual_subset_live source rho

/-- Query the listed variables in order, then continue with `recurse` on the
refined restriction, whose number of live variables stays below `bound`. -/
def queryRemainingBelow
    (indices : List (Fin n))
    (rho : PartialAssignment n)
    (bound : Nat)
    (below : rho.liveCount < bound)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < bound → DecisionTree n) : DecisionTree n :=
  match indices with
  | [] => recurse rho below
  | index :: rest =>
      .query index
        (queryRemainingBelow rest
          (rho.refine (PartialAssignment.fix index false)) bound
          ((PartialAssignment.liveCount_refine_le_left rho
            (PartialAssignment.fix index false)).trans_lt below)
          recurse)
        (queryRemainingBelow rest
          (rho.refine (PartialAssignment.fix index true)) bound
          ((PartialAssignment.liveCount_refine_le_left rho
            (PartialAssignment.fix index true)).trans_lt below)
          recurse)

private theorem queryRemainingBelow_computes
    (formula : DNF n)
    (indices : List (Fin n))
    (rho : PartialAssignment n)
    (bound : Nat)
    (below : rho.liveCount < bound)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < bound → DecisionTree n)
    (nodup : indices.Nodup)
    (allLive : ∀ index, index ∈ indices → rho index = none)
    (recurseComputes : ∀ sigma below,
      (recurse sigma below).Computes
        fun input => formula.eval (sigma.apply input)) :
    (queryRemainingBelow indices rho bound below recurse).Computes
      fun input => formula.eval (rho.apply input) := by
  induction indices generalizing rho with
  | nil =>
      exact recurseComputes rho below
  | cons index rest inductionHypothesis =>
      have indexAbsent : index ∉ rest := (List.nodup_cons.mp nodup).1
      have restNodup : rest.Nodup := (List.nodup_cons.mp nodup).2
      have indexLive : rho index = none := allLive index (by simp)
      have tailLive : ∀ current, current ∈ rest →
          rho current = none := by
        intro current currentPresent
        exact allLive current (by simp [currentPresent])
      have refinedTailLive (value : Bool) :
          ∀ current, current ∈ rest →
            (rho.refine (PartialAssignment.fix index value)) current = none := by
        intro current currentPresent
        have different : current ≠ index := by
          intro equal
          subst current
          exact indexAbsent currentPresent
        simp [PartialAssignment.refine, tailLive current currentPresent,
          PartialAssignment.fix, different]
      have falseComputes := inductionHypothesis
        (rho.refine (PartialAssignment.fix index false))
        ((PartialAssignment.liveCount_refine_le_left rho
          (PartialAssignment.fix index false)).trans_lt below)
        restNodup (refinedTailLive false)
      have trueComputes := inductionHypothesis
        (rho.refine (PartialAssignment.fix index true))
        ((PartialAssignment.liveCount_refine_le_left rho
          (PartialAssignment.fix index true)).trans_lt below)
        restNodup (refinedTailLive true)
      intro input
      cases inputValue : input index with
      | false =>
          simp only [queryRemainingBelow, DecisionTree.eval_query, inputValue,
            Bool.false_eq_true, ite_false]
          rw [falseComputes input]
          change formula.eval
              ((rho.refine (PartialAssignment.fix index false)).apply input) =
            formula.eval (rho.apply input)
          rw [PartialAssignment.apply_refine,
            PartialAssignment.apply_fix_eq_self input index false inputValue]
      | true =>
          simp only [queryRemainingBelow, DecisionTree.eval_query, inputValue,
            ite_true]
          rw [trueComputes input]
          change formula.eval
              ((rho.refine (PartialAssignment.fix index true)).apply input) =
            formula.eval (rho.apply input)
          rw [PartialAssignment.apply_refine,
            PartialAssignment.apply_fix_eq_self input index true inputValue]

private theorem depth_queryRemainingBelow_le_liveCount
    (indices : List (Fin n))
    (rho : PartialAssignment n)
    (bound : Nat)
    (below : rho.liveCount < bound)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < bound → DecisionTree n)
    (nodup : indices.Nodup)
    (allLive : ∀ index, index ∈ indices → rho index = none)
    (recurseDepth : ∀ sigma below,
      (recurse sigma below).depth ≤ sigma.liveCount) :
    (queryRemainingBelow indices rho bound below recurse).depth ≤
      rho.liveCount := by
  induction indices generalizing rho with
  | nil =>
      simpa [queryRemainingBelow] using recurseDepth rho below
  | cons index rest inductionHypothesis =>
      have indexAbsent : index ∉ rest := (List.nodup_cons.mp nodup).1
      have restNodup : rest.Nodup := (List.nodup_cons.mp nodup).2
      have indexLive : rho index = none := allLive index (by simp)
      have restLive : ∀ current, current ∈ rest →
          rho current = none := by
        intro current currentPresent
        exact allLive current (by simp [currentPresent])
      have refinedRestLive (value : Bool) :
          ∀ current, current ∈ rest →
            (rho.refine (PartialAssignment.fix index value)) current = none := by
        intro current currentPresent
        have different : current ≠ index := by
          intro equal
          subst current
          exact indexAbsent currentPresent
        simp [PartialAssignment.refine, restLive current currentPresent,
          PartialAssignment.fix, different]
      have falseBound := inductionHypothesis
        (rho.refine (PartialAssignment.fix index false))
        ((PartialAssignment.liveCount_refine_le_left rho
          (PartialAssignment.fix index false)).trans_lt below)
        restNodup (refinedRestLive false)
      have trueBound := inductionHypothesis
        (rho.refine (PartialAssignment.fix index true))
        ((PartialAssignment.liveCount_refine_le_left rho
          (PartialAssignment.fix index true)).trans_lt below)
        restNodup (refinedRestLive true)
      have falseDecrease :=
        PartialAssignment.liveCount_refine_fix_lt_of_live
          rho index false indexLive
      have trueDecrease :=
        PartialAssignment.liveCount_refine_fix_lt_of_live
          rho index true indexLive
      simp only [queryRemainingBelow, DecisionTree.depth_query]
      omega

private theorem queryRemainingBelow_readOnceWithin
    (indices : List (Fin n))
    (rho : PartialAssignment n)
    (bound : Nat)
    (below : rho.liveCount < bound)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < bound → DecisionTree n)
    (nodup : indices.Nodup)
    (allLive : ∀ index, index ∈ indices → rho index = none)
    (recurseReadOnce : ∀ sigma below,
      (recurse sigma below).ReadOnceWithin sigma.liveVariables) :
    (queryRemainingBelow indices rho bound below recurse).ReadOnceWithin
      rho.liveVariables := by
  induction indices generalizing rho with
  | nil =>
      simpa [queryRemainingBelow] using recurseReadOnce rho below
  | cons index rest inductionHypothesis =>
      have indexAbsent : index ∉ rest := (List.nodup_cons.mp nodup).1
      have restNodup : rest.Nodup := (List.nodup_cons.mp nodup).2
      have indexLive : rho index = none := allLive index (by simp)
      have indexPresent : index ∈ rho.liveVariables :=
        (PartialAssignment.mem_liveVariables rho index).2 indexLive
      have restLive : ∀ current, current ∈ rest →
          rho current = none := by
        intro current currentPresent
        exact allLive current (by simp [currentPresent])
      have refinedRestLive (value : Bool) :
          ∀ current, current ∈ rest →
            (rho.refine (PartialAssignment.fix index value)) current = none := by
        intro current currentPresent
        have different : current ≠ index := by
          intro equal
          subst current
          exact indexAbsent currentPresent
        simp [PartialAssignment.refine, restLive current currentPresent,
          PartialAssignment.fix, different]
      have falseReadOnce := inductionHypothesis
        (rho.refine (PartialAssignment.fix index false))
        ((PartialAssignment.liveCount_refine_le_left rho
          (PartialAssignment.fix index false)).trans_lt below)
        restNodup (refinedRestLive false)
      have trueReadOnce := inductionHypothesis
        (rho.refine (PartialAssignment.fix index true))
        ((PartialAssignment.liveCount_refine_le_left rho
          (PartialAssignment.fix index true)).trans_lt below)
        restNodup (refinedRestLive true)
      simp only [queryRemainingBelow, DecisionTree.ReadOnceWithin]
      refine ⟨indexPresent, ?_, ?_⟩
      · simpa [PartialAssignment.liveVariables_refine_fix] using
          falseReadOnce
      · simpa [PartialAssignment.liveVariables_refine_fix] using
          trueReadOnce

/-- One step of the canonical decision tree at a surviving term: query the term's
live variables, answer `true` if the term is satisfied, and otherwise recurse on
the refined restriction. -/
def canonicalSupportStep
    (_formula : DNF n)
    (rho : PartialAssignment n)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < rho.liveCount → DecisionTree n)
    (indices : List (Fin n))
    (allLive : ∀ index, index ∈ indices → rho index = none) :
    DecisionTree n :=
  match indices with
  | [] => .leaf true
  | index :: rest =>
      have indexLive : rho index = none := allLive index (by simp)
      .query index
        (queryRemainingBelow rest
          (rho.refine (PartialAssignment.fix index false)) rho.liveCount
          (PartialAssignment.liveCount_refine_fix_lt_of_live
            rho index false indexLive)
          recurse)
        (queryRemainingBelow rest
          (rho.refine (PartialAssignment.fix index true)) rho.liveCount
          (PartialAssignment.liveCount_refine_fix_lt_of_live
            rho index true indexLive)
          recurse)

private theorem canonicalSupportStep_congr
    (formula : DNF n)
    (rho : PartialAssignment n)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < rho.liveCount → DecisionTree n)
    (left right : List (Fin n))
    (leftLive : ∀ index, index ∈ left → rho index = none)
    (rightLive : ∀ index, index ∈ right → rho index = none)
    (equal : left = right) :
    canonicalSupportStep formula rho recurse left leftLive =
      canonicalSupportStep formula rho recurse right rightLive := by
  subst right
  rfl

/-- One step of the canonical decision tree of a DNF under restriction `rho`:
answer `false` if no term survives, and otherwise query the first surviving
term's live variables. -/
def canonicalDecisionTreeStep
    (formula : DNF n)
    (rho : PartialAssignment n)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < rho.liveCount → DecisionTree n) : DecisionTree n :=
  match formula.firstSurviving rho with
  | none => .leaf false
  | some term =>
      canonicalSupportStep formula rho recurse (liveSupport term rho)
        fun index present => (mem_liveSupport term rho index).1 present |>.2

private theorem depth_canonicalSupportStep_le_liveCount
    (formula : DNF n)
    (rho : PartialAssignment n)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < rho.liveCount → DecisionTree n)
    (indices : List (Fin n))
    (allLive : ∀ index, index ∈ indices → rho index = none)
    (nodup : indices.Nodup)
    (recurseDepth : ∀ sigma below,
      (recurse sigma below).depth ≤ sigma.liveCount) :
    (canonicalSupportStep formula rho recurse indices allLive).depth ≤
      rho.liveCount := by
  cases indices with
  | nil => simp [canonicalSupportStep]
  | cons index rest =>
      have indexAbsent : index ∉ rest := (List.nodup_cons.mp nodup).1
      have restNodup : rest.Nodup := (List.nodup_cons.mp nodup).2
      have indexLive : rho index = none := allLive index (by simp)
      have restLive : ∀ current, current ∈ rest →
          rho current = none := by
        intro current currentPresent
        exact allLive current (by simp [currentPresent])
      have refinedRestLive (value : Bool) :
          ∀ current, current ∈ rest →
            (rho.refine (PartialAssignment.fix index value)) current = none := by
        intro current currentPresent
        have different : current ≠ index := by
          intro equal
          subst current
          exact indexAbsent currentPresent
        simp [PartialAssignment.refine, restLive current currentPresent,
          PartialAssignment.fix, different]
      have falseBelow :=
        PartialAssignment.liveCount_refine_fix_lt_of_live
          rho index false indexLive
      have trueBelow :=
        PartialAssignment.liveCount_refine_fix_lt_of_live
          rho index true indexLive
      have falseBound := depth_queryRemainingBelow_le_liveCount
        rest (rho.refine (PartialAssignment.fix index false)) rho.liveCount
        falseBelow recurse restNodup (refinedRestLive false) recurseDepth
      have trueBound := depth_queryRemainingBelow_le_liveCount
        rest (rho.refine (PartialAssignment.fix index true)) rho.liveCount
        trueBelow recurse restNodup (refinedRestLive true) recurseDepth
      simp only [canonicalSupportStep, DecisionTree.depth_query]
      omega

private theorem canonicalSupportStep_readOnceWithin
    (formula : DNF n)
    (rho : PartialAssignment n)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < rho.liveCount → DecisionTree n)
    (indices : List (Fin n))
    (allLive : ∀ index, index ∈ indices → rho index = none)
    (nodup : indices.Nodup)
    (recurseReadOnce : ∀ sigma below,
      (recurse sigma below).ReadOnceWithin sigma.liveVariables) :
    (canonicalSupportStep formula rho recurse indices allLive).ReadOnceWithin
      rho.liveVariables := by
  cases indices with
  | nil => simp [canonicalSupportStep, DecisionTree.ReadOnceWithin]
  | cons index rest =>
      have indexAbsent : index ∉ rest := (List.nodup_cons.mp nodup).1
      have restNodup : rest.Nodup := (List.nodup_cons.mp nodup).2
      have indexLive : rho index = none := allLive index (by simp)
      have indexPresent : index ∈ rho.liveVariables :=
        (PartialAssignment.mem_liveVariables rho index).2 indexLive
      have restLive : ∀ current, current ∈ rest →
          rho current = none := by
        intro current currentPresent
        exact allLive current (by simp [currentPresent])
      have refinedRestLive (value : Bool) :
          ∀ current, current ∈ rest →
            (rho.refine (PartialAssignment.fix index value)) current = none := by
        intro current currentPresent
        have different : current ≠ index := by
          intro equal
          subst current
          exact indexAbsent currentPresent
        simp [PartialAssignment.refine, restLive current currentPresent,
          PartialAssignment.fix, different]
      have falseBelow :=
        PartialAssignment.liveCount_refine_fix_lt_of_live
          rho index false indexLive
      have trueBelow :=
        PartialAssignment.liveCount_refine_fix_lt_of_live
          rho index true indexLive
      have falseReadOnce := queryRemainingBelow_readOnceWithin
        rest (rho.refine (PartialAssignment.fix index false)) rho.liveCount
        falseBelow recurse restNodup (refinedRestLive false) recurseReadOnce
      have trueReadOnce := queryRemainingBelow_readOnceWithin
        rest (rho.refine (PartialAssignment.fix index true)) rho.liveCount
        trueBelow recurse restNodup (refinedRestLive true) recurseReadOnce
      simp only [canonicalSupportStep, DecisionTree.ReadOnceWithin]
      refine ⟨indexPresent, ?_, ?_⟩
      · simpa [PartialAssignment.liveVariables_refine_fix] using
          falseReadOnce
      · simpa [PartialAssignment.liveVariables_refine_fix] using
          trueReadOnce

private theorem canonicalSupportStep_computes
    (formula : DNF n)
    (rho : PartialAssignment n)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < rho.liveCount → DecisionTree n)
    (indices : List (Fin n))
    (allLive : ∀ index, index ∈ indices → rho index = none)
    (nodup : indices.Nodup)
    (recurseComputes : ∀ sigma below,
      (recurse sigma below).Computes
        fun input => formula.eval (sigma.apply input))
    (emptyTrue : indices = [] → ∀ input,
      formula.eval (rho.apply input) = true) :
    (canonicalSupportStep formula rho recurse indices allLive).Computes
      fun input => formula.eval (rho.apply input) := by
  cases indices with
  | nil =>
      intro input
      simpa [canonicalSupportStep] using (emptyTrue rfl input).symm
  | cons index rest =>
      have indexAbsent : index ∉ rest := (List.nodup_cons.mp nodup).1
      have restNodup : rest.Nodup := (List.nodup_cons.mp nodup).2
      have indexLive : rho index = none := allLive index (by simp)
      have restLive : ∀ current, current ∈ rest →
          rho current = none := by
        intro current currentPresent
        exact allLive current (by simp [currentPresent])
      have refinedRestLive (value : Bool) :
          ∀ current, current ∈ rest →
            (rho.refine (PartialAssignment.fix index value)) current = none := by
        intro current currentPresent
        have different : current ≠ index := by
          intro equal
          subst current
          exact indexAbsent currentPresent
        simp [PartialAssignment.refine, restLive current currentPresent,
          PartialAssignment.fix, different]
      have falseBelow :=
        PartialAssignment.liveCount_refine_fix_lt_of_live
          rho index false indexLive
      have trueBelow :=
        PartialAssignment.liveCount_refine_fix_lt_of_live
          rho index true indexLive
      have falseComputes := queryRemainingBelow_computes
        formula rest (rho.refine (PartialAssignment.fix index false))
        rho.liveCount falseBelow recurse restNodup
        (refinedRestLive false) recurseComputes
      have trueComputes := queryRemainingBelow_computes
        formula rest (rho.refine (PartialAssignment.fix index true))
        rho.liveCount trueBelow recurse restNodup
        (refinedRestLive true) recurseComputes
      intro input
      simp only [canonicalSupportStep, DecisionTree.eval_query]
      cases inputValue : input index with
      | false =>
          simp only [Bool.false_eq_true, ite_false]
          rw [falseComputes input]
          change formula.eval
              ((rho.refine (PartialAssignment.fix index false)).apply input) =
            formula.eval (rho.apply input)
          rw [PartialAssignment.apply_refine,
            PartialAssignment.apply_fix_eq_self input index false inputValue]
      | true =>
          simp only [ite_true]
          rw [trueComputes input]
          change formula.eval
              ((rho.refine (PartialAssignment.fix index true)).apply input) =
            formula.eval (rho.apply input)
          rw [PartialAssignment.apply_refine,
            PartialAssignment.apply_fix_eq_self input index true inputValue]

/-- The canonical decision tree of `formula` below a partial assignment.

The whole formula is freshly restricted between queried terms. Hence later
term selection incorporates every assignment made along the current branch.
-/
def canonicalDecisionTree
    (formula : DNF n)
    (rho : PartialAssignment n) : DecisionTree n :=
  canonicalDecisionTreeStep formula rho fun sigma _ =>
    canonicalDecisionTree formula sigma
termination_by rho.liveCount

mutual

/-- A canonical path transcript partitioned into the successive source terms
selected by the canonical procedure. -/
inductive CanonicalTrace (formula : DNF n) :
    PartialAssignment n → List (DecisionTree.PathStep n) → Type
  /-- The empty path prefix is valid at every canonical state. -/
  | nil (rho : PartialAssignment n) : CanonicalTrace formula rho []
  /-- Begin the next nonempty query block at the first surviving source term.
  -/
  | start
      {rho : PartialAssignment n}
      {term : Term n}
      {indices : List (Fin n)}
      {steps : List (DecisionTree.PathStep n)}
      (found : formula.firstSurviving rho = some term)
      (support_eq : liveSupport term rho = indices)
      (nonempty : indices ≠ [])
      (block : CanonicalBlockTrace formula term rho indices steps) :
      CanonicalTrace formula rho steps

/-- The part of a canonical transcript currently querying one source term.
The final constructor returns to `CanonicalTrace`, which selects the next
source term after the completed block assignment. -/
inductive CanonicalBlockTrace (formula : DNF n) :
    Term n → PartialAssignment n → List (Fin n) →
      List (DecisionTree.PathStep n) → Type
  /-- A requested path prefix may stop in the middle of a query block. -/
  | nil
      (rho : PartialAssignment n)
      (index : Fin n)
      (rest : List (Fin n)) :
      CanonicalBlockTrace formula term rho (index :: rest) []
  /-- Consume a query when more variables remain in the current term. -/
  | takeMore
      {rho : PartialAssignment n}
      {index next : Fin n}
      {rest : List (Fin n)}
      {value : Bool}
      {steps : List (DecisionTree.PathStep n)}
      (tail : CanonicalBlockTrace formula term
        (rho.refine (PartialAssignment.fix index value))
        (next :: rest) steps) :
      CanonicalBlockTrace formula term rho (index :: next :: rest)
        (⟨index, value⟩ :: steps)
  /-- Consume the last query of a block and restart canonical term selection.
  -/
  | takeLast
      {rho : PartialAssignment n}
      {index : Fin n}
      {value : Bool}
      {steps : List (DecisionTree.PathStep n)}
      (tail : CanonicalTrace formula
        (rho.refine (PartialAssignment.fix index value)) steps) :
      CanonicalBlockTrace formula term rho [index]
        (⟨index, value⟩ :: steps)

end

private theorem canonicalBlockTrace_of_queryRemaining_path
    (formula : DNF n)
    (term : Term n)
    (indices : List (Fin n))
    (indicesNonempty : indices ≠ [])
    (rho : PartialAssignment n)
    (bound : Nat)
    (below : rho.liveCount < bound)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < bound → DecisionTree n)
    {steps : List (DecisionTree.PathStep n)}
    {endpoint : DecisionTree n}
    (path : DecisionTree.Path
      (queryRemainingBelow indices rho bound below recurse) steps endpoint)
    (recurseTrace : ∀ sigma below steps endpoint,
      DecisionTree.Path (recurse sigma below) steps endpoint →
        Nonempty (CanonicalTrace formula sigma steps)) :
    Nonempty (CanonicalBlockTrace formula term rho indices steps) := by
  induction indices generalizing rho below steps endpoint with
  | nil => contradiction
  | cons index rest inductionHypothesis =>
      simp only [queryRemainingBelow] at path
      cases path with
      | nil => exact ⟨CanonicalBlockTrace.nil rho index rest⟩
      | takeFalse tail =>
          cases rest with
          | nil =>
              have trace := recurseTrace
                (rho.refine (PartialAssignment.fix index false))
                ((PartialAssignment.liveCount_refine_le_left rho
                  (PartialAssignment.fix index false)).trans_lt below)
                _ _ (by simpa [queryRemainingBelow] using tail)
              exact ⟨CanonicalBlockTrace.takeLast trace.some⟩
          | cons next remaining =>
              have block := inductionHypothesis (by simp)
                (rho.refine (PartialAssignment.fix index false))
                ((PartialAssignment.liveCount_refine_le_left rho
                  (PartialAssignment.fix index false)).trans_lt below) tail
              exact ⟨CanonicalBlockTrace.takeMore block.some⟩
      | takeTrue tail =>
          cases rest with
          | nil =>
              have trace := recurseTrace
                (rho.refine (PartialAssignment.fix index true))
                ((PartialAssignment.liveCount_refine_le_left rho
                  (PartialAssignment.fix index true)).trans_lt below)
                _ _ (by simpa [queryRemainingBelow] using tail)
              exact ⟨CanonicalBlockTrace.takeLast trace.some⟩
          | cons next remaining =>
              have block := inductionHypothesis (by simp)
                (rho.refine (PartialAssignment.fix index true))
                ((PartialAssignment.liveCount_refine_le_left rho
                  (PartialAssignment.fix index true)).trans_lt below) tail
              exact ⟨CanonicalBlockTrace.takeMore block.some⟩

private theorem canonicalBlockTrace_of_supportStep_path
    (formula : DNF n)
    (term : Term n)
    (rho : PartialAssignment n)
    (recurse : (sigma : PartialAssignment n) →
      sigma.liveCount < rho.liveCount → DecisionTree n)
    (indices : List (Fin n))
    (allLive : ∀ index, index ∈ indices → rho index = none)
    (indicesNonempty : indices ≠ [])
    {steps : List (DecisionTree.PathStep n)}
    {endpoint : DecisionTree n}
    (path : DecisionTree.Path
      (canonicalSupportStep formula rho recurse indices allLive)
      steps endpoint)
    (recurseTrace : ∀ sigma below steps endpoint,
      DecisionTree.Path (recurse sigma below) steps endpoint →
        Nonempty (CanonicalTrace formula sigma steps)) :
    Nonempty (CanonicalBlockTrace formula term rho indices steps) := by
  cases indices with
  | nil => contradiction
  | cons index rest =>
      simp only [canonicalSupportStep] at path
      cases path with
      | nil => exact ⟨CanonicalBlockTrace.nil rho index rest⟩
      | takeFalse tail =>
          have indexLive : rho index = none := allLive index (by simp)
          cases rest with
          | nil =>
              have trace := recurseTrace
                (rho.refine (PartialAssignment.fix index false))
                (PartialAssignment.liveCount_refine_fix_lt_of_live
                  rho index false indexLive)
                _ _ (by simpa [queryRemainingBelow] using tail)
              exact ⟨CanonicalBlockTrace.takeLast trace.some⟩
          | cons next remaining =>
              have block := canonicalBlockTrace_of_queryRemaining_path
                formula term (next :: remaining) (by simp)
                (rho.refine (PartialAssignment.fix index false)) rho.liveCount
                (PartialAssignment.liveCount_refine_fix_lt_of_live
                  rho index false indexLive)
                recurse tail recurseTrace
              exact ⟨CanonicalBlockTrace.takeMore block.some⟩
      | takeTrue tail =>
          have indexLive : rho index = none := allLive index (by simp)
          cases rest with
          | nil =>
              have trace := recurseTrace
                (rho.refine (PartialAssignment.fix index true))
                (PartialAssignment.liveCount_refine_fix_lt_of_live
                  rho index true indexLive)
                _ _ (by simpa [queryRemainingBelow] using tail)
              exact ⟨CanonicalBlockTrace.takeLast trace.some⟩
          | cons next remaining =>
              have block := canonicalBlockTrace_of_queryRemaining_path
                formula term (next :: remaining) (by simp)
                (rho.refine (PartialAssignment.fix index true)) rho.liveCount
                (PartialAssignment.liveCount_refine_fix_lt_of_live
                  rho index true indexLive)
                recurse tail recurseTrace
              exact ⟨CanonicalBlockTrace.takeMore block.some⟩

/-- Every path through the canonical decision tree carries a source-term block
trace matching the canonical selection procedure. -/
theorem canonicalTrace_of_path
    (formula : DNF n)
    (rho : PartialAssignment n)
    {steps : List (DecisionTree.PathStep n)}
    {endpoint : DecisionTree n}
    (path : DecisionTree.Path (formula.canonicalDecisionTree rho)
      steps endpoint) :
    Nonempty (CanonicalTrace formula rho steps) := by
  induction rho using
      (invImage PartialAssignment.liveCount Nat.lt_wfRel).wf.induction
      generalizing steps endpoint with
  | h rho inductionHypothesis =>
      rw [canonicalDecisionTree.eq_def] at path
      cases found : formula.firstSurviving rho with
      | none =>
          have leafPath : DecisionTree.Path (.leaf false) steps endpoint := by
            simpa [canonicalDecisionTreeStep, found] using path
          cases leafPath
          exact ⟨CanonicalTrace.nil rho⟩
      | some term =>
          cases support : liveSupport term rho with
          | nil =>
              have stepEqual :
                  canonicalSupportStep formula rho
                    (fun sigma _ => formula.canonicalDecisionTree sigma)
                    (liveSupport term rho)
                    (fun current present =>
                      (mem_liveSupport term rho current).1 present |>.2) =
                    .leaf true := by
                calc
                  _ = canonicalSupportStep formula rho
                        (fun sigma _ => formula.canonicalDecisionTree sigma)
                        [] (by simp) :=
                    canonicalSupportStep_congr formula rho _ _ _ _ _ support
                  _ = .leaf true := by rfl
              have leafPath : DecisionTree.Path (.leaf true) steps endpoint := by
                simp only [canonicalDecisionTreeStep, found] at path
                rw [stepEqual] at path
                exact path
              cases leafPath
              exact ⟨CanonicalTrace.nil rho⟩
          | cons index rest =>
              have allLive : ∀ current,
                  current ∈ index :: rest → rho current = none := by
                intro current present
                exact (mem_liveSupport term rho current).1 (by
                  simpa [support] using present) |>.2
              have supportPath : DecisionTree.Path
                  (canonicalSupportStep formula rho
                    (fun sigma _ => formula.canonicalDecisionTree sigma)
                    (index :: rest) allLive) steps endpoint := by
                simpa [canonicalDecisionTreeStep, found, support] using path
              have block := canonicalBlockTrace_of_supportStep_path
                formula term rho
                (fun sigma _ => formula.canonicalDecisionTree sigma)
                (index :: rest) allLive (by simp) supportPath
                (fun sigma below _ _ tail =>
                  inductionHypothesis sigma below tail)
              exact ⟨CanonicalTrace.start found support (by simp) block.some⟩

/-- The canonical tree computes exactly the DNF under the supplied partial
assignment. -/
theorem canonicalDecisionTree_computes
    (formula : DNF n)
    (rho : PartialAssignment n) :
    (formula.canonicalDecisionTree rho).Computes
      fun input => formula.eval (rho.apply input) := by
  induction rho using
      (invImage PartialAssignment.liveCount Nat.lt_wfRel).wf.induction with
  | h rho inductionHypothesis =>
      rw [canonicalDecisionTree.eq_def]
      cases found : formula.firstSurviving rho with
      | none =>
          intro input
          simp only [canonicalDecisionTreeStep, found,
            DecisionTree.eval_leaf]
          exact (eval_apply_eq_false_of_firstSurviving_eq_none
            formula rho input found).symm
      | some term =>
          simp only [canonicalDecisionTreeStep, found]
          apply canonicalSupportStep_computes
          · exact nodup_liveSupport term rho
          · intro sigma below
            exact inductionHypothesis sigma below
          · exact eval_apply_eq_true_of_firstSurviving_liveSupport_eq_nil
              formula rho found

/-- The canonical tree never queries more coordinates than remain live. -/
theorem depth_canonicalDecisionTree_le_liveCount
    (formula : DNF n)
    (rho : PartialAssignment n) :
    (formula.canonicalDecisionTree rho).depth ≤ rho.liveCount := by
  induction rho using
      (invImage PartialAssignment.liveCount Nat.lt_wfRel).wf.induction with
  | h rho inductionHypothesis =>
      rw [canonicalDecisionTree.eq_def]
      cases found : formula.firstSurviving rho with
      | none => simp [canonicalDecisionTreeStep, found]
      | some term =>
          have allLive : ∀ index, index ∈ liveSupport term rho →
              rho index = none := by
            intro index present
            exact (mem_liveSupport term rho index).1 present |>.2
          simpa only [canonicalDecisionTreeStep, found] using
            depth_canonicalSupportStep_le_liveCount formula rho
              (fun sigma _ => formula.canonicalDecisionTree sigma)
              (liveSupport term rho) allLive (nodup_liveSupport term rho)
              (fun sigma below => inductionHypothesis sigma below)

/-- Every canonical root-to-leaf path queries each initially live coordinate
at most once. -/
theorem canonicalDecisionTree_readOnceWithin
    (formula : DNF n)
    (rho : PartialAssignment n) :
    (formula.canonicalDecisionTree rho).ReadOnceWithin rho.liveVariables := by
  induction rho using
      (invImage PartialAssignment.liveCount Nat.lt_wfRel).wf.induction with
  | h rho inductionHypothesis =>
      rw [canonicalDecisionTree.eq_def]
      cases found : formula.firstSurviving rho with
      | none => simp [canonicalDecisionTreeStep, found,
          DecisionTree.ReadOnceWithin]
      | some term =>
          have allLive : ∀ index, index ∈ liveSupport term rho →
              rho index = none := by
            intro index present
            exact (mem_liveSupport term rho index).1 present |>.2
          simpa only [canonicalDecisionTreeStep, found] using
            canonicalSupportStep_readOnceWithin formula rho
              (fun sigma _ => formula.canonicalDecisionTree sigma)
              (liveSupport term rho) allLive (nodup_liveSupport term rho)
              (fun sigma below => inductionHypothesis sigma below)

/-- Every finite canonical path has distinct queried coordinates, all of which
were live before the path began. -/
theorem canonicalPath_indices_nodup_and_subset_live
    (formula : DNF n)
    (rho : PartialAssignment n)
    {steps : List (DecisionTree.PathStep n)}
    {endpoint : DecisionTree n}
    (path : DecisionTree.Path (formula.canonicalDecisionTree rho)
      steps endpoint) :
    (DecisionTree.PathStep.indices steps).Nodup ∧
      (DecisionTree.PathStep.indices steps).toFinset ⊆ rho.liveVariables :=
  path.indices_nodup_and_subset_of_readOnceWithin
    (formula.canonicalDecisionTree_readOnceWithin rho)

/-- The numeric depth of the distinguished canonical tree. -/
def canonicalDepth
    (formula : DNF n)
    (rho : PartialAssignment n) : Nat :=
  (formula.canonicalDecisionTree rho).depth

/-- Canonical depth is bounded by the number of live variables. -/
theorem canonicalDepth_le_liveCount
    (formula : DNF n)
    (rho : PartialAssignment n) :
    formula.canonicalDepth rho ≤ rho.liveCount :=
  depth_canonicalDecisionTree_le_liveCount formula rho

/-- The concrete bad event counted by the canonical switching argument. -/
def CanonicalDepthAtLeast
    (formula : DNF n)
    (rho : PartialAssignment n)
    (threshold : Nat) : Prop :=
  threshold ≤ formula.canonicalDepth rho

/-- An exact-length prefix of a path through a canonical DNF decision tree. -/
structure CanonicalPath
    (formula : DNF n)
    (rho : PartialAssignment n)
    (length : Nat) where
  /-- Query-and-answer transcript. -/
  steps : List (DecisionTree.PathStep n)
  /-- Subtree reached after the transcript. -/
  endpoint : DecisionTree n
  /-- The transcript follows the canonical tree. -/
  follows : DecisionTree.Path (formula.canonicalDecisionTree rho)
    steps endpoint
  /-- The transcript has the requested exact length. -/
  length_steps : steps.length = length

/-- A canonical-depth event supplies an exact-length canonical path prefix. -/
theorem exists_canonicalPath
    (formula : DNF n)
    (rho : PartialAssignment n)
    (length : Nat)
    (deep : formula.CanonicalDepthAtLeast rho length) :
    Nonempty (CanonicalPath formula rho length) := by
  obtain ⟨steps, endpoint, follows, stepsLength⟩ :=
    DecisionTree.exists_path_of_length_le_depth
      (formula.canonicalDecisionTree rho) length deep
  exact ⟨⟨steps, endpoint, follows, stepsLength⟩⟩

/-- Canonical path coordinates contain no duplicates. -/
theorem CanonicalPath.indices_nodup
    {formula : DNF n}
    {rho : PartialAssignment n}
    {length : Nat}
    (path : CanonicalPath formula rho length) :
    (DecisionTree.PathStep.indices path.steps).Nodup :=
  (formula.canonicalPath_indices_nodup_and_subset_live rho path.follows).1

/-- Every canonical path coordinate was live at the path's initial
restriction. -/
theorem CanonicalPath.indices_subset_live
    {formula : DNF n}
    {rho : PartialAssignment n}
    {length : Nat}
    (path : CanonicalPath formula rho length) :
    (DecisionTree.PathStep.indices path.steps).toFinset ⊆
      rho.liveVariables :=
  (formula.canonicalPath_indices_nodup_and_subset_live rho path.follows).2

/-- The assignment carried by an exact canonical path fixes exactly the path
length. -/
theorem CanonicalPath.assignment_fixedCount
    {formula : DNF n}
    {rho : PartialAssignment n}
    {length : Nat}
    (path : CanonicalPath formula rho length) :
    (DecisionTree.PathStep.assignment path.steps).fixedCount = length := by
  rw [DecisionTree.PathStep.fixedCount_assignment_eq_length path.steps
    path.indices_nodup, path.length_steps]

/-- The assignment carried by a canonical path fixes only variables live at
the path's initial restriction. -/
theorem CanonicalPath.assignment_fixesOnlyLive
    {formula : DNF n}
    {rho : PartialAssignment n}
    {length : Nat}
    (path : CanonicalPath formula rho length) :
    (DecisionTree.PathStep.assignment path.steps).fixedVariables ⊆
      rho.liveVariables := by
  rw [DecisionTree.PathStep.fixedVariables_assignment]
  exact path.indices_subset_live

instance canonicalDepthAtLeastDecidable
    (formula : DNF n)
    (rho : PartialAssignment n)
    (threshold : Nat) :
    Decidable (formula.CanonicalDepthAtLeast rho threshold) :=
  by
    unfold CanonicalDepthAtLeast canonicalDepth
    infer_instance

/-- The canonical tree also computes the syntactically restricted DNF. -/
theorem canonicalDecisionTree_computes_restrict
    (formula : DNF n)
    (rho : PartialAssignment n) :
    (formula.canonicalDecisionTree rho).Computes
      (formula.restrict rho).eval := by
  intro input
  calc
    (formula.canonicalDecisionTree rho).eval input =
        formula.eval (rho.apply input) :=
      formula.canonicalDecisionTree_computes rho input
    _ = (formula.restrict rho).eval input :=
      (restrict_sound formula rho input).symm

/-- The canonical tree witnesses an ordinary decision-tree upper bound for the
restricted DNF. -/
theorem depthAtMost_restrict_canonical
    (formula : DNF n)
    (rho : PartialAssignment n) :
    DecisionTree.DepthAtMost (formula.restrict rho).eval
      (formula.canonicalDepth rho) :=
  ⟨formula.canonicalDecisionTree rho,
    formula.canonicalDecisionTree_computes_restrict rho, le_rfl⟩

/-- If every tree for the restricted function has depth at least `threshold`,
then the canonical tree does too. This relates the concrete switching event to
the representation-independent lower-depth predicate. -/
theorem canonicalDepthAtLeast_of_depthAtLeast
    (formula : DNF n)
    (rho : PartialAssignment n)
    (threshold : Nat)
    (lower : DecisionTree.DepthAtLeast
      (formula.restrict rho).eval threshold) :
    formula.CanonicalDepthAtLeast rho threshold := by
  exact lower (formula.canonicalDecisionTree rho)
    (formula.canonicalDecisionTree_computes_restrict rho)

/-- At the empty restriction, the canonical tree computes the original DNF. -/
theorem canonicalDecisionTree_empty_computes
    (formula : DNF n) :
    (formula.canonicalDecisionTree PartialAssignment.empty).Computes
      formula.eval := by
  simpa using formula.canonicalDecisionTree_computes
    (PartialAssignment.empty : PartialAssignment n)

end DNF

end AC0
end Algebraic
