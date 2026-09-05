/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AC0.Iteration.Defs
public import Complexitylib.Circuits.AC0.Switching.Internal
public import Complexitylib.Circuits.DecisionTree.NormalForm.Internal
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Complexitylib.Circuits.AC0.NormalForm.Internal

/-!
# Iterated switching for AC0 formulas -- proof internals
-/


public section

namespace Complexity

namespace Switching

attribute [local instance] Classical.propDecidable

-- The signature mirrors the family this belongs to; the argument is part of
-- that shape even where this member does not consult it.
@[nolint unusedArguments]
private def finiteEventCount {α : Type} [Fintype α]
    [DecidableEq α] (event : α → Prop)
    [DecidablePred event] : ℕ :=
  (Finset.univ.filter event).card

private theorem finiteEventCount_mono
    {α : Type} [Fintype α] [DecidableEq α]
    (left right : α → Prop)
    [DecidablePred left] [DecidablePred right]
    (himp : ∀ value, left value → right value) :
    finiteEventCount left ≤ finiteEventCount right := by
  apply Finset.card_le_card
  intro value hvalue
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvalue ⊢
  exact himp value hvalue

private theorem finiteEventCount_or_le_add
    {α : Type} [Fintype α] [DecidableEq α]
    (left right : α → Prop)
    [DecidablePred left] [DecidablePred right] :
    finiteEventCount (fun value => left value ∨ right value) ≤
      finiteEventCount left + finiteEventCount right := by
  unfold finiteEventCount
  have heq :
      Finset.univ.filter (fun value => left value ∨ right value) =
        Finset.univ.filter left ∪ Finset.univ.filter right := by
    ext value
    simp
  rw [heq]
  exact Finset.card_union_le
    (Finset.univ.filter left) (Finset.univ.filter right)

private theorem finiteEventCount_prod
    {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (event : α → β → Prop)
    [∀ first, DecidablePred (event first)] :
    finiteEventCount
        (fun pair : α × β => event pair.1 pair.2) =
      ∑ first, finiteEventCount (event first) := by
  simp only [finiteEventCount]
  calc
    (Finset.univ.filter
        (fun pair : α × β => event pair.1 pair.2)).card =
      Fintype.card {pair : α × β // event pair.1 pair.2} := by
        rw [Fintype.card_subtype]
    _ = Fintype.card
        ((first : α) × {second : β // event first second}) :=
      Fintype.card_congr
        (Equiv.subtypeProdEquivSigmaSubtype event)
    _ = ∑ first,
        Fintype.card {second : β // event first second} := by
      rw [Fintype.card_sigma]
    _ = ∑ first,
        (Finset.univ.filter (event first)).card := by
      apply Finset.sum_congr rfl
      intro first _
      rw [Fintype.card_subtype]

private theorem finiteEventCount_prod_mul_le
    {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (event : α → β → Prop)
    [∀ first, DecidablePred (event first)]
    (multiplier bound : ℕ)
    (hbound :
      ∀ first,
        finiteEventCount (event first) * multiplier ≤ bound) :
    finiteEventCount
          (fun pair : α × β => event pair.1 pair.2) *
        multiplier ≤
      Fintype.card α * bound := by
  rw [finiteEventCount_prod, Finset.sum_mul]
  calc
    (∑ first,
        finiteEventCount (event first) * multiplier) ≤
      ∑ _first : α, bound := by
        exact Finset.sum_le_sum fun first _ => hbound first
    _ = Fintype.card α * bound := by simp

private theorem finiteEventCount_prod_left
    {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (event : α → Prop) [DecidablePred event] :
    finiteEventCount
        (fun pair : α × β => event pair.1) =
      finiteEventCount event * Fintype.card β := by
  have hprod := finiteEventCount_prod
    (fun first : α => fun _second : β => event first)
  rw [hprod]
  calc
    (∑ first,
        finiteEventCount fun _second : β => event first) =
      ∑ first,
        if event first then Fintype.card β else 0 := by
          apply Finset.sum_congr rfl
          intro first _
          by_cases hfirst : event first <;>
            simp [finiteEventCount, hfirst]
    _ = ∑ first ∈ Finset.univ.filter event,
        Fintype.card β := by
          rw [Finset.sum_filter]
    _ = finiteEventCount event * Fintype.card β := by
          simp [finiteEventCount]

-- The signature mirrors the family this belongs to; the argument is part of
-- that shape even where this member does not consult it.
@[nolint unusedArguments]
private theorem finiteEventCount_exists_mem_le_sum
    {α β : Type} [Fintype α] [DecidableEq α]
    [DecidableEq β] (values : List β)
    (event : β → α → Prop)
    [∀ value, DecidablePred (event value)] :
    finiteEventCount (fun sample =>
        ∃ value ∈ values, event value sample) ≤
      (values.map fun value =>
        finiteEventCount (event value)).sum := by
  induction values with
  | nil => simp [finiteEventCount]
  | cons value values ih =>
      calc
        finiteEventCount (fun sample =>
            ∃ found ∈ value :: values, event found sample) =
          finiteEventCount (fun sample =>
            event value sample ∨
              ∃ found ∈ values, event found sample) := by
                congr 1
                funext sample
                simp
        _ ≤ finiteEventCount (event value) +
            finiteEventCount (fun sample =>
              ∃ found ∈ values, event found sample) :=
          finiteEventCount_or_le_add _ _
        _ ≤ finiteEventCount (event value) +
            (values.map fun found =>
              finiteEventCount (event found)).sum :=
          Nat.add_le_add_left ih _
        _ = ((value :: values).map fun found =>
              finiteEventCount (event found)).sum := by
          simp

private theorem exists_not_event_of_weight_sum
    {α : Type} [Fintype α] [DecidableEq α]
    (event : α → Prop) [DecidablePred event]
    (weight : α → ℕ) (cap threshold : ℕ)
    (hcap : ∀ value, weight value ≤ cap)
    (haverage :
      Fintype.card α * threshold +
          finiteEventCount event * cap <
        ∑ value, weight value) :
    ∃ value, ¬event value ∧ threshold ≤ weight value := by
  by_contra hnone
  push Not at hnone
  have hpointwise :
      ∀ value,
        weight value ≤
          threshold + if event value then cap else 0 := by
    intro value
    by_cases hevent : event value
    · exact (hcap value).trans (by simp [hevent])
    · have hlow := hnone value hevent
      simp only [hevent, ↓reduceIte, Nat.add_zero]
      omega
  have hsum :
      (∑ value, weight value) ≤
        ∑ value,
          (threshold + if event value then cap else 0) :=
    Finset.sum_le_sum fun value _ => hpointwise value
  have hrhs :
      (∑ value,
          (threshold + if event value then cap else 0)) =
        Fintype.card α * threshold +
          finiteEventCount event * cap := by
    rw [Finset.sum_add_distrib]
    congr 1
    · simp [Nat.mul_comm]
    · calc
        (∑ value, if event value then cap else 0) =
            ∑ value ∈ Finset.univ.filter event, cap := by
          rw [Finset.sum_filter]
        _ = finiteEventCount event * cap := by
          simp [finiteEventCount]
  rw [hrhs] at hsum
  omega

end Switching

namespace RandomRestriction

theorem card_stageSeed_internal (N q stageCount : ℕ) :
    Fintype.card (StageSeed N q stageCount) =
      ((2 * q + 1) ^ N) ^ stageCount := by
  induction stageCount with
  | zero => simp [StageSeed]
  | succ stageCount ih =>
      change Fintype.card
        (StageSeed N q stageCount × Seed N q) = _
      rw [Fintype.card_prod, ih, card_seed_internal, pow_succ]

private theorem sum_comp_freeVariables_internal
    (prior : Restriction.On N) :
    ∑ seed : Seed N q,
        (Restriction.On.comp prior
          (decode seed)).freeVariables.card =
      prior.freeVariables.card *
        (2 * q + 1) ^ (N - 1) := by
  calc
    (∑ seed : Seed N q,
        (Restriction.On.comp prior
          (decode seed)).freeVariables.card) =
      ∑ seed : Seed N q, ∑ index : Fin N,
        if (Restriction.On.comp prior (decode seed)) index = none
        then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro seed _
          rw [Restriction.On.freeVariables,
            Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ index : Fin N, ∑ seed : Seed N q,
        if (Restriction.On.comp prior (decode seed)) index = none
        then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ index : Fin N,
        if prior index = none then
          (2 * q + 1) ^ (N - 1)
        else 0 := by
          apply Finset.sum_congr rfl
          intro index _
          by_cases hprior : prior index = none
          · simp only [Restriction.On.comp, hprior,
              Option.none_or, ite_eq_left]
            calc
              (∑ seed : Seed N q,
                  if decode seed index = none then 1 else 0) =
                (Finset.univ.filter fun seed : Seed N q =>
                  decode seed index = none).card := by
                    rw [← Finset.sum_filter]
                    simp
              _ = _ :=
                eventCount_coordinate_free_internal q index
          · cases hvalue : prior index with
            | none => exact (hprior hvalue).elim
            | some value =>
                simp [Restriction.On.comp, hvalue]
    _ = prior.freeVariables.card *
        (2 * q + 1) ^ (N - 1) := by
          rw [← Finset.sum_filter]
          simp [Restriction.On.freeVariables]

private theorem stageFreeSum_succ_internal
    (N q stageCount : ℕ) :
    stageFreeSum N q (stageCount + 1) =
      stageFreeSum N q stageCount *
        (2 * q + 1) ^ (N - 1) := by
  unfold stageFreeSum
  change (∑ seeds : StageSeed N q stageCount × Seed N q,
    (finalRestriction (stageCount := stageCount + 1)
      (q := q) seeds).freeVariables.card) = _
  rw [Fintype.sum_prod_type]
  simp only [finalRestriction, decodeStages,
    Switching.RestrictionStages.cumulative]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro prior _
  exact sum_comp_freeVariables_internal
    (Switching.RestrictionStages.cumulative stageCount
      (decodeStages prior))

/-- Exact first moment of the number of coordinates surviving every sparse
restriction stage. -/
theorem stageFreeSum_internal (N q stageCount : ℕ) :
    stageFreeSum N q stageCount =
      N * ((2 * q + 1) ^ (N - 1)) ^ stageCount := by
  induction stageCount with
  | zero =>
      simp [stageFreeSum, StageSeed, finalRestriction,
        Switching.RestrictionStages.cumulative,
        Restriction.On.freeVariables]
      erw [Finset.card_univ, Fintype.card_unit, one_mul]
  | succ stageCount ih =>
      rw [stageFreeSum_succ_internal, ih, pow_succ]
      simp [Nat.mul_assoc]

end RandomRestriction

namespace DNF

private theorem eval_switchingDecisionTreeUnder_internal
    (formula : DNF N) (restriction : Restriction.On N)
    (input : BitString N) :
    (formula.switchingDecisionTreeUnder restriction).eval input =
      formula.eval (restriction.applyTo input) := by
  rw [switchingDecisionTreeUnder_eq_internal,
    eval_switchingDecisionTree_internal, eval_restrict]

end DNF

namespace CNF

private theorem eval_switchingDecisionTreeUnder_internal
    (formula : CNF N) (restriction : Restriction.On N)
    (input : BitString N) :
    (formula.switchingDecisionTreeUnder restriction).eval input =
      formula.eval (restriction.applyTo input) := by
  rw [switchingDecisionTreeUnder_eq_internal,
    eval_switchingDecisionTree_internal, eval_restrict]

end CNF

namespace AC0Formula

theorem depth_baseDecisionTree_le_one_internal
    (formula : AC0Formula N) :
    formula.baseDecisionTree.depth ≤ 1 := by
  cases formula with
  | const value => simp [baseDecisionTree, DecisionTree.On.depth]
  | lit literal =>
      rcases literal with ⟨var, polarity⟩
      cases polarity <;>
        simp [baseDecisionTree, DecisionTree.On.depth]
  | and children =>
      simp [baseDecisionTree, DecisionTree.On.depth]
  | or children =>
      simp [baseDecisionTree, DecisionTree.On.depth]

private theorem eval_baseDecisionTree_internal
    (formula : AC0Formula N) (hdepth : formula.depth ≤ 0)
    (input : BitString N) :
    formula.baseDecisionTree.eval input = formula.eval input := by
  cases formula with
  | const value => rfl
  | lit literal =>
      cases literal with
      | mk var polarity =>
          cases polarity <;>
            simp [baseDecisionTree, DecisionTree.On.eval,
              eval, Literal.eval]
  | and children => simp [depth] at hdepth
  | or children => simp [depth] at hdepth

theorem eval_stagedDecisionTree_internal
    (stageCount : ℕ)
    (stages : Switching.RestrictionStages N stageCount)
    (formula : AC0Formula N)
    (hdepth : formula.depth ≤ stageCount)
    (input : BitString N) :
    (formula.stagedDecisionTree stageCount stages).eval input =
      formula.eval
        ((Switching.RestrictionStages.cumulative
          stageCount stages).applyTo input) := by
  induction stageCount generalizing formula input with
  | zero =>
      exact eval_baseDecisionTree_internal formula hdepth input
  | succ stageCount ih =>
      cases formula with
      | const value =>
          rw [stagedDecisionTree,
            DecisionTree.On.eval_restrict_internal,
            ih stages.2 (.const value) (by simp [depth])
              (stages.1.applyTo input)]
          rw [Switching.RestrictionStages.cumulative,
            Restriction.On.applyTo_comp]
      | lit literal =>
          rw [stagedDecisionTree,
            DecisionTree.On.eval_restrict_internal,
            ih stages.2 (.lit literal) (by simp [depth])
              (stages.1.applyTo input)]
          rw [Switching.RestrictionStages.cumulative,
            Restriction.On.applyTo_comp]
      | and children =>
          have hforest : forestDepth children ≤ stageCount := by
            simp only [depth] at hdepth
            omega
          have hall :
              ∀ formulas : List (AC0Formula N),
                (∀ child ∈ formulas,
                  child.depth ≤ stageCount) →
                (formulas.map
                    (stagedDecisionTree stageCount stages.2)).all
                    (fun tree =>
                      tree.eval (stages.1.applyTo input)) =
                  formulas.all
                    (eval
                      ((Switching.RestrictionStages.cumulative
                        stageCount stages.2).applyTo
                          (stages.1.applyTo input))) := by
            intro formulas hformulas
            induction formulas with
            | nil => rfl
            | cons child formulas ihformulas =>
                simp only [List.map_cons, List.all_cons]
                rw [ih stages.2 child
                  (hformulas child (by simp))
                  (stages.1.applyTo input)]
                rw [ihformulas (by
                  intro formula hmem
                  exact hformulas formula (by simp [hmem]))]
          have hchildren := hall children.toList (by
            intro child hmem
            exact
              (depth_le_forestDepth_of_mem child children hmem).trans
                hforest)
          rw [stagedDecisionTree,
            CNF.eval_switchingDecisionTreeUnder_internal,
            CNF.eval_consistentPart_internal,
            DecisionTree.On.eval_allCNF_internal, hchildren]
          rw [← evalAll_ofList_internal,
            AC0Forest.ofList_toList]
          rw [Switching.RestrictionStages.cumulative,
            Restriction.On.applyTo_comp]
          rfl
      | or children =>
          have hforest : forestDepth children ≤ stageCount := by
            simp only [depth] at hdepth
            omega
          have hany :
              ∀ formulas : List (AC0Formula N),
                (∀ child ∈ formulas,
                  child.depth ≤ stageCount) →
                (formulas.map
                    (stagedDecisionTree stageCount stages.2)).any
                    (fun tree =>
                      tree.eval (stages.1.applyTo input)) =
                  formulas.any
                    (eval
                      ((Switching.RestrictionStages.cumulative
                        stageCount stages.2).applyTo
                          (stages.1.applyTo input))) := by
            intro formulas hformulas
            induction formulas with
            | nil => rfl
            | cons child formulas ihformulas =>
                simp only [List.map_cons, List.any_cons]
                rw [ih stages.2 child
                  (hformulas child (by simp))
                  (stages.1.applyTo input)]
                rw [ihformulas (by
                  intro formula hmem
                  exact hformulas formula (by simp [hmem]))]
          have hchildren := hany children.toList (by
            intro child hmem
            exact
              (depth_le_forestDepth_of_mem child children hmem).trans
                hforest)
          rw [stagedDecisionTree,
            DNF.eval_switchingDecisionTreeUnder_internal,
            DNF.eval_consistentPart_internal,
            DecisionTree.On.eval_anyDNF_internal, hchildren]
          rw [← evalAny_ofList_internal,
            AC0Forest.ofList_toList]
          rw [Switching.RestrictionStages.cumulative,
            Restriction.On.applyTo_comp]
          rfl

theorem depth_stagedDecisionTree_const_le_one_internal
    (stageCount : ℕ)
    (stages : Switching.RestrictionStages N stageCount)
    (value : Bool) :
    ((AC0Formula.const value).stagedDecisionTree
      stageCount stages).depth ≤ 1 := by
  induction stageCount with
  | zero =>
      exact depth_baseDecisionTree_le_one_internal (.const value)
  | succ stageCount ih =>
      simp only [stagedDecisionTree]
      exact
        (DecisionTree.On.depth_restrict_le_internal stages.1 _).trans
          (ih stages.2)

theorem depth_stagedDecisionTree_lit_le_one_internal
    (stageCount : ℕ)
    (stages : Switching.RestrictionStages N stageCount)
    (literal : Literal N) :
    ((AC0Formula.lit literal).stagedDecisionTree
      stageCount stages).depth ≤ 1 := by
  induction stageCount with
  | zero =>
      exact depth_baseDecisionTree_le_one_internal (.lit literal)
  | succ stageCount ih =>
      simp only [stagedDecisionTree]
      exact
        (DecisionTree.On.depth_restrict_le_internal stages.1 _).trans
          (ih stages.2)

set_option maxHeartbeats 3000000 in
theorem stageEventCount_stagedBad_mul_pow_le_internal
    (formula : AC0Formula N)
    (stageCount queryCount q : ℕ)
    (hdepth : formula.depth ≤ stageCount)
    (hquery : 2 ≤ queryCount) :
    RandomRestriction.stageEventCount (q := q)
          (stagedBad (stageCount := stageCount)
            formula queryCount) *
        q ^ queryCount ≤
      formula.size *
        ((2 * q + 1) ^ N) ^ stageCount *
        (4 * (queryCount + 1)) ^ queryCount := by
  classical
  induction stageCount generalizing formula with
  | zero =>
      cases formula with
      | const value =>
          have hnot :
              ∀ stages : Switching.RestrictionStages N 0,
                ¬stagedBad (.const value) queryCount stages := by
            intro stages hbad
            exact (not_le_of_gt
              (lt_of_le_of_lt
                (depth_stagedDecisionTree_const_le_one_internal
                  0 stages value)
                hquery)) hbad
          simp [RandomRestriction.stageEventCount,
            hnot]
      | lit literal =>
          have hnot :
              ∀ stages : Switching.RestrictionStages N 0,
                ¬stagedBad (.lit literal) queryCount stages := by
            intro stages hbad
            exact (not_le_of_gt
              (lt_of_le_of_lt
                (depth_stagedDecisionTree_lit_le_one_internal
                  0 stages literal)
                hquery)) hbad
          simp [RandomRestriction.stageEventCount,
            hnot]
      | and children => simp [depth] at hdepth
      | or children => simp [depth] at hdepth
  | succ stageCount ih =>
      cases formula with
      | const value =>
          have hnot :
              ∀ stages :
                  Switching.RestrictionStages N (stageCount + 1),
                ¬stagedBad (.const value) queryCount stages := by
            intro stages hbad
            exact (not_le_of_gt
              (lt_of_le_of_lt
                (depth_stagedDecisionTree_const_le_one_internal
                  (stageCount + 1) stages value)
                hquery)) hbad
          simp [RandomRestriction.stageEventCount,
            hnot]
      | lit literal =>
          have hnot :
              ∀ stages :
                  Switching.RestrictionStages N (stageCount + 1),
                ¬stagedBad (.lit literal) queryCount stages := by
            intro stages hbad
            exact (not_le_of_gt
              (lt_of_le_of_lt
                (depth_stagedDecisionTree_lit_le_one_internal
                  (stageCount + 1) stages literal)
                hquery)) hbad
          simp [RandomRestriction.stageEventCount,
            hnot]
      | and children =>
          have hforest : forestDepth children ≤ stageCount := by
            simp only [depth] at hdepth
            omega
          let childEvent :
              AC0Formula N →
                RandomRestriction.StageSeed N q stageCount → Prop :=
            fun child prior =>
              stagedBad child queryCount
                (RandomRestriction.decodeStages prior)
          let childBad :
              RandomRestriction.StageSeed N q stageCount → Prop :=
            fun prior =>
              ∃ child ∈ children.toList, childEvent child prior
          have hchildUnion :
              Switching.finiteEventCount childBad ≤
                (children.toList.map fun child =>
                  Switching.finiteEventCount
                    (childEvent child)).sum := by
            simpa [childBad] using
              (Switching.finiteEventCount_exists_mem_le_sum
                children.toList childEvent)
          have hchild :
              Switching.finiteEventCount childBad *
                    q ^ queryCount ≤
                forestSize children *
                  ((2 * q + 1) ^ N) ^ stageCount *
                  (4 * (queryCount + 1)) ^ queryCount := by
            calc
              Switching.finiteEventCount childBad *
                    q ^ queryCount ≤
                  (children.toList.map fun child =>
                    Switching.finiteEventCount
                      (childEvent child)).sum *
                    q ^ queryCount :=
                Nat.mul_le_mul_right _ hchildUnion
              _ = (children.toList.map fun child =>
                    Switching.finiteEventCount
                        (childEvent child) *
                      q ^ queryCount).sum := by
                rw [List.sum_map_mul_right]
              _ ≤ (children.toList.map fun child =>
                    child.size *
                      ((2 * q + 1) ^ N) ^ stageCount *
                      (4 * (queryCount + 1)) ^
                        queryCount).sum := by
                apply List.sum_le_sum
                intro child hmem
                have hchildDepth :
                    child.depth ≤ stageCount :=
                  (depth_le_forestDepth_of_mem child children
                    hmem).trans hforest
                simpa [childEvent,
                  RandomRestriction.stageEventCount,
                  Switching.finiteEventCount] using
                    ih child hchildDepth
              _ = forestSize children *
                    ((2 * q + 1) ^ N) ^ stageCount *
                    (4 * (queryCount + 1)) ^
                      queryCount := by
                rw [show (children.toList.map fun child =>
                      child.size *
                        ((2 * q + 1) ^ N) ^ stageCount *
                        (4 * (queryCount + 1)) ^
                          queryCount).sum =
                    (children.toList.map size).sum *
                      (((2 * q + 1) ^ N) ^ stageCount *
                        (4 * (queryCount + 1)) ^
                          queryCount) by
                    simpa [Nat.mul_assoc] using
                      List.sum_map_mul_right children.toList size
                        (((2 * q + 1) ^ N) ^ stageCount *
                          (4 * (queryCount + 1)) ^
                            queryCount)]
                rw [← forestSize_ofList_internal,
                  AC0Forest.ofList_toList]
                simp [Nat.mul_assoc]
          let trees :
              RandomRestriction.StageSeed N q stageCount →
                List (DecisionTree.On N) :=
            fun prior =>
              children.toList.map
                (stagedDecisionTree stageCount
                  (RandomRestriction.decodeStages prior))
          let normal :
              RandomRestriction.StageSeed N q stageCount → CNF N :=
            fun prior => DecisionTree.On.allCNF (trees prior)
          let switchGood :
              RandomRestriction.StageSeed N q stageCount →
                RandomRestriction.Seed N q → Prop :=
            fun prior current =>
              ¬childBad prior ∧
                CNF.switchingBad (normal prior).consistentPart
                  queryCount
                  (RandomRestriction.decode current)
          have hconditional :
              ∀ prior,
                Switching.finiteEventCount (switchGood prior) *
                      q ^ queryCount ≤
                  (2 * q + 1) ^ N *
                    (4 * (queryCount + 1)) ^
                      queryCount := by
            intro prior
            by_cases hbad : childBad prior
            · simp [switchGood, hbad,
                Switching.finiteEventCount]
            · have hwidth : (normal prior).width ≤ queryCount := by
                apply
                  DecisionTree.On.width_allCNF_le_internal
                    (trees prior) queryCount
                intro tree htree
                rcases List.mem_map.mp htree with
                  ⟨child, hmem, rfl⟩
                have hnot :
                    ¬queryCount ≤
                      (stagedDecisionTree stageCount
                        (RandomRestriction.decodeStages prior)
                        child).depth := by
                  intro hdeep
                  exact hbad ⟨child, hmem, hdeep⟩
                omega
              have hswitch :=
                CNF.switchingBad_consistentPart_width_encoding_bound_internal
                  (normal prior) q queryCount
              have hweaken :
                  RandomRestriction.eventCount (q := q)
                        (CNF.switchingBad
                          (normal prior).consistentPart
                          queryCount) *
                      q ^ queryCount ≤
                    (2 * q + 1) ^ N *
                      (4 * (queryCount + 1)) ^
                        queryCount :=
                hswitch.trans
                  (Nat.mul_le_mul_left _
                    (Nat.pow_le_pow_left
                      (Nat.mul_le_mul_left 4
                        (Nat.add_le_add_right hwidth 1))
                      queryCount))
              simpa [switchGood, hbad,
                Switching.finiteEventCount,
                RandomRestriction.eventCount] using hweaken
          have hswitch :
              Switching.finiteEventCount
                    (fun pair :
                        RandomRestriction.StageSeed N q stageCount ×
                          RandomRestriction.Seed N q =>
                      switchGood pair.1 pair.2) *
                  q ^ queryCount ≤
                ((2 * q + 1) ^ N) ^ (stageCount + 1) *
                  (4 * (queryCount + 1)) ^
                    queryCount := by
            have hproduct :=
              Switching.finiteEventCount_prod_mul_le
                switchGood (q ^ queryCount)
                ((2 * q + 1) ^ N *
                  (4 * (queryCount + 1)) ^ queryCount)
                hconditional
            rw [RandomRestriction.card_stageSeed_internal] at hproduct
            simpa [pow_succ, Nat.mul_assoc] using hproduct
          let prefixPair :
              RandomRestriction.StageSeed N q stageCount ×
                RandomRestriction.Seed N q → Prop :=
            fun pair => childBad pair.1
          have hprefix :
              Switching.finiteEventCount prefixPair *
                    q ^ queryCount ≤
                forestSize children *
                  ((2 * q + 1) ^ N) ^ (stageCount + 1) *
                  (4 * (queryCount + 1)) ^
                    queryCount := by
            have hcount :
                Switching.finiteEventCount prefixPair =
                Switching.finiteEventCount childBad *
                    (2 * q + 1) ^ N := by
              simpa [prefixPair,
                RandomRestriction.card_seed_internal,
                Nat.mul_comm, Nat.add_comm] using
                (Switching.finiteEventCount_prod_left
                  (β := RandomRestriction.Seed N q) childBad)
            rw [hcount]
            have hmul :=
              Nat.mul_le_mul_right ((2 * q + 1) ^ N) hchild
            simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm,
              Nat.mul_left_comm] using hmul
          let rootEvent :
              RandomRestriction.StageSeed N q stageCount ×
                RandomRestriction.Seed N q → Prop :=
            fun pair =>
              stagedBad (.and children) queryCount
                (RandomRestriction.decodeStages
                  (stageCount := stageCount + 1) (q := q) pair)
          have hroot :
              Switching.finiteEventCount rootEvent ≤
                Switching.finiteEventCount prefixPair +
                  Switching.finiteEventCount
                    (fun pair :
                        RandomRestriction.StageSeed N q stageCount ×
                          RandomRestriction.Seed N q =>
                      switchGood pair.1 pair.2) := by
            calc
              Switching.finiteEventCount rootEvent ≤
                  Switching.finiteEventCount
                    (fun pair => prefixPair pair ∨
                      switchGood pair.1 pair.2) := by
                apply Switching.finiteEventCount_mono
                intro pair hdeep
                by_cases hbad : childBad pair.1
                · exact Or.inl hbad
                · exact Or.inr ⟨hbad, hdeep⟩
              _ ≤ Switching.finiteEventCount prefixPair +
                    Switching.finiteEventCount
                      (fun pair :
                          RandomRestriction.StageSeed N q stageCount ×
                            RandomRestriction.Seed N q =>
                        switchGood pair.1 pair.2) :=
                Switching.finiteEventCount_or_le_add prefixPair
                  (fun pair :
                      RandomRestriction.StageSeed N q stageCount ×
                        RandomRestriction.Seed N q =>
                    switchGood pair.1 pair.2)
          have hEq : RandomRestriction.stageEventCount (N := N) (stageCount := stageCount + 1) q
              ((and children).stagedBad queryCount) = Switching.finiteEventCount rootEvent := by
            unfold RandomRestriction.stageEventCount Switching.finiteEventCount
            congr 1
            congr 1
          rw [hEq]
          show _ ≤
              (1 + forestSize children) *
                ((2 * q + 1) ^ N) ^ (stageCount + 1) *
                (4 * (queryCount + 1)) ^ queryCount
          calc
            Switching.finiteEventCount rootEvent *
                  q ^ queryCount ≤
                (Switching.finiteEventCount prefixPair +
                    Switching.finiteEventCount
                      (fun pair :
                          RandomRestriction.StageSeed N q stageCount ×
                            RandomRestriction.Seed N q =>
                        switchGood pair.1 pair.2)) *
                  q ^ queryCount :=
              Nat.mul_le_mul_right _ hroot
            _ = Switching.finiteEventCount prefixPair *
                  q ^ queryCount +
                Switching.finiteEventCount
                    (fun pair :
                        RandomRestriction.StageSeed N q stageCount ×
                          RandomRestriction.Seed N q =>
                      switchGood pair.1 pair.2) *
                  q ^ queryCount := by
              rw [Nat.add_mul]
            _ ≤ forestSize children *
                    ((2 * q + 1) ^ N) ^ (stageCount + 1) *
                    (4 * (queryCount + 1)) ^ queryCount +
                  ((2 * q + 1) ^ N) ^ (stageCount + 1) *
                    (4 * (queryCount + 1)) ^ queryCount :=
              Nat.add_le_add hprefix hswitch
            _ = (1 + forestSize children) *
                  ((2 * q + 1) ^ N) ^ (stageCount + 1) *
                  (4 * (queryCount + 1)) ^ queryCount := by
              simp [Nat.add_mul, Nat.mul_assoc, Nat.add_comm]
      | or children =>
          have hforest : forestDepth children ≤ stageCount := by
            simp only [depth] at hdepth
            omega
          let childEvent :
              AC0Formula N →
                RandomRestriction.StageSeed N q stageCount → Prop :=
            fun child prior =>
              stagedBad child queryCount
                (RandomRestriction.decodeStages prior)
          let childBad :
              RandomRestriction.StageSeed N q stageCount → Prop :=
            fun prior =>
              ∃ child ∈ children.toList, childEvent child prior
          have hchildUnion :
              Switching.finiteEventCount childBad ≤
                (children.toList.map fun child =>
                  Switching.finiteEventCount
                    (childEvent child)).sum := by
            simpa [childBad] using
              (Switching.finiteEventCount_exists_mem_le_sum
                children.toList childEvent)
          have hchild :
              Switching.finiteEventCount childBad *
                    q ^ queryCount ≤
                forestSize children *
                  ((2 * q + 1) ^ N) ^ stageCount *
                  (4 * (queryCount + 1)) ^ queryCount := by
            calc
              Switching.finiteEventCount childBad *
                    q ^ queryCount ≤
                  (children.toList.map fun child =>
                    Switching.finiteEventCount
                      (childEvent child)).sum *
                    q ^ queryCount :=
                Nat.mul_le_mul_right _ hchildUnion
              _ = (children.toList.map fun child =>
                    Switching.finiteEventCount
                        (childEvent child) *
                      q ^ queryCount).sum := by
                rw [List.sum_map_mul_right]
              _ ≤ (children.toList.map fun child =>
                    child.size *
                      ((2 * q + 1) ^ N) ^ stageCount *
                      (4 * (queryCount + 1)) ^
                        queryCount).sum := by
                apply List.sum_le_sum
                intro child hmem
                have hchildDepth :
                    child.depth ≤ stageCount :=
                  (depth_le_forestDepth_of_mem child children
                    hmem).trans hforest
                simpa [childEvent,
                  RandomRestriction.stageEventCount,
                  Switching.finiteEventCount] using
                    ih child hchildDepth
              _ = forestSize children *
                    ((2 * q + 1) ^ N) ^ stageCount *
                    (4 * (queryCount + 1)) ^
                      queryCount := by
                rw [show (children.toList.map fun child =>
                      child.size *
                        ((2 * q + 1) ^ N) ^ stageCount *
                        (4 * (queryCount + 1)) ^
                          queryCount).sum =
                    (children.toList.map size).sum *
                      (((2 * q + 1) ^ N) ^ stageCount *
                        (4 * (queryCount + 1)) ^
                          queryCount) by
                    simpa [Nat.mul_assoc] using
                      List.sum_map_mul_right children.toList size
                        (((2 * q + 1) ^ N) ^ stageCount *
                          (4 * (queryCount + 1)) ^
                            queryCount)]
                rw [← forestSize_ofList_internal,
                  AC0Forest.ofList_toList]
                simp [Nat.mul_assoc]
          let trees :
              RandomRestriction.StageSeed N q stageCount →
                List (DecisionTree.On N) :=
            fun prior =>
              children.toList.map
                (stagedDecisionTree stageCount
                  (RandomRestriction.decodeStages prior))
          let normal :
              RandomRestriction.StageSeed N q stageCount → DNF N :=
            fun prior => DecisionTree.On.anyDNF (trees prior)
          let switchGood :
              RandomRestriction.StageSeed N q stageCount →
                RandomRestriction.Seed N q → Prop :=
            fun prior current =>
              ¬childBad prior ∧
                DNF.switchingBad (normal prior).consistentPart
                  queryCount
                  (RandomRestriction.decode current)
          have hconditional :
              ∀ prior,
                Switching.finiteEventCount (switchGood prior) *
                      q ^ queryCount ≤
                  (2 * q + 1) ^ N *
                    (4 * (queryCount + 1)) ^
                      queryCount := by
            intro prior
            by_cases hbad : childBad prior
            · simp [switchGood, hbad,
                Switching.finiteEventCount]
            · have hwidth : (normal prior).width ≤ queryCount := by
                apply
                  DecisionTree.On.width_anyDNF_le_internal
                    (trees prior) queryCount
                intro tree htree
                rcases List.mem_map.mp htree with
                  ⟨child, hmem, rfl⟩
                have hnot :
                    ¬queryCount ≤
                      (stagedDecisionTree stageCount
                        (RandomRestriction.decodeStages prior)
                        child).depth := by
                  intro hdeep
                  exact hbad ⟨child, hmem, hdeep⟩
                omega
              have hswitch :=
                DNF.switchingBad_consistentPart_width_encoding_bound_internal
                  (normal prior) q queryCount
              have hweaken :
                  RandomRestriction.eventCount (q := q)
                        (DNF.switchingBad
                          (normal prior).consistentPart
                          queryCount) *
                      q ^ queryCount ≤
                    (2 * q + 1) ^ N *
                      (4 * (queryCount + 1)) ^
                        queryCount :=
                hswitch.trans
                  (Nat.mul_le_mul_left _
                    (Nat.pow_le_pow_left
                      (Nat.mul_le_mul_left 4
                        (Nat.add_le_add_right hwidth 1))
                      queryCount))
              simpa [switchGood, hbad,
                Switching.finiteEventCount,
                RandomRestriction.eventCount] using hweaken
          have hswitch :
              Switching.finiteEventCount
                    (fun pair :
                        RandomRestriction.StageSeed N q stageCount ×
                          RandomRestriction.Seed N q =>
                      switchGood pair.1 pair.2) *
                  q ^ queryCount ≤
                ((2 * q + 1) ^ N) ^ (stageCount + 1) *
                  (4 * (queryCount + 1)) ^
                    queryCount := by
            have hproduct :=
              Switching.finiteEventCount_prod_mul_le
                switchGood (q ^ queryCount)
                ((2 * q + 1) ^ N *
                  (4 * (queryCount + 1)) ^ queryCount)
                hconditional
            rw [RandomRestriction.card_stageSeed_internal] at hproduct
            simpa [pow_succ, Nat.mul_assoc] using hproduct
          let prefixPair :
              RandomRestriction.StageSeed N q stageCount ×
                RandomRestriction.Seed N q → Prop :=
            fun pair => childBad pair.1
          have hprefix :
              Switching.finiteEventCount prefixPair *
                    q ^ queryCount ≤
                forestSize children *
                  ((2 * q + 1) ^ N) ^ (stageCount + 1) *
                  (4 * (queryCount + 1)) ^
                    queryCount := by
            have hcount :
                Switching.finiteEventCount prefixPair =
                Switching.finiteEventCount childBad *
                    (2 * q + 1) ^ N := by
              simpa [prefixPair,
                RandomRestriction.card_seed_internal,
                Nat.mul_comm, Nat.add_comm] using
                (Switching.finiteEventCount_prod_left
                  (β := RandomRestriction.Seed N q) childBad)
            rw [hcount]
            have hmul :=
              Nat.mul_le_mul_right ((2 * q + 1) ^ N) hchild
            simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm,
              Nat.mul_left_comm] using hmul
          let rootEvent :
              RandomRestriction.StageSeed N q stageCount ×
                RandomRestriction.Seed N q → Prop :=
            fun pair =>
              stagedBad (.or children) queryCount
                (RandomRestriction.decodeStages
                  (stageCount := stageCount + 1) (q := q) pair)
          have hroot :
              Switching.finiteEventCount rootEvent ≤
                Switching.finiteEventCount prefixPair +
                  Switching.finiteEventCount
                    (fun pair :
                        RandomRestriction.StageSeed N q stageCount ×
                          RandomRestriction.Seed N q =>
                      switchGood pair.1 pair.2) := by
            calc
              Switching.finiteEventCount rootEvent ≤
                  Switching.finiteEventCount
                    (fun pair => prefixPair pair ∨
                      switchGood pair.1 pair.2) := by
                apply Switching.finiteEventCount_mono
                intro pair hdeep
                by_cases hbad : childBad pair.1
                · exact Or.inl hbad
                · exact Or.inr ⟨hbad, hdeep⟩
              _ ≤ Switching.finiteEventCount prefixPair +
                    Switching.finiteEventCount
                      (fun pair :
                          RandomRestriction.StageSeed N q stageCount ×
                            RandomRestriction.Seed N q =>
                        switchGood pair.1 pair.2) :=
                Switching.finiteEventCount_or_le_add prefixPair
                  (fun pair :
                      RandomRestriction.StageSeed N q stageCount ×
                        RandomRestriction.Seed N q =>
                    switchGood pair.1 pair.2)
          have hEq : RandomRestriction.stageEventCount (N := N) (stageCount := stageCount + 1) q
              ((or children).stagedBad queryCount) = Switching.finiteEventCount rootEvent := by
            unfold RandomRestriction.stageEventCount Switching.finiteEventCount
            congr 1
            congr 1
          rw [hEq]
          show _ ≤
              (1 + forestSize children) *
                ((2 * q + 1) ^ N) ^ (stageCount + 1) *
                (4 * (queryCount + 1)) ^ queryCount
          calc
            Switching.finiteEventCount rootEvent *
                  q ^ queryCount ≤
                (Switching.finiteEventCount prefixPair +
                    Switching.finiteEventCount
                      (fun pair :
                          RandomRestriction.StageSeed N q stageCount ×
                            RandomRestriction.Seed N q =>
                        switchGood pair.1 pair.2)) *
                  q ^ queryCount :=
              Nat.mul_le_mul_right _ hroot
            _ = Switching.finiteEventCount prefixPair *
                  q ^ queryCount +
                Switching.finiteEventCount
                    (fun pair :
                        RandomRestriction.StageSeed N q stageCount ×
                          RandomRestriction.Seed N q =>
                      switchGood pair.1 pair.2) *
                  q ^ queryCount := by
              rw [Nat.add_mul]
            _ ≤ forestSize children *
                    ((2 * q + 1) ^ N) ^ (stageCount + 1) *
                    (4 * (queryCount + 1)) ^ queryCount +
                  ((2 * q + 1) ^ N) ^ (stageCount + 1) *
                    (4 * (queryCount + 1)) ^ queryCount :=
              Nat.add_le_add hprefix hswitch
            _ = (1 + forestSize children) *
                  ((2 * q + 1) ^ N) ^ (stageCount + 1) *
                  (4 * (queryCount + 1)) ^ queryCount := by
              simp [Nat.add_mul, Nat.mul_assoc, Nat.add_comm]

theorem exists_shallow_stagedDecisionTree_internal
    (formula : AC0Formula N)
    (stageCount queryCount q : ℕ)
    (haverage :
      ((2 * q + 1) ^ N) ^ stageCount * queryCount +
          RandomRestriction.stageEventCount (q := q)
            (stagedBad (stageCount := stageCount)
              formula queryCount) * N <
        RandomRestriction.stageFreeSum N q stageCount) :
    ∃ seeds : RandomRestriction.StageSeed N q stageCount,
      (formula.stagedDecisionTree stageCount
          (RandomRestriction.decodeStages seeds)).depth <
        queryCount ∧
      queryCount ≤
        (RandomRestriction.finalRestriction seeds).freeVariables.card := by
  let event :
      RandomRestriction.StageSeed N q stageCount → Prop :=
    fun seeds =>
      stagedBad formula queryCount
        (RandomRestriction.decodeStages seeds)
  let weight :
      RandomRestriction.StageSeed N q stageCount → ℕ :=
    fun seeds =>
      (RandomRestriction.finalRestriction seeds).freeVariables.card
  have haverage' :
      Fintype.card
            (RandomRestriction.StageSeed N q stageCount) *
          queryCount +
          Switching.finiteEventCount event * N <
        ∑ seeds, weight seeds := by
    rw [RandomRestriction.card_stageSeed_internal]
    simpa [event, weight,
      RandomRestriction.stageEventCount,
      Switching.finiteEventCount,
      RandomRestriction.stageFreeSum] using haverage
  obtain ⟨seeds, hgood, hfree⟩ :=
    Switching.exists_not_event_of_weight_sum
      event weight N queryCount
      (fun seed =>
        (Finset.card_le_univ
          (RandomRestriction.finalRestriction seed).freeVariables).trans_eq
          (Fintype.card_fin N))
      haverage'
  exact ⟨seeds, Nat.lt_of_not_ge hgood, hfree⟩

theorem exists_shallow_stagedDecisionTree_of_counting_internal
    (formula : AC0Formula N)
    (stageCount queryCount q : ℕ)
    (hdepth : formula.depth ≤ stageCount)
    (hquery : 2 ≤ queryCount) (hq : 0 < q)
    (hnumeric :
      (((2 * q + 1) ^ N) ^ stageCount * queryCount) *
            q ^ queryCount +
          formula.size *
              ((2 * q + 1) ^ N) ^ stageCount *
              (4 * (queryCount + 1)) ^ queryCount * N <
        (N * ((2 * q + 1) ^ (N - 1)) ^ stageCount) *
          q ^ queryCount) :
    ∃ seeds : RandomRestriction.StageSeed N q stageCount,
      (formula.stagedDecisionTree stageCount
          (RandomRestriction.decodeStages seeds)).depth <
        queryCount ∧
      queryCount ≤
        (RandomRestriction.finalRestriction seeds).freeVariables.card := by
  have hbad :=
    stageEventCount_stagedBad_mul_pow_le_internal
      formula stageCount queryCount q hdepth hquery
  have hbadN :=
    Nat.mul_le_mul_right N hbad
  have hmultiplied :
      (((2 * q + 1) ^ N) ^ stageCount * queryCount +
          RandomRestriction.stageEventCount (q := q)
            (stagedBad (stageCount := stageCount)
              formula queryCount) * N) *
            q ^ queryCount <
        (N * ((2 * q + 1) ^ (N - 1)) ^ stageCount) *
          q ^ queryCount := by
    apply lt_of_le_of_lt _ hnumeric
    rw [Nat.add_mul]
    apply Nat.add_le_add_left
    simpa [Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using hbadN
  have haverage :
      ((2 * q + 1) ^ N) ^ stageCount * queryCount +
          RandomRestriction.stageEventCount (q := q)
            (stagedBad (stageCount := stageCount)
              formula queryCount) * N <
        RandomRestriction.stageFreeSum N q stageCount := by
    rw [RandomRestriction.stageFreeSum_internal]
    exact
      (Nat.mul_lt_mul_right (Nat.pow_pos hq)).mp
        hmultiplied
  exact exists_shallow_stagedDecisionTree_internal
    formula stageCount queryCount q haverage

end AC0Formula
end Complexity
