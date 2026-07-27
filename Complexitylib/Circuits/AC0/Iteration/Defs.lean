/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.AC0.Restriction
public import Complexitylib.Circuits.AC0.Switching.Defs
public import Complexitylib.Circuits.DecisionTree.NormalForm.Defs
public import Complexitylib.Circuits.RandomRestriction.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card

/-!
# Iterated switching for AC0 formulas -- definitions

A restriction stage is stored newest first. The tail therefore contains the
earlier stages used to simplify the children of a gate, while the head is the
next restriction used to switch the normal form assembled at that gate.

This representation is finite and nonuniform. It contains restrictions and
formula trees only; it does not contain or assume a circuit generator.
-/

@[expose] public section

namespace Complexity

open scoped BigOperators

namespace Switching

/-- A newest-first sequence of exactly `stageCount` finite restrictions. -/
def RestrictionStages (N : ℕ) : ℕ → Type
  | 0 => Unit
  | stageCount + 1 =>
      Restriction.On N × RestrictionStages N stageCount

namespace RestrictionStages

/-- Compose all stages chronologically, so earlier fixed values take
precedence over later stages. -/
def cumulative :
    (stageCount : ℕ) → RestrictionStages N stageCount →
      Restriction.On N
  | 0, _ => Restriction.On.empty
  | stageCount + 1, stages =>
      Restriction.On.comp
        (cumulative stageCount stages.2) stages.1

end RestrictionStages
end Switching

namespace RandomRestriction

/-- Independent sparse-restriction seeds for exactly `stageCount` stages.
The recursive product stores the earlier stages before the newest seed. -/
def StageSeed (N q : ℕ) : ℕ → Type
  | 0 => Unit
  | stageCount + 1 => StageSeed N q stageCount × Seed N q

instance stageSeedFintype (N q stageCount : ℕ) :
    Fintype (StageSeed N q stageCount) := by
  induction stageCount with
  | zero =>
      simp only [StageSeed]
      infer_instance
  | succ stageCount ih =>
      simp only [StageSeed]
      infer_instance

instance stageSeedDecidableEq (N q stageCount : ℕ) :
    DecidableEq (StageSeed N q stageCount) := by
  induction stageCount with
  | zero =>
      simp only [StageSeed]
      infer_instance
  | succ stageCount ih =>
      simp only [StageSeed]
      infer_instance

/-- Decode every seed in a staged sparse restriction. -/
def decodeStages :
    {stageCount : ℕ} → StageSeed N q stageCount →
      Switching.RestrictionStages N stageCount
  | 0, _ => ()
  | _ + 1, seeds =>
      (decode seeds.2, decodeStages seeds.1)

/-- The cumulative finite restriction decoded from all stages. -/
def finalRestriction (seeds : StageSeed N q stageCount) :
    Restriction.On N :=
  Switching.RestrictionStages.cumulative stageCount
    (decodeStages seeds)

/-- Count staged seeds whose decoded restrictions satisfy `event`. -/
def stageEventCount (q : ℕ)
    (event : Switching.RestrictionStages N stageCount → Prop)
    [DecidablePred event] : ℕ :=
  (Finset.univ.filter fun seeds : StageSeed N q stageCount =>
    event (decodeStages seeds)).card

/-- Sum, over all staged seeds, of the number of variables left free by the
cumulative restriction. -/
def stageFreeSum (N q stageCount : ℕ) : ℕ :=
  ∑ seeds : StageSeed N q stageCount,
    (finalRestriction seeds).freeVariables.card

end RandomRestriction

namespace AC0Formula

/-- The depth-at-most-one decision tree used at the bottom of the staged
compiler. Gate cases are a harmless fallback: correctness uses this
construction only when the formula has connective depth zero. -/
def baseDecisionTree : AC0Formula N → DecisionTree.On N
  | .const value => .leaf value
  | .lit literal =>
      if literal.polarity then
        .node literal.var (.leaf false) (.leaf true)
      else
        .node literal.var (.leaf true) (.leaf false)
  | .and children =>
      .leaf (evalAll (fun _ => false) children)
  | .or children =>
      .leaf (evalAny (fun _ => false) children)

/-- Compile a depth-bounded AC0 formula through a newest-first sequence of
switching stages.

At a gate, the earlier stages recursively compile every child to a decision
tree. A conjunction of those trees becomes a CNF and a disjunction becomes a
DNF. The newest restriction is then handled by the corresponding complete
block switching tree. -/
noncomputable def stagedDecisionTree :
    (stageCount : ℕ) →
      Switching.RestrictionStages N stageCount →
      AC0Formula N → DecisionTree.On N
  | 0, _, formula => formula.baseDecisionTree
  | stageCount + 1, stages, formula =>
      match formula with
      | .const value =>
          (stagedDecisionTree stageCount stages.2 (.const value)).restrict
            stages.1
      | .lit literal =>
          (stagedDecisionTree stageCount stages.2 (.lit literal)).restrict
            stages.1
      | .and children =>
          let trees := children.toList.map
            (stagedDecisionTree stageCount stages.2)
          (DecisionTree.On.allCNF trees).consistentPart
            |>.switchingDecisionTreeUnder stages.1
      | .or children =>
          let trees := children.toList.map
            (stagedDecisionTree stageCount stages.2)
          (DecisionTree.On.anyDNF trees).consistentPart
            |>.switchingDecisionTreeUnder stages.1

/-- The staged compiler fails its target depth when its output has depth at
least `queryCount`. -/
def stagedBad (formula : AC0Formula N) (queryCount : ℕ)
    (stages : Switching.RestrictionStages N stageCount) : Prop :=
  queryCount ≤ (formula.stagedDecisionTree stageCount stages).depth

noncomputable instance stagedBadDecidable
    (formula : AC0Formula N) (queryCount stageCount : ℕ) :
    DecidablePred
      (stagedBad (stageCount := stageCount) formula queryCount) :=
  fun stages => by
    unfold stagedBad
    infer_instance

end AC0Formula
end Complexity
