/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan
public import Complexitylib.Algebraic.Translation
public import Cslib.Computability.Circuit.Boolean.Basic

/-!
# Conversions to CSLib's Boolean basis

CSLib counts constants, negations, conjunctions, and disjunctions as gates.
Our De Morgan basis also has an identity operation and supports weighted costs.
The realizations below preserve all outputs: importing a CSLib circuit preserves
its gate count, while exporting a De Morgan circuit removes identity gates.
Neither conversion identifies `standardCost` with CSLib size, since constants
are free under `standardCost`.
-/

@[expose] public section

namespace Algebraic.DeMorgan

open Cslib.Circuits

/-- The one-gate circuit over this library's De Morgan basis simulating each
operation of CSLib's De Morgan basis. -/
def fromBooleanOperation : (op : Boolean.Op) →
    Circuit signature (Boolean.signature.Arity op) 1 1
  | .const false => (Translation.id signature).operation .false
  | .const true => (Translation.id signature).operation .true
  | .not => (Translation.id signature).operation .not
  | .and => (Translation.id signature).operation .and
  | .or => (Translation.id signature).operation .or

/-- Realize CSLib's Boolean operations in the weighted De Morgan basis. -/
def fromBoolean :
    Realization Boolean.signature signature Boolean.interpretation interpretation where
  gateCount := fun _ => 1
  operation := fromBooleanOperation
  realizes := by
    funext op input
    cases op with
    | const value =>
        cases value
        · exact congrFun (congrFun (Translation.pull_id (σ := signature) interpretation) .false) input
        · exact congrFun (congrFun (Translation.pull_id (σ := signature) interpretation) .true) input
    | not => exact congrFun (congrFun (Translation.pull_id (σ := signature) interpretation) .not) input
    | and => exact congrFun (congrFun (Translation.pull_id (σ := signature) interpretation) .and) input
    | or => exact congrFun (congrFun (Translation.pull_id (σ := signature) interpretation) .or) input

/-- Importing a CSLib circuit preserves the number of internal gates. -/
@[simp] theorem fromBoolean_size (circuit : Circuit Boolean.signature n g m) :
    (fromBoolean.compile circuit).size = circuit.size := by
  rw [← Circuit.cost_unit, Realization.compile_cost]
  have cost : fromBoolean.pullCost OperationCost.unit = OperationCost.unit := by
    funext op
    cases op with
    | const value => cases value <;> rfl
    | not | and | or => rfl
  rw [cost, Circuit.cost_unit]

/-- Weighted logical-gate cost is at most the imported CSLib gate count. -/
theorem fromBoolean_standardCost_le (circuit : Circuit Boolean.signature n g m) :
    (fromBoolean.compile circuit).cost standardCost ≤ circuit.size := by
  calc
    _ ≤ 1 * (fromBoolean.compile circuit).size :=
      Circuit.cost_le_mul_size _ _ (by intro op; cases op <;> decide)
    _ = circuit.size := by rw [one_mul, fromBoolean_size]

/-- The number of CSLib De Morgan gates simulating each operation of this library's
De Morgan basis: none for the identity, one otherwise. -/
def toBooleanGateCount : Op → Nat
  | .id => 0
  | .false | .true | .not | .and | .or => 1

/-- The CSLib De Morgan circuit simulating each operation of this library's De
Morgan basis; the identity uses no gate. -/
def toBooleanOperation : (op : Op) →
    Circuit Boolean.signature (arity op) (toBooleanGateCount op) 1
  | .false => (Translation.id Boolean.signature).operation (.const false)
  | .true => (Translation.id Boolean.signature).operation (.const true)
  | .id => Circuit.id Boolean.signature 1
  | .not => (Translation.id Boolean.signature).operation .not
  | .and => (Translation.id Boolean.signature).operation .and
  | .or => (Translation.id Boolean.signature).operation .or

/-- Realize De Morgan operations in CSLib, using a free wire for identity. -/
def toBoolean :
    Realization signature Boolean.signature interpretation Boolean.interpretation where
  gateCount := toBooleanGateCount
  operation := toBooleanOperation
  realizes := by
    funext op input
    cases op with
    | false =>
        exact congrFun (congrFun (Translation.pull_id Boolean.interpretation) (.const false)) input
    | true =>
        exact congrFun (congrFun (Translation.pull_id Boolean.interpretation) (.const true)) input
    | id =>
        change (Circuit.id Boolean.signature 1).eval Boolean.interpretation input 0 =
          input (0 : Fin 1)
        exact congrFun (Circuit.eval_id Boolean.interpretation input) (0 : Fin 1)
    | not => exact congrFun (congrFun (Translation.pull_id Boolean.interpretation) .not) input
    | and => exact congrFun (congrFun (Translation.pull_id Boolean.interpretation) .and) input
    | or => exact congrFun (congrFun (Translation.pull_id Boolean.interpretation) .or) input

/-- Removing identity gates never increases the internal gate count. -/
theorem toBoolean_size_le (circuit : Circuit signature n g m) :
    (toBoolean.compile circuit).size ≤ circuit.size := by
  simpa only [Realization.compile, one_mul] using toBoolean.toTranslation.compile_size_le_mul circuit
    (K := 1) (by intro op; cases op <;> decide)

/-- CSLib's scalar computation predicate agrees with generic computation
for its Boolean interpretation and a single designated output. -/
theorem boolean_computes_iff (circuit : Circuit Boolean.signature n g 1)
    (function : Cslib.BooleanFunction n) :
    circuit.Computes Boolean.interpretation function ↔
      circuit.ComputesWith Boolean.interpretation (fun input _ => function input) := by
  constructor
  · intro computes input
    funext output
    have equal : output = 0 := Subsingleton.elim _ _
    simpa only [equal] using computes input
  · intro computes input
    exact congrFun (computes input) 0

/-- Importing a Boolean circuit preserves its scalar computation contract. -/
theorem fromBoolean_computes (circuit : Circuit Boolean.signature n g 1)
    (function : Cslib.BooleanFunction n) :
    (fromBoolean.compile circuit).ComputesWith interpretation (fun input _ => function input) ↔
      circuit.Computes Boolean.interpretation function := by
  rw [boolean_computes_iff]
  simp only [Circuit.ComputesWith, Realization.compile_eval]

/-- Exporting a De Morgan circuit preserves its scalar computation contract. -/
theorem toBoolean_computes (circuit : Circuit signature n g 1)
    (function : ScalarFunction Bool n) :
    (toBoolean.compile circuit).Computes Boolean.interpretation function ↔
      circuit.ComputesWith interpretation (fun input _ => function input) := by
  rw [boolean_computes_iff]
  simp only [Circuit.ComputesWith, Realization.compile_eval]

end Algebraic.DeMorgan
