/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Parallel

/-!
# Free interleaving of two record arrays

Two global circuits may compute different fields for every record. Running
them once each and interleaving their outputs by fixed wiring combines those
fields without duplicating either computation.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.RecordArray

/-- Interleave the left and right field blocks within every record. -/
def outputWire (records leftWidth rightWidth : Nat)
    (output : Fin (records * (leftWidth + rightWidth))) :
    Fin (records * leftWidth + records * rightWidth) :=
  let pair := (finProdFinEquiv (m := records) (n := leftWidth + rightWidth)).symm output
  Fin.addCases
    (fun bit => Fin.castAdd (records * rightWidth) (finProdFinEquiv (pair.1, bit)))
    (fun bit => Fin.natAdd (records * leftWidth) (finProdFinEquiv (pair.1, bit))) pair.2

/-- Compute both field arrays once, then interleave by free output wiring. -/
def combine
    (left : Circuit signature inputs (records * leftWidth))
    (right : Circuit signature inputs (records * rightWidth)) :=
  (left.parallel right).mapOutputs (outputWire records leftWidth rightWidth)

/-- Each combined record is the concatenation of the two computed fields. -/
theorem combine_eval
    (left : Circuit signature inputs (records * leftWidth))
    (right : Circuit signature inputs (records * rightWidth))
    (interpretation : Interpretation signature Value)
    (input : Fin inputs → Value) (record : Fin records) (bit : Fin (leftWidth + rightWidth)) :
    (combine left right).eval interpretation input (finProdFinEquiv (record, bit)) =
      Fin.append
        (fun field => left.eval interpretation input (finProdFinEquiv (record, field)))
        (fun field => right.eval interpretation input (finProdFinEquiv (record, field))) bit := by
  rw [combine, Circuit.eval_mapOutputs, Circuit.eval_parallel]
  simp only [Function.comp_apply, outputWire, Equiv.symm_apply_apply]
  refine Fin.addCases (fun leftBit => ?_) (fun rightBit => ?_) bit
  · rw [Fin.addCases_left, Fin.append_left, Fin.append_left]
  · rw [Fin.addCases_right, Fin.append_right, Fin.append_right]

/-- Interleaving adds no cost to the two global computations. -/
theorem combine_cost
    (left : Circuit signature inputs (records * leftWidth))
    (right : Circuit signature inputs (records * rightWidth))
    (cost : OperationCost signature) :
    (combine left right).cost cost = left.cost cost + right.cost cost := by
  rw [combine, Circuit.cost_mapOutputs, Circuit.cost_parallel]

end Algebraic.MassProduction.Nonuniform.RecordArray
