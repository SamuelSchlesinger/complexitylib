/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Program
public import Cslib.Computability.Circuit.Basic

/-!
# Circuits from CSLib

The circuit type and its evaluation are supplied by CSLib. A circuit consists of
a shared straight-line program and designated output wires; its size counts only
internal gates. Local semantics, costs, and constructions extend this same type.
-/

@[expose] public section

namespace Algebraic

export Cslib.Circuits (Circuit)

namespace Circuit

export Cslib.Circuits.Circuit
  (wiring id size_wiring program_wiring outputs_wiring FanInAtMost instDecidableFanInAtMost
   fanInAtMost_wiring outputDepths depth outputDepths_wiring depth_wiring eval eval_wiring
   map_eval computation trace)

/-- The identity circuit evaluates to its input. -/
@[simp] theorem eval_id {σ : Signature} {n : Nat} {U : Type u}
    (interpretation : Interpretation σ U) (input : Fin n → U) :
    (Circuit.id σ n).eval interpretation input = input := rfl

end Circuit
end Algebraic
