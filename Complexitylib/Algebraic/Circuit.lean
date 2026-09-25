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
  (id FanInAtMost instDecidableFanInAtMost size outputDepths depth eval eval_id map_eval
   computation trace)

end Circuit
end Algebraic
