/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Homomorphism
public import Cslib.Computability.Circuit.Program

/-!
# Straight-line programs from CSLib

Wires, renamings, gate lines, and programs are CSLib's types. Their constructors,
evaluation, depths, and structural laws are re-exported for existing imports.
-/

@[expose] public section

namespace Algebraic

export Cslib.Circuits (Wire)

namespace Wire

/-- Regard an original input as a wire. -/
abbrev input {n g : Nat} (input : Fin n) : Wire n g :=
  Fin.castAdd g input

/-- Regard a gate output as a wire. -/
abbrev gate {n g : Nat} (gate : Fin g) : Wire n g :=
  Fin.natAdd n gate

export Cslib.Circuits.Wire (Renaming)

namespace Renaming

export Cslib.Circuits.Wire.Renaming
  (apply apply_input apply_gate id id_apply comp comp_apply castSucc castSucc_apply
   skipLast skipLast_gate_last skipLast_lastWire skipLast_castSucc
   appendLast appendLast_gate_last appendLast_lastWire appendLast_castSucc
   ofPermutation ofPermutation_gate value_apply)

end Renaming
end Wire

export Cslib.Circuits (Line)

namespace Line

export Cslib.Circuits.Line
  (mapWires mapWires_op mapWires_wires eval eval_mapWires eval_mapRenaming depth map_eval)

end Line

export Cslib.Circuits (Program)

namespace Program

export Cslib.Circuits.Program
  (empty gate FanInAtMost instDecidableFanInAtMost eval eval_gate_last eval_gate_castSucc
   depths wireDepths depth map_eval trace trace_input trace_gate_castSucc trace_gate_last
   map_trace gateFunction wireFunction gateFunction_apply wireFunction_input wireFunction_gate
   gateFunction_gate_last gateFunction_gate_castSucc trace_gateWire lines lines_gate_last
   lines_gate_castSucc lines_eval)

end Program
end Algebraic
