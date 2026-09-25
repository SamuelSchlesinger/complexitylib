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

export Cslib.Circuits.Wire
  (input gate elim elim_input elim_gate equiv card castSucc castSucc_input castSucc_gate
   lastCases castAdd castAdd_input castAdd_gate)

export Cslib.Circuits.Wire (lastCases_last lastCases_castSucc)

export Cslib.Circuits.Wire (Renaming)

namespace Renaming

export Cslib.Circuits.Wire.Renaming
  (apply apply_input apply_gate id id_apply comp comp_apply castSucc castSucc_apply
   skipLast skipLast_gates_last skipLast_castSucc
   appendLast appendLast_gates_last appendLast_castSucc
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
   depths wireDepths depth map_eval trace trace_input trace_gate_castSucc
   map_trace gateFunction wireFunction gateFunction_apply wireFunction_input wireFunction_gate
   gateFunction_gate_last gateFunction_gate_castSucc trace_gateWire lines lines_gate_last
   lines_gate_castSucc lines_eval eq_eval_of_forall_lines_eval)

end Program
end Algebraic
