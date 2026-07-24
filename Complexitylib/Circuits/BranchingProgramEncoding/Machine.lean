/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.Instr
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScan
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScanLoop
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScanToken
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.OutputProbe
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.OutputProbeToken
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotBranch
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotCapture
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotDescend
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotPosition
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotStep

/-!
# Machine emission of branching-program codes

Concrete serializer leaves for the canonical width-five branching-program
encoding, together with the two-bit recursive slot dispatcher.
-/
