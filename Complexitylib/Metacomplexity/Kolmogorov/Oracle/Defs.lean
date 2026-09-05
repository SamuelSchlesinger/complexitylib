/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Oracle.OutputSemantics.Defs
public import Mathlib.Data.Nat.Cast.WithTop
public import Mathlib.Order.Lattice.Nat

/-!
# Oracle-relative Kolmogorov complexity -- definitions

The machine and Boolean oracle are both explicit parameters. As in the
ordinary machine-relative layer, extended naturals distinguish a zero-length
description from the absence of any description. The bounded clock charges
local transitions and oracle lookups according to `OracleTM.reachesIn`.
-/


@[expose] public section

namespace Complexity

namespace OracleTM

variable {n : ℕ}

/-- Lengths of programs that eventually produce `output` relative to `oracle`. -/
def producingProgramSizes (machine : OracleTM n) (oracle : BooleanOracle)
    (output : List Bool) : Set ℕ :=
  {size | ∃ program, program.length = size ∧
    machine.Produces oracle program output}

/-- Lengths of programs that produce `output` within `time` relative to
`oracle`. -/
def timeBoundedProducingProgramSizes (machine : OracleTM n)
    (oracle : BooleanOracle) (output : List Bool) (time : ℕ) : Set ℕ :=
  {size | ∃ program, program.length = size ∧
    machine.ProducesInTime oracle program output time}

/-- Plain description complexity relative to a machine and Boolean oracle. -/
noncomputable def plainKolmogorovComplexity (machine : OracleTM n)
    (oracle : BooleanOracle) (output : List Bool) : WithTop ℕ :=
  sInf ((fun size : ℕ => (size : WithTop ℕ)) ''
    machine.producingProgramSizes oracle output)

/-- Whole-output time-bounded description complexity relative to a machine and
Boolean oracle. -/
noncomputable def timeBoundedKolmogorovComplexity (machine : OracleTM n)
    (oracle : BooleanOracle) (output : List Bool) (time : ℕ) : WithTop ℕ :=
  sInf ((fun size : ℕ => (size : WithTop ℕ)) ''
    machine.timeBoundedProducingProgramSizes oracle output time)

end OracleTM

end Complexity
