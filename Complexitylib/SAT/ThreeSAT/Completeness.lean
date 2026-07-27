/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.NP.Reduction
public import Complexitylib.SAT.CookLevin.Assembly
public import Complexitylib.SAT.ThreeSAT.Headline
public import Complexitylib.SAT.Tseitin.Machine

/-!
# NP-completeness of 3SAT

The total Tseitin transformation is a polynomial-time many-one reduction from
the existing encoded CNF-SAT language to the exact-3 language. Together with
Cook--Levin and the direct proof that 3SAT belongs to `NP`, this gives the
headline NP-completeness theorem.

## Main results

- `ThreeSAT.cnfsat_le_language`
- `ThreeSAT.NPHard_language`
- `ThreeSAT.NPComplete_language`
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

/-- The total Tseitin transformation is a polynomial-time many-one reduction
from encoded CNF-SAT to encoded 3SAT. -/
theorem cnfsat_le_language : CNFSAT.language ≤ₚ language :=
  ⟨reduction, reduction_mem_FP, mem_language_iff_reduction_mem⟩

/-- Encoded 3SAT is NP-hard. -/
theorem NPHard_language : NPHard language :=
  SAT.NPHard_language.of_reduction cnfsat_le_language

/-- **3SAT is NP-complete.** -/
theorem NPComplete_language : NPComplete language :=
  ⟨language_mem_NP, NPHard_language⟩

end ThreeSAT

end SAT

end Complexity
