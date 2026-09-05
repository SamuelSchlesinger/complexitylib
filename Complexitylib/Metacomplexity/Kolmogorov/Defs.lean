/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Universality.Defs
public import Mathlib.Data.List.Infix
public import Mathlib.Data.Nat.Cast.WithTop
public import Mathlib.Order.Lattice.Nat

/-!
# Machine-relative Kolmogorov complexity

This definitions layer introduces plain and time-bounded description
complexity for every deterministic machine. Universality is deliberately not a
precondition: it is relevant to invariance and upper bounds, not to the minimum
itself. Extended naturals distinguish a genuine zero-length description from
the absence of any description.

Prefix-free complexity is restricted to a machine carrying a proof that its
halting domain is prefix-free. The library's ordinary input convention does not
provide that property automatically.

## Main definitions

- `TM.plainKolmogorovComplexity` -- machine-relative plain complexity `C_U`
- `TM.timeBoundedKolmogorovComplexity` -- whole-output bounded complexity `C_U^t`
- `TM.HasPrefixFreeDomain` -- prefix-freeness of the raw halting domain
- `TM.PrefixFreeMachine` -- a machine bundled with that domain certificate
- `TM.prefixKolmogorovComplexity` -- prefix-free complexity `K_U`
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Lengths of programs on which `machine` eventually produces `output`. -/
def producingProgramSizes (machine : TM n) (output : List Bool) : Set ℕ :=
  {size | ∃ program, program.length = size ∧ machine.Produces program output}

/-- Lengths of programs on which `machine` produces `output` within `time`. -/
def timeBoundedProducingProgramSizes (machine : TM n) (output : List Bool)
    (time : ℕ) : Set ℕ :=
  {size | ∃ program,
    program.length = size ∧ machine.ProducesInTime program output time}

/-- Plain machine-relative Kolmogorov complexity. The value is `⊤` exactly
when no program makes `machine` produce `output`. -/
noncomputable def plainKolmogorovComplexity (machine : TM n)
    (output : List Bool) : WithTop ℕ :=
  sInf ((fun size : ℕ => (size : WithTop ℕ)) '' machine.producingProgramSizes output)

/-- Whole-output time-bounded machine-relative Kolmogorov complexity. The
primitive clock is explicit, and the value is `⊤` if no program produces the
output within it. -/
noncomputable def timeBoundedKolmogorovComplexity (machine : TM n)
    (output : List Bool) (time : ℕ) : WithTop ℕ :=
  sInf ((fun size : ℕ => (size : WithTop ℕ)) ''
    machine.timeBoundedProducingProgramSizes output time)

/-- The raw halting domain of `machine` is prefix-free: two halting programs
related by the list-prefix order must be equal. -/
def HasPrefixFreeDomain (machine : TM n) : Prop :=
  ∀ {first second : List Bool}, machine.Halts first → machine.Halts second →
    first <+: second → first = second

/-- A deterministic machine bundled with a proof that its halting domain is
prefix-free. This certificate is what licenses `K_U` terminology. -/
structure PrefixFreeMachine (n : ℕ) where
  /-- The underlying deterministic machine. -/
  machine : TM n
  /-- Its raw halting domain is prefix-free. -/
  prefixFree : machine.HasPrefixFreeDomain

/-- Prefix-free Kolmogorov complexity for a certified prefix-free machine. -/
noncomputable def prefixKolmogorovComplexity (machine : PrefixFreeMachine n)
    (output : List Bool) : WithTop ℕ :=
  machine.machine.plainKolmogorovComplexity output

end TM

end Complexity
