/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Internal.Universality

/-!
# The universal machine satisfies the generic universality interface

This module connects the concrete six-work-tape machine `TM.utmTM` to the
machine-independent interface of `Complexitylib.Models.TuringMachine.Universality`.

## Main results

- `TM.utmTM_simulates_pair` — for every machine `M` there is a description `α`
  such that `utmTM` simulates `M` exactly under the uniform compiler `pair α`:
  halting and every exact output are preserved and reflected, and a source run
  within `t` steps is reproduced within an explicit polynomial clock
- `TM.utmTM_isEfficientlyUniversal` — polynomially efficient universality, with
  additive description overhead `2|α| + 2`
- `TM.utmTM_isUniversal` — semantic universality

## Reading the results

`TM.IsUniversal` and `TM.IsEfficientlyUniversal` ask only for some computable
compiler. `utmTM_simulates_pair` names it: the fixed map `p ↦ pair α p`, where
`α` encodes the source machine, which is polynomial-time and adds exactly
`2|α| + 2` bits.

The simulation is exact in both directions. Halting and output are reflected as
well as preserved: `utmTM` diverges on `pair α p` whenever the source diverges on
`p`.
-/


public section

namespace Complexity

namespace TM

/-- **`utmTM` simulates every machine through a fixed description.** For every
`k`-work-tape machine `M` there is a description `α` such that `utmTM`, run on
`pair α p`, halts exactly when `M` halts on `p` and produces exactly `M`'s
outputs. A source run within `t` steps on program `p` is reproduced within
`utmTime α (16(k + 1)(t + |p| + 1)²) |p|` steps: the quadratic single-tape
reduction followed by the linear-time universal simulation. -/
theorem utmTM_simulates_pair {k : ℕ} (M : TM k) :
    ∃ α : List Bool, utmTM.Simulates M (pair α) ∧
      utmTM.SimulatesInTime M (pair α) (fun program time =>
        UTMBody.utmTime α (16 * (k + 1) * (time + program.length + 1) ^ 2)
          program.length) :=
  UTMBody.utmTM_simulates_pair_internal M

/-- **The concrete universal machine is polynomially efficiently universal.** -/
theorem utmTM_isEfficientlyUniversal : utmTM.IsEfficientlyUniversal :=
  UTMBody.utmTM_isEfficientlyUniversal_internal

/-- **The concrete universal machine is universal.** -/
theorem utmTM_isUniversal : utmTM.IsUniversal :=
  utmTM_isEfficientlyUniversal.isUniversal

end TM

end Complexity
