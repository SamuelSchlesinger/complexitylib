/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Combinators.ForInput.Defs
public import Complexitylib.Models.TuringMachine.Combinators.ForInput.Internal

/-!
# Read-only-input loop combinator

`TM.forInputTM body` advances over a Boolean input symbol and invokes `body`
without copying the input into auxiliary space. For input-preserving bodies,
this iterates exactly once per original symbol. It is the input-fueled
counterpart of the unary-work-register loop `TM.forRegTM`.

## Main results

- `TM.IsTransducer.forInputTM` — input-driven iteration preserves one-way output.
- `TM.ForInputLoopSpec.reachesIn` — exact indexed execution from a loop certificate.
- `TM.ForInputLoopSpaceSpec.prefix_withinAuxSpace` — every prefix of the exact
  loop run respects the certified auxiliary-space budget.
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Exact remaining execution of a certified input-driven loop. -/
theorem ForInputLoopSpec.reachesIn {body : TM n} {bodyTime : ℕ → ℕ}
    {total count value : ℕ} (spec : ForInputLoopSpec body bodyTime total)
    (htotal : value + count = total) :
    (forInputTM body).reachesIn (forInputLoopTime bodyTime value count)
      (spec.scanCfg value) spec.doneCfg :=
  spec.reachesIn_internal count value htotal

/-- Every prefix up to the exact remaining runtime of a certified input-driven
loop respects its all-reachable auxiliary-space budget. -/
theorem ForInputLoopSpaceSpec.prefix_withinAuxSpace
    {body : TM n} {bodyTime : ℕ → ℕ}
    {total inputLength spaceBound count value t : ℕ}
    {spec : ForInputLoopSpec body bodyTime total}
    (spaceSpec : ForInputLoopSpaceSpec spec inputLength spaceBound)
    {c : Cfg n (forInputTM body).Q}
    (htotal : value + count = total)
    (hreach : (forInputTM body).reachesIn t (spec.scanCfg value) c)
    (htime : t ≤ forInputLoopTime bodyTime value count) :
    c.WithinAuxSpace inputLength spaceBound :=
  spaceSpec.prefix_withinAuxSpace_internal count value t c htotal hreach htime

/-- Iterating a one-way-output body over the read-only input remains a
one-way-output transducer. -/
theorem IsTransducer.forInputTM {n : ℕ} {body : TM n}
    (hbody : body.IsTransducer) : (forInputTM body).IsTransducer :=
  hbody.forInputTM_internal

end TM

end Complexity
