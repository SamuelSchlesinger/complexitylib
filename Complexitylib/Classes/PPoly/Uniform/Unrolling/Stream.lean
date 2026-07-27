/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Stream.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Stream.Internal

/-!
# Streamable deterministic unrolling arithmetic

This module exposes the base-independent gate count of one packed transition
layer and closed forms for the configuration base, first unused wire, and gate
count after any canonical deterministic trace prefix.

These are pure structural facts about the direct-unrolling circuit. They are
intended to be consumed by an append-only log-space serializer without making
that serializer reproduce the recursive `TraceBuild` arithmetic at run time.

## Main results

- `CircuitUnrolling.size_nextFormula_eq_directStepFormulaSize` — formula size
  ignores absolute wire bases.
- `CircuitUnrolling.stepFragmentSize_eq_directStepSize` — every packed layer at
  a fixed horizon has one exact size.
- `TM.directPrefixTraceBuild_configBase`,
  `TM.directPrefixTraceBuild_available`, and
  `TM.directPrefixTraceBuild_size` — closed forms for deterministic prefixes.
- `TM.directUnrollingRawCircuit_eq_init_append_steps` — the complete direct raw
  circuit is initialization, a flat canonical layer list, and acceptance.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- Absolute incoming configuration and choice-wire numbers do not affect a
next-configuration formula's tree size. -/
@[simp] theorem size_nextFormula_eq_directStepFormulaSize (tm : NTM k)
    (T configBase choiceWire : ℕ) (atom : ConfigAtom tm T) :
    (nextFormula tm T configBase choiceWire atom).size =
      directStepFormulaSize tm T atom :=
  size_nextFormula_eq_directStepFormulaSize_internal tm T configBase choiceWire atom

/-- At a fixed horizon, every packed transition fragment has the same exact
gate count, independently of its incoming configuration and choice wires. -/
@[simp] theorem stepFragmentSize_eq_directStepSize (tm : NTM k)
    (T configBase choiceWire : ℕ) :
    stepFragmentSize tm T configBase choiceWire = directStepSize tm T :=
  stepFragmentSize_eq_directStepSize_internal tm T configBase choiceWire

end CircuitUnrolling

namespace TM

/-- After `i ≤ T` deterministic transition layers, the packed configuration
starts after exactly `i` base-independent layer fragments. -/
theorem directPrefixTraceBuild_configBase (tm : TM k)
    (T n i : ℕ) [NeZero n] (hi : i ≤ T) :
    (tm.directPrefixTraceBuild T n i).configBase =
      n + i * CircuitUnrolling.directStepSize tm.toNTM T :=
  tm.directPrefixTraceBuild_configBase_internal T n i hi

/-- After `i ≤ T` deterministic transition layers, the first unused wire is
the primary prefix, initial configuration width, and `i` complete layer sizes. -/
theorem directPrefixTraceBuild_available (tm : TM k)
    (T n i : ℕ) [NeZero n] (hi : i ≤ T) :
    (tm.directPrefixTraceBuild T n i).available =
      n + CircuitUnrolling.configWidth tm.toNTM T +
        i * CircuitUnrolling.directStepSize tm.toNTM T :=
  tm.directPrefixTraceBuild_available_internal T n i hi

/-- After `i ≤ T` deterministic transition layers, the trace prefix contains
the initial configuration block followed by `i` equal-size packed layers. -/
theorem directPrefixTraceBuild_size (tm : TM k)
    (T n i : ℕ) [NeZero n] (hi : i ≤ T) :
    (tm.directPrefixTraceBuild T n i).size =
      CircuitUnrolling.configWidth tm.toNTM T +
        i * CircuitUnrolling.directStepSize tm.toNTM T :=
  tm.directPrefixTraceBuild_size_internal T n i hi

/-- The circuit accumulated after `i ≤ T` layers is the initialization fragment
followed by the first `i` canonical closed-form transition fragments. -/
theorem directPrefixTraceBuild_circuit (tm : TM k)
    (T n i : ℕ) [NeZero n] (hi : i ≤ T) :
    (tm.directPrefixTraceBuild T n i).circuit =
      CircuitUnrolling.initFragment tm.toNTM T n n
          (CircuitUnrolling.deterministicInputWires T n) ++
        ((List.finRange T).take i).flatMap (tm.directStepFragment T n) :=
  tm.directPrefixTraceBuild_circuit_internal T n i hi

/-- The complete deterministic trace fragment is initialization followed by
all canonical closed-form transition fragments in layer order. -/
theorem directTraceFragment_eq_init_append_steps (tm : TM k)
    (T n : ℕ) [NeZero n] :
    CircuitUnrolling.traceFragment tm.toNTM T n n
        (CircuitUnrolling.deterministicInputWires T n) =
      CircuitUnrolling.initFragment tm.toNTM T n n
          (CircuitUnrolling.deterministicInputWires T n) ++
        (List.finRange T).flatMap (tm.directStepFragment T n) :=
  tm.directTraceFragment_eq_init_append_steps_internal T n

/-- The final deterministic configuration block begins after exactly `T`
base-independent transition fragments. -/
theorem directTraceOutputBase (tm : TM k) (T n : ℕ) [NeZero n] :
    CircuitUnrolling.traceOutputBase tm.toNTM T n n
        (CircuitUnrolling.deterministicInputWires T n) =
      n + T * CircuitUnrolling.directStepSize tm.toNTM T :=
  tm.directTraceOutputBase_internal T n

/-- The positive direct-unrolling raw circuit is exactly the initialization
fragment, the flattened canonical transition layers, and one final acceptance
gate at the closed-form final configuration base. -/
theorem directUnrollingRawCircuit_eq_init_append_steps (tm : TM k)
    (f : ℕ → ℕ) (n : ℕ) [NeZero n] :
    tm.directUnrollingRawCircuit f n =
      CircuitUnrolling.initFragment tm.toNTM (f n) n n
          (CircuitUnrolling.deterministicInputWires (f n) n) ++
        (List.finRange (f n)).flatMap (tm.directStepFragment (f n) n) ++
        [CircuitUnrolling.acceptanceGate tm.toNTM (f n)
          (n + f n * CircuitUnrolling.directStepSize tm.toNTM (f n))] :=
  tm.directUnrollingRawCircuit_eq_init_append_steps_internal f n

end TM

end Complexity
