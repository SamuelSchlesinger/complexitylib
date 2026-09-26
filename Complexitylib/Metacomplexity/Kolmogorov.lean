/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Internal
public import Complexitylib.Metacomplexity.Kolmogorov.Conditional
public import Complexitylib.Metacomplexity.Kolmogorov.Chain
public import Complexitylib.Metacomplexity.Kolmogorov.Depth
public import Complexitylib.Metacomplexity.Kolmogorov.Symmetry

/-!
# Machine-relative Kolmogorov complexity

Plain and whole-output time-bounded description complexity are defined for
every deterministic machine, independently of universality. Both take values
in `WithTop ℕ`, so `⊤` records that no qualifying program exists. Prefix-free
complexity is exposed only for a machine whose raw halting domain is certified
prefix-free.

The threshold theorems characterize each minimum by a short producing program.
Generic simulations yield additive plain-complexity comparison, while a
polynomial timed simulation gives an explicit resource-aware bounded-complexity
comparison. Bounded input locality also implies that every finite `t`-time
complexity value is at most `t`.

## Main results

- `TM.plainKolmogorovComplexity_le_coe_iff` -- plain threshold characterization
- `TM.timeBoundedKolmogorovComplexity_le_coe_iff` -- bounded characterization
- `TM.timeBoundedKolmogorovComplexity_lt_coe_iff` -- strict characterization
- `TM.timeBoundedKolmogorovComplexity_mono` -- more time cannot increase complexity
- `TM.timeBoundedKolmogorovComplexity_le_time` -- finite values are at most the clock
- `TM.computationalDepth_add_plain` -- exact decomposition of bounded complexity
- `TM.computationalDepth_mono` -- more time cannot increase computational depth
- `TM.computationalDepthBetween_add` -- exact three-clock depth telescoping
- `timeBoundedKolmogorovComplexity_pair_le_of_composition` -- finite upper chain rule
- `timeBoundedKolmogorovComplexity_pair_le_add_of_conditional_composition` -- additive chain
- `TimeBoundedSymmetryOfInformation` -- explicit machine-relative lower-chain hypothesis
- `TimeBoundedSymmetryOfInformation.conditional_le_of_pair_upper` -- depth-loss bridge
- `TimeBoundedSymmetryOfInformation.conditional_le_of_composition` -- evaluator bridge
- `TM.Simulates.plainKolmogorovComplexity_le_add` -- additive invariance direction
- `TM.PolynomialTimeOverhead.kolmogorov_transfer` -- resource-aware comparison
- `TM.IsUniversal.plainKolmogorovComplexity_ne_top` -- universal descriptions exist
- `TM.IsEfficientlyUniversal.timeBoundedKolmogorovComplexity_printer` -- uniform printer
-/


public section

namespace Complexity

namespace TM

variable {n simulatorTapes sourceTapes : ℕ}

/-- Prefix-free complexity is the plain minimum of the certified machine; the
bundle's domain proof licenses the prefix-free interpretation. -/
@[simp] theorem prefixKolmogorovComplexity_eq (machine : PrefixFreeMachine n)
    (output : List Bool) :
    prefixKolmogorovComplexity machine output =
      machine.machine.plainKolmogorovComplexity output := rfl

/-- Any producing program upper-bounds plain complexity. -/
theorem plainKolmogorovComplexity_le {machine : TM n} {program output : List Bool}
    (hproduce : machine.Produces program output) :
    machine.plainKolmogorovComplexity output ≤ program.length :=
  plainKolmogorovComplexity_le_internal hproduce

/-- Plain complexity is infinite exactly when the output has no description. -/
theorem plainKolmogorovComplexity_eq_top_iff (machine : TM n) (output : List Bool) :
    machine.plainKolmogorovComplexity output = ⊤ ↔
      ¬∃ program, machine.Produces program output :=
  plainKolmogorovComplexity_eq_top_iff_internal machine output

/-- Every finite plain complexity value is attained by a producing program. -/
theorem plainKolmogorovComplexity_witness (machine : TM n) (output : List Bool)
    (hfinite : machine.plainKolmogorovComplexity output ≠ ⊤) :
    ∃ program, (program.length : WithTop ℕ) =
      machine.plainKolmogorovComplexity output ∧ machine.Produces program output :=
  plainKolmogorovComplexity_witness_internal machine output hfinite

/-- Plain complexity is at most `bound` exactly when a producing program of
length at most `bound` exists. -/
theorem plainKolmogorovComplexity_le_coe_iff (machine : TM n)
    (output : List Bool) (bound : ℕ) :
    machine.plainKolmogorovComplexity output ≤ (bound : WithTop ℕ) ↔
      ∃ program, program.length ≤ bound ∧ machine.Produces program output :=
  plainKolmogorovComplexity_le_coe_iff_internal machine output bound

/-- Any program producing within a clock upper-bounds time-bounded complexity. -/
theorem timeBoundedKolmogorovComplexity_le {machine : TM n}
    {program output : List Bool} {time : ℕ}
    (hproduce : machine.ProducesInTime program output time) :
    machine.timeBoundedKolmogorovComplexity output time ≤ program.length :=
  timeBoundedKolmogorovComplexity_le_internal hproduce

/-- Time-bounded complexity is infinite exactly when no program produces the
output within the clock. -/
theorem timeBoundedKolmogorovComplexity_eq_top_iff (machine : TM n)
    (output : List Bool) (time : ℕ) :
    machine.timeBoundedKolmogorovComplexity output time = ⊤ ↔
      ¬∃ program, machine.ProducesInTime program output time :=
  timeBoundedKolmogorovComplexity_eq_top_iff_internal machine output time

/-- Every finite time-bounded complexity value is attained. -/
theorem timeBoundedKolmogorovComplexity_witness (machine : TM n)
    (output : List Bool) (time : ℕ)
    (hfinite : machine.timeBoundedKolmogorovComplexity output time ≠ ⊤) :
    ∃ program, (program.length : WithTop ℕ) =
      machine.timeBoundedKolmogorovComplexity output time ∧
      machine.ProducesInTime program output time :=
  timeBoundedKolmogorovComplexity_witness_internal machine output time hfinite

/-- Every finite `t`-time description complexity is at most `t`: a producing
program can be truncated to the prefix reachable by the input head. -/
theorem timeBoundedKolmogorovComplexity_le_time (machine : TM n)
    (output : List Bool) (time : ℕ)
    (hfinite : machine.timeBoundedKolmogorovComplexity output time ≠ ⊤) :
    machine.timeBoundedKolmogorovComplexity output time ≤
      (time : WithTop ℕ) :=
  timeBoundedKolmogorovComplexity_le_time_internal
    machine output time hfinite

/-- Time-bounded complexity is at most `bound` exactly when a short program
produces the output within the clock. -/
theorem timeBoundedKolmogorovComplexity_le_coe_iff (machine : TM n)
    (output : List Bool) (time bound : ℕ) :
    machine.timeBoundedKolmogorovComplexity output time ≤ (bound : WithTop ℕ) ↔
      ∃ program, program.length ≤ bound ∧
        machine.ProducesInTime program output time :=
  timeBoundedKolmogorovComplexity_le_coe_iff_internal machine output time bound

/-- Time-bounded complexity is strictly below `bound` exactly when a program
strictly shorter than `bound` produces the output within the clock. -/
theorem timeBoundedKolmogorovComplexity_lt_coe_iff (machine : TM n)
    (output : List Bool) (time bound : ℕ) :
    machine.timeBoundedKolmogorovComplexity output time < (bound : WithTop ℕ) ↔
      ∃ program, program.length < bound ∧
        machine.ProducesInTime program output time :=
  timeBoundedKolmogorovComplexity_lt_coe_iff_internal machine output time bound

/-- Enlarging the clock cannot increase time-bounded complexity. -/
theorem timeBoundedKolmogorovComplexity_mono (machine : TM n)
    (output : List Bool) {first second : ℕ} (hclock : first ≤ second) :
    machine.timeBoundedKolmogorovComplexity output second ≤
      machine.timeBoundedKolmogorovComplexity output first :=
  timeBoundedKolmogorovComplexity_mono_internal machine output hclock

/-- Removing the time restriction cannot increase description complexity. -/
theorem plainKolmogorovComplexity_le_timeBounded (machine : TM n)
    (output : List Bool) (time : ℕ) :
    machine.plainKolmogorovComplexity output ≤
      machine.timeBoundedKolmogorovComplexity output time :=
  plainKolmogorovComplexity_le_timeBounded_internal machine output time

/-- An output-preserving compiler with additive length overhead gives the
corresponding direction of the plain Kolmogorov invariance inequality. -/
theorem Simulates.plainKolmogorovComplexity_le_add
    {simulator : TM simulatorTapes} {source : TM sourceTapes}
    {compile : List Bool → List Bool} {constant : ℕ}
    (hsim : simulator.Simulates source compile)
    (hlength : HasAdditiveProgramOverhead compile constant) (output : List Bool) :
    simulator.plainKolmogorovComplexity output ≤
      source.plainKolmogorovComplexity output + (constant : WithTop ℕ) :=
  simulates_plainKolmogorovComplexity_le_add_internal hsim hlength output

/-- A polynomial timed simulation transfers a bounded description of length
`bound` into one of length `bound + constant` under an explicit polynomially
larger clock. The coefficient and exponent are uniform over all outputs, source
clocks and bounds. (The proof takes them from the clock policy `hclock`, but
the statement asserts only their existence.) -/
theorem PolynomialTimeOverhead.kolmogorov_transfer
    {simulator : TM simulatorTapes} {source : TM sourceTapes}
    {compile : List Bool → List Bool} {constant : ℕ} {clock : TimeOverhead}
    (hsim : simulator.SimulatesInTime source compile clock)
    (hlength : HasAdditiveProgramOverhead compile constant)
    (hclock : PolynomialTimeOverhead clock) :
    ∃ coefficient exponent, ∀ (output : List Bool) (sourceTime bound : ℕ),
      source.timeBoundedKolmogorovComplexity output sourceTime ≤
          (bound : WithTop ℕ) →
        simulator.timeBoundedKolmogorovComplexity output
            (coefficient * (bound + sourceTime + 1) ^ exponent) ≤
          (bound + constant : ℕ) :=
  polynomialTimeOverhead_kolmogorov_transfer_internal hsim hlength hclock

/-- Every semantically universal machine has a finite plain description of
every binary string. The proof uses universality only against the fixed
input-to-output copy machine. -/
theorem IsUniversal.plainKolmogorovComplexity_ne_top
    {simulator : TM simulatorTapes} (huniversal : simulator.IsUniversal)
    (output : List Bool) :
    simulator.plainKolmogorovComplexity output ≠ ⊤ :=
  huniversal.plainKolmogorovComplexity_ne_top_internal output

/-- Every output has finite bounded complexity at some clock on any
semantically universal machine. Semantic universality alone does not select a
uniform time bound. -/
theorem IsUniversal.exists_timeBoundedKolmogorovComplexity_ne_top
    {simulator : TM simulatorTapes} (huniversal : simulator.IsUniversal)
    (output : List Bool) :
    ∃ time, simulator.timeBoundedKolmogorovComplexity output time ≠ ⊤ :=
  huniversal.exists_timeBoundedKolmogorovComplexity_ne_top_internal output

/-- Polynomially efficient universality supplies one uniform printer: every
string `x` has a description of length at most `|x| + constant` within
`coefficient * (2|x| + 3)^exponent` steps. The same bound remains valid at
every larger clock. -/
theorem IsEfficientlyUniversal.timeBoundedKolmogorovComplexity_printer
    {simulator : TM simulatorTapes}
    (huniversal : simulator.IsEfficientlyUniversal) :
    ∃ constant coefficient exponent, ∀ (output : List Bool) (time : ℕ),
      coefficient * (2 * output.length + 3) ^ exponent ≤ time →
        simulator.timeBoundedKolmogorovComplexity output time ≤
          (output.length + constant : ℕ) :=
  huniversal.timeBoundedKolmogorovComplexity_printer_internal

/-- Efficient universality gives the usual linear self-description upper bound
for plain complexity, with one additive constant for every output. -/
theorem IsEfficientlyUniversal.plainKolmogorovComplexity_le_length_add
    {simulator : TM simulatorTapes}
    (huniversal : simulator.IsEfficientlyUniversal) :
    ∃ constant, ∀ output : List Bool,
      simulator.plainKolmogorovComplexity output ≤
        (output.length + constant : ℕ) :=
  huniversal.plainKolmogorovComplexity_le_length_add_internal

/-- The uniform polynomial printer clock makes time-bounded complexity finite
for every output of an efficiently universal machine. -/
theorem IsEfficientlyUniversal.exists_polynomial_printer_finite
    {simulator : TM simulatorTapes}
    (huniversal : simulator.IsEfficientlyUniversal) :
    ∃ coefficient exponent, ∀ output : List Bool,
      simulator.timeBoundedKolmogorovComplexity output
        (coefficient * (2 * output.length + 3) ^ exponent) ≠ ⊤ :=
  huniversal.exists_polynomial_printer_finite_internal

end TM

end Complexity
