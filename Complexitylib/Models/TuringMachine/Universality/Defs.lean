/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.OutputSemantics.Defs

/-!
# Generic universal-machine interfaces

These definitions describe universal simulation independently of any concrete
machine encoding, pairing function, work-tape count, or overhead formula.
Semantic simulation, compiler length, and simulation time are separate
predicates so later invariance theorems can request exactly the hypotheses they
need. The universality predicates require the compiler to be computable, so a
compiled program cannot carry undecidable information such as whether the
source halts.

## Main definitions

- `TM.IsComputable` -- a string function computed by some deterministic machine
- `TM.Simulates` -- preservation of halting and exact string output
- `TM.HasAdditiveProgramOverhead` -- an additive compiler-length bound
- `TM.SimulatesInTime` -- forward simulation under an explicit clock transform
- `TM.PolynomialTimeOverhead` -- a polynomial policy for clock transforms
- `TM.IsUniversal` -- semantic universality over every work-tape count
- `TM.IsEfficientlyUniversalFor` -- universality relative to an overhead policy
- `TM.IsEfficientlyUniversal` -- the polynomial-overhead specialization
-/


@[expose] public section

namespace Complexity

namespace TM

variable {simulatorTapes sourceTapes : ℕ}

/-- A simulation clock may depend on the source program and its source-machine
time budget. Keeping the complete program available makes clock composition
exact; asymptotic policies below constrain this dependence through its length. -/
abbrev TimeOverhead := List Bool → ℕ → ℕ

/-- A string function is computable when some deterministic machine, with any
number of work tapes, halts on every input with exactly the function's value on
its output tape. -/
def IsComputable (function : List Bool → List Bool) : Prop :=
  ∃ (tapes : ℕ) (machine : TM tapes), machine.Computes function

/-- `simulator` semantically simulates `source` under `compile` when compilation
preserves both raw halting and every exact binary-string output. This is a
partial-function semantics: no concrete description syntax is built in. -/
structure Simulates (simulator : TM simulatorTapes) (source : TM sourceTapes)
    (compile : List Bool → List Bool) : Prop where
  /-- Compilation preserves and reflects halting. -/
  halts_iff : ∀ program, simulator.Halts (compile program) ↔ source.Halts program
  /-- Compilation preserves and reflects exact string outputs. -/
  produces_iff : ∀ program output,
    simulator.Produces (compile program) output ↔ source.Produces program output

/-- Compiler `compile` adds at most `constant` bits to every program. -/
def HasAdditiveProgramOverhead (compile : List Bool → List Bool) (constant : ℕ) : Prop :=
  ∀ program, (compile program).length ≤ program.length + constant

/-- A forward, resource-aware simulation statement. Source halting and exact
output production under budget `sourceTime` are reproduced under clock
`clock program sourceTime`. Untimed reflection belongs to `Simulates` and is
intentionally separate. -/
structure SimulatesInTime (simulator : TM simulatorTapes) (source : TM sourceTapes)
    (compile : List Bool → List Bool) (clock : TimeOverhead) : Prop where
  /-- Bounded source halting transfers through the compiler and clock. -/
  halts : ∀ program sourceTime, source.HaltsInTime program sourceTime →
    simulator.HaltsInTime (compile program) (clock program sourceTime)
  /-- Bounded exact-output production transfers through the compiler and clock. -/
  produces : ∀ program output sourceTime,
    source.ProducesInTime program output sourceTime →
      simulator.ProducesInTime (compile program) output (clock program sourceTime)

/-- A clock transform is polynomial when one bivariate polynomial in source
time and source-program length bounds it everywhere. Constants may depend on
the simulated machine, as they do for ordinary universal simulation. -/
def PolynomialTimeOverhead (clock : TimeOverhead) : Prop :=
  ∃ coefficient exponent, ∀ program sourceTime,
    clock program sourceTime ≤
      coefficient * (program.length + sourceTime + 1) ^ exponent

/-- A machine is semantically universal when it simulates every deterministic
machine, with any finite number of work tapes, under some computable program
compiler.

Computability of the compiler is essential. Without it the predicate is
trivial: a machine that prints the rest of its input after a leading `0` and
diverges after a leading `1` would qualify, with a compiler that consults the
source machine's halting behavior and output. -/
def IsUniversal (simulator : TM simulatorTapes) : Prop :=
  ∀ (sourceTapes : ℕ) (source : TM sourceTapes),
    ∃ compile : List Bool → List Bool,
      IsComputable compile ∧ simulator.Simulates source compile

/-- Universality relative to a chosen admissibility policy for time overhead.
Every source machine receives a computable semantic compiler, an additive
program-length constant, and an explicit clock satisfying `admissible`. -/
def IsEfficientlyUniversalFor (simulator : TM simulatorTapes)
    (admissible : TimeOverhead → Prop) : Prop :=
  ∀ (sourceTapes : ℕ) (source : TM sourceTapes),
    ∃ (compile : List Bool → List Bool) (constant : ℕ) (clock : TimeOverhead),
      IsComputable compile ∧ simulator.Simulates source compile ∧
      HasAdditiveProgramOverhead compile constant ∧
      simulator.SimulatesInTime source compile clock ∧ admissible clock

/-- Polynomially efficient universality with additive description overhead. -/
def IsEfficientlyUniversal (simulator : TM simulatorTapes) : Prop :=
  simulator.IsEfficientlyUniversalFor PolynomialTimeOverhead

end TM

end Complexity
