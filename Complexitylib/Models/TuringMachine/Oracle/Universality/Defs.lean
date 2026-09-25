/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Oracle.OutputSemantics.Defs
public import Complexitylib.Models.TuringMachine.Universality.Defs

/-!
# Oracle-uniform universal-machine interfaces -- definitions

An oracle simulation uses one compiler and one clock for every Boolean oracle.
This quantifier order is essential: allowing the compiler to depend on the
oracle could hide an entire test truth table in a nominal constant.

The admissibility policies for program length and time reuse the ordinary
machine interfaces because they concern only finite program strings and numeric
clocks. Oracle lookup cost is already charged by `OracleTM.reachesIn`.
-/


@[expose] public section

namespace Complexity

namespace OracleTM

variable {simulatorTapes sourceTapes : ℕ}

/-- Uniform semantic simulation of one oracle machine by another. The compiler
is independent of the Boolean oracle. -/
structure Simulates (simulator : OracleTM simulatorTapes)
    (source : OracleTM sourceTapes) (compile : List Bool → List Bool) : Prop where
  /-- Compilation preserves and reflects halting for every oracle. -/
  halts_iff : ∀ oracle program,
    simulator.Halts oracle (compile program) ↔
      source.Halts oracle program
  /-- Compilation preserves and reflects eventual exact output for every
  oracle. -/
  produces_iff : ∀ oracle program output,
    simulator.Produces oracle (compile program) output ↔
      source.Produces oracle program output

/-- Forward oracle-uniform simulation under an explicit clock transform. -/
structure SimulatesInTime (simulator : OracleTM simulatorTapes)
    (source : OracleTM sourceTapes) (compile : List Bool → List Bool)
    (clock : TM.TimeOverhead) : Prop where
  /-- Bounded production transfers for every oracle under the same clock. -/
  produces : ∀ oracle program output sourceTime,
    source.ProducesInTime oracle program output sourceTime →
      simulator.ProducesInTime oracle (compile program) output
        (clock program sourceTime)

/-- Oracle universality uses one computable compiler per source machine,
uniformly over all Boolean oracles. As for `TM.IsUniversal`, computability of
the compiler keeps undecidable information out of the compiled program. -/
def IsUniversal (simulator : OracleTM simulatorTapes) : Prop :=
  ∀ (sourceTapes : ℕ) (source : OracleTM sourceTapes),
    ∃ compile : List Bool → List Bool,
      TM.IsComputable compile ∧ simulator.Simulates source compile

/-- Oracle universality relative to an admissible clock policy. The computable
compiler, additive length constant, and clock are all selected before the
oracle. -/
def IsEfficientlyUniversalFor (simulator : OracleTM simulatorTapes)
    (admissible : TM.TimeOverhead → Prop) : Prop :=
  ∀ (sourceTapes : ℕ) (source : OracleTM sourceTapes),
    ∃ (compile : List Bool → List Bool) (constant : ℕ)
      (clock : TM.TimeOverhead),
      TM.IsComputable compile ∧ simulator.Simulates source compile ∧
      TM.HasAdditiveProgramOverhead compile constant ∧
      simulator.SimulatesInTime source compile clock ∧ admissible clock

/-- Polynomially efficient oracle universality with additive description
overhead, uniformly across every Boolean oracle. -/
def IsEfficientlyUniversal (simulator : OracleTM simulatorTapes) : Prop :=
  simulator.IsEfficientlyUniversalFor TM.PolynomialTimeOverhead

end OracleTM

end Complexity
