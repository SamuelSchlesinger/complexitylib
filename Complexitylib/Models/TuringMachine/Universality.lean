/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Universality.Internal

/-!
# Generic universal-machine interfaces

This module gives machine-independent definitions of semantic and efficient
universality. A simulation compiler acts on arbitrary binary programs; its
correctness does not mention a concrete description codec. Additive description
overhead and an explicit program-sensitive clock are separate reusable
hypotheses. Universality requires the compiler to be computable.

The default `IsEfficientlyUniversal` policy asks for a polynomial in source
running time and source-program length. `IsEfficientlyUniversalFor` remains
available for sharper policies.

## Main results

- `TM.IsComputable.comp` -- computable string functions compose
- `TM.Simulates.refl`, `TM.Simulates.comp` -- semantic simulation is compositional
- `TM.HasAdditiveProgramOverhead.comp` -- additive compiler costs compose
- `TM.SimulatesInTime.comp` -- exact simulation clocks compose
- `TM.PolynomialTimeOverhead.comp` -- polynomial clocks survive compilation
- `TM.IsEfficientlyUniversalFor.isUniversal` -- efficient implies semantic
- `TM.Simulates.isUniversal` -- universality transfers through a simulator
-/


public section

namespace Complexity

namespace TM

variable {firstTapes secondTapes thirdTapes : ℕ}

/-- Computable string functions are closed under composition. -/
theorem IsComputable.comp {first second : List Bool → List Bool}
    (hsecond : IsComputable second) (hfirst : IsComputable first) :
    IsComputable (second ∘ first) :=
  isComputable_comp_internal hfirst hsecond

/-- Every machine simulates itself under the identity compiler. -/
theorem Simulates.refl (machine : TM firstTapes) : machine.Simulates machine id :=
  simulates_refl_internal machine

/-- Semantic simulations compose, with the inner compiler applied first. -/
theorem Simulates.comp {first : TM firstTapes} {second : TM secondTapes}
    {third : TM thirdTapes} {compileFirst compileSecond : List Bool → List Bool}
    (hFirst : first.Simulates second compileFirst)
    (hSecond : second.Simulates third compileSecond) :
    first.Simulates third (compileFirst ∘ compileSecond) :=
  simulates_comp_internal hFirst hSecond

/-- The identity compiler has zero additive program overhead. -/
theorem HasAdditiveProgramOverhead.id : HasAdditiveProgramOverhead id 0 :=
  additiveProgramOverhead_id_internal

/-- A larger additive constant preserves a compiler-length bound. -/
theorem HasAdditiveProgramOverhead.mono {compile : List Bool → List Bool}
    {first second : ℕ} (hbound : first ≤ second)
    (hoverhead : HasAdditiveProgramOverhead compile first) :
    HasAdditiveProgramOverhead compile second :=
  additiveProgramOverhead_mono_internal hbound hoverhead

/-- Additive compiler-length bounds compose by addition. -/
theorem HasAdditiveProgramOverhead.comp
    {compileFirst compileSecond : List Bool → List Bool} {first second : ℕ}
    (hFirst : HasAdditiveProgramOverhead compileFirst first)
    (hSecond : HasAdditiveProgramOverhead compileSecond second) :
    HasAdditiveProgramOverhead (compileFirst ∘ compileSecond) (second + first) :=
  additiveProgramOverhead_comp_internal hFirst hSecond

/-- Identity execution has the identity time overhead. -/
theorem SimulatesInTime.refl (machine : TM firstTapes) :
    machine.SimulatesInTime machine id (fun _ sourceTime => sourceTime) :=
  simulatesInTime_refl_internal machine

/-- Enlarging a simulation clock preserves a timed simulation. -/
theorem SimulatesInTime.mono {simulator : TM firstTapes} {source : TM secondTapes}
    {compile : List Bool → List Bool} {firstClock secondClock : TimeOverhead}
    (hclock : ∀ program sourceTime, firstClock program sourceTime ≤
      secondClock program sourceTime)
    (hsim : simulator.SimulatesInTime source compile firstClock) :
    simulator.SimulatesInTime source compile secondClock :=
  simulatesInTime_mono_internal hclock hsim

/-- Timed simulations compose by feeding the inner compiled program and clock
to the outer clock. -/
theorem SimulatesInTime.comp {first : TM firstTapes} {second : TM secondTapes}
    {third : TM thirdTapes} {compileFirst compileSecond : List Bool → List Bool}
    {clockFirst clockSecond : TimeOverhead}
    (hFirst : first.SimulatesInTime second compileFirst clockFirst)
    (hSecond : second.SimulatesInTime third compileSecond clockSecond) :
    first.SimulatesInTime third (compileFirst ∘ compileSecond)
      (fun program sourceTime =>
        clockFirst (compileSecond program) (clockSecond program sourceTime)) :=
  simulatesInTime_comp_internal hFirst hSecond

/-- The identity clock is polynomial. -/
theorem PolynomialTimeOverhead.identity :
    PolynomialTimeOverhead (fun _program sourceTime => sourceTime) :=
  polynomialTimeOverhead_identity_internal

/-- Polynomial clocks compose through a compiler with additive length overhead. -/
theorem PolynomialTimeOverhead.comp
    {compileInner : List Bool → List Bool} {additive : ℕ}
    {clockOuter clockInner : TimeOverhead}
    (hlength : HasAdditiveProgramOverhead compileInner additive)
    (hOuter : PolynomialTimeOverhead clockOuter)
    (hInner : PolynomialTimeOverhead clockInner) :
    PolynomialTimeOverhead (fun program sourceTime =>
      clockOuter (compileInner program) (clockInner program sourceTime)) :=
  polynomialTimeOverhead_comp_internal hlength hOuter hInner

/-- Universality for any admissible time policy implies semantic universality. -/
theorem IsEfficientlyUniversalFor.isUniversal {simulator : TM firstTapes}
    {admissible : TimeOverhead → Prop}
    (h : simulator.IsEfficientlyUniversalFor admissible) : simulator.IsUniversal :=
  efficientlyUniversalFor_isUniversal_internal h

/-- Polynomially efficient universality implies semantic universality. -/
theorem IsEfficientlyUniversal.isUniversal {simulator : TM firstTapes}
    (h : simulator.IsEfficientlyUniversal) : simulator.IsUniversal :=
  efficientlyUniversalFor_isUniversal_internal h

/-- Weakening the admissibility policy preserves efficient universality. -/
theorem IsEfficientlyUniversalFor.mono {simulator : TM firstTapes}
    {firstPolicy secondPolicy : TimeOverhead → Prop}
    (hpolicy : ∀ clock, firstPolicy clock → secondPolicy clock)
    (h : simulator.IsEfficientlyUniversalFor firstPolicy) :
    simulator.IsEfficientlyUniversalFor secondPolicy :=
  efficientlyUniversalFor_mono_internal hpolicy h

/-- A simulator of a universal machine under a computable compiler is itself
universal. -/
theorem Simulates.isUniversal {first : TM firstTapes} {second : TM secondTapes}
    {compile : List Bool → List Bool} (hsim : first.Simulates second compile)
    (hcompile : IsComputable compile) (huniversal : second.IsUniversal) :
    first.IsUniversal :=
  simulates_isUniversal_internal hcompile hsim huniversal

end TM

end Complexity
