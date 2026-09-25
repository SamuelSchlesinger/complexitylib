/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.OutputSemantics
public import Complexitylib.Models.TuringMachine.Universality.Defs
import Complexitylib.Models.TuringMachine.Composition

/-!
# Generic universal-machine interfaces -- proof internals

Proofs supporting the public API in
`Complexitylib.Models.TuringMachine.Universality`.
-/


public section

namespace Complexity

namespace TM

variable {firstTapes secondTapes thirdTapes : ℕ}

theorem isComputable_comp_internal {first second : List Bool → List Bool}
    (hfirst : IsComputable first) (hsecond : IsComputable second) :
    IsComputable (second ∘ first) := by
  obtain ⟨firstTapes, firstMachine, firstTime, hfirstTime⟩ := hfirst
  obtain ⟨secondTapes, secondMachine, secondTime, hsecondTime⟩ := hsecond
  -- The composition theorem needs a monotone second clock; take running maxima.
  let envelope : ℕ → ℕ := fun n => (Finset.range (n + 1)).sup secondTime
  have hmono : Monotone envelope := fun first second hle =>
    Finset.sup_mono (Finset.range_subset_range.mpr (by omega))
  have hle : ∀ n, secondTime n ≤ envelope n := fun n =>
    Finset.le_sup (Finset.self_mem_range_succ n)
  exact ⟨_, compositionTM firstMachine secondMachine, _,
    compositionTM_computesInTime hfirstTime (hsecondTime.mono hle) hmono⟩

theorem simulates_refl_internal (machine : TM firstTapes) :
    machine.Simulates machine id where
  halts_iff _ := Iff.rfl
  produces_iff _ _ := Iff.rfl

theorem simulates_comp_internal {first : TM firstTapes} {second : TM secondTapes}
    {third : TM thirdTapes} {compileFirst : List Bool → List Bool}
    {compileSecond : List Bool → List Bool}
    (hFirst : first.Simulates second compileFirst)
    (hSecond : second.Simulates third compileSecond) :
    first.Simulates third (compileFirst ∘ compileSecond) where
  halts_iff program :=
    (hFirst.halts_iff (compileSecond program)).trans (hSecond.halts_iff program)
  produces_iff program output :=
    (hFirst.produces_iff (compileSecond program) output).trans
      (hSecond.produces_iff program output)

theorem additiveProgramOverhead_id_internal :
    HasAdditiveProgramOverhead id 0 := by
  intro program
  simp

theorem additiveProgramOverhead_mono_internal {compile : List Bool → List Bool}
    {first second : ℕ} (hbound : first ≤ second)
    (hoverhead : HasAdditiveProgramOverhead compile first) :
    HasAdditiveProgramOverhead compile second := by
  intro program
  exact (hoverhead program).trans (by omega)

theorem additiveProgramOverhead_comp_internal
    {compileFirst compileSecond : List Bool → List Bool} {first second : ℕ}
    (hFirst : HasAdditiveProgramOverhead compileFirst first)
    (hSecond : HasAdditiveProgramOverhead compileSecond second) :
    HasAdditiveProgramOverhead (compileFirst ∘ compileSecond) (second + first) := by
  intro program
  dsimp only [Function.comp_apply]
  exact (hFirst (compileSecond program)).trans (by
    have := hSecond program
    omega)

theorem simulatesInTime_refl_internal (machine : TM firstTapes) :
    machine.SimulatesInTime machine id (fun _ sourceTime => sourceTime) where
  halts _program _sourceTime hhalt := hhalt
  produces _program _output _sourceTime hproduce := hproduce

theorem simulatesInTime_mono_internal {simulator : TM firstTapes}
    {source : TM secondTapes} {compile : List Bool → List Bool}
    {firstClock secondClock : TimeOverhead}
    (hclock : ∀ program sourceTime, firstClock program sourceTime ≤
      secondClock program sourceTime)
    (hsim : simulator.SimulatesInTime source compile firstClock) :
    simulator.SimulatesInTime source compile secondClock where
  halts program sourceTime hhalt :=
    (hsim.halts program sourceTime hhalt).mono (hclock program sourceTime)
  produces program output sourceTime hproduce :=
    (hsim.produces program output sourceTime hproduce).mono
      (hclock program sourceTime)

theorem simulatesInTime_comp_internal {first : TM firstTapes}
    {second : TM secondTapes} {third : TM thirdTapes}
    {compileFirst compileSecond : List Bool → List Bool}
    {clockFirst clockSecond : TimeOverhead}
    (hFirst : first.SimulatesInTime second compileFirst clockFirst)
    (hSecond : second.SimulatesInTime third compileSecond clockSecond) :
    first.SimulatesInTime third (compileFirst ∘ compileSecond)
      (fun program sourceTime =>
        clockFirst (compileSecond program) (clockSecond program sourceTime)) where
  halts program sourceTime hhalt :=
    hFirst.halts (compileSecond program) (clockSecond program sourceTime)
      (hSecond.halts program sourceTime hhalt)
  produces program output sourceTime hproduce :=
    hFirst.produces (compileSecond program) output (clockSecond program sourceTime)
      (hSecond.produces program output sourceTime hproduce)

theorem polynomialTimeOverhead_identity_internal :
    PolynomialTimeOverhead (fun _program sourceTime => sourceTime) := by
  refine ⟨1, 1, fun program sourceTime => ?_⟩
  simp only [one_mul, pow_one]
  omega

theorem polynomialTimeOverhead_comp_internal
    {compileInner : List Bool → List Bool} {additive : ℕ}
    {clockOuter clockInner : TimeOverhead}
    (hlength : HasAdditiveProgramOverhead compileInner additive)
    (hOuter : PolynomialTimeOverhead clockOuter)
    (hInner : PolynomialTimeOverhead clockInner) :
    PolynomialTimeOverhead (fun program sourceTime =>
      clockOuter (compileInner program) (clockInner program sourceTime)) := by
  obtain ⟨outerCoefficient, outerExponent, hOuter⟩ := hOuter
  obtain ⟨innerCoefficient, innerExponent, hInner⟩ := hInner
  refine ⟨outerCoefficient * (additive + innerCoefficient + 2) ^ outerExponent,
    (innerExponent + 1) * outerExponent, fun program sourceTime => ?_⟩
  let base := program.length + sourceTime + 1
  let power := base ^ (innerExponent + 1)
  have hbase : 1 ≤ base := by
    dsimp only [base]
    omega
  have hbasePower : base ≤ power := by
    dsimp only [power]
    simpa [pow_one] using
      Nat.pow_le_pow_right hbase (by omega : 1 ≤ innerExponent + 1)
  have hlengthPower : program.length ≤ power := by
    apply le_trans (show program.length ≤ base by dsimp only [base]; omega)
    exact hbasePower
  have honePower : 1 ≤ power := hbase.trans hbasePower
  have hadditivePower : additive ≤ additive * power :=
    Nat.le_mul_of_pos_right additive honePower
  have hinnerPower : base ^ innerExponent ≤ power := by
    dsimp only [power]
    exact Nat.pow_le_pow_right hbase (Nat.le_succ innerExponent)
  have hclockInner : clockInner program sourceTime ≤ innerCoefficient * power :=
    (hInner program sourceTime).trans (Nat.mul_le_mul_left _ hinnerPower)
  have houterBase :
      (compileInner program).length + clockInner program sourceTime + 1 ≤
        (additive + innerCoefficient + 2) * power := by
    calc
      (compileInner program).length + clockInner program sourceTime + 1
          ≤ (program.length + additive) + innerCoefficient * power + 1 :=
            Nat.add_le_add_right
              (Nat.add_le_add (hlength program) hclockInner) 1
      _ ≤ power + additive * power + innerCoefficient * power + power := by omega
      _ = (additive + innerCoefficient + 2) * power := by
        simp only [Nat.add_mul, Nat.succ_mul]
        omega
  calc
    clockOuter (compileInner program) (clockInner program sourceTime)
        ≤ outerCoefficient *
            ((compileInner program).length + clockInner program sourceTime + 1) ^
              outerExponent := hOuter _ _
    _ ≤ outerCoefficient * ((additive + innerCoefficient + 2) * power) ^
          outerExponent :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left houterBase outerExponent)
    _ = (outerCoefficient * (additive + innerCoefficient + 2) ^ outerExponent) *
          base ^ ((innerExponent + 1) * outerExponent) := by
      simp only [mul_pow, power, ← pow_mul, Nat.mul_assoc]

theorem efficientlyUniversalFor_isUniversal_internal {simulator : TM firstTapes}
    {admissible : TimeOverhead → Prop}
    (h : simulator.IsEfficientlyUniversalFor admissible) : simulator.IsUniversal := by
  intro sourceTapes source
  obtain ⟨compile, _constant, _clock, hcompile, hsim, _hlength, _htime, _hadmissible⟩ :=
    h sourceTapes source
  exact ⟨compile, hcompile, hsim⟩

theorem efficientlyUniversalFor_mono_internal {simulator : TM firstTapes}
    {firstPolicy secondPolicy : TimeOverhead → Prop}
    (hpolicy : ∀ clock, firstPolicy clock → secondPolicy clock)
    (h : simulator.IsEfficientlyUniversalFor firstPolicy) :
    simulator.IsEfficientlyUniversalFor secondPolicy := by
  intro sourceTapes source
  obtain ⟨compile, constant, clock, hcompile, hsim, hlength, htime, hadmissible⟩ :=
    h sourceTapes source
  exact ⟨compile, constant, clock, hcompile, hsim, hlength, htime,
    hpolicy clock hadmissible⟩

theorem simulates_isUniversal_internal {first : TM firstTapes} {second : TM secondTapes}
    {compile : List Bool → List Bool} (hcompile : IsComputable compile)
    (hsim : first.Simulates second compile)
    (huniversal : second.IsUniversal) : first.IsUniversal := by
  intro thirdTapes third
  obtain ⟨compileThird, hcompileThird, hthird⟩ := huniversal thirdTapes third
  exact ⟨compile ∘ compileThird, isComputable_comp_internal hcompileThird hcompile,
    simulates_comp_internal hsim hthird⟩

end TM

end Complexity
