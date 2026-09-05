/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Defs
public import Complexitylib.Models.TuringMachine.Universality
import Complexitylib.Models.TuringMachine.Subroutines.CopyOutput

/-!
# Machine-relative Kolmogorov complexity -- proof internals

Proofs supporting the public API in
`Complexitylib.Metacomplexity.Kolmogorov`.
-/


public section

namespace Complexity

namespace TM

variable {n simulatorTapes sourceTapes : ℕ}

theorem plainKolmogorovComplexity_le_internal {machine : TM n}
    {program output : List Bool} (hproduce : machine.Produces program output) :
    machine.plainKolmogorovComplexity output ≤ program.length := by
  apply sInf_le
  exact ⟨program.length, ⟨program, rfl, hproduce⟩, rfl⟩

theorem plainKolmogorovComplexity_eq_top_iff_internal (machine : TM n)
    (output : List Bool) :
    machine.plainKolmogorovComplexity output = ⊤ ↔
      ¬∃ program, machine.Produces program output := by
  rw [plainKolmogorovComplexity, sInf_eq_top]
  constructor
  · intro htop ⟨program, hproduce⟩
    have h := htop (program.length : WithTop ℕ)
      ⟨program.length, ⟨program, rfl, hproduce⟩, rfl⟩
    exact (WithTop.coe_ne_top : (program.length : WithTop ℕ) ≠ ⊤) h
  · intro hnone value hvalue
    obtain ⟨_size, ⟨program, _hlength, hproduce⟩, _hvalue⟩ := hvalue
    exact (hnone ⟨program, hproduce⟩).elim

theorem plainKolmogorovComplexity_witness_internal (machine : TM n)
    (output : List Bool) (hfinite : machine.plainKolmogorovComplexity output ≠ ⊤) :
    ∃ program, (program.length : WithTop ℕ) =
      machine.plainKolmogorovComplexity output ∧ machine.Produces program output := by
  have hexists : ∃ program, machine.Produces program output := by
    by_contra hnone
    exact hfinite ((plainKolmogorovComplexity_eq_top_iff_internal machine output).mpr hnone)
  obtain ⟨program₀, hprogram₀⟩ := hexists
  have hset : ((fun size : ℕ => (size : WithTop ℕ)) ''
      machine.producingProgramSizes output).Nonempty :=
    ⟨program₀.length, program₀.length, ⟨program₀, rfl, hprogram₀⟩, rfl⟩
  have hmem := csInf_mem hset
  obtain ⟨size, ⟨program, hlength, hproduce⟩, hcoe⟩ := hmem
  exact ⟨program, hlength ▸ hcoe, hproduce⟩

theorem plainKolmogorovComplexity_le_coe_iff_internal (machine : TM n)
    (output : List Bool) (bound : ℕ) :
    machine.plainKolmogorovComplexity output ≤ (bound : WithTop ℕ) ↔
      ∃ program, program.length ≤ bound ∧ machine.Produces program output := by
  constructor
  · intro hbound
    have hfinite : machine.plainKolmogorovComplexity output ≠ ⊤ := by
      intro htop
      rw [htop] at hbound
      exact WithTop.not_top_le_coe bound hbound
    obtain ⟨program, hlength, hproduce⟩ :=
      plainKolmogorovComplexity_witness_internal machine output hfinite
    refine ⟨program, ?_, hproduce⟩
    exact WithTop.coe_le_coe.mp (hlength.trans_le hbound)
  · rintro ⟨program, hlength, hproduce⟩
    exact (plainKolmogorovComplexity_le_internal hproduce).trans
      (WithTop.coe_le_coe.mpr hlength)

theorem timeBoundedKolmogorovComplexity_le_internal {machine : TM n}
    {program output : List Bool} {time : ℕ}
    (hproduce : machine.ProducesInTime program output time) :
    machine.timeBoundedKolmogorovComplexity output time ≤ program.length := by
  apply sInf_le
  exact ⟨program.length, ⟨program, rfl, hproduce⟩, rfl⟩

theorem timeBoundedKolmogorovComplexity_eq_top_iff_internal (machine : TM n)
    (output : List Bool) (time : ℕ) :
    machine.timeBoundedKolmogorovComplexity output time = ⊤ ↔
      ¬∃ program, machine.ProducesInTime program output time := by
  rw [timeBoundedKolmogorovComplexity, sInf_eq_top]
  constructor
  · intro htop ⟨program, hproduce⟩
    have h := htop (program.length : WithTop ℕ)
      ⟨program.length, ⟨program, rfl, hproduce⟩, rfl⟩
    exact (WithTop.coe_ne_top : (program.length : WithTop ℕ) ≠ ⊤) h
  · intro hnone value hvalue
    obtain ⟨_size, ⟨program, _hlength, hproduce⟩, _hvalue⟩ := hvalue
    exact (hnone ⟨program, hproduce⟩).elim

theorem timeBoundedKolmogorovComplexity_witness_internal (machine : TM n)
    (output : List Bool) (time : ℕ)
    (hfinite : machine.timeBoundedKolmogorovComplexity output time ≠ ⊤) :
    ∃ program, (program.length : WithTop ℕ) =
      machine.timeBoundedKolmogorovComplexity output time ∧
      machine.ProducesInTime program output time := by
  have hexists : ∃ program, machine.ProducesInTime program output time := by
    by_contra hnone
    exact hfinite
      ((timeBoundedKolmogorovComplexity_eq_top_iff_internal machine output time).mpr hnone)
  obtain ⟨program₀, hprogram₀⟩ := hexists
  have hset : ((fun size : ℕ => (size : WithTop ℕ)) ''
      machine.timeBoundedProducingProgramSizes output time).Nonempty :=
    ⟨program₀.length, program₀.length, ⟨program₀, rfl, hprogram₀⟩, rfl⟩
  have hmem := csInf_mem hset
  obtain ⟨size, ⟨program, hlength, hproduce⟩, hcoe⟩ := hmem
  exact ⟨program, hlength ▸ hcoe, hproduce⟩

theorem timeBoundedKolmogorovComplexity_le_time_internal (machine : TM n)
    (output : List Bool) (time : ℕ)
    (hfinite : machine.timeBoundedKolmogorovComplexity output time ≠ ⊤) :
    machine.timeBoundedKolmogorovComplexity output time ≤
      (time : WithTop ℕ) := by
  obtain ⟨program, _hlength, hproduce⟩ :=
    timeBoundedKolmogorovComplexity_witness_internal
      machine output time hfinite
  have hshort := producesInTime_take_internal hproduce
  exact (timeBoundedKolmogorovComplexity_le_internal hshort).trans
    (WithTop.coe_le_coe.mpr (List.length_take_le time program))

theorem timeBoundedKolmogorovComplexity_le_coe_iff_internal (machine : TM n)
    (output : List Bool) (time bound : ℕ) :
    machine.timeBoundedKolmogorovComplexity output time ≤ (bound : WithTop ℕ) ↔
      ∃ program, program.length ≤ bound ∧
        machine.ProducesInTime program output time := by
  constructor
  · intro hbound
    have hfinite : machine.timeBoundedKolmogorovComplexity output time ≠ ⊤ := by
      intro htop
      rw [htop] at hbound
      exact WithTop.not_top_le_coe bound hbound
    obtain ⟨program, hlength, hproduce⟩ :=
      timeBoundedKolmogorovComplexity_witness_internal machine output time hfinite
    refine ⟨program, ?_, hproduce⟩
    exact WithTop.coe_le_coe.mp (hlength.trans_le hbound)
  · rintro ⟨program, hlength, hproduce⟩
    exact (timeBoundedKolmogorovComplexity_le_internal hproduce).trans
      (WithTop.coe_le_coe.mpr hlength)

theorem timeBoundedKolmogorovComplexity_lt_coe_iff_internal (machine : TM n)
    (output : List Bool) (time bound : ℕ) :
    machine.timeBoundedKolmogorovComplexity output time < (bound : WithTop ℕ) ↔
      ∃ program, program.length < bound ∧
        machine.ProducesInTime program output time := by
  constructor
  · intro hbound
    have hfinite : machine.timeBoundedKolmogorovComplexity output time ≠ ⊤ := by
      intro htop
      rw [htop] at hbound
      exact (not_lt_of_ge le_top) hbound
    obtain ⟨program, hlength, hproduce⟩ :=
      timeBoundedKolmogorovComplexity_witness_internal machine output time hfinite
    refine ⟨program, ?_, hproduce⟩
    exact WithTop.coe_lt_coe.mp (hlength.trans_lt hbound)
  · rintro ⟨program, hlength, hproduce⟩
    exact (timeBoundedKolmogorovComplexity_le_internal hproduce).trans_lt
      (WithTop.coe_lt_coe.mpr hlength)

theorem timeBoundedKolmogorovComplexity_mono_internal (machine : TM n)
    (output : List Bool) {first second : ℕ} (hclock : first ≤ second) :
    machine.timeBoundedKolmogorovComplexity output second ≤
      machine.timeBoundedKolmogorovComplexity output first := by
  apply le_sInf
  rintro _value ⟨size, ⟨program, hlength, hproduce⟩, rfl⟩
  subst size
  exact timeBoundedKolmogorovComplexity_le_internal (hproduce.mono hclock)

theorem plainKolmogorovComplexity_le_timeBounded_internal (machine : TM n)
    (output : List Bool) (time : ℕ) :
    machine.plainKolmogorovComplexity output ≤
      machine.timeBoundedKolmogorovComplexity output time := by
  apply le_sInf
  rintro _value ⟨size, ⟨program, hlength, hproduce⟩, rfl⟩
  subst size
  exact plainKolmogorovComplexity_le_internal (produces_of_producesInTime hproduce)

theorem simulates_plainKolmogorovComplexity_le_add_internal
    {simulator : TM simulatorTapes} {source : TM sourceTapes}
    {compile : List Bool → List Bool} {constant : ℕ}
    (hsim : simulator.Simulates source compile)
    (hlength : HasAdditiveProgramOverhead compile constant) (output : List Bool) :
    simulator.plainKolmogorovComplexity output ≤
      source.plainKolmogorovComplexity output + (constant : WithTop ℕ) := by
  by_cases htop : source.plainKolmogorovComplexity output = ⊤
  · simp [htop]
  · obtain ⟨program, hprogramLength, hproduce⟩ :=
      plainKolmogorovComplexity_witness_internal source output htop
    have hcompiled := plainKolmogorovComplexity_le_internal
      ((hsim.produces_iff program output).mpr hproduce)
    rw [← hprogramLength]
    exact hcompiled.trans (WithTop.coe_le_coe.mpr (hlength program))

theorem polynomialTimeOverhead_kolmogorov_transfer_internal
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
          (bound + constant : ℕ) := by
  obtain ⟨coefficient, exponent, hclock⟩ := hclock
  refine ⟨coefficient, exponent, fun output sourceTime bound hsource => ?_⟩
  obtain ⟨program, hprogramLength, hproduce⟩ :=
    (timeBoundedKolmogorovComplexity_le_coe_iff_internal
      source output sourceTime bound).mp hsource
  have htime : clock program sourceTime ≤
      coefficient * (bound + sourceTime + 1) ^ exponent := by
    exact (hclock program sourceTime).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) exponent))
  have hcompiled := (hsim.produces program output sourceTime hproduce).mono htime
  have hcompiledLength : (compile program).length ≤ bound + constant :=
    (hlength program).trans (Nat.add_le_add_right hprogramLength constant)
  exact (timeBoundedKolmogorovComplexity_le_internal hcompiled).trans
    (WithTop.coe_le_coe.mpr hcompiledLength)

theorem IsUniversal.plainKolmogorovComplexity_ne_top_internal
    {simulator : TM simulatorTapes} (huniversal : simulator.IsUniversal)
    (output : List Bool) :
    simulator.plainKolmogorovComplexity output ≠ ⊤ := by
  obtain ⟨compile, hsimulates⟩ :=
    huniversal 0 (copyInputToOutputTM (n := 0))
  have hsource : (copyInputToOutputTM (n := 0)).ProducesInTime output output
      (output.length + 2) := by
    simpa [TM.ProducesInTime] using (copyInputToOutputTM_computesInTime 0 output)
  have hcompiled : simulator.Produces (compile output) output :=
    (hsimulates.produces_iff output output).mpr
      (produces_of_producesInTime hsource)
  intro htop
  exact (plainKolmogorovComplexity_eq_top_iff_internal simulator output).mp
    htop ⟨compile output, hcompiled⟩

theorem IsUniversal.exists_timeBoundedKolmogorovComplexity_ne_top_internal
    {simulator : TM simulatorTapes} (huniversal : simulator.IsUniversal)
    (output : List Bool) :
    ∃ time, simulator.timeBoundedKolmogorovComplexity output time ≠ ⊤ := by
  obtain ⟨compile, hsimulates⟩ :=
    huniversal 0 (copyInputToOutputTM (n := 0))
  have hsource : (copyInputToOutputTM (n := 0)).ProducesInTime output output
      (output.length + 2) := by
    simpa [TM.ProducesInTime] using (copyInputToOutputTM_computesInTime 0 output)
  have hcompiled : simulator.Produces (compile output) output :=
    (hsimulates.produces_iff output output).mpr
      (produces_of_producesInTime hsource)
  obtain ⟨time, hbounded⟩ :=
    (produces_iff_exists_producesInTime simulator (compile output) output).mp
      hcompiled
  have hle := timeBoundedKolmogorovComplexity_le_internal hbounded
  exact ⟨time, ne_top_of_le_ne_top
    (show ((compile output).length : WithTop ℕ) ≠ ⊤ from WithTop.coe_ne_top)
      hle⟩

theorem IsEfficientlyUniversal.timeBoundedKolmogorovComplexity_printer_internal
    {simulator : TM simulatorTapes}
    (huniversal : simulator.IsEfficientlyUniversal) :
    ∃ constant coefficient exponent, ∀ (output : List Bool) (time : ℕ),
      coefficient * (2 * output.length + 3) ^ exponent ≤ time →
        simulator.timeBoundedKolmogorovComplexity output time ≤
          (output.length + constant : ℕ) := by
  obtain ⟨compile, constant, clock, _hsimulates, hlength, htimed, hclock⟩ :=
    huniversal 0 (copyInputToOutputTM (n := 0))
  obtain ⟨coefficient, exponent, hclock⟩ := hclock
  refine ⟨constant, coefficient, exponent, ?_⟩
  intro output time htime
  have hsource : (copyInputToOutputTM (n := 0)).ProducesInTime output output
      (output.length + 2) := by
    simpa [TM.ProducesInTime] using (copyInputToOutputTM_computesInTime 0 output)
  have hcompiled := htimed.produces output output (output.length + 2) hsource
  have hclockBound := hclock output (output.length + 2)
  have harg : output.length + (output.length + 2) + 1 =
      2 * output.length + 3 := by
    omega
  rw [harg] at hclockBound
  have hcompiled' := hcompiled.mono (hclockBound.trans htime)
  exact (timeBoundedKolmogorovComplexity_le_internal hcompiled').trans
    (WithTop.coe_le_coe.mpr (hlength output))

theorem IsEfficientlyUniversal.plainKolmogorovComplexity_le_length_add_internal
    {simulator : TM simulatorTapes}
    (huniversal : simulator.IsEfficientlyUniversal) :
    ∃ constant, ∀ output : List Bool,
      simulator.plainKolmogorovComplexity output ≤
        (output.length + constant : ℕ) := by
  obtain ⟨constant, coefficient, exponent, hprinter⟩ :=
    huniversal.timeBoundedKolmogorovComplexity_printer_internal
  refine ⟨constant, fun output => ?_⟩
  exact (plainKolmogorovComplexity_le_timeBounded_internal simulator output
    (coefficient * (2 * output.length + 3) ^ exponent)).trans
      (hprinter output _ le_rfl)

theorem IsEfficientlyUniversal.exists_polynomial_printer_finite_internal
    {simulator : TM simulatorTapes}
    (huniversal : simulator.IsEfficientlyUniversal) :
    ∃ coefficient exponent, ∀ output : List Bool,
      simulator.timeBoundedKolmogorovComplexity output
        (coefficient * (2 * output.length + 3) ^ exponent) ≠ ⊤ := by
  obtain ⟨constant, coefficient, exponent, hprinter⟩ :=
    huniversal.timeBoundedKolmogorovComplexity_printer_internal
  refine ⟨coefficient, exponent, fun output => ?_⟩
  exact ne_top_of_le_ne_top
    (show ((output.length + constant : ℕ) : WithTop ℕ) ≠ ⊤ from
      WithTop.coe_ne_top)
    (hprinter output _ le_rfl)

end TM

end Complexity
