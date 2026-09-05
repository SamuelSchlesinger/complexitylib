/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Oracle.Defs
public import Complexitylib.Models.TuringMachine.Oracle.OutputSemantics
public import Complexitylib.Models.TuringMachine.Oracle.Universality
public import Complexitylib.Metacomplexity.Kolmogorov.Defs

/-!
# Oracle-relative Kolmogorov complexity -- proof internals
-/


public section

namespace Complexity

namespace OracleTM

variable {n : ℕ}

theorem plainKolmogorovComplexity_le_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {program output : List Bool}
    (hproduce : machine.Produces oracle program output) :
    machine.plainKolmogorovComplexity oracle output ≤ program.length := by
  apply sInf_le
  exact ⟨program.length, ⟨program, rfl, hproduce⟩, rfl⟩

theorem timeBoundedKolmogorovComplexity_le_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {program output : List Bool} {time : ℕ}
    (hproduce : machine.ProducesInTime oracle program output time) :
    machine.timeBoundedKolmogorovComplexity oracle output time ≤
      program.length := by
  apply sInf_le
  exact ⟨program.length, ⟨program, rfl, hproduce⟩, rfl⟩

theorem timeBoundedKolmogorovComplexity_eq_top_iff_internal
    (machine : OracleTM n) (oracle : BooleanOracle)
    (output : List Bool) (time : ℕ) :
    machine.timeBoundedKolmogorovComplexity oracle output time = ⊤ ↔
      ¬∃ program, machine.ProducesInTime oracle program output time := by
  rw [timeBoundedKolmogorovComplexity, sInf_eq_top]
  constructor
  · intro htop ⟨program, hproduce⟩
    have h := htop (program.length : WithTop ℕ)
      ⟨program.length, ⟨program, rfl, hproduce⟩, rfl⟩
    exact (WithTop.coe_ne_top : (program.length : WithTop ℕ) ≠ ⊤) h
  · intro hnone value hvalue
    obtain ⟨_size, ⟨program, _hlength, hproduce⟩, _hvalue⟩ := hvalue
    exact (hnone ⟨program, hproduce⟩).elim

theorem timeBoundedKolmogorovComplexity_witness_internal
    (machine : OracleTM n) (oracle : BooleanOracle)
    (output : List Bool) (time : ℕ)
    (hfinite : machine.timeBoundedKolmogorovComplexity oracle output time ≠ ⊤) :
    ∃ program, (program.length : WithTop ℕ) =
        machine.timeBoundedKolmogorovComplexity oracle output time ∧
      machine.ProducesInTime oracle program output time := by
  have hexists : ∃ program,
      machine.ProducesInTime oracle program output time := by
    by_contra hnone
    exact hfinite
      ((timeBoundedKolmogorovComplexity_eq_top_iff_internal
        machine oracle output time).mpr hnone)
  obtain ⟨program₀, hprogram₀⟩ := hexists
  have hset : ((fun size : ℕ => (size : WithTop ℕ)) ''
      machine.timeBoundedProducingProgramSizes oracle output time).Nonempty :=
    ⟨program₀.length, program₀.length,
      ⟨program₀, rfl, hprogram₀⟩, rfl⟩
  obtain ⟨size, ⟨program, hlength, hproduce⟩, hcoe⟩ := csInf_mem hset
  exact ⟨program, hlength ▸ hcoe, hproduce⟩

theorem timeBoundedKolmogorovComplexity_le_coe_iff_internal
    (machine : OracleTM n) (oracle : BooleanOracle)
    (output : List Bool) (time bound : ℕ) :
    machine.timeBoundedKolmogorovComplexity oracle output time ≤
        (bound : WithTop ℕ) ↔
      ∃ program, program.length ≤ bound ∧
        machine.ProducesInTime oracle program output time := by
  constructor
  · intro hbound
    have hfinite :
        machine.timeBoundedKolmogorovComplexity oracle output time ≠ ⊤ := by
      intro htop
      rw [htop] at hbound
      exact WithTop.not_top_le_coe bound hbound
    obtain ⟨program, hlength, hproduce⟩ :=
      timeBoundedKolmogorovComplexity_witness_internal
        machine oracle output time hfinite
    refine ⟨program, ?_, hproduce⟩
    exact WithTop.coe_le_coe.mp (hlength.trans_le hbound)
  · rintro ⟨program, hlength, hproduce⟩
    exact (timeBoundedKolmogorovComplexity_le_internal hproduce).trans
      (WithTop.coe_le_coe.mpr hlength)

theorem timeBoundedKolmogorovComplexity_mono_internal
    (machine : OracleTM n) (oracle : BooleanOracle)
    (output : List Bool) {first second : ℕ} (hclock : first ≤ second) :
    machine.timeBoundedKolmogorovComplexity oracle output second ≤
      machine.timeBoundedKolmogorovComplexity oracle output first := by
  apply le_sInf
  rintro _value ⟨size, ⟨program, hlength, hproduce⟩, rfl⟩
  subst size
  exact timeBoundedKolmogorovComplexity_le_internal
    (hproduce.mono hclock)

theorem polynomialTimeOverhead_kolmogorov_transfer_internal
    {simulatorTapes sourceTapes : ℕ}
    {simulator : OracleTM simulatorTapes} {source : OracleTM sourceTapes}
    {compile : List Bool → List Bool} {constant : ℕ}
    {clock : TM.TimeOverhead}
    (hsim : simulator.SimulatesInTime source compile clock)
    (hlength : TM.HasAdditiveProgramOverhead compile constant)
    (hclock : TM.PolynomialTimeOverhead clock) :
    ∃ coefficient exponent,
      ∀ (oracle : BooleanOracle) (output : List Bool)
        (sourceTime bound : ℕ),
        source.timeBoundedKolmogorovComplexity oracle output sourceTime ≤
            (bound : WithTop ℕ) →
          simulator.timeBoundedKolmogorovComplexity oracle output
              (coefficient * (bound + sourceTime + 1) ^ exponent) ≤
            (bound + constant : ℕ) := by
  obtain ⟨coefficient, exponent, hclock⟩ := hclock
  refine ⟨coefficient, exponent, ?_⟩
  intro oracle output sourceTime bound hsource
  obtain ⟨program, hprogramLength, hproduce⟩ :=
    (timeBoundedKolmogorovComplexity_le_coe_iff_internal
      source oracle output sourceTime bound).mp hsource
  have htime : clock program sourceTime ≤
      coefficient * (bound + sourceTime + 1) ^ exponent := by
    exact (hclock program sourceTime).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) exponent))
  have hcompiled :=
    (hsim.produces oracle program output sourceTime hproduce).mono htime
  have hcompiledLength : (compile program).length ≤ bound + constant :=
    (hlength program).trans (Nat.add_le_add_right hprogramLength constant)
  exact (timeBoundedKolmogorovComplexity_le_internal hcompiled).trans
    (WithTop.coe_le_coe.mpr hcompiledLength)

end OracleTM

namespace TM

theorem toOracleTM_timeBoundedKolmogorovComplexity_eq_internal
    (machine : TM n) (oracle : BooleanOracle)
    (output : List Bool) (time : ℕ) :
    machine.toOracleTM.timeBoundedKolmogorovComplexity oracle output time =
      machine.timeBoundedKolmogorovComplexity output time := by
  unfold OracleTM.timeBoundedKolmogorovComplexity
  unfold TM.timeBoundedKolmogorovComplexity
  congr 2
  ext size
  simp only [OracleTM.timeBoundedProducingProgramSizes,
    TM.timeBoundedProducingProgramSizes, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨program, hlength, hproduce⟩
    exact ⟨program, hlength,
      (machine.toOracleTM_producesInTime_iff oracle program output time).mp
        hproduce⟩
  · rintro ⟨program, hlength, hproduce⟩
    exact ⟨program, hlength,
      (machine.toOracleTM_producesInTime_iff oracle program output time).mpr
        hproduce⟩

end TM

end Complexity
