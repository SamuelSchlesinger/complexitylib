/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Asymptotics.PolyBound
public import Complexitylib.Classes.FNP.Defs
public import Complexitylib.Metacomplexity.Kolmogorov.Internal
public import Complexitylib.Metacomplexity.MINKT.Defs

/-!
# Minimum time-bounded Kolmogorov complexity -- proof internals

Proofs of canonical-code exactness, short-program semantics, and monotonicity
for the public MINKT API.
-/


public section

namespace Complexity

namespace MINKT

namespace Instance

variable {tapes : ℕ}

theorem length_unaryClock_internal (inst : Instance) :
    inst.unaryClock.length = inst.time := by
  simp [unaryClock]

theorem decode?_encode_internal (inst : Instance) :
    decode? inst.encode = some inst := by
  rcases inst with ⟨output, time⟩
  simp [decode?, encode, unaryClock]

theorem decode?_eq_some_iff_internal (bits : List Bool) (inst : Instance) :
    decode? bits = some inst ↔ bits = inst.encode := by
  constructor
  · intro hdecode
    cases hpair : unpair? bits with
    | none => simp [decode?, hpair] at hdecode
    | some components =>
        rcases components with ⟨output, clock⟩
        by_cases hclock : clock = List.replicate clock.length true
        · have hbits := eq_pair_of_unpair?_eq_some hpair
          rw [decode?, hpair] at hdecode
          change (if clock = List.replicate clock.length true then
              some { output := output, time := clock.length } else none) =
            some inst at hdecode
          rw [ite_eq_left hclock] at hdecode
          cases hdecode
          calc
            bits = pair output clock := hbits
            _ = pair output (List.replicate clock.length true) :=
              congrArg (pair output) hclock
            _ = encode { output, time := clock.length } := rfl
        · rw [decode?, hpair] at hdecode
          change (if clock = List.replicate clock.length true then
              some { output := output, time := clock.length } else none) =
            some inst at hdecode
          rw [ite_eq_right hclock] at hdecode
          contradiction
  · rintro rfl
    exact decode?_encode_internal inst

theorem decode?_eq_none_iff_internal (bits : List Bool) :
    decode? bits = none ↔ ¬ ∃ inst : Instance, bits = inst.encode := by
  constructor
  · intro hnone ⟨inst, hbits⟩
    rw [hbits, decode?_encode_internal] at hnone
    contradiction
  · intro hnoncanonical
    cases hdecode : decode? bits with
    | none => rfl
    | some inst =>
        exact (hnoncanonical
          ⟨inst, (decode?_eq_some_iff_internal bits inst).mp hdecode⟩).elim

theorem encode_injective_internal : Function.Injective encode := by
  intro first second hencode
  have hfirst := decode?_encode_internal first
  rw [hencode, decode?_encode_internal second] at hfirst
  exact Option.some.inj hfirst.symm

theorem length_encode_internal (inst : Instance) :
    inst.encode.length = 2 * inst.output.length + 2 + inst.time := by
  simp [encode, length_unaryClock_internal]

theorem isBelow_iff_hasProgramShorterThan_internal (inst : Instance)
    (machine : TM tapes) (threshold : ℕ → ℕ) :
    inst.IsBelow machine threshold ↔
      inst.HasProgramShorterThan machine threshold := by
  exact TM.timeBoundedKolmogorovComplexity_lt_coe_iff_internal
    machine inst.output inst.time (threshold inst.output.length)

theorem isBelow_withTime_mono_internal (inst : Instance)
    (machine : TM tapes) (threshold : ℕ → ℕ) {first second : ℕ}
    (hclock : first ≤ second)
    (hsmall : (inst.withTime first).IsBelow machine threshold) :
    (inst.withTime second).IsBelow machine threshold := by
  exact (TM.timeBoundedKolmogorovComplexity_mono_internal
    machine inst.output hclock).trans_lt hsmall

theorem isBelow_threshold_mono_internal (inst : Instance)
    (machine : TM tapes) {first second : ℕ → ℕ}
    (hthreshold : ∀ length, first length ≤ second length)
    (hsmall : inst.IsBelow machine first) :
    inst.IsBelow machine second := by
  exact hsmall.trans_le (WithTop.coe_le_coe.mpr (hthreshold inst.output.length))

end Instance

theorem programWitnessRelation_length_le_polynomial_internal
    {tapes : ℕ} (machine : TM tapes) (threshold : ℕ → ℕ)
    (polynomial : Polynomial ℕ)
    (hthreshold : ∀ length, threshold length ≤ polynomial.eval length)
    {bits program : List Bool}
    (hrelation : ProgramWitnessRelation machine threshold bits program) :
    program.length ≤ polynomial.eval bits.length := by
  obtain ⟨inst, hdecode, hlength, _hproduce⟩ := hrelation
  have hcanonical := (Instance.decode?_eq_some_iff_internal bits inst).mp hdecode
  rw [hcanonical]
  have houtputLength : inst.output.length ≤ inst.encode.length := by
    rw [Instance.length_encode_internal]
    omega
  exact (Nat.le_of_lt hlength).trans
    ((hthreshold inst.output.length).trans
      (polynomial_eval_mono_nat polynomial houtputLength))

theorem programWitnessRelation_polyBalanced_internal
    {tapes : ℕ} (machine : TM tapes) (threshold : ℕ → ℕ)
    (hthreshold : PolyBound threshold) :
    PolyBalanced (ProgramWitnessRelation machine threshold) := by
  obtain ⟨polynomial, hpolynomial⟩ := hthreshold
  exact ⟨polynomial, fun _bits _program hrelation =>
    programWitnessRelation_length_le_polynomial_internal
      machine threshold polynomial hpolynomial hrelation⟩

theorem programWitnessRelation_mem_FNP_of_pairLang_mem_P_internal
    {tapes : ℕ} (machine : TM tapes) (threshold : ℕ → ℕ)
    (hthreshold : PolyBound threshold)
    (hverifier : pairLang (ProgramWitnessRelation machine threshold) ∈ P) :
    ProgramWitnessRelation machine threshold ∈ FNP :=
  ⟨programWitnessRelation_polyBalanced_internal machine threshold hthreshold,
    hverifier⟩

end MINKT

end Complexity
