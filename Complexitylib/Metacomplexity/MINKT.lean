/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINKT.Defs
public import Complexitylib.Metacomplexity.MINKT.Gap
public import Complexitylib.Metacomplexity.MINKT.Gap.Logarithmic
public import Complexitylib.Metacomplexity.MINKT.Gap.Logarithmic.Efficient
public import Complexitylib.Metacomplexity.MINKT.Internal
import Complexitylib.Classes.NP.WitnessConstruction

/-!
# The Minimum Time-Bounded Kolmogorov Complexity problem

This module exposes a canonical, total machine-relative `MINKT[r]` language.
Its inputs are encoded as `(x, 1^t)`, and its strict threshold convention is

`C_U^t(x) < r(|x|)`.

Universality is deliberately separate: all definitions and finite facts hold
for an arbitrary deterministic machine, while later invariance and hardness
results can ask for the precise efficient-universality property they use.

## Main definitions

- `MINKT.Instance` -- an output string and primitive unary clock
- `MINKT.Instance.encode` / `decode?` -- canonical total codec
- `MINKT.Instance.IsBelow` -- strict time-bounded complexity predicate
- `MINKT.ProgramWitnessRelation` -- direct short-program witness relation
- `MINKT` -- encoded language, with malformed strings rejected
- `GapMINKT.Logarithmic.problem` -- exact `s + log_2(tau)` promise
-/


public section

namespace Complexity

namespace MINKT

namespace Instance

variable {tapes : ℕ}

/-- The unary clock contains exactly `time` bits. -/
@[simp] theorem length_unaryClock (inst : Instance) :
    inst.unaryClock.length = inst.time :=
  length_unaryClock_internal inst

/-- Canonical MINKT encodings decode to their original instances. -/
@[simp] theorem decode?_encode (inst : Instance) :
    decode? inst.encode = some inst :=
  decode?_encode_internal inst

/-- Exact decoding accepts precisely canonical output/unary-clock encodings. -/
theorem decode?_eq_some_iff (bits : List Bool) (inst : Instance) :
    decode? bits = some inst ↔ bits = inst.encode :=
  decode?_eq_some_iff_internal bits inst

/-- Decoding rejects exactly the noncanonical strings. -/
theorem decode?_eq_none_iff (bits : List Bool) :
    decode? bits = none ↔ ¬ ∃ inst : Instance, bits = inst.encode :=
  decode?_eq_none_iff_internal bits

/-- Canonical MINKT encoding is injective. -/
theorem encode_injective : Function.Injective encode :=
  encode_injective_internal

/-- Exact encoded length: a doubled self-delimiting output followed by the
unary clock. -/
@[simp] theorem length_encode (inst : Instance) :
    inst.encode.length = 2 * inst.output.length + 2 + inst.time :=
  length_encode_internal inst

/-- Strict time-bounded complexity is equivalent to a producing program whose
length is strictly below the length-dependent threshold. -/
theorem isBelow_iff_hasProgramShorterThan (inst : Instance)
    (machine : TM tapes) (threshold : ℕ → ℕ) :
    inst.IsBelow machine threshold ↔
      inst.HasProgramShorterThan machine threshold :=
  isBelow_iff_hasProgramShorterThan_internal inst machine threshold

/-- Increasing an instance's clock preserves a MINKT yes-instance. -/
theorem IsBelow.withTime_mono (inst : Instance)
    (machine : TM tapes) (threshold : ℕ → ℕ) {first second : ℕ}
    (hclock : first ≤ second)
    (hsmall : (inst.withTime first).IsBelow machine threshold) :
    (inst.withTime second).IsBelow machine threshold :=
  isBelow_withTime_mono_internal inst machine threshold hclock hsmall

/-- Pointwise increasing the threshold preserves a MINKT yes-instance. -/
theorem IsBelow.threshold_mono (inst : Instance)
    (machine : TM tapes) {first second : ℕ → ℕ}
    (hthreshold : ∀ length, first length ≤ second length)
    (hsmall : inst.IsBelow machine first) :
    inst.IsBelow machine second :=
  isBelow_threshold_mono_internal inst machine hthreshold hsmall

end Instance

end MINKT

/-- A canonical code belongs to `MINKT[threshold]` exactly when its instance
satisfies the strict time-bounded complexity inequality. -/
@[simp] theorem MINKT.mem_encode_iff {tapes : ℕ} (machine : TM tapes)
    (threshold : ℕ → ℕ) (inst : MINKT.Instance) :
    inst.encode ∈ MINKT machine threshold ↔ inst.IsBelow machine threshold := by
  simp [MINKT]

/-- Canonical membership has an exact direct short-program characterization. -/
theorem MINKT.mem_encode_iff_exists_program {tapes : ℕ} (machine : TM tapes)
    (threshold : ℕ → ℕ) (inst : MINKT.Instance) :
    inst.encode ∈ MINKT machine threshold ↔
      ∃ program, program.length < threshold inst.output.length ∧
        machine.ProducesInTime program inst.output inst.time := by
  rw [MINKT.mem_encode_iff,
    MINKT.Instance.isBelow_iff_hasProgramShorterThan]
  rfl

/-- Every malformed instance code is rejected by the total MINKT language. -/
theorem MINKT.not_mem_of_decode?_eq_none {tapes : ℕ} {machine : TM tapes}
    {threshold : ℕ → ℕ} {bits : List Bool}
    (hdecode : MINKT.Instance.decode? bits = none) :
    bits ∉ MINKT machine threshold := by
  simp [MINKT, hdecode]

/-- Decoded membership has an explicit unique-instance witness. -/
theorem MINKT.mem_iff_exists_instance {tapes : ℕ} (machine : TM tapes)
    (threshold : ℕ → ℕ) (bits : List Bool) :
    bits ∈ MINKT machine threshold ↔
      ∃ inst : MINKT.Instance,
        MINKT.Instance.decode? bits = some inst ∧
          inst.IsBelow machine threshold := by
  cases hdecode : MINKT.Instance.decode? bits with
  | none => simp [MINKT, hdecode]
  | some inst => simp [MINKT, hdecode]

/-- MINKT membership is exactly existence of a raw short-program witness. -/
theorem MINKT.mem_iff_exists_programWitness {tapes : ℕ} (machine : TM tapes)
    (threshold : ℕ → ℕ) (bits : List Bool) :
    bits ∈ MINKT machine threshold ↔
      ∃ program, MINKT.ProgramWitnessRelation machine threshold bits program := by
  rw [MINKT.mem_iff_exists_instance]
  constructor
  · rintro ⟨inst, hdecode, hisBelow⟩
    obtain ⟨program, hlength, hproduce⟩ :=
      (MINKT.Instance.isBelow_iff_hasProgramShorterThan
        inst machine threshold).mp hisBelow
    exact ⟨program, inst, hdecode, hlength, hproduce⟩
  · rintro ⟨program, inst, hdecode, hlength, hproduce⟩
    refine ⟨inst, hdecode, ?_⟩
    exact (MINKT.Instance.isBelow_iff_hasProgramShorterThan
      inst machine threshold).mpr ⟨program, hlength, hproduce⟩

/-- A polynomial bound on the threshold gives the same polynomial bound on
every accepted raw program witness, measured against the encoded input. -/
theorem MINKT.programWitnessRelation_length_le_polynomial
    {tapes : ℕ} (machine : TM tapes) (threshold : ℕ → ℕ)
    (polynomial : Polynomial ℕ)
    (hthreshold : ∀ length, threshold length ≤ polynomial.eval length)
    {bits program : List Bool}
    (hrelation : MINKT.ProgramWitnessRelation machine threshold bits program) :
    program.length ≤ polynomial.eval bits.length :=
  MINKT.programWitnessRelation_length_le_polynomial_internal
    machine threshold polynomial hthreshold hrelation

/-- If the MINKT threshold is polynomially bounded, its raw program relation
is polynomially balanced. -/
theorem MINKT.programWitnessRelation_polyBalanced
    {tapes : ℕ} (machine : TM tapes) (threshold : ℕ → ℕ)
    (hthreshold : PolyBound threshold) :
    PolyBalanced (MINKT.ProgramWitnessRelation machine threshold) :=
  MINKT.programWitnessRelation_polyBalanced_internal
    machine threshold hthreshold

/-- With polynomial threshold growth, a polynomial-time paired verifier makes
the raw MINKT program relation an FNP relation. -/
theorem MINKT.programWitnessRelation_mem_FNP_of_pairLang_mem_P
    {tapes : ℕ} (machine : TM tapes) (threshold : ℕ → ℕ)
    (hthreshold : PolyBound threshold)
    (hverifier : pairLang
      (MINKT.ProgramWitnessRelation machine threshold) ∈ P) :
    MINKT.ProgramWitnessRelation machine threshold ∈ FNP :=
  MINKT.programWitnessRelation_mem_FNP_of_pairLang_mem_P_internal
    machine threshold hthreshold hverifier

/-- NP packaging for MINKT: polynomial threshold growth and a polynomial-time
paired verifier suffice. -/
theorem MINKT.mem_NP_of_pairLang_mem_P
    {tapes : ℕ} (machine : TM tapes) (threshold : ℕ → ℕ)
    (hthreshold : PolyBound threshold)
    (hverifier : pairLang
      (MINKT.ProgramWitnessRelation machine threshold) ∈ P) :
    MINKT machine threshold ∈ NP := by
  apply NP.mem_NP_of_FNP
    (MINKT.programWitnessRelation_mem_FNP_of_pairLang_mem_P
      machine threshold hthreshold hverifier)
  intro bits
  exact MINKT.mem_iff_exists_programWitness machine threshold bits

/-- Pointwise threshold growth gives language inclusion. -/
theorem MINKT.mono {tapes : ℕ} (machine : TM tapes)
    {first second : ℕ → ℕ} (hthreshold : ∀ length, first length ≤ second length) :
    MINKT machine first ⊆ MINKT machine second := by
  intro bits hbits
  obtain ⟨inst, hdecode, hsmall⟩ :=
    (MINKT.mem_iff_exists_instance machine first bits).mp hbits
  exact (MINKT.mem_iff_exists_instance machine second bits).mpr
    ⟨inst, hdecode,
      MINKT.Instance.IsBelow.threshold_mono inst machine hthreshold hsmall⟩

end Complexity
