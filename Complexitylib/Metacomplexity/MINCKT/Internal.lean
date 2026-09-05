/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Defs
import Complexitylib.Metacomplexity.Kolmogorov.Conditional.Internal

/-!
# Minimum conditional time-bounded Kolmogorov complexity -- proof internals
-/


public section

namespace Complexity

namespace MINCKT

namespace Instance

variable {tapes : ℕ}

theorem length_unaryClock_internal (inst : Instance) :
    inst.unaryClock.length = inst.time := by
  simp [unaryClock]

theorem decode?_encode_internal (inst : Instance) :
    decode? inst.encode = some inst := by
  rcases inst with ⟨output, condition, time⟩
  simp [decode?, encode, unaryClock]

theorem decode?_eq_some_iff_internal (bits : List Bool) (inst : Instance) :
    decode? bits = some inst ↔ bits = inst.encode := by
  constructor
  · intro hdecode
    cases houter : unpair? bits with
    | none => simp [decode?, houter] at hdecode
    | some outerComponents =>
        rcases outerComponents with ⟨output, remaining⟩
        cases hinner : unpair? remaining with
        | none => simp [decode?, houter, hinner] at hdecode
        | some innerComponents =>
            rcases innerComponents with ⟨condition, clock⟩
            rw [decode?, houter] at hdecode
            dsimp only at hdecode
            rw [hinner] at hdecode
            change (if clock = List.replicate clock.length true then
                some (Instance.mk output condition clock.length)
              else none) = some inst at hdecode
            by_cases hclock : clock = List.replicate clock.length true
            · have hbits := eq_pair_of_unpair?_eq_some houter
              have hremaining := eq_pair_of_unpair?_eq_some hinner
              rw [ite_eq_left hclock] at hdecode
              cases hdecode
              calc
                bits = pair output remaining := hbits
                _ = pair output (pair condition clock) :=
                  congrArg (pair output) hremaining
                _ = pair output
                    (pair condition (List.replicate clock.length true)) := by
                  exact congrArg (fun current => pair output (pair condition current))
                    hclock
                _ = encode
                    { output, condition, time := clock.length } := rfl
            · rw [ite_eq_right hclock] at hdecode
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
    inst.encode.length =
      2 * inst.output.length + 2 * inst.condition.length + inst.time + 4 := by
  simp [encode, length_unaryClock_internal]
  omega

theorem isAtMost_iff_hasProgramAtMost_internal (inst : Instance)
    (machine : OracleTM tapes) (threshold : ℕ) :
    inst.IsAtMost machine threshold ↔
      inst.HasProgramAtMost machine threshold := by
  exact
    OracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity_le_coe_iff_internal
      machine inst.output inst.condition inst.time threshold

theorem isAtMost_withTime_mono_internal (inst : Instance)
    (machine : OracleTM tapes) (threshold : ℕ) {first second : ℕ}
    (hclock : first ≤ second)
    (hsmall : (inst.withTime first).IsAtMost machine threshold) :
    (inst.withTime second).IsAtMost machine threshold := by
  exact
    (OracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity_mono_internal
      machine inst.output inst.condition hclock).trans hsmall

theorem isAtMost_threshold_mono_internal (inst : Instance)
    (machine : OracleTM tapes) {first second : ℕ}
    (hthreshold : first ≤ second)
    (hsmall : inst.IsAtMost machine first) :
    inst.IsAtMost machine second := by
  exact hsmall.trans (WithTop.coe_le_coe.mpr hthreshold)

end Instance

end MINCKT

end Complexity
