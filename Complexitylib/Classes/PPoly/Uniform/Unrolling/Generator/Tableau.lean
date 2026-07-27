/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Tableau.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Tableau.Internal

/-!
# Verified direct-tableau generator

This module exposes the complete append-only generator for the regularly
padded direct-unrolling family. Its concrete binary routine is sound, emits
exactly the family's tagged circuit code (including the separate zero-length
member), and has a verified logarithmic all-prefix auxiliary-space bound.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Emitting all transition layers and restoring the outer counter is sound. -/
theorem emitTransitionSteps_sound (tm : TM k) :
    (emitTransitionSteps tm).Sound :=
  emitTransitionSteps_sound_internal tm

/-- A clean positive-horizon entry with a clear layer counter satisfies the
complete transition loop's domain. -/
theorem emitTransitionSteps_requires (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hloop : values Work.loop₂ = 0)
    (hhorizon : 0 < values Work.horizon) :
    (emitTransitionSteps tm).requires values :=
  emitTransitionSteps_requires_internal tm values hclean hloop hhorizon

/-- The compact transition-layer wrapper is sound. -/
theorem tableauTransitionSteps_sound (tm : TM k) :
    (tableauTransitionSteps tm).Sound :=
  tableauTransitionSteps_sound_internal tm

/-- The compact finalization wrapper is sound. -/
theorem tableauFinalization_sound (tm : TM k) :
    (tableauFinalization tm).Sound :=
  tableauFinalization_sound_internal tm

/-- From the canonical initial configuration base and frontier, the complete
transition loop emits exactly the canonical flattened step stream. -/
theorem emitTransitionSteps_emitted (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) (n : ℕ)
    (hloop : values Work.loop₂ = 0)
    (hconfigBase : values Work.configBase = n)
    (havailable : values Work.available =
      n + configWidth tm.toNTM (values Work.horizon)) :
    (emitTransitionSteps tm).emitted values =
      ((List.finRange (values Work.horizon)).flatMap
        (tm.directStepFragment (values Work.horizon) n)).flatMap
          CircuitCode.RawGate.encode :=
  emitTransitionSteps_emitted_exact_internal tm values hclean hhorizon n hloop
    hconfigBase havailable

/-- The complete positive tableau body is sound. -/
theorem positiveTableauBody_sound (tm : TM k) :
    (positiveTableauBody tm).Sound :=
  positiveTableauBody_sound_internal tm

/-- Every positive canonical input-length vector satisfies the tableau body's
compact entry contract after the polynomial/header preamble. -/
theorem positiveTableauBody_requires (tm : TM k) (q : Polynomial ℕ)
    (n : ℕ) (hn : 0 < n) :
    (positiveTableauBody tm).requires
      (preambleValues tm q
        (BinaryRoutine.inputLengthValues Work.inputLength n)) :=
  positiveTableauBody_requires_internal tm q n hn

/-- On a positive input length, the tableau body emits exactly the encoded raw
gate stream of the padded direct-unrolling member. -/
theorem positiveTableauBody_emitted (tm : TM k) (q : Polynomial ℕ)
    (n : ℕ) [NeZero n] (hn : 0 < n) :
    (positiveTableauBody tm).emitted
        (preambleValues tm q
          (BinaryRoutine.inputLengthValues Work.inputLength n)) =
      (tm.paddedDirectUnrollingRawCircuit
        (TM.directSerializerHorizonPolynomial q).eval n).flatMap
          CircuitCode.RawGate.encode :=
  positiveTableauBody_emitted_internal tm q n hn

/-- The complete zero/positive padded-tableau generator is sound. -/
theorem paddedDirectUnrollingProgram_sound (tm : TM k)
    (q : Polynomial ℕ) : (paddedDirectUnrollingProgram tm q).Sound :=
  paddedDirectUnrollingProgram_sound_internal tm q

/-- The complete program's compact domain holds on every canonical
input-length vector, including length zero. -/
theorem paddedDirectUnrollingProgram_requires_inputLengthValues
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) :
    (paddedDirectUnrollingProgram tm q).requires
      (BinaryRoutine.inputLengthValues Work.inputLength n) :=
  paddedDirectUnrollingProgram_requires_inputLengthValues_internal tm q n

/-- The complete generator emits exactly the regularly padded direct family
code at every input length. -/
theorem paddedDirectUnrollingProgram_emitted (tm : TM k)
    (q : Polynomial ℕ) (n : ℕ) :
    (paddedDirectUnrollingProgram tm q).emitted
        (BinaryRoutine.inputLengthValues Work.inputLength n) =
      tm.paddedDirectUnrollingCode
        (TM.directSerializerHorizonPolynomial q).eval n :=
  paddedDirectUnrollingProgram_emitted_internal tm q n

/-- Counting the fresh input length and running the verified serializer gives
a total transducer for the once-normalized padded code map, with the exact
compositional all-prefix space bound. -/
theorem paddedDirectUnrollingGenerator_computesInSpace
    (tm : TM k) (q : Polynomial ℕ) :
    (BinaryRoutine.afterInputLength Work.inputLength
      (paddedDirectUnrollingProgram tm q)).ComputesInSpace
        (fun input => tm.paddedDirectUnrollingCode
          (TM.directSerializerHorizonPolynomial q).eval input.length)
        (BinaryRoutine.afterInputLengthSpace Work.inputLength
          (paddedDirectUnrollingProgram tm q)) :=
  paddedDirectUnrollingGenerator_computesInSpace_internal tm q

/-- The complete fresh-input serializer uses logarithmic auxiliary space.
Its output may have polynomial length, but the one-way output tape is never
charged as reusable workspace. -/
theorem paddedDirectUnrollingGenerator_space_bigO_log
    (tm : TM k) (q : Polynomial ℕ) :
    BinaryRoutine.afterInputLengthSpace Work.inputLength
        (paddedDirectUnrollingProgram tm q) =O
      (fun n => Nat.log 2 n) :=
  paddedDirectUnrollingGenerator_space_bigO_log_internal tm q

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
