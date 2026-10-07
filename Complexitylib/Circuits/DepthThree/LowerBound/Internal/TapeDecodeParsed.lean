/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeParse
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeDecodeBlocks

/-!
# Unrestricted depth-three lower bound: tape decode parsed

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeDecodeParsed.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeDecodeParsed

open TapeMultiProgram

/-- Tape-store contents at the output stage of the decode parsed routine. -/
def outputStore (w : List Bool) : TapeStore :=
  TapeDecodeBlocks.outputStore (TapeParse.outputStore w) w

@[simp] theorem outputStore_block (w : List Bool) (kind : InputBlockKind) :
    outputStore w (TapeInputBlocks.outputRegister kind) = inputBlockData w kind :=
  TapeDecodeBlocks.outputStore_block _ _ _

theorem outputStore_other (w : List Bool) (q : TapeRegister)
    (h15 : q ≠ 15) (h16 : q ≠ 16) (h17 : q ≠ 17) (h18 : q ≠ 18) :
    outputStore w q = TapeParse.outputStore w q :=
  TapeDecodeBlocks.outputStore_other _ _ _ h15 h16 h17 h18

@[simp] theorem outputStore_data (w : List Bool) :
    outputStore w 2 = List.replicate (dataDimension w.length) true := by
  rw [outputStore_other w 2 (by decide) (by decide) (by decide) (by decide)]
  exact TapeParse.outputStore_data w

@[simp] theorem outputStore_hash (w : List Bool) :
    outputStore w 3 = List.replicate (hashDimension (dataDimension w.length)) true := by
  rw [outputStore_other w 3 (by decide) (by decide) (by decide) (by decide)]
  exact TapeParse.outputStore_hash w

@[simp] theorem outputStore_order (w : List Bool) :
    outputStore w 4 = List.replicate (independenceOrder (dataDimension w.length)) true := by
  rw [outputStore_other w 4 (by decide) (by decide) (by decide) (by decide)]
  exact TapeParse.outputStore_order w

theorem outputStore_empty (w : List Bool) (q : TapeRegister)
    (h0 : q ≠ 0) (h1 : q ≠ 1) (h2 : q ≠ 2) (h3 : q ≠ 3)
    (h4 : q ≠ 4) (h8 : q ≠ 8) (h15 : q ≠ 15) (h16 : q ≠ 16)
    (h17 : q ≠ 17) (h18 : q ≠ 18) : outputStore w q = [] := by
  rw [outputStore_other w q h15 h16 h17 h18]
  exact TapeParse.outputStore_empty w q h0 h1 h2 h3 h4 h8

theorem runs_decode (w : List Bool) (hfit : InputFits w) :
    RunsIn TapeDecodeBlocks.program.step
      (cfg TapeDecodeBlocks.start (storeTapes (TapeParse.outputStore w)))
      (cfg TapeDecodeBlocks.done (storeTapes (outputStore w)))
      (804 * (w.length + 1) ^ 2) := by
  apply TapeDecodeBlocks.runs_decode _ w hfit
  · exact TapeParse.outputStore_input w
  · exact TapeParse.outputStore_data w
  · exact TapeParse.outputStore_hash w
  · exact TapeParse.outputStore_order w
  all_goals apply TapeParse.outputStore_empty <;> decide

end TapeDecodeParsed
end DepthThreeLowerBound

end Complexity
