/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Program.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Program.Internal

/-!
# Uniform evaluation of near-halving recursion and final extraction

The complete string program emits one fixed-length word per leaf. It is
polynomial-time in all runtime parameters under the established intermediate
state bound, including an explicit bound for the initial power of two.
Zero executed levels need no entropy or reserve hypothesis. The final stage
reads only its two exact seed words, allowing unused trailing seed bits.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity in
/-- Encoded final extraction agrees with the structured runtime operation. -/
theorem nearHalvingBlockFinishEval_encode (h Q E ell : Nat)
    (state : NearHalvingBlockRunState) :
    nearHalvingBlockFinishEval
      (pair (encodeNearHalvingBlockRun h Q E state) (List.replicate ell true)) =
        nearHalvingBlockFinish E ell state :=
  Internal.nearHalvingBlockFinishEval_encode h Q E ell state

open Complexity in
/-- The total final extraction step is polynomial-time on every encoded input word. -/
@[polytime] theorem nearHalvingBlockFinishEval_mem_FP : nearHalvingBlockFinishEval ∈ FP :=
  Internal.nearHalvingBlockFinishEval_mem_FP

/-- Every executed level doubles the number of fixed-length leaf outputs. -/
theorem nearHalvingBlockExtractorBits_length (N h Q E ell count : Nat)
    (source seeds : List Bool) :
    (nearHalvingBlockExtractorBits N h Q E ell count source seeds).length =
      2 ^ count * ell :=
  Internal.nearHalvingBlockExtractorBits_length N h Q E ell count source seeds

open Complexity in
/-- The complete extractor program composes bounded recursion with shared leaf extraction. -/
theorem nearHalvingBlockExtractorBits_mem_FP {N h Q E ell count : List Bool → Nat}
    {source seeds : List Bool → List Bool}
    (hN : UnaryFn N) (hh : UnaryFn h) (hQ : UnaryFn Q) (hE : UnaryFn E)
    (hell : UnaryFn ell) (hcount : UnaryFn count) (hpower : UnaryFn fun z => 2 ^ h z)
    (hsource : source ∈ FP) (hseeds : seeds ∈ FP)
    (levels : ∀ z, count z ≤ h z)
    (valid : ∀ z, count z = 0 ∨ (nearHalvingBlockEntropy (h z) (Q z) 0 ≤ N z ∧
      2 * (6 * (nearHalvingBlockRate (h z) + 1) *
        explicitCondenserBudget (N z) (nearHalvingBlockEntropy (h z) (Q z) 0) (E z) +
          2 * E z) ≤ Q z)) :
    (fun z => nearHalvingBlockExtractorBits (N z) (h z) (Q z) (E z) (ell z) (count z)
      (source z) (seeds z)) ∈ FP :=
  Internal.nearHalvingBlockExtractorBits_mem_FP hN hh hQ hE hell hcount hpower
    hsource hseeds levels valid

end Algebraic.Cutwidth.Extractor
