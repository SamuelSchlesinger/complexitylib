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
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Run
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Block.Program
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Parameters
import Complexitylib.Classes.P.StringAccess
import Complexitylib.Tactic.PolyTime

/-!
# Computation of the complete near-halving extractor

Compose the certified bounded payload loop with the total final extractor.
The iteration certificate accounts for every intermediate state; final
field-seed slicing and extraction use registered polynomial-time rules.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem nearHalvingBlockFinishEval_encode (h Q E ell : Nat)
    (state : NearHalvingBlockRunState) :
    nearHalvingBlockFinishEval
      (pair (encodeNearHalvingBlockRun h Q E state) (List.replicate ell true)) =
        nearHalvingBlockFinish E ell state := by
  simp only [nearHalvingBlockFinishEval, encodeNearHalvingBlockRun, nearHalvingBlockFinish,
    pairFst_pair, pairSnd_pair, List.length_replicate]

theorem nearHalvingBlockFinishEval_mem_FP : nearHalvingBlockFinishEval ∈ FP := by
  unfold nearHalvingBlockFinishEval
  polytime

theorem nearHalvingBlockExtractorBits_length (N h Q E ell count : Nat)
    (source seeds : List Bool) :
    (nearHalvingBlockExtractorBits N h Q E ell count source seeds).length =
      2 ^ count * ell := by
  simp only [nearHalvingBlockExtractorBits, nearHalvingBlockFinish,
    oneShotBlockExtractorBits_length, List.length_replicate, nearHalvingBlockRun_count]

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
      (source z) (seeds z)) ∈ FP := by
  have loop := nearHalvingBlockRun_mem_FP hN hh hQ hE hcount hpower hsource hseeds levels valid
  have finished := mem_FP_comp (mem_FP_pair loop hell.mem_FP) nearHalvingBlockFinishEval_mem_FP
  simpa only [Function.comp_def, nearHalvingBlockFinishEval_encode, nearHalvingBlockExtractorBits]
    using finished

end Algebraic.Cutwidth.Extractor.Internal
