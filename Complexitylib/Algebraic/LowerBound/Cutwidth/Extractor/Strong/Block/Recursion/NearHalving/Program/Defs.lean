/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Run.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Block.Program.Defs

/-!
# The complete near-halving extractor as a bit program

After the requested number of block steps, apply one shared one-shot
extractor to every leaf. Both final field seeds are sliced at their exact
widths, so bits following the complete seed word are ignored. The separate
iteration count permits a zero-step fallback in total parameter generators.
All string operations are total, including on short or malformed inputs.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Extract every current leaf using the exact final condenser and hash seed words. -/
def nearHalvingBlockFinish (E ell : Nat) (state : NearHalvingBlockRunState) : List Bool :=
  let condenserWidth := 2 * 3 ^ oneShotCondenserExponent state.width ell E
  let hashWidth := 2 * 3 ^ oneShotHashExponent state.width ell E
  oneShotBlockExtractorBits state.width ell E state.payload
    (state.seeds.take condenserWidth) ((state.seeds.drop condenserWidth).take hashWidth)
    (List.replicate state.count true)

/-- Parse an encoded runtime state and unary leaf length, then extract all current blocks. -/
def nearHalvingBlockFinishEval (z : List Bool) : List Bool :=
  let state := pairFst z
  let ell := (pairSnd z).length
  let dynamic := pairFst state
  let fixed := pairSnd state
  let width := (pairFst (pairFst dynamic)).length
  let count := pairSnd (pairSnd dynamic)
  let E := (pairFst (pairSnd fixed)).length
  let payload := pairFst (pairSnd (pairSnd fixed))
  let seeds := pairSnd (pairSnd (pairSnd fixed))
  let condenserWidth := 2 * 3 ^ oneShotCondenserExponent width ell E
  let hashWidth := 2 * 3 ^ oneShotHashExponent width ell E
  oneShotBlockExtractorBits width ell E payload
    (seeds.take condenserWidth) ((seeds.drop condenserWidth).take hashWidth) count

/-- Execute the requested block levels and finish with the shared leaf extractor. -/
def nearHalvingBlockExtractorBits (N h Q E ell count : Nat)
    (source seeds : List Bool) : List Bool :=
  nearHalvingBlockFinish E ell (nearHalvingBlockRun N h Q E count source seeds)

end Algebraic.Cutwidth.Extractor
