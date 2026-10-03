/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing.Program.Defs

/-!
# A total string program for the first affine phase

The program takes a false-completed prefix of the right word, runs the
depth-sixty-four matched extractor on the original left word, supplies that
result to the actual advice program on the original right word, and uses its
output as the seed of the growing-depth matched extractor on the original
left word. Its depth is `clog 2 (t + 1) + 64`.

All parameters and words are runtime inputs. Each component retains its
total behavior on invalid parameters. This is the computational first phase
of Chattopadhyay--Liao, *Extractors for Sum of Two Sources* (2021), Theorem 6.1,
printed p.23, instantiated with the library's actual component programs:
<https://arxiv.org/abs/2110.12652>. Statistical guarantees are separate.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- The first extraction seed, padded with false bits to its exact width. -/
def affinePhaseOneFirstSeedWord (L₀ : Nat) (y : List Bool) : List Bool :=
  (y ++ List.replicate (matchedBlockSeedBits L₀) false).take (matchedBlockSeedBits L₀)

/-- Execute all three actual component programs, rereading both original source words. -/
def affinePhaseOneRuntime (t L₀ e₀ L₁ e₁ er : Nat) (x y advice : List Bool) : List Bool :=
  let first := matchedBlockExtractorRuntime 64 L₀ e₀ x (affinePhaseOneFirstSeedWord L₀ y)
  let second := adviceCorrelationBreakerRuntime L₁ e₁ y first advice
  growingMatchedBlockExtractorRuntime t L₁ er x second

/-- Decode three data words and six unary numerical words from a single paired input. -/
def affinePhaseOneEval (z : List Bool) : List Bool :=
  let data := pairFst z
  let params := pairSnd z
  let stages := pairSnd params
  let first := pairFst stages
  let later := pairSnd stages
  affinePhaseOneRuntime (pairFst params).length (pairFst first).length
    (pairSnd first).length (pairFst later).length (pairFst (pairSnd later)).length
    (pairSnd (pairSnd later)).length
    (pairFst data) (pairFst (pairSnd data)) (pairSnd (pairSnd data))

end Algebraic.Cutwidth.Extractor
