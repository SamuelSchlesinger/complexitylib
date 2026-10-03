/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Run.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Run.Internal

/-!
# Uniform bounded evaluation of the near-halving payload loop

The actual encoded loop follows the specified rounded widths and consumes
exactly one shared field seed per level. Every positive iteration count
produces a payload of the exact scheduled block length, even from an arbitrary
source word. The state-size bound also includes that initial word, all unary
workspace, block counts, and unused seeds.

One FP program evaluates any partial run whose requested count is at most
the depth and is either zero or has the proved entropy and reserve budgets.
The initialization power has its own explicit unary-computation premise;
the step updates it by division. Canonical seed semantics and the final
one-shot stage are separate layers. This loop uses the finite arithmetic
schedule credited in `NearHalving.Parameters`.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The encoded runtime step computes the complete structured workspace update. -/
theorem nearHalvingBlockRunStepEval_encode (h Q E : Nat) (state : NearHalvingBlockRunState) :
    nearHalvingBlockRunStepEval (encodeNearHalvingBlockRun h Q E state) =
      encodeNearHalvingBlockRun h Q E (nearHalvingBlockRunStep h Q E state) :=
  Internal.nearHalvingBlockRunStepEval_encode h Q E state

/-- Any finite encoded run agrees with structured payload and seed iteration. -/
theorem nearHalvingBlockRunStepEval_iterate (h Q E : Nat) (state : NearHalvingBlockRunState)
    (i : Nat) :
    nearHalvingBlockRunStepEval^[i] (encodeNearHalvingBlockRun h Q E state) =
      encodeNearHalvingBlockRun h Q E ((nearHalvingBlockRunStep h Q E)^[i] state) :=
  Internal.nearHalvingBlockRunStepEval_iterate h Q E state i

/-- Exact encoded storage includes every numeric field, payload, and seed suffix. -/
theorem encodeNearHalvingBlockRun_length (h Q E : Nat) (state : NearHalvingBlockRunState) :
    (encodeNearHalvingBlockRun h Q E state).length =
      8 * state.width + 4 * state.remaining + 4 * state.remainingPower + 2 * state.count +
        4 * h + 2 * Q + 2 * E + 2 * state.payload.length + state.seeds.length + 28 :=
  Internal.encodeNearHalvingBlockRun_length h Q E state

/-- Up to the supplied depth, numeric workspace follows the actual rounded schedule. -/
theorem nearHalvingBlockRun_numeric (N h Q E : Nat) (source seeds : List Bool)
    {i : Nat} (level : i ≤ h) :
    (nearHalvingBlockRun N h Q E i source seeds).width = nearHalvingBlockWidth N h Q E i ∧
      (nearHalvingBlockRun N h Q E i source seeds).remaining = h - i ∧
      (nearHalvingBlockRun N h Q E i source seeds).remainingPower = 2 ^ (h - i) :=
  Internal.nearHalvingBlockRun_numeric N h Q E source seeds level

/-- The next partial run applies one actual payload and seed-consumption step. -/
theorem nearHalvingBlockRun_succ (N h Q E i : Nat) (source seeds : List Bool) :
    nearHalvingBlockRun N h Q E (i + 1) source seeds =
      nearHalvingBlockRunStep h Q E (nearHalvingBlockRun N h Q E i source seeds) :=
  Internal.nearHalvingBlockRun_succ N h Q E i source seeds

/-- Every executed step doubles the number of blocks. -/
theorem nearHalvingBlockRun_count (N h Q E i : Nat) (source seeds : List Bool) :
    (nearHalvingBlockRun N h Q E i source seeds).count = 2 ^ i :=
  Internal.nearHalvingBlockRun_count N h Q E i source seeds

/-- The unused suffix drops exactly the sum of the executed field seed widths. -/
theorem nearHalvingBlockRun_seeds (N h Q E : Nat) (source seeds : List Bool)
    {i : Nat} (level : i ≤ h) :
    (nearHalvingBlockRun N h Q E i source seeds).seeds =
      seeds.drop ((Finset.range i).sum (nearHalvingBlockSeedWidth N h Q E)) :=
  Internal.nearHalvingBlockRun_seeds N h Q E source seeds level

/-- The unused seed suffix never exceeds the original seed-word length. -/
theorem nearHalvingBlockRun_seeds_length (N h Q E i : Nat) (source seeds : List Bool) :
    (nearHalvingBlockRun N h Q E i source seeds).seeds.length ≤ seeds.length :=
  Internal.nearHalvingBlockRun_seeds_length N h Q E i source seeds

/-- Every positive partial run has exact scheduled payload length, for any initial word. -/
theorem nearHalvingBlockRun_payload_length (N h Q E : Nat) (source seeds : List Bool)
    {i : Nat} (level : i ≤ h) (positive : 0 < i) :
    (nearHalvingBlockRun N h Q E i source seeds).payload.length =
      2 ^ i * nearHalvingBlockWidth N h Q E i :=
  Internal.nearHalvingBlockRun_payload_length N h Q E source seeds level positive

/-- All complete state encodings are bounded; zero steps need no splitting hypotheses. -/
theorem nearHalvingBlockRun_iterate_bound (N h Q E : Nat) (source seeds : List Bool)
    {i : Nat} (level : i ≤ h)
    (valid : i = 0 ∨ (nearHalvingBlockEntropy h Q 0 ≤ N ∧
      2 * (6 * (nearHalvingBlockRate h + 1) *
        explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 2 * E) ≤ Q)) :
    (encodeNearHalvingBlockRun h Q E (nearHalvingBlockRun N h Q E i source seeds)).length ≤
      14 * N + 8 * h + 4 * 2 ^ h + 2 * Q + 2 * E +
        2 * source.length + seeds.length + 30 :=
  Internal.nearHalvingBlockRun_iterate_bound N h Q E source seeds level valid

open Complexity in
/-- The total encoded step is polynomial-time on arbitrary, including malformed, input strings. -/
@[polytime] theorem nearHalvingBlockRunStepEval_mem_FP : nearHalvingBlockRunStepEval ∈ FP :=
  Internal.nearHalvingBlockRunStepEval_mem_FP

open Complexity in
/-- One uniform program evaluates the complete payload loop under the explicit state bound.
The initialization power is certified separately, and zero steps require no reserve budget. -/
theorem nearHalvingBlockRun_mem_FP {N h Q E count : List Bool → Nat}
    {source seeds : List Bool → List Bool}
    (hN : UnaryFn N) (hh : UnaryFn h) (hQ : UnaryFn Q) (hE : UnaryFn E)
    (hcount : UnaryFn count) (hpower : UnaryFn fun z => 2 ^ h z)
    (hsource : source ∈ FP) (hseeds : seeds ∈ FP)
    (levels : ∀ z, count z ≤ h z)
    (valid : ∀ z, count z = 0 ∨ (nearHalvingBlockEntropy (h z) (Q z) 0 ≤ N z ∧
      2 * (6 * (nearHalvingBlockRate (h z) + 1) *
        explicitCondenserBudget (N z) (nearHalvingBlockEntropy (h z) (Q z) 0) (E z) +
          2 * E z) ≤ Q z)) :
    (fun z => encodeNearHalvingBlockRun (h z) (Q z) (E z)
      (nearHalvingBlockRun (N z) (h z) (Q z) (E z) (count z) (source z) (seeds z))) ∈ FP :=
  Internal.nearHalvingBlockRun_mem_FP hN hh hQ hE hcount hpower hsource hseeds levels valid

end Algebraic.Cutwidth.Extractor
