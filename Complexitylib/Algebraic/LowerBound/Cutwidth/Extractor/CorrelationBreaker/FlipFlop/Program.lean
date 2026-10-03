/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Internal

/-!
# Correct, uniform polynomial-time evaluation of the advice-bit step

The actual three-call look-ahead and eight-call step agree exactly with
their Boolean-vector definitions at the stated common scale. Their total
string evaluators have registered `polytime` certificates with variable
source words, shared scale, error exponent, and advice bit. These results
certify the concrete computation and its cost; the opposite-bit statistical
guarantee and full advice iteration are separate obligations.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- The seed prefix is exactly the corresponding initial segment of the state word. -/
theorem flipFlopSeedPrefix_ofFn (L : Nat) (q : Fin (matchedBlockOutputBits 64 L) → Bool) :
    List.ofFn (flipFlopSeedPrefix L q) = (List.ofFn q).take (matchedBlockSeedBits L) :=
  Internal.flipFlopSeedPrefix_ofFn L q

/-- The string look-ahead encodes precisely both outputs of the concrete vector program. -/
theorem flipFlopLookAheadRuntime_eq (n L e : Nat)
    (left : MatchedBlockRuntimeValid n 24 L e)
    (state : MatchedBlockRuntimeValid (matchedBlockOutputBits 64 L) 24 L e)
    (x : Fin n → Bool) (q : Fin (matchedBlockOutputBits 64 L) → Bool) :
    flipFlopLookAheadRuntime L e (List.ofFn x) (List.ofFn q) =
      pair (List.ofFn (flipFlopLookAhead n L e x q).1)
        (List.ofFn (flipFlopLookAhead n L e x q).2) :=
  Internal.flipFlopLookAheadRuntime_eq n L e left state x q

/-- At a common valid scale, every input and either advice bit follow the vector program. -/
theorem flipFlopStepRuntime_eq (n m L e : Nat) (guard : FlipFlopSizeGuard n m L e)
    (x : Fin n → Bool) (y : Fin m → Bool)
    (q : Fin (matchedBlockOutputBits 64 L) → Bool) (b : Bool) :
    flipFlopStepRuntime L e (List.ofFn x) (List.ofFn y) (List.ofFn q) b =
      List.ofFn (flipFlopStep n m L e x y q b) :=
  Internal.flipFlopStepRuntime_eq n m L e guard x y q b

/-- Every runtime result fits in the common state width, including invalid inputs. -/
theorem flipFlopStepRuntime_length_le (L e : Nat) (x y q : List Bool) (b : Bool) :
    (flipFlopStepRuntime L e x y q b).length ≤ matchedBlockOutputBits 64 L :=
  Internal.flipFlopStepRuntime_length_le L e x y q b

/-- Three actual extractor calls compose uniformly in the source, state, scale, and error. -/
@[polytime] theorem flipFlopLookAheadRuntime_mem_FP {L e : List Bool → Nat}
    {x q : List Bool → List Bool} (hL : UnaryFn L) (he : UnaryFn e)
    (hx : x ∈ FP) (hq : q ∈ FP) :
    (fun z => flipFlopLookAheadRuntime (L z) (e z) (x z) (q z)) ∈ FP :=
  Internal.flipFlopLookAheadRuntime_mem_FP hL he hx hq

/-- The entire advice-bit step is polynomial-time, including the bit-dependent choices. -/
@[polytime] theorem flipFlopStepRuntime_mem_FP {L e : List Bool → Nat}
    {x y q : List Bool → List Bool} {b : List Bool → Bool}
    (hL : UnaryFn L) (he : UnaryFn e) (hx : x ∈ FP) (hy : y ∈ FP) (hq : q ∈ FP)
    (hb : FPPred fun z => b z = true) :
    (fun z => flipFlopStepRuntime (L z) (e z) (x z) (y z) (q z) (b z)) ∈ FP :=
  Internal.flipFlopStepRuntime_mem_FP hL he hx hy hq hb

/-- Canonical paired input decodes the source words, unary scale and error, and advice bit. -/
theorem flipFlopStepEval_pair (x y q scale error bit : List Bool) :
    flipFlopStepEval (pair (pair x (pair y q)) (pair scale (pair error bit))) =
      flipFlopStepRuntime scale.length error.length x y q (bit[0]?.getD false) :=
  Internal.flipFlopStepEval_pair x y q scale error bit

/-- A single total polynomial-time evaluator covers all input lengths and shared parameters. -/
@[polytime] theorem flipFlopStepEval_mem_FP : flipFlopStepEval ∈ FP :=
  Internal.flipFlopStepEval_mem_FP

end Algebraic.Cutwidth.Extractor
