/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Program.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Program.Internal

/-!
# One uniform program for the selected finite advice construction

The evaluator computes the chosen scale, local error exponent, and right
width from the original source/advice lengths and unary target/output
parameters. It normalizes the right word to that width and executes the
actual advice chain and final output prefix. Canonical inputs agree exactly
with `adviceTruncatedCorrelationBreaker` at the same selected parameters as
the checked statistical theorem. This equality needs no entropy premise.

All chooser values have uniform unary certificates. Complete loop bounds
include both source words, the generated parameters, remaining advice, and
current state. The polynomial-time certificate holds on every encoded
input, including malformed pairs and infeasible statistical parameters.
Only fixed powers of two appear in parameter generation. No search or
unbounded-iteration closure is used.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Generate the local error exponent uniformly from unary advice length and target. -/
@[polytime] theorem adviceErrorExponent_unaryFn {a target : List Bool → Nat}
    (ha : UnaryFn a) (htarget : UnaryFn target) :
    UnaryFn fun z => adviceErrorExponent (a z) (target z) :=
  Internal.adviceErrorExponent_unaryFn ha htarget

/-- Generate the common scale uniformly from all four unary chooser inputs. -/
@[polytime] theorem adviceScale_unaryFn {n a target out : List Bool → Nat}
    (hn : UnaryFn n) (ha : UnaryFn a) (htarget : UnaryFn target) (hout : UnaryFn out) :
    UnaryFn fun z => adviceScale (n z) (a z) (target z) (out z) :=
  Internal.adviceScale_unaryFn hn ha htarget hout

/-- The source reserve and normalized right width are uniformly unary-computable. -/
@[polytime] theorem adviceSourceEntropy_unaryFn {n a target out : List Bool → Nat}
    (hn : UnaryFn n) (ha : UnaryFn a) (htarget : UnaryFn target) (hout : UnaryFn out) :
    UnaryFn fun z => adviceSourceEntropy (n z) (a z) (target z) (out z) :=
  Internal.adviceSourceEntropy_unaryFn hn ha htarget hout

/-- The normalized right input always has exactly its selected width. -/
theorem adviceSelectedRightWord_length (m : Nat) (y : List Bool) :
    (adviceSelectedRightWord m y).length = m :=
  Internal.adviceSelectedRightWord_length m y

/-- Normalization leaves every canonical right input unchanged. -/
theorem adviceSelectedRightWord_eq (m : Nat) (y : List Bool) (length : y.length = m) :
    adviceSelectedRightWord m y = y :=
  Internal.adviceSelectedRightWord_eq m y length

/-- Prefix normalization with false completion has a uniform polynomial-time certificate. -/
@[polytime] theorem adviceSelectedRightWord_mem_FP
    {m : List Bool → Nat} {y : List Bool → List Bool} (hm : UnaryFn m) (hy : y ∈ FP) :
    (fun z => adviceSelectedRightWord (m z) (y z)) ∈ FP :=
  Internal.adviceSelectedRightWord_mem_FP hm hy

/-- A request for zero output bits returns immediately for every input. -/
theorem adviceSelectedCorrelationBreakerRuntime_zero (target : Nat) (x y advice : List Bool) :
    adviceSelectedCorrelationBreakerRuntime target 0 x y advice = [] :=
  Internal.adviceSelectedCorrelationBreakerRuntime_zero target x y advice

/-- The total runtime produces exactly the requested output width on arbitrary words. -/
theorem adviceSelectedCorrelationBreakerRuntime_length (target out : Nat)
    (x y advice : List Bool) :
    (adviceSelectedCorrelationBreakerRuntime target out x y advice).length = out :=
  Internal.adviceSelectedCorrelationBreakerRuntime_length target out x y advice

/-- Canonical source words compute exactly the actual selected truncated program. -/
theorem adviceSelectedCorrelationBreakerRuntime_eq (n target out : Nat)
    (advice : List Bool) (x : Fin n → Bool)
    (y : Fin (adviceSourceEntropy n advice.length target out) → Bool) :
    adviceSelectedCorrelationBreakerRuntime target out (List.ofFn x) (List.ofFn y) advice =
      List.ofFn (adviceTruncatedCorrelationBreaker n
        (adviceSourceEntropy n advice.length target out)
        (adviceScale n advice.length target out) (adviceErrorExponent advice.length target)
        out x y advice) :=
  Internal.adviceSelectedCorrelationBreakerRuntime_eq n target out advice x y

/-- Every complete loop encoding is bounded, including the generated right-source padding. -/
theorem adviceSelectedCorrelationBreakerRun_length_le (target out : Nat)
    (x y advice : List Bool) (i : Nat) :
    let n := x.length
    let a := advice.length
    let L := adviceScale n a target out
    let e := adviceErrorExponent a target
    let m := adviceSourceEntropy n a target out
    (encodeAdviceRunState (adviceRun L e x (adviceSelectedRightWord m y) advice i)).length ≤
      4 * n + 2 * m + 2 * L + 2 * e + 2 * a + matchedBlockOutputBits 64 L + 12 :=
  Internal.adviceSelectedCorrelationBreakerRun_length_le target out x y advice i

/-- The whole selected program is uniform in its numerical inputs and all original words. -/
@[polytime] theorem adviceSelectedCorrelationBreakerRuntime_mem_FP
    {target out : List Bool → Nat} {x y advice : List Bool → List Bool}
    (htarget : UnaryFn target) (hout : UnaryFn out)
    (hx : x ∈ FP) (hy : y ∈ FP) (hadvice : advice ∈ FP) :
    (fun z => adviceSelectedCorrelationBreakerRuntime
      (target z) (out z) (x z) (y z) (advice z)) ∈ FP :=
  Internal.adviceSelectedCorrelationBreakerRuntime_mem_FP htarget hout hx hy hadvice

/-- The codec retains both sources and advice, followed by unary target/output words. -/
theorem adviceSelectedCorrelationBreakerEval_pair (x y advice targetWord outWord : List Bool) :
    adviceSelectedCorrelationBreakerEval
      (pair (pair x y) (pair advice (pair targetWord outWord))) =
        adviceSelectedCorrelationBreakerRuntime targetWord.length outWord.length x y advice :=
  Internal.adviceSelectedCorrelationBreakerEval_pair x y advice targetWord outWord

/-- The single paired evaluator exactly serializes the selected statistical construction. -/
theorem adviceSelectedCorrelationBreakerEval_eq (n target out : Nat)
    (advice : List Bool) (x : Fin n → Bool)
    (y : Fin (adviceSourceEntropy n advice.length target out) → Bool) :
    adviceSelectedCorrelationBreakerEval (pair (pair (List.ofFn x) (List.ofFn y))
      (pair advice (pair (List.replicate target true) (List.replicate out true)))) =
      List.ofFn (adviceTruncatedCorrelationBreaker n
        (adviceSourceEntropy n advice.length target out)
        (adviceScale n advice.length target out) (adviceErrorExponent advice.length target)
        out x y advice) :=
  Internal.adviceSelectedCorrelationBreakerEval_eq n target out advice x y

/-- Every evaluator output has the length of the decoded output request. -/
theorem adviceSelectedCorrelationBreakerEval_length (z : List Bool) :
    (adviceSelectedCorrelationBreakerEval z).length =
      (pairSnd (pairSnd (pairSnd z))).length :=
  Internal.adviceSelectedCorrelationBreakerEval_length z

/-- Even malformed encoded inputs produce an output no longer than their input. -/
theorem adviceSelectedCorrelationBreakerEval_length_le (z : List Bool) :
    (adviceSelectedCorrelationBreakerEval z).length ≤ z.length :=
  Internal.adviceSelectedCorrelationBreakerEval_length_le z

/-- One total string function evaluates all selected parameters in polynomial time. -/
@[polytime] theorem adviceSelectedCorrelationBreakerEval_mem_FP :
    adviceSelectedCorrelationBreakerEval ∈ FP :=
  Internal.adviceSelectedCorrelationBreakerEval_mem_FP

end Algebraic.Cutwidth.Extractor
