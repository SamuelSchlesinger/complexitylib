/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters.Internal

/-!
# Finite advice-chain parameters with checked guards and reserves

For advice length `a`, target error exponent `target`, requested output `out`,
and left-source width `n`, the total chooser sets

* `e = target + 2*a + clog₂(a+1) + 10`,
* `L = 1024*(a+target+out+clog₂(n+1)+256)`, and
* `m = 2^150*(a+1)*L`.

All fixed-depth program guards hold, the final extraction has room for `out`
bits, and `m` covers the three entropy reserves. Using this reserve in an
`n`-bit source still requires `m ≤ n`, made explicit in the capacity corollary.
These are conservative finite arithmetic deductions for the CGL Algorithm 2 /
Lemma 6.9 route, <https://arxiv.org/pdf/1505.00107>, rather than constants from
that paper. Distributional security and uniform runtime are separate layers.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The local error exponent fits in the chosen common scale. -/
theorem adviceParameters_error_le (n a target out : Nat) :
    adviceErrorExponent a target ≤ adviceScale n a target out :=
  Internal.adviceParameters_error_le n a target out

/-- All four runtime size guards hold for the chosen right-source length and scale. -/
theorem adviceParameters_sizeGuard (n a target out : Nat) :
    FlipFlopSizeGuard n (adviceSourceEntropy n a target out)
      (adviceScale n a target out) (adviceErrorExponent a target) :=
  Internal.adviceParameters_sizeGuard n a target out

/-- The full refreshed state fits inside the chosen right-source length. -/
theorem adviceParameters_stateWidth_le (n a target out : Nat) :
    matchedBlockOutputBits 64 (adviceScale n a target out) ≤
      adviceSourceEntropy n a target out :=
  Internal.adviceParameters_stateWidth_le n a target out

/-- The final depth-twenty-four extraction has room for the requested output. -/
theorem adviceParameters_output_le (n a target out : Nat) :
    out ≤ matchedBlockSeedBits (adviceScale n a target out) :=
  Internal.adviceParameters_output_le n a target out

/-- The refreshed-state entropy covers a seed-pair observation and local error. -/
theorem adviceParameters_state_reserve (n a target out : Nat) :
    2 ^ 62 * adviceScale n a target out +
        2 * matchedBlockSeedBits (adviceScale n a target out) +
        adviceErrorExponent a target ≤
      matchedBlockOutputBits 64 (adviceScale n a target out) :=
  Internal.adviceParameters_state_reserve n a target out

/-- The chosen source reserve covers every left observation in `a` advice steps. -/
theorem adviceParameters_left_reserve (n a target out : Nat) :
    2 ^ 62 * adviceScale n a target out +
        (8 * a + 7) * matchedBlockSeedBits (adviceScale n a target out) +
        adviceErrorExponent a target ≤ adviceSourceEntropy n a target out :=
  Internal.adviceParameters_left_reserve n a target out

/-- The chosen source reserve covers every right observation in `a` advice steps. -/
theorem adviceParameters_right_reserve (n a target out : Nat) :
    2 ^ 142 * adviceScale n a target out +
        (5 * a + 5) * matchedBlockOutputBits 64 (adviceScale n a target out) +
        adviceErrorExponent a target ≤ adviceSourceEntropy n a target out :=
  Internal.adviceParameters_right_reserve n a target out

/-- Left-input capacity is an explicit hypothesis, not a property of the total chooser. -/
theorem adviceParameters_left_reserve_of_capacity (n a target out : Nat)
    (capacity : adviceSourceEntropy n a target out ≤ n) :
    2 ^ 62 * adviceScale n a target out +
        (8 * a + 7) * matchedBlockSeedBits (adviceScale n a target out) +
        adviceErrorExponent a target ≤ n :=
  (adviceParameters_left_reserve n a target out).trans capacity

end Algebraic.Cutwidth.Extractor
