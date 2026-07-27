/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Advice.Reverse
public import Complexitylib.Classes.Randomized.PPoly.Defs
public import Complexitylib.Classes.Randomized.PPoly.Internal

/-!
# Bounded-error probabilistic computation has polynomial-size circuits

For each input length, finite amplification supplies one seed that is correct
simultaneously on every input of that length. Fixing that seed in a parallel
bounded-acceptance circuit produces a polynomial-size nonuniform family. The
serialized circuit evaluator then turns that family into a polynomial-advice
decider.

## Main results

- `NTM.uniformCorrectSeed_correct`: correctness of the selected seed.
- `NTM.hardwiredAmplificationFamily_function_iff`: fixed-length semantics.
- `NTM.hardwiredAmplificationFamily_decides`: whole-language correctness.
- `NTM.hardwiredAmplificationFamily_size_bigO`: quantitative size bound.
- `BPP_subset_PPoly`: every language in `BPP` has polynomial-size circuits.
- `BPP_subset_PAdvice`: every language in `BPP` has a polynomial-advice decider.
-/

@[expose] public section

namespace Complexity

namespace NTM

/-- The selected seed returns the correct amplified verdict on every input of
its designated length. -/
theorem uniformCorrectSeed_correct (tm : NTM k) (L : Language)
    (f : ℕ → ℕ) (haccept : tm.AcceptsWithProb L f (2 / 3))
    (hreject : tm.RejectsWithProb L f (1 / 3)) (n : ℕ)
    (x : BitString n) :
    blockMajority (tm.repeatAcceptEvent x.toList (f n))
        (tm.uniformCorrectSeed L f haccept hreject n) = true ↔
      x.toList ∈ L :=
  tm.uniformCorrectSeed_correct_internal L f haccept hreject n x

/-- The hardwired family agrees with `L` on every fixed-length input. -/
theorem hardwiredAmplificationFamily_function_iff
    (tm : NTM k) (L : Language) (f : ℕ → ℕ)
    (haccept : tm.AcceptsWithProb L f (2 / 3))
    (hreject : tm.RejectsWithProb L f (1 / 3)) (n : ℕ)
    (x : BitString n) :
    (tm.hardwiredAmplificationFamily L f haccept hreject).function n x = true ↔
      x.toList ∈ L :=
  tm.hardwiredAmplificationFamily_function_iff_internal
    L f haccept hreject n x

/-- The hardwired amplification family decides the original language. -/
theorem hardwiredAmplificationFamily_decides
    (tm : NTM k) (L : Language) (f : ℕ → ℕ)
    (haccept : tm.AcceptsWithProb L f (2 / 3))
    (hreject : tm.RejectsWithProb L f (1 / 3)) :
    (tm.hardwiredAmplificationFamily L f haccept hreject).Decides L :=
  tm.hardwiredAmplificationFamily_decides_internal L f haccept hreject

/-- If the original fixed-time horizon is `O(n^d)`, the hardwired amplified
family has size `O(n^(3d+4))`. -/
theorem hardwiredAmplificationFamily_size_bigO
    (tm : NTM k) (L : Language) {f : ℕ → ℕ} {d : ℕ}
    (haccept : tm.AcceptsWithProb L f (2 / 3))
    (hreject : tm.RejectsWithProb L f (1 / 3))
    (hf : f =O ((· ^ d) : ℕ → ℕ)) :
    (tm.hardwiredAmplificationFamily L f haccept hreject).size =O
      ((· ^ (3 * d + 4)) : ℕ → ℕ) :=
  tm.hardwiredAmplificationFamily_size_bigO_internal L haccept hreject hf

end NTM

/-- **BPP ⊆ P/poly**: amplify to inverse-exponential error, select one seed
that is correct on all inputs of each length, and hardwire that seed into a
parallel bounded-acceptance circuit. -/
theorem BPP_subset_PPoly : BPP ⊆ PPoly :=
  BPP_subset_PPoly_internal

/-- **BPP ⊆ PAdvice**: the polynomial-size family supplied by nonuniform
derandomization is evaluated using its length-dependent encoding as advice. -/
theorem BPP_subset_PAdvice : BPP ⊆ PAdvice :=
  BPP_subset_PPoly.trans PPoly_subset_PAdvice

end Complexity
