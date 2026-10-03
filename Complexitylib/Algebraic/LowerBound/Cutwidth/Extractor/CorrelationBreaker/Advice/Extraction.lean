/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Internal

/-!
# Strong extraction by the complete concrete advice chain

Unequal advice of equal length makes the actual honest output close to
uniform, jointly with the actual tampered output and the entire original
right state. Inputs are independent conditional on the shared tag. The
honest right input is uniform on each row; the left input has the stated
average point-mass envelope. Tampered inputs are arbitrary functions of
those same original left and right states.

The proof constructs every intermediate invariant from the input law. The
finite dyadic corollary pays the conservative per-bit error amplification
with an explicit entropy reserve and local error schedule. Chattopadhyay,
Goyal, and Li supply the advice-chain strategy in Algorithm 2, Section 6.3
of <https://arxiv.org/abs/1505.00107>; the additional final extraction from
the original left source retains the full original right state.
-/

public section

namespace Algebraic.Cutwidth.Extractor

universe u

/-- The actual complete advice program obeys its finite error budget. -/
theorem adviceCorrelationBreaker_dist_le (n m L e : Nat) {Z A B : Type u}
    [Fintype Z] [Fintype A] [Fintype B]
    (guard : FlipFlopSizeGuard n m L e) (size : matchedBlockOutputBits 64 L ≤ m)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (advice advice' : List Bool) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (uniform : ∀ z, mapWeight (y z) (r z) = uniformWeight (Fin m → Bool))
    (length : advice.length = advice'.length) (different : advice ≠ advice') :
    let actual := adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice'
    weightDist actual (uniformSecondWeight actual) ≤
      adviceCorrelationBreakerError m L e advice.length (∑ z, μ z) :=
  Internal.adviceCorrelationBreaker_dist_le n m L e guard size
    w l r x x' y y' advice advice' μ hw hl hr nonnegative cap uniform length different

/-- An explicit entropy reserve and error schedule give the requested dyadic error. -/
theorem adviceCorrelationBreaker_dyadic_dist_le (n m L target : Nat) {Z A B : Type u}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (advice advice' : List Bool) (μ : Z → ℝ)
    (guard : FlipFlopSizeGuard n m L (adviceErrorExponent advice.length target))
    (size : matchedBlockOutputBits 64 L ≤ m)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (uniform : ∀ z, mapWeight (y z) (r z) = uniformWeight (Fin m → Bool))
    (length : advice.length = advice'.length) (different : advice ≠ advice')
    (left : (∑ z, μ z) ≤ ((2 : ℝ) ^ (2 ^ 150 * (advice.length + 1) * L))⁻¹)
    (right : 2 ^ 150 * (advice.length + 1) * L ≤ m) :
    let e := adviceErrorExponent advice.length target
    let actual := adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice'
    weightDist actual (uniformSecondWeight actual) ≤ ((2 : ℝ) ^ target)⁻¹ :=
  Internal.adviceCorrelationBreaker_dyadic_dist_le n m L target w l r x x' y y' advice advice' μ guard size
    hw hl hr nonnegative cap uniform length different left right

end Algebraic.Cutwidth.Extractor
