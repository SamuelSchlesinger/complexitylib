/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
public import Mathlib.Data.Fintype.Pi
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Weighted.Internal

/-!
# The scheduled condenser on arbitrary capped sources

The actual decoded runtime map strongly condenses every normalized weighted
source with point masses at most `2^(-k)`. Its ideal output is normalized and
has the same point-mass cap separately at every retained seed, with joint
total variation error at most `2^(-e)`.

This extends the checked flat-source guarantee by exact finite mixtures.
Inputs may use any injective encoding into words of the stated length; the
fixed-length Boolean-vector specialization uses `List.ofFn`. The ideal real
weights are statistical witnesses, not additional runtime inputs.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The scheduled runtime condenser preserves the point-mass cap of every
weighted source represented injectively by words of length `n`. -/
theorem decodedExplicitCondenser_weighted (n k e u : Nat) {α : Type*} [Fintype α]
    [Fintype (AdjoinRoot
      (binaryModulus (sparseFieldExponent u (explicitCondenserBudget n k e))))]
    (rate : 0 < u) (input : α ↪ List Bool) (source : ∀ x, (input x).length = n) :
    WeightedStrongSeededCondenser
      (fun x => decodedExplicitCondenser n k e u (input x)) (2 ^ k) (2 ^ k)
      ((2 : ℝ) ^ e)⁻¹ :=
  Internal.decodedExplicitCondenser_weighted n k e u rate input source

/-- The scheduled runtime condenser is strong on every capped distribution
of fixed-length Boolean vectors, including zero-length inputs. -/
theorem decodedExplicitCondenser_weighted_ofFn (n k e u : Nat)
    [Fintype (AdjoinRoot
      (binaryModulus (sparseFieldExponent u (explicitCondenserBudget n k e))))]
    (rate : 0 < u) :
    WeightedStrongSeededCondenser
      (fun x : Fin n → Bool => decodedExplicitCondenser n k e u (List.ofFn x))
      (2 ^ k) (2 ^ k) ((2 : ℝ) ^ e)⁻¹ :=
  Internal.decodedExplicitCondenser_weighted_ofFn n k e u rate

end Algebraic.Cutwidth.Extractor
