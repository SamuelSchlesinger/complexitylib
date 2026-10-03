/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Circuits.BitString
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding.Internal

/-!
# Balanced padding permits any fixed extraction error below one half

If `f` extracts with error strictly below one half, `balancePad f` is exactly
balanced and rectangle-free at twice the original threshold. The list evaluator
preserves uniform polynomial time. In particular, the lower bound does not need
an extractor error of one quarter solely to ensure accepting-input density.
-/

public section

namespace Algebraic.Cutwidth

/-- Error strictly below one half guarantees both output values on every
large flat-source pair. -/
theorem FlatSumsetExtractor.disperser {n K : Nat} {f : Cslib.BooleanFunction n} {ν : ℝ}
    (extract : FlatSumsetExtractor f K ν) (hK : 0 < K) (hν : ν < 1 / 2) :
    FlatSumsetDisperser f K :=
  Extractor.Internal.flatSumsetExtractor_disperser extract hK hν

/-- A two-sided sumset disperser remains one after balanced padding, with a
factor-two loss in support threshold. -/
theorem FlatSumsetDisperser.balancePad {n K : Nat} {f : Cslib.BooleanFunction n}
    (disperse : FlatSumsetDisperser f K) : FlatSumsetDisperser (balancePad f) (2 * K) :=
  Extractor.Internal.flatSumsetDisperser_balancePad disperse

/-- Dispersion excludes one-rectangles, without any accepting-density
assumption. -/
theorem FlatSumsetDisperser.rectangleFree {n K : Nat} {f : Cslib.BooleanFunction n}
    (disperse : FlatSumsetDisperser f K) : RectangleFree f K :=
  Extractor.Internal.flatSumsetDisperser_rectangleFree disperse

/-- Any extraction error strictly below one half yields a rectangle-free
balanced extension. -/
theorem FlatSumsetExtractor.balancePad_rectangleFree
    {n K : Nat} {f : Cslib.BooleanFunction n} {ν : ℝ}
    (extract : FlatSumsetExtractor f K ν) (hK : 0 < K) (hν : ν < 1 / 2) :
    RectangleFree (balancePad f) (2 * K) :=
  Extractor.Internal.flatSumsetExtractor_balancePad_rectangleFree extract hK hν

/-- Exactly one fresh bit accepts for each old input, so balanced padding
accepts exactly half its input cube. -/
theorem card_accepting_balancePad {n : Nat} (f : Cslib.BooleanFunction n) :
    (accepting (balancePad f)).card = 2 ^ n :=
  Extractor.Internal.card_accepting_balancePad f

/-- The list evaluator agrees with the finite Boolean-function padding on
every positive input length. -/
theorem balancePadEval_toList {n : Nat} {f : Cslib.BooleanFunction n}
    {eval : List Bool → List Bool}
    (heval : ∀ x : Complexity.BitString n, eval x.toList = [f x])
    (x : Complexity.BitString (n + 1)) :
    balancePadEval eval x.toList = [balancePad f x] :=
  Extractor.Internal.balancePadEval_toList heval x

/-- Balanced padding preserves a uniform polynomial-time evaluator. -/
theorem balancePadEval_mem_FP {eval : List Bool → List Bool} (heval : eval ∈ Complexity.FP) :
    balancePadEval eval ∈ Complexity.FP :=
  Extractor.Internal.balancePadEval_mem_FP heval

end Algebraic.Cutwidth
