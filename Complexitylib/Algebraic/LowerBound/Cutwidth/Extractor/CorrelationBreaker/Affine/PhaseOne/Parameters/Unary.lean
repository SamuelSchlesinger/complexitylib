/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters.Unary.Internal

/-!
# Polynomial-time unary choice of all first-phase parameters

Every selected width, error exponent, and source entropy has one total
uniform unary-generation certificate. The growing depth is logarithmic in
the unary tampering parameter, so its powers remain polynomially bounded.
No guard or source-capacity promise is needed for parameter computation.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

variable {n t a target : List Bool → Nat}

/-- Uniformly generate the common advice and logarithm base. -/
@[polytime] theorem affinePhaseOneBase_unaryFn (hn : UnaryFn n) (ht : UnaryFn t)
    (ha : UnaryFn a) (htarget : UnaryFn target) :
    UnaryFn fun z => affinePhaseOneBase (n z) (t z) (a z) (target z) :=
  Internal.affinePhaseOneBase_unaryFn hn ht ha htarget

/-- Uniformly generate the common advice and final-extraction scale. -/
@[polytime] theorem affinePhaseOneScale_unaryFn (hn : UnaryFn n) (ht : UnaryFn t)
    (ha : UnaryFn a) (htarget : UnaryFn target) :
    UnaryFn fun z => affinePhaseOneScale (n z) (t z) (a z) (target z) :=
  Internal.affinePhaseOneScale_unaryFn hn ht ha htarget

/-- Uniformly generate the initial extraction scale. -/
@[polytime] theorem affinePhaseOneInitialScale_unaryFn (hn : UnaryFn n) (ht : UnaryFn t)
    (ha : UnaryFn a) (htarget : UnaryFn target) :
    UnaryFn fun z => affinePhaseOneInitialScale (n z) (t z) (a z) (target z) :=
  Internal.affinePhaseOneInitialScale_unaryFn hn ht ha htarget

/-- Uniformly generate the full original right-source width. -/
@[polytime] theorem affinePhaseOneRightBits_unaryFn (hn : UnaryFn n) (ht : UnaryFn t)
    (ha : UnaryFn a) (htarget : UnaryFn target) :
    UnaryFn fun z => affinePhaseOneRightBits (n z) (t z) (a z) (target z) :=
  Internal.affinePhaseOneRightBits_unaryFn hn ht ha htarget

/-- Uniformly generate the local dyadic error exponent. -/
@[polytime] theorem affinePhaseOneLocalError_unaryFn (htarget : UnaryFn target) :
    UnaryFn fun z => affinePhaseOneLocalError (target z) :=
  Internal.affinePhaseOneLocalError_unaryFn htarget

/-- Uniformly generate the full left-source entropy reserve using bounded growing-depth powers. -/
@[polytime] theorem affinePhaseOneSourceEntropy_unaryFn (hn : UnaryFn n) (ht : UnaryFn t)
    (ha : UnaryFn a) (htarget : UnaryFn target) :
    UnaryFn fun z => affinePhaseOneSourceEntropy (n z) (t z) (a z) (target z) :=
  Internal.affinePhaseOneSourceEntropy_unaryFn hn ht ha htarget

end Algebraic.Cutwidth.Extractor
