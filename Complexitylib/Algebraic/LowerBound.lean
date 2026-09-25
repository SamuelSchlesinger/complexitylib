/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.NormalForm
public import Complexitylib.Algebraic.LowerBound.AC0.LiteralGate
public import Complexitylib.Algebraic.LowerBound.AC0.BottomGate
public import Complexitylib.Algebraic.LowerBound.AC0.DecisionTree
public import Complexitylib.Algebraic.LowerBound.AC0.DecisionTreeTrace
public import Complexitylib.Algebraic.LowerBound.AC0.Duality
public import Complexitylib.Algebraic.LowerBound.AC0.TreeNormalForm
public import Complexitylib.Algebraic.LowerBound.AC0.Layer
public import Complexitylib.Algebraic.LowerBound.AC0.LayerFormula
public import Complexitylib.Algebraic.LowerBound.AC0.CanonicalDecisionTree
public import Complexitylib.Algebraic.LowerBound.AC0.RandomRestriction
public import Complexitylib.Algebraic.LowerBound.AC0.RestrictionAveraging
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.Encoding
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.CombinedAdvice
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.CanonicalEncoding
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.CombinedCanonicalEncoding
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.CombinedCanonicalTrace
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.CombinedCanonicalPacking
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.Canonical
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.CombinedCanonical
public import Complexitylib.Algebraic.LowerBound.AC0.Switching
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.Family
public import Complexitylib.Algebraic.LowerBound.AC0.BottomFamily
public import Complexitylib.Algebraic.LowerBound.AC0.LayerSwitching
public import Complexitylib.Algebraic.LowerBound.AC0.LayerSwitchingBounds
public import Complexitylib.Algebraic.LowerBound.AC0.LayerExistence
public import Complexitylib.Algebraic.LowerBound.AC0.LayerExistenceBounds
public import Complexitylib.Algebraic.LowerBound.AC0.LayerIteration
public import Complexitylib.Algebraic.LowerBound.AC0.LayerIterationBounds
public import Complexitylib.Algebraic.LowerBound.AC0.LayerSchedule
public import Complexitylib.Algebraic.LowerBound.AC0.Parity
public import Complexitylib.Algebraic.LowerBound.AC0.ParityParameters
public import Complexitylib.Algebraic.LowerBound.AC0.ParitySurvivors
public import Complexitylib.Algebraic.LowerBound.AC0.ParityNormalForm
public import Complexitylib.Algebraic.LowerBound.AC0.ParityCircuit
public import Complexitylib.Algebraic.LowerBound.AC0.ParityTopGate
public import Complexitylib.Algebraic.LowerBound.AC0.ParityDepthReduction
public import Complexitylib.Algebraic.LowerBound.AC0.ParityLowerBound
public import Complexitylib.Algebraic.LowerBound.AC0.ParitySizeArithmetic
public import Complexitylib.Algebraic.LowerBound.AC0.ParityScale
public import Complexitylib.Algebraic.LowerBound.AC0.ParityRoot
public import Complexitylib.Algebraic.LowerBound.AC0.ParitySeparation
public import Complexitylib.Algebraic.LowerBound.FanIn
public import Complexitylib.Algebraic.LowerBound.Counting
public import Complexitylib.Algebraic.LowerBound.Hierarchy
public import Complexitylib.Algebraic.LowerBound.GateElimination
public import Complexitylib.Algebraic.LowerBound.Approximation
public import Complexitylib.Algebraic.LowerBound.Fusion
public import Complexitylib.Algebraic.LowerBound.Monotone.Clique.Exponential
public import Complexitylib.Algebraic.LowerBound.Cutwidth
public import Complexitylib.Algebraic.LowerBound.Nechiporuk
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson

/-!
# Circuit lower bounds

This umbrella module collects the library's circuit lower-bound methods.
-/

@[expose] public section
