/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Core
public import Complexitylib.Algebraic.Basis.Arithmetic
public import Complexitylib.Algebraic.Basis.Arithmetic.Expression
public import Complexitylib.Algebraic.Basis.Arithmetic.Power
public import Complexitylib.Algebraic.Basis.AC0
public import Complexitylib.Algebraic.Basis.AC0.Normalization
public import Complexitylib.Algebraic.Basis.AC0.Restriction
public import Complexitylib.Algebraic.Basis.DeMorgan.Expression
public import Complexitylib.Algebraic.Basis.DeMorgan.NativeCost
public import Complexitylib.Algebraic.Basis.DeMorgan.PairIndicator
public import Complexitylib.Algebraic.Basis.DeMorgan.Threshold
public import Complexitylib.Algebraic.Basis.DeMorgan.ShannonLupanov
public import Complexitylib.Algebraic.Basis.AndOr.Preimage
public import Complexitylib.Algebraic.Basis.Binary
public import Complexitylib.Algebraic.Basis.Binary.Formula
public import Complexitylib.Algebraic.Translation.Optimal
public import Complexitylib.Algebraic.Translation.Category
public import Complexitylib.Algebraic.Translation.Metric
public import Complexitylib.Algebraic.Translation.Block
public import Complexitylib.Algebraic.Translation.Contextual
public import Complexitylib.Algebraic.Simulation
public import Complexitylib.Algebraic.Complexity
public import Complexitylib.Algebraic.Complexity.Relative
public import Complexitylib.Algebraic.Complexity.RelativeCounting
public import Complexitylib.Algebraic.Complexity.RelativeTransport
public import Complexitylib.Algebraic.Complexity.RelativeSupport
public import Complexitylib.Algebraic.Complexity.RelativeApproximation
public import Complexitylib.Algebraic.ConditionalComplexity
public import Complexitylib.Algebraic.ConditionalComplexity.Boolean
public import Complexitylib.Algebraic.ConditionalComplexity.Counting
public import Complexitylib.Algebraic.ConditionalComplexity.Counterexample
public import Complexitylib.Algebraic.ConditionalComplexity.Restriction
public import Complexitylib.Algebraic.ConditionalComplexity.Linear
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Hessian.Relative
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Hessian.PairingRelative
public import Complexitylib.Algebraic.CircuitFamily
public import Complexitylib.Algebraic.CircuitFamily.Growth
public import Complexitylib.Algebraic.Analysis
public import Complexitylib.Algebraic.Restriction
public import Complexitylib.Algebraic.PartialAssignment
public import Complexitylib.Algebraic.Reduction
public import Complexitylib.Algebraic.Compaction
public import Complexitylib.Algebraic.Counting
public import Complexitylib.Algebraic.MassProduction
public import Complexitylib.Algebraic.MassProduction.RoutingAssembly
public import Complexitylib.Algebraic.LowerBound
public import Complexitylib.Algebraic.Applications

/-!
# Algebraic circuits

The algebraic-circuits library, imported wholesale: finite-arity universal
algebra and shared circuit computation on CSLib's generic circuit model
(`Cslib.Circuits`), with semantics, costs, translations, and lower-bound
frameworks over arbitrary carriers and gate bases. Its declarations keep the
`Algebraic` namespace; see `ROADMAP.md` (item 7) for the plan to consolidate it
with Complexitylib's own circuit developments.
-/
