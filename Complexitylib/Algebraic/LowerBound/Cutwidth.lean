/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Rectangle
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Multigraph
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Network
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Wiring
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Wiring.Signals
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Boundary
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Operations
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Components
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Tree
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.TreeComponent
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Padding
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Glue
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Endpoint
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.CutBoundary
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.LocalConfigurations
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.EdgeSwitch
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.BoundaryNormalization
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.NeighborNormalization
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.BoundaryLift
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.ConnectedPartition
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Clusters
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.CycleRemoval
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.BridgeQuotient
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSuppression
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSuppression.Regions
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.WeightedTree
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Suppression
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Amplification
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Rebalancing
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Reduction
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Helpful
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MedianOrdering
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Compression
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Expansion
public import Complexitylib.Algebraic.LowerBound.Cutwidth.FourN
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Forget
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Nondeterministic
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Direction
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Balanced
public import Complexitylib.Algebraic.LowerBound.Cutwidth.AverageCase
public import Complexitylib.Algebraic.LowerBound.Cutwidth.SingleCut
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Ordering
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Rank
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.TotallyRegular
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Polynomial
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Polynomial.Arithmetic
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Polynomial.Cauchy
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Quadratic
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Restrict
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.FieldMul
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Tripartite
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding.Asymptotics
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Majority
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Majority.Probability
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Moments
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Moments.Tails
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.FourthMoment
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Conditioning
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.BadSeeds
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Selection
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Amplification
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Polynomial
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Monomials
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Interpolation
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Substitution
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Expansion.Primitive
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Expansion.Quotient
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Expansion
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Polynomial
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binomial
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binomial.Extension
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Encoding
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Codec
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Extension
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Sparse
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Unary
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Linear
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Lossless
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Lossless
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Weighted
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Block
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Block.Program
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Block.Program.Correctness
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Splitting
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Unary
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Serialization
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Composition
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.FlatMixture
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Equiv
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Projection
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.SeedPadding
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Transport
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformState
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.FixedTampering
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.FixedTampering.Second
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformRefresh
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Expectation
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Leakage
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Perturbation
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Independence
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Conditional
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Factored
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Identity
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Transport
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.SeedStep
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated.Family
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Conditioning
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Condenser.Repair
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Condenser
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Condenser.Extraction
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Level
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Level.Extraction
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Initial
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Extraction
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Linearity
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters.Explicit
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Seeds
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Linearity
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Asymptotics
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Codec
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.State
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.State.Parameters
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Run
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Run.Correctness
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program.Correctness
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program.Family
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Boolean
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Affine
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.BoundedDepth
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing.Program
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Affine
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Program
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.LookAhead
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.UniformState
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.False
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.True
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.UniformState
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Output
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Preservation.Half
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Preservation.Weak
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Preservation.Step
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Program
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Parameters
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Program
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Perturbed
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Alternating
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Truncation
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Initial
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Transcript
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Second
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Final
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Extraction
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Extraction.Bounds
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Extraction.Parameters
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters.Unary
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Program
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Program.Parameters
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Explicit
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Asymptotics
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Unary
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Codec
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Boolean
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Run
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Run.Correctness
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Program
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Program.Correctness
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Program
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Program.Family
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Padded
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Field
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Binary
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Parameters
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Correctness
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Extraction
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Weighted
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Block
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Block.Program
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Kernel
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.SecondMoment
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Star
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Order
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Band.Order
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Band.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Band
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Arccos
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Exact
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Decay
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Superconcentrator

/-!
# The cutwidth lower bound

This umbrella collects the `(4 - ε) n` lower bound for rectangle-free
functions over the full binary basis. `FourN` combines cut counting, circuit
wiring, compression, and the proved sharp cubic bisection and pathwidth
bounds. `Nondeterministic` extends the conclusion to arbitrarily many witness
inputs; `AverageCase` gives the agreement bound for balanced functions.
`SingleCut` proves the single-cut criterion: one split of a circuit's wires,
crossed by `|A|` forward and `|B|` backward signals with `i` inputs on one side,
bounds the accepted inputs of a `K`-rectangle-free function by
`K (2 ^ (i + |B|) + 2 ^ (n - i + |A|))`.
`MultiOutput.Ordering` transfers the graph-ordering hypothesis to programs over
any signature with fan-in two and any number of outputs: a ranking of the wires
whose prefixes are crossed by at most `(A + η) (s - n)⁺ + O(log (n + s))`
signals, component by component.
`MultiOutput.Rank` bounds the signals crossing any split of a circuit computing
a linear map `x ↦ M x` over a finite field below by
`rank M[Y_T, X_S] + rank M[Y_S, X_T]`.
`MultiOutput.TotallyRegular` combines the two: a fan-in-two circuit over a
finite field computing a totally regular `N × N` map, such as an explicit
Cauchy matrix over `ZMod q`, has more than `(1 + 1/(2 κ_E) - ε) N ≥ (41/9 - ε) N`
gates for all large `N`.
`MultiOutput.Quadratic` proves the single-output analogue for quadratic forms
`x ↦ xᵀ M x`: every split is crossed by at least `rank (M + Mᵀ)[X_S, X_T]`
signals, so a fan-in-two circuit over a finite field computing such a form with
`M + Mᵀ` totally regular, such as the Hankel Cauchy matrix `1 / (i + j + 2)` over
`ZMod q`, has more than `(1 + 1/(4 κ_E) - ε) N ≥ (25/9 - ε) N` gates for all
large `N`. The rank-cut bound also holds when a combination of several outputs
is the quadratic form.
`MultiOutput.Restrict` restricts the fibre bound to product domains and to the
inputs with some coordinates fixed. `MultiOutput.FieldMul` applies it to
multiplication in a degree-`n` extension of a finite field, written in a basis:
fixing one factor makes it linear, and averaging over the fixed factor shows
that a fan-in-two circuit over any signature has more than
`(2 + 1/(2 κ_E) - ε) n ≥ (50/9 - ε) n` gates for all large `n`, in particular for
`GF(2 ^ n)` over the full binary basis.
`MultiOutput.MatMul.Tripartite` proves the charging combinatorics of the terminal
graph of `n × n` matrix multiplication, the complete tripartite graph on the
three index sets, and the threshold prefix of a ranking.

`Bisection.Helpful` completes the graph theorem. Its proof uses the first
boundary normalization phase, a partition into bounded connected clusters,
red-edge incidence counting, and the exact boundary lift. The resulting
bounded helpful-set theorem combines with accumulation and logarithmic-cost
rebalancing. The second normalization phase, thin-path systems, weighted core
forests, and simultaneous restoration remain available as separate graph APIs.

`Extractor` transfers flat-source sumset extraction to the hard-family
properties. `Extractor.Padding` permits any fixed error below one half by
adding a balancing bit. `Extractor.SourceReduction` proves that the stated
low-order parity bounds on enough good source fixings imply extraction with
error `35/72`, by composing the moment, majority, and conditioning arguments.
`Extractor.Sampler` supplies the finite extractor-to-sampler conversion and
amplification; `SourceReduction.Selection` proves the simultaneous choice of
good parity coordinates from individual bad-seed bounds. `Condenser.Polynomial`
defines the underlying modular polynomial map and proves its source linearity.
`Condenser.Expansion` proves its finite neighbor expansion for a supplied
irreducible modulus, using interpolation and quotient-field root counting.
`Condenser.Lossless.Polynomial` converts this to flat-source lossless
condensation while preserving the seed; the mixture layer extends it to all
larger flat supports. `Modulus.Binomial` supplies a sparse
irreducible family from a noncube coefficient, and its `Extension` module
proves that the quotient root supplies another noncube.
`Modulus.Binary` gives an explicit irreducible binary trinomial family, its
fixed-width quotient codec, and a uniform encoded modular-powering program.
Its `Extension` module identifies the binomial tower with a larger binary quotient.
`Condenser.Encoding.Correctness` proves that the actual uniform `FP` program,
using coefficient transposition and modular Horner evaluation, computes the
polynomial condenser and preserves source addition. Source packing preserves
all fixed-length inputs within capacity. `Encoding.Lossless` transfers the
flat-source and mixture guarantees to this actual program.
`Parameters.Sparse` proves that field bit lengths twice a power of three
preserve the intended output rate with the appropriate powering exponent.
`Parameters.Explicit` selects the dimensions from source length, entropy,
inverse error, and rate; `Encoding.Explicit` computes them uniformly and
proves error at most `2^(-e)` for the resulting program.
`Strong` retains the seed in its statistical comparison. `Hashing` proves the
sharp leftover-hash bound and instantiates it with uniform binary field
multiplication and truncation. `Strong.Composition` retains both independent
seeds through a mixture-aware condenser-to-extractor argument.
`Strong.OneShot` joins these results to an actual linear `FP` bit program,
extracting `ell` bits with error `2^(-e)` from sources of min-entropy at
least `ell + 2*e`. `Strong.FlatMixture` decomposes arbitrary capped weights
into exact-size flat sources. `Strong.Weighted` extends both extraction
and lossless condensation to these weights with the same error.
`Strong.Weighted.Coupling` repairs a marginal while retaining correlations.
`Strong.Weighted.Conditional` completes null rows and retains the actual side-information law.
Its `Transport` layer preserves conditional distance under tag-dependent output bijections.
`Strong.Weighted.Transcript` factors the actual law after left, right, or adaptive observations.
Its `Envelope` layer charges only source-side messages against the average entropy budget.
`Coupling.Conditional` replaces a marginal at its exact average distance while retaining
the transcript and the other coordinate jointly.
`Coupling.Factored` repairs a distinguished right state to uniform while preserving
both original sources and the factored law. Continuation costs one repair distance
when the retained marginal is preserved, and at most two otherwise.
`Strong.Weighted.Leakage` bounds extraction error using an average joint-mass envelope;
individual conditional sources need not all retain the extractor's entropy threshold.
`Strong.Weighted.Merging` combines this with a seed close to uniform given a right-side
observation, retaining the entire right variable and charging its seed error once.
`Merging.Independence` merges two possibly overlapping tampering sets with error
`2*epsilon+delta` under the explicit average-envelope budget.
`Strong.Weighted.Affine` extracts from a source combined with a correlated right mask,
retaining the full right state whenever fixed-mask output transport is bijective.
`Strong.Weighted.Alternating` switches extraction sides after a message and composes
an actual affine extraction with the next call, retaining the entire opposite source.
`Strong.Weighted.LookAhead` proves the actual two-round, one-tampering transition,
retaining the complete right state and both first outputs with explicit entropy charges.
Its `UniformState` layer derives the next look-ahead from a nearly uniform refreshed
state. `Refresh` proves both first refresh estimates with exact transcript factors and
original-source envelopes. `FixedTampering` handles a left-only tampered seed in the
next extraction and refresh, retaining the original left source. Its `Second` layer
handles the second look-ahead output and proves that a normalized left observation
preserves the original average seed discrepancy exactly. `UniformRefresh` handles
either selected refresh from whole-state uniformity, with arbitrary correlated
tampering and no pointwise current-state entropy premise.
`Strong.Weighted.Perturbation` handles seeds close to jointly independent uniform seeds,
including the extra distance needed to retain the actual tag-and-seed marginal.
`Strong.Block.Splitting` repairs a two-block source with a quantified error.
`Strong.Block` supplies the general prefix-based block-source invariant.
`Strong.Block.Splitting.Iterated` splits every dependent pair into successive
half-blocks at error at most `t * 2^(-e)`, preserving the required conditional caps.
Its family corollary retains the earlier seed with the same joint error.
`Strong.Block.Condenser` applies one seed across dependent blocks with at
most one condenser error per block. Its extraction corollary compares the
entire output tuple with uniform; the scheduled condenser has the same shared-seed
guarantee on actual decoded blocks. `Strong.OneShot.Block` similarly reuses
one pair of field seeds across all leaves, with error at most `t * 2^(-e)`.
`Strong.Weighted.SeedStep` retains earlier randomness and adds a fresh seed
without increasing a prior joint error. `Strong.Block.Level` combines condensation
and splitting; `Strong.Block.Recursion` iterates the actual finite maps with an
explicit error sum and one seed per level. Its extraction theorem joins an initial
condenser, all levels, and a final block extractor, with the finite dyadic error budget.
Fixed-seed additivity is preserved when the supplied component maps preserve addition.
`Condenser.Encoding.Explicit.Pair` splits the actual condenser output into
two equal Boolean-vector halves with the same entropy threshold and error.
Its splitting budget supplies the two finite entropy inequalities for a level.
`Condenser.Encoding.Explicit.Block.Program` computes one shared-seed block
level uniformly in polynomial time, with exact fixed-width tuple semantics.
Its correctness theorem identifies the result with the statistical level map.
`Strong.Block.Recursion.Scheduled` specifies all component maps and a
constant-rate integer schedule, discharges its entropy budgets, and proves
the strong-extraction guarantee. Its seed cardinality and finite seed-bit
bound are explicit, and its actual maps preserve source XOR for fixed seeds.
`Scheduled.Asymptotics` supplies a fixed family with logarithmic seed length,
sublinear source entropy, and any fixed power of logarithmic output length.
`Scheduled.Codec` identifies its retained seed tuples with exact-length bit words.
`Scheduled.Program` evaluates initial condensation, the bounded block loop, and
the final shared extraction uniformly in polynomial time, including all parameter
generation. Its correctness theorem identifies the full output with the statistical
tuple. `Program.Family` gives one polynomial-time string evaluator for each fixed
family and proves eventual agreement on all source inputs and canonical seeds.
`Scheduled.Boolean` supplies the actual program on fixed-length Boolean sources
and seeds, with the strong-extraction guarantee and fixed-seed XOR law. Its public
statistical statements require no field enumeration instances.
`Scheduled.Affine` applies this actual program to a source XOR a correlated right mask,
with the full right state retained and an explicit average-entropy error budget.
`Scheduled.BoundedDepth` bounds its actual seed width and entropy at fixed depths,
providing finite parameters for matching the short alternating calls.
`Scheduled.Matched` runs the actual bit program with those matched widths, retaining
the full padded seed in its strong guarantee. Its `Program` layer gives a total
uniform polynomial-time runtime and canonical agreement, including arbitrary seed tails.
`Matched.Growing` supplies the statistical guarantee at variable depth under an explicit
depth/error/logarithm budget. Its `Program` layer gives a total polynomial-time evaluator
at depth `clog 2 (t+1)+64`, with polynomial block count in the unary parameter `t`, exact
vector agreement, and ignored seed tails. `Matched.Affine` retains the full correlated
right state when the source is XORed with its mask.
`CorrelationBreaker.FlipFlop.Program` composes the actual three-call look-ahead and
eight-call advice-bit step, with exact vector semantics and registered `polytime` proofs.
Its `LookAhead` layer specializes the retained two-round statistical guarantee to these
actual calls without supplied extractors or an intermediate-seed hypothesis.
Its `UniformState` layer instantiates the repaired-state estimate for the actual program.
`FlipFlop.Opposite.False` proves the complete honest-zero/tampered-one execution
from original source envelopes and the initial seed error, retaining both histories,
the tampered final output, and the full original left state.
`Opposite.True` proves the other orientation from the original source and current-state
envelopes and prefix error. `Transcript` factors the actual pair of executions for
arbitrary advice bits into normalized original-source kernels. It gives exact envelope
growth of `D^8` on the left and `C^4` on the right, before observing final outputs.
`Preservation.Half` proves either selected refresh, retaining either tampered refresh,
when the incoming tampered state is fixed by the transcript. Its premises are whole-state
honest uniformity and the original source envelopes, with no current-state entropy cap.
`Opposite.UniformState` supplies the first differing advice bit from whole-state uniformity.
`Preservation.Weak` and `Preservation.Step` cover complete steps before and after that
difference. `Transcript.Output` identifies their exact original-law factors, including
the tampered final state in the separated phase.
`CorrelationBreaker.Advice.Program` computes the complete advice fold and a final
left-source extraction. Its uniform `FP` proof bounds the entire encoded loop state.
`Advice.Extraction` constructs the complete invariant from the original sources and
proves a strong finite bound for unequal equal-length advice, retaining the original
right state and actual tampered output. Its explicit entropy reserve and local error
schedule give any dyadic target. `Advice.Parameters` checks all finite program guards
and reserves; `Advice.Truncation` preserves the guarantee for shorter requested outputs.
`Advice.Extraction.Parameters` combines them into the actual requested-width guarantee
with every numerical side condition discharged by the chooser.
`Advice.Extraction.Program` computes that chooser and requested output in one total
polynomial-time evaluator, with exact agreement on canonical source words.
`Advice.Extraction.Perturbed` allows a jointly near-uniform honest right input and
charges its discrepancy once because the actual retained marginal is preserved.
`Advice.Extraction.Alternating` swaps source sides after a right observation, paying
its alphabet size in the source envelope and requiring the preceding seed estimate.
`Affine.PhaseOne` defines the actual three-call first phase and its complete transcript.
Its `Initial` theorem derives the first extracted seed estimate from the original
uniform right input and left envelope, retaining every first right message.
Its `Transcript` theorems give exact original-law factors and envelope totals for
all three observations, including normalized null rows.
`Second` derives the advice-generated seed guarantee from those original hypotheses.
`Final` and `Extraction` prove the complete actual first phase's pairwise guarantee,
retaining the executed transcript, original right state, and one tampered output.
The original-left contributions satisfy the same bound for later merging, and finite
source reserves give any dyadic error target. No intermediate security witness is assumed.
`PhaseOne.Parameters` supplies all finite component guards and entropy reserves with a
total explicit chooser; its unary generators are uniformly polynomial-time.
`Extraction.Parameters` proves the actual pairwise error `2^-target` from the original
source hypotheses and chosen mass bound, with no remaining numerical guard premise.
`PhaseOne.Program` computes all three calls in one total polynomial-time evaluator.
Canonical agreement needs the three finite component guards, with no statistical premises.
Its `Parameters` wrapper computes the full chooser and normalizes the right word;
canonical agreement then has no numerical or source-capacity premise.
`Strong.Weighted.Merging.Smooth` constructs a conditional uniform-coordinate repair,
preserving all original left observations and charging its distance once. It provides
the smooth-source consumer needed by the next subset-doubling stage.
`NearHalving` uses a rate increasing with depth and a near-halving entropy schedule.
Its rounded parameters give an actual extractor on `8*b` bits at entropy `2*b`,
with `b` output bits, error `1/4`, and seed length at most a cubic logarithm,
for all sufficiently large `b`. Exact seed codecs and payload invariants identify
the complete bit program with this statistical map, including unused seed padding.
`Gamma.Padded` reads this same total polynomial-time program on a seed whose
width is the explicit cubic-logarithmic budget; the entire seed is uniform and
retained in the strong guarantee.
`Affine.Iteration` and its selected parameters complete the actual subset-doubling
induction. `SourceReduction.Construction` composes the actual sampler, fixed affine
tests, XOR, and majority. Its asymptotic layer proves sublinear source entropy and
eventual numerical guards. Its uniform layer bounds every enumeration loop and
provides one total polynomial-time evaluator for a fixed balanced family.
`SourceReduction.Construction.Hardness` proves the unconditional `(4-ε)n`
lower bound for that family, measured at the full input length; its language is in `P`.
`Aggregate` preserves the Gaussian coefficient, about `4.5625`, for binary circuits
augmented by arbitrary finite commutative-monoid gates with sublinear total budget.
The budget counts one output-guess bit and the ceiling logarithm of the register
cardinality per special occurrence. It includes noninvertible AND, OR, and capped
counting, as well as modular and symmetric gates.
`Superconcentrator` applies the graph-ordering hypothesis to superconcentrators: every
`N`-superconcentrator has at least `(2 + 1/A - ε) N` edges, about `5.5625 N` for the
edge-score coefficient, improving the `5 N` of Lev and Valiant.
-/

@[expose] public section
