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
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Forget
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Nondeterministic
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Direction
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Balanced
public import Complexitylib.Algebraic.LowerBound.Cutwidth.AverageCase
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
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Expectation
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Leakage
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Independence
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Conditional
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

/-!
# The cutwidth lower bound

This umbrella collects the `(4 - ε) n` lower bound for rectangle-free
functions over the full binary basis. `FourN` combines cut counting, circuit
wiring, compression, and the proved sharp cubic bisection and pathwidth
bounds. `Nondeterministic` extends the conclusion to arbitrarily many witness
inputs; `AverageCase` gives the agreement bound for balanced functions.

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
`Coupling.Conditional` replaces a marginal at its exact average distance while retaining
the transcript and the other coordinate jointly.
`Strong.Weighted.Leakage` bounds extraction error using an average joint-mass envelope;
individual conditional sources need not all retain the extractor's entropy threshold.
`Strong.Weighted.Merging` combines this with a seed close to uniform given a right-side
observation, retaining the entire right variable and charging its seed error once.
`Merging.Independence` merges two possibly overlapping tampering sets with error
`2*epsilon+delta` under the explicit average-envelope budget.
`Strong.Weighted.Affine` extracts from a source combined with a correlated right mask,
retaining the full right state whenever fixed-mask output transport is bijective.
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
`NearHalving` uses a rate increasing with depth and a near-halving entropy schedule.
Its rounded parameters give an actual extractor on `8*b` bits at entropy `2*b`,
with `b` output bits, error `1/4`, and seed length at most a cubic logarithm,
for all sufficiently large `b`. Exact seed codecs and payload invariants identify
the complete bit program with this statistical map, including unused seed padding.
`Gamma.Padded` reads this same total polynomial-time program on a seed whose
width is the explicit cubic-logarithmic budget; the entire seed is uniform and
retained in the strong guarantee.
The affine correlation breaker, its internal extractor requirements, parity estimates,
and composition into the final uniform hard family remain necessary for a lower
bound on a concrete language in `P`.
-/

@[expose] public section
