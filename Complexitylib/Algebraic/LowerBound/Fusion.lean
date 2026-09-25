/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Framework
public import Complexitylib.Algebraic.LowerBound.Fusion.Substitution
public import Complexitylib.Algebraic.LowerBound.Fusion.Contextual
public import Complexitylib.Algebraic.LowerBound.Fusion.Counting
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Atoms
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.ExactSupport
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.BoundedFailure
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Combined
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Expression
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Power
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Rank
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Rank.Local
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Rank.Occurrence
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Multiple
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Linear
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Linear.Quotient
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.MultiplicativeShadow
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.MultiplicativeShadow.Polynomial
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.MultiplicativeShadow.Pairwise
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Quotient
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Nonlinear
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Degree
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Decomposition
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Profile
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Profile.Multiplication
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular.Profile.Decomposition
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Decomposition
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Mixing
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Squarefree
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Squarefree.Mixing
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Hessian
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Hessian.Pairing
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Hessian.Pairwise
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Support
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.MonotonePolynomial
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.MonotonePolynomial.Layer
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.MonotonePolynomial.Exact
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.General
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Expansion
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.MonomialSubstitution
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.WeightedMonomialSubstitution
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.Addition
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.PositiveConstants
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.Weighted
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.Weighted.Addition
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.Weighted.Exact
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.Weighted.NNRat
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Unit
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Collision
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Addition
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Polynomial
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Clique
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Clique.PositiveConstants
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Clique.NaturalConstants
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Clique.NNRat
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Clique.Exact
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Clique.Total
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Degree
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Rank
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.WeightedRank
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.MatrixRank
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.MatrixRank.Support
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.MatrixRank.Block
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.MatrixRank.BlockSum
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.MatrixRank.Cover
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.MatrixRank.Cover.Identity
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Rectangular
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Rectangular.Translation.Binary
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Rectangular.Restriction.Binary
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Rectangular.Restriction.Binary.Compilation
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Translation
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Translation.Binary
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Restriction
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Restriction.Binary
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Restriction.Binary.Compilation
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Coverage
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Rectangle
public import Complexitylib.Algebraic.LowerBound.Fusion.Semifilter
public import Complexitylib.Algebraic.LowerBound.Fusion.Cyclic
public import Complexitylib.Algebraic.LowerBound.Fusion.Cyclic.Closure
public import Complexitylib.Algebraic.LowerBound.Fusion.Cyclic.JoinMeet
public import Complexitylib.Algebraic.LowerBound.Fusion.Cyclic.Compiler
public import Complexitylib.Algebraic.LowerBound.Fusion.Cyclic.LowerJoinMeet
public import Complexitylib.Algebraic.LowerBound.Fusion.Cyclic.Complete
public import Complexitylib.Algebraic.LowerBound.Fusion.Boolean
public import Complexitylib.Algebraic.LowerBound.Fusion.Pullback
public import Complexitylib.Algebraic.LowerBound.Fusion.Conondeterministic
public import Complexitylib.Algebraic.LowerBound.Fusion.Neq
public import Complexitylib.Algebraic.LowerBound.Fusion.Conondeterministic.Neq
public import Complexitylib.Algebraic.LowerBound.Fusion.Cyclic.Neq
public import Complexitylib.Algebraic.LowerBound.Fusion.Comap
public import Complexitylib.Algebraic.LowerBound.Fusion.Neq.Preimage
public import Complexitylib.Algebraic.LowerBound.Fusion.CrownCollision
public import Complexitylib.Algebraic.LowerBound.Fusion.Graph.Canonical

/-!
# Fusion lower bounds

This umbrella exports the algebra-generic fusion engine, its semi-filter
set-cover specialization, and the pointwise Boolean interfaces.

The semi-filter layer formalizes the acyclic lower-bound direction of the
modern cover-complexity presentation.  The converse via cyclic circuits is a
different computational model and is intentionally not folded into
`Program`.

Fusion models and their lower bounds transport along homomorphisms without
changing atom costs (`Comap`).

Restricting crown-graph collision to one-hot assignments gives the inequality
problem and hence a logarithmic AND-gate lower bound (`CrownCollision`).

References:

* A. Wigderson, *The Fusion Method for Lower Bounds in Circuit Complexity*
  (1993).
* B. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and
  Two-Dimensional Cover Problems* (2025), https://arxiv.org/abs/2503.14117.
* J. Pich, *Localizability of the Approximation Method* (2022),
  https://arxiv.org/abs/2212.09285.
-/

@[expose] public section
