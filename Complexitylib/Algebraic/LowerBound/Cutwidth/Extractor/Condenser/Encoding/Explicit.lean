/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Polynomial.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Extension.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Encoding.BitPolynomial.Addition.Defs
public import Complexitylib.Tactic.PolyTime.Init
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Internal

/-!
# Uniform binary condensation with an explicit parameter schedule

One polynomial-time program computes the field dimensions, extension degree,
powering stride, coordinate count, and output from four unary parameters and
two input words. Its decoded coordinates are exactly the previously proved
polynomial condenser, and it preserves source XOR for each fixed seed.

The output length satisfies the exact rate bound `u*length ≤ (u+1)*k + u*b`.
The seed width `b` is bounded in `Parameters.Explicit`; the finite statistical
guarantees for this same program are in `Encoding.Explicit.Lossless`. The
underlying polynomial map and sparse-parameter source credits are recorded
in `Condenser.Polynomial` and `Parameters.Sparse`.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity Complexity.BitPolynomial

/-- The output has one fixed-width block per selected coordinate. -/
theorem explicitCondenserBits_length (n k e u : Nat) (source seed : List Bool) :
    (explicitCondenserBits n k e u source seed).length =
      condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)) *
        sparseFieldBits u (explicitCondenserBudget n k e) :=
  Internal.explicitCondenserBits_length n k e u source seed

/-- The actual program's output satisfies the selected rate bound. -/
theorem explicitCondenserBits_output_rate (n k e u : Nat) (source seed : List Bool) :
    u * (explicitCondenserBits n k e u source seed).length ≤
      (u + 1) * k + u * sparseFieldBits u (explicitCondenserBudget n k e) :=
  Internal.explicitCondenserBits_output_rate n k e u source seed

/-- The paired evaluator reads all four numerical parameters from word lengths. -/
theorem explicitCondenserEval_pair (source seed n k e u : List Bool) :
    explicitCondenserEval (pair (pair source seed) (pair (pair n k) (pair e u))) =
      explicitCondenserBits n.length k.length e.length u.length source seed :=
  Internal.explicitCondenserEval_pair source seed n k e u

/-- The scheduled program computes the exact polynomial condenser at its selected parameters. -/
theorem decodedExplicitCondenser_eq (n k e u : Nat) (bits : List Bool)
    (seed : AdjoinRoot (binaryModulus
      (sparseFieldExponent u (explicitCondenserBudget n k e)))) :
    let T := explicitCondenserBudget n k e
    let s := sparseFieldExponent u T
    let v := explicitCondenserExtensionExponent n k e u
    let r := sparsePowerBits u T
    let m := condenserCoordinates k r
    decodedExplicitCondenser n k e u bits seed =
      polynomialCondenser (extensionModulus s v) r m
        (sourcePolynomial s (explicitCondenserExtensionDegree n k e u) bits) seed :=
  Internal.decodedExplicitCondenser_eq n k e u bits seed

/-- For every field seed, the actual scheduled output preserves padded source XOR. -/
theorem decodedExplicitCondenser_addBits (n k e u : Nat) (a b : List Bool)
    (seed : AdjoinRoot (binaryModulus
      (sparseFieldExponent u (explicitCondenserBudget n k e)))) :
    decodedExplicitCondenser n k e u (addBits a b) seed =
      decodedExplicitCondenser n k e u a seed + decodedExplicitCondenser n k e u b seed :=
  Internal.decodedExplicitCondenser_addBits n k e u a b seed

/-- Every all-false source produces the zero coordinate vector. -/
theorem decodedExplicitCondenser_replicate_false (n k e u length : Nat)
    (seed : AdjoinRoot (binaryModulus
      (sparseFieldExponent u (explicitCondenserBudget n k e)))) :
    decodedExplicitCondenser n k e u (List.replicate length false) seed = 0 :=
  Internal.decodedExplicitCondenser_replicate_false n k e u length seed

/-- Uniform polynomial time includes parameter generation, with every operand variable. -/
@[polytime] theorem explicitCondenserBits_mem_FP {n k e u : List Bool → Nat}
    {source seed : List Bool → List Bool}
    (hn : UnaryFn n) (hk : UnaryFn k) (he : UnaryFn e) (hu : UnaryFn u)
    (hsource : source ∈ FP) (hseed : seed ∈ FP) :
    (fun z => explicitCondenserBits (n z) (k z) (e z) (u z) (source z) (seed z)) ∈ FP :=
  Internal.explicitCondenserBits_mem_FP hn hk he hu hsource hseed

/-- A single polynomial-time machine computes the complete paired program. -/
@[polytime] theorem explicitCondenserEval_mem_FP : explicitCondenserEval ∈ FP :=
  Internal.explicitCondenserEval_mem_FP

end Algebraic.Cutwidth.Extractor
