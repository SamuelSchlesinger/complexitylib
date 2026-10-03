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
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Linear
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Unary
import Complexitylib.Tactic.PolyTime

/-!
# Correctness and polynomial time for the selected parameter schedule

The previously checked runtime program is instantiated at the finite explicit
parameters. The semantic statements retain arbitrary source and seed values;
the resource proof composes unary parameter generation with the program's
existing polynomial-time certificate.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity Complexity.BitPolynomial

theorem explicitCondenserBits_length (n k e u : Nat) (source seed : List Bool) :
    (explicitCondenserBits n k e u source seed).length =
      condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)) *
        sparseFieldBits u (explicitCondenserBudget n k e) := by
  simp only [explicitCondenserBits, condenserBits_length, List.length_replicate, sparseFieldBits]

theorem explicitCondenserBits_output_rate (n k e u : Nat) (source seed : List Bool) :
    u * (explicitCondenserBits n k e u source seed).length ≤
      (u + 1) * k + u * sparseFieldBits u (explicitCondenserBudget n k e) := by
  rw [explicitCondenserBits_length]
  exact explicitCondenser_output_rate n k e u

theorem explicitCondenserEval_pair (source seed n k e u : List Bool) :
    explicitCondenserEval (pair (pair source seed) (pair (pair n k) (pair e u))) =
      explicitCondenserBits n.length k.length e.length u.length source seed := by
  simp only [explicitCondenserEval, pairFst_pair, pairSnd_pair]

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
        (sourcePolynomial s (explicitCondenserExtensionDegree n k e u) bits) seed := by
  let T := explicitCondenserBudget n k e
  let s := sparseFieldExponent u T
  let v := explicitCondenserExtensionExponent n k e u
  let r := sparsePowerBits u T
  let m := condenserCoordinates k r
  have h := decodedCondenser_eq s v (List.replicate (3 ^ s) true)
    (List.replicate (3 ^ v) true) (List.replicate r true) (List.replicate m true)
    bits seed (by simp) (by simp)
  unfold decodedCondenser at h
  rw [List.length_replicate] at h
  simpa only [decodedExplicitCondenser, explicitCondenserBits, List.length_replicate,
    explicitCondenserExtensionDegree, sparseFieldBits, T, s, v, r, m] using h

theorem decodedExplicitCondenser_addBits (n k e u : Nat) (a b : List Bool)
    (seed : AdjoinRoot (binaryModulus
      (sparseFieldExponent u (explicitCondenserBudget n k e)))) :
    decodedExplicitCondenser n k e u (addBits a b) seed =
      decodedExplicitCondenser n k e u a seed + decodedExplicitCondenser n k e u b seed := by
  let T := explicitCondenserBudget n k e
  let s := sparseFieldExponent u T
  let v := explicitCondenserExtensionExponent n k e u
  let r := sparsePowerBits u T
  let m := condenserCoordinates k r
  have h := decodedCondenser_addBits s v (List.replicate (3 ^ s) true)
    (List.replicate (3 ^ v) true) (List.replicate r true) (List.replicate m true)
    a b seed (by simp) (by simp)
  unfold decodedCondenser at h
  rw [List.length_replicate] at h
  simpa only [decodedExplicitCondenser, explicitCondenserBits, List.length_replicate,
    explicitCondenserExtensionDegree, sparseFieldBits, T, s, v, r, m] using h

theorem decodedExplicitCondenser_replicate_false (n k e u length : Nat)
    (seed : AdjoinRoot (binaryModulus
      (sparseFieldExponent u (explicitCondenserBudget n k e)))) :
    decodedExplicitCondenser n k e u (List.replicate length false) seed = 0 := by
  let T := explicitCondenserBudget n k e
  let s := sparseFieldExponent u T
  let v := explicitCondenserExtensionExponent n k e u
  let r := sparsePowerBits u T
  let m := condenserCoordinates k r
  have h := decodedCondenser_replicate_false s v length (List.replicate (3 ^ s) true)
    (List.replicate (3 ^ v) true) (List.replicate r true) (List.replicate m true)
    seed (by simp) (by simp)
  unfold decodedCondenser at h
  rw [List.length_replicate] at h
  simpa only [decodedExplicitCondenser, explicitCondenserBits, List.length_replicate,
    explicitCondenserExtensionDegree, sparseFieldBits, T, s, v, r, m] using h

theorem explicitCondenserBits_mem_FP {n k e u : List Bool → Nat}
    {source seed : List Bool → List Bool}
    (hn : UnaryFn n) (hk : UnaryFn k) (he : UnaryFn e) (hu : UnaryFn u)
    (hsource : source ∈ FP) (hseed : seed ∈ FP) :
    (fun z => explicitCondenserBits (n z) (k z) (e z) (u z) (source z) (seed z)) ∈ FP := by
  polytime [explicitCondenserBits]

theorem explicitCondenserEval_mem_FP : explicitCondenserEval ∈ FP := by
  unfold explicitCondenserEval
  apply explicitCondenserBits_mem_FP <;> polytime

end Algebraic.Cutwidth.Extractor.Internal
