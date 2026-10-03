/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Block.Program.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot
import Complexitylib.Encoding.BitPolynomial
import Complexitylib.Classes.P.Range
import Complexitylib.Tactic.PolyTime
import Mathlib.Data.List.OfFn

/-!
# Fixed-width semantics and uniformity of shared-seed leaf extraction

Each slice is one runtime input to the existing one-shot extractor. Equal
input widths recover the original tuple, and equal output widths recover
the decoded statistical tuple. Polynomial-time range concatenation keeps
all numerical parameters, both seeds, and the block count as runtime data.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity Complexity.BitPolynomial

theorem oneShotBlockExtractorBits_length (n ell e : Nat)
    (blocks condenserSeed hashSeed count : List Bool) :
    (oneShotBlockExtractorBits n ell e blocks condenserSeed hashSeed count).length =
      count.length * ell := by
  simp [oneShotBlockExtractorBits, oneShotExtractorBits_length]

private theorem coefficientBlock_flatten_ofFn (t width : Nat) (blocks : Fin t → List Bool)
    (length : ∀ i, (blocks i).length = width) (i : Fin t) :
    coefficientBlock (List.ofFn blocks).flatten width i.val = blocks i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [coefficientBlock, Fin.val_zero, Nat.zero_mul, List.drop_zero,
        List.ofFn_succ, List.flatten_cons]
      exact List.take_left' (length 0)
    · simp only [coefficientBlock, Fin.val_succ, Nat.add_mul, Nat.one_mul,
        List.ofFn_succ, List.flatten_cons]
      rw [Nat.add_comm (j.val * width) width, ← length 0, List.drop_length_add_append]
      simpa only [coefficientBlock, ← length 0] using
        ih (fun j => blocks j.succ) (fun j => length j.succ) j

theorem oneShotBlockExtractorBits_ofFn (n ell e : Nat) {t : Nat}
    (blocks : Fin t → Fin n → Bool) (condenserSeed hashSeed count : List Bool)
    (size : count.length = t) :
    oneShotBlockExtractorBits n ell e
        (List.ofFn (fun i => List.ofFn (blocks i))).flatten condenserSeed hashSeed count =
      (List.ofFn (fun i => oneShotExtractorBits n ell e (List.ofFn (blocks i))
        condenserSeed hashSeed)).flatten := by
  rw [oneShotBlockExtractorBits, size, List.flatMap_def]
  apply congrArg List.flatten
  apply List.ext_getElem (by simp)
  intro j hj _
  have bound : j < t := by simpa using hj
  simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using
    congrArg (fun bits => oneShotExtractorBits n ell e bits condenserSeed hashSeed)
      (coefficientBlock_flatten_ofFn t n (fun i => List.ofFn (blocks i))
        (fun _ => List.length_ofFn) ⟨j, bound⟩)

private theorem oneShotExtractorBits_eq_decoded (n ell e : Nat) (source : List Bool)
    (seeds : AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)) ×
      AdjoinRoot (binaryModulus (oneShotHashExponent n ell e))) :
    oneShotExtractorBits n ell e source
        (BinaryFieldCodec.encode (oneShotCondenserExponent n ell e) seeds.1)
        (BinaryFieldCodec.encode (oneShotHashExponent n ell e) seeds.2) =
      List.ofFn (fun j => decide (decodedOneShotExtractor n ell e source seeds j = 1)) := by
  let bits := oneShotExtractorBits n ell e source
    (BinaryFieldCodec.encode (oneShotCondenserExponent n ell e) seeds.1)
    (BinaryFieldCodec.encode (oneShotHashExponent n ell e) seeds.2)
  change bits = List.ofFn (fun j : Fin ell =>
    decide (Polynomial.toFn ell (ofBits bits) j = 1))
  apply List.ext_getElem (by simp only [bits, oneShotExtractorBits_length, List.length_ofFn])
  intro j hj _
  simp only [List.getElem_ofFn, Polynomial.toFn, LinearMap.pi_apply, Polynomial.lcoeff_apply,
    ofBits_coeff, List.getElem?_eq_getElem hj, Option.getD_some]
  cases bits[j] <;> decide

theorem oneShotBlockExtractorBits_eq_decoded (n ell e : Nat) {t : Nat}
    (blocks : Fin t → Fin n → Bool)
    (seeds : AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)) ×
      AdjoinRoot (binaryModulus (oneShotHashExponent n ell e)))
    (count : List Bool) (size : count.length = t) :
    oneShotBlockExtractorBits n ell e
        (List.ofFn (fun i => List.ofFn (blocks i))).flatten
        (BinaryFieldCodec.encode (oneShotCondenserExponent n ell e) seeds.1)
        (BinaryFieldCodec.encode (oneShotHashExponent n ell e) seeds.2) count =
      (List.ofFn (fun i => List.ofFn (fun j =>
        decide (decodedOneShotExtractor n ell e (List.ofFn (blocks i)) seeds j = 1)))).flatten := by
  rw [oneShotBlockExtractorBits_ofFn n ell e blocks _ _ count size]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact oneShotExtractorBits_eq_decoded n ell e (List.ofFn (blocks i)) seeds

theorem oneShotBlockExtractorBits_mem_FP {n ell e : List Bool → Nat}
    {blocks condenserSeed hashSeed count : List Bool → List Bool}
    (hn : UnaryFn n) (hell : UnaryFn ell) (he : UnaryFn e)
    (hblocks : blocks ∈ FP) (hcondenser : condenserSeed ∈ FP)
    (hhash : hashSeed ∈ FP) (hcount : count ∈ FP) :
    (fun z => oneShotBlockExtractorBits (n z) (ell z) (e z)
      (blocks z) (condenserSeed z) (hashSeed z) (count z)) ∈ FP := by
  have entry : (fun w => oneShotExtractorBits
      (n (pairFst w)) (ell (pairFst w)) (e (pairFst w))
      (coefficientBlock (blocks (pairFst w)) (n (pairFst w)) (pairSnd w).length)
      (condenserSeed (pairFst w)) (hashSeed (pairFst w))) ∈ FP := by
    dsimp only [coefficientBlock]
    polytime
  refine mem_FP_of_eq (flatMap_range_mem_FP entry hcount) fun z => ?_
  simp only [oneShotBlockExtractorBits, pairFst_pair, pairSnd_pair, List.length_replicate]

end Algebraic.Cutwidth.Extractor.Internal
