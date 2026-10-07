/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageBitEvaluator

/-!
# Unrestricted depth-three lower bound: language bit loop invariants

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/LanguageBitLoopInvariants.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

namespace DepthThreeLowerBound

/-- Scan a bit list while applying the specified XOR update. -/
def xorScan : Bool → List Bool → Bool
  | acc, [] => acc
  | acc, b :: bs => xorScan (Bool.xor acc b) bs

@[simp] theorem xorScan_nil (acc : Bool) : xorScan acc [] = acc := rfl

theorem xorScan_step (acc b : Bool) (bs : List Bool) :
    xorScan acc (b :: bs) = xorScan (Bool.xor acc b) bs := rfl

theorem xorScan_eq (acc : Bool) (bs : List Bool) :
    xorScan acc bs = Bool.xor acc (xorBits bs) := by
  induction bs generalizing acc with
  | nil => simp [xorScan]
  | cons b bs ih =>
    simp only [xorScan, xorBits_cons, ih, Bool.xor_assoc]

theorem xorBits_append (a b : List Bool) :
    xorBits (a ++ b) = Bool.xor (xorBits a) (xorBits b) := by
  induction a with
  | nil => simp
  | cons x a ih =>
    simp only [List.cons_append, xorBits_cons, ih, Bool.xor_assoc]

theorem xorScan_prefix_invariant (done todo : List Bool) :
    xorScan (xorBits done) todo = xorBits (done ++ todo) := by
  rw [xorScan_eq, xorBits_append]

theorem ofFn_nat_eq_map_range {α : Type uDepth1} (n : ℕ) (f : ℕ → α) :
    List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- The partial convolution after processing one input row. -/
def convolutionRow (a b : List Bool) (i k : ℕ) : List Bool :=
  (List.range b.length).map fun j =>
    if i + j = k then a.getD i false && b.getD j false else false

/-- The convolution accumulator after processing successive rows. -/
def convolutionRows (a b : List Bool) (k : ℕ) : List Bool :=
  (List.range a.length).map fun i => xorBits (convolutionRow a b i k)

/-- The contribution of the input bit pair to the convolution accumulator. -/
def convolutionBit (a b : List Bool) (k : ℕ) : Bool :=
  xorBits (convolutionRows a b k)

theorem convolutionRow_scan (a b : List Bool) (i k : ℕ) :
    xorScan false (convolutionRow a b i k) = xorBits (convolutionRow a b i k) := by
  simp [xorScan_eq]

theorem convolutionRows_scan (a b : List Bool) (k : ℕ) :
    xorScan false (convolutionRows a b k) = convolutionBit a b k := by
  simp [xorScan_eq, convolutionBit]

theorem convolutionBit_eq_wordConvolve (a b : List Bool) (k : ℕ)
    (hk : k < a.length + b.length) :
    convolutionBit a b k =
      wordConvolve (listWord a.length a) (listWord b.length b) ⟨k, hk⟩ := by
  unfold convolutionBit convolutionRows convolutionRow wordConvolve listWord
  simp only [← ofFn_nat_eq_map_range]

/-- Compute the convolution of two polynomial coefficient lists. -/
def convolveBitLists (a b : List Bool) : List Bool :=
  (List.range (a.length + b.length)).map (convolutionBit a b)

@[simp] theorem convolveBitLists_length (a b : List Bool) :
    (convolveBitLists a b).length = a.length + b.length := by
  simp [convolveBitLists]

theorem convolveBitLists_eq (a b : List Bool) :
    convolveBitLists a b =
      wordList (wordConvolve (listWord a.length a) (listWord b.length b)) := by
  unfold convolveBitLists wordList
  rw [← ofFn_nat_eq_map_range]
  apply congrArg List.ofFn
  funext i
  exact convolutionBit_eq_wordConvolve a b i.val i.is_lt

theorem hornerBitLists_nil (r : ℕ) (p h : List Bool) :
    hornerBitLists r p h [] = wordList (fun _ : Fin r => false) := rfl

theorem hornerBitLists_cons (r : ℕ) (p h b : List Bool) (bs : List (List Bool)) :
    hornerBitLists r p h (b :: bs) =
      wordList (wordXor (listWord r b)
        (wordMulMod (listWord r p) (listWord r h)
          (listWord r (hornerBitLists r p h bs)))) := by
  simp [hornerBitLists, wordHorner]

end DepthThreeLowerBound

end Complexity
