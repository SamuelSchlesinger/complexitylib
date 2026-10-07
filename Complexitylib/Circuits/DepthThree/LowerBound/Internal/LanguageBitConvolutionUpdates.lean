/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageBitLoopInvariants
public import Mathlib.Data.List.GetD

/-!
# Unrestricted depth-three lower bound: language bit convolution updates

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/LanguageBitConvolutionUpdates.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

/-- XOR a bit into a selected list position. -/
def xorListAt (c : List Bool) (k : ℕ) (v : Bool) : List Bool :=
  c.set k (Bool.xor (c.getD k false) v)

@[simp] theorem xorListAt_length (c : List Bool) (k : ℕ) (v : Bool) :
    (xorListAt c k v).length = c.length := by
  simp [xorListAt]

theorem xorListAt_getD (c : List Bool) (j : ℕ) (v : Bool)
    (hj : j < c.length) (k : ℕ) :
    (xorListAt c j v).getD k false =
      Bool.xor (c.getD k false) (if j = k then v else false) := by
  by_cases h : j = k
  · subst k
    simp [xorListAt, List.getElem?_set_self hj]
  · simp [xorListAt, h, List.getElem?_set_ne h]

theorem xorListAt_split («prefix» suffix : List Bool) (old v : Bool) :
    xorListAt («prefix» ++ old :: suffix) «prefix».length v =
      «prefix» ++ Bool.xor old v :: suffix := by
  unfold xorListAt
  rw [List.getD_append_right «prefix» (old :: suffix) false «prefix».length le_rfl]
  simp

/-- Accumulate one row of bitwise convolution updates. -/
def convolutionUpdateRow (a b : List Bool) (i : ℕ) :
    List ℕ → List Bool → List Bool
  | [], c => c
  | j :: js, c => convolutionUpdateRow a b i js
      (xorListAt c (i + j) (a.getD i false && b.getD j false))

@[simp] theorem convolutionUpdateRow_nil (a b : List Bool) (i : ℕ) (c : List Bool) :
    convolutionUpdateRow a b i [] c = c := rfl

theorem convolutionUpdateRow_step (a b : List Bool) (i j : ℕ)
    (js : List ℕ) (c : List Bool) :
    convolutionUpdateRow a b i (j :: js) c =
      convolutionUpdateRow a b i js
        (xorListAt c (i + j) (a.getD i false && b.getD j false)) := rfl

@[simp] theorem convolutionUpdateRow_length (a b : List Bool) (i : ℕ)
    (js : List ℕ) (c : List Bool) :
    (convolutionUpdateRow a b i js c).length = c.length := by
  induction js generalizing c with
  | nil => rfl
  | cons j js ih =>
      rw [convolutionUpdateRow_step, ih, xorListAt_length]

theorem convolutionUpdateRow_getD (a b : List Bool) (i : ℕ)
    (js : List ℕ) (c : List Bool) (k : ℕ)
    (hbound : ∀ j ∈ js, i + j < c.length) :
    (convolutionUpdateRow a b i js c).getD k false =
      Bool.xor (c.getD k false)
        (xorBits (js.map fun j =>
          if i + j = k then a.getD i false && b.getD j false else false)) := by
  induction js generalizing c with
  | nil => simp
  | cons j js ih =>
      have hj : i + j < c.length := hbound j (by simp)
      have hrest : ∀ j' ∈ js, i + j' <
          (xorListAt c (i + j) (a.getD i false && b.getD j false)).length := by
        intro j' hj'
        rw [xorListAt_length]
        exact hbound j' (List.mem_cons_of_mem j hj')
      rw [convolutionUpdateRow_step, ih _ hrest,
        xorListAt_getD c (i + j) (a.getD i false && b.getD j false) hj k]
      simp only [List.map_cons, xorBits_cons, Bool.xor_assoc]

/-- Accumulate all rows of bitwise convolution updates. -/
def convolutionUpdateRows (a b : List Bool) : List ℕ → List Bool → List Bool
  | [], c => c
  | i :: is, c => convolutionUpdateRows a b is
      (convolutionUpdateRow a b i (List.range b.length) c)

@[simp] theorem convolutionUpdateRows_nil (a b : List Bool) (c : List Bool) :
    convolutionUpdateRows a b [] c = c := rfl

theorem convolutionUpdateRows_step (a b : List Bool) (i : ℕ)
    (is : List ℕ) (c : List Bool) :
    convolutionUpdateRows a b (i :: is) c =
      convolutionUpdateRows a b is
        (convolutionUpdateRow a b i (List.range b.length) c) := rfl

@[simp] theorem convolutionUpdateRows_length (a b : List Bool)
    (is : List ℕ) (c : List Bool) :
    (convolutionUpdateRows a b is c).length = c.length := by
  induction is generalizing c with
  | nil => rfl
  | cons i is ih =>
      rw [convolutionUpdateRows_step, ih, convolutionUpdateRow_length]

theorem convolutionUpdateRows_getD (a b : List Bool)
    (is : List ℕ) (c : List Bool) (k : ℕ)
    (hbound : ∀ i ∈ is, ∀ j < b.length, i + j < c.length) :
    (convolutionUpdateRows a b is c).getD k false =
      Bool.xor (c.getD k false)
        (xorBits (is.map fun i => xorBits (convolutionRow a b i k))) := by
  induction is generalizing c with
  | nil => simp
  | cons i is ih =>
      have hcols : ∀ j ∈ List.range b.length, i + j < c.length := by
        intro j hj
        exact hbound i (by simp) j (List.mem_range.mp hj)
      have hrest : ∀ i' ∈ is, ∀ j < b.length, i' + j <
          (convolutionUpdateRow a b i (List.range b.length) c).length := by
        intro i' hi' j hj
        rw [convolutionUpdateRow_length]
        exact hbound i' (List.mem_cons_of_mem i hi') j hj
      rw [convolutionUpdateRows_step, ih _ hrest,
        convolutionUpdateRow_getD a b i (List.range b.length) c k hcols]
      simp only [List.map_cons, xorBits_cons, convolutionRow, Bool.xor_assoc]

/-- Compute bit-list convolution by successive updates. -/
def convolveByUpdates (a b : List Bool) : List Bool :=
  convolutionUpdateRows a b (List.range a.length)
    (List.replicate (a.length + b.length) false)

@[simp] theorem convolveByUpdates_length (a b : List Bool) :
    (convolveByUpdates a b).length = a.length + b.length := by
  simp [convolveByUpdates]

theorem convolutionUpdate_index_lt (a b : List Bool) {i j : ℕ}
    (hi : i < a.length) (hj : j < b.length) :
    i + j < a.length + b.length :=
  Nat.add_lt_add hi hj

theorem convolveByUpdates_getD (a b : List Bool) (k : ℕ) :
    (convolveByUpdates a b).getD k false = convolutionBit a b k := by
  have hbound : ∀ i ∈ List.range a.length, ∀ j < b.length,
      i + j < (List.replicate (a.length + b.length) false).length := by
    intro i hi j hj
    simpa only [List.length_replicate] using
      convolutionUpdate_index_lt a b (List.mem_range.mp hi) hj
  unfold convolveByUpdates
  rw [convolutionUpdateRows_getD a b (List.range a.length)
    (List.replicate (a.length + b.length) false) k hbound]
  simp [convolutionBit, convolutionRows]

theorem convolveByUpdates_eq (a b : List Bool) :
    convolveByUpdates a b = convolveBitLists a b := by
  apply List.ext_getElem
  · simp
  · intro k hk hl
    have hk' : k < a.length + b.length := by
      simpa only [convolveBitLists_length] using hl
    have hleft := convolveByUpdates_getD a b k
    have hright : (convolveBitLists a b).getD k false = convolutionBit a b k := by
      simp [convolveBitLists, List.getElem?_range hk']
    rw [List.getD_eq_getElem _ _ hk] at hleft
    rw [List.getD_eq_getElem _ _ hl] at hright
    exact hleft.trans hright.symm

end DepthThreeLowerBound

end Complexity
