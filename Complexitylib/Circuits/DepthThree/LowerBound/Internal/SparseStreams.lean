/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.EntropyBits
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Count
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Unrestricted depth-three lower bound: sparse streams

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/SparseStreams.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

open scoped BigOperators

namespace DepthThreeLowerBound

/-- The binary decision tree recording a sparsification process. -/
inductive SparseDecisionTree (Label : Type uDepth1) where
  | leaf : SparseDecisionTree Label
  | node : Label → SparseDecisionTree Label → SparseDecisionTree Label →
      SparseDecisionTree Label

namespace SparseDecisionTree

variable {Label : Type uDepth2}

/-- Leaves of the sparsification decision tree. -/
def Leaf : SparseDecisionTree Label → Type
  | .leaf => Unit
  | .node _ l r => Leaf l ⊕ Leaf r

/-- The finite enumeration of a sparsification tree's leaves. -/
@[instance_reducible]
def leafFintype : (t : SparseDecisionTree Label) → Fintype t.Leaf
  | .leaf => inferInstanceAs (Fintype Unit)
  | .node _ l r => by
      change Fintype (Leaf l ⊕ Leaf r)
      letI := leafFintype l
      letI := leafFintype r
      infer_instance

instance (t : SparseDecisionTree Label) : Fintype t.Leaf := leafFintype t

/-- The sequence of branch choices leading to a leaf. -/
def stream [DecidableEq Label] : (t : SparseDecisionTree Label) →
    t.Leaf → Label → List Bool
  | .leaf, _, _ => []
  | .node a l _, .inl p, i =>
      if i = a then false :: stream l p i else stream l p i
  | .node a _ r, .inr p, i =>
      if i = a then true :: stream r p i else stream r p i

/-- Read a branch bit from a leaf's choice stream. -/
def streamBit [DecidableEq Label] (t : SparseDecisionTree Label)
    (p : t.Leaf) (i : Label) (k : ℕ) : Bool :=
  (t.stream p i).getD k false

/-- Pad a leaf's choice stream to the specified common length. -/
def padded [DecidableEq Label] (t : SparseDecisionTree Label) (N : Label → ℕ)
    (p : t.Leaf) (i : Label) (k : Fin (N i)) : Bool :=
  t.streamBit p i k

theorem streamBit_injective [DecidableEq Label] (t : SparseDecisionTree Label) :
    Function.Injective t.streamBit := by
  induction t with
  | leaf =>
      intro p q _
      exact Subsingleton.elim (α := Unit) p q
  | node a l r ihl ihr =>
      intro p q h
      cases p with
      | inl p =>
          cases q with
          | inl q =>
              have hpq : p = q := ihl (by
                funext i k
                by_cases hi : i = a
                · subst i
                  simpa only [streamBit, stream, ite_eq_left rfl, ite_true, List.getD_cons_succ]
                    using
                    congrFun (congrFun h a) (k + 1)
                · simpa only [streamBit, stream, ite_eq_right hi] using
                    congrFun (congrFun h i) k)
              exact congrArg Sum.inl hpq
          | inr q =>
              have hfalse : False := by
                simpa only [streamBit, stream, ite_eq_left rfl, ite_true, List.getD_cons_zero,
                  Bool.false_eq_true] using congrFun (congrFun h a) 0
              exact hfalse.elim
      | inr p =>
          cases q with
          | inl q =>
              have hfalse : False := by
                simpa only [streamBit, stream, ite_eq_left rfl, ite_true, List.getD_cons_zero,
                  Bool.true_eq_false] using congrFun (congrFun h a) 0
              exact hfalse.elim
          | inr q =>
              have hpq : p = q := ihr (by
                funext i k
                by_cases hi : i = a
                · subst i
                  simpa only [streamBit, stream, ite_eq_left rfl, ite_true, List.getD_cons_succ]
                    using
                    congrFun (congrFun h a) (k + 1)
                · simpa only [streamBit, stream, ite_eq_right hi] using
                    congrFun (congrFun h i) k)
              exact congrArg Sum.inr hpq

theorem padded_injective [DecidableEq Label] (t : SparseDecisionTree Label)
    (N : Label → ℕ) (hN : ∀ (p : t.Leaf) i, (t.stream p i).length ≤ N i) :
    Function.Injective (t.padded N) := by
  intro p q h
  apply t.streamBit_injective
  funext i k
  by_cases hk : k < N i
  · exact congrFun (congrFun h i) ⟨k, hk⟩
  · have hNk : N i ≤ k := Nat.le_of_not_gt hk
    change (t.stream p i).getD k false = (t.stream q i).getD k false
    rw [List.getD_eq_default _ _ ((hN p i).trans hNk),
      List.getD_eq_default _ _ ((hN q i).trans hNk)]

private theorem sum_getD_false (N : ℕ) (xs : List Bool) (h : xs.length ≤ N) :
    (∑ j : Fin N, if xs.getD j.val false = true then (1 : ℕ) else 0) =
      xs.count true := by
  induction N generalizing xs with
  | zero => cases xs <;> simp_all
  | succ N ih =>
      cases xs with
      | nil => simp
      | cons b xs =>
          have hx : xs.length ≤ N := Nat.le_of_succ_le_succ h
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ]
          rw [ih xs hx]
          cases b <;> simp [Nat.add_comm]

theorem trueCount_getD (xs : List Bool) (N : ℕ) (h : xs.length ≤ N) :
    trueCount (fun j : Fin N => xs.getD j.val false) = xs.count true := by
  unfold trueCount
  exact (Finset.natCast_card_filter (R := ℕ)
    (fun j : Fin N => xs.getD j.val false = true) Finset.univ).trans
      (sum_getD_false N xs h)

theorem padded_trueCount [DecidableEq Label] (t : SparseDecisionTree Label)
    (N : Label → ℕ) (p : t.Leaf) (i : Label)
    (h : (t.stream p i).length ≤ N i) :
    trueCount (t.padded N p i) = (t.stream p i).count true :=
  trueCount_getD (t.stream p i) (N i) h

theorem card_le_prod_admitted [DecidableEq Label] [Fintype Label]
    (t : SparseDecisionTree Label) (N : Label → ℕ)
    (hN : ∀ (p : t.Leaf) i, (t.stream p i).length ≤ N i)
    (admitted : (i : Label) → Finset (Fin (N i) → Bool))
    (hmem : ∀ (p : t.Leaf) i, t.padded N p i ∈ admitted i) :
    Fintype.card t.Leaf ≤ ∏ i, (admitted i).card := by
  classical
  let enc : t.Leaf → ((i : Label) → {w // w ∈ admitted i}) :=
    fun p i => ⟨t.padded N p i, hmem p i⟩
  have henc : Function.Injective enc := by
    intro p q h
    apply t.padded_injective N hN
    funext i
    exact congrArg Subtype.val (congrFun h i)
  simpa only [Fintype.card_pi, Fintype.card_coe] using
    (Fintype.card_le_of_injective enc henc)

theorem card_le_prod_lowWeight [DecidableEq Label] [Fintype Label]
    (t : SparseDecisionTree Label) (N r : Label → ℕ)
    (hN : ∀ (p : t.Leaf) i, (t.stream p i).length ≤ N i)
    (hones : ∀ (p : t.Leaf) i, r i * (t.stream p i).count true ≤ N i) :
    Fintype.card t.Leaf ≤
      ∏ i, (Finset.univ.filter (fun w : Fin (N i) → Bool =>
        r i * trueCount w ≤ N i)).card := by
  classical
  apply t.card_le_prod_admitted N hN
  intro p i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [t.padded_trueCount N p i (hN p i)]
  exact hones p i

end SparseDecisionTree

end DepthThreeLowerBound

end Complexity
