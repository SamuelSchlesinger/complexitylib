/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.DecisionTree.Finite.Internal
public import Complexitylib.Circuits.DecisionTree.NormalForm.Defs
public import Complexitylib.Circuits.NormalForm.Operations.Internal
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Compiling finite decision trees to CNF and DNF -- proof internals
-/

@[expose] public section

namespace Complexity
namespace DecisionTree.On

private theorem any_comp_cons_literal
    (literal : Literal N)
    (terms : List (List (Literal N)))
    (input : BitString N) :
    terms.any
        ((fun term =>
          term.all fun found => found.eval input) ∘
          fun term => literal :: term) =
      (literal.eval input &&
        terms.any fun term =>
          term.all fun found => found.eval input) := by
  induction terms with
  | nil => simp
  | cons term terms ih =>
      simp only [List.any_cons, Function.comp_apply,
        List.all_cons, ih]
      cases literal.eval input <;>
        cases term.all (fun found => found.eval input) <;>
        cases terms.any (fun found =>
          found.all fun inner => inner.eval input) <;> rfl

theorem eval_toDNF_internal
    (tree : DecisionTree.On N) (input : BitString N) :
    tree.toDNF.eval input = tree.eval input := by
  induction tree with
  | leaf value => cases value <;> rfl
  | node index ifFalse ifTrue ihFalse ihTrue =>
      simp only [toDNF, DNF.eval, toDNFTerms,
        List.any_append, List.any_map]
      rw [any_comp_cons_literal,
        any_comp_cons_literal]
      change
        ((Literal.eval
              { var := index, polarity := false } input &&
            ifFalse.toDNF.eval input) ||
          (Literal.eval
              { var := index, polarity := true } input &&
            ifTrue.toDNF.eval input)) =
          DecisionTree.On.eval input
            (.node index ifFalse ifTrue)
      rw [ihFalse, ihTrue]
      cases hinput : input index <;>
        simp [Literal.eval, DecisionTree.On.eval, hinput]

theorem eval_toCNF_internal
    (tree : DecisionTree.On N) (input : BitString N) :
    tree.toCNF.eval input = tree.eval input := by
  rw [toCNF, DNF.eval_neg, eval_toDNF_internal,
    eval_neg_internal]
  simp

private theorem length_le_depth_toDNFTerms
    (tree : DecisionTree.On N)
    (term : List (Literal N))
    (hterm : term ∈ tree.toDNFTerms) :
    term.length ≤ tree.depth := by
  induction tree generalizing term with
  | leaf value =>
      cases value with
      | false => simp [toDNFTerms] at hterm
      | true =>
          simp only [toDNFTerms, List.mem_singleton] at hterm
          subst term
          rfl
  | node index ifFalse ifTrue ihFalse ihTrue =>
      simp only [toDNFTerms, List.mem_append,
        List.mem_map] at hterm
      simp only [DecisionTree.On.depth]
      rcases hterm with hterm | hterm
      · obtain ⟨tail, htail, rfl⟩ := hterm
        exact Nat.succ_le_succ
          ((ihFalse tail htail).trans
            (le_max_left _ _))
      · obtain ⟨tail, htail, rfl⟩ := hterm
        exact Nat.succ_le_succ
          ((ihTrue tail htail).trans
            (le_max_right _ _))

theorem width_toDNF_le_depth_internal
    (tree : DecisionTree.On N) :
    tree.toDNF.width ≤ tree.depth := by
  rw [DNF.width_le_iff]
  intro term hterm
  exact length_le_depth_toDNFTerms tree term hterm

theorem width_toCNF_le_depth_internal
    (tree : DecisionTree.On N) :
    tree.toCNF.width ≤ tree.depth := by
  have hbound := width_toDNF_le_depth_internal tree.neg
  rw [depth_neg_internal] at hbound
  simpa only [toCNF, DNF.width_neg] using hbound

private theorem length_toDNFTerms_le_numLeaves
    (tree : DecisionTree.On N) :
    tree.toDNFTerms.length ≤ tree.numLeaves := by
  induction tree with
  | leaf value =>
      cases value <;> simp [toDNFTerms, numLeaves]
  | node index ifFalse ifTrue ihFalse ihTrue =>
      simp only [toDNFTerms, List.length_append,
        List.length_map, numLeaves]
      omega

theorem complexity_toDNF_le_numLeaves_internal
    (tree : DecisionTree.On N) :
    tree.toDNF.complexity ≤ tree.numLeaves :=
  length_toDNFTerms_le_numLeaves tree

theorem complexity_toCNF_le_numLeaves_internal
    (tree : DecisionTree.On N) :
    tree.toCNF.complexity ≤ tree.numLeaves := by
  have hbound :=
    complexity_toDNF_le_numLeaves_internal tree.neg
  rw [numLeaves_neg_internal] at hbound
  simpa only [toCNF, DNF.complexity_neg] using hbound

theorem complexity_toDNF_le_two_pow_depth_internal
    (tree : DecisionTree.On N) :
    tree.toDNF.complexity ≤ 2 ^ tree.depth :=
  (complexity_toDNF_le_numLeaves_internal tree).trans
    (numLeaves_le_two_pow_depth_internal tree)

theorem complexity_toCNF_le_two_pow_depth_internal
    (tree : DecisionTree.On N) :
    tree.toCNF.complexity ≤ 2 ^ tree.depth :=
  (complexity_toCNF_le_numLeaves_internal tree).trans
    (numLeaves_le_two_pow_depth_internal tree)

theorem eval_anyDNF_internal
    (trees : List (DecisionTree.On N))
    (input : BitString N) :
    (anyDNF trees).eval input =
      trees.any fun tree => tree.eval input := by
  rw [anyDNF, DNF.eval_disjoin_internal,
    List.any_map]
  apply congrArg (fun predicate =>
    trees.any predicate)
  funext tree
  exact eval_toDNF_internal tree input

theorem eval_allCNF_internal
    (trees : List (DecisionTree.On N))
    (input : BitString N) :
    (allCNF trees).eval input =
      trees.all fun tree => tree.eval input := by
  rw [allCNF, CNF.eval_conjoin_internal,
    List.all_map]
  apply congrArg (fun predicate =>
    trees.all predicate)
  funext tree
  exact eval_toCNF_internal tree input

theorem width_anyDNF_le_internal
    (trees : List (DecisionTree.On N)) (bound : ℕ)
    (hbound :
      ∀ tree ∈ trees, tree.depth ≤ bound) :
    (anyDNF trees).width ≤ bound := by
  apply DNF.width_disjoin_le_internal
  intro formula hformula
  rw [List.mem_map] at hformula
  obtain ⟨tree, htree, rfl⟩ := hformula
  exact (width_toDNF_le_depth_internal tree).trans
    (hbound tree htree)

theorem width_allCNF_le_internal
    (trees : List (DecisionTree.On N)) (bound : ℕ)
    (hbound :
      ∀ tree ∈ trees, tree.depth ≤ bound) :
    (allCNF trees).width ≤ bound := by
  apply CNF.width_conjoin_le_internal
  intro formula hformula
  rw [List.mem_map] at hformula
  obtain ⟨tree, htree, rfl⟩ := hformula
  exact (width_toCNF_le_depth_internal tree).trans
    (hbound tree htree)

theorem complexity_anyDNF_le_internal
    (trees : List (DecisionTree.On N)) (bound : ℕ)
    (hbound :
      ∀ tree ∈ trees, tree.depth ≤ bound) :
    (anyDNF trees).complexity ≤
      trees.length * 2 ^ bound := by
  rw [anyDNF, DNF.complexity_disjoin_internal]
  induction trees with
  | nil => simp
  | cons tree trees ih =>
      simp only [List.map_cons, List.sum_cons,
        List.length_cons]
      have htreeDepth := hbound tree (by simp)
      have htree :
          tree.toDNF.complexity ≤ 2 ^ bound :=
        (complexity_toDNF_le_two_pow_depth_internal tree).trans
          (Nat.pow_le_pow_right (by omega) htreeDepth)
      have htail :
          ((List.map toDNF trees).map DNF.complexity).sum ≤
            trees.length * 2 ^ bound := by
        apply ih
        intro found hfound
        exact hbound found (by simp [hfound])
      simp only [Nat.succ_mul]
      omega

theorem complexity_allCNF_le_internal
    (trees : List (DecisionTree.On N)) (bound : ℕ)
    (hbound :
      ∀ tree ∈ trees, tree.depth ≤ bound) :
    (allCNF trees).complexity ≤
      trees.length * 2 ^ bound := by
  rw [allCNF, CNF.complexity_conjoin_internal]
  induction trees with
  | nil => simp
  | cons tree trees ih =>
      simp only [List.map_cons, List.sum_cons,
        List.length_cons]
      have htreeDepth := hbound tree (by simp)
      have htree :
          tree.toCNF.complexity ≤ 2 ^ bound :=
        (complexity_toCNF_le_two_pow_depth_internal tree).trans
          (Nat.pow_le_pow_right (by omega) htreeDepth)
      have htail :
          ((List.map toCNF trees).map CNF.complexity).sum ≤
            trees.length * 2 ^ bound := by
        apply ih
        intro found hfound
        exact hbound found (by simp [hfound])
      simp only [Nat.succ_mul]
      omega

end DecisionTree.On
end Complexity
