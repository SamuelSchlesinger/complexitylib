/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.DecisionTree.Path.Defs
public import Complexitylib.Circuits.DecisionTree.Finite.Internal
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Canonical deepest paths in finite decision trees -- proof internals
-/

@[expose] public section

namespace Complexity
namespace DecisionTree.On

theorem pathReadOnce_neg_internal (tree : DecisionTree.On N) :
    tree.neg.PathReadOnce ↔ tree.PathReadOnce := by
  induction tree with
  | leaf value => rfl
  | node index ifFalse ifTrue ihFalse ihTrue =>
      simp [neg, PathReadOnce, vars_neg_internal,
        ihFalse, ihTrue]

theorem length_deepPath_internal (tree : DecisionTree.On N) :
    tree.deepPath.length = tree.depth := by
  induction tree with
  | leaf value => rfl
  | node index ifFalse ifTrue ihFalse ihTrue =>
      by_cases hle : ifTrue.depth ≤ ifFalse.depth
      · simp [deepPath, depth, hle, ihFalse]
      · have hreverse : ifFalse.depth ≤ ifTrue.depth := by
          omega
        simp [deepPath, depth, hle, ihTrue, hreverse]

theorem mem_vars_of_mem_deepPath_internal
    (tree : DecisionTree.On N) (query : Fin N × Bool)
    (hquery : query ∈ tree.deepPath) :
    query.1 ∈ tree.vars := by
  induction tree with
  | leaf value => simp [deepPath] at hquery
  | node index ifFalse ifTrue ihFalse ihTrue =>
      by_cases hle : ifTrue.depth ≤ ifFalse.depth
      · simp only [deepPath, hle, ↓reduceIte,
          List.mem_cons] at hquery
        rcases hquery with hhead | htail
        · rw [hhead]
          simp [vars]
        · exact Finset.mem_insert_of_mem
            (Finset.mem_union_left _ (ihFalse htail))
      · simp only [deepPath, hle, ↓reduceIte,
          List.mem_cons] at hquery
        rcases hquery with hhead | htail
        · rw [hhead]
          simp [vars]
        · exact Finset.mem_insert_of_mem
            (Finset.mem_union_right _ (ihTrue htail))

theorem nodup_deepPathVars_internal
    (tree : DecisionTree.On N) (readOnce : tree.PathReadOnce) :
    tree.deepPathVars.Nodup := by
  induction tree with
  | leaf value => simp [deepPathVars, deepPath]
  | node index ifFalse ifTrue ihFalse ihTrue =>
      simp only [PathReadOnce] at readOnce
      by_cases hle : ifTrue.depth ≤ ifFalse.depth
      · simp only [deepPathVars, deepPath, hle, ↓reduceIte,
          List.map_cons]
        apply List.nodup_cons.mpr
        constructor
        · intro hmem
          rw [List.mem_map] at hmem
          obtain ⟨query, hquery, hfst⟩ := hmem
          exact readOnce.1
            (hfst ▸ mem_vars_of_mem_deepPath_internal
              ifFalse query hquery)
        · exact ihFalse readOnce.2.2.1
      · simp only [deepPathVars, deepPath, hle, ↓reduceIte,
          List.map_cons]
        apply List.nodup_cons.mpr
        constructor
        · intro hmem
          rw [List.mem_map] at hmem
          obtain ⟨query, hquery, hfst⟩ := hmem
          exact readOnce.2.1
            (hfst ▸ mem_vars_of_mem_deepPath_internal
              ifTrue query hquery)
        · exact ihTrue readOnce.2.2.2

theorem depth_le_card_vars_of_pathReadOnce_internal
    (tree : DecisionTree.On N) (readOnce : tree.PathReadOnce) :
    tree.depth ≤ tree.vars.card := by
  induction tree with
  | leaf value =>
      simp [DecisionTree.On.depth,
        DecisionTree.On.vars]
  | node index ifFalse ifTrue ihFalse ihTrue =>
      simp only [PathReadOnce] at readOnce
      have hfalse := ihFalse readOnce.2.2.1
      have htrue := ihTrue readOnce.2.2.2
      simp only [DecisionTree.On.depth,
        DecisionTree.On.vars]
      rw [Finset.card_insert_of_notMem]
      · have hfalseCard :
            ifFalse.vars.card ≤
              (ifFalse.vars ∪ ifTrue.vars).card :=
          Finset.card_le_card Finset.subset_union_left
        have htrueCard :
            ifTrue.vars.card ≤
              (ifFalse.vars ∪ ifTrue.vars).card :=
          Finset.card_le_card Finset.subset_union_right
        omega
      · simp only [Finset.mem_union, not_or]
        exact ⟨readOnce.1, readOnce.2.1⟩

/-- The first `queryCount` query indices on a deep path, packaged as an
embedding when the whole tree is path-read-once. -/
noncomputable def deepPrefixEmbeddingInternal
    (tree : DecisionTree.On N) (queryCount : ℕ)
    (hdepth : queryCount ≤ tree.depth)
    (readOnce : tree.PathReadOnce) :
    Fin queryCount ↪ Fin N where
  toFun position :=
    tree.deepPathVars.get
      (Fin.castLE (by
        simpa [deepPathVars, length_deepPath_internal] using hdepth)
        position)
  inj' := by
    intro left right hequal
    apply Fin.ext
    have hnodup :=
      nodup_deepPathVars_internal tree readOnce
    have hget :=
      (List.Nodup.get_inj_iff hnodup).mp hequal
    exact congrArg
      (fun index : Fin tree.deepPathVars.length => index.val) hget

/-- Branch bit at each of the first `queryCount` positions of the chosen deep
path. -/
noncomputable def deepPrefixValuesInternal
    (tree : DecisionTree.On N) (queryCount : ℕ)
    (hdepth : queryCount ≤ tree.depth) :
    Fin queryCount → Bool :=
  fun position =>
    (tree.deepPath.get
      (Fin.castLE (by
        simpa [length_deepPath_internal] using hdepth)
        position)).2

theorem deepPrefixEmbedding_mem_vars_internal
    (tree : DecisionTree.On N) (queryCount : ℕ)
    (hdepth : queryCount ≤ tree.depth)
    (readOnce : tree.PathReadOnce) (position : Fin queryCount) :
    deepPrefixEmbeddingInternal tree queryCount hdepth readOnce position ∈
      tree.vars := by
  have hmem :
      deepPrefixEmbeddingInternal tree queryCount hdepth readOnce position ∈
        tree.deepPathVars := by
    unfold deepPrefixEmbeddingInternal
    exact List.get_mem _ _
  rw [deepPathVars, List.mem_map] at hmem
  obtain ⟨query, hquery, hfst⟩ := hmem
  exact hfst ▸
    mem_vars_of_mem_deepPath_internal tree query hquery

end DecisionTree.On
end Complexity
