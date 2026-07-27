/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.DecisionTree.Block.Defs
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Complete query blocks in finite decision trees -- proof internals
-/

@[expose] public section

namespace Complexity
namespace DecisionTree.On

theorem assignmentFor_apply_of_mem_internal
    (queries : List (Fin N)) (input : BitString N)
    (index : Fin N) (hmem : index ∈ queries) :
    assignmentFor queries input index = some (input index) := by
  induction queries with
  | nil => simp at hmem
  | cons head rest ih =>
      by_cases heq : index = head
      · subst index
        simp [assignmentFor, Restriction.On.comp,
          Restriction.On.single]
      · have hrest : index ∈ rest := by
          simpa [heq] using hmem
        simp [assignmentFor, Restriction.On.comp,
          Restriction.On.single, heq, ih hrest]

theorem assignmentFor_apply_of_not_mem_internal
    (queries : List (Fin N)) (input : BitString N)
    (index : Fin N) (hmem : index ∉ queries) :
    assignmentFor queries input index = none := by
  induction queries with
  | nil => rfl
  | cons head rest ih =>
      simp only [List.mem_cons, not_or] at hmem
      simp [assignmentFor, Restriction.On.comp,
        Restriction.On.single, hmem.1, ih hmem.2]

theorem assignmentFor_applyTo_internal
    (queries : List (Fin N)) (input : BitString N) :
    (assignmentFor queries input).applyTo input = input := by
  funext index
  unfold Restriction.On.applyTo
  by_cases hmem : index ∈ queries
  · rw [assignmentFor_apply_of_mem_internal
      queries input index hmem]
    rfl
  · rw [assignmentFor_apply_of_not_mem_internal
      queries input index hmem]
    rfl

theorem assignmentFor_reapply_internal
    (queries : List (Fin N)) (input fallback : BitString N) :
    assignmentFor queries
        ((assignmentFor queries input).applyTo fallback) =
      assignmentFor queries input := by
  funext index
  by_cases hmem : index ∈ queries
  · rw [assignmentFor_apply_of_mem_internal _ _ _ hmem,
      assignmentFor_apply_of_mem_internal _ input _ hmem]
    unfold Restriction.On.applyTo
    rw [assignmentFor_apply_of_mem_internal
      _ input _ hmem]
    rfl
  · rw [assignmentFor_apply_of_not_mem_internal _ _ _ hmem,
      assignmentFor_apply_of_not_mem_internal
        _ input _ hmem]

theorem assignmentOfPath_append_internal
    (left right : List (Fin N × Bool)) :
    assignmentOfPath (left ++ right) =
      Restriction.On.comp
        (assignmentOfPath left)
        (assignmentOfPath right) := by
  induction left with
  | nil => simp [assignmentOfPath]
  | cons query left ih =>
      simp [assignmentOfPath, ih,
        Restriction.On.comp_assoc]

theorem assignmentOfPath_apply_of_not_mem_internal
    (path : List (Fin N × Bool)) (index : Fin N)
    (hindex : index ∉ path.map Prod.fst) :
    assignmentOfPath path index = none := by
  induction path with
  | nil => rfl
  | cons query path ih =>
      simp only [List.map_cons, List.mem_cons,
        not_or] at hindex
      simp [assignmentOfPath, Restriction.On.comp,
        Restriction.On.single, hindex.1, ih hindex.2]

theorem assignmentOfPath_apply_eq_some_of_mem_internal
    (path : List (Fin N × Bool))
    (hnodup : (path.map Prod.fst).Nodup)
    (index : Fin N) (hindex : index ∈ path.map Prod.fst) :
    ∃ value, assignmentOfPath path index = some value := by
  induction path with
  | nil => simp at hindex
  | cons query path ih =>
      have hparts := List.nodup_cons.mp hnodup
      simp only [List.map_cons, List.mem_cons] at hindex
      rcases hindex with hhead | htail
      · subst index
        exact ⟨query.2, by
          simp [assignmentOfPath, Restriction.On.comp,
            Restriction.On.single]⟩
      · obtain ⟨value, hvalue⟩ :=
          ih hparts.2 htail
        have hne : index ≠ query.1 := by
          intro heq
          subst index
          exact hparts.1 htail
        exact ⟨value, by
          simp [assignmentOfPath, Restriction.On.comp,
            Restriction.On.single, hne, hvalue]⟩

theorem assignmentOfPath_apply_of_mem_internal
    (path : List (Fin N × Bool))
    (hnodup : (path.map Prod.fst).Nodup)
    (query : Fin N × Bool) (hquery : query ∈ path) :
    assignmentOfPath path query.1 = some query.2 := by
  induction path with
  | nil => simp at hquery
  | cons head path ih =>
      have hparts := List.nodup_cons.mp hnodup
      simp only [List.mem_cons] at hquery
      rcases hquery with rfl | htail
      · simp [assignmentOfPath, Restriction.On.comp,
          Restriction.On.single]
      · have hne : query.1 ≠ head.1 := by
          intro heq
          apply hparts.1
          rw [List.mem_map]
          exact ⟨query, htail, heq⟩
        simp [assignmentOfPath, Restriction.On.comp,
          Restriction.On.single, hne, ih hparts.2 htail]

theorem assignmentOfPath_deepBlockPath_internal
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N) :
    assignmentOfPath
        (deepBlockPath queries continuation) =
      deepBranch queries continuation := by
  induction queries generalizing continuation with
  | nil => rfl
  | cons index rest ih =>
      let falseContinuation := fun tail => continuation
        (Restriction.On.comp
          (Restriction.On.single index false) tail)
      let trueContinuation := fun tail => continuation
        (Restriction.On.comp
          (Restriction.On.single index true) tail)
      by_cases hle :
          (queryAll rest trueContinuation).depth ≤
            (queryAll rest falseContinuation).depth
      · simp [deepBlockPath, deepBranch, assignmentOfPath,
          falseContinuation, trueContinuation, hle, ih]
      · simp [deepBlockPath, deepBranch, assignmentOfPath,
          falseContinuation, trueContinuation, hle, ih]

theorem deepPath_queryAll_internal
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N) :
    (queryAll queries continuation).deepPath =
      deepBlockPath queries continuation ++
        (continuation
          (deepBranch queries continuation)).deepPath := by
  induction queries generalizing continuation with
  | nil => rfl
  | cons index rest ih =>
      let falseContinuation := fun tail => continuation
        (Restriction.On.comp
          (Restriction.On.single index false) tail)
      let trueContinuation := fun tail => continuation
        (Restriction.On.comp
          (Restriction.On.single index true) tail)
      by_cases hle :
          (queryAll rest trueContinuation).depth ≤
            (queryAll rest falseContinuation).depth
      · simp [queryAll, deepPath, deepBlockPath,
          deepBranch, falseContinuation, trueContinuation,
          hle, ih]
      · simp [queryAll, deepPath, deepBlockPath,
          deepBranch, falseContinuation, trueContinuation,
          hle, ih]

theorem map_fst_deepBlockPath_internal
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N) :
    (deepBlockPath queries continuation).map Prod.fst =
      queries := by
  induction queries generalizing continuation with
  | nil => rfl
  | cons index rest ih =>
      let falseContinuation := fun tail => continuation
        (Restriction.On.comp
          (Restriction.On.single index false) tail)
      let trueContinuation := fun tail => continuation
        (Restriction.On.comp
          (Restriction.On.single index true) tail)
      by_cases hle :
          (queryAll rest trueContinuation).depth ≤
            (queryAll rest falseContinuation).depth
      · simp [deepBlockPath, falseContinuation,
          trueContinuation, hle, ih]
      · simp [deepBlockPath, falseContinuation,
          trueContinuation, hle, ih]

theorem deepBranch_apply_of_not_mem_internal
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N)
    (index : Fin N) (hmem : index ∉ queries) :
    deepBranch queries continuation index = none := by
  induction queries generalizing continuation with
  | nil => rfl
  | cons head rest ih =>
      simp only [List.mem_cons, not_or] at hmem
      let falseContinuation := fun tail => continuation
        (Restriction.On.comp
          (Restriction.On.single head false) tail)
      let trueContinuation := fun tail => continuation
        (Restriction.On.comp
          (Restriction.On.single head true) tail)
      by_cases hle :
          (queryAll rest trueContinuation).depth ≤
            (queryAll rest falseContinuation).depth
      · simp [deepBranch, falseContinuation,
          trueContinuation, hle, Restriction.On.comp,
          Restriction.On.single, hmem.1, ih _ hmem.2]
      · simp [deepBranch, falseContinuation,
          trueContinuation, hle, Restriction.On.comp,
          Restriction.On.single, hmem.1, ih _ hmem.2]

theorem deepBranch_apply_eq_some_of_mem_internal
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N)
    (hnodup : queries.Nodup) (index : Fin N)
    (hmem : index ∈ queries) :
    ∃ value,
      deepBranch queries continuation index = some value := by
  induction queries generalizing continuation with
  | nil => simp at hmem
  | cons head rest ih =>
      have hparts := List.nodup_cons.mp hnodup
      simp only [List.mem_cons] at hmem
      let falseContinuation := fun tail => continuation
        (Restriction.On.comp
          (Restriction.On.single head false) tail)
      let trueContinuation := fun tail => continuation
        (Restriction.On.comp
          (Restriction.On.single head true) tail)
      by_cases hle :
          (queryAll rest trueContinuation).depth ≤
            (queryAll rest falseContinuation).depth
      · rcases hmem with rfl | hrest
        · exact ⟨false, by
            simp [deepBranch, hle, falseContinuation,
              trueContinuation, Restriction.On.comp,
              Restriction.On.single]⟩
        · obtain ⟨value, hvalue⟩ :=
            ih falseContinuation hparts.2 hrest
          have hne : index ≠ head := by
            intro heq
            subst index
            exact hparts.1 hrest
          exact ⟨value, by
            simp [deepBranch, hle, falseContinuation,
              trueContinuation, Restriction.On.comp,
              Restriction.On.single, hne, hvalue]⟩
      · rcases hmem with rfl | hrest
        · exact ⟨true, by
            simp [deepBranch, hle, falseContinuation,
              trueContinuation, Restriction.On.comp,
              Restriction.On.single]⟩
        · obtain ⟨value, hvalue⟩ :=
            ih trueContinuation hparts.2 hrest
          have hne : index ≠ head := by
            intro heq
            subst index
            exact hparts.1 hrest
          exact ⟨value, by
            simp [deepBranch, hle, falseContinuation,
              trueContinuation, Restriction.On.comp,
              Restriction.On.single, hne, hvalue]⟩

theorem deepBranch_apply_of_mem_deepBlockPath_internal
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N)
    (hnodup : queries.Nodup) (query : Fin N × Bool)
    (hquery : query ∈ deepBlockPath queries continuation) :
    deepBranch queries continuation query.1 =
      some query.2 := by
  induction queries generalizing continuation with
  | nil => simp [deepBlockPath] at hquery
  | cons head rest ih =>
      have hparts := List.nodup_cons.mp hnodup
      let falseContinuation := fun tail => continuation
        (Restriction.On.comp
          (Restriction.On.single head false) tail)
      let trueContinuation := fun tail => continuation
        (Restriction.On.comp
          (Restriction.On.single head true) tail)
      by_cases hle :
          (queryAll rest trueContinuation).depth ≤
            (queryAll rest falseContinuation).depth
      · simp [deepBlockPath, falseContinuation,
          trueContinuation, hle] at hquery
        rcases hquery with rfl | hrest
        · simp [deepBranch, hle, falseContinuation,
            trueContinuation, Restriction.On.comp,
            Restriction.On.single]
        · have hvalue :=
            ih falseContinuation hparts.2 hrest
          have hmem : query.1 ∈ rest := by
            rw [← map_fst_deepBlockPath_internal
              rest falseContinuation]
            exact List.mem_map_of_mem hrest
          have hne : query.1 ≠ head := by
            intro heq
            rw [heq] at hmem
            exact hparts.1 hmem
          simpa [deepBranch, hle, falseContinuation,
            trueContinuation, Restriction.On.comp,
            Restriction.On.single, hne] using hvalue
      · simp [deepBlockPath, falseContinuation,
          trueContinuation, hle] at hquery
        rcases hquery with rfl | hrest
        · simp [deepBranch, hle, falseContinuation,
            trueContinuation, Restriction.On.comp,
            Restriction.On.single]
        · have hvalue :=
            ih trueContinuation hparts.2 hrest
          have hmem : query.1 ∈ rest := by
            rw [← map_fst_deepBlockPath_internal
              rest trueContinuation]
            exact List.mem_map_of_mem hrest
          have hne : query.1 ≠ head := by
            intro heq
            rw [heq] at hmem
            exact hparts.1 hmem
          simpa [deepBranch, hle, falseContinuation,
            trueContinuation, Restriction.On.comp,
            Restriction.On.single, hne] using hvalue

theorem assignmentFor_deepBranch_internal
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N)
    (hnodup : queries.Nodup) (fallback : BitString N) :
    assignmentFor queries
        ((deepBranch queries continuation).applyTo fallback) =
      deepBranch queries continuation := by
  funext index
  by_cases hmem : index ∈ queries
  · rw [assignmentFor_apply_of_mem_internal
      queries _ index hmem]
    obtain ⟨value, hvalue⟩ :=
      deepBranch_apply_eq_some_of_mem_internal
        queries continuation hnodup index hmem
    unfold Restriction.On.applyTo
    rw [hvalue]
    rfl
  · rw [assignmentFor_apply_of_not_mem_internal
      queries _ index hmem]
    exact (deepBranch_apply_of_not_mem_internal
      queries continuation index hmem).symm

theorem eval_queryAll_internal
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N)
    (input : BitString N) :
    (queryAll queries continuation).eval input =
      (continuation (assignmentFor queries input)).eval input := by
  induction queries generalizing continuation with
  | nil => rfl
  | cons index rest ih =>
      cases hvalue : input index
      · simp only [queryAll, DecisionTree.On.eval, hvalue,
          Bool.false_eq_true, ↓reduceIte, assignmentFor]
        exact ih _
      · simp only [queryAll, DecisionTree.On.eval, hvalue,
          ↓reduceIte, assignmentFor]
        exact ih _

theorem depth_queryAll_le_internal
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N)
    (continuationDepth : ℕ)
    (hdepth : ∀ restriction,
      (continuation restriction).depth ≤ continuationDepth) :
    (queryAll queries continuation).depth ≤
      queries.length + continuationDepth := by
  induction queries generalizing continuation with
  | nil =>
      simpa [queryAll] using hdepth Restriction.On.empty
  | cons index rest ih =>
      simp only [queryAll, DecisionTree.On.depth,
        List.length_cons]
      have hfalse := ih
        (fun tail => continuation
          (Restriction.On.comp
            (Restriction.On.single index false) tail))
        (fun restriction => hdepth _)
      have htrue := ih
        (fun tail => continuation
          (Restriction.On.comp
            (Restriction.On.single index true) tail))
        (fun restriction => hdepth _)
      omega

theorem vars_queryAll_subset_internal
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N)
    (support : Finset (Fin N))
    (hvars : ∀ restriction,
      (continuation restriction).vars ⊆ support) :
    (queryAll queries continuation).vars ⊆
      queries.toFinset ∪ support := by
  induction queries generalizing continuation with
  | nil =>
      simpa [queryAll] using hvars Restriction.On.empty
  | cons index rest ih =>
      have hfalse := ih
        (fun tail => continuation
          (Restriction.On.comp
            (Restriction.On.single index false) tail))
        (fun restriction => hvars _)
      have htrue := ih
        (fun tail => continuation
          (Restriction.On.comp
            (Restriction.On.single index true) tail))
        (fun restriction => hvars _)
      simpa [queryAll, DecisionTree.On.vars] using
        Finset.insert_subset_insert index
          (Finset.union_subset_union hfalse htrue)

theorem pathReadOnce_queryAll_internal
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N)
    (hnodup : queries.Nodup)
    (hreadOnce : ∀ restriction,
      (continuation restriction).PathReadOnce)
    (hdisjoint : ∀ restriction,
      Disjoint queries.toFinset (continuation restriction).vars) :
    (queryAll queries continuation).PathReadOnce := by
  induction queries generalizing continuation with
  | nil =>
      simpa [queryAll] using
        hreadOnce Restriction.On.empty
  | cons index rest ih =>
      have hnodupParts := List.nodup_cons.mp hnodup
      let falseContinuation := fun tail => continuation
        (Restriction.On.comp
          (Restriction.On.single index false) tail)
      let trueContinuation := fun tail => continuation
        (Restriction.On.comp
          (Restriction.On.single index true) tail)
      have restDisjointFalse : ∀ restriction,
          Disjoint rest.toFinset
            (falseContinuation restriction).vars := by
        intro restriction
        rw [Finset.disjoint_left]
        intro queried hrest hcontinuation
        exact (Finset.disjoint_left.mp (hdisjoint _) (by
          simp [hrest])) hcontinuation
      have restDisjointTrue : ∀ restriction,
          Disjoint rest.toFinset
            (trueContinuation restriction).vars := by
        intro restriction
        rw [Finset.disjoint_left]
        intro queried hrest hcontinuation
        exact (Finset.disjoint_left.mp (hdisjoint _) (by
          simp [hrest])) hcontinuation
      have hfalseRead := ih falseContinuation
        hnodupParts.2 (fun restriction => hreadOnce _)
        restDisjointFalse
      have htrueRead := ih trueContinuation
        hnodupParts.2 (fun restriction => hreadOnce _)
        restDisjointTrue
      have continuationAvoidsIndex : ∀ restriction,
          (continuation restriction).vars ⊆
            Finset.univ.erase index := by
        intro restriction queried hqueried
        simp only [Finset.mem_erase, Finset.mem_univ,
          and_true]
        intro hequal
        subst queried
        exact (Finset.disjoint_left.mp
          (hdisjoint restriction) (by simp)) hqueried
      have hfalseVars := vars_queryAll_subset_internal
        rest falseContinuation (Finset.univ.erase index)
        (fun restriction => continuationAvoidsIndex _)
      have htrueVars := vars_queryAll_subset_internal
        rest trueContinuation (Finset.univ.erase index)
        (fun restriction => continuationAvoidsIndex _)
      simp only [queryAll, PathReadOnce]
      refine ⟨?_, ?_, hfalseRead, htrueRead⟩
      · intro hmem
        rcases Finset.mem_union.mp (hfalseVars hmem) with
          hrest | hcontinuation
        · exact hnodupParts.1 (by simpa using hrest)
        · exact (Finset.mem_erase.mp hcontinuation).1 rfl
      · intro hmem
        rcases Finset.mem_union.mp (htrueVars hmem) with
          hrest | hcontinuation
        · exact hnodupParts.1 (by simpa using hrest)
        · exact (Finset.mem_erase.mp hcontinuation).1 rfl

end DecisionTree.On
end Complexity
