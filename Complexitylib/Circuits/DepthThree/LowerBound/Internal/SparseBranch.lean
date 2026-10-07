/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.SparseCounting
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Sunflower

/-!
# Unrestricted depth-three lower bound: sparse branch

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/SparseBranch.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

noncomputable section

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [instDecidableEqV : DecidableEq V]

/-- Insert a batch of clauses and remove clauses it subsumes. -/
def sparseBatchUpdate (A B : Finset (Clause V)) : Finset (Clause V) := by
  classical
  exact B ∪ A.filter (fun C => ¬ ∃ D ∈ B, D ⊆ C)

@[simp] theorem mem_sparseBatchUpdate {A B : Finset (Clause V)} {C : Clause V} :
    C ∈ sparseBatchUpdate A B ↔ C ∈ B ∨ (C ∈ A ∧ ¬ ∃ D ∈ B, D ⊆ C) := by
  classical
  simp only [sparseBatchUpdate, Finset.mem_union, Finset.mem_filter]

theorem batch_subset_sparseBatchUpdate (A B : Finset (Clause V)) :
    B ⊆ sparseBatchUpdate A B := fun _ h => mem_sparseBatchUpdate.mpr (Or.inl h)

theorem sparseBatchUpdate_subset_union (A B : Finset (Clause V)) :
    sparseBatchUpdate A B ⊆ B ∪ A := by
  classical
  intro C hC
  rcases mem_sparseBatchUpdate.mp hC with hB | ⟨hA, _⟩
  · exact Finset.mem_union.mpr (Or.inl hB)
  · exact Finset.mem_union.mpr (Or.inr hA)

theorem sparseBatchUpdate_mono_left {A A' B : Finset (Clause V)} (h : A ⊆ A') :
    sparseBatchUpdate A B ⊆ sparseBatchUpdate A' B := by
  intro C hC
  rcases mem_sparseBatchUpdate.mp hC with hB | ⟨hA, hn⟩
  · exact mem_sparseBatchUpdate.mpr (Or.inl hB)
  · exact mem_sparseBatchUpdate.mpr (Or.inr ⟨h hA, hn⟩)

theorem sparseBatchUpdate_dominates (A B : Finset (Clause V)) {C : Clause V}
    (hC : C ∈ A) : ∃ D ∈ sparseBatchUpdate A B, D ⊆ C := by
  classical
  by_cases h : ∃ D ∈ B, D ⊆ C
  · obtain ⟨D, hD, hDC⟩ := h
    exact ⟨D, batch_subset_sparseBatchUpdate A B hD, hDC⟩
  · exact ⟨C, mem_sparseBatchUpdate.mpr (Or.inr ⟨hC, h⟩), Finset.Subset.refl _⟩

theorem sparseBatchUpdate_satisfies (A B : Finset (Clause V)) (x : Cube V) :
    (∀ C ∈ sparseBatchUpdate A B, C.eval x = true) ↔
      (∀ C ∈ A, C.eval x = true) ∧ (∀ D ∈ B, D.eval x = true) := by
  classical
  constructor
  · intro h
    refine ⟨?_, fun D hD => h D (batch_subset_sparseBatchUpdate A B hD)⟩
    intro C hC
    obtain ⟨D, hD, hDC⟩ := sparseBatchUpdate_dominates A B hC
    exact Clause.eval_mono hDC (h D hD)
  · rintro ⟨hA, hB⟩ C hC
    rcases mem_sparseBatchUpdate.mp hC with hC | ⟨hC, _⟩
    · exact hB C hC
    · exact hA C hC

private theorem bool_eq_of_true_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Active clauses together with the clauses introduced by sparsification. -/
structure SparseState (V : Type uDepth2) where
  /-- The currently active clauses. -/
  active : Finset (Clause V)
  /-- Side clauses accumulated during branching. -/
  side : Finset (Literal V)
  /-- Clauses introduced by the sparsification process. -/
  added : Finset (Clause V)

namespace SparseState

/-- Read the active clause family as a CNF. -/
def toCNF (s : SparseState V) : CNF V :=
  s.active.toList ++ s.side.toList.map (fun l => {l})

/-- Evaluate the CNF represented by a sparsification state. -/
def eval (s : SparseState V) (x : Cube V) : Bool := s.toCNF.eval x

/-- The normalization, width, and containment invariants of a sparsification state. -/
structure Valid (s : SparseState V) (b : ℕ) : Prop where
  normalized : ∀ C ∈ s.active, C.Normalized
  nonempty : ∀ C ∈ s.active, C.Nonempty
  antichain : ∀ C ∈ s.active, ∀ D ∈ s.active, C ⊆ D → C = D
  width_le : ∀ C ∈ s.active, C.width ≤ b
  added_subset : s.added ⊆ s.active

omit [DecidableEq V] in
@[simp] theorem eval_eq_true
    {V : Type uDepth1}

    (s : SparseState V) (x : Cube V) :
    s.eval x = true ↔
      (∀ C ∈ s.active, C.eval x = true) ∧ (∀ l ∈ s.side, l.eval x = true) := by
  classical
  classical
  change CNF.eval (s.active.toList ++ s.side.toList.map (fun l => ({l} : Clause V))) x = true ↔ _
  rw [CNF.eval_eq_true]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro C hC
      exact h C (List.mem_append.mpr (Or.inl (Finset.mem_toList.mpr hC)))
    · intro l hl
      have hunit := h {l} (List.mem_append.mpr (Or.inr
        (List.mem_map.mpr ⟨l, Finset.mem_toList.mpr hl, rfl⟩)))
      simpa only [Clause.eval_singleton] using hunit
  · rintro ⟨hA, hS⟩ C hC
    rcases List.mem_append.mp hC with hC | hC
    · exact hA C (Finset.mem_toList.mp hC)
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hC
      simpa only [Clause.eval_singleton] using hS l (Finset.mem_toList.mp hl)
/-- Update both active and introduced clauses with an insertion batch. -/
def batchUpdate (s : SparseState V) (B : Finset (Clause V)) : SparseState V where
  active := sparseBatchUpdate s.active B
  side := s.side
  added := sparseBatchUpdate s.added B

@[simp] theorem batchUpdate_active (s : SparseState V) (B : Finset (Clause V)) :
    (s.batchUpdate B).active = sparseBatchUpdate s.active B := rfl

@[simp] theorem batchUpdate_side (s : SparseState V) (B : Finset (Clause V)) :
    (s.batchUpdate B).side = s.side := rfl

@[simp] theorem batchUpdate_added (s : SparseState V) (B : Finset (Clause V)) :
    (s.batchUpdate B).added = sparseBatchUpdate s.added B := rfl

theorem eval_batchUpdate_eq_true (s : SparseState V) (B : Finset (Clause V))
    (x : Cube V) :
    (s.batchUpdate B).eval x = true ↔ s.eval x = true ∧ ∀ C ∈ B, C.eval x = true := by
  rw [eval_eq_true, eval_eq_true]
  change ((∀ C ∈ sparseBatchUpdate s.active B, C.eval x = true) ∧
      (∀ l ∈ s.side, l.eval x = true)) ↔ _
  rw [sparseBatchUpdate_satisfies]
  constructor
  · rintro ⟨⟨hA, hB⟩, hS⟩
    exact ⟨⟨hA, hS⟩, hB⟩
  · rintro ⟨⟨hA, hS⟩, hB⟩
    exact ⟨⟨hA, hB⟩, hS⟩

end SparseState

/-- A uniform batch of fresh clauses used in a sparsification step. -/
structure InsertionBatch (s : SparseState V) (i : ℕ) where
  /-- The clauses inserted by this batch. -/
  clauses : Finset (Clause V)
  /-- The common size of the selected clauses. -/
  size : ℕ
  nonempty : clauses.Nonempty
  size_pos : 0 < size
  size_lt : size < i
  uniform : ∀ D ∈ clauses, D.card = size
  subclause : ∀ D ∈ clauses, ∃ A ∈ s.active, D ⊂ A
  pairwise_disjoint : ∀ D ∈ clauses, ∀ E ∈ clauses, D ≠ E → Disjoint D E

namespace InsertionBatch

variable {s : SparseState V} {i b : ℕ}

omit [DecidableEq V] in
theorem clause_nonempty
    {V : Type uDepth1}

    {s : DepthThreeLowerBound.SparseState V}
    {i : ℕ}
    (B : InsertionBatch s i) (D : Clause V)
    (hD : D ∈ B.clauses) : D.Nonempty :=
  Finset.card_pos.mp (by rw [B.uniform D hD]; exact B.size_pos)
theorem antichain (B : InsertionBatch s i) :
    ∀ D ∈ B.clauses, ∀ E ∈ B.clauses, D ⊆ E → D = E := by
  classical
  intro D hD E hE hDE
  by_contra hne
  obtain ⟨l, hl⟩ := B.clause_nonempty D hD
  exact Finset.disjoint_left.mp (B.pairwise_disjoint D hD E hE hne) hl (hDE hl)

omit [DecidableEq V] in
theorem fresh
    {V : Type uDepth1}

    {s : DepthThreeLowerBound.SparseState V}
    {i : ℕ}
    {b : ℕ}
    (B : InsertionBatch s i) (hs : s.Valid b) :
    ∀ D ∈ B.clauses, ∀ A ∈ s.active, ¬ A ⊆ D := by
  classical
  intro D hD A hA hAD
  obtain ⟨E, hE, hDE⟩ := B.subclause D hD
  have hAE : A = E := hs.antichain A hA E hE (hAD.trans hDE.1)
  apply hDE.2
  simpa only [hAE] using hAD
omit instDecidableEqV in
theorem not_mem_active (B : InsertionBatch s i) (hs : s.Valid b)
    {D : Clause V} (hD : D ∈ B.clauses) : D ∉ s.active :=
  fun hA => B.fresh hs D hD D hA (Finset.Subset.refl _)

omit instDecidableEqV in
theorem disjoint_active (B : InsertionBatch s i) (hs : s.Valid b) :
    Disjoint s.active B.clauses := by
  classical
  exact Finset.disjoint_left.mpr (fun D hA hB => B.not_mem_active hs hB hA)

omit instDecidableEqV in
theorem disjoint_added (B : InsertionBatch s i) (hs : s.Valid b) :
    Disjoint s.added B.clauses := by
  classical
  exact Finset.disjoint_left.mpr
    (fun D hA hB => B.not_mem_active hs hB (hs.added_subset hA))

theorem removed_strict (B : InsertionBatch s i) (hs : s.Valid b)
    {C : Clause V} (hC : C ∈ s.active)
    (hnot : C ∉ sparseBatchUpdate s.active B.clauses) :
    ∃ D ∈ B.clauses, D ⊂ C := by
  classical
  have hex : ∃ D ∈ B.clauses, D ⊆ C := by
    by_contra hnone
    exact hnot (mem_sparseBatchUpdate.mpr (Or.inr ⟨hC, hnone⟩))
  obtain ⟨D, hD, hDC⟩ := hex
  exact ⟨D, hD, hDC, B.fresh hs D hD C hC⟩

omit [DecidableEq V] in
theorem normalized
    {V : Type uDepth1}

    {s : DepthThreeLowerBound.SparseState V}
    {i : ℕ}
    {b : ℕ}
    (B : InsertionBatch s i) (hs : s.Valid b)
    {D : Clause V} (hD : D ∈ B.clauses) : D.Normalized := by
  classical
  obtain ⟨A, hA, hDA⟩ := B.subclause D hD
  exact (hs.normalized A hA).subset hDA.1
omit [DecidableEq V] in
theorem width_le
    {V : Type uDepth1}

    {s : DepthThreeLowerBound.SparseState V}
    {i : ℕ}
    {b : ℕ}
    (B : InsertionBatch s i) (hs : s.Valid b)
    {D : Clause V} (hD : D ∈ B.clauses) : D.width ≤ b := by
  classical
  obtain ⟨A, hA, hDA⟩ := B.subclause D hD
  exact (Clause.width_mono hDA.1).trans (hs.width_le A hA)
theorem valid_batchUpdate (B : InsertionBatch s i) (hs : s.Valid b) :
    (s.batchUpdate B.clauses).Valid b := by
  classical
  refine ⟨?_, ?_, ?_, ?_, sparseBatchUpdate_mono_left hs.added_subset⟩
  · intro C hC
    rcases mem_sparseBatchUpdate.mp hC with hB | ⟨hA, _⟩
    · exact B.normalized hs hB
    · exact hs.normalized C hA
  · intro C hC
    rcases mem_sparseBatchUpdate.mp hC with hB | ⟨hA, _⟩
    · exact B.clause_nonempty C hB
    · exact hs.nonempty C hA
  · intro C hC D hD hCD
    rcases mem_sparseBatchUpdate.mp hC with hCB | ⟨hCA, hCnot⟩
    · rcases mem_sparseBatchUpdate.mp hD with hDB | ⟨hDA, hDnot⟩
      · exact B.antichain C hCB D hDB hCD
      · exact (hDnot ⟨C, hCB, hCD⟩).elim
    · rcases mem_sparseBatchUpdate.mp hD with hDB | ⟨hDA, hDnot⟩
      · exact (B.fresh hs D hDB C hCA hCD).elim
      · exact hs.antichain C hCA D hDA hCD
  · intro C hC
    rcases mem_sparseBatchUpdate.mp hC with hB | ⟨hA, _⟩
    · exact B.width_le hs hB
    · exact hs.width_le C hA

theorem literal_occurrences_le_one (B : InsertionBatch s i) (u : ℕ)
    (l : Literal V) : literalOccurrences B.clauses u l ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro D hD E hE
  obtain ⟨hDsize, hlD⟩ := Finset.mem_filter.mp hD
  obtain ⟨hEsize, hlE⟩ := Finset.mem_filter.mp hE
  have hDB := (mem_clausesOfSize.mp hDsize).1
  have hEB := (mem_clausesOfSize.mp hEsize).1
  by_contra hne
  exact Finset.disjoint_left.mp (B.pairwise_disjoint D hDB E hEB hne) hlD hlE

@[simp] theorem added_eq (B : InsertionBatch s i) :
    (s.batchUpdate B.clauses).added = sparseBatchUpdate s.added B.clauses := rfl

end InsertionBatch

section SignedSunflower

/-- A uniform signed-clause sunflower selected from the active family. -/
structure SignedSunflower (s : SparseState V) (i r : ℕ) where
  /-- The selected family of sunflower clauses. -/
  family : Finset (Clause V)
  /-- The common intersection of the sunflower. -/
  core : Clause V
  subset_active : family ⊆ s.active
  card_family : family.card = r
  two_le : 2 ≤ r
  uniform : ∀ A ∈ family, A.card = i
  core_nonempty : core.Nonempty
  sunflower : Sunflower family core

namespace SignedSunflower

variable {s : SparseState V} {i r b : ℕ}

theorem card_family_ge_two (f : SignedSunflower s i r) : 2 ≤ f.family.card := by
  rw [f.card_family]
  exact f.two_le

theorem family_nonempty (f : SignedSunflower s i r) : f.family.Nonempty :=
  Finset.card_pos.mp (by have := f.card_family_ge_two; omega)

theorem size_ge_two (f : SignedSunflower s i r) : 2 ≤ i := by
  have hc := Finset.card_pos.mpr f.core_nonempty
  have hi := f.sunflower.core_card_lt f.card_family_ge_two f.uniform
  omega

theorem size_le (f : SignedSunflower s i r) (hs : s.Valid b) : i ≤ b := by
  obtain ⟨A, hA⟩ := f.family_nonempty
  rw [← f.uniform A hA, (hs.normalized A (f.subset_active hA)).card_eq_width]
  exact hs.width_le A (f.subset_active hA)

/-- The sunflower clauses with their common core removed. -/
def petals (f : SignedSunflower s i r) : Finset (Clause V) :=
  f.family.image (fun A => A \ f.core)

@[simp] theorem mem_petals (f : SignedSunflower s i r) (D : Clause V) :
    D ∈ f.petals ↔ ∃ A ∈ f.family, A \ f.core = D := Finset.mem_image

/-- The insertion batch for the sunflower's core branch. -/
def coreBatch (f : SignedSunflower s i r) : InsertionBatch s i where
  clauses := {f.core}
  size := f.core.card
  nonempty := Finset.singleton_nonempty _
  size_pos := Finset.card_pos.mpr f.core_nonempty
  size_lt := f.sunflower.core_card_lt f.card_family_ge_two f.uniform
  uniform := by intro D hD; simp only [Finset.mem_singleton.mp hD]
  subclause := by
    intro D hD
    have hDcore : D = f.core := Finset.mem_singleton.mp hD
    subst D
    obtain ⟨A, hA⟩ := f.family_nonempty
    refine ⟨A, f.subset_active hA, f.sunflower.core_subset f.card_family_ge_two hA, ?_⟩
    intro hAC
    have hle := Finset.card_le_card hAC
    have hlt := f.sunflower.core_card_lt f.card_family_ge_two f.uniform
    rw [f.uniform A hA] at hle
    omega
  pairwise_disjoint := by
    intro D hD E hE hne
    exact (hne ((Finset.mem_singleton.mp hD).trans (Finset.mem_singleton.mp hE).symm)).elim

/-- The insertion batch for the sunflower's petal branch. -/
def petalBatch (f : SignedSunflower s i r) : InsertionBatch s i where
  clauses := f.petals
  size := i - f.core.card
  nonempty := by
    obtain ⟨A, hA⟩ := f.family_nonempty
    exact ⟨A \ f.core, Finset.mem_image.mpr ⟨A, hA, rfl⟩⟩
  size_pos := Nat.sub_pos_of_lt (f.sunflower.core_card_lt f.card_family_ge_two f.uniform)
  size_lt := by
    have hc := Finset.card_pos.mpr f.core_nonempty
    have hi := f.sunflower.core_card_lt f.card_family_ge_two f.uniform
    omega
  uniform := by
    intro D hD
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hD
    exact f.sunflower.petal_card f.card_family_ge_two f.uniform hA
  subclause := by
    intro D hD
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hD
    refine ⟨A, f.subset_active hA, Finset.sdiff_subset, ?_⟩
    intro hAsub
    have hle := Finset.card_le_card hAsub
    have hlt := f.sunflower.petal_card_lt f.card_family_ge_two f.uniform f.core_nonempty hA
    rw [f.uniform A hA] at hle
    omega
  pairwise_disjoint := by
    intro D hD E hE hne
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hE
    apply f.sunflower.petals_disjoint hA hB
    intro hAB
    exact hne (congrArg (fun C => C \ f.core) hAB)

/-- Choose the core or petal insertion batch. -/
def batch (f : SignedSunflower s i r) (choice : Bool) : InsertionBatch s i :=
  if choice then f.petalBatch else f.coreBatch

/-- The sparsification state obtained by taking the core branch. -/
def coreBranch (f : SignedSunflower s i r) : SparseState V :=
  s.batchUpdate f.coreBatch.clauses

/-- The sparsification state obtained by taking the petal branch. -/
def petalBranch (f : SignedSunflower s i r) : SparseState V :=
  { s.batchUpdate f.petalBatch.clauses with side := s.side ∪ f.core.image Literal.compl }

/-- Choose the core or petal successor state. -/
def branch (f : SignedSunflower s i r) (choice : Bool) : SparseState V :=
  if choice then f.petalBranch else f.coreBranch

@[simp] theorem branch_active (f : SignedSunflower s i r) (choice : Bool) :
    (f.branch choice).active = sparseBatchUpdate s.active (f.batch choice).clauses := by
  cases choice <;> rfl

@[simp] theorem branch_added (f : SignedSunflower s i r) (choice : Bool) :
    (f.branch choice).added = sparseBatchUpdate s.added (f.batch choice).clauses := by
  cases choice <;> rfl

theorem batch_card (f : SignedSunflower s i r) (choice : Bool) :
    (f.batch choice).clauses.card = if choice then r else 1 := by
  cases choice
  · exact Finset.card_singleton _
  · exact (f.sunflower.card_petals f.card_family_ge_two).trans f.card_family

theorem coreBranch_valid (f : SignedSunflower s i r) (hs : s.Valid b) :
    f.coreBranch.Valid b := f.coreBatch.valid_batchUpdate hs

theorem petalBranch_valid (f : SignedSunflower s i r) (hs : s.Valid b) :
    f.petalBranch.Valid b := by
  have h := f.petalBatch.valid_batchUpdate hs
  exact ⟨h.normalized, h.nonempty, h.antichain, h.width_le, h.added_subset⟩

theorem branch_valid (f : SignedSunflower s i r) (choice : Bool) (hs : s.Valid b) :
    (f.branch choice).Valid b := by
  cases choice
  · exact f.coreBranch_valid hs
  · exact f.petalBranch_valid hs

theorem core_false_iff_complement_units (C : Clause V) (x : Cube V) :
    C.eval x = false ↔ ∀ l ∈ C.image Literal.compl, l.eval x = true := by
  constructor
  · intro hC l hl
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hl
    have haf : a.eval x = false := by
      cases hax : a.eval x
      · rfl
      · have hCt : C.eval x = true :=
          (Clause.eval_eq_true C x).mpr ⟨a, ha, (Literal.eval_eq_true a x).mp hax⟩
        exact (Bool.false_ne_true (hC.symm.trans hCt)).elim
    simp only [Literal.eval_compl, haf, Bool.not_false]
  · intro h
    cases hC : C.eval x
    · rfl
    · obtain ⟨a, ha, hax⟩ := (Clause.eval_eq_true C x).mp hC
      have hat : a.eval x = true := (Literal.eval_eq_true a x).mpr hax
      have hbad := h a.compl (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
      simp only [Literal.eval_compl, hat, Bool.not_true] at hbad
      exact (Bool.false_ne_true hbad).elim

theorem petals_true_of_core_false (f : SignedSunflower s i r) (x : Cube V)
    (hA : ∀ C ∈ s.active, C.eval x = true) (hC : f.core.eval x = false) :
    ∀ P ∈ f.petals, P.eval x = true := by
  intro P hP
  obtain ⟨A, hAfamily, rfl⟩ := Finset.mem_image.mp hP
  obtain ⟨l, hlA, hlx⟩ := (Clause.eval_eq_true A x).mp (hA A (f.subset_active hAfamily))
  have hlnot : l ∉ f.core := by
    intro hlcore
    have htrue := (Clause.eval_eq_true f.core x).mpr ⟨l, hlcore, hlx⟩
    exact Bool.false_ne_true (hC.symm.trans htrue)
  exact (Clause.eval_eq_true (A \ f.core) x).mpr
    ⟨l, Finset.mem_sdiff.mpr ⟨hlA, hlnot⟩, hlx⟩

theorem eval_coreBranch (f : SignedSunflower s i r) (x : Cube V) :
    f.coreBranch.eval x = (s.eval x && f.core.eval x) := by
  apply bool_eq_of_true_iff
  change (s.batchUpdate {f.core}).eval x = true ↔ _
  rw [SparseState.eval_batchUpdate_eq_true, Bool.and_eq_true]
  simp only [Finset.mem_singleton, forall_eq]

theorem eval_petalBranch (f : SignedSunflower s i r) (x : Cube V) :
    f.petalBranch.eval x = (s.eval x && !(f.core.eval x)) := by
  apply bool_eq_of_true_iff
  rw [SparseState.eval_eq_true, Bool.and_eq_true, SparseState.eval_eq_true]
  change ((∀ C ∈ sparseBatchUpdate s.active f.petals, C.eval x = true) ∧
      (∀ l ∈ s.side ∪ f.core.image Literal.compl, l.eval x = true)) ↔ _
  rw [sparseBatchUpdate_satisfies]
  constructor
  · rintro ⟨⟨hA, _hP⟩, hS⟩
    have hc : f.core.eval x = false :=
      (core_false_iff_complement_units f.core x).mpr
        (fun l hl => hS l (Finset.mem_union.mpr (Or.inr hl)))
    refine ⟨⟨hA, fun l hl => hS l (Finset.mem_union.mpr (Or.inl hl))⟩, ?_⟩
    simp only [hc, Bool.not_false]
  · rintro ⟨⟨hA, hS⟩, hnot⟩
    have hc : f.core.eval x = false := by
      cases he : f.core.eval x <;> simp_all
    refine ⟨⟨hA, f.petals_true_of_core_false x hA hc⟩, ?_⟩
    intro l hl
    rcases Finset.mem_union.mp hl with hl | hl
    · exact hS l hl
    · exact (core_false_iff_complement_units f.core x).mp hc l hl

theorem branch_indicator (f : SignedSunflower s i r) (x : Cube V) :
    indicator (s.eval x) = indicator (f.coreBranch.eval x) +
      indicator (f.petalBranch.eval x) := by
  rw [f.eval_coreBranch, f.eval_petalBranch]
  cases s.eval x <;> cases f.core.eval x <;> simp

theorem branch_disjoint (f : SignedSunflower s i r) (x : Cube V) :
    ¬ (f.coreBranch.eval x = true ∧ f.petalBranch.eval x = true) := by
  rw [f.eval_coreBranch, f.eval_petalBranch]
  cases s.eval x <;> cases f.core.eval x <;> simp

end SignedSunflower
end SignedSunflower

end DepthThreeLowerBound

end

end Complexity
