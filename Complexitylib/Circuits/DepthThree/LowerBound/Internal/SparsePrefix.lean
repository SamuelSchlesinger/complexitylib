/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.SparseBranch
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Linarith

/-!
# Unrestricted depth-three lower bound: sparse prefix

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/SparsePrefix.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

namespace DepthThreeLowerBound

open scoped BigOperators

variable {V : Type uDepth1} [DecidableEq V]

/-- Numerical hypotheses for the occurrence bounds in sparsification. -/
structure SparseNumerics (r e D : ℕ → ℕ) (b : ℕ) : Prop where
  r_ge_two : ∀ i, 2 ≤ i → i ≤ b → 2 ≤ r i
  e_one : e 1 = 1
  e_succ : ∀ i, 1 ≤ i → i + 1 ≤ b →
    e (i + 1) = i.factorial * (r (i + 1) - 1) ^ i
  D_eq : ∀ i, 1 ≤ i → i ≤ b →
    D i = (e i + 1) * (2 + ∑ v ∈ Finset.Ico 1 i, D v)

theorem sparse_occurrence_le_of_no_sunflower
    {r e D : ℕ → ℕ} {b : ℕ} (hnum : SparseNumerics r e D b)
    (s : SparseState V) (u : ℕ) (hu : 1 ≤ u) (hub : u ≤ b)
    (hno : ¬ Nonempty (SignedSunflower s u (r u))) (l : Literal V) :
    literalOccurrences s.active u l ≤ e u := by
  classical
  cases u with
  | zero => omega
  | succ i =>
      by_cases hi : i = 0
      · subst i
        simpa only [hnum.e_one] using literalOccurrences_one_le s.active l
      · have hi1 : 1 ≤ i := by omega
        have hr : 2 ≤ r (i + 1) := hnum.r_ge_two _ (by omega) hub
        rw [hnum.e_succ i hi1 hub]
        apply no_nonempty_core_sunflower_occurrence_le
          (clausesOfSize s.active (i + 1)) i (r (i + 1)) hr
          (fun C hC => (mem_clausesOfSize.mp hC).2)
        intro sub hsub hcard core hcore hflower
        apply hno
        exact ⟨{
          family := sub
          core := core
          subset_active := hsub.trans (clausesOfSize_subset s.active (i + 1))
          card_family := hcard
          two_le := hr
          uniform := fun C hC => (mem_clausesOfSize.mp (hsub hC)).2
          core_nonempty := hcore
          sunflower := hflower
        }⟩

/-- A minimal eligible sunflower, a branch choice, and its resulting state. -/
structure SparseStep (r : ℕ → ℕ) (s t : SparseState V) where
  /-- The common size of the selected clauses. -/
  size : ℕ
  /-- The selected signed sunflower. -/
  selected : SignedSunflower s size (r size)
  minimal : ∀ j, 2 ≤ j → j < size →
    ¬ Nonempty (SignedSunflower s j (r j))
  /-- Choose the core branch or the petal branch. -/
  choice : Bool
  target : t = selected.branch choice

namespace SparseStep

/-- The insertion batch selected by a sparsification step. -/
noncomputable def batch {r : ℕ → ℕ} {s t : SparseState V}
    (step : SparseStep r s t) : InsertionBatch s step.size :=
  step.selected.batch step.choice

theorem target_active {r : ℕ → ℕ} {s t : SparseState V}
    (step : SparseStep r s t) :
    t.active = sparseBatchUpdate s.active step.batch.clauses := by
  exact (congrArg (fun q : SparseState V => q.active) step.target).trans
    (step.selected.branch_active step.choice)

theorem target_added {r : ℕ → ℕ} {s t : SparseState V}
    (step : SparseStep r s t) :
    t.added = sparseBatchUpdate s.added step.batch.clauses := by
  exact (congrArg (fun q : SparseState V => q.added) step.target).trans
    (step.selected.branch_added step.choice)

theorem valid {r : ℕ → ℕ} {s t : SparseState V} {b : ℕ}
    (step : SparseStep r s t) (hs : s.Valid b) : t.Valid b := by
  rw [step.target]
  exact step.selected.branch_valid step.choice hs

theorem fresh_added {r : ℕ → ℕ} {s t : SparseState V} {b : ℕ}
    (step : SparseStep r s t) (hs : s.Valid b) :
    Disjoint s.added step.batch.clauses := by
  classical
  apply Finset.disjoint_left.mpr
  intro C hCa hCB
  exact step.batch.fresh hs C hCB C (hs.added_subset hCa) (Finset.Subset.refl C)

theorem batch_size_count {r : ℕ → ℕ} {s t : SparseState V}
    (step : SparseStep r s t) (u : ℕ) :
    (clausesOfSize step.batch.clauses u).card =
      if step.batch.size = u then step.batch.clauses.card else 0 := by
  classical
  by_cases h : step.batch.size = u
  · have hself : clausesOfSize step.batch.clauses u = step.batch.clauses :=
      clausesOfSize_eq_self _ _ (fun C hC => (step.batch.uniform C hC).trans h)
    rw [ite_eq_left h, hself]
  · have hempty : clausesOfSize step.batch.clauses u = ∅ := by
      apply clausesOfSize_eq_empty
      intro C hC
      rw [step.batch.uniform C hC]
      exact h
    rw [ite_eq_right h, hempty, Finset.card_empty]

theorem removed_eq_empty_of_le {r : ℕ → ℕ} {s t : SparseState V} {b : ℕ}
    (step : SparseStep r s t) (hs : s.Valid b) (u : ℕ)
    (hu : u ≤ step.batch.size) : subsumedOfSize s.added step.batch.clauses u = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro C hC
  obtain ⟨hC, D, hDB, hDC⟩ := Finset.mem_filter.mp hC
  obtain ⟨hCa, hCu⟩ := mem_clausesOfSize.mp hC
  have hsize : C.card ≤ D.card := by rw [hCu, step.batch.uniform D hDB]; exact hu
  have heq : D = C := Finset.eq_of_subset_of_card_le hDC hsize
  subst D
  exact step.batch.fresh hs C hDB C (hs.added_subset hCa) (Finset.Subset.refl C)

theorem update_balance {r : ℕ → ℕ} {s t : SparseState V} {b : ℕ}
    (step : SparseStep r s t) (hs : s.Valid b) (u : ℕ) :
    (clausesOfSize t.added u).card + (subsumedOfSize s.added step.batch.clauses u).card =
      (clausesOfSize s.added u).card +
        if step.batch.size = u then step.batch.clauses.card else 0 := by
  rw [step.target_added, ← step.batch_size_count u]
  exact clausesOfSize_update_balance s.added step.batch.clauses u (step.fresh_added hs)

end SparseStep

/-- A finite sequence of valid sparsification steps. -/
inductive SparsePath (r : ℕ → ℕ) (start : SparseState V) : SparseState V → Type _
  | nil : SparsePath r start start
  | snoc {s t : SparseState V} (path : SparsePath r start s)
      (step : SparseStep r s t) : SparsePath r start t

namespace SparsePath

variable {r e D : ℕ → ℕ} {b : ℕ} {start finish : SparseState V}

/-- The number of steps in a sparsification path. -/
def length : {finish : SparseState V} → SparsePath r start finish → ℕ
  | _, .nil => 0
  | _, .snoc path _ => length path + 1

/-- The clauses inserted along a sparsification path. -/
noncomputable def insertions :
    {finish : SparseState V} → SparsePath r start finish → ℕ → ℕ
  | _, .nil, _ => 0
  | _, .snoc path step, u =>
      insertions path u + if step.batch.size = u then step.batch.clauses.card else 0

/-- Count processed sunflowers of each size along the path. -/
def processed : {finish : SparseState V} → SparsePath r start finish → ℕ → ℕ
  | _, .nil, _ => 0
  | _, .snoc path step, i => processed path i + if step.size = i then 1 else 0

/-- Count petal-branch choices of each size along the path. -/
def petalSteps : {finish : SparseState V} → SparsePath r start finish → ℕ → ℕ
  | _, .nil, _ => 0
  | _, .snoc path step, i =>
      petalSteps path i + if step.size = i ∧ step.choice = true then 1 else 0

theorem valid (path : SparsePath r start finish) (hstart : start.Valid b) :
    finish.Valid b := by
  induction path with
  | nil => exact hstart
  | snoc path step ih => exact step.valid ih

@[simp] theorem insertions_nil (u : ℕ) :
    (SparsePath.nil : SparsePath r start start).insertions u = 0 := rfl

@[simp] theorem insertions_snoc {s t : SparseState V}
    (path : SparsePath r start s) (step : SparseStep r s t) (u : ℕ) :
    (path.snoc step).insertions u =
      path.insertions u + if step.batch.size = u then step.batch.clauses.card else 0 := rfl

theorem insertions_sum_snoc {s t : SparseState V}
    (path : SparsePath r start s) (step : SparseStep r s t) (u : ℕ) :
    (∑ v ∈ Finset.Ico 1 u, (path.snoc step).insertions v) =
      (∑ v ∈ Finset.Ico 1 u, path.insertions v) +
        if step.batch.size < u then step.batch.clauses.card else 0 := by
  classical
  simp only [insertions_snoc, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp only [Finset.mem_Ico, Nat.succ_le_iff.mpr step.batch.size_pos, true_and]

theorem added_occurrence_bound (path : SparsePath r start finish)
    (hnum : SparseNumerics r e D b) (hstart : start.Valid b)
    (hadded : start.added = ∅) :
    ∀ u, 1 ≤ u → u ≤ b → ∀ l,
      literalOccurrences finish.added u l ≤ e u + 1 := by
  classical
  induction path with
  | nil =>
      intro u hu hub l
      simp [hadded, literalOccurrences, clausesOfSize]
  | @snoc s t path step ih =>
      intro u hu hub l
      have hs := path.valid hstart
      have hupdate := literalOccurrences_update_le s.added step.batch.clauses u l
      change literalOccurrences (sparseBatchUpdate s.added step.batch.clauses) u l ≤ _ at hupdate
      rw [← step.target_added] at hupdate
      by_cases hsize : step.batch.size = u
      · have hlt : u < step.size := hsize ▸ step.batch.size_lt
        have hpre := sparse_occurrence_le_of_no_sunflower hnum s u hu hub
          (fun hflower => step.minimal u (by
            have hflower_size : 2 ≤ u := (Classical.choice hflower).size_ge_two
            exact hflower_size) hlt hflower) l
        have hadd := literalOccurrences_mono hs.added_subset u l
        have hbatch := step.batch.literal_occurrences_le_one u l
        omega
      · have hempty : clausesOfSize step.batch.clauses u = ∅ := by
          apply clausesOfSize_eq_empty
          intro C hC
          rw [step.batch.uniform C hC]
          exact hsize
        have hzero : literalOccurrences step.batch.clauses u l = 0 := by
          simp [literalOccurrences, hempty]
        have hprev := ih u hu hub l
        omega

theorem online_insertion_bound (path : SparsePath r start finish)
    (hnum : SparseNumerics r e D b) (hstart : start.Valid b)
    (hadded : start.added = ∅) :
    ∀ u, 1 ≤ u → u ≤ b →
      path.insertions u ≤ (clausesOfSize finish.added u).card +
        (e u + 1) * ∑ v ∈ Finset.Ico 1 u, path.insertions v := by
  classical
  induction path with
  | nil =>
      intro u hu hub
      simp [hadded, clausesOfSize]
  | @snoc s t path step ih =>
      intro u hu hub
      have hs := path.valid hstart
      have hbalance := step.update_balance hs u
      have hprev := ih u hu hub
      have hocc := path.added_occurrence_bound hnum hstart hadded u hu hub
      have hremoved := subsumedOfSize_card_le s.added step.batch.clauses u (e u + 1)
        (fun C hC => step.batch.clause_nonempty C hC) hocc
      rw [insertions_snoc, insertions_sum_snoc]
      by_cases hlt : step.batch.size < u
      · have hne : step.batch.size ≠ u := Nat.ne_of_lt hlt
        simp only [ite_eq_right hne, ite_eq_left hlt, Nat.add_zero] at hbalance ⊢
        nlinarith
      · have hremoved_zero := step.removed_eq_empty_of_le hs u (Nat.le_of_not_gt hlt)
        rw [hremoved_zero, Finset.card_empty, Nat.add_zero] at hbalance
        simp only [ite_eq_right hlt, Nat.add_zero]
        omega

theorem insertion_recurrence [Fintype V] (path : SparsePath r start finish)
    (hnum : SparseNumerics r e D b) (hstart : start.Valid b)
    (hadded : start.added = ∅) (u : ℕ) (hu : 1 ≤ u) (hub : u ≤ b) :
    path.insertions u ≤ (e u + 1) *
      (2 * Fintype.card V + ∑ v ∈ Finset.Ico 1 u, path.insertions v) := by
  have hv := path.valid hstart
  have hsurvive := clausesOfSize_card_le finish.added u (e u + 1)
    (fun C hC => hv.nonempty C (hv.added_subset (mem_clausesOfSize.mp hC).1))
    (path.added_occurrence_bound hnum hstart hadded u hu hub)
  have honline := path.online_insertion_bound hnum hstart hadded u hu hub
  nlinarith

theorem length_le_insertions (path : SparsePath r start finish)
    (hstart : start.Valid b) :
    path.length ≤ ∑ u ∈ Finset.Ico 1 b, path.insertions u := by
  induction path with
  | nil => simp [length]
  | @snoc s t path step ih =>
      have hbatch : 0 < step.batch.clauses.card := step.batch.nonempty.card_pos
      have hsize : step.batch.size < b :=
        step.batch.size_lt.trans_le (step.selected.size_le (path.valid hstart))
      change path.length + 1 ≤ _
      rw [insertions_sum_snoc, ite_eq_left hsize]
      omega

theorem processed_le_insertions (path : SparsePath r start finish) (i : ℕ) :
    path.processed i ≤ ∑ u ∈ Finset.Ico 1 i, path.insertions u := by
  induction path with
  | nil => simp [processed]
  | @snoc s t path step ih =>
      have hbatch : 0 < step.batch.clauses.card := step.batch.nonempty.card_pos
      change path.processed i + (if step.size = i then 1 else 0) ≤ _
      rw [insertions_sum_snoc]
      by_cases hi : step.size = i
      · have hsize : step.batch.size < i := hi ▸ step.batch.size_lt
        simp only [ite_eq_left hi, ite_eq_left hsize]
        omega
      · simp only [ite_eq_right hi, Nat.add_zero]
        split <;> omega

theorem petalSteps_mul_le_insertions (path : SparsePath r start finish) (i : ℕ) :
    r i * path.petalSteps i ≤ ∑ u ∈ Finset.Ico 1 i, path.insertions u := by
  induction path with
  | nil => simp [petalSteps]
  | @snoc s t path step ih =>
      change r i * (path.petalSteps i +
        if step.size = i ∧ step.choice = true then 1 else 0) ≤ _
      rw [insertions_sum_snoc]
      by_cases hi : step.size = i ∧ step.choice = true
      · have hsize : step.batch.size < i := hi.1 ▸ step.batch.size_lt
        have hcard : step.batch.clauses.card = r i := by
          simp only [SparseStep.batch, step.selected.batch_card, hi.2, ↓reduceIte, hi.1]
        simp only [ite_eq_left hi, ite_eq_left hsize, Nat.mul_add, Nat.mul_one, hcard]
        omega
      · simp only [ite_eq_right hi, Nat.add_zero]
        split <;> omega

end SparsePath

theorem sparse_insertion_budget_of_recurrence
    (r e D N : ℕ → ℕ) (b m : ℕ) (hnum : SparseNumerics r e D b)
    (hN : ∀ u, 1 ≤ u → u ≤ b →
      N u ≤ (e u + 1) * (2 * m + ∑ v ∈ Finset.Ico 1 u, N v)) :
    ∀ u, 1 ≤ u → u ≤ b → N u ≤ D u * m := by
  intro u
  induction u using Nat.strong_induction_on with
  | h u ih =>
      intro hu hub
      have hsum : (∑ v ∈ Finset.Ico 1 u, N v) ≤
          (∑ v ∈ Finset.Ico 1 u, D v) * m := by
        calc
          (∑ v ∈ Finset.Ico 1 u, N v) ≤
              ∑ v ∈ Finset.Ico 1 u, D v * m := by
            apply Finset.sum_le_sum
            intro v hv
            have hv' := Finset.mem_Ico.mp hv
            exact ih v hv'.2 hv'.1 (le_trans (Nat.le_of_lt hv'.2) hub)
          _ = _ := (Finset.sum_mul _ _ _).symm
      calc
        N u ≤ (e u + 1) * (2 * m + ∑ v ∈ Finset.Ico 1 u, N v) := hN u hu hub
        _ ≤ (e u + 1) * (2 * m + (∑ v ∈ Finset.Ico 1 u, D v) * m) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_left hsum _)
        _ = D u * m := by
          rw [hnum.D_eq u hu hub, ← Nat.add_mul, Nat.mul_assoc]

namespace SparsePath

variable {r e D : ℕ → ℕ} {b : ℕ} {start finish : SparseState V}

theorem insertion_budget [Fintype V] (path : SparsePath r start finish)
    (hnum : SparseNumerics r e D b) (hstart : start.Valid b)
    (hadded : start.added = ∅) (u : ℕ) (hu : 1 ≤ u) (hub : u ≤ b) :
    path.insertions u ≤ D u * Fintype.card V :=
  sparse_insertion_budget_of_recurrence r e D path.insertions b (Fintype.card V) hnum
    (path.insertion_recurrence hnum hstart hadded) u hu hub

theorem insertion_sum_budget [Fintype V] (path : SparsePath r start finish)
    (hnum : SparseNumerics r e D b) (hstart : start.Valid b)
    (hadded : start.added = ∅) (i : ℕ) (hi : i ≤ b + 1) :
    (∑ u ∈ Finset.Ico 1 i, path.insertions u) ≤
      (∑ u ∈ Finset.Ico 1 i, D u) * Fintype.card V := by
  calc
    (∑ u ∈ Finset.Ico 1 i, path.insertions u) ≤
        ∑ u ∈ Finset.Ico 1 i, D u * Fintype.card V := by
      apply Finset.sum_le_sum
      intro u hu
      have hu' := Finset.mem_Ico.mp hu
      exact path.insertion_budget hnum hstart hadded u hu'.1 (by omega)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem length_budget [Fintype V] (path : SparsePath r start finish)
    (hnum : SparseNumerics r e D b) (hstart : start.Valid b)
    (hadded : start.added = ∅) :
    path.length ≤ (∑ u ∈ Finset.Ico 1 b, D u) * Fintype.card V :=
  (path.length_le_insertions hstart).trans
    (path.insertion_sum_budget hnum hstart hadded b (by omega))

theorem processed_budget [Fintype V] (path : SparsePath r start finish)
    (hnum : SparseNumerics r e D b) (hstart : start.Valid b)
    (hadded : start.added = ∅) (i : ℕ) (hi : i ≤ b) :
    path.processed i ≤ (∑ u ∈ Finset.Ico 1 i, D u) * Fintype.card V :=
  (path.processed_le_insertions i).trans
    (path.insertion_sum_budget hnum hstart hadded i (by omega))

theorem petalSteps_budget [Fintype V] (path : SparsePath r start finish)
    (hnum : SparseNumerics r e D b) (hstart : start.Valid b)
    (hadded : start.added = ∅) (i : ℕ) (hi : i ≤ b) :
    r i * path.petalSteps i ≤ (∑ u ∈ Finset.Ico 1 i, D u) * Fintype.card V :=
  (path.petalSteps_mul_le_insertions i).trans
    (path.insertion_sum_budget hnum hstart hadded i (by omega))

end SparsePath

end DepthThreeLowerBound

end Complexity
