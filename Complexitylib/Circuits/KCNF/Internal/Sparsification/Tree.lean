/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.KCNF.Internal.Sparsification.Path
import Mathlib.Tactic

/-!
# Sparsification -- the branching tree

A deterministic choice (`chooseBranch`) turns the procedure into a binary tree. A word
`w : List Bool` names the node reached by taking the heart (`false`) or petal (`true`) branch
at each step (`walk`); a *leaf word* is one whose proper prefixes reach non-sparse nodes and
which itself reaches a sparse node (`IsLeafWord`). Every leaf word yields a `Path` with the same
length and the same petal steps (`exists_path_of_isLeafWord`).

Every solution of the root reaches a leaf containing it (`exists_isLeafWord_sat`, by induction on
the potential). The leaves are recovered from the positions of their petal steps: following any
branch sequence `f : ℕ → Bool` until a sparse node is reached (`walkSeq`) ends at the leaf of
every leaf word that agrees with `f` (`walkSeq_eq_walk`).
-/

@[expose] public section

namespace Complexity.ClauseSet.Sparsify

open Finset

variable {N : ℕ}

/-- A clause set that is not sparse has a valid branching choice. -/
theorem exists_choice (θ : ℕ → ℕ) {ψ : ClauseSet N} (h : ¬ Sparse θ ψ) :
    ∃ c H, Choice θ ψ c H := by
  classical
  have hex : ∃ c, ∃ H, Heavy θ ψ c H := by
    simp only [Sparse, not_forall, not_not] at h
    exact h
  set c₀ := Nat.find hex
  obtain ⟨H₀, hH₀⟩ := Nat.find_spec hex
  obtain ⟨H, hH, hmax⟩ := (univ.filter (Heavy θ ψ c₀)).exists_max_image card
    ⟨H₀, mem_filter.mpr ⟨mem_univ _, hH₀⟩⟩
  refine ⟨c₀, H, (mem_filter.mp hH).2, fun c' H' h' => Nat.find_min' hex ⟨H', h'⟩,
    fun H' h' => hmax H' (mem_filter.mpr ⟨mem_univ _, h'⟩)⟩

/-- The deterministic branching choice: a valid choice if there is one. -/
noncomputable def chooseBranch (θ : ℕ → ℕ) (ψ : ClauseSet N) : ℕ × Finset (Literal N) :=
  open Classical in
  if h : Sparse θ ψ then (0, ∅)
  else ((exists_choice θ h).choose, (exists_choice θ h).choose_spec.choose)

theorem choice_chooseBranch {θ : ℕ → ℕ} {ψ : ClauseSet N} (h : ¬ Sparse θ ψ) :
    Choice θ ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2 := by
  unfold chooseBranch
  rw [dite_eq_right h]
  exact (exists_choice θ h).choose_spec.choose_spec

/-- One deterministic branching step. -/
noncomputable def step (θ : ℕ → ℕ) (ψ : ClauseSet N) (b : Bool) : ClauseSet N :=
  child ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2 b

/-- The node reached along a word of branches. -/
noncomputable def walk (θ : ℕ → ℕ) : ClauseSet N → List Bool → ClauseSet N
  | ψ, [] => ψ
  | ψ, b :: w => walk θ (step θ ψ b) w

/-- A *leaf word*: its proper prefixes reach non-sparse nodes and it reaches a sparse node. -/
def IsLeafWord (θ : ℕ → ℕ) : ClauseSet N → List Bool → Prop
  | ψ, [] => Sparse θ ψ
  | ψ, b :: w => ¬ Sparse θ ψ ∧ IsLeafWord θ (step θ ψ b) w

/-- Follow the branch sequence `f` for at most `n` steps, stopping at a sparse node. -/
noncomputable def walkSeq (θ : ℕ → ℕ) : ℕ → ClauseSet N → (ℕ → Bool) → ClauseSet N
  | 0, ψ, _ => ψ
  | n + 1, ψ, f =>
    open Classical in
    if Sparse θ ψ then ψ else walkSeq θ n (step θ ψ (f 0)) fun i => f (i + 1)

variable {θ : ℕ → ℕ}

theorem walk_append_singleton (ψ : ClauseSet N) (u : List Bool) (b : Bool) :
    walk θ ψ (u ++ [b]) = step θ (walk θ ψ u) b := by
  induction u generalizing ψ with
  | nil => rfl
  | cons a u ih => exact ih (step θ ψ a)

theorem walk_take_succ (ψ : ClauseSet N) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    walk θ ψ (w.take (i + 1)) = step θ (walk θ ψ (w.take i)) (w.getD i false) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
    walk_append_singleton, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some]

theorem IsLeafWord.not_sparse_take {ψ : ClauseSet N} {w : List Bool} (h : IsLeafWord θ ψ w) :
    ∀ i < w.length, ¬ Sparse θ (walk θ ψ (w.take i)) := by
  induction w generalizing ψ with
  | nil => intro i hi; simp at hi
  | cons b w ih =>
    intro i hi
    cases i with
    | zero => exact h.1
    | succ i =>
      rw [List.take_succ_cons, walk]
      exact ih h.2 i (by simpa using hi)

theorem IsLeafWord.sparse_walk {ψ : ClauseSet N} {w : List Bool} (h : IsLeafWord θ ψ w) :
    Sparse θ (walk θ ψ w) := by
  induction w generalizing ψ with
  | nil => exact h
  | cons b w ih => exact ih h.2

theorem sat_of_sat_step {ψ : ClauseSet N} {b : Bool} {x : BitString N}
    (hx : (step θ ψ b).Sat x) : ψ.Sat x :=
  sat_of_sat_child hx

theorem reduced_step {ψ : ClauseSet N} (b : Bool) : Reduced (step θ ψ b) :=
  reduced_child _ _ _ _

section

variable (hθ : ∀ j, 1 ≤ θ j)
include hθ

theorem card_le_of_mem_step {ψ : ClauseSet N} (hψ : ¬ Sparse θ ψ) {k : ℕ}
    (hk : ∀ C ∈ ψ, C.card ≤ k) {b : Bool} {C : Finset (Literal N)} (hC : C ∈ step θ ψ b) :
    C.card ≤ k :=
  card_le_of_mem_child hθ (choice_chooseBranch hψ).1 hk hC

/-- Every clause of a child is contained in a clause of its parent. -/
theorem refines_step {ψ : ClauseSet N} (hψ : ¬ Sparse θ ψ) {b : Bool} {C : Finset (Literal N)}
    (hC : C ∈ step θ ψ b) : ∃ D ∈ ψ, C ⊆ D := by
  rcases mem_union.mp (child_subset _ _ _ _ hC) with hC | hC
  · exact ⟨C, hC, subset_rfl⟩
  · obtain ⟨D, hD, hCD⟩ := exists_flower_ssuperset hθ (choice_chooseBranch hψ).1 hC
    exact ⟨D, flower_subset _ _ _ hD, hCD.subset⟩

/-- Every clause reached by following branches is contained in a clause of the start. -/
theorem refines_walkSeq {n : ℕ} {ψ : ClauseSet N} {f : ℕ → Bool} {C : Finset (Literal N)}
    (hC : C ∈ walkSeq θ n ψ f) : ∃ D ∈ ψ, C ⊆ D := by
  induction n generalizing ψ f C with
  | zero => exact ⟨C, hC, subset_rfl⟩
  | succ n ih =>
    unfold walkSeq at hC
    split_ifs at hC with hsparse
    · exact ⟨C, hC, subset_rfl⟩
    · obtain ⟨D, hD, hCD⟩ := ih hC
      obtain ⟨E, hE, hDE⟩ := refines_step hθ hsparse hD
      exact ⟨E, hE, hCD.trans hDE⟩

/-- **Covering.** Every solution of a clause set reaches a leaf of which it is a solution. -/
theorem exists_isLeafWord_sat (ψ : ClauseSet N) {x : BitString N} (hx : ψ.Sat x) :
    ∃ w, IsLeafWord θ ψ w ∧ (walk θ ψ w).Sat x := by
  induction h : potential ψ using Nat.strong_induction_on generalizing ψ with
  | _ n ih =>
    by_cases hsparse : Sparse θ ψ
    · exact ⟨[], hsparse, hx⟩
    · set b := decide ¬ ∃ l ∈ (chooseBranch θ ψ).2, l.eval x = true
      have hstep : (step θ ψ b).Sat x := sat_child_of_sat hx
      have hlt : potential (step θ ψ b) < n :=
        h ▸ potential_child_lt hθ (choice_chooseBranch hsparse).1 b
      obtain ⟨w, hw, hwx⟩ := ih _ hlt (step θ ψ b) hstep rfl
      exact ⟨b :: w, ⟨hsparse, hw⟩, hwx⟩

omit hθ in
theorem sat_of_sat_walk {ψ : ClauseSet N} {w : List Bool} (hw : IsLeafWord θ ψ w)
    {x : BitString N} (hx : (walk θ ψ w).Sat x) : ψ.Sat x := by
  induction w generalizing ψ with
  | nil => exact hx
  | cons b w ih => exact sat_of_sat_step (ih hw.2 hx)

omit hθ in
theorem sat_of_sat_walkSeq {n : ℕ} {ψ : ClauseSet N} {f : ℕ → Bool} {x : BitString N}
    (hx : (walkSeq θ n ψ f).Sat x) : ψ.Sat x := by
  induction n generalizing ψ f with
  | zero => exact hx
  | succ n ih =>
    unfold walkSeq at hx
    split_ifs at hx with hsparse
    · exact hx
    · exact sat_of_sat_step (ih hx)

theorem card_le_of_mem_walkSeq {k n : ℕ} {ψ : ClauseSet N} (hk : ∀ C ∈ ψ, C.card ≤ k)
    {f : ℕ → Bool} {C : Finset (Literal N)} (hC : C ∈ walkSeq θ n ψ f) : C.card ≤ k := by
  induction n generalizing ψ f with
  | zero => exact hk C hC
  | succ n ih =>
    unfold walkSeq at hC
    split_ifs at hC with hsparse
    · exact hk C hC
    · exact ih (fun D hD => card_le_of_mem_step hθ hsparse hk hD) hC

end

/-- Following a branch sequence that agrees with a leaf word, for at least as many steps, ends at
that leaf. -/
theorem walkSeq_eq_walk {ψ : ClauseSet N} {w : List Bool} (hw : IsLeafWord θ ψ w)
    {f : ℕ → Bool} (hf : ∀ i < w.length, f i = w.getD i false) {n : ℕ} (hn : w.length ≤ n) :
    walkSeq θ n ψ f = walk θ ψ w := by
  induction w generalizing ψ f n with
  | nil =>
    cases n with
    | zero => rfl
    | succ n => simp only [walkSeq, walk]; exact ite_eq_left hw
  | cons b w ih =>
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hn; omega⟩
    simp only [walkSeq, walk]
    rw [ite_eq_right hw.1]
    have hf0 : f 0 = b := by simpa using hf 0 (by simp)
    rw [hf0]
    refine ih hw.2 (fun i hi => ?_) (by simpa using hn)
    simpa using hf (i + 1) (by simpa using hi)

/-- **A leaf word is a branch.** It yields a `Path` with the same length, ending in a sparse node,
whose petal steps are the positions of `true` in the word. -/
theorem exists_path_of_isLeafWord {ψ : ClauseSet N} (hred : Reduced ψ) {w : List Bool}
    (hw : IsLeafWord θ ψ w) :
    ∃ P : Path θ N, P.node 0 = ψ ∧ P.len = w.length ∧ Sparse θ (P.node P.len) ∧
      (range P.len).filter (fun i => P.dir i = true) =
        (range w.length).filter fun i => w.getD i false = true := by
  have hns := hw.not_sparse_take
  refine ⟨{ len := w.length
            node := fun i => walk θ ψ (w.take i)
            size := fun i => (chooseBranch θ (walk θ ψ (w.take i))).1
            heart := fun i => (chooseBranch θ (walk θ ψ (w.take i))).2
            dir := fun i => w.getD i false
            choice := fun i hi => choice_chooseBranch (hns i hi)
            step := fun i hi => walk_take_succ ψ w hi
            reduced_zero := by simpa [walk] using hred }, by simp [walk], rfl, ?_, rfl⟩
  simpa [List.take_length] using hw.sparse_walk

end Complexity.ClauseSet.Sparsify
