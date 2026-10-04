/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Defs

/-!
# Tensor rank and border rank: proof internals

Proofs behind `Complexitylib.Algebraic.LinearAlgebra.Tensor.BorderRank`: the algebra of
`RankLE` (sums, scalar multiples, monotonicity, existence of a decomposition), its transport
along `map` and `subtensor`, the composition of maps (`map_map`, proved on outer products), and
the corresponding closure arguments for `BorderRankLE`.
-/

@[expose] public section

namespace Algebraic.Tensor3.Internal

open Finset Matrix

variable {α β γ α' β' γ' : Type*}

theorem outer_zero_left (v : β → ℂ) (w : γ → ℂ) : outer (0 : α → ℂ) v w = 0 := by
  funext i j k
  simp [outer]

theorem smul_outer (c : ℂ) (u : α → ℂ) (v : β → ℂ) (w : γ → ℂ) :
    c • outer u v w = outer (c • u) v w := by
  funext i j k
  simp [outer, mul_assoc]

theorem rankLE_zero_iff {T : Tensor3 α β γ} : T.RankLE 0 ↔ T = 0 := by
  constructor
  · rintro ⟨u, v, w, rfl⟩
    simp
  · rintro rfl
    exact ⟨Fin.elim0, Fin.elim0, Fin.elim0, by simp⟩

theorem rankLE_one_iff {T : Tensor3 α β γ} :
    T.RankLE 1 ↔ ∃ (u : α → ℂ) (v : β → ℂ) (w : γ → ℂ), T = outer u v w := by
  constructor
  · rintro ⟨u, v, w, rfl⟩
    exact ⟨u 0, v 0, w 0, by simp⟩
  · rintro ⟨u, v, w, rfl⟩
    exact ⟨fun _ => u, fun _ => v, fun _ => w, by simp⟩

theorem rankLE_add {S T : Tensor3 α β γ} {r r' : ℕ} (hS : S.RankLE r) (hT : T.RankLE r') :
    (S + T).RankLE (r + r') := by
  obtain ⟨u, v, w, rfl⟩ := hS
  obtain ⟨u', v', w', rfl⟩ := hT
  refine ⟨Fin.append u u', Fin.append v v', Fin.append w w', ?_⟩
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem zero_rankLE (d : ℕ) : (0 : Tensor3 α β γ).RankLE d :=
  ⟨fun _ => 0, fun _ => 0, fun _ => 0, by simp [outer_zero_left]⟩

theorem rankLE_mono {T : Tensor3 α β γ} {r r' : ℕ} (h : T.RankLE r) (hr : r ≤ r') :
    T.RankLE r' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  simpa using rankLE_add h (zero_rankLE d)

theorem rankLE_sum {ι : Type*} (s : Finset ι) (T : ι → Tensor3 α β γ) (r : ι → ℕ)
    (h : ∀ x ∈ s, (T x).RankLE (r x)) : (∑ x ∈ s, T x).RankLE (∑ x ∈ s, r x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_rankLE (α := α) (β := β) (γ := γ) 0
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact rankLE_add (h a (mem_insert_self _ _)) (ih fun x hx => h x (mem_insert_of_mem hx))

theorem rankLE_smul {T : Tensor3 α β γ} {r : ℕ} (c : ℂ) (h : T.RankLE r) :
    (c • T).RankLE r := by
  obtain ⟨u, v, w, rfl⟩ := h
  exact ⟨fun s => c • u s, v, w, by simp [Finset.smul_sum, smul_outer]⟩

theorem rankLE_card_mul_card [Fintype α] [Fintype β] (T : Tensor3 α β γ) :
    T.RankLE (Fintype.card α * Fintype.card β) := by
  classical
  have hT : T = ∑ i, ∑ j, outer (Pi.single i 1) (Pi.single j 1) (T i j) := by
    funext i j k
    simp [outer, Finset.sum_apply, Pi.single_apply]
  rw [hT]
  have := rankLE_sum (Finset.univ : Finset α) _ (fun _ => ∑ _ : β, 1) fun i _ =>
    rankLE_sum (Finset.univ : Finset β) _ (fun _ => 1) fun j _ =>
      rankLE_one_iff.mpr ⟨Pi.single i 1, Pi.single j 1, T i j, rfl⟩
  simpa [mul_comm] using this

section Map

variable [Fintype α] [Fintype β] [Fintype γ]
variable (X : Matrix α' α ℂ) (Y : Matrix β' β ℂ) (Z : Matrix γ' γ ℂ)

theorem map_outer (u : α → ℂ) (v : β → ℂ) (w : γ → ℂ) :
    map X Y Z (outer u v w) = outer (X *ᵥ u) (Y *ᵥ v) (Z *ᵥ w) := by
  funext i' j' k'
  simp only [map, outer, Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem map_add (S T : Tensor3 α β γ) : map X Y Z (S + T) = map X Y Z S + map X Y Z T := by
  funext i' j' k'
  simp only [map, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem map_zero : map X Y Z (0 : Tensor3 α β γ) = 0 := by
  funext i' j' k'
  simp [map]

theorem map_smul (c : ℂ) (T : Tensor3 α β γ) : map X Y Z (c • T) = c • map X Y Z T := by
  funext i' j' k'
  simp only [map, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => by ring

theorem map_finset_sum {ι : Type*} (s : Finset ι) (T : ι → Tensor3 α β γ) :
    map X Y Z (∑ x ∈ s, T x) = ∑ x ∈ s, map X Y Z (T x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using map_zero X Y Z
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, map_add, ih]

theorem rankLE_map {T : Tensor3 α β γ} {r : ℕ} (h : T.RankLE r) : (map X Y Z T).RankLE r := by
  obtain ⟨u, v, w, rfl⟩ := h
  exact ⟨fun s => X *ᵥ u s, fun s => Y *ᵥ v s, fun s => Z *ᵥ w s, by
    rw [map_finset_sum]
    simp [map_outer]⟩

theorem continuous_map : Continuous (map X Y Z : Tensor3 α β γ → Tensor3 α' β' γ') := by
  unfold map
  fun_prop

theorem map_diagonal [DecidableEq α] [DecidableEq β] [DecidableEq γ] (a : α → ℂ) (b : β → ℂ)
    (c : γ → ℂ) (T : Tensor3 α β γ) :
    map (diagonal a) (diagonal b) (diagonal c) T = fun i j k => a i * b j * c k * T i j k := by
  funext i j k
  simp [map, diagonal_apply, ite_mul]

theorem map_one [DecidableEq α] [DecidableEq β] [DecidableEq γ] (T : Tensor3 α β γ) :
    map 1 1 1 T = T := by
  rw [← diagonal_one, ← diagonal_one, ← diagonal_one, map_diagonal]
  funext i j k
  simp

end Map

section MapMap

variable [Fintype α] [Fintype β] [Fintype γ] [Fintype α'] [Fintype β'] [Fintype γ']
variable {α'' β'' γ'' : Type*}

theorem map_map (X : Matrix α' α ℂ) (Y : Matrix β' β ℂ) (Z : Matrix γ' γ ℂ)
    (X' : Matrix α'' α' ℂ) (Y' : Matrix β'' β' ℂ) (Z' : Matrix γ'' γ' ℂ) (T : Tensor3 α β γ) :
    map X' Y' Z' (map X Y Z T) = map (X' * X) (Y' * Y) (Z' * Z) T := by
  obtain ⟨u, v, w, rfl⟩ := rankLE_card_mul_card T
  simp only [map_finset_sum, map_outer, Matrix.mulVec_mulVec]

end MapMap

section Subtensor

variable (f : α' → α) (g : β' → β) (h : γ' → γ)

theorem subtensor_outer (u : α → ℂ) (v : β → ℂ) (w : γ → ℂ) :
    (outer u v w).subtensor f g h = outer (u ∘ f) (v ∘ g) (w ∘ h) :=
  rfl

theorem subtensor_finset_sum {ι : Type*} (s : Finset ι) (T : ι → Tensor3 α β γ) :
    (∑ x ∈ s, T x).subtensor f g h = ∑ x ∈ s, (T x).subtensor f g h := by
  funext i j k
  simp [subtensor, Finset.sum_apply]

theorem rankLE_subtensor {T : Tensor3 α β γ} {r : ℕ} (hT : T.RankLE r) :
    (T.subtensor f g h).RankLE r := by
  obtain ⟨u, v, w, rfl⟩ := hT
  exact ⟨fun s => u s ∘ f, fun s => v s ∘ g, fun s => w s ∘ h, by
    rw [subtensor_finset_sum]
    rfl⟩

theorem continuous_subtensor :
    Continuous fun T : Tensor3 α β γ => T.subtensor f g h := by
  unfold subtensor
  fun_prop

end Subtensor

section Border

theorem borderRankLE_of_rankLE {T : Tensor3 α β γ} {r : ℕ} (h : T.RankLE r) :
    T.BorderRankLE r :=
  subset_closure h

theorem borderRankLE_mono {T : Tensor3 α β γ} {r r' : ℕ} (h : T.BorderRankLE r) (hr : r ≤ r') :
    T.BorderRankLE r' :=
  closure_mono (fun _ hS => rankLE_mono hS hr) h

theorem isClosed_setOf_borderRankLE (r : ℕ) :
    IsClosed {T : Tensor3 α β γ | T.BorderRankLE r} :=
  isClosed_closure

theorem borderRankLE_add {S T : Tensor3 α β γ} {r r' : ℕ} (hS : S.BorderRankLE r)
    (hT : T.BorderRankLE r') : (S + T).BorderRankLE (r + r') :=
  map_mem_closure₂ continuous_add hS hT fun _ ha _ hb => rankLE_add ha hb

theorem borderRankLE_smul {T : Tensor3 α β γ} {r : ℕ} (c : ℂ) (h : T.BorderRankLE r) :
    (c • T).BorderRankLE r :=
  map_mem_closure (continuous_const_smul c) h fun _ hS => rankLE_smul c hS

theorem borderRankLE_map [Fintype α] [Fintype β] [Fintype γ] (X : Matrix α' α ℂ)
    (Y : Matrix β' β ℂ) (Z : Matrix γ' γ ℂ) {T : Tensor3 α β γ} {r : ℕ}
    (h : T.BorderRankLE r) : (map X Y Z T).BorderRankLE r :=
  map_mem_closure (continuous_map X Y Z) h fun _ hS => rankLE_map X Y Z hS

theorem borderRankLE_subtensor (f : α' → α) (g : β' → β) (h : γ' → γ) {T : Tensor3 α β γ}
    {r : ℕ} (hT : T.BorderRankLE r) : (T.subtensor f g h).BorderRankLE r :=
  map_mem_closure (f := fun T : Tensor3 α β γ => T.subtensor f g h) (continuous_subtensor f g h) hT
    fun _ hS => rankLE_subtensor f g h hS

theorem borderRankLE_zero_iff {T : Tensor3 α β γ} : T.BorderRankLE 0 ↔ T = 0 := by
  have : {S : Tensor3 α β γ | S.RankLE 0} = {0} := by
    ext S
    simp [rankLE_zero_iff]
  rw [BorderRankLE, this, closure_singleton, Set.mem_singleton_iff]

end Border

section Rank

variable [Fintype α] [Fintype β]

theorem rankLE_tensorRank (T : Tensor3 α β γ) : T.RankLE T.tensorRank :=
  Nat.sInf_mem (s := {r | T.RankLE r}) ⟨_, rankLE_card_mul_card T⟩

theorem tensorRank_le_iff {T : Tensor3 α β γ} {r : ℕ} : T.tensorRank ≤ r ↔ T.RankLE r :=
  ⟨fun h => rankLE_mono (rankLE_tensorRank T) h, fun h => Nat.sInf_le h⟩

theorem borderRankLE_borderRank (T : Tensor3 α β γ) : T.BorderRankLE T.borderRank :=
  Nat.sInf_mem (s := {r | T.BorderRankLE r}) ⟨_, borderRankLE_of_rankLE (rankLE_card_mul_card T)⟩

theorem borderRank_le_iff {T : Tensor3 α β γ} {r : ℕ} : T.borderRank ≤ r ↔ T.BorderRankLE r :=
  ⟨fun h => borderRankLE_mono (borderRankLE_borderRank T) h, fun h => Nat.sInf_le h⟩

end Rank

end Algebraic.Tensor3.Internal
