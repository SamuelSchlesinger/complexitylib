/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.CutBoundary
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Exact cut changes in the bisection argument

Flipping a set toggles exactly the edges in its cut. The resulting integer
identities make successive moves telescope, including moves that restore
balance after improving the cut.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.Internal

open scoped Classical symmDiff

variable {W : Type} [Fintype W] (H : SimpleGraph W)

theorem cutFinset_symmDiff (S X : Finset W) :
    H.cutFinset (S ∆ X) = H.cutFinset S ∆ H.cutFinset X := by
  ext e
  obtain ⟨u, v⟩ := e
  simp only [SimpleGraph.mem_cutFinset_mk, Finset.mem_symmDiff]
  tauto

theorem helpfulness_eq_sub (S X : Finset W) :
    helpfulness H S X = (H.cutFinset S).card - (H.cutFinset (S ∆ X)).card := by
  rw [cutFinset_symmDiff, Finset.symmDiff_def]
  have disjoint : Disjoint (H.cutFinset S \ H.cutFinset X)
      (H.cutFinset X \ H.cutFinset S) := disjoint_sdiff_sdiff
  rw [Finset.card_union_of_disjoint disjoint]
  have hcard := Finset.card_sdiff_add_card_inter (H.cutFinset S) (H.cutFinset X)
  rw [Finset.inter_comm] at hcard
  unfold helpfulness
  push_cast
  lia

theorem helpfulness_eq_sub_sdiff {S X : Finset W} (hX : X ⊆ S) :
    helpfulness H S X = (H.cutFinset S).card - (H.cutFinset (S \ X)).card := by
  rw [helpfulness_eq_sub, symmDiff_comm S X, symmDiff_of_le hX]

theorem helpfulness_eq_sub_union {S X : Finset W} (hX : Disjoint S X) :
    helpfulness H S X = (H.cutFinset S).card - (H.cutFinset (S ∪ X)).card := by
  rw [helpfulness_eq_sub, Finset.symmDiff_eq_union hX]

theorem helpfulness_add (S X Y : Finset W) :
    helpfulness H S (X ∆ Y) = helpfulness H S X + helpfulness H (S ∆ X) Y := by
  simp only [helpfulness_eq_sub, symmDiff_assoc]
  ring

theorem helpfulness_compl (S X : Finset W) :
    helpfulness H Sᶜ X = helpfulness H S X := by
  simp only [helpfulness, cutFinset_compl]

theorem exists_min_cut_of_card {m : Nat} (hm : m ≤ Fintype.card W) :
    ∃ S : Finset W, S.card = m ∧
      ∀ T : Finset W, T.card = m → (H.cutFinset S).card ≤ (H.cutFinset T).card := by
  let candidates := Finset.univ.filter (fun S : Finset W => S.card = m)
  have nonempty : candidates.Nonempty := by
    obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset W)) (n := m) (by simpa only [Finset.card_univ] using hm)
    exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩⟩
  obtain ⟨S, hS, minimal⟩ := candidates.exists_min_image (fun T => (H.cutFinset T).card) nonempty
  exact ⟨S, (Finset.mem_filter.mp hS).2,
    fun T hT => minimal T (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩)⟩

theorem exists_min_bisection :
    ∃ S : Finset W, S.card ≤ Sᶜ.card + 1 ∧ Sᶜ.card ≤ S.card + 1 ∧
      ∀ T : Finset W, T.card ≤ Tᶜ.card + 1 → Tᶜ.card ≤ T.card + 1 →
        (H.cutFinset S).card ≤ (H.cutFinset T).card := by
  obtain ⟨S, hS, minimal⟩ := exists_min_cut_of_card H (Nat.div_le_self (Fintype.card W) 2)
  have sumS := Finset.card_compl_add_card S
  refine ⟨S, by lia, by lia, ?_⟩
  intro T leftSmall rightSmall
  by_cases hT : T.card = Fintype.card W / 2
  · exact minimal T hT
  · have sumT := Finset.card_compl_add_card T
    have hcomp : Tᶜ.card = Fintype.card W / 2 := by lia
    simpa only [cutFinset_compl] using minimal Tᶜ hcomp

theorem two_moves_le_zero {S : Finset W}
    (minimal : ∀ T : Finset W, T.card = S.card → (H.cutFinset S).card ≤ (H.cutFinset T).card)
    {X Y : Finset W} (hX : X ⊆ S) (hY : Y ⊆ (S \ X)ᶜ) (sameSize : Y.card = X.card) :
    helpfulness H S X + helpfulness H (S \ X)ᶜ Y ≤ 0 := by
  have disjoint : Disjoint (S \ X) Y := Finset.disjoint_left.mpr
    (fun _ hu hv => Finset.mem_compl.mp (hY hv) hu)
  have size : ((S \ X) ∪ Y).card = S.card := by
    rw [Finset.card_union_of_disjoint disjoint, sameSize,
      Finset.card_sdiff_add_card_eq_card hX]
  have bound := minimal ((S \ X) ∪ Y) size
  rw [helpfulness_compl, helpfulness_eq_sub_sdiff H hX,
    helpfulness_eq_sub_union H disjoint]
  lia

theorem cutFinset_singleton (v : W) :
    H.cutFinset {v} = (H.neighborFinset v).map (Sym2.mkEmbedding v) := by
  ext e
  constructor
  · intro he
    obtain ⟨hadj, u, w, rfl, hu, _⟩ := H.mem_cutFinset.mp he
    have huv : u = v := Finset.mem_singleton.mp hu
    subst u
    exact Finset.mem_map.mpr ⟨w, (H.mem_neighborFinset v w).mpr hadj, rfl⟩
  · intro he
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp he
    have hadj := (H.mem_neighborFinset v w).mp hw
    apply H.mem_cutFinset_mk.mpr
    refine ⟨hadj, Or.inl ⟨Finset.mem_singleton_self _, ?_⟩⟩
    intro hwv
    have hwv' : w = v := Finset.mem_singleton.mp hwv
    exact H.loopless.irrefl v (hwv' ▸ hadj)

private theorem cutFinset_singleton_inter {S : Finset W} {v : W} (hv : v ∈ S) :
    H.cutFinset {v} ∩ H.cutFinset S =
      (H.neighborFinset v \ S).map (Sym2.mkEmbedding v) := by
  ext e
  rw [Finset.mem_inter, cutFinset_singleton]
  constructor
  · rintro ⟨he, hcut⟩
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp he
    have crossing := (H.mem_cutFinset_mk.mp hcut).2
    have hwS : w ∉ S := by tauto
    exact Finset.mem_map.mpr ⟨w, Finset.mem_sdiff.mpr ⟨hw, hwS⟩, rfl⟩
  · intro he
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨hadj, hwS⟩ := Finset.mem_sdiff.mp hw
    exact ⟨Finset.mem_map.mpr ⟨w, hadj, rfl⟩,
      H.mem_cutFinset_mk.mpr ⟨(H.mem_neighborFinset v w).mp hadj, Or.inl ⟨hv, hwS⟩⟩⟩

theorem helpfulness_eq_two_mul_inter_sub (S X : Finset W) :
    helpfulness H S X =
      2 * ((H.cutFinset X ∩ H.cutFinset S).card : ℤ) - (H.cutFinset X).card := by
  have hcard := Finset.card_sdiff_add_card_inter (H.cutFinset X) (H.cutFinset S)
  unfold helpfulness
  lia

theorem helpfulness_singleton {S : Finset W} {v : W} (hv : v ∈ S) :
    helpfulness H S {v} = 2 * ((H.neighborFinset v \ S).card : ℤ) - H.degree v := by
  rw [helpfulness_eq_two_mul_inter_sub, cutFinset_singleton_inter H hv,
    cutFinset_singleton, Finset.card_map, Finset.card_map,
    SimpleGraph.card_neighborFinset_eq_degree]

theorem one_le_helpfulness_singleton {S : Finset W} {v : W} (hv : v ∈ S)
    (degree : H.degree v ≤ 3) (outside : 2 ≤ (H.neighborFinset v \ S).card) :
    1 ≤ helpfulness H S {v} := by
  rw [helpfulness_singleton H hv]
  lia

theorem card_cut_inter_eq_sum_neighbors {S X : Finset W} (hX : X ⊆ S) :
    (H.cutFinset X ∩ H.cutFinset S).card = ∑ v ∈ X, (H.neighborFinset v \ S).card := by
  let edges (v : W) := (H.neighborFinset v \ S).map (Sym2.mkEmbedding v)
  have partition : X.biUnion edges = H.cutFinset X ∩ H.cutFinset S := by
    ext e
    constructor
    · intro he
      obtain ⟨v, hv, he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp he
      obtain ⟨hadj, hwS⟩ := Finset.mem_sdiff.mp hw
      have adjacent := (H.mem_neighborFinset v w).mp hadj
      exact Finset.mem_inter.mpr
        ⟨H.mem_cutFinset_mk.mpr ⟨adjacent, Or.inl ⟨hv, fun h => hwS (hX h)⟩⟩,
          H.mem_cutFinset_mk.mpr ⟨adjacent, Or.inl ⟨hX hv, hwS⟩⟩⟩
    · intro he
      obtain ⟨heX, heS⟩ := Finset.mem_inter.mp he
      obtain ⟨hadj, v, w, rfl, hv, _⟩ := H.mem_cutFinset.mp heX
      have crossing := (H.mem_cutFinset_mk.mp heS).2
      have hvS := hX hv
      have hwS : w ∉ S := by tauto
      exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_map.mpr
        ⟨w, Finset.mem_sdiff.mpr ⟨(H.mem_neighborFinset v w).mpr hadj, hwS⟩, rfl⟩⟩
  have disjoint : (X : Set W).PairwiseDisjoint edges := by
    intro u hu v hv hne
    apply Finset.disjoint_left.mpr
    intro e heU heV
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp heU
    obtain ⟨b, hb, heq⟩ := Finset.mem_map.mp heV
    change s(v, b) = s(u, a) at heq
    rcases Sym2.eq_iff.mp heq with ⟨hvu, _⟩ | ⟨hva, _⟩
    · exact hne hvu.symm
    · exact (Finset.mem_sdiff.mp ha).2 (hva ▸ hX hv)
  rw [← partition, Finset.card_biUnion disjoint]
  simp only [edges, Finset.card_map]

theorem card_cutFinset_eq_sum_neighbors (X : Finset W) :
    (H.cutFinset X).card = ∑ v ∈ X, (H.neighborFinset v \ X).card := by
  simpa only [Finset.inter_self] using card_cut_inter_eq_sum_neighbors H (S := X) le_rfl

theorem degree_sum_cut (X : Finset W) :
    (H.cutFinset X).card + 2 * (H.induce {w | w ∈ X}).edgeFinset.card =
      ∑ v ∈ X, H.degree v := by
  let G := H.induce {w | w ∈ X}
  have localCount (v : {w | w ∈ X}) :
      G.degree v + (H.neighborFinset v \ X).card = H.degree v := by
    have count := congrArg Finset.card (H.map_neighborFinset_induce (s := {w | w ∈ X}) v)
    rw [Finset.card_map] at count
    have degreeCount : G.degree v = (H.neighborFinset v ∩ X).card := by
      change (G.neighborFinset v).card = _
      convert count using 1 <;> congr 1 <;> ext w <;>
        simp only [G, Finset.mem_inter, Set.mem_toFinset, Set.mem_ofPred_eq,
          SimpleGraph.mem_neighborFinset]
    rw [degreeCount, Nat.add_comm, Finset.card_sdiff_add_card_inter]
    rfl
  have total := Finset.sum_congr rfl
    (fun v (_ : v ∈ (Finset.univ : Finset {w | w ∈ X})) => localCount v)
  have outside : (∑ v : {w | w ∈ X}, (H.neighborFinset v \ X).card) =
      ∑ v ∈ X, (H.neighborFinset v \ X).card :=
    (Finset.sum_subtype X (by simp) (fun v => (H.neighborFinset v \ X).card)).symm
  have degrees : (∑ v : {w | w ∈ X}, H.degree v) = ∑ v ∈ X, H.degree v :=
    (Finset.sum_subtype X (by simp) (fun v => H.degree v)).symm
  rw [Finset.sum_add_distrib, G.sum_degrees_eq_twice_card_edges, outside, degrees,
    ← card_cutFinset_eq_sum_neighbors H X] at total
  exact (Nat.add_comm _ _).trans total

theorem abs_helpfulness_le_card_cut (S X : Finset W) :
    |helpfulness H S X| ≤ (H.cutFinset X).card := by
  have count := Finset.card_sdiff_add_card_inter (H.cutFinset X) (H.cutFinset S)
  rw [abs_le]
  unfold helpfulness
  constructor <;> lia

theorem abs_helpfulness_le_mul_card (S X : Finset W) {d : Nat}
    (degree : ∀ v ∈ X, H.degree v ≤ d) :
    |helpfulness H S X| ≤ d * X.card := by
  have total := degree_sum_cut H X
  have sumBound := Finset.sum_le_sum degree
  simp only [Finset.sum_const, nsmul_eq_mul] at sumBound
  have cutBound : (H.cutFinset X).card ≤ d * X.card := by
    calc (H.cutFinset X).card ≤ X.card * d := by lia
      _ = d * X.card := Nat.mul_comm _ _
  exact (abs_helpfulness_le_card_cut H S X).trans (by exact_mod_cast cutBound)

theorem helpfulness_eq_degree_sum {S X : Finset W} (hX : X ⊆ S) :
    helpfulness H S X = 2 * (∑ v ∈ X, ((H.neighborFinset v \ S).card : ℤ)) +
      2 * ((H.induce {w | w ∈ X}).edgeFinset.card : ℤ) - ∑ v ∈ X, (H.degree v : ℤ) := by
  rw [helpfulness_eq_two_mul_inter_sub, card_cut_inter_eq_sum_neighbors H hX]
  have total := degree_sum_cut H X
  have totalInt : ((H.cutFinset X).card : ℤ) +
      2 * ((H.induce {w | w ∈ X}).edgeFinset.card : ℤ) = ∑ v ∈ X, (H.degree v : ℤ) := by
    exact_mod_cast total
  push_cast
  lia

theorem card_sub_two_le_helpfulness {S X : Finset W} (hX : X ⊆ S)
    (connected : (H.induce {w | w ∈ X}).Connected)
    (degree : ∀ v ∈ X, H.degree v ≤ 3)
    (boundary : ∀ v ∈ X, ∃ w ∉ S, H.Adj v w) :
    (X.card : ℤ) - 2 ≤ helpfulness H S X := by
  have external (v : W) (hv : v ∈ X) : 1 ≤ (H.neighborFinset v \ S).card := by
    obtain ⟨w, hw, hadj⟩ := boundary v hv
    exact Finset.card_pos.mpr ⟨w,
      Finset.mem_sdiff.mpr ⟨(H.mem_neighborFinset v w).mpr hadj, hw⟩⟩
  have outward := Finset.sum_le_sum external
  have degrees := Finset.sum_le_sum degree
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.mul_one] at outward degrees
  have treeCount := connected.card_vert_le_card_edgeSet_add_one
  simp only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at treeCount
  have cardX : Fintype.card {w | w ∈ X} = X.card :=
    Fintype.card_of_finset' X (fun _ => Iff.rfl)
  rw [cardX] at treeCount
  rw [helpfulness_eq_degree_sum H hX]
  have hExt : (X.card : ℤ) ≤ ∑ v ∈ X, ((H.neighborFinset v \ S).card : ℤ) := by
    exact_mod_cast outward
  have hDeg : (∑ v ∈ X, (H.degree v : ℤ)) ≤ X.card * 3 := by exact_mod_cast degrees
  lia

end Algebraic.Cutwidth.Bisection.Internal
