/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Relations

/-!
# One-way-liveness proof: RankLoss

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Automata/RankLoss.lean

Module and namespace names, imports, and formatting are adapted to complexitylib.
The machine definitions are shared through `Models.FiniteAutomaton.Defs`.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

/-- The exponential rank-loss threshold for relations on `h` points. -/
def rankLoss (h : ℕ) : ℕ := 2 ^ ((h - 2) / 31)

/-- A simultaneous rank-loss bound for relation quotients with unit lifts. -/
def RankLossAt (h : ℕ) : Prop :=
  ∀ (H A M : Type) [Fintype H] [Fintype A] [Monoid M] [Finite M],
    Fintype.card H = h →
    ∀ (ρ : M →* Pairing (A ⊕ A)), Function.Injective ρ →
    ∀ (φ : M →* BRel H), Function.Surjective φ → HasUnitLifts φ →
    ∀ (a : M), a * a = a → ∀ (x y : H), x ≠ y → φ a = BRel.addEdge x y →
      rankLoss h ≤ Fintype.card A - Pairing.rank (ρ a)

/-- One new relation pair forces the inductive rank loss, after two genuine
corner reductions. The support budget loses only the factor two. -/
lemma rank_drop_step {H A M : Type} [Fintype A] [Monoid M] [Finite M]
    (ρ : M →* Pairing (A ⊕ A)) (hρ : Function.Injective ρ)
    (φ : M →* BRel H) (hφ : Function.Surjective φ)
    (e : M) (he : e * e = e) (b : Corner e he) (hb : b * b = b)
    (P N : BRel H) (heP : φ e = P) (hbN : φ b.val = N)
    (F : Set H) [Fintype F]
    (hF : BRel.restrictedId F * P * BRel.restrictedId F = BRel.restrictedId F)
    (hPN : P * N = N) (hNP : N * P = N)
    (x y : F) (hxy : x ≠ y)
    (hN : ∀ i j : F, N.holds i.val j.val ↔ (BRel.addEdge x y).holds i j)
    (hIH : RankLossAt (Fintype.card F)) :
    rankLoss (Fintype.card F) ≤ 2 * (Pairing.rank (ρ e) - Pairing.rank (ρ b.val)) := by
  classical
  let ρ₁ := Pairing.reduceHom ρ e he
  have hρ₁ : Function.Injective ρ₁ := Pairing.reduceHom_injective ρ e he hρ
  have hP : P * P = P := by rw [← heP, ← map_mul, he]
  let φ₁ := Corner.mapTo (he := he) (hq := hP) φ heP
  have hs₁ : Function.Surjective φ₁ := Corner.mapTo_surjective φ heP hφ
  obtain ⟨hQ, θ, hθ, hPQ, hQP⟩ := BRel.relation_corner hP F hF
  let Q := P * BRel.restrictedId F * P
  let q : Corner P hP := ⟨Q, hPQ, hQP⟩
  have hq : q * q = q := Corner.ext hQ
  obtain ⟨d, hd, hφd, hmin⟩ := exists_min_rank_lift ρ₁ φ₁ hs₁ q hq
  let ρ₂ := Pairing.reduceHom ρ₁ d hd
  have hρ₂ : Function.Injective ρ₂ := Pairing.reduceHom_injective ρ₁ d hd hρ₁
  let φ₂ := Corner.mapTo (he := hd) (hq := hq) φ₁ hφd
  let E := (Corner.flattenEquiv q hq).trans θ
  let ψ := E.toMonoidHom.comp φ₂
  have hsψ : Function.Surjective ψ :=
    E.surjective.comp (Corner.mapTo_surjective φ₁ hφd hs₁)
  have hlψ : HasUnitLifts ψ :=
    (min_rank_corner_unitLifts ρ₁ hρ₁ φ₁ hs₁ d hd q hq hφd hmin).comp_equiv E
  let w : Corner d hd := Corner.sandwich b
  have hw : ψ w = BRel.addEdge x y := by
    ext i j
    change (θ ((Corner.flattenEquiv q hq) (φ₂ w))).holds i j ↔ _
    rw [hθ]
    change (φ₁ (d * b * d)).val.holds i.val j.val ↔ _
    rw [map_mul, map_mul, hφd]
    change (Q * φ b.val * Q).holds i.val j.val ↔ _
    rw [hbN]
    exact (BRel.sandwich_holds_on F hF hPN hNP i j).trans (hN i j)
  obtain ⟨n, hn, hnidem⟩ := exists_idempotent_power w
  have him : ψ (w ^ n) = BRel.addEdge x y := by
    rw [map_pow, hw]
    exact IsIdempotentElem.pow_eq (BRel.addEdge_idem x y) (Nat.ne_of_gt hn)
  have hlow := hIH F {i // i ∈ Pairing.lefts (ρ₁ d)} (Corner d hd) rfl
    ρ₂ hρ₂ ψ hsψ hlψ (w ^ n) hnidem x y hxy him
  let J := Pairing.support (ρ₁ b)
  obtain ⟨K, hK, hall⟩ := Pairing.reduceHom_common_support ρ₁ d hd J
  have hwK : Pairing.support (ρ₂ w) ⊆ K := hall b (Finset.Subset.refl _)
  have hvK : Pairing.support (ρ₂ (w ^ n)) ⊆ K := by
    rw [map_pow]
    exact (Pairing.support_pow_subset _ _).trans hwK
  have hJ : J.card ≤ 2 * (Pairing.rank (ρ e) - Pairing.rank (ρ b.val)) := by
    have hi : ρ₁ b * ρ₁ b = ρ₁ b := by rw [← map_mul, hb]
    have hh := Pairing.support_idempotent_bound (ρ₁ b) hi
    simpa only [ρ₁, Pairing.card_reduced, Pairing.reduceHom_rank] using hh
  calc
    rankLoss (Fintype.card F) ≤ Fintype.card {i // i ∈ Pairing.lefts (ρ₁ d)} -
        Pairing.rank (ρ₂ (w ^ n)) := hlow
    _ ≤ (Pairing.support (ρ₂ (w ^ n))).card := Pairing.defect_le_support _
    _ ≤ K.card := Finset.card_le_card hvK
    _ ≤ J.card := hK
    _ ≤ 2 * (Pairing.rank (ρ e) - Pairing.rank (ρ b.val)) := hJ

namespace RectangleFrame
open scoped Classical
variable {H I J : Type} [Fintype I] [Fintype J]
    (F : RectangleFrame H I J)

/-- Frame vertices removed except for the selected row and column, together with the hub. -/
noncomputable def deleted (i : I) (j : J) : Finset H :=
  ((Finset.univ.erase i).image F.left ∪ (Finset.univ.erase j).image F.right) ∪ {F.hub}

/-- The vertices that survive the frame deletion. -/
def retained (i : I) (j : J) : Set H := {x | x ∉ F.deleted i j}

lemma deleted_card (i : I) (j : J) :
    (F.deleted i j).card = (Fintype.card I - 1) + (Fintype.card J - 1) + 1 := by
  have hLR :
      Disjoint ((Finset.univ.erase i).image F.left) ((Finset.univ.erase j).image F.right) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
    exact F.disjoint a b hb.symm
  have hh : Disjoint ((Finset.univ.erase i).image F.left ∪ (Finset.univ.erase j).image F.right)
      {F.hub} := by
    rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and]
    exact ⟨fun a _ => F.left_ne_hub a, fun b _ => F.right_ne_hub b⟩
  simp only [deleted, Finset.card_union_of_disjoint hh, Finset.card_union_of_disjoint hLR,
    Finset.card_singleton, Finset.card_image_of_injective _ F.left_injective,
    Finset.card_image_of_injective _ F.right_injective,
    Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]

lemma retained_card [Fintype H] (i : I) (j : J) :
    Fintype.card (F.retained i j) = Fintype.card H -
      ((Fintype.card I - 1) + (Fintype.card J - 1) + 1) := by
  rw [Fintype.card_of_subtype (F.deleted i j)ᶜ (by intro x; simp [retained]),
    Finset.card_compl, F.deleted_card]

lemma retained_ne_hub (i : I) (j : J) (x : H) (hx : x ∈ F.retained i j) : x ≠ F.hub := by
  intro h
  subst x
  exact hx (by simp [deleted])

@[simp] lemma left_mem_retained (i k : I) (j : J) :
    F.left k ∈ F.retained i j ↔ k = i := by
  simp only [retained, Set.mem_ofPred_eq, deleted, Finset.mem_union, Finset.mem_image,
    Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_singleton]
  constructor
  · intro h
    by_contra hk
    exact h (Or.inl (Or.inl ⟨k, hk, rfl⟩))
  · rintro rfl ((⟨a, ha, he⟩ | ⟨b, _, he⟩) | he)
    · exact ha (F.left_injective he)
    · exact F.disjoint k b he.symm
    · exact F.left_ne_hub k he

@[simp] lemma right_mem_retained (i : I) (j k : J) :
    F.right k ∈ F.retained i j ↔ k = j := by
  simp only [retained, Set.mem_ofPred_eq, deleted, Finset.mem_union, Finset.mem_image,
    Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_singleton]
  constructor
  · intro h
    by_contra hk
    exact h (Or.inl (Or.inr ⟨k, hk, rfl⟩))
  · rintro rfl ((⟨a, _, he⟩ | ⟨b, hb, he⟩) | he)
    · exact F.disjoint a k he
    · exact hb (F.right_injective he)
    · exact F.right_ne_hub k he

lemma old_avoids_retained {E : Set (I × J)} {i : I} {j : J} (h : (i,j) ∉ E) :
    ∀ p ∈ E, F.left p.1 ∉ F.retained i j ∨ F.right p.2 ∉ F.retained i j := by
  intro p hp
  simp only [left_mem_retained, right_mem_retained]
  by_contra! hh
  have he : p = (i, j) := Prod.ext hh.1 hh.2
  exact h (he ▸ hp)

lemma exists_frame [Fintype H] (h : 33 ≤ Fintype.card H) :
    Nonempty (RectangleFrame H (Fin 16) (Fin 16)) := by
  obtain ⟨f⟩ : Nonempty (((Fin 16 ⊕ Fin 16) ⊕ Unit) ↪ H) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa using h
  refine ⟨⟨fun i => f (Sum.inl (Sum.inl i)), fun j => f (Sum.inl (Sum.inr j)),
    f (Sum.inr ()), ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i j hij
    simpa using f.injective hij
  · intro i j hij
    simpa using f.injective hij
  · intro i j hij
    simpa using f.injective hij
  · intro i hij
    simpa using f.injective hij
  · intro j hij
    simpa using f.injective hij
end RectangleFrame


open scoped Classical

lemma rectangle_chain {H A M I J : Type} [Fintype H] [Fintype A]
    [Fintype I] [Fintype J] [Monoid M] [Finite M]
    (ρ : M →* Pairing (A ⊕ A)) (hρ : Function.Injective ρ)
    (φ : M →* BRel H) (hφ : Function.Surjective φ)
    (F : RectangleFrame H I J) (L : ℕ)
    (hL : ∀ i j, rankLoss (Fintype.card (F.retained i j)) = L)
    (hIH : ∀ i j, RankLossAt (Fintype.card (F.retained i j)))
    (e : M) (he : e * e = e) (heφ : φ e = F.base)
    (g : I × J → Corner e he)
    (hg : ∀ p, φ (g p).val = F.rel {p})
    (K : Finset {i // i ∈ Pairing.lefts (ρ e)})
    (hgK : ∀ p, Pairing.support (Pairing.reduceHom ρ e he (g p)) ⊆ K)
    (E : Finset (I × J)) :
    ∃ b : Corner e he, b * b = b ∧ φ b.val = F.rel (E : Set (I × J)) ∧
      Pairing.support (Pairing.reduceHom ρ e he b) ⊆ K ∧
      E.card * L ≤ 2 * (Pairing.rank (ρ e) - Pairing.rank (ρ b.val)) := by
  classical
  let ρ₀ := Pairing.reduceHom ρ e he
  induction E using Finset.induction_on with
  | empty =>
    refine ⟨1, one_mul _, ?_, ?_, ?_⟩
    · simpa only [Corner.val_one, Finset.coe_empty, F.rel_empty] using heφ
    · simp only [map_one, Pairing.support_one, Finset.empty_subset]
    · simp
  | @insert p E hp ih =>
    obtain ⟨b, hb, hbφ, hbK, hbound⟩ := ih
    let w : Corner b hb := Corner.sandwich (g p)
    obtain ⟨n, hn, hnidem⟩ := exists_idempotent_power w
    let v := w ^ n
    have hv : v.val * v.val = v.val := congrArg Corner.val hnidem
    have hwφ : φ w.val.val = F.rel ((insert p E : Finset (I × J)) : Set (I × J)) := by
      change φ ((b.val * (g p).val) * b.val) = _
      rw [map_mul, map_mul, hbφ, hg, F.rel_mul, F.rel_mul]
      congr 1
      ext q
      simp only [Set.mem_union, Set.mem_singleton_iff, Finset.mem_coe,
        Finset.mem_insert]
      tauto
    have hvφ : φ v.val.val = F.rel ((insert p E : Finset (I × J)) : Set (I × J)) := by
      dsimp [v]
      rw [Corner.val_pow_pos w hn, Corner.val_pow_pos w.val hn, map_pow, hwφ]
      exact IsIdempotentElem.pow_eq (F.rel_idem _) (Nat.ne_of_gt hn)
    have mulK (a c : Pairing ({i // i ∈ Pairing.lefts (ρ e)} ⊕ {i // i ∈ Pairing.lefts (ρ e)}))
        (ha : Pairing.support a ⊆ K) (hc : Pairing.support c ⊆ K) :
        Pairing.support (a * c) ⊆ K :=
      by
        intro i hi
        have hh := Pairing.support_mul_subset a c hi
        simp only [Finset.mem_union] at hh
        exact hh.elim (fun h => ha h) (fun h => hc h)
    have hwK : Pairing.support (ρ₀ w.val) ⊆ K := by
      change Pairing.support (ρ₀ (b * g p * b)) ⊆ K
      rw [map_mul, map_mul]
      exact mulK _ _ (mulK _ _ hbK (hgK p)) hbK
    have hvK : Pairing.support (ρ₀ v.val) ⊆ K := by
      dsimp [v]
      rw [Corner.val_pow_pos _ hn, map_pow]
      exact (Pairing.support_pow_subset _ _).trans hwK
    let R := F.retained p.1 p.2
    have hR := F.restricted_old (E : Set (I × J)) R (F.retained_ne_hub p.1 p.2)
      (F.old_avoids_retained hp)
    obtain ⟨hPN, hNP⟩ := F.rel_absorb (E := (E : Set (I × J)))
      (D := ((insert p E : Finset (I × J)) : Set (I × J))) (by simp)
    let u : R := ⟨F.left p.1, (F.left_mem_retained _ _ _).mpr rfl⟩
    let z : R := ⟨F.right p.2, (F.right_mem_retained _ _ _).mpr rfl⟩
    have huz : u ≠ z := fun h => F.disjoint p.1 p.2 (congrArg Subtype.val h)
    have him : ∀ i j : R, (F.rel ((insert p E : Finset (I × J)) : Set (I × J))).holds
        i.val j.val ↔ (BRel.addEdge u z).holds i j := by
      simpa only [Finset.coe_insert] using
        F.restricted_new (E : Set (I × J)) R (F.retained_ne_hub p.1 p.2)
          (F.old_avoids_retained hp) p.1 p.2 u.property z.property
    let v' := Corner.flattenEquiv b hb v
    have hv' : v' * v' = v' := by rw [← map_mul, hnidem]
    have hstep := rank_drop_step ρ hρ φ hφ b.val (Corner.val_idempotent b hb) v' hv'
      (F.rel E) (F.rel ((insert p E : Finset (I × J)) : Set (I × J)))
      hbφ hvφ R hR hPN hNP u z huz him (hIH p.1 p.2)
    rw [hL] at hstep
    have hrb : Pairing.rank (ρ b.val) ≤ Pairing.rank (ρ e) := by
      have hh := Pairing.rank_mul_le_left (ρ e) (ρ b.val)
      rwa [← map_mul, b.left] at hh
    have hrv : Pairing.rank (ρ v.val.val) ≤ Pairing.rank (ρ b.val) := by
      have hh := Pairing.rank_mul_le_left (ρ b.val) (ρ v.val.val)
      have heq : b.val * v.val.val = v.val.val := congrArg Corner.val v.left
      rwa [← map_mul, heq] at hh
    refine ⟨v.val, hv, hvφ, hvK, ?_⟩
    change L ≤ 2 * (Pairing.rank (ρ b.val) - Pairing.rank (ρ v.val.val)) at hstep
    rw [Finset.card_insert_of_notMem hp, Nat.add_mul, one_mul]
    omega


lemma rankLoss_recurrence {h : ℕ} (hh : 33 ≤ h) : rankLoss h = 2 * rankLoss (h - 31) := by
  have he : (h - 2) / 31 = (h - 31 - 2) / 31 + 1 := by omega
  simp only [rankLoss, he, pow_succ]
  omega

/-- Exponential rank loss by 256-addition amplification, simultaneously in the
relation alphabet and the ambient diagram degree. -/
theorem rankLoss_all (h : ℕ) : RankLossAt h := by
  induction h using Nat.strong_induction_on with
  | h h IH =>
    intro H A M _ _ _ _ hH ρ hρ φ hφ hl a ha x y hxy hφa
    classical
    have hcpos : 1 ≤ Fintype.card A - Pairing.rank (ρ a) := by
      have hr := Pairing.rank_le_card (ρ a)
      have hne : Pairing.rank (ρ a) ≠ Fintype.card A := by
        intro heq
        have hu := isUnit_of_injective_map_finite ρ hρ a (Pairing.full_rank_isUnit (ρ a) heq)
        have haone : a = 1 := (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp ha
        have hh : BRel.addEdge x y = 1 := by rw [← hφa, haone, map_one]
        exact BRel.addEdge_ne_one hxy hh
      omega
    by_cases hh : h < 33
    · have he : (h - 2) / 31 = 0 := by omega
      simpa only [rankLoss, he, pow_zero] using hcpos
    have hh : 33 ≤ h := by omega
    obtain ⟨F⟩ := RectangleFrame.exists_frame (H := H) (by omega)
    let c := Fintype.card A - Pairing.rank (ρ a)
    let src : Fin 16 ⊕ Fin 16 → H := Sum.elim F.left (fun _ => F.hub)
    let dst : Fin 16 ⊕ Fin 16 → H := Sum.elim (fun _ => F.hub) F.right
    have hdist (p : Fin 16 ⊕ Fin 16) : src p ≠ dst p := by
      cases p with
      | inl i => exact F.left_ne_hub i
      | inr j => exact (F.right_ne_hub j).symm
    choose s hs hφs hrs using fun p =>
      conjugate_lift ρ φ hl a ha x y hxy hφa (src p) (dst p) (hdist p)
    let J : Finset A := Finset.univ.biUnion (fun p => Pairing.support (ρ (s p)))
    have hsJ (p : Fin 16 ⊕ Fin 16) : Pairing.support (ρ (s p)) ⊆ J := by
      intro i hi
      exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, hi⟩
    have hJ : J.card ≤ 64 * c := by
      have hb (p : Fin 16 ⊕ Fin 16) : (Pairing.support (ρ (s p))).card ≤ 2 * c := by
        have hi : ρ (s p) * ρ (s p) = ρ (s p) := by rw [← map_mul, hs]
        simpa only [hrs, c] using Pairing.support_idempotent_bound (ρ (s p)) hi
      have hh := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin 16 ⊕ Fin 16))
        (fun p => Pairing.support (ρ (s p))) (2 * c) (fun p _ => hb p)
      simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin] at hh
      dsimp [J]
      omega
    have hbase : F.base * F.base = F.base := BRel.restrictedId_idem _
    obtain ⟨e, he, heφ⟩ := exists_idempotent_lift φ hφ F.base hbase
    let ρ₀ := Pairing.reduceHom ρ e he
    obtain ⟨K, hK, hall⟩ := Pairing.reduceHom_common_support ρ e he J
    let g : Fin 16 × Fin 16 → Corner e he := fun p =>
      Corner.sandwich (s (Sum.inl p.1) * s (Sum.inr p.2))
    have hg (p : Fin 16 × Fin 16) : φ (g p).val = F.rel {p} := by
      change φ (e * (s (Sum.inl p.1) * s (Sum.inr p.2)) * e) = _
      rw [map_mul, map_mul, map_mul, heφ, hφs, hφs]
      dsimp [src, dst]
      rw [← mul_assoc]
      exact F.generator_image p.1 p.2
    have hgK (p : Fin 16 × Fin 16) : Pairing.support (ρ₀ (g p)) ⊆ K := by
      apply hall
      rw [map_mul]
      intro i hi
      rcases Finset.mem_union.mp (Pairing.support_mul_subset _ _ hi) with hi | hi
      · exact hsJ _ hi
      · exact hsJ _ hi
    have hcard (i j : Fin 16) : Fintype.card (F.retained i j) = h - 31 := by
      rw [F.retained_card, hH]
      rfl
    have hi (i j : Fin 16) : RankLossAt (Fintype.card (F.retained i j)) := by
      rw [hcard]
      exact IH (h - 31) (by omega)
    obtain ⟨b, _hb, _hbφ, hbK, hcost⟩ := rectangle_chain ρ hρ φ hφ F (rankLoss (h - 31))
      (fun i j => congrArg rankLoss (hcard i j)) hi e he heφ g hg K hgK Finset.univ
    have hbudget : Pairing.rank (ρ e) - Pairing.rank (ρ b.val) ≤ 64 * c := by
      have hd := Pairing.defect_le_support (ρ₀ b)
      have hbc := Finset.card_le_card hbK
      simp only [ρ₀, Pairing.card_reduced, Pairing.reduceHom_rank] at hd
      omega
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hcost
    rw [rankLoss_recurrence hh]
    change 2 * rankLoss (h - 31) ≤ c
    omega


namespace Corner
variable {M : Type*} [Monoid M]
/-- The corner at the identity is equivalent to the original monoid. -/
def oneEquiv : Corner (1 : M) (one_mul 1) ≃* M where
  toFun := Corner.val
  invFun x := ⟨x, one_mul x, mul_one x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
end Corner

/-- No permutation-lift hypothesis remains in the divisor degree bound. -/
theorem relation_divisor_degree {H A M : Type} [Fintype H] [Fintype A]
    [Monoid M] [Finite M] (ρ : M →* Pairing (A ⊕ A)) (hρ : Function.Injective ρ)
    (φ : M →* BRel H) (hφ : Function.Surjective φ) (x y : H) (hxy : x ≠ y) :
    rankLoss (Fintype.card H) ≤ Fintype.card A := by
  classical
  obtain ⟨e, he, heφ, hmin⟩ := exists_min_rank_lift ρ φ hφ 1 (one_mul 1)
  let ρ₀ := Pairing.reduceHom ρ e he
  let φ₀ := Corner.mapTo (he := he) (hq := one_mul 1) φ heφ
  let ψ := Corner.oneEquiv.toMonoidHom.comp φ₀
  have hψ : Function.Surjective ψ := Corner.oneEquiv.surjective.comp
    (Corner.mapTo_surjective φ heφ hφ)
  have hlψ : HasUnitLifts ψ :=
    (min_rank_corner_unitLifts ρ hρ φ hφ e he 1 (one_mul 1) heφ hmin).comp_equiv Corner.oneEquiv
  obtain ⟨a, ha, haψ⟩ := exists_idempotent_lift ψ hψ (BRel.addEdge x y) (BRel.addEdge_idem x y)
  have hb := rankLoss_all (Fintype.card H) H {i // i ∈ Pairing.lefts (ρ e)} (Corner e he)
    rfl ρ₀ (Pairing.reduceHom_injective ρ e he hρ) ψ hψ hlψ a ha x y hxy haψ
  rw [Pairing.card_reduced] at hb
  exact hb.trans ((Nat.sub_le _ _).trans (Pairing.rank_le_card _))

end Complexity.FiniteAutomaton
