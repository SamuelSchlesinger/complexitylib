/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Network
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Balanced functions and the one-sided count

A function is `(K, ν)`-balanced when, on every rectangle with both sides of
size at least `K`, under every split, the fraction of accepting inputs lies
within `ν` of one half. A sumset extractor with error `ν` is balanced with
`K` polynomial, for the same reason it is rectangle-free.

The one-sided count `Network.card_accepting_inter_le` bounds, for a network
with unique satisfying assignments, the number of its accepted inputs on
which a balanced `f` is `1`. Fix a vertex set `L`. The accepted inputs are
partitioned by the bits their satisfying assignment places on the cut of
`L`, and each class is a rectangle of past and future assignments. Classes
with both sides at least `K` are balanced. A class with a small past side
has at most `K - 1` rows; summing its columns over all such classes counts
pairs of a future assignment and a cut assignment, and the cut assignment is
determined by the future assignment together with the forward-crossing bits
(`BackwardDetermined`). Symmetrically for small future sides with the
backward-crossing bits (`ForwardDetermined`).
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth

open scoped Classical

variable {n : Nat}

/-- The points of the rectangle `P × Q`, under the split `U`, accepted by `f`. -/
noncomputable def rectangleOnes (f : Cslib.BooleanFunction n) (U : Finset (Fin n))
    (P : Finset (U → Bool)) (Q : Finset (↥Uᶜ → Bool)) :
    Finset ((U → Bool) × (↥Uᶜ → Bool)) :=
  (P ×ˢ Q).filter fun pq => f (glue U pq.1 pq.2) = true

/-- `f` is `(K, ν)`-balanced: on every rectangle with both sides of size at
least `K`, under every split, the accepted fraction is within `ν` of `1/2`. -/
def Balanced (f : Cslib.BooleanFunction n) (K : Nat) (ν : ℝ) : Prop :=
  ∀ (U : Finset (Fin n)) (P : Finset (U → Bool)) (Q : Finset (↥Uᶜ → Bool)),
    K ≤ P.card → K ≤ Q.card →
      (1 / 2 - ν) * (P.card * Q.card) ≤ ((rectangleOnes f U P Q).card : ℝ) ∧
        ((rectangleOnes f U P Q).card : ℝ) ≤ (1 / 2 + ν) * (P.card * Q.card)

namespace Network

variable {V E : Type} (N : Network n V E) [Fintype V] [Fintype E]

/-- The forward-crossing edges of `L`: produced inside `L`, consumed outside. -/
noncomputable def fwdCut (L : Finset V) : Finset E :=
  (N.cut L).filter fun e => N.fst e ∈ L

/-- The backward-crossing edges of `L`: produced outside `L`, consumed inside. -/
noncomputable def bwdCut (L : Finset V) : Finset E :=
  (N.cut L).filter fun e => N.snd e ∈ L

omit [Fintype V] in
theorem mem_fwdCut {L : Finset V} {e : E} : e ∈ N.fwdCut L ↔ e ∈ N.cut L ∧ N.fst e ∈ L := by
  simp [fwdCut]

omit [Fintype V] in
theorem mem_bwdCut {L : Finset V} {e : E} : e ∈ N.bwdCut L ↔ e ∈ N.cut L ∧ N.snd e ∈ L := by
  simp [bwdCut]

omit [Fintype V] in
theorem fwdCut_subset (L : Finset V) : N.fwdCut L ⊆ N.cut L := Finset.filter_subset _ _

omit [Fintype V] in
theorem bwdCut_subset (L : Finset V) : N.bwdCut L ⊆ N.cut L := Finset.filter_subset _ _

omit [Fintype V] in
/-- The cut is the disjoint union of its forward- and backward-crossing edges. -/
theorem card_fwdCut_add_card_bwdCut (L : Finset V) :
    (N.fwdCut L).card + (N.bwdCut L).card = (N.cut L).card := by
  have h : (N.cut L).filter (fun e => N.snd e ∈ L) = (N.cut L).filter fun e => ¬ N.fst e ∈ L := by
    ext e
    simp only [Finset.mem_filter, Multigraph.mem_cut]
    tauto
  rw [fwdCut, bwdCut, h]
  exact Finset.card_filter_add_card_filter_not _

/-- Every accepted input has exactly one satisfying assignment. -/
def Unambiguous : Prop :=
  ∀ (x : Fin n → Bool) (α α' : E → Bool), N.Satisfies x α → N.Satisfies x α' → α = α'

/-- The inputs read in `L` and the backward-crossing bits determine the cut. -/
def ForwardDetermined : Prop :=
  ∀ (L : Finset V) (x x' : Fin n → Bool) (α α' : E → Bool),
    N.Satisfies x α → N.Satisfies x' α' → (∀ j ∈ N.past L, x j = x' j) →
    (∀ e ∈ N.bwdCut L, α e = α' e) → ∀ e ∈ N.cut L, α e = α' e

/-- The inputs read outside `L` and the forward-crossing bits determine the cut. -/
def BackwardDetermined : Prop :=
  ∀ (L : Finset V) (x x' : Fin n → Bool) (α α' : E → Bool),
    N.Satisfies x α → N.Satisfies x' α' → (∀ j ∈ N.read, j ∉ N.past L → x j = x' j) →
    (∀ e ∈ N.fwdCut L, α e = α' e) → ∀ e ∈ N.cut L, α e = α' e

/-- Gluing a consistent past and future gives a satisfying assignment that
agrees with the cut assignment on the cut. -/
theorem exists_satisfies_glue {L : Finset V} {σ : E → Bool}
    {p : ↥(N.past L) → Bool} (hp : p ∈ N.pastSet L σ)
    {q : ↥(N.past L)ᶜ → Bool} (hq : q ∈ N.futureSet L σ) :
    ∃ γ : E → Bool, N.Satisfies (glue (N.past L) p q) γ ∧ ∀ e ∈ N.cut L, γ e = σ e := by
  obtain ⟨α, checksL, agreeα, portsα⟩ := N.mem_pastSet.mp hp
  obtain ⟨β, checksR, agreeβ, portsβ⟩ := N.mem_futureSet.mp hq
  let γ : E → Bool := fun e => if N.fst e ∈ L ∨ N.snd e ∈ L then α e else β e
  have cutEq : ∀ e ∈ N.cut L, α e = β e := fun e he => (agreeα e he).trans (agreeβ e he).symm
  have γα : ∀ e, (N.fst e ∈ L ∨ N.snd e ∈ L) → γ e = α e := fun e he => by simp [γ, he]
  have γβ : ∀ v ∉ L, ∀ e, (N.fst e = v ∨ N.snd e = v) → γ e = β e := by
    intro v hv e he
    by_cases touches : N.fst e ∈ L ∨ N.snd e ∈ L
    · rw [γα e touches]
      apply cutEq
      rw [Multigraph.mem_cut]
      rcases he with rfl | rfl <;> tauto
    · simp [γ, touches]
  refine ⟨γ, ⟨fun v => ?_, fun j hj => ?_⟩, fun e he => ?_⟩
  · by_cases hv : v ∈ L
    · refine N.check_local v α γ (fun e he => (γα e ?_).symm) (checksL v hv)
      rcases he with rfl | rfl
      · exact Or.inl hv
      · exact Or.inr hv
    · exact N.check_local v β γ (fun e he => (γβ v hv e he).symm) (checksR v hv)
  · by_cases hjL : N.portVertex j ∈ L
    · have hjpast : j ∈ N.past L := N.mem_past.mpr ⟨hj, hjL⟩
      have touches : N.fst (N.portEdge j) ∈ L ∨ N.snd (N.portEdge j) ∈ L := by
        rcases N.port_incident j hj with h | h
        · exact Or.inl (h ▸ hjL)
        · exact Or.inr (h ▸ hjL)
      rw [γα _ touches, portsα ⟨j, hjpast⟩]
      simp [glue, hjpast]
    · have hjpast : j ∉ N.past L := fun h => hjL (N.mem_past.mp h).2
      rw [γβ _ hjL _ (N.port_incident j hj), portsβ ⟨j, Finset.mem_compl.mpr hjpast⟩ hj]
      simp [glue, hjpast]
  · have touches : N.fst e ∈ L ∨ N.snd e ∈ L := by
      rw [Multigraph.mem_cut] at he
      tauto
    rw [γα e touches]
    exact agreeα e he

/-- Gluing is injective: a point of the product is recovered by restriction. -/
theorem glue_injOn (U : Finset (Fin n)) (S : Finset ((U → Bool) × (↥Uᶜ → Bool))) :
    Set.InjOn (fun pq : (U → Bool) × (↥Uᶜ → Bool) => glue U pq.1 pq.2) S := by
  intro pq _ pq' _ h
  simp only at h
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · have := congrFun h i
    simpa using this
  · have := congrFun h i
    simpa using this

/-- **The one-sided count.** For a network with unique satisfying assignments
computing `g`, and a `(K, ν)`-balanced `f`, the accepted inputs of `g` on
which `f` is `1` number at most `(1/2 + ν)` times the accepted inputs plus
the thin-rectangle mass at the cut of `L`. -/
theorem card_accepting_inter_le {g : Cslib.BooleanFunction n} (hg : N.Computes g)
    (unique : N.Unambiguous) (fwd : N.ForwardDetermined) (bwd : N.BackwardDetermined)
    {f : Cslib.BooleanFunction n} {K : Nat} {ν : ℝ} (hν : 0 ≤ ν) (hbal : Balanced f K ν)
    (L : Finset V) :
    ((accepting g ∩ accepting f).card : ℝ) ≤ (1 / 2 + ν) * (accepting g).card +
      ((K - 1 : Nat) : ℝ) * (2 ^ (n - (N.past L).card + (N.fwdCut L).card) +
        2 ^ ((N.past L).card + (N.bwdCut L).card)) := by
  have choice : ∀ x ∈ accepting g, ∃ α, N.Satisfies x α :=
    fun x hx => (hg x).mp (mem_accepting.mp hx)
  choose! α hα using choice
  set U := N.past L with hU
  set A := accepting g with hA
  -- The cut assignment of an accepted input, extended by `false` off the cut.
  let key : (Fin n → Bool) → (E → Bool) := fun x e => if e ∈ N.cut L then α x e else false
  let R : (E → Bool) → Finset (Fin n → Bool) := fun σ => A.filter fun x => key x = σ
  let P : (E → Bool) → Finset (U → Bool) := fun σ => N.pastSet L σ
  let Q : (E → Bool) → Finset (↥Uᶜ → Bool) := fun σ => N.futureSet L σ
  set S := A.image key with hS
  have key_cut : ∀ x, ∀ e ∈ N.cut L, key x e = α x e := fun x e he => by simp [key, he]
  have key_off : ∀ x, ∀ e, e ∉ N.cut L → key x e = false := fun x e he => by simp [key, he]
  have mem_R : ∀ σ x, x ∈ R σ ↔ x ∈ A ∧ key x = σ := fun σ x => by simp [R]
  -- Restrictions of an accepted input lie in the past and future sets of its key.
  have past_mem : ∀ x ∈ A, (fun j : U => x j) ∈ P (key x) := by
    intro x hx
    show (fun j : U => x j) ∈ N.pastSet L (key x)
    rw [N.pastSet_congr (σ' := α x) (fun e he => key_cut x e he)]
    exact N.restrict_mem_pastSet (hα x hx) L
  have future_mem : ∀ x ∈ A, (fun j : ↥Uᶜ => x j) ∈ Q (key x) := by
    intro x hx
    show (fun j : ↥Uᶜ => x j) ∈ N.futureSet L (key x)
    rw [N.futureSet_congr (σ' := α x) (fun e he => key_cut x e he)]
    exact N.restrict_mem_futureSet (hα x hx) L
  -- Gluing a past and a future of a realized key lands in its class.
  have glue_mem : ∀ σ ∈ S, ∀ p ∈ P σ, ∀ q ∈ Q σ, glue U p q ∈ R σ := by
    intro σ hσ p hp q hq
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hσ
    obtain ⟨γ, hγ, hγcut⟩ := N.exists_satisfies_glue hp hq
    have hy : glue U p q ∈ A := mem_accepting.mpr ((hg _).mpr ⟨γ, hγ⟩)
    refine (mem_R _ _).mpr ⟨hy, funext fun e => ?_⟩
    by_cases he : e ∈ N.cut L
    · rw [key_cut _ e he, key_cut x₀ e he]
      have := unique _ _ _ (hα _ hy) hγ
      rw [this, hγcut e he, key_cut x₀ e he]
    · rw [key_off _ e he, key_off x₀ e he]
  -- Each class is the glued rectangle.
  have R_eq : ∀ σ ∈ S, R σ = (P σ ×ˢ Q σ).image fun pq => glue U pq.1 pq.2 := by
    intro σ hσ
    ext x
    constructor
    · intro hx
      obtain ⟨hxA, hkey⟩ := (mem_R σ x).mp hx
      refine Finset.mem_image.mpr ⟨(fun j : U => x j, fun j : ↥Uᶜ => x j), ?_, glue_restrict U x⟩
      rw [Finset.mem_product]
      exact ⟨hkey ▸ past_mem x hxA, hkey ▸ future_mem x hxA⟩
    · intro hx
      obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_product] at hpq
      exact glue_mem σ hσ p hpq.1 q hpq.2
  have card_R : ∀ σ ∈ S, (R σ).card = (P σ).card * (Q σ).card := by
    intro σ hσ
    rw [R_eq σ hσ, Finset.card_image_of_injOn (glue_injOn U _), Finset.card_product]
  -- The accepted inputs of `f` in a class are the accepted points of its rectangle.
  have ones_R : ∀ σ ∈ S, (R σ ∩ accepting f).card = (rectangleOnes f U (P σ) (Q σ)).card := by
    intro σ hσ
    rw [R_eq σ hσ]
    have : ((P σ ×ˢ Q σ).image fun pq => glue U pq.1 pq.2) ∩ accepting f =
        (rectangleOnes f U (P σ) (Q σ)).image fun pq => glue U pq.1 pq.2 := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_product, mem_accepting,
        rectangleOnes, Finset.mem_filter]
      constructor
      · rintro ⟨⟨⟨p, q⟩, hpq, rfl⟩, hf⟩
        exact ⟨(p, q), ⟨hpq, hf⟩, rfl⟩
      · rintro ⟨⟨p, q⟩, ⟨hpq, hf⟩, rfl⟩
        exact ⟨⟨(p, q), hpq, rfl⟩, hf⟩
    rw [this, Finset.card_image_of_injOn (glue_injOn U _)]
  -- Realized keys are nonempty classes; a past of a realized key and any future
  -- of it glue to an input with that key.
  have realized_past : ∀ σ ∈ S, (P σ).Nonempty := by
    intro σ hσ
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hσ
    exact ⟨_, past_mem x₀ hx₀⟩
  have realized_future : ∀ σ ∈ S, (Q σ).Nonempty := by
    intro σ hσ
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hσ
    exact ⟨_, future_mem x₀ hx₀⟩
  -- A future assignment and the forward-crossing bits determine the key.
  have key_of_future : ∀ σ ∈ S, ∀ σ' ∈ S, ∀ q, q ∈ Q σ → q ∈ Q σ' →
      (∀ e ∈ N.fwdCut L, σ e = σ' e) → σ = σ' := by
    intro σ hσ σ' hσ' q hq hq' hagree
    obtain ⟨p, hp⟩ := realized_past σ hσ
    obtain ⟨p', hp'⟩ := realized_past σ' hσ'
    have hy := glue_mem σ hσ p hp q hq
    have hy' := glue_mem σ' hσ' p' hp' q hq'
    obtain ⟨hyA, hykey⟩ := (mem_R _ _).mp hy
    obtain ⟨hy'A, hy'key⟩ := (mem_R _ _).mp hy'
    have hcut := bwd L _ _ _ _ (hα _ hyA) (hα _ hy'A)
      (fun j _ hj => by
        have hjc : j ∈ Uᶜ := Finset.mem_compl.mpr hj
        show glue U p q j = glue U p' q j
        rw [show j = (⟨j, hjc⟩ : ↥Uᶜ).1 from rfl, glue_apply_compl, glue_apply_compl])
      (fun e he => by
        have he' := N.fwdCut_subset L he
        rw [← key_cut _ e he', ← key_cut _ e he', hykey, hy'key]
        exact hagree e he)
    funext e
    by_cases he : e ∈ N.cut L
    · rw [← hykey, ← hy'key, key_cut _ e he, key_cut _ e he]
      exact hcut e he
    · rw [← hykey, ← hy'key, key_off _ e he, key_off _ e he]
  -- A past assignment and the backward-crossing bits determine the key.
  have key_of_past : ∀ σ ∈ S, ∀ σ' ∈ S, ∀ p, p ∈ P σ → p ∈ P σ' →
      (∀ e ∈ N.bwdCut L, σ e = σ' e) → σ = σ' := by
    intro σ hσ σ' hσ' p hp hp' hagree
    obtain ⟨q, hq⟩ := realized_future σ hσ
    obtain ⟨q', hq'⟩ := realized_future σ' hσ'
    have hy := glue_mem σ hσ p hp q hq
    have hy' := glue_mem σ' hσ' p hp' q' hq'
    obtain ⟨hyA, hykey⟩ := (mem_R _ _).mp hy
    obtain ⟨hy'A, hy'key⟩ := (mem_R _ _).mp hy'
    have hcut := fwd L _ _ _ _ (hα _ hyA) (hα _ hy'A)
      (fun j hj => by
        show glue U p q j = glue U p q' j
        rw [show j = (⟨j, hj⟩ : U).1 from rfl, glue_apply_mem, glue_apply_mem])
      (fun e he => by
        have he' := N.bwdCut_subset L he
        rw [← key_cut _ e he', ← key_cut _ e he', hykey, hy'key]
        exact hagree e he)
    funext e
    by_cases he : e ∈ N.cut L
    · rw [← hykey, ← hy'key, key_cut _ e he, key_cut _ e he]
      exact hcut e he
    · rw [← hykey, ← hy'key, key_off _ e he, key_off _ e he]
  -- Thin classes: summing the large side over the small-side classes.
  have thinP : (∑ σ ∈ S.filter (fun σ => (P σ).card < K), ((Q σ).card : ℝ)) ≤
      2 ^ (n - U.card + (N.fwdCut L).card) := by
    let T := S.filter fun σ => (P σ).card < K
    let φ : (Σ _ : E → Bool, ↥Uᶜ → Bool) → (↥Uᶜ → Bool) × (↥(N.fwdCut L) → Bool) :=
      fun sq => (sq.2, fun e => sq.1 e)
    have inj : Set.InjOn φ ↑(T.sigma Q) := by
      rintro ⟨σ, q⟩ h ⟨σ', q'⟩ h' heq
      rw [Finset.mem_coe, Finset.mem_sigma] at h h'
      simp only [φ, Prod.mk.injEq] at heq
      obtain ⟨rfl, hfwd⟩ := heq
      have : σ = σ' := key_of_future σ (Finset.mem_filter.mp h.1).1 σ'
        (Finset.mem_filter.mp h'.1).1 q h.2 h'.2 fun e he => congrFun hfwd ⟨e, he⟩
      subst this
      rfl
    have hcard : (T.sigma Q).card ≤ 2 ^ (n - U.card + (N.fwdCut L).card) := by
      calc (T.sigma Q).card ≤ (Finset.univ : Finset ((↥Uᶜ → Bool) × (↥(N.fwdCut L) → Bool))).card :=
            Finset.card_le_card_of_injOn φ (fun _ _ => Finset.mem_univ _) inj
        _ = 2 ^ (n - U.card + (N.fwdCut L).card) := by
            rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
              Fintype.card_bool, Fintype.card_coe, Fintype.card_coe, Finset.card_compl,
              Fintype.card_fin, pow_add]
    have : (∑ σ ∈ T, ((Q σ).card : ℝ)) = ((T.sigma Q).card : ℝ) := by
      rw [Finset.card_sigma]
      push_cast
      rfl
    rw [this]
    exact_mod_cast hcard
  have thinQ : (∑ σ ∈ S.filter (fun σ => (Q σ).card < K), ((P σ).card : ℝ)) ≤
      2 ^ (U.card + (N.bwdCut L).card) := by
    let T := S.filter fun σ => (Q σ).card < K
    let φ : (Σ _ : E → Bool, U → Bool) → (U → Bool) × (↥(N.bwdCut L) → Bool) :=
      fun sp => (sp.2, fun e => sp.1 e)
    have inj : Set.InjOn φ ↑(T.sigma P) := by
      rintro ⟨σ, p⟩ h ⟨σ', p'⟩ h' heq
      rw [Finset.mem_coe, Finset.mem_sigma] at h h'
      simp only [φ, Prod.mk.injEq] at heq
      obtain ⟨rfl, hbwd⟩ := heq
      have : σ = σ' := key_of_past σ (Finset.mem_filter.mp h.1).1 σ'
        (Finset.mem_filter.mp h'.1).1 p h.2 h'.2 fun e he => congrFun hbwd ⟨e, he⟩
      subst this
      rfl
    have hcard : (T.sigma P).card ≤ 2 ^ (U.card + (N.bwdCut L).card) := by
      calc (T.sigma P).card ≤ (Finset.univ : Finset ((U → Bool) × (↥(N.bwdCut L) → Bool))).card :=
            Finset.card_le_card_of_injOn φ (fun _ _ => Finset.mem_univ _) inj
        _ = 2 ^ (U.card + (N.bwdCut L).card) := by
            rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
              Fintype.card_bool, Fintype.card_coe, Fintype.card_coe, pow_add]
    have : (∑ σ ∈ T, ((P σ).card : ℝ)) = ((T.sigma P).card : ℝ) := by
      rw [Finset.card_sigma]
      push_cast
      rfl
    rw [this]
    exact_mod_cast hcard
  -- The pointwise bound on each class.
  have pointwise : ∀ σ ∈ S, ((R σ ∩ accepting f).card : ℝ) ≤
      (1 / 2 + ν) * (R σ).card +
        ((K - 1 : Nat) : ℝ) * (if (P σ).card < K then ((Q σ).card : ℝ) else 0) +
        ((K - 1 : Nat) : ℝ) * (if (Q σ).card < K then ((P σ).card : ℝ) else 0) := by
    intro σ hσ
    have hK1 : (0 : ℝ) ≤ ((K - 1 : Nat) : ℝ) := by positivity
    have hR : ((R σ).card : ℝ) = (P σ).card * (Q σ).card := by exact_mod_cast card_R σ hσ
    have hones : ((R σ ∩ accepting f).card : ℝ) = (rectangleOnes f U (P σ) (Q σ)).card := by
      exact_mod_cast ones_R σ hσ
    have hle : ((R σ ∩ accepting f).card : ℝ) ≤ (R σ).card := by
      exact_mod_cast Finset.card_le_card Finset.inter_subset_left
    by_cases hP : (P σ).card < K
    · -- Small past side: at most `K - 1` rows.
      have hPle : ((P σ).card : ℝ) ≤ ((K - 1 : Nat) : ℝ) := by
        exact_mod_cast Nat.le_sub_one_of_lt hP
      have hQ0 : (0 : ℝ) ≤ (Q σ).card := by positivity
      rw [ite_eq_left hP]
      have : ((R σ).card : ℝ) ≤ ((K - 1 : Nat) : ℝ) * (Q σ).card := by
        rw [hR]
        exact mul_le_mul_of_nonneg_right hPle hQ0
      have hR0 : (0 : ℝ) ≤ (1 / 2 + ν) * (R σ).card := by positivity
      have h3 : (0 : ℝ) ≤ ((K - 1 : Nat) : ℝ) * (if (Q σ).card < K then ((P σ).card : ℝ) else 0) := by
        split_ifs <;> positivity
      linarith
    by_cases hQ : (Q σ).card < K
    · have hQle : ((Q σ).card : ℝ) ≤ ((K - 1 : Nat) : ℝ) := by
        exact_mod_cast Nat.le_sub_one_of_lt hQ
      have hP0 : (0 : ℝ) ≤ (P σ).card := by positivity
      rw [ite_eq_right hP, ite_eq_left hQ]
      have : ((R σ).card : ℝ) ≤ ((K - 1 : Nat) : ℝ) * (P σ).card := by
        rw [hR, mul_comm]
        exact mul_le_mul_of_nonneg_right hQle hP0
      have hR0 : (0 : ℝ) ≤ (1 / 2 + ν) * (R σ).card := by positivity
      linarith
    · -- Both sides large: balance.
      rw [ite_eq_right hP, ite_eq_right hQ]
      have hbal' := (hbal U (P σ) (Q σ) (not_lt.mp hP) (not_lt.mp hQ)).2
      rw [hones, hR]
      linarith
  -- Sum over the classes.
  have partition : ((A ∩ accepting f).card : ℝ) = ∑ σ ∈ S, ((R σ ∩ accepting f).card : ℝ) := by
    have h := Finset.card_eq_sum_card_fiberwise (f := key) (s := A ∩ accepting f) (t := S)
      (fun x hx => Finset.mem_image.mpr ⟨x, (Finset.mem_inter.mp hx).1, rfl⟩)
    rw [h]
    push_cast
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 2
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter, mem_R]
    tauto
  have partitionA : ((A).card : ℝ) = ∑ σ ∈ S, ((R σ).card : ℝ) := by
    have h := Finset.card_eq_sum_card_fiberwise (f := key) (s := A) (t := S)
      (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    rw [h]
    push_cast
    rfl
  calc ((A ∩ accepting f).card : ℝ)
      = ∑ σ ∈ S, ((R σ ∩ accepting f).card : ℝ) := partition
    _ ≤ ∑ σ ∈ S, ((1 / 2 + ν) * (R σ).card +
          ((K - 1 : Nat) : ℝ) * (if (P σ).card < K then ((Q σ).card : ℝ) else 0) +
          ((K - 1 : Nat) : ℝ) * (if (Q σ).card < K then ((P σ).card : ℝ) else 0)) :=
        Finset.sum_le_sum pointwise
    _ = (1 / 2 + ν) * ∑ σ ∈ S, ((R σ).card : ℝ) +
          ((K - 1 : Nat) : ℝ) * ∑ σ ∈ S.filter (fun σ => (P σ).card < K), ((Q σ).card : ℝ) +
          ((K - 1 : Nat) : ℝ) * ∑ σ ∈ S.filter (fun σ => (Q σ).card < K), ((P σ).card : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum, Finset.sum_filter, Finset.sum_filter]
        simp only [mul_ite, mul_zero]
    _ ≤ (1 / 2 + ν) * (accepting g).card +
          ((K - 1 : Nat) : ℝ) * (2 ^ (n - (N.past L).card + (N.fwdCut L).card) +
            2 ^ ((N.past L).card + (N.bwdCut L).card)) := by
        rw [← partitionA]
        have hK1 : (0 : ℝ) ≤ ((K - 1 : Nat) : ℝ) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left thinP hK1, mul_le_mul_of_nonneg_left thinQ hK1]

end Network

end Cutwidth
end Algebraic
