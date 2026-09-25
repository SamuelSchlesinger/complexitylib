/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Rectangle
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Multigraph
public import Mathlib.Data.Finset.Max

/-!
# Constraint networks and the cut-counting lemma

A `Network` is a multigraph whose vertices carry local checks on the bits
written on their incident edges, together with a port for each input variable
read by the network: a vertex and an incident edge that must carry the
variable's value. The network computes `f` when the accepted inputs are exactly
those for which some edge assignment satisfies every check and every port.

For a vertex ordering, the bits on a prefix cut summarize what the processed
part of the network remembers. The past assignments consistent with a cut
assignment and the future assignments consistent with it form a one-rectangle
of `f` (`accepted_of_mem_pastSet_of_mem_futureSet`). Charging every accepted
input to the first vertex at which its past set becomes large, the
cut-counting lemma `card_accepting_le` bounds the number of accepted inputs of
a `K`-rectangle-free function by `|V| · 2 ^ (w + 3) · (K - 1) ^ 2`, where `w`
bounds every prefix cut and each vertex has at most three incident edges.
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth

open scoped Classical

/-- A constraint network over `n` input variables: a multigraph with a local
check at every vertex and a port for every variable it reads. -/
structure Network (n : Nat) (V E : Type) extends Multigraph V E where
  /-- The local check of a vertex on an assignment of bits to edges. -/
  Check : V → (E → Bool) → Prop
  /-- A check depends only on the bits of the incident edges. -/
  check_local : ∀ v (α β : E → Bool),
    (∀ e, fst e = v ∨ snd e = v → α e = β e) → Check v α → Check v β
  /-- The variables read by the network. -/
  read : Finset (Fin n)
  /-- The vertex at which a variable is read. Irrelevant outside `read`. -/
  portVertex : Fin n → V
  /-- The edge carrying a variable's value. Irrelevant outside `read`. -/
  portEdge : Fin n → E
  /-- The port edge of a read variable is incident to its port vertex. -/
  port_incident : ∀ j ∈ read, fst (portEdge j) = portVertex j ∨ snd (portEdge j) = portVertex j

namespace Network

variable {n : Nat} {V E : Type} (N : Network n V E)

/-- An edge assignment satisfies every check and carries the input on every port. -/
def Satisfies (x : Fin n → Bool) (α : E → Bool) : Prop :=
  (∀ v, N.Check v α) ∧ ∀ j ∈ N.read, α (N.portEdge j) = x j

/-- The accepted inputs are those with a satisfying edge assignment. -/
def Computes (f : Cslib.BooleanFunction n) : Prop :=
  ∀ x, f x = true ↔ ∃ α, N.Satisfies x α

/-- A computed function depends only on the variables the network reads. -/
theorem Computes.dependsOnlyOn {f : Cslib.BooleanFunction n} (h : N.Computes f) :
    DependsOnlyOn f N.read := by
  intro x y agree
  apply Bool.eq_iff_iff.mpr
  rw [h x, h y]
  constructor <;> rintro ⟨α, checks, ports⟩ <;> refine ⟨α, checks, fun j hj => ?_⟩
  · rw [ports j hj, agree j hj]
  · rw [ports j hj, agree j hj]

/-- The variables read at a vertex of `L`. -/
noncomputable def past (L : Finset V) : Finset (Fin n) :=
  N.read.filter fun j => N.portVertex j ∈ L

theorem mem_past {L : Finset V} {j : Fin n} :
    j ∈ N.past L ↔ j ∈ N.read ∧ N.portVertex j ∈ L := by
  simp [past]

@[simp] theorem past_empty : N.past ∅ = ∅ := by
  ext j
  simp [mem_past]

@[simp] theorem past_univ [Fintype V] : N.past Finset.univ = N.read := by
  ext j
  simp [mem_past]

section Finite

variable [Fintype V] [Fintype E]

/-- The past assignments consistent with a cut assignment: assignments to the
variables read in `L` extended by an edge assignment satisfying the checks of
`L` and agreeing with `σ` on the cut. -/
noncomputable def pastSet (L : Finset V) (σ : E → Bool) : Finset (↥(N.past L) → Bool) :=
  Finset.univ.filter fun p => ∃ α : E → Bool,
    (∀ v ∈ L, N.Check v α) ∧ (∀ e ∈ N.cut L, α e = σ e) ∧
      ∀ j : ↥(N.past L), α (N.portEdge j) = p j

/-- The future assignments consistent with a cut assignment: assignments to the
remaining variables extended by an edge assignment satisfying the checks
outside `L`, agreeing with `σ` on the cut, and carrying the read variables. -/
noncomputable def futureSet (L : Finset V) (σ : E → Bool) :
    Finset (↥(N.past L)ᶜ → Bool) :=
  Finset.univ.filter fun q => ∃ β : E → Bool,
    (∀ v ∉ L, N.Check v β) ∧ (∀ e ∈ N.cut L, β e = σ e) ∧
      ∀ j : ↥(N.past L)ᶜ, j.1 ∈ N.read → β (N.portEdge j) = q j

theorem mem_pastSet {L : Finset V} {σ : E → Bool} {p : ↥(N.past L) → Bool} :
    p ∈ N.pastSet L σ ↔ ∃ α : E → Bool,
      (∀ v ∈ L, N.Check v α) ∧ (∀ e ∈ N.cut L, α e = σ e) ∧
        ∀ j : ↥(N.past L), α (N.portEdge j) = p j := by
  simp [pastSet]

theorem mem_futureSet {L : Finset V} {σ : E → Bool} {q : ↥(N.past L)ᶜ → Bool} :
    q ∈ N.futureSet L σ ↔ ∃ β : E → Bool,
      (∀ v ∉ L, N.Check v β) ∧ (∀ e ∈ N.cut L, β e = σ e) ∧
        ∀ j : ↥(N.past L)ᶜ, j.1 ∈ N.read → β (N.portEdge j) = q j := by
  simp [futureSet]

/-- The past set depends on the cut assignment only through the cut. -/
theorem pastSet_congr {L : Finset V} {σ σ' : E → Bool}
    (h : ∀ e ∈ N.cut L, σ e = σ' e) : N.pastSet L σ = N.pastSet L σ' := by
  ext p
  rw [mem_pastSet, mem_pastSet]
  constructor <;> rintro ⟨α, checks, agree, ports⟩ <;> refine ⟨α, checks, fun e he => ?_, ports⟩
  · rw [agree e he, h e he]
  · rw [agree e he, h e he]

/-- The future set depends on the cut assignment only through the cut. -/
theorem futureSet_congr {L : Finset V} {σ σ' : E → Bool}
    (h : ∀ e ∈ N.cut L, σ e = σ' e) : N.futureSet L σ = N.futureSet L σ' := by
  ext q
  rw [mem_futureSet, mem_futureSet]
  constructor <;> rintro ⟨β, checks, agree, ports⟩ <;> refine ⟨β, checks, fun e he => ?_, ports⟩
  · rw [agree e he, h e he]
  · rw [agree e he, h e he]

/-- The past of an accepted input lies in the past set of its own assignment. -/
theorem restrict_mem_pastSet {x : Fin n → Bool} {α : E → Bool} (h : N.Satisfies x α)
    (L : Finset V) : (fun j : ↥(N.past L) => x j) ∈ N.pastSet L α :=
  N.mem_pastSet.mpr ⟨α, fun v _ => h.1 v, fun _ _ => rfl,
    fun j => h.2 j (N.mem_past.mp j.2).1⟩

/-- The future of an accepted input lies in the future set of its own assignment. -/
theorem restrict_mem_futureSet {x : Fin n → Bool} {α : E → Bool} (h : N.Satisfies x α)
    (L : Finset V) : (fun j : ↥(N.past L)ᶜ => x j) ∈ N.futureSet L α :=
  N.mem_futureSet.mpr ⟨α, fun v _ => h.1 v, fun _ _ => rfl, fun j hj => h.2 j hj⟩

/-- Before any vertex is processed, only the empty past assignment exists. -/
theorem card_pastSet_empty_le (σ : E → Bool) : (N.pastSet ∅ σ).card ≤ 1 := by
  calc (N.pastSet ∅ σ).card ≤ Fintype.card (↥(N.past ∅) → Bool) := Finset.card_le_univ _
    _ = 1 := by simp

/-- A consistent past and future together form an accepted input: the past and
future sets of a cut assignment form a one-rectangle. -/
theorem accepted_of_mem_pastSet_of_mem_futureSet {f : Cslib.BooleanFunction n}
    (hf : N.Computes f) {L : Finset V} {σ : E → Bool}
    {p : ↥(N.past L) → Bool} (hp : p ∈ N.pastSet L σ)
    {q : ↥(N.past L)ᶜ → Bool} (hq : q ∈ N.futureSet L σ) :
    f (glue (N.past L) p q) = true := by
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
  refine (hf _).mpr ⟨γ, fun v => ?_, fun j hj => ?_⟩
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

/-- Every accepted input restricts into a fixed past set of the whole vertex
set, so a small final past set forces few accepted inputs. -/
theorem card_accepting_lt_of_card_pastSet_univ_lt {f : Cslib.BooleanFunction n}
    (hf : N.Computes f) {K : Nat}
    (small : (N.pastSet Finset.univ fun _ => false).card < K) :
    (accepting f).card < K * 2 ^ (n - N.read.card) := by
  let φ : (Fin n → Bool) → (↥(N.past Finset.univ) → Bool) × (↥(N.past Finset.univ)ᶜ → Bool) :=
    fun x => (fun j => x j, fun j => x j)
  have inj : Function.Injective φ := by
    intro x y h
    have := congrArg (fun pq : (↥(N.past Finset.univ) → Bool) × (↥(N.past Finset.univ)ᶜ → Bool) =>
      glue (N.past Finset.univ) pq.1 pq.2) h
    simpa [φ, glue_restrict] using this
  have maps : Set.MapsTo φ ↑(accepting f)
      ↑((N.pastSet Finset.univ fun _ => false) ×ˢ
        (Finset.univ : Finset (↥(N.past Finset.univ)ᶜ → Bool))) := by
    intro x hx
    obtain ⟨α, hα⟩ := (hf x).mp (mem_accepting.mp hx)
    rw [Finset.mem_coe, Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [N.pastSet_congr (σ' := α) (by simp)]
    exact N.restrict_mem_pastSet hα _
  have complCard : ((N.past Finset.univ)ᶜ).card = n - N.read.card := by
    rw [Finset.card_compl, Fintype.card_fin, past_univ]
  calc (accepting f).card
      ≤ ((N.pastSet Finset.univ fun _ => false) ×ˢ
          (Finset.univ : Finset (↥(N.past Finset.univ)ᶜ → Bool))).card :=
        Finset.card_le_card_of_injOn φ maps inj.injOn
    _ = (N.pastSet Finset.univ fun _ => false).card * 2 ^ (n - N.read.card) := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_coe, complCard]
    _ < K * 2 ^ (n - N.read.card) :=
        Nat.mul_lt_mul_of_pos_right small (Nat.two_pow_pos _)

section Ordered

variable [LinearOrder V]

/-- The vertices strictly before `v`. -/
noncomputable def below (v : V) : Finset V :=
  Finset.univ.filter fun u => u < v

/-- The vertices up to and including `v`. -/
noncomputable def upto (v : V) : Finset V :=
  Finset.univ.filter fun u => u ≤ v

theorem mem_below {u v : V} : u ∈ below v ↔ u < v := by simp [below]

theorem mem_upto {u v : V} : u ∈ upto v ↔ u ≤ v := by simp [upto]

theorem isLowerSet_below (v : V) : IsLowerSet ((below v : Finset V) : Set V) := by
  intro a b hba ha
  rw [Finset.mem_coe, mem_below] at *
  exact lt_of_le_of_lt hba ha

theorem isLowerSet_upto (v : V) : IsLowerSet ((upto v : Finset V) : Set V) := by
  intro a b hba ha
  rw [Finset.mem_coe, mem_upto] at *
  exact hba.trans ha

/-- The prefix through the last vertex is everything. -/
theorem upto_max' (h : (Finset.univ : Finset V).Nonempty) :
    upto (Finset.univ.max' h) = Finset.univ := by
  ext u
  simp only [mem_upto, Finset.mem_univ, iff_true]
  exact Finset.le_max' _ _ (Finset.mem_univ u)

/-- The vertices before `v` are empty or the prefix through an earlier vertex. -/
theorem below_eq_empty_or_exists_upto (v : V) :
    below v = ∅ ∨ ∃ u, u < v ∧ below v = upto u := by
  by_cases h : (below v).Nonempty
  · right
    refine ⟨(below v).max' h, mem_below.mp (Finset.max'_mem _ h), ?_⟩
    ext u
    rw [mem_below, mem_upto]
    constructor
    · intro hu
      exact Finset.le_max' _ _ (mem_below.mpr hu)
    · intro hu
      exact hu.trans_lt (mem_below.mp (Finset.max'_mem _ h))
  · left
    exact Finset.not_nonempty_iff_eq_empty.mp h

/-- Processing one vertex changes the cut only among its incident edges. -/
theorem cut_upto_subset (v : V) : N.cut (upto v) ⊆ N.cut (below v) ∪ N.edgesAt v := by
  intro e he
  rw [Finset.mem_union, Multigraph.mem_cut, Multigraph.mem_edgesAt]
  rw [Multigraph.mem_cut] at he
  by_cases h₁ : N.fst e = v
  · exact Or.inr (Or.inl h₁)
  by_cases h₂ : N.snd e = v
  · exact Or.inr (Or.inr h₂)
  left
  rw [mem_below, mem_below]
  rw [mem_upto, mem_upto] at he
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne]
  tauto

end Ordered

/-- **The cut-counting lemma.** For a network computing a `K`-rectangle-free
function, with every vertex of degree at most three and every prefix cut of
the ordering of size at most `w`, either the final past set is small, so that
fewer than `K · 2 ^ (n - |read|)` inputs are accepted, or at most
`|V| · 2 ^ (w + 3) · (K - 1) ^ 2` inputs are accepted. -/
theorem card_accepting_le [LinearOrder V] [Nonempty V]
    {f : Cslib.BooleanFunction n} (hf : N.Computes f) (hdeg : N.MaxDegreeLE 3)
    {w : Nat} (hw : ∀ v, (N.cut (below v)).card ≤ w)
    {K : Nat} (hK : 1 < K) (hrect : RectangleFree f K) :
    (accepting f).card < K * 2 ^ (n - N.read.card) ∨
      (accepting f).card ≤ Fintype.card V * 2 ^ (w + 3) * (K - 1) ^ 2 := by
  have choice : ∀ x ∈ accepting f, ∃ α, N.Satisfies x α :=
    fun x hx => (hf x).mp (mem_accepting.mp hx)
  choose! α hα using choice
  by_cases hbig : (N.pastSet Finset.univ fun _ => false).card < K
  · exact Or.inl (N.card_accepting_lt_of_card_pastSet_univ_lt hf hbig)
  right
  rw [not_lt] at hbig
  have univ_nonempty : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty
  -- The set of vertices at which the past set of `x` has become large.
  let big : (Fin n → Bool) → Finset V := fun x =>
    Finset.univ.filter fun v => K ≤ (N.pastSet (upto v) (α x)).card
  have big_nonempty : ∀ x ∈ accepting f, (big x).Nonempty := by
    intro x _
    refine ⟨Finset.univ.max' univ_nonempty, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [upto_max', N.pastSet_congr (σ' := fun _ => false) (by simp)]
    exact hbig
  -- The first such vertex.
  let first : (Fin n → Bool) → V := fun x =>
    if h : (big x).Nonempty then (big x).min' h else Classical.arbitrary V
  have first_eq : ∀ x, (hx : x ∈ accepting f) → first x = (big x).min' (big_nonempty x hx) := by
    intro x hx
    simp [first, big_nonempty x hx]
  have first_big : ∀ x ∈ accepting f, K ≤ (N.pastSet (upto (first x)) (α x)).card := by
    intro x hx
    have mem := Finset.min'_mem (big x) (big_nonempty x hx)
    rw [first_eq x hx]
    exact (Finset.mem_filter.mp mem).2
  have first_min : ∀ x ∈ accepting f, ∀ u, u < first x →
      (N.pastSet (upto u) (α x)).card < K := by
    intro x hx u hu
    by_contra h
    rw [not_lt] at h
    have mem : u ∈ big x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    have := Finset.min'_le (big x) u mem
    rw [first_eq x hx] at hu
    exact absurd hu (not_lt.mpr this)
  have below_small : ∀ x ∈ accepting f, (N.pastSet (below (first x)) (α x)).card < K := by
    intro x hx
    rcases below_eq_empty_or_exists_upto (first x) with h | ⟨u, hu, h⟩
    · rw [h]
      exact lt_of_le_of_lt (N.card_pastSet_empty_le _) hK
    · rw [h]
      exact first_min x hx u hu
  have future_small : ∀ x ∈ accepting f,
      (N.futureSet (upto (first x)) (α x)).card < K := by
    intro x hx
    rcases hrect (N.past (upto (first x))) (N.pastSet _ (α x)) (N.futureSet _ (α x))
      (fun p hp q hq => N.accepted_of_mem_pastSet_of_mem_futureSet hf hp hq) with h | h
    · exact absurd h (not_lt.mpr (first_big x hx))
    · exact h
  -- The edges whose bits determine the charge: the cut before the first vertex
  -- and the edges incident to it.
  let D : V → Finset E := fun v => N.cut (below v) ∪ N.edgesAt v
  have D_card : ∀ v, (D v).card ≤ w + 3 := fun v =>
    (Finset.card_union_le _ _).trans (add_le_add (hw v) (hdeg v))
  have cut_upto_subset_D : ∀ v, N.cut (upto v) ⊆ D v := fun v => N.cut_upto_subset v
  have cut_below_subset_D : ∀ v, N.cut (below v) ⊆ D v := fun v => Finset.subset_union_left
  let key : (Fin n → Bool) → V × (E → Bool) := fun x =>
    (first x, fun e => if e ∈ D (first x) then α x e else false)
  -- Inputs with the same key are determined by a past and a future assignment.
  have fiber : ∀ κ ∈ (accepting f).image key,
      ((accepting f).filter fun x => key x = κ).card ≤ (K - 1) ^ 2 := by
    rintro ⟨v, τ⟩ _
    set F := (accepting f).filter fun x => key x = (v, τ) with hF
    rcases F.eq_empty_or_nonempty with hempty | ⟨x₁, hx₁⟩
    · rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
    have keyed : ∀ x ∈ F, first x = v ∧ ∀ e ∈ D v, α x e = τ e := by
      intro x hx
      have h := (Finset.mem_filter.mp hx).2
      simp only [key, Prod.mk.injEq] at h
      obtain ⟨hv, hτ⟩ := h
      refine ⟨hv, fun e he => ?_⟩
      rw [← hτ]
      simp [hv, he]
    obtain ⟨hx₁acc, _⟩ := Finset.mem_filter.mp hx₁
    obtain ⟨hv₁, hτ₁⟩ := keyed x₁ hx₁
    have agree : ∀ x ∈ F, ∀ e ∈ D v, α x e = α x₁ e := by
      intro x hx e he
      rw [(keyed x hx).2 e he, hτ₁ e he]
    let φ : (Fin n → Bool) → (↥(N.past (below v)) → Bool) × (↥(N.past (upto v))ᶜ → Bool) :=
      fun x => (fun j => x j, fun j => x j)
    have maps : Set.MapsTo φ ↑F
        ↑(N.pastSet (below v) (α x₁) ×ˢ N.futureSet (upto v) (α x₁)) := by
      intro x hx
      have hxacc := (Finset.mem_filter.mp hx).1
      rw [Finset.mem_coe, Finset.mem_product]
      constructor
      · rw [N.pastSet_congr (σ' := α x)
          (fun e he => (agree x hx e (cut_below_subset_D v he)).symm)]
        exact N.restrict_mem_pastSet (hα x hxacc) _
      · rw [N.futureSet_congr (σ' := α x)
          (fun e he => (agree x hx e (cut_upto_subset_D v he)).symm)]
        exact N.restrict_mem_futureSet (hα x hxacc) _
    have inj : Set.InjOn φ F := by
      intro x hx y hy hxy
      have hxacc := (Finset.mem_filter.mp hx).1
      have hyacc := (Finset.mem_filter.mp hy).1
      simp only [φ, Prod.mk.injEq] at hxy
      obtain ⟨hpast, hfuture⟩ := hxy
      funext j
      by_cases h₁ : j ∈ N.past (below v)
      · exact congrFun hpast ⟨j, h₁⟩
      by_cases h₂ : j ∈ N.past (upto v)
      · obtain ⟨hj, hjv⟩ := N.mem_past.mp h₂
        have hv : N.portVertex j = v := by
          apply eq_of_le_of_not_lt (mem_upto.mp hjv)
          intro hlt
          exact h₁ (N.mem_past.mpr ⟨hj, mem_below.mpr hlt⟩)
        have hedge : N.portEdge j ∈ D v :=
          Finset.mem_union_right _ (N.mem_edgesAt.mpr (hv ▸ N.port_incident j hj))
        rw [← (hα x hxacc).2 j hj, ← (hα y hyacc).2 j hj, agree x hx _ hedge, agree y hy _ hedge]
      · exact congrFun hfuture ⟨j, Finset.mem_compl.mpr h₂⟩
    calc F.card ≤ (N.pastSet (below v) (α x₁) ×ˢ N.futureSet (upto v) (α x₁)).card :=
          Finset.card_le_card_of_injOn φ maps inj
      _ = (N.pastSet (below v) (α x₁)).card * (N.futureSet (upto v) (α x₁)).card :=
          Finset.card_product _ _
      _ ≤ (K - 1) * (K - 1) := by
          apply Nat.mul_le_mul
          · exact Nat.le_sub_one_of_lt (hv₁ ▸ below_small x₁ hx₁acc)
          · exact Nat.le_sub_one_of_lt (hv₁ ▸ future_small x₁ hx₁acc)
      _ = (K - 1) ^ 2 := (sq _).symm
  -- Keys are determined by a vertex and the bits on at most `w + 3` edges.
  have image_card : ((accepting f).image key).card ≤ Fintype.card V * 2 ^ (w + 3) := by
    let ψ : V × (E → Bool) → Σ v : V, (↥(D v) → Bool) := fun vτ => ⟨vτ.1, fun e => vτ.2 e⟩
    have inj : Set.InjOn ψ ((accepting f).image key) := by
      rintro ⟨v, τ⟩ hmem ⟨v', τ'⟩ hmem' heq
      simp only [ψ, Sigma.mk.inj_iff] at heq
      obtain ⟨rfl, hτ⟩ := heq
      have hτ' := eq_of_heq hτ
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hmem
      obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hmem'
      simp only [key, Prod.mk.injEq] at hx hy
      obtain ⟨hxv, hxτ⟩ := hx
      obtain ⟨hyv, hyτ⟩ := hy
      refine Prod.ext rfl ?_
      funext e
      by_cases he : e ∈ D v
      · exact congrFun hτ' ⟨e, he⟩
      · rw [← hxτ, ← hyτ]
        simp [hxv, hyv, he]
    calc ((accepting f).image key).card
        ≤ (Finset.univ : Finset (Σ v : V, (↥(D v) → Bool))).card :=
          Finset.card_le_card_of_injOn ψ (fun _ _ => Finset.mem_univ _) inj
      _ = ∑ v : V, 2 ^ (D v).card := by
          rw [Finset.card_univ, Fintype.card_sigma]
          simp [Fintype.card_bool]
      _ ≤ ∑ _v : V, 2 ^ (w + 3) :=
          Finset.sum_le_sum fun v _ => Nat.pow_le_pow_right two_pos (D_card v)
      _ = Fintype.card V * 2 ^ (w + 3) := by simp [Finset.sum_const, Finset.card_univ]
  calc (accepting f).card ≤ (K - 1) ^ 2 * ((accepting f).image key).card :=
        Finset.card_le_mul_card_image _ _ fiber
    _ ≤ (K - 1) ^ 2 * (Fintype.card V * 2 ^ (w + 3)) := Nat.mul_le_mul_left _ image_card
    _ = Fintype.card V * 2 ^ (w + 3) * (K - 1) ^ 2 := by ring

end Finite

end Network

end Cutwidth
end Algebraic
