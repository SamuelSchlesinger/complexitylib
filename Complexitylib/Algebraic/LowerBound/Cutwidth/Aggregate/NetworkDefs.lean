/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Network

/-!
# Constraint networks with a commutative aggregate

Local contributions multiply in a finite commutative monoid. The final acceptance
predicate may inspect the product. No cancellation or inverses are required.
-/

@[expose] public section

namespace Algebraic.Cutwidth

open scoped Classical

/-- A local constraint network augmented with one commutative aggregate. -/
structure AggregateNetwork (n : Nat) (V E M : Type) [CommMonoid M]
    extends Network n V E where
  /-- The contribution made at a vertex. -/
  contribution : V → (E → Bool) → M
  /-- A contribution depends only on incident edge values. -/
  contribution_local : ∀ v (α β : E → Bool),
    (∀ e, fst e = v ∨ snd e = v → α e = β e) → contribution v α = contribution v β
  /-- The test on the final aggregate. -/
  Accept : M → Prop

namespace AggregateNetwork

variable {n : Nat} {V E M : Type} [CommMonoid M] (N : AggregateNetwork n V E M)

/-- Aggregate of contributions from a set of processed vertices. -/
noncomputable def accumulated (L : Finset V) (α : E → Bool) : M :=
  ∏ v ∈ L, N.contribution v α

@[simp] theorem accumulated_empty (α : E → Bool) : N.accumulated ∅ α = 1 := by
  simp [accumulated]

section Finite

variable [Fintype V] [Fintype E]

/-- A satisfying edge assignment obeys the local network and global aggregate test. -/
def Satisfies (x : Fin n → Bool) (α : E → Bool) : Prop :=
  N.toNetwork.Satisfies x α ∧ N.Accept (N.accumulated Finset.univ α)

/-- The network accepts exactly the true inputs of the Boolean function. -/
def Computes (f : Cslib.BooleanFunction n) : Prop :=
  ∀ x, f x = true ↔ ∃ α, N.Satisfies x α

/-- Past inputs compatible with a cut assignment and an exact past aggregate. -/
noncomputable def pastSet (L : Finset V) (σ : E → Bool) (m : M) :
    Finset (↥(N.toNetwork.past L) → Bool) :=
  Finset.univ.filter fun p => ∃ α : E → Bool,
    (∀ v ∈ L, N.Check v α) ∧ (∀ e ∈ N.cut L, α e = σ e) ∧
      (∀ j : ↥(N.toNetwork.past L), α (N.portEdge j) = p j) ∧ N.accumulated L α = m

/-- Future inputs compatible with the past aggregate and final acceptance. -/
noncomputable def futureSet (L : Finset V) (σ : E → Bool) (m : M) :
    Finset (↥(N.toNetwork.past L)ᶜ → Bool) :=
  Finset.univ.filter fun q => ∃ β : E → Bool,
    (∀ v ∉ L, N.Check v β) ∧ (∀ e ∈ N.cut L, β e = σ e) ∧
      (∀ j : ↥(N.toNetwork.past L)ᶜ, j.1 ∈ N.read → β (N.portEdge j) = q j) ∧
        N.Accept (m * N.accumulated Lᶜ β)

theorem mem_pastSet {L : Finset V} {σ : E → Bool} {m : M}
    {p : ↥(N.toNetwork.past L) → Bool} :
    p ∈ N.pastSet L σ m ↔ ∃ α : E → Bool,
      (∀ v ∈ L, N.Check v α) ∧ (∀ e ∈ N.cut L, α e = σ e) ∧
        (∀ j : ↥(N.toNetwork.past L), α (N.portEdge j) = p j) ∧ N.accumulated L α = m := by
  simp [pastSet]

theorem mem_futureSet {L : Finset V} {σ : E → Bool} {m : M}
    {q : ↥(N.toNetwork.past L)ᶜ → Bool} :
    q ∈ N.futureSet L σ m ↔ ∃ β : E → Bool,
      (∀ v ∉ L, N.Check v β) ∧ (∀ e ∈ N.cut L, β e = σ e) ∧
        (∀ j : ↥(N.toNetwork.past L)ᶜ, j.1 ∈ N.read → β (N.portEdge j) = q j) ∧
          N.Accept (m * N.accumulated Lᶜ β) := by
  simp [futureSet]

omit [Fintype E] in
theorem accumulated_mul_compl (L : Finset V) (α : E → Bool) :
    N.accumulated L α * N.accumulated Lᶜ α = N.accumulated Finset.univ α := by
  exact Finset.prod_mul_prod_compl L (fun v => N.contribution v α)

/-- The past set uses only the edge values on the cut. -/
theorem pastSet_congr {L : Finset V} {σ σ' : E → Bool} {m : M}
    (h : ∀ e ∈ N.cut L, σ e = σ' e) : N.pastSet L σ m = N.pastSet L σ' m := by
  ext p
  rw [mem_pastSet, mem_pastSet]
  constructor <;> rintro ⟨α, checks, agree, ports, hm⟩ <;>
    refine ⟨α, checks, fun e he => ?_, ports, hm⟩
  · rw [agree e he, h e he]
  · rw [agree e he, h e he]

/-- The future set uses only the edge values on the cut. -/
theorem futureSet_congr {L : Finset V} {σ σ' : E → Bool} {m : M}
    (h : ∀ e ∈ N.cut L, σ e = σ' e) : N.futureSet L σ m = N.futureSet L σ' m := by
  ext q
  rw [mem_futureSet, mem_futureSet]
  constructor <;> rintro ⟨β, checks, agree, ports, hm⟩ <;>
    refine ⟨β, checks, fun e he => ?_, ports, hm⟩
  · rw [agree e he, h e he]
  · rw [agree e he, h e he]

/-- A satisfying input supplies a member of its own past set. -/
theorem restrict_mem_pastSet {x : Fin n → Bool} {α : E → Bool} (h : N.Satisfies x α)
    (L : Finset V) :
    (fun j : ↥(N.toNetwork.past L) => x j) ∈ N.pastSet L α (N.accumulated L α) :=
  N.mem_pastSet.mpr ⟨α, fun v _ => h.1.1 v, fun _ _ => rfl,
    fun j => h.1.2 j (N.toNetwork.mem_past.mp j.2).1, rfl⟩

/-- A satisfying input supplies a member of its own future set. -/
theorem restrict_mem_futureSet {x : Fin n → Bool} {α : E → Bool} (h : N.Satisfies x α)
    (L : Finset V) :
    (fun j : ↥(N.toNetwork.past L)ᶜ => x j) ∈ N.futureSet L α (N.accumulated L α) :=
  N.mem_futureSet.mpr ⟨α, fun v _ => h.1.1 v, fun _ _ => rfl,
    fun j hj => h.1.2 j hj, by simpa [N.accumulated_mul_compl] using h.2⟩

/-- The empty past has at most one assignment, for any aggregate. -/
theorem card_pastSet_empty_le (σ : E → Bool) (m : M) : (N.pastSet ∅ σ m).card ≤ 1 := by
  calc (N.pastSet ∅ σ m).card ≤ Fintype.card (↥(N.toNetwork.past ∅) → Bool) :=
      Finset.card_le_univ _
    _ = 1 := by simp

/-- Combining compatible sides is sound because contributions are local and commute. -/
theorem accepted_of_mem_pastSet_of_mem_futureSet {f : Cslib.BooleanFunction n}
    (hf : N.Computes f) {L : Finset V} {σ : E → Bool} {m : M}
    {p : ↥(N.toNetwork.past L) → Bool} (hp : p ∈ N.pastSet L σ m)
    {q : ↥(N.toNetwork.past L)ᶜ → Bool} (hq : q ∈ N.futureSet L σ m) :
    f (glue (N.toNetwork.past L) p q) = true := by
  obtain ⟨α, checksL, agreeα, portsα, accumα⟩ := N.mem_pastSet.mp hp
  obtain ⟨β, checksR, agreeβ, portsβ, acceptβ⟩ := N.mem_futureSet.mp hq
  let γ : E → Bool := fun e => if N.fst e ∈ L ∨ N.snd e ∈ L then α e else β e
  have cutEq : ∀ e ∈ N.cut L, α e = β e :=
    fun e he => (agreeα e he).trans (agreeβ e he).symm
  have γα : ∀ v ∈ L, ∀ e, (N.fst e = v ∨ N.snd e = v) → γ e = α e := by
    intro v hv e he
    have touches : N.fst e ∈ L ∨ N.snd e ∈ L := by
      rcases he with h | h
      · exact Or.inl (h ▸ hv)
      · exact Or.inr (h ▸ hv)
    simp [γ, touches]
  have γβ : ∀ v ∉ L, ∀ e, (N.fst e = v ∨ N.snd e = v) → γ e = β e := by
    intro v hv e he
    by_cases touches : N.fst e ∈ L ∨ N.snd e ∈ L
    · simp only [γ, touches, ite_true]
      apply cutEq
      rw [Multigraph.mem_cut]
      rcases he with rfl | rfl <;> tauto
    · simp [γ, touches]
  refine (hf _).mpr ⟨γ, ⟨fun v => ?_, fun j hj => ?_⟩, ?_⟩
  · by_cases hv : v ∈ L
    · exact N.check_local v α γ (fun e he => (γα v hv e he).symm) (checksL v hv)
    · exact N.check_local v β γ (fun e he => (γβ v hv e he).symm) (checksR v hv)
  · by_cases hjL : N.portVertex j ∈ L
    · have hjpast : j ∈ N.toNetwork.past L := N.toNetwork.mem_past.mpr ⟨hj, hjL⟩
      rw [γα _ hjL _ (N.port_incident j hj), portsα ⟨j, hjpast⟩]
      simp [glue, hjpast]
    · have hjpast : j ∉ N.toNetwork.past L :=
        fun h => hjL (N.toNetwork.mem_past.mp h).2
      rw [γβ _ hjL _ (N.port_incident j hj),
        portsβ ⟨j, Finset.mem_compl.mpr hjpast⟩ hj]
      simp [glue, hjpast]
  · rw [← N.accumulated_mul_compl L γ]
    have left : N.accumulated L γ = m := by
      rw [← accumα]
      exact Finset.prod_congr rfl fun v hv => N.contribution_local v γ α (γα v hv)
    have right : N.accumulated Lᶜ γ = N.accumulated Lᶜ β :=
      Finset.prod_congr rfl fun v hv =>
        N.contribution_local v γ β (γβ v (Finset.mem_compl.mp hv))
    rwa [left, right]

omit [Fintype E] in
/-- Advancing one vertex multiplies the accumulator by its local contribution. -/
theorem accumulated_upto [LinearOrder V] (v : V) (α : E → Bool) :
    N.accumulated (Network.upto v) α =
      N.accumulated (Network.below v) α * N.contribution v α := by
  have hup : Network.upto v = insert v (Network.below v) := by
    ext u
    simp only [Network.mem_upto, Finset.mem_insert, Network.mem_below]
    exact le_iff_eq_or_lt
  rw [hup, accumulated, Finset.prod_insert (by simp [Network.mem_below])]
  exact mul_comm _ _

end Finite
end AggregateNetwork
end Algebraic.Cutwidth
