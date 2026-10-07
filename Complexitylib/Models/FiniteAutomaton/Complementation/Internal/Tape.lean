/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Chain
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Normalization

/-!
# Two-way complementation: tape

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/Tape.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace Complementation.Internal

open scoped SetRel

/-- Chain symbols agree with ordinary zero-based lookup of the nonempty symbol list. -/
theorem chainSymbol_getElem {Sigma : Type*} {m : ℕ} (w : List Sigma) (last : Sigma)
    (c : ChainNode m w.length) :
    chainSymbol w last c = (w ++ [last])[c.position]'(by
      have := c.position_le
      simp only [List.length_append, List.length_singleton]
      omega) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases c with
    | inl q => rfl
    | inr c => simpa only [chainSymbol, ChainNode.position, List.cons_append,
        List.getElem_cons_succ] using ih c

/-- Lookup of the explicitly marked list agrees with the automaton's tape lookup. -/
theorem marked_getElem {Sigma : Type*} (w : List Sigma) (p : Fin (w.length + 2)) :
    ((Sum.inl 0 : Fin 2 ⊕ Sigma) :: (w.map Sum.inr ++ [Sum.inl 1]))[p.val]'(by simp; omega) =
      tapeSymbol w p := by
  obtain ⟨p, hp⟩ := p
  cases p with
  | zero => rfl
  | succ p =>
    by_cases h : p = w.length
    · subst p
      simp [tapeSymbol]
    · have hlt : p < w.length := by omega
      rw [List.getElem_cons_succ, List.getElem_append_left (by simpa using hlt),
        List.getElem_map]
      simp [tapeSymbol, h]

/-- Convert the recursively joined cells and one terminal exit into tape coordinates. -/
noncomputable def ChainNode.exitEquiv (m n : ℕ) :
    (ChainNode m n ⊕ Fin m) ≃ (Fin m × Fin (n + 2)) :=
  Equiv.ofBijective (fun c => match c with
    | .inl v => (v.label, ⟨v.position, by have := v.position_le; omega⟩)
    | .inr q => (q, ⟨n + 1, by omega⟩)) (by
      constructor
      · intro c d h
        have hq := congrArg (fun p : Fin m × Fin (n + 2) => p.1) h
        have hp := congrArg (fun p : Fin m × Fin (n + 2) => p.2.val) h
        cases c with
        | inl c =>
          cases d with
          | inl d => exact congrArg Sum.inl (c.coordinates_injective d hp hq)
          | inr q => have := c.position_le; dsimp at hp; omega
        | inr q =>
          cases d with
          | inl d => have := d.position_le; dsimp at hp; omega
          | inr r => exact congrArg Sum.inr hq
      · rintro ⟨q, p⟩
        by_cases hp : p.val ≤ n
        · obtain ⟨c, hq, hc⟩ := ChainNode.coordinates_surjective q p.val hp
          exact ⟨Sum.inl c, Prod.ext hq (Fin.ext hc)⟩
        · exact ⟨Sum.inr q, Prod.ext rfl (Fin.ext (by change n + 1 = p.val; omega))⟩)

/-- A graph equivalence transports finite paths in both directions. -/
theorem relStar_equiv_iff {V W : Type*} (e : V ≃ W) (R : SetRel V V) (S : SetRel W W)
    (h : ∀ x y, (e x, e y) ∈ S ↔ (x, y) ∈ R) (x y : V) :
    (e x, e y) ∈ relStar S ↔ (x, y) ∈ relStar R := by
  constructor
  · intro hrun
    have hlift := hrun.lift e.symm (p := fun a b => (a, b) ∈ R) (by
      intro a b hab
      apply (h (e.symm a) (e.symm b)).mp
      simpa only [Equiv.apply_symm_apply] using hab)
    change Relation.ReflTransGen (fun a b => (a, b) ∈ R) x y
    simpa only [Function.onFun, Equiv.symm_apply_apply] using hlift
  · exact fun hrun => hrun.lift e (fun a b hab => (h a b).mpr hab)

/-- A terminal block with no outgoing edges is reached by an internal path and one exit. -/
theorem blockRelation_terminal {V Q : Type*} (E : SetRel V V) (O : SetRel V Q)
    (c : V) (q : Q) :
    (Sum.inl c, Sum.inr q) ∈ relStar (blockRelation E O ∅ ∅) ↔
      (c, q) ∈ relStar E ○ O := by
  rw [blockRelation_star_cross]
  simp only [SetRel.empty_comp, Set.empty_union, relStar_empty, SetRel.comp_id]

/-- A cell's scanned symbol depends only on its position. -/
theorem chainSymbol_position {Sigma : Type*} {m : ℕ} (w : List Sigma) (last : Sigma)
    (c d : ChainNode m w.length) (hp : c.position = d.position) :
    chainSymbol w last c = chainSymbol w last d := by
  rw [chainSymbol_getElem, chainSymbol_getElem]
  simp only [hp]

/-- Local moves on the bounded tape, with a final terminal position beyond the last cell. -/
def chainStep {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma) :
    SetRel (Fin m × Fin (w.length + 2)) (Fin m × Fin (w.length + 2)) :=
  {cd | ∃ c : ChainNode m w.length, cd.1.2.val = c.position ∧ ∃ move : Fin 3,
    (cd.1.1, cd.2.1) ∈ moves (chainSymbol w last c) move ∧
      (cd.2.2.val : ℤ) = (cd.1.2.val : ℤ) + (move.val : ℤ) - 1}

/-- The joined network with terminal exits has exactly the bounded tape's local edges. -/
theorem chainStep_exitEquiv {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma)
    (x y : ChainNode m w.length ⊕ Fin m) :
    (ChainNode.exitEquiv m w.length x, ChainNode.exitEquiv m w.length y) ∈
        chainStep moves w last ↔
      (x, y) ∈ blockRelation (chainNetwork moves w last).edge
        (chainNetwork moves w last).rightOut ∅ ∅ := by
  cases x with
  | inl c =>
    cases y with
    | inl d =>
      change (∃ a : ChainNode m w.length, c.position = a.position ∧ ∃ move : Fin 3,
          (c.label, d.label) ∈ moves (chainSymbol w last a) move ∧
            (d.position : ℤ) = (c.position : ℤ) + (move.val : ℤ) - 1) ↔
        (c, d) ∈ (chainNetwork moves w last).edge
      rw [chainNetwork_edges]
      constructor
      · rintro ⟨a, hp, move, h, hd⟩
        exact ⟨move, (chainSymbol_position w last a c hp.symm) ▸ h, hd⟩
      · rintro ⟨move, h, hd⟩
        exact ⟨c, rfl, move, h, hd⟩
    | inr q =>
      change (∃ a : ChainNode m w.length, c.position = a.position ∧ ∃ move : Fin 3,
          (c.label, q) ∈ moves (chainSymbol w last a) move ∧
            ((w.length + 1 : ℕ) : ℤ) = (c.position : ℤ) + (move.val : ℤ) - 1) ↔
        (c, q) ∈ (chainNetwork moves w last).rightOut
      rw [(chainNetwork_exits moves w last c q).2]
      constructor
      · rintro ⟨a, hp, move, h, hd⟩
        have hc := c.position_le
        have hm : move = 2 := Fin.ext (by have := move.isLt; omega)
        refine ⟨by have := move.isLt; omega, ?_⟩
        simpa only [← chainSymbol_position w last c a hp, hm] using h
      · rintro ⟨hp, h⟩
        exact ⟨c, rfl, 2, h, by rw [hp]; push_cast; omega⟩
  | inr q =>
    change (∃ a : ChainNode m w.length, w.length + 1 = a.position ∧ _) ↔ _
    constructor
    · rintro ⟨a, hp, _⟩
      have := a.position_le
      omega
    · intro h
      cases y <;> exact h.elim

/-- The designated forward edge of a diagram product is exactly a successful tape run. -/
theorem chainStep_recognition {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma)
    (q r : Fin m) :
    ((q, ⟨0, by omega⟩), (r, ⟨w.length + 1, by omega⟩)) ∈ relStar (chainStep moves w last) ↔
      (q, r) ∈ (chainNetwork moves w last).summary.forward := by
  obtain ⟨c, hq, hp⟩ := ChainNode.coordinates_surjective (n := w.length) q 0 (Nat.zero_le _)
  have hstart : ChainNode.exitEquiv m w.length (Sum.inl c) = (q, ⟨0, by omega⟩) :=
    Prod.ext hq (Fin.ext hp)
  have hend : ChainNode.exitEquiv m w.length (Sum.inr r) =
      (r, ⟨w.length + 1, by omega⟩) := rfl
  rw [← hstart, ← hend, relStar_equiv_iff (ChainNode.exitEquiv m w.length)
    (blockRelation (chainNetwork moves w last).edge (chainNetwork moves w last).rightOut ∅ ∅)
    (chainStep moves w last) (chainStep_exitEquiv moves w last), blockRelation_terminal]
  constructor
  · rintro ⟨d, hcd, hdr⟩
    exact ⟨d, ⟨c, (chainNetwork_entrances moves w last q c).1.mpr ⟨hp, hq.symm⟩,
      hcd⟩, hdr⟩
  · rintro ⟨d, ⟨c', hqc, hcd⟩, hdr⟩
    obtain ⟨hp', hq'⟩ := (chainNetwork_entrances moves w last q c').1.mp hqc
    have hc : c' = c := c'.coordinates_injective c (hp'.trans hp.symm) (hq'.symm.trans hq.symm)
    exact ⟨d, hc ▸ hcd, hdr⟩

end Complementation.Internal

end Complexity.FiniteAutomaton
