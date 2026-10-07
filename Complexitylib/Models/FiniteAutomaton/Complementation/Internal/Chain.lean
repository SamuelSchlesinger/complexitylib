/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Network

/-!
# Two-way complementation: chain

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/Chain.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace Complementation.Internal

open scoped SetRel

/-- Internal vertices of a chain with one distinguished final cell. -/
def ChainNode (m : ℕ) : ℕ → Type
  | 0 => Fin m
  | n + 1 => Fin m ⊕ ChainNode m n

namespace ChainNode

/-- Zero-based cell coordinate. -/
def position {m : ℕ} : {n : ℕ} → ChainNode m n → ℕ
  | 0, _ => 0
  | _ + 1, .inl _ => 0
  | _ + 1, .inr c => c.position + 1

/-- State label carried at a cell. -/
def label {m : ℕ} : {n : ℕ} → ChainNode m n → Fin m
  | 0, q => q
  | _ + 1, .inl q => q
  | _ + 1, .inr c => c.label

/-- Every vertex belongs to one of the chain's cells. -/
theorem position_le {m n : ℕ} (c : ChainNode m n) : c.position ≤ n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    cases c with
    | inl q => exact Nat.zero_le _
    | inr c => exact Nat.succ_le_succ (ih c)

/-- A cell coordinate and a state label uniquely identify an internal vertex. -/
theorem coordinates_injective {m n : ℕ} (c d : ChainNode m n)
    (hp : c.position = d.position) (hq : c.label = d.label) : c = d := by
  induction n with
  | zero => exact hq
  | succ n ih =>
    cases c with
    | inl q =>
      cases d with
      | inl r => exact congrArg Sum.inl hq
      | inr d => exact (Nat.succ_ne_zero _ hp.symm).elim
    | inr c =>
      cases d with
      | inl r => exact (Nat.succ_ne_zero _ hp).elim
      | inr d => exact congrArg Sum.inr (ih c d (Nat.succ.inj hp) hq)

/-- Every valid cell coordinate and state label occurs. -/
theorem coordinates_surjective {m n : ℕ} (q : Fin m) (p : ℕ) (hp : p ≤ n) :
    ∃ c : ChainNode m n, c.label = q ∧ c.position = p := by
  induction n generalizing p with
  | zero => exact ⟨q, rfl, by dsimp [position]; omega⟩
  | succ n ih =>
    cases p with
    | zero => exact ⟨Sum.inl q, rfl, rfl⟩
    | succ p =>
      obtain ⟨c, hq, hc⟩ := ih p (by omega)
      exact ⟨Sum.inr c, hq, congrArg Nat.succ hc⟩

end ChainNode

/-- The symbol at a vertex in a nonempty cell chain. -/
def chainSymbol {Sigma : Type*} {m : ℕ} (w : List Sigma) (last : Sigma) :
    ChainNode m w.length → Sigma :=
  match w with
  | [] => fun _ => last
  | a :: tail => fun c => match c with
    | .inl _ => a
    | .inr d => chainSymbol tail last d

/-- A single cell retains stays internally and exposes its two moving transitions. -/
def cellNetwork {m : ℕ} (moves : Fin 3 → SetRel (Fin m) (Fin m)) : Network m (Fin m) where
  edge := moves 1
  leftIn := SetRel.id
  rightIn := SetRel.id
  leftOut := moves 0
  rightOut := moves 2

/-- Join a list of cells to a distinguished final cell. -/
def chainNetwork {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma) :
    Network m (ChainNode m w.length) :=
  match w with
  | [] => cellNetwork (moves last)
  | a :: tail => (cellNetwork (moves a)).join (chainNetwork moves tail last)

/-- The path summary of a cell chain is the product of its cell diagrams. -/
theorem chainNetwork_summary {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma) :
    (chainNetwork moves w last).summary =
      wordDiagram (fun a => cellDiagram m (moves a 1) (moves a 2) (moves a 0)) (w ++ [last]) := by
  induction w with
  | nil =>
    change (cellNetwork (moves last)).summary = _
    simp [Network.summary, cellNetwork, cellDiagram, wordDiagram, SetRel.id_comp]
  | cons a w ih =>
    change ((cellNetwork (moves a)).join (chainNetwork moves w last)).summary = _
    rw [Network.summary_join, ih]
    simp only [Network.summary, cellNetwork, SetRel.id_comp, cellDiagram, wordDiagram,
      List.cons_append, List.map_cons, List.prod_cons]
    rfl

/-- Entrances attach exactly to the first and last cells with their unchanged labels. -/
theorem chainNetwork_entrances {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma)
    (q : Fin m) (c : ChainNode m w.length) :
    ((q, c) ∈ (chainNetwork moves w last).leftIn ↔ c.position = 0 ∧ q = c.label) ∧
    ((q, c) ∈ (chainNetwork moves w last).rightIn ↔ c.position = w.length ∧ q = c.label) := by
  induction w with
  | nil =>
    change (q = c ↔ 0 = 0 ∧ q = c) ∧ (q = c ↔ 0 = 0 ∧ q = c)
    simp
  | cons a w ih =>
    cases c with
    | inl r =>
      change ((∃ v : Fin m, (Sum.inl r : Fin m ⊕ ChainNode m w.length) = Sum.inl v ∧
          q = v) ↔ 0 = 0 ∧ q = r) ∧
        ((∃ v, (Sum.inl r : Fin m ⊕ ChainNode m w.length) = Sum.inr v ∧
          (q, v) ∈ (chainNetwork moves w last).rightIn) ↔ 0 = w.length + 1 ∧ q = r)
      simp [eq_comm]
    | inr c =>
      change ((∃ v : Fin m, (Sum.inr c : Fin m ⊕ ChainNode m w.length) = Sum.inl v ∧
          q = v) ↔ c.position + 1 = 0 ∧ q = c.label) ∧
        ((∃ v, (Sum.inr c : Fin m ⊕ ChainNode m w.length) = Sum.inr v ∧
          (q, v) ∈ (chainNetwork moves w last).rightIn) ↔
            c.position + 1 = w.length + 1 ∧ q = c.label)
      simpa using (ih c).2

/-- Only the endpoint cells can exit a chain, using the appropriate moving transition. -/
theorem chainNetwork_exits {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma)
    (c : ChainNode m w.length) (q : Fin m) :
    ((c, q) ∈ (chainNetwork moves w last).leftOut ↔
      c.position = 0 ∧ (c.label, q) ∈ moves (chainSymbol w last c) 0) ∧
    ((c, q) ∈ (chainNetwork moves w last).rightOut ↔
      c.position = w.length ∧ (c.label, q) ∈ moves (chainSymbol w last c) 2) := by
  induction w with
  | nil =>
    change ((c, q) ∈ moves last 0 ↔ 0 = 0 ∧ (c, q) ∈ moves last 0) ∧
      ((c, q) ∈ moves last 2 ↔ 0 = 0 ∧ (c, q) ∈ moves last 2)
    simp
  | cons a w ih =>
    cases c with
    | inl r =>
      change ((∃ v : Fin m, (Sum.inl r : Fin m ⊕ ChainNode m w.length) = Sum.inl v ∧
          (v, q) ∈ moves a 0) ↔ 0 = 0 ∧ (r, q) ∈ moves a 0) ∧
        ((∃ v, (Sum.inl r : Fin m ⊕ ChainNode m w.length) = Sum.inr v ∧
          (v, q) ∈ (chainNetwork moves w last).rightOut) ↔
            0 = w.length + 1 ∧ (r, q) ∈ moves a 2)
      simp
    | inr c =>
      change ((∃ v : Fin m, (Sum.inr c : Fin m ⊕ ChainNode m w.length) = Sum.inl v ∧
          (v, q) ∈ moves a 0) ↔ c.position + 1 = 0 ∧
            (c.label, q) ∈ moves (chainSymbol w last c) 0) ∧
        ((∃ v, (Sum.inr c : Fin m ⊕ ChainNode m w.length) = Sum.inr v ∧
          (v, q) ∈ (chainNetwork moves w last).rightOut) ↔
            c.position + 1 = w.length + 1 ∧ (c.label, q) ∈ moves (chainSymbol w last c) 2)
      simpa using (ih c).2

/-- Internal edges are precisely local transitions that stay within the chain. -/
theorem chainNetwork_edges {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma)
    (c d : ChainNode m w.length) :
    (c, d) ∈ (chainNetwork moves w last).edge ↔
      ∃ move : Fin 3, (c.label, d.label) ∈ moves (chainSymbol w last c) move ∧
        (d.position : ℤ) = (c.position : ℤ) + (move.val : ℤ) - 1 := by
  induction w with
  | nil =>
    change (c, d) ∈ moves last 1 ↔
      ∃ move : Fin 3, (c, d) ∈ moves last move ∧ (0 : ℤ) = 0 + (move.val : ℤ) - 1
    constructor
    · exact fun h => ⟨1, h, by norm_num⟩
    · rintro ⟨move, h, hp⟩
      have hm : move = 1 := Fin.ext (by norm_num at hp; omega)
      simpa only [hm] using h
  | cons a w ih =>
    cases c with
    | inl q =>
      cases d with
      | inl r =>
        change (q, r) ∈ moves a 1 ↔
          ∃ move : Fin 3, (q, r) ∈ moves a move ∧ (0 : ℤ) = 0 + (move.val : ℤ) - 1
        constructor
        · exact fun h => ⟨1, h, by norm_num⟩
        · rintro ⟨move, h, hp⟩
          have hm : move = 1 := Fin.ext (by norm_num at hp; omega)
          simpa only [hm] using h
      | inr d =>
        change (q, d) ∈ moves a 2 ○ (chainNetwork moves w last).leftIn ↔ _
        constructor
        · rintro ⟨r, hqr, hrd⟩
          obtain ⟨hp, hq⟩ := (chainNetwork_entrances moves w last r d).1.mp hrd
          exact ⟨2, hq ▸ hqr, by dsimp [ChainNode.position]; rw [hp]; norm_num⟩
        · rintro ⟨move, h, hp⟩
          change ((d.position + 1 : ℕ) : ℤ) = 0 + (move.val : ℤ) - 1 at hp
          have hm : move = 2 := Fin.ext (by have := move.isLt; omega)
          have hd : d.position = 0 := by have := move.isLt; omega
          refine ⟨d.label, ?_, (chainNetwork_entrances moves w last d.label d).1.mpr ⟨hd, rfl⟩⟩
          simpa only [ChainNode.label, chainSymbol, hm] using h
    | inr c =>
      cases d with
      | inl r =>
        change (c, r) ∈ (chainNetwork moves w last).leftOut ○ SetRel.id ↔ _
        rw [SetRel.comp_id]
        constructor
        · intro h
          obtain ⟨hp, hq⟩ := (chainNetwork_exits moves w last c r).1.mp h
          exact ⟨0, hq, by dsimp [ChainNode.position]; rw [hp]; norm_num⟩
        · rintro ⟨move, h, hp⟩
          change (0 : ℤ) = ((c.position + 1 : ℕ) : ℤ) + (move.val : ℤ) - 1 at hp
          have hm : move = 0 := Fin.ext (by omega)
          have hc : c.position = 0 := by omega
          refine (chainNetwork_exits moves w last c r).1.mpr ⟨hc, ?_⟩
          simpa only [ChainNode.label, chainSymbol, hm] using h
      | inr d =>
        change (c, d) ∈ (chainNetwork moves w last).edge ↔ _
        rw [ih c d]
        simp only [ChainNode.label, chainSymbol, ChainNode.position, Nat.cast_add, Nat.cast_one]
        constructor <;> rintro ⟨move, h, hp⟩ <;> exact ⟨move, h, by omega⟩

end Complementation.Internal

end Complexity.FiniteAutomaton
