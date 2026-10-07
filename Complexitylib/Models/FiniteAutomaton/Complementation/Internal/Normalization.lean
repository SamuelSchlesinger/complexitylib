/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Model

/-!
# Two-way complementation: normalization

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/Normalization.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace Complementation.Internal

open scoped SetRel

/-- Only the first tape position carries the left endmarker. -/
theorem tapeSymbol_left_iff {Sigma : Type*} (w : List Sigma) (p : Fin (w.length + 2)) :
    tapeSymbol w p = Sum.inl 0 ↔ p.val = 0 := by
  unfold tapeSymbol
  split_ifs <;> simp_all

/-- Only the last original tape position carries the right endmarker. -/
theorem tapeSymbol_right_iff {Sigma : Type*} (w : List Sigma) (p : Fin (w.length + 2)) :
    tapeSymbol w p = Sum.inl 1 ↔ p.val = w.length + 1 := by
  unfold tapeSymbol
  split_ifs <;> simp_all

namespace TwoNFA

/-- Rename states along an equivalence, retaining all transitions and moves. -/
def reindex {Sigma Q Q' : Type*} (A : TwoNFA Sigma Q) (e : Q ≃ Q') : TwoNFA Sigma Q' where
  initial := e A.initial
  accepting := e.symm ⁻¹' A.accepting
  transition q s := {target | (e.symm target.1, target.2) ∈ A.transition (e.symm q) s}

theorem reindex_language {Sigma Q Q' : Type*} (A : TwoNFA Sigma Q) (e : Q ≃ Q') :
    (A.reindex e).language = A.language := by
  ext w
  constructor
  · rintro ⟨⟨q, p⟩, haccept, hrun⟩
    refine ⟨(e.symm q, p), haccept, ?_⟩
    have h := hrun.lift (fun c : Q' × Fin (w.length + 2) => (e.symm c.1, c.2))
      (p := fun c d => (c, d) ∈ A.step w) (fun _ _ h => h)
    simpa only [Function.onFun, reindex, relStar, Set.mem_ofPred_eq, Equiv.symm_apply_apply] using h
  · rintro ⟨⟨q, p⟩, haccept, hrun⟩
    refine ⟨(e q, p), ?_, ?_⟩
    · simpa only [reindex, Set.mem_preimage, Equiv.symm_apply_apply] using haccept
    · exact hrun.lift (fun c : Q × Fin (w.length + 2) => (e c.1, c.2))
        (fun c d h => by
          simpa only [Function.onFun, step, reindex, Set.mem_ofPred_eq,
            Equiv.symm_apply_apply] using h)

/-- Embed an original configuration while reserving one state and one exit position. -/
def augmentConfig {Q : Type*} {n : ℕ} (c : Q × Fin n) : Option Q × Fin (n + 1) :=
  (some c.1, c.2.castSucc)

theorem augmentConfig_injective {Q : Type*} {n : ℕ} :
    Function.Injective (augmentConfig : Q × Fin n → Option Q × Fin (n + 1)) := by
  intro a b hab
  have hstate : some a.1 = some b.1 := congrArg Prod.fst hab
  have hpos : a.2.val = b.2.val :=
    congrArg (fun p : Option Q × Fin (n + 1) => p.2.val) hab
  exact Prod.ext (Option.some.inj hstate) (Fin.ext hpos)

/-- Original moves, an accepting stay into the fresh state, and its rightward sweep. -/
def augmentedStep {Sigma Q : Type*} (A : TwoNFA Sigma Q) (w : List Sigma) :
    SetRel (Option Q × Fin (w.length + 3)) (Option Q × Fin (w.length + 3)) :=
  {(c, d) | (∃ x y : Q × Fin (w.length + 2),
      c = augmentConfig x ∧ d = augmentConfig y ∧ (x, y) ∈ A.step w) ∨
    (∃ q : Q, ∃ p : Fin (w.length + 2),
      c = augmentConfig (q, p) ∧ d = (none, p.castSucc) ∧ q ∈ A.accepting) ∨
    (c.1 = none ∧ d.1 = none ∧ d.2.val = c.2.val + 1)}

/-- Before entering the fresh state, every augmented finite path is an original run. -/
theorem augmented_run_cases {Sigma Q : Type*} (A : TwoNFA Sigma Q) (w : List Sigma)
    {c : Option Q × Fin (w.length + 3)}
    (hrun : (augmentConfig (A.initial, ⟨0, by omega⟩), c) ∈ relStar (A.augmentedStep w)) :
    w ∈ A.language ∨ ∃ x : Q × Fin (w.length + 2),
      c = augmentConfig x ∧ ((A.initial, ⟨0, by omega⟩), x) ∈ relStar (A.step w) := by
  induction hrun with
  | refl => exact Or.inr ⟨(A.initial, ⟨0, by omega⟩), rfl, .refl⟩
  | @tail c d _ hstep ih =>
    rcases ih with haccept | ⟨x, rfl, hxrun⟩
    · exact Or.inl haccept
    rcases hstep with ⟨y, z, hxy, rfl, hyz⟩ | ⟨q, p, hxq, _, hq⟩ | ⟨hnone, _, _⟩
    · have hxy' : x = y := augmentConfig_injective hxy
      exact Or.inr ⟨z, rfl, (hxy' ▸ hxrun).tail hyz⟩
    · have hxq' : x = (q, p) := augmentConfig_injective hxq
      exact Or.inl ⟨(q, p), hq, hxq' ▸ hxrun⟩
    · exact (Option.some_ne_none _ hnone).elim

/-- The fresh state can sweep from any position to the designated right exit. -/
theorem augmented_sink_exit {Sigma Q : Type*} (A : TwoNFA Sigma Q) (w : List Sigma)
    (p : Fin (w.length + 3)) :
    ((none, p), (none, ⟨w.length + 2, by omega⟩)) ∈ relStar (A.augmentedStep w) := by
  have hsweep : ∀ k, ∀ p : Fin (w.length + 3), p.val + k = w.length + 2 →
      ((none, p), (none, ⟨w.length + 2, by omega⟩)) ∈ relStar (A.augmentedStep w) := by
    intro k
    induction k with
    | zero =>
      intro p hp
      have hlast : p = ⟨w.length + 2, by omega⟩ := Fin.ext (by omega)
      rw [hlast]
      exact .refl
    | succ k ih =>
      intro p hp
      let next : Fin (w.length + 3) := ⟨p.val + 1, by omega⟩
      have hnext : next.val + k = w.length + 2 := by dsimp [next]; omega
      exact (ih next hnext).head (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  exact hsweep (w.length + 2 - p.val) p (by omega)

/-- Finite acceptance is equivalent to reaching the designated augmented exit. -/
theorem augmented_acceptance {Sigma Q : Type*} (A : TwoNFA Sigma Q) (w : List Sigma) :
    w ∈ A.language ↔
      (augmentConfig (A.initial, ⟨0, by omega⟩), (none, ⟨w.length + 2, by omega⟩)) ∈
        relStar (A.augmentedStep w) := by
  constructor
  · rintro ⟨c, hc, hrun⟩
    have hlift := hrun.lift augmentConfig
      (p := fun c d => (c, d) ∈ A.augmentedStep w)
      (fun x y h => Or.inl ⟨x, y, rfl, rfl, h⟩)
    have hjump : (augmentConfig c, (none, c.2.castSucc)) ∈ A.augmentedStep w :=
      Or.inr (Or.inl ⟨c.1, c.2, rfl, rfl, hc⟩)
    exact (hlift.tail hjump).trans (A.augmented_sink_exit w c.2.castSucc)
  · intro hrun
    rcases A.augmented_run_cases w hrun with h | ⟨c, heq, _⟩
    · exact h
    · have hnone : (none : Option Q) = some c.1 :=
        congrArg (fun p : Option Q × Fin (w.length + 3) => p.1) heq
      cases hnone

/-- Augmented moves at one symbol, including the original endmarker restrictions. -/
def augmentedMove {Sigma Q : Type*} (A : TwoNFA Sigma Q) (symbol : Fin 2 ⊕ Sigma)
    (move : Fin 3) : SetRel (Option Q) (Option Q) :=
  {pq | match pq.1, pq.2 with
    | some q, some r => (r, move) ∈ A.transition q symbol ∧
        (symbol = Sum.inl 0 → move ≠ 0) ∧ (symbol = Sum.inl 1 → move ≠ 2)
    | some q, none => q ∈ A.accepting ∧ move = 1
    | none, none => move = 2
    | none, some _ => False}

/-- The global augmented graph is exactly the graph of the local moves and head displacement. -/
theorem augmentedStep_local_iff {Sigma Q : Type*} (A : TwoNFA Sigma Q) (w : List Sigma)
    (c d : Option Q × Fin (w.length + 3)) :
    (c, d) ∈ A.augmentedStep w ↔
      ∃ p : Fin (w.length + 2), c.2 = p.castSucc ∧ ∃ move : Fin 3,
        (c.1, d.1) ∈ A.augmentedMove (tapeSymbol w p) move ∧
        (d.2.val : ℤ) = (p.val : ℤ) + (move.val : ℤ) - 1 := by
  constructor
  · rintro (⟨⟨q, p⟩, ⟨r, t⟩, rfl, rfl, hstep⟩ |
      ⟨q, p, rfl, rfl, hq⟩ | ⟨hc, hd, hpos⟩)
    · obtain ⟨move, htrans, hpos⟩ := hstep
      change (t.val : ℤ) = (p.val : ℤ) + (move.val : ℤ) - 1 at hpos
      refine ⟨p, rfl, move, ⟨htrans, ?_, ?_⟩, hpos⟩
      · intro hleft hmove
        have hp := (tapeSymbol_left_iff w p).mp hleft
        have hm := congrArg Fin.val hmove
        simp only [Fin.val_zero] at hm
        omega
      · intro hright hmove
        have hp := (tapeSymbol_right_iff w p).mp hright
        have hm := congrArg Fin.val hmove
        norm_num at hm
        omega
    · exact ⟨p, rfl, 1, ⟨hq, rfl⟩, by simp⟩
    · let p : Fin (w.length + 2) := ⟨c.2.val, by have := d.2.isLt; omega⟩
      refine ⟨p, Fin.ext rfl, 2, ?_, ?_⟩
      · rw [hc, hd]
        exact rfl
      · dsimp [p]
        omega
  · rintro ⟨p, hpos, move, hlocal, hdisp⟩
    obtain ⟨cq, cp⟩ := c
    obtain ⟨dq, dp⟩ := d
    change cp = p.castSucc at hpos
    subst cp
    change (dp.val : ℤ) = (p.val : ℤ) + (move.val : ℤ) - 1 at hdisp
    cases cq with
    | none =>
      cases dq with
      | none =>
        change move = 2 at hlocal
        subst move
        exact Or.inr (Or.inr ⟨rfl, rfl, by simp only [Fin.val_castSucc]; norm_num at hdisp; omega⟩)
      | some r => exact hlocal.elim
    | some q =>
      cases dq with
      | none =>
        change q ∈ A.accepting ∧ move = 1 at hlocal
        obtain ⟨hq, rfl⟩ := hlocal
        refine Or.inr (Or.inl ⟨q, p, rfl, ?_, hq⟩)
        congr 1
        apply Fin.ext
        change dp.val = p.val
        norm_num at hdisp
        omega
      | some r =>
        change (r, move) ∈ A.transition q (tapeSymbol w p) ∧
          (tapeSymbol w p = Sum.inl 0 → move ≠ 0) ∧
          (tapeSymbol w p = Sum.inl 1 → move ≠ 2) at hlocal
        have hdp : dp.val < w.length + 2 := by
          by_contra hn
          have hdpval : dp.val = w.length + 2 := by omega
          have hpval : p.val = w.length + 1 := by have := move.isLt; omega
          have hm : move = 2 := Fin.ext (by have := move.isLt; omega)
          exact hlocal.2.2 ((tapeSymbol_right_iff w p).mpr hpval) hm
        refine Or.inl ⟨(q, p), (r, ⟨dp.val, hdp⟩), rfl, ?_, move, hlocal.1, hdisp⟩
        exact Prod.ext rfl (Fin.ext rfl)

end TwoNFA

end Complementation.Internal

end Complexity.FiniteAutomaton
