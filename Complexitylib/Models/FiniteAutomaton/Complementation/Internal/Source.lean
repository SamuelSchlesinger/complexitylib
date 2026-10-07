/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Normalization
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.RelationMonoid

/-!
# Two-way complementation: source

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/Source.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace Complementation.Internal

open scoped SetRel

/-- Relation product for an input word; the empty product is the identity. -/
def relationProduct {H : Type*} (w : List (SetRel H H)) : SetRel H H :=
  w.foldr SetRel.comp SetRel.id

theorem relationProduct_append {H : Type*} (u v : List (SetRel H H)) :
    relationProduct (u ++ v) = relationProduct u ○ relationProduct v := by
  induction u with
  | nil => simp [relationProduct]
  | cons R u ih => simpa [relationProduct, SetRel.comp_assoc] using congrArg (R ○ ·) ih

/-- The source language consists of the words with nonempty relation product. -/
def sourceLanguage (H : Type*) : Set (List (SetRel H H)) :=
  {w | (relationProduct w).Nonempty}

/-- The explicit source machine: `none` starts, `some none` accepts, and
    `some (some h)` is the state labelled by `h`. -/
def sourceAutomaton (H : Type*) : TwoNFA (SetRel H H) (Option (Option H)) where
  initial := none
  accepting := {some none}
  transition state symbol := match state, symbol with
    | none, .inl marker =>
      if marker = 0 then {target | ∃ h, target = (some (some h), 2)} else ∅
    | some (some p), .inr R =>
      {target | ∃ q, (p, q) ∈ R ∧ target = (some (some q), 2)}
    | some (some _), .inl marker =>
      if marker = 1 then {(some none, 1)} else ∅
    | _, _ => ∅

/-- Configurations from which the explicit source machine has a suffix witness. -/
def sourceProductive {H : Type*} (w : List (SetRel H H)) :
    Set (Option (Option H) × Fin (w.length + 2)) :=
  {c | match c.1 with
    | none => c.2.val = 0 ∧ (relationProduct w).Nonempty
    | some none => True
    | some (some p) => 1 ≤ c.2.val ∧ ∃ q, (p, q) ∈ relationProduct (w.drop (c.2.val - 1))}

theorem sourceProductive_of_step {H : Type*} (w : List (SetRel H H))
    {c d : Option (Option H) × Fin (w.length + 2)}
    (hstep : (c, d) ∈ (sourceAutomaton H).step w) (hd : d ∈ sourceProductive w) :
    c ∈ sourceProductive w := by
  obtain ⟨cs, ci⟩ := c
  obtain ⟨ds, di⟩ := d
  obtain ⟨move, htransition, hpos⟩ := hstep
  change (ds, move) ∈ (sourceAutomaton H).transition cs (tapeSymbol w ci) at htransition
  change (di.val : ℤ) = (ci.val : ℤ) + (move.val : ℤ) - 1 at hpos
  cases cs with
  | none =>
    by_cases hleft : ci.val = 0
    · have hex : ∃ p, ds = some (some p) ∧ move = 2 := by
        simpa [sourceAutomaton, tapeSymbol, hleft] using htransition
      obtain ⟨p, hds, hmove⟩ := hex
      subst ds
      subst move
      have hdi : di.val = 1 := by norm_num at hpos; omega
      obtain ⟨_, q, hpq⟩ := hd
      exact ⟨hleft, (p, q), by simpa [hdi] using hpq⟩
    · by_cases hright : ci.val = w.length + 1 <;>
        simp [sourceAutomaton, tapeSymbol, hleft, hright] at htransition
  | some state =>
    cases state with
    | none =>
      change (ds, move) ∈ (∅ : Set (Option (Option H) × Fin 3)) at htransition
      exact htransition.elim
    | some p =>
      by_cases hleft : ci.val = 0
      · simp [sourceAutomaton, tapeSymbol, hleft] at htransition
      · by_cases hright : ci.val = w.length + 1
        · change 1 ≤ ci.val ∧ ∃ q, (p, q) ∈ relationProduct (w.drop (ci.val - 1))
          refine ⟨by omega, p, ?_⟩
          simp [hright, relationProduct]
        · have hex : ∃ q, (p, q) ∈ w[ci.val - 1]'(by omega) ∧
              ds = some (some q) ∧ move = 2 := by
            simpa [sourceAutomaton, tapeSymbol, hleft, hright] using htransition
          obtain ⟨q, hpq, hds, hmove⟩ := hex
          subst ds
          subst move
          have hdi : di.val = ci.val + 1 := by norm_num at hpos; omega
          obtain ⟨_, r, hqr⟩ := hd
          change 1 ≤ ci.val ∧ ∃ r, (p, r) ∈ relationProduct (w.drop (ci.val - 1))
          refine ⟨by omega, r, ?_⟩
          rw [List.drop_eq_getElem_cons (show ci.val - 1 < w.length from by omega)]
          change (p, r) ∈ w[ci.val - 1] ○ relationProduct (w.drop (ci.val - 1 + 1))
          refine ⟨q, hpq, ?_⟩
          simpa only [hdi, Nat.add_sub_cancel,
            Nat.sub_add_cancel (show 1 ≤ ci.val by omega)] using hqr

theorem sourceAutomaton_sound {H : Type*} (w : List (SetRel H H))
    (hw : w ∈ (sourceAutomaton H).language) : (relationProduct w).Nonempty := by
  obtain ⟨c, hc, hrun⟩ := hw
  have hproductive : c ∈ sourceProductive w := by
    change c.1 ∈ ({some none} : Set (Option (Option H))) at hc
    have hstate : c.1 = some none := hc
    simp only [sourceProductive, Set.mem_ofPred_eq, hstate]
  have hback : ∀ {c d}, (c, d) ∈ relStar ((sourceAutomaton H).step w) →
      d ∈ sourceProductive w → c ∈ sourceProductive w := by
    intro c d h
    induction h with
    | refl => exact id
    | tail _ hstep ih => exact fun hd => ih (sourceProductive_of_step w hstep hd)
  exact (hback hrun hproductive).2

theorem sourceAutomaton_suffix_run {H : Type*} (w : List (SetRel H H))
    (u v : List (SetRel H H)) (hw : w = u ++ v) {p q : H}
    (hpq : (p, q) ∈ relationProduct v) :
    ((some (some p), ⟨u.length + 1, by simp [hw]⟩),
      (some none, ⟨w.length + 1, by omega⟩)) ∈ relStar ((sourceAutomaton H).step w) := by
  induction v generalizing u p with
  | nil =>
    have hlen : w.length = u.length := by simp [hw]
    apply Relation.ReflTransGen.single
    refine ⟨1, ?_, ?_⟩
    · simp [sourceAutomaton, tapeSymbol, hlen]
    · simp [hlen]
  | cons R v ih =>
    obtain ⟨r, hpr, hrq⟩ := hpq
    have hlen : w.length = u.length + (v.length + 1) := by simp [hw]
    have hw' : w = (u ++ [R]) ++ v := by
      simpa only [List.append_assoc, List.singleton_append] using hw
    have htail := ih (u ++ [R]) hw' hrq
    apply htail.head
    refine ⟨2, ?_, ?_⟩
    · have hsymbol : tapeSymbol w ⟨u.length + 1, by omega⟩ = Sum.inr R := by
        simp [tapeSymbol, hw, List.getElem_append_right]
      change (some (some r), (2 : Fin 3)) ∈
        (sourceAutomaton H).transition (some (some p)) (tapeSymbol w _)
      rw [hsymbol]
      exact ⟨r, hpr, rfl⟩
    · simp [List.length_append]
      omega

/-- The explicit machine recognizes nonempty relation products. -/
theorem sourceAutomaton_language (H : Type*) :
    (sourceAutomaton H).language = sourceLanguage H := by
  ext w
  constructor
  · exact sourceAutomaton_sound w
  · rintro ⟨⟨p, q⟩, hpq⟩
    refine ⟨(some none, ⟨w.length + 1, by omega⟩), rfl, ?_⟩
    have hrun := sourceAutomaton_suffix_run w [] w (by simp) hpq
    apply hrun.head
    refine ⟨2, ?_, ?_⟩
    · exact ⟨p, rfl⟩
    · norm_num

/-- The source language on `h` labels is recognized using exactly `h + 2` states. -/
theorem sourceLanguage_state_bound (H : Type*) [Fintype H] :
    ∃ A : TwoNFA (SetRel H H) (Fin (Fintype.card H + 2)), A.language = sourceLanguage H := by
  classical
  let e : Option (Option H) ≃ Fin (Fintype.card H + 2) :=
    (Fintype.equivFin _).trans (finCongr (by simp))
  refine ⟨(sourceAutomaton H).reindex e, ?_⟩
  rw [TwoNFA.reindex_language, sourceAutomaton_language]

/-- Singleton letters on the two sides test one edge of a word's relation product. -/
theorem singleton_word_context {H : Type*} (w : List (SetRel H H)) (p q : H) :
    (relationProduct ([restrictedIdentity {p}] ++ w ++ [restrictedIdentity {q}])).Nonempty ↔
      (p, q) ∈ relationProduct w := by
  rw [relationProduct_append, relationProduct_append]
  simp only [relationProduct, List.foldr_cons, List.foldr_nil, SetRel.comp_id]
  rw [singleton_context]
  constructor
  · rintro ⟨⟨x, y⟩, _, _, hpq⟩
    exact hpq
  · intro hpq
    exact ⟨(p, q), rfl, rfl, hpq⟩

end Complementation.Internal

end Complexity.FiniteAutomaton
