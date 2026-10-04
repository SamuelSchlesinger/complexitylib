/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Circuit.Defs

/-!
# Erasure identities and exact consistency

The original and erased programs have identical wire namespaces. Gate equations
therefore compare their traces directly, using CSLib's acyclic uniqueness theorem.
-/

@[expose] public section

namespace Algebraic.Aggregate

variable {J : Type} {State : J → Type} {n g m : ℕ}

theorem eraseLine_mapWires (line : Line (signature State) n g) (value : Bool)
    {n' g' : ℕ} (map : Wire n g → Wire n' g') :
    eraseLine (line.mapWires map) value = (eraseLine line value).mapWires map := by
  rcases line with ⟨op, wires⟩
  cases op with
  | binary => rfl
  | special =>
      simp only [eraseLine, Line.mapWires]
      congr 1
      funext slot
      exact slot.elim0

theorem lines_eraseWith (p : Program (signature State) n g) (values : Fin g → Bool)
    (gate : Fin g) :
    (eraseWith p values).lines gate = eraseLine (p.lines gate) (values gate) := by
  induction p with
  | empty => exact gate.elim0
  | @gate g p line ih =>
      induction gate using Fin.lastCases with
      | last => simp [eraseWith, eraseLine_mapWires]
      | cast gate => simp [eraseWith, ih, eraseLine_mapWires]

theorem eraseLine_eval [∀ j, CommMonoid (State j)]
    (line : Line (signature State) n g) (value : Bool)
    (input : Fin n → Bool) (gates : Fin g → Bool) :
    (eraseLine line value).eval ordinaryInterpretation input gates =
      if line.op.isSpecial then value else line.eval interpretation input gates := by
  rcases line with ⟨op, wires⟩
  cases op <;> rfl

theorem eraseWith_eval_gate [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (values : Fin g → Bool)
    (input : Fin n → Bool) (gate : Fin g) :
    (eraseWith p values).eval ordinaryInterpretation input gate =
      if (p.lines gate).op.isSpecial then values gate else
        (p.lines gate).eval interpretation input
          ((eraseWith p values).eval ordinaryInterpretation input) := by
  rw [← Program.lines_eval, lines_eraseWith, eraseLine_eval]

theorem erase_fanInAtMost (p : Program (signature State) n g) (a : Guess p) :
    (erase p a).FanInAtMost 2 := by
  suffices h : ∀ values, (eraseWith p values).FanInAtMost 2 from h _
  clear a
  induction p with
  | empty => intro _; trivial
  | gate p line ih =>
      intro values
      exact ⟨ih _, ordinary_arity_le_two _⟩

/-- Erased special gates have no slots; every ordinary gate retains its two slots. -/
theorem arity_lines_erase (p : Program (signature State) n g) (a : Guess p) (gate : Fin g) :
    ordinarySignature.Arity ((erase p a).lines gate).op =
      if (p.lines gate).op.isSpecial then 0 else 2 := by
  rw [erase, lines_eraseWith]
  generalize p.lines gate = line
  rcases line with ⟨op, wires⟩
  cases op <;> rfl

theorem erase_eval_special [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (a : Guess p) (input : Fin n → Bool)
    (gate : SpecialGate p) :
    (erase p a).eval ordinaryInterpretation input gate = a gate := by
  simp [erase, eraseWith_eval_gate, gate.property, guessValues]

theorem erase_eval_of_consistent [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (a : Guess p) (input : Fin n → Bool)
    (h : Consistent p a input) :
    (erase p a).eval ordinaryInterpretation input = p.eval interpretation input := by
  apply Program.eq_eval_of_forall_lines_eval
  intro gate
  by_cases hs : (p.lines gate).op.isSpecial = true
  · exact (h ⟨gate, hs⟩).trans (erase_eval_special p a input ⟨gate, hs⟩).symm
  · simp [erase, eraseWith_eval_gate, hs]

theorem erase_eval_actualGuess [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (input : Fin n → Bool) :
    (erase p (actualGuess p input)).eval ordinaryInterpretation input =
      p.eval interpretation input := by
  symm
  apply Program.eq_eval_of_forall_lines_eval
  intro gate
  rw [erase, lines_eraseWith, eraseLine_eval]
  split
  · simp_all [guessValues, actualGuess]
  · exact Program.lines_eval p interpretation input gate

theorem actualGuess_consistent [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (input : Fin n → Bool) :
    Consistent p (actualGuess p input) input := by
  intro gate
  rw [erase_eval_actualGuess]
  exact Program.lines_eval p interpretation input gate

theorem consistent_iff_eq_actualGuess [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (a : Guess p) (input : Fin n → Bool) :
    Consistent p a input ↔ a = actualGuess p input := by
  constructor
  · intro h
    funext gate
    rw [← erase_eval_special p a input gate, erase_eval_of_consistent p a input h]
    rfl
  · rintro rfl
    exact actualGuess_consistent p input

end Algebraic.Aggregate
