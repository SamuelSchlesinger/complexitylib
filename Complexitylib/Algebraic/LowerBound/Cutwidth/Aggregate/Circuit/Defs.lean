/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Aggregate

/-!
# Output guesses and erasure for aggregate circuits

Only special occurrences receive guessed bits. Erasure preserves every gate index
and every ordinary incoming wire, replacing each special gate by a nullary constant.
Thus a special output may feed another special gate, an ordinary gate, or the output.
-/

@[expose] public section

namespace Algebraic.Aggregate

variable {J : Type} {State : J → Type} {n g m : ℕ}

/-- The special gate occurrences in an actual straight-line program. -/
abbrev SpecialGate (p : Program (signature State) n g) :=
  {gate : Fin g // (p.lines gate).op.isSpecial = true}

/-- The number of special occurrences, not the number of possible operation symbols. -/
def specialCount (p : Program (signature State) n g) : ℕ := Fintype.card (SpecialGate p)

/-- One output bit for each special occurrence. -/
abbrev Guess (p : Program (signature State) n g) := SpecialGate p → Bool

/-- The aggregate register belonging to a particular special occurrence. -/
abbrev Register (p : Program (signature State) n g) (gate : SpecialGate p) :=
  (p.lines gate).op.Register

/-- Simultaneous registers for all special occurrences. -/
abbrev Registers (p : Program (signature State) n g) := ∀ gate : SpecialGate p, Register p gate

/-- Output-guess bits plus the binary logarithmic budgets of the actual registers. -/
def budget [∀ j, Fintype (State j)] (p : Program (signature State) n g) : ℕ :=
  specialCount p + ∑ gate : SpecialGate p, Nat.clog 2 (Fintype.card (Register p gate))

/-- Extend special-only guesses by a dummy bit on ordinary gates. The dummy is ignored. -/
def guessValues (p : Program (signature State) n g) (a : Guess p) (gate : Fin g) : Bool :=
  if h : (p.lines gate).op.isSpecial = true then a ⟨gate, h⟩ else false

/-- Erase one line while retaining the wire namespace. -/
def eraseLine (line : Line (signature State) n g) (value : Bool) :
    Line ordinarySignature n g :=
  match line with
  | ⟨.binary f, wires⟩ => ⟨.binary f, wires⟩
  | ⟨.special .., _⟩ => ⟨.constant value, Fin.elim0⟩

/-- The structural erasure uses a total lookup; only special entries are inspected. -/
def eraseWith : {g : ℕ} → Program (signature State) n g → (Fin g → Bool) →
    Program ordinarySignature n g
  | _, .empty, _ => .empty
  | g + 1, .gate p line, values =>
      (eraseWith p (values ∘ Fin.castSucc)).gate (eraseLine line (values (Fin.last g)))

/-- Replace each special gate by its guessed nullary output, preserving all gate indices. -/
def erase (p : Program (signature State) n g) (a : Guess p) :
    Program ordinarySignature n g := eraseWith p (guessValues p a)

/-- The designated outputs use precisely the same wires after erasure. -/
def eraseCircuit (c : Circuit (signature State) n m) (a : Guess c.program) :
    Circuit ordinarySignature n m := ⟨erase c.program a, c.outputs⟩

/-- Every special gate agrees with evaluation of its original slots on a candidate trace. -/
def Consistent [∀ j, CommMonoid (State j)] (p : Program (signature State) n g)
    (a : Guess p) (input : Fin n → Bool) : Prop :=
  ∀ gate : SpecialGate p,
    (p.lines gate).eval interpretation input ((erase p a).eval ordinaryInterpretation input) =
      a gate

/-- The true special-output vector. -/
def actualGuess [∀ j, CommMonoid (State j)] (p : Program (signature State) n g)
    (input : Fin n → Bool) : Guess p := fun gate => p.eval interpretation input gate

end Algebraic.Aggregate
