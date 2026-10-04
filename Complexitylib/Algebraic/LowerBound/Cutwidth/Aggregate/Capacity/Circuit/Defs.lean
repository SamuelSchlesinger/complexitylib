/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Circuit.Count

/-!
# Primary-input summaries for aggregate circuits

Each binary occurrence contributes one bit. Each special occurrence contributes
one monoid element, aggregating only the selected primary-input slots. No internal
wire values or output guesses enter this summary.
-/

@[expose] public section

namespace Algebraic.Aggregate.Capacity

variable {J : Type} {State : J → Type} {n g : ℕ}

/-- The per-occurrence summary type. -/
abbrev SummaryRegister : Op State → Type
  | .binary _ => Bool
  | .special kind _ _ _ => State kind

instance [∀ j, Fintype (State j)] (op : Op State) : Fintype (SummaryRegister op) := by
  cases op <;> dsimp [SummaryRegister] <;> infer_instance

/-- Only selected primary inputs belong to the sending party. -/
def selected (U : Finset (Fin n)) : Wire n g → Prop
  | .input i => i ∈ U
  | .gate _ => False

instance (U : Finset (Fin n)) (wire : Wire n g) : Decidable (selected U wire) := by
  cases wire <;> dsimp [selected] <;> infer_instance

/-- A line's summary uses only selected values. If both binary inputs are selected,
only its output is needed; if exactly one is selected, only that input is needed. -/
def lineSummary [∀ j, CommMonoid (State j)] (line : Line (signature State) n g)
    (U : Finset (Fin n)) (values : Wire n g → Bool) : SummaryRegister line.op :=
  match line with
  | ⟨.binary f, wires⟩ =>
      if selected U (wires 0) then
        if selected U (wires 1) then f (values (wires 0)) (values (wires 1))
        else values (wires 0)
      else if selected U (wires 1) then values (wires 1) else false
  | ⟨.special _ _ contribution _, wires⟩ =>
      ∏ slot with selected U (wires slot), contribution slot (values (wires slot))

/-- The one-way key has one register for each actual gate occurrence. -/
abbrev Key (p : Program (signature State) n g) :=
  (gate : Fin g) → SummaryRegister (p.lines gate).op

/-- The sending party summarizes its primary inputs at every gate. -/
def key [∀ j, CommMonoid (State j)] (p : Program (signature State) n g)
    (U : Finset (Fin n)) (input : Fin n → Bool) : Key p :=
  fun gate => lineSummary (p.lines gate) U (Wire.elim input (fun _ => false))

/-- Bit capacity charges a binary gate one bit and a special gate its register size. -/
def capacity [∀ j, Fintype (State j)] (p : Program (signature State) n g) : ℕ :=
  ordinaryCount p + ∑ gate : SpecialGate p, Nat.clog 2 (Fintype.card (Register p gate))

end Algebraic.Aggregate.Capacity
