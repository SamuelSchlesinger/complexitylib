/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Binary
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Data.Nat.Log

/-!
# Binary gates and finite commutative aggregates

A special operation multiplies one contribution for each ordered input slot and
applies a Boolean readout. Slots may repeat wires. Commutativity permits partitioning
the contributions; no cancellation, inverse, or group structure is required.
-/

@[expose] public section

namespace Algebraic.Aggregate

variable {J : Type} (State : J → Type)

/-- A full binary Boolean operation or a finite-arity aggregate operation. -/
inductive Op where
  | binary (function : Bool → Bool → Bool)
  | special (kind : J) (arity : ℕ)
      (contribution : Fin arity → Bool → State kind) (readout : State kind → Bool)

/-- The mixed signature retains the special operation's ordered slots. -/
abbrev signature : Signature where
  Op := Op State
  Arity
    | .binary _ => 2
    | .special _ arity _ _ => arity

variable {State}

/-- Whether an operation needs an aggregate consistency check. -/
def Op.isSpecial : Op State → Bool
  | .binary _ => false
  | .special .. => true

/-- The register carried by an operation; binary operations need no register. -/
abbrev Op.Register : Op State → Type
  | .binary _ => PUnit
  | .special kind _ _ _ => State kind

instance [∀ j, CommMonoid (State j)] (op : Op State) : CommMonoid op.Register := by
  cases op <;> dsimp [Op.Register] <;> infer_instance

instance [∀ j, Fintype (State j)] (op : Op State) : Fintype op.Register := by
  cases op <;> dsimp [Op.Register] <;> infer_instance

/-- A slot's contribution; the unused register of a binary gate is trivial. -/
def Op.slotContribution (op : Op State) :
    Fin ((signature State).Arity op) → Bool → op.Register :=
  match op with
  | .binary _ => fun _ _ => PUnit.unit
  | .special _ _ contribution _ => contribution

/-- The Boolean predicate applied to a special register; unused on binary operations. -/
def Op.readout (op : Op State) : op.Register → Bool :=
  match op with
  | .binary _ => fun _ => false
  | .special _ _ _ readout => readout

/-- Boolean evaluation of the mixed signature. -/
def interpretation [∀ j, CommMonoid (State j)] : Interpretation (signature State) Bool
  | .binary f, arguments => f (arguments 0) (arguments 1)
  | .special _ _ contribution readout, arguments =>
      readout (∏ slot, contribution slot (arguments slot))

/-- Operations of the ordinary circuit after guessing all special output bits. -/
inductive OrdinaryOp where
  | binary (function : Bool → Bool → Bool)
  | constant (value : Bool)

/-- Erased special gates have zero incoming wires. -/
abbrev ordinarySignature : Signature where
  Op := OrdinaryOp
  Arity
    | .binary _ => 2
    | .constant _ => 0

/-- Interpretation of binary operations and guessed constants. -/
def ordinaryInterpretation : Interpretation ordinarySignature Bool
  | .binary f, arguments => f (arguments 0) (arguments 1)
  | .constant value, _ => value

/-- Each ordinary operation has at most two input slots. -/
theorem ordinary_arity_le_two (op : OrdinaryOp) : ordinarySignature.Arity op ≤ 2 := by
  cases op <;> simp

end Algebraic.Aggregate
