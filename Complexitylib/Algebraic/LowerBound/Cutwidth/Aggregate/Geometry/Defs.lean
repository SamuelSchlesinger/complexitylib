/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Binary
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Pi

/-!
# Signed unbounded AND and XOR circuits

Every operation is either an affine Boolean function or a conjunction of signed
inputs with an optional output negation. This includes unbounded AND, OR, XOR,
constants, and the full binary basis. Programs use the existing acyclic circuit
model: every operation costs one gate and repeated wires and unrestricted fanout
are allowed. The geometric count records conjunctions with at least two distinct
direct primary inputs, including repeated literals of either polarity.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

/-- Parity of a finite indexed family of bits. -/
def xorSum : {r : ℕ} → (Fin r → Bool) → Bool
  | 0, _ => false
  | _ + 1, x => x 0 ^^ xorSum (Fin.tail x)

/-- Affine operations and optionally negated conjunctions of signed literals. -/
inductive Op where
  | affine (arity : ℕ) (bias : Bool) (coefficient : Fin arity → Bool)
  | conjunction (arity : ℕ) (polarity : Fin arity → Bool) (negated : Bool)

/-- The actual number of input slots of an operation. -/
abbrev Op.arity : Op → ℕ
  | .affine r _ _ => r
  | .conjunction r _ _ => r

/-- Signature for signed AND/OR/XOR circuits. -/
abbrev signature : Signature := ⟨Op, Op.arity⟩

/-- Every conjunction input is a genuine, possibly negated literal. -/
def conjunctionValue {r : ℕ} (polarity : Fin r → Bool) (negated : Bool)
    (x : Fin r → Bool) : Bool :=
  negated ^^ decide (∀ i, x i = polarity i)

/-- Boolean semantics of the signed operations. -/
def interpretation : Interpretation signature Bool
  | .affine _ bias coefficient, x => bias ^^ xorSum (fun i => coefficient i && x i)
  | .conjunction _ polarity negated, x => conjunctionValue polarity negated x

/-- Whether the operation uses the conjunction form. -/
def Op.isConjunction : Op → Bool
  | .affine .. => false
  | .conjunction .. => true

variable {n g : ℕ}

/-- Distinct original input variables appearing directly among a line's slots. -/
def primaryInputs (line : Line signature n g) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ slot, line.wires slot = .input i

/-- Conjunctions with at least two distinct direct original input variables. -/
def multiPrimary (line : Line signature n g) : Bool :=
  line.op.isConjunction && decide (2 ≤ (primaryInputs line).card)

/-- Number of multiple-primary conjunctions in an actual program. -/
def multiCount : {g : ℕ} → Program signature n g → ℕ
  | _, .empty => 0
  | _, .gate p line => multiCount p + if multiPrimary line then 1 else 0

end Algebraic.Aggregate.Geometry
