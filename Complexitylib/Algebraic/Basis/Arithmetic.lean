/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Cost
public import Mathlib.Data.Fintype.Sum

/-!
# Arithmetic circuit basis

The arithmetic basis has binary addition and multiplication together with a
family of nullary constants.  The constant symbols are parameterized
independently of the semantic carrier, so the same syntax can be interpreted
in a polynomial ring, an extension field, a quotient, or an abstract algebra.

No ring laws are built into the circuit syntax.  `interpretation` only asks for
addition and multiplication on the carrier and for a map assigning semantic
values to constant symbols.  Algebraic laws and homomorphism properties belong
to the chosen interpretations.
-/

@[expose] public section

namespace Algebraic
namespace Arithmetic

/-- Addition, multiplication, and a parameterized family of constants. -/
inductive Op (K : Type u)
  | add
  | mul
  | constant (value : K)
  deriving DecidableEq

/-- Arithmetic operations are equivalent to two binary symbols plus the
constant-symbol type. -/
def opEquiv : Op K ≃ (Bool ⊕ K) where
  toFun
    | .add => .inl false
    | .mul => .inl true
    | .constant value => .inr value
  invFun
    | .inl false => .add
    | .inl true => .mul
    | .inr value => .constant value
  left_inv op := by cases op <;> rfl
  right_inv value := by
    cases value with
    | inl tag => cases tag <;> rfl
    | inr value => rfl

/-- A finite constant alphabet gives a finite arithmetic signature. -/
noncomputable instance [Fintype K] : Fintype (Op K) :=
  Fintype.ofEquiv (Bool ⊕ K) (opEquiv (K := K)).symm

/-- Arity of an arithmetic operation. -/
def arity : Op K → Nat
  | .add | .mul => 2
  | .constant _ => 0

@[simp] theorem arity_add : arity (Op.add : Op K) = 2 := rfl
@[simp] theorem arity_mul : arity (Op.mul : Op K) = 2 := rfl
@[simp] theorem arity_constant (value : K) :
    arity (.constant value) = 0 := rfl

/-- Signature of arithmetic circuits with constants named by `K`. -/
abbrev signature (K : Type u) : Signature where
  Op := Op K
  Arity := arity

/-- Interpret arithmetic syntax in any carrier with addition and
multiplication, using `constant` to interpret the nullary symbols. -/
def interpretation
    [Add R]
    [Mul R]
    (constant : K → R) :
    (op : Op K) → (Fin (arity op) → R) → R
  | .add, input =>
      input (Fin.cast (by rfl) (0 : Fin 2)) +
        input (Fin.cast (by rfl) (1 : Fin 2))
  | .mul, input =>
      input (Fin.cast (by rfl) (0 : Fin 2)) *
        input (Fin.cast (by rfl) (1 : Fin 2))
  | .constant value, _ => constant value

/-- Interpret constants by themselves in their native arithmetic carrier. -/
def nativeInterpretation
    [Add K]
    [Mul K] : Interpretation (signature K) K :=
  interpretation id

/-- Charge additions and multiplications independently; constants are free. -/
def weightedCost
    (addition multiplication : Nat) : OperationCost (signature K)
  | .add => addition
  | .mul => multiplication
  | .constant _ => 0

/-- Standard arithmetic gate count: additions and multiplications cost one. -/
def gateCost : OperationCost (signature K) :=
  weightedCost 1 1

/-- Multiplicative complexity: only multiplication gates are charged. -/
def multiplicationCost : OperationCost (signature K) :=
  weightedCost 0 1

/-- Additive complexity: only addition gates are charged. -/
def additionCost : OperationCost (signature K) :=
  weightedCost 1 0

@[simp] theorem weightedCost_add
    (addition multiplication : Nat) :
    weightedCost (K := K) addition multiplication .add = addition := rfl

@[simp] theorem weightedCost_mul
    (addition multiplication : Nat) :
    weightedCost (K := K) addition multiplication .mul = multiplication := rfl

@[simp] theorem weightedCost_constant
    (addition multiplication : Nat)
    (value : K) :
    weightedCost addition multiplication (.constant value) = 0 := rfl

@[simp] theorem gateCost_add : gateCost (K := K) .add = 1 := rfl
@[simp] theorem gateCost_mul : gateCost (K := K) .mul = 1 := rfl
@[simp] theorem gateCost_constant (value : K) :
    gateCost (.constant value) = 0 := rfl

@[simp] theorem multiplicationCost_add :
    multiplicationCost (K := K) .add = 0 := rfl
@[simp] theorem multiplicationCost_mul :
    multiplicationCost (K := K) .mul = 1 := rfl
@[simp] theorem multiplicationCost_constant (value : K) :
    multiplicationCost (.constant value) = 0 := rfl

@[simp] theorem additionCost_add : additionCost (K := K) .add = 1 := rfl
@[simp] theorem additionCost_mul : additionCost (K := K) .mul = 0 := rfl
@[simp] theorem additionCost_constant (value : K) :
    additionCost (.constant value) = 0 := rfl

end Arithmetic
end Algebraic
