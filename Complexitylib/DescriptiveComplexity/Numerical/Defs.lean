/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Definable
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Bitwise

/-!
# Canonical numerical predicates for first-order logic

Append selected numerical relation symbols to an input vocabulary and interpret
them canonically on `Fin card`. Order and BIT are binary; addition and
multiplication are ternary graphs of natural arithmetic restricted to the
universe, without modular wraparound. BIT takes the number before the bit index.

These extensions use the existing relation atoms, substitution, and semantics.
Input relations and constants retain their meanings. Definability with numerical
predicates is evaluated only on canonical expansions, so it does not assert
invariance under arbitrary permutations of the original input structure.

The numerical-predicate convention follows Immerman's *Descriptive Complexity*
and Schweikardt--Schwentick, *A note on the expressive power of linear orders*
(2011), Section 2, <https://lmcs.episciences.org/1008/pdf>.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

/-- Numerical relations available as designated symbols in a vocabulary extension. -/
inductive NumericalPredicate where
  /-- Strict canonical order. -/
  | lt
  /-- `bit x i` tests bit `i` of the natural number `x`, starting at zero. -/
  | bit
  /-- The ternary graph `x + y = z` of natural addition. -/
  | add
  /-- The ternary graph `x * y = z` of natural multiplication. -/
  | mul
  deriving DecidableEq

/-- Number of arguments of each designated numerical relation. -/
abbrev NumericalPredicate.arity : NumericalPredicate → Nat
  | .lt | .bit => 2
  | .add | .mul => 3

/-- Interpret a numerical relation on natural-number arguments. -/
def NumericalPredicate.Holds : (p : NumericalPredicate) → (Fin p.arity → Nat) → Prop
  | .lt, args => args 0 < args 1
  | .bit, args => (args 0).testBit (args 1) = true
  | .add, args => args 0 + args 1 = args 2
  | .mul, args => args 0 * args 1 = args 2

instance (p : NumericalPredicate) (args : Fin p.arity → Nat) : Decidable (p.Holds args) := by
  cases p <;> dsimp only [NumericalPredicate.Holds] <;> infer_instance

/-- Append numerical relation symbols, preserving the input vocabulary's constants. -/
def Vocabulary.withNumerical (V : Vocabulary) (predicates : List NumericalPredicate) :
    Vocabulary where
  numRels := V.numRels + predicates.length
  relArity := Fin.addCases V.relArity (fun i => (predicates.get i).arity)
  numConsts := V.numConsts

/-- The input vocabulary with canonical strict order. -/
abbrev Vocabulary.withOrder (V : Vocabulary) : Vocabulary := V.withNumerical [.lt]

/-- The input vocabulary with the canonical BIT predicate. -/
abbrev Vocabulary.withBit (V : Vocabulary) : Vocabulary := V.withNumerical [.bit]

/-- The input vocabulary with the graphs of addition and multiplication. -/
abbrev Vocabulary.withArithmetic (V : Vocabulary) : Vocabulary := V.withNumerical [.add, .mul]

/-- Expand an input structure by the selected canonical numerical relations. -/
def FinStruct.withNumerical {V : Vocabulary} (A : FinStruct V)
    (predicates : List NumericalPredicate) : FinStruct (V.withNumerical predicates) where
  card := A.card
  hcard := A.hcard
  rel r := by
    refine Fin.addCases (fun i args => ?_) (fun j args => ?_) r
    · exact A.rel i (fun k => args (Fin.cast (by simp [Vocabulary.withNumerical]) k))
    · exact (predicates.get j).Holds
        (fun k => (args (Fin.cast (by simp [Vocabulary.withNumerical]) k)).val)
  const := A.const

/-- The computable Boolean version of canonical numerical expansion. -/
def DecFinStruct.withNumerical {V : Vocabulary} (A : DecFinStruct V)
    (predicates : List NumericalPredicate) : DecFinStruct (V.withNumerical predicates) where
  card := A.card
  hcard := A.hcard
  rel r := by
    refine Fin.addCases (fun i args => ?_) (fun j args => ?_) r
    · exact A.rel i (fun k => args (Fin.cast (by simp [Vocabulary.withNumerical]) k))
    · exact decide ((predicates.get j).Holds
        (fun k => (args (Fin.cast (by simp [Vocabulary.withNumerical]) k)).val))
  const := A.const

/-- Forget the additional symbols through a quantifier-free first-order interpretation. -/
def FOInterpretation.forgetNumerical (V : Vocabulary) (predicates : List NumericalPredicate) :
    FOInterpretation (V.withNumerical predicates) V where
  relFormula r := .relApp (Fin.castAdd predicates.length r) fun i =>
    .var (Fin.cast (by simp [Vocabulary.withNumerical]) i)
  constMap := id

/-- Regard an input formula as a formula over the extended numerical vocabulary. -/
def Formula.withNumerical {V : Vocabulary} {n : Nat} (φ : Formula V n)
    (predicates : List NumericalPredicate) : Formula (V.withNumerical predicates) n :=
  (FOInterpretation.forgetNumerical V predicates).translate φ

/-- Apply a selected numerical relation symbol to terms in the extended vocabulary. -/
def Formula.numerical {V : Vocabulary} {n : Nat} (predicates : List NumericalPredicate)
    (r : Fin predicates.length)
    (args : Fin (predicates.get r).arity → Term (V.withNumerical predicates) n) :
    Formula (V.withNumerical predicates) n :=
  .relApp (Fin.natAdd V.numRels r) fun i =>
    args (Fin.cast (by simp [Vocabulary.withNumerical]) i)

/-- Strict canonical order as an ordinary first-order atom. -/
def Formula.orderLt {V : Vocabulary} {n : Nat} (x y : Term V.withOrder n) :
    Formula V.withOrder n := .numerical [.lt] 0 ![x, y]

/-- The zero-based bit test, with the number before its bit index. -/
def Formula.bit {V : Vocabulary} {n : Nat} (x i : Term V.withBit n) :
    Formula V.withBit n := .numerical [.bit] 0 ![x, i]

/-- Natural addition restricted to the finite universe, without modular wraparound. -/
def Formula.add {V : Vocabulary} {n : Nat} (x y z : Term V.withArithmetic n) :
    Formula V.withArithmetic n := .numerical [.add, .mul] 0 ![x, y, z]

/-- Natural multiplication restricted to the finite universe, without modular wraparound. -/
def Formula.mul {V : Vocabulary} {n : Nat} (x y z : Term V.withArithmetic n) :
    Formula V.withArithmetic n := .numerical [.add, .mul] 1 ![x, y, z]

/-- FO definability on the canonical expansions by the selected numerical predicates. -/
def FODefinableWithNumerical {V : Vocabulary} (predicates : List NumericalPredicate)
    (Q : BooleanQuery V) : Prop :=
  ∃ φ : Sentence (V.withNumerical predicates),
    ∀ A : FinStruct V, Q A ↔ Sentence.Models (A.withNumerical predicates) φ

end Complexity.DescriptiveComplexity
