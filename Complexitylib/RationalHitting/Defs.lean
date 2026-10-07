/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Computability.TuringMachine.StackTuringMachine
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Tactic

/-!
# Rational hitting lists: model

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/Model.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting

universe u

/-- A noncommutative rational formula over `n` variables and rational constants. -/
inductive Formula (n : ℕ) where
  /-- An input variable. -/
  | var : Fin n → Formula n
  /-- A rational scalar. -/
  | const : ℚ → Formula n
  /-- Addition of two subformulas. -/
  | add : Formula n → Formula n → Formula n
  /-- Ordered multiplication of two subformulas. -/
  | mul : Formula n → Formula n → Formula n
  /-- Inversion, defined only when the evaluated operand is a unit. -/
  | inv : Formula n → Formula n
  deriving DecidableEq

namespace Formula

/-- Number of syntax-tree nodes, counting variables, constants, and operations. -/
def size {n : ℕ} : Formula n → ℕ
  | .var _ | .const _ => 1
  | .add f g | .mul f g => f.size + g.size + 1
  | .inv f => f.size + 1

/-- Evaluation in any rational algebra; a unary inverse requires an actual
    two-sided inverse of the evaluated operand, not a totalized inverse. -/
inductive Eval {n : ℕ} {R : Type u} [Ring R]
    (c : ℚ →+* R) (X : Fin n → R) : Formula n → R → Prop where
  /-- A variable evaluates to its assigned value. -/
  | var (i) : Eval c X (.var i) (X i)
  /-- A constant evaluates through the specified scalar homomorphism. -/
  | const (a) : Eval c X (.const a) (c a)
  /-- Defined summands give a defined sum. -/
  | add {f g a b} : Eval c X f a → Eval c X g b → Eval c X (.add f g) (a + b)
  /-- Defined factors give a defined ordered product. -/
  | mul {f g a b} : Eval c X f a → Eval c X g b → Eval c X (.mul f g) (a * b)
  /-- Both inverse identities are required at an inverse node. -/
  | inv {f a b} : Eval c X f a → a * b = 1 → b * a = 1 → Eval c X (.inv f) b

end Formula

/-- Square rational matrices of the specified dimension. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℚ
/-- A matrix substitution for every input variable. -/
abbrev Tuple (n d : ℕ) := Fin n → Mat d

/-- Defined evaluation on a rational matrix tuple. -/
def Evaluates {n d : ℕ} (f : Formula n) (X : Tuple n d) (v : Mat d) : Prop :=
  f.Eval (algebraMap ℚ (Mat d)) X v

/-- Some positive-dimensional rational matrix substitution is in the formula's domain. -/
def Admissible {n : ℕ} (f : Formula n) : Prop :=
  ∃ d, 0 < d ∧ ∃ (X : Tuple n d), ∃ v, Evaluates f X v

/-- Some positive-dimensional rational matrix substitution has a defined nonzero value. -/
def Nonzero {n : ℕ} (f : Formula n) : Prop :=
  ∃ d, 0 < d ∧ ∃ (X : Tuple n d), ∃ v, Evaluates f X v ∧ v ≠ 0

/-- All output tuples have one common positive dimension. -/
structure Output (n : ℕ) where
  /-- Common dimension of all matrix tuples. -/
  dimension : ℕ
  /-- Exclude the trivial zero-dimensional matrix ring. -/
  dimension_pos : 0 < dimension
  /-- The finite list of matrix substitutions, in output order. -/
  tuples : List (Tuple n dimension)

/-- Little-endian unsigned binary, prefixed by a unary bit-length and a zero
    terminator. This is a self-delimiting binary encoding, including zero. -/
def encodeNat (a : ℕ) : List Bool :=
  let ds := (Nat.digits 2 a).map (fun b => b != 0)
  List.replicate ds.length true ++ [false] ++ ds

/-- Sign bit, binary numerator magnitude, and positive binary denominator.
    Rat.num and Rat.den are the canonical reduced numerator and denominator. -/
def encodeRat (a : ℚ) : List Bool :=
  [decide (a.num < 0)] ++ encodeNat a.num.natAbs ++ encodeNat a.den

/-- Serialize a tuple in variable, row, and column order using reduced rational encodings. -/
def encodeTuple {n d : ℕ} (X : Tuple n d) : List Bool :=
  (List.finRange n).flatMap fun i =>
    (List.finRange d).flatMap fun j =>
      (List.finRange d).flatMap fun k => encodeRat (X i j k)

/-- Encode the common dimension, tuple count, and all rational matrix entries. -/
def encodeOutput {n : ℕ} (H : Output n) : List Bool :=
  encodeNat H.dimension ++ encodeNat H.tuples.length ++ H.tuples.flatMap encodeTuple

/-- 0 is blank, 1 and 2 are the two literal binary digits, 3 is work space.
    Fixed finite tape alphabet and finite state space; no advice or oracle. -/
abbrev Alphabet := Fin 4
/-- A finite-state Mathlib machine on the fixed four-symbol alphabet. -/
abbrev Machine (m : ℕ) := Turing.TM0.Machine Alphabet (Fin (m + 1))
/-- Configuration of the corresponding Mathlib machine. -/
abbrev Config (m : ℕ) := Turing.TM0.Cfg Alphabet (Fin (m + 1))

/-- The two nonblank tape symbols representing a literal binary digit. -/
def tapeBit (b : Bool) : Alphabet := if b then 2 else 1

/-- Two unary parameters separated by one distinguished nonblank symbol. -/
def unaryInput (n s : ℕ) : List Alphabet :=
  List.replicate n 2 ++ [1] ++ List.replicate s 2

/-- Exactly t ordinary deterministic TM0 transitions. -/
def run {m : ℕ} (G : Machine m) : ℕ → Config m → Option (Config m)
  | 0, a => some a
  | t + 1, a => (Turing.TM0.step G a).bind (run G t)

/-- Halt within the given transition bound with the complete encoding at and right of the head. -/
def OutputsWithin {m n : ℕ} (G : Machine m) (s bound : ℕ) (H : Output n) : Prop :=
  ∃ t ≤ bound, ∃ a : Config m,
    run G t (Turing.TM0.init (unaryInput n s)) = some a ∧
    Turing.TM0.step G a = none ∧
    a.Tape.right₀ = Turing.ListBlank.mk ((encodeOutput H).map tapeBit)

/-- Every admissible nonzero formula of bounded size has an invertible value on the list. -/
def Hits {n : ℕ} (s : ℕ) (H : Output n) : Prop :=
  ∀ f : Formula n, f.size ≤ s → Admissible f → Nonzero f →
    ∃ X ∈ H.tuples, ∃ v, Evaluates f X v ∧ IsUnit v

/-- A fixed polynomial bound on bit time, full binary output length,
and common positive dimension. -/
def MainStatement : Prop :=
  ∃ (m : ℕ) (G : Machine m) (C k : ℕ), 0 < C ∧ 0 < k ∧
    ∀ n s : ℕ, 1 ≤ n → 1 ≤ s → ∃ H : Output n,
      H.dimension ≤ C * (n + s + 1) ^ k ∧
      (encodeOutput H).length ≤ C * (n + s + 1) ^ k ∧
      OutputsWithin G s (C * (n + s + 1) ^ k) H ∧ Hits s H

end RationalHitting

end Complexity
