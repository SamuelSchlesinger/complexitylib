/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.HighRate.Residue
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting common-zero-block monomials

For the asymptotic construction it is enough to take field widths that are
multiples of the block width. Exponents are then base-`2^h` digit strings.
After transposing the digit matrix, the retained monomials are exactly the
strings of digit columns containing an all-zero column. Their cardinality is
`A^m - (A-1)^m`, where `A = 2^(dimension*h)`.
-/

@[expose] public section

namespace Algebraic.MassProduction.HighRate

open scoped BigOperators

/-- Number of words containing a specified letter at least once. -/
theorem cardWordsContaining
    {Alphabet : Type*} [Fintype Alphabet] (letter : Alphabet) (length : Nat) :
    Nat.card {word : Fin length → Alphabet // ∃ index, word index = letter} =
      Fintype.card Alphabet ^ length - (Fintype.card Alphabet - 1) ^ length := by
  classical
  have avoided : Fintype.card {word : Fin length → Alphabet // ∀ index, word index ≠ letter} =
      (Fintype.card Alphabet - 1) ^ length := by
    rw [Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun _ value => value ≠ letter))]
    simp [Fintype.card_pi]
  rw [Nat.card_eq_fintype_card]
  have complemented := Fintype.card_subtype_compl
    (fun word : Fin length → Alphabet => ∀ index, word index ≠ letter)
  simpa only [not_forall, not_not, Fintype.card_fun, Fintype.card_fin, avoided] using complemented

/-- A matrix with one base-`2^h` digit per coordinate and per digit block. -/
abbrev DigitMatrix (Coordinate : Type*) (blockWidth blocks : Nat) :=
  Fin blocks → Coordinate → Fin (2 ^ blockWidth)

/-- Retain exactly the digit matrices having a common all-zero block. -/
abbrev RetainedDigits (Coordinate : Type*) (blockWidth blocks : Nat) :=
  {digits : DigitMatrix Coordinate blockWidth blocks // ∃ block, digits block = 0}

/-- Reading each coordinate's digits as a natural exponent is a bijection
with all reduced exponent vectors. -/
def digitExponentEquiv (Coordinate : Type*) (blockWidth blocks : Nat) :
    DigitMatrix Coordinate blockWidth blocks ≃
      (Coordinate → Fin ((2 ^ blockWidth) ^ blocks)) :=
  (Equiv.piComm fun _ : Fin blocks => fun _ : Coordinate => Fin (2 ^ blockWidth)).trans
    (Equiv.piCongrRight fun _ => finFunctionFinEquiv)

/-- The natural exponent vector represented by a digit matrix. -/
def digitDegrees (digits : DigitMatrix Coordinate blockWidth blocks) : Coordinate → Nat :=
  fun coordinate => (digitExponentEquiv Coordinate blockWidth blocks digits coordinate).val

/-- Every digit matrix encodes reduced exponents for a field of width
`blockWidth * blocks`. -/
theorem digitDegrees_lt (digits : DigitMatrix Coordinate blockWidth blocks)
    (coordinate : Coordinate) :
    digitDegrees digits coordinate < 2 ^ (blockWidth * blocks) := by
  simpa only [digitDegrees, ← pow_mul] using
    (digitExponentEquiv Coordinate blockWidth blocks digits coordinate).isLt

/-- Extracting one encoded digit returns the original digit. -/
theorem digitDegreesDigit (digits : DigitMatrix Coordinate blockWidth blocks)
    (block : Fin blocks) (coordinate : Coordinate) :
    digitDegrees digits coordinate / 2 ^ (blockWidth * block.val) % 2 ^ blockWidth =
      (digits block coordinate).val := by
  have roundTrip := congrFun (finFunctionFinEquiv.symm_apply_apply
    (fun index => digits index coordinate)) block
  change (finFunctionFinEquiv (fun index => digits index coordinate)).val /
      2 ^ (blockWidth * block.val) % 2 ^ blockWidth = _
  rw [pow_mul]
  exact congrArg Fin.val roundTrip

/-- Every retained matrix supplies a common zero block in its exponent
vector. The block starts at `blockWidth * block`. -/
theorem retainedDigitsCommonZeroBlock
    (digits : RetainedDigits Coordinate blockWidth blocks) :
    ∃ block : Fin blocks, CommonZeroBlock (digitDegrees digits.val)
      (blockWidth * block.val) blockWidth := by
  obtain ⟨block, blockZero⟩ := digits.property
  refine ⟨block, (commonZeroBlock_iff _ _ _).mpr ?_⟩
  intro coordinate
  rw [digitDegreesDigit, congrFun blockZero coordinate]
  rfl

/-- Exact dimension of the chosen monomial family before evaluation. -/
theorem cardRetainedDigits (Coordinate : Type*) [Fintype Coordinate]
    (blockWidth blocks : Nat) :
    Nat.card (RetainedDigits Coordinate blockWidth blocks) =
      (2 ^ (blockWidth * Fintype.card Coordinate)) ^ blocks -
        (2 ^ (blockWidth * Fintype.card Coordinate) - 1) ^ blocks := by
  classical
  have counted := cardWordsContaining (0 : Coordinate → Fin (2 ^ blockWidth)) blocks
  simpa only [Fintype.card_fun, Fintype.card_fin, ← pow_mul] using counted

end Algebraic.MassProduction.HighRate
