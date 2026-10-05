/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Compressed.Defs
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Compression by the rank of modular contributions

For aggregate gates over one prime modulus, the two possible contributions of
each circuit signal are columns of a matrix. Its column space is an actual joint
register, with exactly `p ^ rank` states. Arbitrary readouts, repeated slots, and
dependencies between special gates are included in this construction.
-/

@[expose] public section

namespace Algebraic.Aggregate.Compressed.Modular

/-- The additive modular register, written multiplicatively for the aggregate API. -/
abbrev State (p : ℕ) (_ : Unit) := Multiplicative (ZMod p)

variable {p n g : ℕ}

/-- A weighted modular equality gate; all weights one give the usual MOD gate. -/
def gate (weights : Fin n → ZMod p) (target : ZMod p) : Op (State p) :=
  .special () n (fun slot value => Multiplicative.ofAdd (if value then weights slot else 0))
    (fun state => decide (state.toAdd = target))

/-- Every special gate in the modular signature has the same modular register. -/
def registerEquiv (op : Op (State p)) (h : op.isSpecial = true) :
    op.Register ≃* Multiplicative (ZMod p) := by
  cases op with
  | binary f => simp [Op.isSpecial] at h
  | special kind arity contribution readout => exact MulEquiv.refl _

variable (c : Program (signature (State p)) n g)

/-- All dependent special registers identify with a vector of residues. -/
def registersEquiv : Registers c ≃* Multiplicative (SpecialGate c → ZMod p) :=
  (MulEquiv.piCongrRight fun gate : SpecialGate c =>
    registerEquiv (c.lines gate).op gate.property).trans
    (MulEquiv.piMultiplicative fun _ : SpecialGate c => ZMod p).symm

/-- The two possible contribution columns for each signal, counting repeated slots. -/
def contributionMatrix : Matrix (SpecialGate c) (Wire n g × Bool) (ZMod p) :=
  fun gate column => (registersEquiv c (wireContribution c column.1 column.2)).toAdd gate

/-- The concrete space spanned by the joint modular contributions. -/
def contributionSpace : Submodule (ZMod p) (SpecialGate c → ZMod p) :=
  Submodule.span (ZMod p) (Set.range (contributionMatrix c).col)

/-- Joint modular information is measured by the rank of the contribution matrix. -/
noncomputable def contributionRank : ℕ := (contributionMatrix c).rank

/-- A vector in the contribution space is one compressed aggregate state. -/
abbrev CompressedState := Multiplicative (contributionSpace c)

noncomputable instance [NeZero p] : Fintype (contributionSpace c) := Fintype.ofFinite _

/-- The column-space inclusion decodes the joint special registers. -/
def decode : CompressedState c →* Registers c :=
  (registersEquiv c).symm.toMonoidHom.comp
    (contributionSpace c).subtype.toAddMonoidHom.toMultiplicative

/-- Every modular circuit factors through its contribution space, without a rank premise. -/
def factorization : Factorization c (CompressedState c) where
  contribution wire value := Multiplicative.ofAdd
    ⟨(contributionMatrix c).col (wire, value), Submodule.subset_span ⟨(wire, value), rfl⟩⟩
  decode := decode c
  factor _ _ := (registersEquiv c).symm_apply_apply _

/-- The rank counts the independent modular coordinates in the concrete compressed state. -/
theorem contributionRank_eq_finrank :
    contributionRank c = Module.finrank (ZMod p) (contributionSpace c) :=
  Matrix.rank_eq_finrank_span_cols _

/-- Over a prime modulus, the joint state space has exactly one residue per rank coordinate. -/
theorem card_compressedState [Fact p.Prime] :
    Fintype.card (CompressedState c) = p ^ contributionRank c := by
  rw [Fintype.card_multiplicative, Module.card_eq_pow_finrank (K := ZMod p),
    ZMod.card, ← contributionRank_eq_finrank]

/-- Matrix rank never exceeds the number of modular gates. -/
theorem contributionRank_le_specialCount [Fact p.Prime] :
    contributionRank c ≤ specialCount c := Matrix.rank_le_card_height _

/-- The compiler charges the rank-based joint state twice, for guessing and checking. -/
theorem budget_compressedState [Fact p.Prime] :
    budget (CompressedState c) = 2 * Nat.clog 2 (p ^ contributionRank c) := by
  rw [budget, card_compressedState]

/-- A matrix factorization through `r` coordinates certifies a rank bound. -/
theorem contributionRank_le_of_factor [Fact p.Prime] {r : ℕ}
    (left : Matrix (SpecialGate c) (Fin r) (ZMod p))
    (right : Matrix (Fin r) (Wire n g × Bool) (ZMod p))
    (h : contributionMatrix c = left * right) : contributionRank c ≤ r := by
  unfold contributionRank
  rw [h]
  exact (Matrix.rank_mul_le_left left right).trans (by
    simpa using Matrix.rank_le_card_width left)

/-- For a fixed modulus, the compressed budget is bounded linearly by matrix rank. -/
theorem budget_compressedState_le [Fact p.Prime] :
    budget (CompressedState c) ≤ 2 * contributionRank c * Nat.clog 2 p := by
  rw [budget_compressedState, Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  apply Nat.clog_le_of_le_pow
  calc
    p ^ contributionRank c ≤ (2 ^ Nat.clog 2 p) ^ contributionRank c := by
      gcongr
      exact (Nat.clog_le_iff_le_pow (by decide)).mp (le_refl (Nat.clog 2 p))
    _ = 2 ^ (contributionRank c * Nat.clog 2 p) := by rw [← pow_mul, Nat.mul_comm]

end Algebraic.Aggregate.Compressed.Modular
