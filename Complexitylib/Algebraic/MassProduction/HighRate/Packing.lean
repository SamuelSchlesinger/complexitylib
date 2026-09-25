/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.HighRate.Rate

/-!
# Packing many high-rate code copies without rounding loss

Take one plus the quotient of the desired source-bit count by the message
capacity of one code. This fits all source bits and loses at most one whole
codeword to rounding. The integer rate inequality transfers directly to the
total physical storage. The actual placement can be chosen offline and used
as a single batched prefix lookup table.
-/

@[expose] public section

namespace Algebraic.MassProduction.HighRate

/-- A sufficient number of code copies, including one final partial copy. -/
def packingCopies (sourceBits messageSymbols symbolBits : Nat) : Nat :=
  sourceBits / (messageSymbols * symbolBits) + 1

/-- All source bits fit in the chosen copies' information positions. -/
theorem packingCopies_capacity
    (sourceBits messageSymbols symbolBits : Nat)
    (messagePositive : 0 < messageSymbols) (symbolPositive : 0 < symbolBits) :
    sourceBits ≤ packingCopies sourceBits messageSymbols symbolBits * messageSymbols * symbolBits := by
  have remainder := Nat.mod_lt sourceBits (Nat.mul_pos messagePositive symbolPositive)
  have division := Nat.mod_add_div sourceBits (messageSymbols * symbolBits)
  unfold packingCopies
  rw [Nat.mul_assoc, Nat.add_mul, Nat.one_mul, Nat.mul_comm
    (sourceBits / (messageSymbols * symbolBits)) (messageSymbols * symbolBits)]
  omega

/-- The storage expansion is the code-rate expansion plus at most one
codeword's worth of rounding. -/
theorem packingCopies_storage
    (sourceBits messageSymbols codeSymbols symbolBits precision : Nat)
    (rate : precision * codeSymbols ≤ (precision + 1) * messageSymbols) :
    precision * (packingCopies sourceBits messageSymbols symbolBits * codeSymbols * symbolBits) ≤
      (precision + 1) * sourceBits + precision * (codeSymbols * symbolBits) := by
  let quotient := sourceBits / (messageSymbols * symbolBits)
  have fullCopies : quotient * (messageSymbols * symbolBits) ≤ sourceBits :=
    Nat.div_mul_le_self _ _
  have fullStorage : precision * (quotient * codeSymbols * symbolBits) ≤
      (precision + 1) * sourceBits := by
    calc
      _ = quotient * (precision * codeSymbols) * symbolBits := by ring
      _ ≤ quotient * ((precision + 1) * messageSymbols) * symbolBits := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ rate)
      _ = (precision + 1) * (quotient * (messageSymbols * symbolBits)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ fullCopies
  calc
    _ = precision * (quotient * codeSymbols * symbolBits) + precision * (codeSymbols * symbolBits) := by
      unfold packingCopies quotient
      ring
    _ ≤ _ := Nat.add_le_add_right fullStorage _

/-- An offline injection assigns every source bit to a distinct code,
information symbol, and binary coordinate. -/
theorem existsPackingPlacement
    {Information : Type*} [Fintype Information]
    (sourceBits symbolBits : Nat)
    (informationPositive : 0 < Fintype.card Information) (symbolPositive : 0 < symbolBits) :
    Nonempty (Fin sourceBits ↪
      (Fin (packingCopies sourceBits (Fintype.card Information) symbolBits) ×
        Information × Fin symbolBits)) := by
  classical
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_fin, Fintype.card_prod, Nat.mul_assoc] using
    packingCopies_capacity sourceBits (Fintype.card Information) symbolBits
      informationPositive symbolPositive

end Algebraic.MassProduction.HighRate
