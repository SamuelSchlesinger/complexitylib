/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Encoding.Arithmetic

/-!
# Validation of the structure wire format

A string at a specified universe size has the prescribed length and unary
header, and every constant block is one-hot. Relation tables are unrestricted.
The tests use natural-number addresses, suitable for polynomial-time loops.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

/-- The structure wire format at a specified universe size, including all one-hot blocks. -/
def IsValidEncoding (V : Vocabulary) (card : Nat) (bits : List Bool) : Prop :=
  2 ≤ card ∧ bits.length = encodingLength V card ∧
    (∀ i < card + 1, bits[i]?.getD false = decide (i < card)) ∧
    ∀ c : Fin V.numConsts, ∃ a < card, ∀ b < card,
      bits[constantAddress V card c b]?.getD false = decide (a = b)

end Complexity.DescriptiveComplexity
