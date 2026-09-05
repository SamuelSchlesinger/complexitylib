/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.CoinEnum

/-!
# Writing symbols as fixed-width blocks

A proof for a constraint graph is an assignment written out, one fixed-width
block per vertex. This module supplies the block: any finite alphabet small
enough is written as its index in binary, at a width the caller chooses.

The codec need not be computable — a verifier's *decision* has to be
polynomial-time, but the correspondence between symbols and blocks is only used
to state what the decision means.

## Main definitions

- `Complexity.symEnc`, `Complexity.symDec` — the block of a symbol, and back

## Main results

- `Complexity.symDec_symEnc` — the codec round-trips
- `Complexity.length_symEnc` — blocks have the chosen width
-/

@[expose] public section

namespace Complexity

variable (α : Type) [Fintype α] [Inhabited α]

/-- The block a symbol occupies: its index, in binary, at width `w`. -/
noncomputable def symEnc (w : ℕ) (s : α) : List Bool :=
  bitsOfLenLE w (Fintype.equivFin α s).val

/-- The symbol a block names. -/
noncomputable def symDec (u : List Bool) : α :=
  if h : binValLE u < Fintype.card α then (Fintype.equivFin α).symm ⟨binValLE u, h⟩
  else default

variable {α}

omit [Inhabited α] in
@[simp] theorem length_symEnc (w : ℕ) (s : α) : (symEnc α w s).length = w := by
  rw [symEnc, bitsOfLenLE_length]

/-- **The codec round-trips**, as long as the width holds the alphabet. -/
theorem symDec_symEnc {w : ℕ} (h : Fintype.card α ≤ 2 ^ w) (s : α) :
    symDec α (symEnc α w s) = s := by
  have hlt : (Fintype.equivFin α s).val < 2 ^ w :=
    lt_of_lt_of_le (Fintype.equivFin α s).isLt h
  have hval : binValLE (symEnc α w s) = (Fintype.equivFin α s).val := by
    rw [symEnc, binValLE_bitsOfLenLE _ _ hlt]
  rw [symDec, hval, dite_eq_left (Fintype.equivFin α s).isLt]
  simp

end Complexity
