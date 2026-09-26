/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Encoding.DataEncode
import Complexitylib.Classes.Containments.Internal.FPBridge
import Complexitylib.Classes.P.NatCodes
import Complexitylib.Classes.P.DataEncode.Internal.Write

/-!
# Writing encodings in polynomial time

A polynomial-time construction that hands its result to a `DataEncode` consumer,
such as a verifier reading a list of query positions, has to write the
`DataEncode.bitstringEncode` of that result. This module shows that writing the
encoding of a bit list, and of a number, is polynomial-time.

A bit list is encoded as the encodings of its bits between two brackets, and
writing that is a fold over the list (`encodeList_mem_FP`). A number is encoded
as its minimal binary expansion `Nat.bits`, so writing a polynomial-time
number's encoding is writing its expansion (`bits_mem_FP`) and then encoding
that list (`natEncode_mem_FP`). No width has to be supplied.

## Main results

- `encodeList_mem_FP` — writing the encoding of a bit list is polynomial-time
- `natEncode_mem_FP` — writing the encoding of a polynomial-time number is
  polynomial-time
-/

public section

namespace Complexity

/-- **Writing the encoding of a bit list is polynomial-time.** If `a ∈ FP`, then
so is `z ↦ DataEncode.bitstringEncode (a z)`. -/
theorem encodeList_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => DataEncode.bitstringEncode (a z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.appendFn_mem_FP (encodeBody_mem_FP ha)
    (constFn_mem_FP [true])) (Cobham.cons_mem_FP false))
    fun z => (bitstringEncode_eq_encodeBody (a z)).symm

/-- **Writing the encoding of a polynomial-time number is polynomial-time.** If
`n` is a polynomial-time number, then `z ↦ DataEncode.bitstringEncode (n z)` is
in `FP`: a number is encoded as its minimal binary expansion. -/
theorem natEncode_mem_FP {n : List Bool → ℕ} (hn : UnaryFn n) :
    (fun z => DataEncode.bitstringEncode (n z)) ∈ FP :=
  encodeList_mem_FP (bits_mem_FP hn)

end Complexity
