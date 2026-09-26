/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Mathlib.NatBits
import Complexitylib.Classes.Containments.Internal.FPBridge
import Complexitylib.Classes.P.Range
import Complexitylib.Classes.P.Unary
import Complexitylib.Classes.P.UnaryLength
import Complexitylib.Classes.P.NatCodes.Internal

/-!
# Binary codes of numbers in polynomial time

Converting between a number written in unary, which is how
`Complexitylib.Classes.P.Unary` writes a polynomial-time number, and the same
number written in binary, least significant bit first, as `Nat.toBitsLE`,
`Nat.fromBitsLE` and `Nat.bits` do.

*Writing binary* is polynomial-time without any side condition. The width-`w`
expansion of `n` (`toBitsLE_mem_FP`) lists bit `i` of `n` at position `i`
(`toBitsLE_eq_map_range`), and each bit is a polynomial-time test on `i`. The
minimal expansion `Nat.bits n` (`bits_mem_FP`) is the expansion at width
`Nat.size n`.

*Reading binary* can only be polynomial-time up to a cap, because a numeral of
`k` bits can denote a number near `2 ^ k`, far too large to write in unary. The
value capped at a polynomial-time number is polynomial-time
(`UnaryFn.fromBitsLE_min`), and so is the value itself when the cap is known not
to bind (`UnaryFn.fromBitsLE_of_le`).

## Main results

- `toBitsLE_eq_map_range` — the fixed-width expansion, bit by bit
- `toBitsLE_mem_FP` — writing a fixed-width expansion is polynomial-time
- `bits_mem_FP`, `bits_length_mem_FP` — writing the minimal expansion is
  polynomial-time
- `UnaryFn.fromBitsLE_min`, `UnaryFn.fromBitsLE_of_le` — reading a numeral back,
  below a cap, is polynomial-time
-/

public section

namespace Complexity

variable {w n c : List Bool → ℕ} {s : List Bool → List Bool}

/-! ## Writing binary -/

/-- **The fixed-width expansion, bit by bit.** Position `i` of the width-`w`
little-endian expansion of `v` holds bit `i` of `v`. -/
theorem toBitsLE_eq_map_range (w v : ℕ) :
    Nat.toBitsLE w v = (List.range w).map fun i => decide (v / 2 ^ i % 2 = 1) := by
  induction w with
  | zero => rfl
  | succ w ih =>
    rw [List.range_succ, List.map_append, ← ih]
    simp [Nat.toBitsLE, Nat.toBits, beq_eq_decide]

/-- **Writing a fixed-width expansion is polynomial-time.** If `w` and `n` are
polynomial-time numbers, then so is writing the low `w z` bits of `n z`, least
significant first. -/
theorem toBitsLE_mem_FP (hw : UnaryFn w) (hn : UnaryFn n) :
    (fun z => Nat.toBitsLE (w z) (n z)) ∈ FP := by
  refine mem_FP_of_eq (bitwise_mem_FP hw (bit_fpPred hn).flag_mem_FP fun _ _ => ?_)
    fun z => (toBitsLE_eq_map_range _ _).symm
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate]

/-- **Writing the minimal expansion is polynomial-time**: `Nat.bits` of a
polynomial-time number, the expansion with no trailing zero. -/
theorem bits_mem_FP (hn : UnaryFn n) : (fun z => (n z).bits) ∈ FP :=
  mem_FP_of_eq (toBitsLE_mem_FP hn.size hn) fun _ => Nat.toBitsLE_size _

/-- The input length, in binary, is polynomial-time. -/
theorem bits_length_mem_FP : (fun z : List Bool => z.length.bits) ∈ FP :=
  bits_mem_FP unaryLength_mem_FP

/-! ## Reading binary -/

/-- **Reading a numeral below a cap is polynomial-time.** If `s ∈ FP` and `c` is
a polynomial-time number, then so is the value of `s z`, read least significant
bit first, capped at `c z`. (Inside the `UnaryFn` namespace a bare `min` means
`UnaryFn.min`, hence `Min.min`.) -/
theorem UnaryFn.fromBitsLE_min (hs : s ∈ FP) (hc : UnaryFn c) :
    UnaryFn fun z => Min.min (Nat.fromBitsLE (s z)) (c z) :=
  fromBitsLE_min_internal hs hc

/-- **Reading a numeral is polynomial-time** when its value is at most a
polynomial-time number. -/
theorem UnaryFn.fromBitsLE_of_le (hs : s ∈ FP) (hc : UnaryFn c)
    (h : ∀ z, Nat.fromBitsLE (s z) ≤ c z) : UnaryFn fun z => Nat.fromBitsLE (s z) :=
  (UnaryFn.fromBitsLE_min hs hc).of_eq fun z => min_eq_left (h z)

end Complexity
