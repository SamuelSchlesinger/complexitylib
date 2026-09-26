/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Encoding.Pairing
public import Complexitylib.Mathlib.NatBits
import Complexitylib.Classes.Containments.Internal.FPBridge
import Complexitylib.Classes.P.Iterate
import Complexitylib.Classes.P.Unary

/-!
# Binary codes of numbers in polynomial time — proof internals

The helper facts behind `Complexitylib.Classes.P.NatCodes`.

A bit of a number is a quotient by a power of two, and the power can be capped:
dividing `n` by anything above `n` gives `0`, just as dividing by a larger power
of two does. That keeps the power a polynomial-time number.

Reading a binary numeral back is a fold over its bits, from the most significant
(last) bit to the least significant (first) one, that doubles the value and adds
the bit. Capping every intermediate value at `c` keeps the fold's states
polynomially short and changes nothing below the cap, since doubling and adding
preserve "at least `c`".

## Contents

- `div_min_two_pow` — a quotient by a power of two, with the power capped
- `bit_fpPred` — bit `i` of a polynomial-time number, as a test on
  `pair z (1^i)`
- `fromBitsLE_min_internal` — the capped value of a binary numeral is a
  polynomial-time number
-/

@[expose] public section

namespace Complexity

variable {n c : List Bool → ℕ} {s : List Bool → List Bool}

/-- Capping the power of two at `n + 1` does not change the quotient of `n`. -/
theorem div_min_two_pow (n i : ℕ) : n / min (2 ^ i) (n + 1) = n / 2 ^ i := by
  rcases le_total (2 ^ i) (n + 1) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, Nat.div_eq_of_lt (Nat.lt_succ_self n),
      Nat.div_eq_of_lt (by omega)]

/-- **Bit `i` of a polynomial-time number is a polynomial-time test** of
`pair z (1^i)`. -/
theorem bit_fpPred (hn : UnaryFn n) :
    FPPred fun v => n (pairFst v) / 2 ^ (pairSnd v).length % 2 = 1 :=
  (FPPred.eq ((hn.lift.div ((UnaryFn.const 2).powMin UnaryFn.index
      (hn.lift.add (UnaryFn.const 1)))).mod (UnaryFn.const 2)) (UnaryFn.const 1)).of_iff
    fun v => by rw [div_min_two_pow]

/-- **The capped value of a binary numeral is a polynomial-time number.** The
fold over the bits of `s z` that doubles the value, adds the bit and caps the
result at `c z` computes `min (Nat.fromBitsLE (s z)) (c z)`. -/
theorem fromBitsLE_min_internal (hs : s ∈ FP) (hc : UnaryFn c) :
    UnaryFn fun z => min (Nat.fromBitsLE (s z)) (c z) := by
  -- The fold's step reads the cap and the value so far off `pair (pair (1^c) (1^x)) t`.
  have hacc : UnaryFn fun v => (pairSnd (pairFst v)).length :=
    UnaryFn.length (mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP)
  have hcap : UnaryFn fun v => (pairFst (pairFst v)).length :=
    UnaryFn.length (mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP)
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP hc
  refine recFold_mem_FP_of_bound
    (g := fun z t => List.replicate (min (Nat.fromBitsLE t) (c z)) true)
    (((UnaryFn.const 2).mul hacc).min hcap)
    ((((UnaryFn.const 2).mul hacc).add (UnaryFn.const 1)).min hcap)
    (constFn_mem_FP []) hc hs (fun _ => rfl) (fun z t => ?_) (fun z t => ?_)
    (PolyBound.eval p) fun z t _ => ?_
  · simp only [pairFst_pair, pairSnd_pair, List.length_replicate, Nat.fromBitsLE_cons,
      Bool.false_eq_true, ↓reduceIte, zero_add]
    congr 1
    omega
  · simp only [pairFst_pair, pairSnd_pair, List.length_replicate, Nat.fromBitsLE_cons,
      ↓reduceIte]
    congr 1
    omega
  · have hcz := hp z
    simp only [List.length_replicate] at hcz ⊢
    omega

end Complexity
