/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.BinArith

/-!
# Counting out the value of a bit string

A verifier turns its coins into an index — into a list of edges, say — and an
index has to be counted out in unary before a polynomial-time loop can use it.
This module does that: it reads a bit string as a little-endian binary number
and writes that many marks.

The conversion is only polynomial time when the value is, which is why the
result is clamped: the fold's state is truncated to a width the caller supplies.
On strings short enough for the clamp — logarithmically many coins, say — the
answer is exact.

## Main definitions

- `Complexity.unaryVal` — the value of a bit string, in unary

## Main results

- `Complexity.unaryVal_eq` — it is exact when the clamp is wide enough
- `Complexity.unaryVal_mem_FP` — it is polynomial time
-/

@[expose] public section

namespace Complexity

/-- Reading a zero: the value doubles. -/
def binDbl (z : List Bool) : List Bool :=
  pairSnd (pairFst z) ++ pairSnd (pairFst z)

/-- Reading a one: the value doubles and gains one. -/
def binDblOne (z : List Bool) : List Bool :=
  pairSnd (pairFst z) ++ pairSnd (pairFst z) ++ [true]

theorem binDbl_mem_FP : binDbl ∈ FP := by
  have h : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  exact Cobham.appendFn_mem_FP h h

theorem binDblOne_mem_FP : binDblOne ∈ FP := by
  have h : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  exact Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP h h) (constFn_mem_FP [true])

/-- **The value of a bit string, in unary**, computed on `pair anything bits`. -/
def unaryVal (p : Polynomial ℕ) (z : List Bool) : List Bool :=
  Cobham.recFoldClamp binDbl binDblOne (p.eval z.length) [] (pairFst z)
    (pairSnd z)

theorem unaryVal_mem_FP (p : Polynomial ℕ) : unaryVal p ∈ FP :=
  Cobham.recFoldClamp_mem_FP binDbl_mem_FP binDblOne_mem_FP (constFn_mem_FP []) p

theorem binValLE_cons_false (l : List Bool) : binValLE (false :: l) = 2 * binValLE l := by
  rw [binValLE]; simp

theorem binValLE_cons_true (l : List Bool) :
    binValLE (true :: l) = 2 * binValLE l + 1 := by
  rw [binValLE]; simp; omega

/-- The fold really counts out the value, as long as the clamp is wide enough. -/
theorem recFoldClamp_binValLE (bound : ℕ) (W : List Bool) :
    ∀ l : List Bool, 2 ^ l.length ≤ bound →
      Cobham.recFoldClamp binDbl binDblOne bound [] W l
        = List.replicate (binValLE l) true := by
  intro l
  induction l with
  | nil =>
      intro _
      rw [Cobham.recFoldClamp]
      simp [binValLE]
  | cons b l ih =>
      intro hb
      have hb' : 2 ^ l.length ≤ bound := by
        have : 2 ^ l.length ≤ 2 ^ (b :: l).length :=
          Nat.pow_le_pow_right (by omega) (by simp)
        omega
      have hval : binValLE l < 2 ^ l.length := binValLE_lt l
      have hlen : 2 ^ (l.length + 1) ≤ bound := by
        have : (b :: l).length = l.length + 1 := by simp
        omega
      rw [Cobham.recFoldClamp, ih hb']
      have hstate : pairSnd (pairFst
          (pair (pair W (List.replicate (binValLE l) true)) l))
          = List.replicate (binValLE l) true := by
        rw [pairFst_pair, pairSnd_pair]
      cases b with
      | false =>
          show (binDbl _).take bound = _
          rw [binDbl, hstate, binValLE_cons_false, two_mul, ← List.replicate_add]
          refine List.take_of_length_le ?_
          rw [List.length_replicate]
          omega
      | true =>
          show (binDblOne _).take bound = _
          rw [binDblOne, hstate, binValLE_cons_true, two_mul,
            show List.replicate (binValLE l) true ++ List.replicate (binValLE l) true ++ [true]
              = List.replicate (binValLE l + binValLE l + 1) true from by
              rw [List.replicate_add, List.replicate_add]
              rfl]
          refine List.take_of_length_le ?_
          rw [List.length_replicate]
          omega

/-- **The conversion is exact** when the clamp is wide enough for the value. -/
theorem unaryVal_eq {p : Polynomial ℕ} {z : List Bool}
    (h : 2 ^ (pairSnd z).length ≤ p.eval z.length) :
    unaryVal p z = List.replicate (binValLE (pairSnd z)) true :=
  recFoldClamp_binValLE _ _ _ h

end Complexity
