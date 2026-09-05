/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.BinToUnary
public import Complexitylib.Classes.Containments.Internal.IPLeaf

/-!
# The canonical bits of a number

`DataEncode` writes a natural number as `Nat.bits`, its little-endian bits with
no trailing zero. A fixed-width counter, which is what a polynomial-time machine
can produce, carries trailing zeros; dropping them is the missing step between
the two.

Dropping trailing zeros is a right fold — what to do with a bit depends on
whether everything after it vanished — so `recFoldClamp` expresses it directly,
with no reversal.

## Main definitions

- `Complexity.stripTrailing` — drop trailing zeros

## Main results

- `Complexity.stripTrailing_eq_bits` — the result is `Nat.bits` of the value
- `Complexity.stripTrailing_mem_FP` — it is polynomial time
-/

@[expose] public section

namespace Complexity

/-- Drop trailing zeros from a little-endian bit string. -/
def stripTrailing : List Bool → List Bool
  | [] => []
  | false :: t => if stripTrailing t = [] then [] else false :: stripTrailing t
  | true :: t => true :: stripTrailing t

@[simp] theorem stripTrailing_nil : stripTrailing [] = [] := rfl

theorem stripTrailing_false (t : List Bool) :
    stripTrailing (false :: t) =
      if stripTrailing t = [] then [] else false :: stripTrailing t := rfl

theorem stripTrailing_true (t : List Bool) :
    stripTrailing (true :: t) = true :: stripTrailing t := rfl

theorem length_stripTrailing (l : List Bool) : (stripTrailing l).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons b t ih =>
      cases b
      · rw [stripTrailing_false]
        split
        · simp
        · simp only [List.length_cons]
          omega
      · rw [stripTrailing_true]
        simp only [List.length_cons]
        omega

/-- **Dropping trailing zeros gives the canonical bits.** -/
theorem stripTrailing_eq_bits (l : List Bool) : stripTrailing l = (binValLE l).bits := by
  induction l with
  | nil => rfl
  | cons b t ih =>
      cases b
      · rw [stripTrailing_false, ih, binValLE_cons_false]
        by_cases h : (binValLE t).bits = []
        · rw [ite_eq_left h]
          have h0 : binValLE t = 0 := by
            have hb := binValLE_bits (binValLE t)
            rw [h] at hb
            exact hb.symm
          rw [h0]
          simp
        · rw [ite_eq_right h]
          have hne : binValLE t ≠ 0 := by
            intro h0
            rw [h0, Nat.zero_bits] at h
            exact h rfl
          rw [Nat.bit0_bits _ hne]
      · rw [stripTrailing_true, ih, binValLE_cons_true, Nat.bit1_bits]

/-! ### Polynomial time -/

/-- The fold step on a zero. -/
def stripZero (z : List Bool) : List Bool :=
  Cobham.selectHead (emptyFlag (pairSnd (pairFst z))) []
    (false :: pairSnd (pairFst z))

/-- The fold step on a one. -/
def stripOne (z : List Bool) : List Bool :=
  true :: pairSnd (pairFst z)

theorem stripZero_mem_FP : stripZero ∈ FP := by
  have h : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP h) (constFn_mem_FP [])
    (mem_FP_comp h (Cobham.cons_mem_FP false))

theorem stripOne_mem_FP : stripOne ∈ FP := by
  have h : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  exact mem_FP_comp h (Cobham.cons_mem_FP true)

/-- The fold computes `stripTrailing`, as long as the clamp allows the answer. -/
theorem recFoldClamp_stripTrailing (bound : ℕ) (W : List Bool) :
    ∀ l : List Bool, l.length ≤ bound →
      Cobham.recFoldClamp stripZero stripOne bound [] W l = stripTrailing l := by
  intro l
  induction l with
  | nil =>
      intro _
      rw [Cobham.recFoldClamp]
      simp
  | cons b t ih =>
      intro hb
      have hb' : t.length ≤ bound := by
        simp only [List.length_cons] at hb
        omega
      rw [Cobham.recFoldClamp, ih hb']
      have hstate : pairSnd (pairFst
          (pair (pair W (stripTrailing t)) t)) = stripTrailing t := by
        rw [pairFst_pair, pairSnd_pair]
      have hlt : (stripTrailing t).length ≤ t.length := length_stripTrailing t
      cases b
      · show (stripZero _).take bound = _
        rw [stripZero, hstate, stripTrailing_false]
        cases hs : stripTrailing t with
        | nil =>
            rw [emptyFlag_nil, selectHead_cons_true, ite_eq_left rfl]
            simp
        | cons c s =>
            rw [emptyFlag_cons, selectHead_cons_false, ite_eq_right (by simp)]
            refine List.take_of_length_le ?_
            simp only [List.length_cons]
            rw [hs] at hlt
            simp only [List.length_cons] at hlt
            simp only [List.length_cons] at hb
            omega
      · show (stripOne _).take bound = _
        rw [stripOne, hstate, stripTrailing_true]
        refine List.take_of_length_le ?_
        simp only [List.length_cons] at hb ⊢
        omega

/-- Dropping trailing zeros, on `pair anything bits`. -/
def stripFn (z : List Bool) : List Bool :=
  Cobham.recFoldClamp stripZero stripOne z.length [] (pairFst z)
    (pairSnd z)

theorem stripFn_mem_FP : stripFn ∈ FP := by
  have := Cobham.recFoldClamp_mem_FP stripZero_mem_FP stripOne_mem_FP
    (constFn_mem_FP []) (Polynomial.X)
  refine mem_FP_of_eq this fun z => ?_
  rw [stripFn]
  simp

theorem stripFn_eq (z : List Bool) :
    stripFn z = stripTrailing (pairSnd z) := by
  refine recFoldClamp_stripTrailing _ _ _ ?_
  exact sndBlock_length_le z

end Complexity
