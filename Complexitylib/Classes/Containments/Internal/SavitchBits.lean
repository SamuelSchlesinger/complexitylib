/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.FPBridge
public import Complexitylib.Classes.Containments.Internal.WitnessEnum

/-!
# A fixed-width binary counter inside the polynomial-time algebra

⚠️ Unreviewed by Bolton

Savitch's recursion searches for a midpoint by enumerating every bitstring of the
width a configuration code occupies. The enumeration is an ordinary little-endian
increment that wraps around, and the wrap is what tells the search it has run out
of candidates.

`Complexity.addBit` is that increment as a plain recursion — carry in, carry out,
result — and `Complexity.bumpStep` is the same thing as a left-to-right scan on a
packed state, the shape `Cobham.iterate_mem_FP` iterates. The two agree
(`Complexity.bumpStep_iterate_run`), so the arithmetic can be done on the
recursion and the polynomial-time bound on the scan.

## Main definitions

- `Complexity.addBit` — increment a little-endian bitstring, with carry
- `Complexity.bumpBits`, `Complexity.bumpOver` — its two components
- `Complexity.bumpStep` — one step of the scan that computes it
- `Complexity.bumpFlag`, `Complexity.bumpCode` — the packed verdicts

## Main results

- `Complexity.addBit_binValLE` — the adder is correct
- `Complexity.bumpBits_length` — the width is preserved
- `Complexity.bumpOver_iff` — the carry fires exactly on the last candidate
- `Complexity.bumpCodeFn_mem_FP`, `Complexity.bumpFlagFn_mem_FP` — both are in `FP`
-/

@[expose] public section

namespace Complexity

open Cobham

/-! ## The increment as a recursion -/

/-- Add a carry bit into a little-endian bitstring: the carry out and the result. -/
def addBit : Bool → List Bool → Bool × List Bool
  | c, [] => (c, [])
  | c, b :: t => ((addBit (c && b) t).1, (xor c b) :: (addBit (c && b) t).2)

@[simp] theorem addBit_nil (c : Bool) : addBit c [] = (c, []) := rfl

@[simp] theorem addBit_cons (c b : Bool) (t : List Bool) :
    addBit c (b :: t) = ((addBit (c && b) t).1, (xor c b) :: (addBit (c && b) t).2) := rfl

/-- The increment of a little-endian bitstring, wrapping on overflow. -/
def bumpBits (w : List Bool) : List Bool := (addBit true w).2

/-- Did the increment wrap around? -/
def bumpOver (w : List Bool) : Bool := (addBit true w).1

/-- Adding no carry changes nothing. -/
@[simp] theorem addBit_false (w : List Bool) : addBit false w = (false, w) := by
  induction w with
  | nil => rfl
  | cons b t ih => simp [addBit, ih]

/-- The width is preserved. -/
@[simp] theorem addBit_length (c : Bool) (w : List Bool) :
    (addBit c w).2.length = w.length := by
  induction w generalizing c with
  | nil => rfl
  | cons b t ih => simp [addBit, ih]

@[simp] theorem bumpBits_length (w : List Bool) : (bumpBits w).length = w.length :=
  addBit_length true w

/-- **The adder is correct.** -/
theorem addBit_binValLE (c : Bool) (w : List Bool) :
    binValLE (addBit c w).2 + (if (addBit c w).1 then 2 ^ w.length else 0)
      = binValLE w + (if c then 1 else 0) := by
  induction w generalizing c with
  | nil => cases c <;> simp [binValLE]
  | cons b t ih =>
      have h := ih (c && b)
      rcases hab : addBit (c && b) t with ⟨d, s⟩
      rw [hab] at h
      simp only [addBit_cons, hab, binValLE, List.length_cons, pow_succ]
      clear hab ih
      cases c <;> cases b <;> cases d <;> simp at h ⊢ <;> omega

/-- **The carry fires exactly on the last candidate.** -/
theorem bumpOver_iff (w : List Bool) :
    bumpOver w = true ↔ binValLE w = 2 ^ w.length - 1 := by
  have h := addBit_binValLE true w
  have hlt := binValLE_lt (addBit true w).2
  have hlt' := binValLE_lt w
  rw [addBit_length] at hlt
  rw [bumpOver]
  constructor
  · intro hc
    rw [hc] at h
    simp at h
    omega
  · intro hv
    by_contra hc
    simp only [Bool.not_eq_true] at hc
    rw [hc] at h
    simp at h
    omega

/-- **The increment counts.** -/
theorem binValLE_bumpBits_of_not_over (w : List Bool) (h : bumpOver w = false) :
    binValLE (bumpBits w) = binValLE w + 1 := by
  have hb := addBit_binValLE true w
  rw [bumpOver] at h
  rw [h] at hb
  simp at hb
  rw [bumpBits]
  omega

/-- Iterating the increment from zero enumerates the candidates in order. -/
theorem bumpBits_iterate (ℓ : ℕ) :
    ∀ j, j < 2 ^ ℓ → bumpBits^[j] (bitsOfLenLE ℓ 0) = bitsOfLenLE ℓ j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hj' : j < 2 ^ ℓ := by omega
      rw [Function.iterate_succ_apply', ih hj']
      have hlen : (bitsOfLenLE ℓ j).length = ℓ := bitsOfLenLE_length ℓ j
      have hval : binValLE (bitsOfLenLE ℓ j) = j := binValLE_bitsOfLenLE ℓ j hj'
      have hover : bumpOver (bitsOfLenLE ℓ j) = false := by
        by_contra hc
        simp only [Bool.not_eq_false] at hc
        rw [bumpOver_iff, hlen, hval] at hc
        omega
      have := binValLE_bumpBits_of_not_over _ hover
      rw [hval] at this
      rw [← bitsOfLenLE_binValLE (bumpBits (bitsOfLenLE ℓ j)), this, bumpBits_length, hlen]

/-! ## The increment as a scan

The same increment, written as a left-to-right pass over the string: carry, the
bits already emitted, and the bits still to read. This is the shape
`Cobham.iterate_mem_FP` iterates, and every operation in it is one of the
algebra's. -/

/-- One step of the increment scan. -/
def bumpStep : List Bool × List Bool × List Bool → List Bool × List Bool × List Bool
  | (c, acc, []) => (c, acc, [])
  | (c, acc, b :: t) => (andBit c [b], acc ++ selectHead c (notBit [b]) [b], t)

@[simp] theorem bumpStep_nil (c acc : List Bool) : bumpStep (c, acc, []) = (c, acc, []) := rfl

theorem bumpStep_flag (c b : Bool) (acc t : List Bool) :
    bumpStep ([c], acc, b :: t) = ([c && b], acc ++ [xor c b], t) := by
  rw [bumpStep]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · show andBit [c] [b] = [c && b]
    cases c <;> cases b <;> rfl
  · show acc ++ selectHead [c] (notBit [b]) [b] = acc ++ [xor c b]
    cases c <;> cases b <;> rfl

/-- **The scan computes the increment.** -/
theorem bumpStep_iterate_run (c : Bool) (acc w : List Bool) :
    bumpStep^[w.length] ([c], acc, w) = ([(addBit c w).1], acc ++ (addBit c w).2, []) := by
  induction w generalizing c acc with
  | nil => simp
  | cons b t ih =>
      rw [List.length_cons, Function.iterate_succ_apply, bumpStep_flag, ih,
        addBit_cons]
      simp

/-- The scan never has more in hand than it started with. -/
theorem bumpStep_iterate_length (c : Bool) (acc w : List Bool) (n : ℕ) :
    (bumpStep^[n] ([c], acc, w)).1.length = 1 ∧
      (bumpStep^[n] ([c], acc, w)).2.1.length + (bumpStep^[n] ([c], acc, w)).2.2.length
        ≤ acc.length + w.length := by
  induction n generalizing c acc w with
  | zero => exact ⟨rfl, le_rfl⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      cases w with
      | nil =>
          have := ih c acc []
          simpa using this
      | cons b t =>
          rw [bumpStep_flag]
          have := ih (c && b) (acc ++ [xor c b]) t
          refine ⟨this.1, le_trans this.2 ?_⟩
          simp
          omega

/-! ## The packed scan -/

/-- The packed scan state. -/
def bumpPack (c acc rest : List Bool) : List Bool := pair c (pair acc rest)

@[simp] theorem bumpPack_length (c acc rest : List Bool) :
    (bumpPack c acc rest).length = 2 * c.length + 2 * acc.length + rest.length + 4 := by
  rw [bumpPack, pair_length, pair_length]
  omega

/-- One step of the packed scan. -/
def bumpStepP (z : List Bool) : List Bool :=
  selectHead (lenLeFlag (pairSnd (pairSnd z)) [false])
    (pair (andBit (pairFst z) ((pairSnd (pairSnd z)).take 1))
      (pair (pairFst (pairSnd z) ++
          selectHead (pairFst z) (notBit ((pairSnd (pairSnd z)).take 1))
            ((pairSnd (pairSnd z)).take 1))
        ((pairSnd (pairSnd z)).drop 1)))
    z

/-- **The packed step is the unpacked step.** -/
theorem bumpStepP_pack (c acc rest : List Bool) :
    bumpStepP (bumpPack c acc rest)
      = bumpPack (bumpStep (c, acc, rest)).1 (bumpStep (c, acc, rest)).2.1
          (bumpStep (c, acc, rest)).2.2 := by
  rw [bumpStepP, bumpPack]
  simp only [pairFst_pair, pairSnd_pair]
  cases rest with
  | nil =>
      rw [selectHead]
      have hflag : lenLeFlag ([] : List Bool) [false] = [false] := rfl
      rw [hflag]
      simp [bumpPack]
  | cons b t =>
      have hflag : lenLeFlag (b :: t) [false] = [true] :=
        (lenLeFlag_eq_true_iff (b :: t) [false]).mpr (by simp)
      rw [selectHead, hflag]
      simp only [List.head?_cons, reduceIte]
      rw [bumpStep, bumpPack]
      simp

/-- **The packed iteration is the unpacked one.** -/
theorem bumpStepP_iterate (s : List Bool × List Bool × List Bool) (n : ℕ) :
    bumpStepP^[n] (bumpPack s.1 s.2.1 s.2.2)
      = bumpPack (bumpStep^[n] s).1 (bumpStep^[n] s).2.1 (bumpStep^[n] s).2.2 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, bumpStepP_pack, ih (bumpStep s),
        Function.iterate_succ_apply]

/-- The packed iteration, with the state's three components spelled out. -/
theorem bumpStepP_iterate_args (c acc rest : List Bool) (n : ℕ) :
    bumpStepP^[n] (bumpPack c acc rest)
      = bumpPack (bumpStep^[n] (c, acc, rest)).1 (bumpStep^[n] (c, acc, rest)).2.1
          (bumpStep^[n] (c, acc, rest)).2.2 :=
  bumpStepP_iterate (c, acc, rest) n

/-! ## The verdicts -/

/-- The packed scan run to completion. -/
def bumpRun (w : List Bool) : List Bool := bumpStepP^[w.length] (bumpPack [true] [] w)

/-- The increment of `w`, computed by the scan. -/
def bumpCode (w : List Bool) : List Bool := pairFst (pairSnd (bumpRun w))

/-- The carry out of the increment, as a flag. -/
def bumpFlag (w : List Bool) : List Bool := pairFst (bumpRun w)

theorem bumpRun_eq (w : List Bool) :
    bumpRun w = bumpPack [bumpOver w] (bumpBits w) [] := by
  rw [bumpRun, bumpStepP_iterate_args, bumpStep_iterate_run, bumpOver, bumpBits]
  simp

@[simp] theorem bumpCode_eq (w : List Bool) : bumpCode w = bumpBits w := by
  rw [bumpCode, bumpRun_eq, bumpPack]
  simp

@[simp] theorem bumpFlag_eq (w : List Bool) : bumpFlag w = [bumpOver w] := by
  rw [bumpFlag, bumpRun_eq, bumpPack]
  simp

/-! ## Both are polynomial-time -/

theorem bumpStepP_mem_FP : bumpStepP ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hfst : ∀ {a : List Bool → List Bool}, a ∈ FP →
      (fun z => pairFst (a z)) ∈ FP := by
    intro a ha
    have := mem_FP_comp ha Cobham.fstBlock_mem_FP
    exact this
  have hsnd : ∀ {a : List Bool → List Bool}, a ∈ FP →
      (fun z => pairSnd (a z)) ∈ FP := by
    intro a ha
    have := mem_FP_comp ha Cobham.sndBlock_mem_FP
    exact this
  have hc := hfst hid
  have hw := hsnd hid
  have hrest := hsnd hw
  have hacc := hfst hw
  have hone : (fun _ : List Bool => ([false] : List Bool)) ∈ FP := constFn_mem_FP [false]
  have htake : (fun z => (pairSnd (pairSnd z)).take 1) ∈ FP := by
    have := Cobham.takeLenFn_mem_FP hone hrest
    simpa using this
  have hdrop : (fun z => (pairSnd (pairSnd z)).drop 1) ∈ FP := by
    have := dropLenFn_mem_FP hone hrest
    simpa using this
  have hbit : (fun z => selectHead (pairFst z)
      (notBit ((pairSnd (pairSnd z)).take 1)) ((pairSnd (pairSnd z)).take 1)) ∈ FP :=
    Cobham.selectHeadFn_mem_FP hc (notBitFn_mem_FP htake) htake
  exact Cobham.selectHeadFn_mem_FP (lenLeFlagFn_mem_FP hrest hone)
    (Cobham.pairFn_mem_FP (andBitFn_mem_FP hc htake)
      (Cobham.pairFn_mem_FP (Cobham.appendFn_mem_FP hacc hbit) hdrop)) hid

/-- **The increment is polynomial-time.** -/
theorem bumpRunFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => bumpRun (a z)) ∈ FP := by
  have hinit : (fun z => bumpPack [true] [] (a z)) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP [true])
      (Cobham.pairFn_mem_FP (constFn_mem_FP []) ha)
  have hwidth : (fun z => pair [true] (pair (a z) (a z))) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP [true]) (Cobham.pairFn_mem_FP ha ha)
  have hbound : ∀ z, ∀ n ≤ (a z).length,
      (bumpStepP^[n] (bumpPack [true] [] (a z))).length
        ≤ (pair [true] (pair (a z) (a z))).length := by
    intro z n _
    rw [bumpStepP_iterate_args]
    obtain ⟨h1, h2⟩ := bumpStep_iterate_length true [] (a z) n
    have hone : ([true] : List Bool).length = 1 := rfl
    rw [bumpPack_length, pair_length, pair_length]
    simp only [List.length_nil] at h2
    omega
  exact Cobham.iterate_mem_FP bumpStepP_mem_FP hinit ha hwidth hbound

theorem bumpCodeFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => bumpCode (a z)) ∈ FP := by
  have h1 := mem_FP_comp (bumpRunFn_mem_FP ha) Cobham.sndBlock_mem_FP
  have h2 := mem_FP_comp h1 Cobham.fstBlock_mem_FP
  simp [bumpCode]
  exact h2
theorem bumpFlagFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => bumpFlag (a z)) ∈ FP := by
  have h := mem_FP_comp (bumpRunFn_mem_FP ha) Cobham.fstBlock_mem_FP
  simp [bumpFlag]
  exact h

end Complexity
