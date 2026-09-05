/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.SavitchBits

/-!
# Binary addition and comparison inside the polynomial-time algebra

⚠️ Unreviewed by Bolton

`Complexitylib.Classes.Containments.Internal.SavitchBits` builds a fixed-width *counter* in the
algebra — increment and overflow. A search that accumulates counts needs more: to add two numbers
and to compare them. Both are the same shape of computation, a single left-to-right scan over the
two operands, and both are written twice here for the same reason the counter was: as a plain
recursion, where the arithmetic is proved, and as a scan on a packed state, which is the shape
`Cobham.iterate_mem_FP` iterates.

Numbers are little-endian, least significant bit first, and the two operands are the same width.
Addition returns the carry out separately, so nothing is lost to wraparound.

## Main definitions

- `Complexity.addBitsLE` — addition with carry, as a recursion
- `Complexity.addBits`, `Complexity.addCarry` — its two components
- `Complexity.ltBitsLE`, `Complexity.ltFlag` — comparison
- `Complexity.strsOfLen`, `Complexity.strsLe` — the strings of a given length, and up to it
- `Complexity.nextStr`, `Complexity.strIdx` — one counter enumerating every short string

## Main results

- `Complexity.addBitsLE_binValLE` — the adder is correct
- `Complexity.ltFlag_eq_true_iff` — the comparator is correct
- `Complexity.addBitsFn_mem_FP`, `Complexity.ltFlagFn_mem_FP` — both are in `FP`
- `Complexity.strsLe_eq_image` — the enumeration hits every short string exactly once
-/

@[expose] public section

namespace Complexity

open Cobham

/-! ## The bit operations -/

/-- The carry out of a full adder. -/
def majB (c b d : Bool) : Bool := (c && b) || ((c && d) || (b && d))

/-- The sum bit of a full adder. -/
def sumB (c b d : Bool) : Bool := xor (xor c b) d

theorem majB_sumB (c b d : Bool) :
    (sumB c b d).toNat + 2 * (majB c b d).toNat = c.toNat + b.toNat + d.toNat := by
  cases c <;> cases b <;> cases d <;> rfl

theorem binValLE_cons (b : Bool) (w : List Bool) :
    binValLE (b :: w) = b.toNat + 2 * binValLE w := by
  cases b <;> simp [binValLE]

/-- Exclusive or of two flags. -/
def xorBit (x y : List Bool) : List Bool := selectHead x (notBit y) y

/-- The carry out, on flags. -/
def majBit (x y z : List Bool) : List Bool :=
  orBit (andBit x y) (orBit (andBit x z) (andBit y z))

/-- The sum bit, on flags. -/
def sumBit (x y z : List Bool) : List Bool := xorBit (xorBit x y) z

@[simp] theorem xorBit_flag (c d : Bool) : xorBit [c] [d] = [xor c d] := by
  cases c <;> cases d <;> rfl

@[simp] theorem majBit_flag (c b d : Bool) : majBit [c] [b] [d] = [majB c b d] := by
  cases c <;> cases b <;> cases d <;> rfl

@[simp] theorem sumBit_flag (c b d : Bool) : sumBit [c] [b] [d] = [sumB c b d] := by
  cases c <;> cases b <;> cases d <;> rfl

/-- The leading bit of a string, as a flag, reading past the end as zero. -/
def bit1 (v : List Bool) : List Bool := (v ++ [false]).take 1

@[simp] theorem bit1_nil : bit1 [] = [false] := rfl

@[simp] theorem bit1_cons (d : Bool) (t : List Bool) : bit1 (d :: t) = [d] := rfl

theorem bit1_eq (v : List Bool) : bit1 v = [v.headD false] := by
  cases v <;> rfl

/-! ## Addition as a recursion -/

/-- Add two little-endian bitstrings with a carry in: the carry out and the sum bits. The
second operand is read through `headD`/`drop`, so the two are stepped in lockstep. -/
def addBitsLE : Bool → List Bool → List Bool → Bool × List Bool
  | c, [], _ => (c, [])
  | c, b :: tu, v =>
      ((addBitsLE (majB c b (v.headD false)) tu (v.drop 1)).1,
        sumB c b (v.headD false) :: (addBitsLE (majB c b (v.headD false)) tu (v.drop 1)).2)

@[simp] theorem addBitsLE_nil (c : Bool) (v : List Bool) : addBitsLE c [] v = (c, []) := rfl

theorem addBitsLE_cons (c b : Bool) (tu tv : List Bool) :
    addBitsLE c (b :: tu) (d :: tv)
      = ((addBitsLE (majB c b d) tu tv).1, sumB c b d :: (addBitsLE (majB c b d) tu tv).2) := rfl

@[simp] theorem addBitsLE_length (c : Bool) (u v : List Bool) :
    (addBitsLE c u v).2.length = u.length := by
  induction u generalizing c v with
  | nil => rfl
  | cons b tu ih => simp [addBitsLE, ih]

/-- **The adder is correct.** -/
theorem addBitsLE_binValLE (c : Bool) (u v : List Bool) (h : v.length = u.length) :
    binValLE (addBitsLE c u v).2 + (addBitsLE c u v).1.toNat * 2 ^ u.length
      = binValLE u + binValLE v + c.toNat := by
  induction u generalizing c v with
  | nil =>
      have hv : v = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst hv
      simp [binValLE]
  | cons b tu ih =>
      obtain ⟨d, tv, rfl⟩ : ∃ d tv, v = d :: tv := by
        cases v with
        | nil => simp at h
        | cons d tv => exact ⟨d, tv, rfl⟩
      have htv : tv.length = tu.length := by simpa using h
      have hih := ih (majB c b d) tv htv
      have hmaj := majB_sumB c b d
      have hmul : (addBitsLE (majB c b d) tu tv).1.toNat * (2 ^ tu.length * 2)
          = 2 * ((addBitsLE (majB c b d) tu tv).1.toNat * 2 ^ tu.length) := by ring
      rw [addBitsLE_cons]
      simp only [binValLE_cons, List.length_cons, pow_succ]
      omega

/-! ## Addition as a scan -/

/-- One step of the addition scan: the carry, the bits emitted so far, and the two operands
still to read. -/
def addStep :
    List Bool × List Bool × List Bool × List Bool →
      List Bool × List Bool × List Bool × List Bool
  | (c, acc, [], v) => (c, acc, [], v)
  | (c, acc, b :: tu, v) =>
      (majBit c [b] (bit1 v), acc ++ sumBit c [b] (bit1 v), tu, v.drop 1)

@[simp] theorem addStep_nil (c acc v : List Bool) : addStep (c, acc, [], v) = (c, acc, [], v) :=
  rfl

theorem addStep_flag (c b : Bool) (acc tu v : List Bool) :
    addStep ([c], acc, b :: tu, v)
      = ([majB c b (v.headD false)], acc ++ [sumB c b (v.headD false)], tu, v.drop 1) := by
  rw [addStep, bit1_eq]
  simp

/-- **The scan computes the sum.** -/
theorem addStep_iterate_run (c : Bool) (acc u v : List Bool) (h : v.length = u.length) :
    addStep^[u.length] ([c], acc, u, v)
      = ([(addBitsLE c u v).1], acc ++ (addBitsLE c u v).2, [], []) := by
  induction u generalizing c acc v with
  | nil =>
      have hv : v = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst hv
      simp
  | cons b tu ih =>
      obtain ⟨d, tv, rfl⟩ : ∃ d tv, v = d :: tv := by
        cases v with
        | nil => simp at h
        | cons d tv => exact ⟨d, tv, rfl⟩
      have htv : tv.length = tu.length := by simpa using h
      rw [List.length_cons, Function.iterate_succ_apply, addStep_flag]
      simp only [List.headD_cons, List.drop_succ_cons, List.drop_zero]
      rw [ih (majB c b d) (acc ++ [sumB c b d]) tv htv, addBitsLE_cons]
      simp

/-- The scan never has more in hand than it started with. -/
theorem addStep_iterate_length (c : Bool) (acc u v : List Bool) (n : ℕ) :
    (addStep^[n] ([c], acc, u, v)).1.length = 1 ∧
      (addStep^[n] ([c], acc, u, v)).2.1.length
          + (addStep^[n] ([c], acc, u, v)).2.2.1.length ≤ acc.length + u.length ∧
      (addStep^[n] ([c], acc, u, v)).2.2.2.length ≤ v.length := by
  induction n generalizing c acc u v with
  | zero => exact ⟨rfl, le_rfl, le_rfl⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      cases u with
      | nil => simpa using ih c acc [] v
      | cons b tu =>
          rw [addStep_flag]
          have := ih (majB c b (v.headD false)) (acc ++ [sumB c b (v.headD false)]) tu (v.drop 1)
          refine ⟨this.1, le_trans this.2.1 ?_, le_trans this.2.2 ?_⟩
          · simp
            omega
          · simp

/-! ## The packed scan -/

/-- The packed scan state. -/
def addPack (c acc ru rv : List Bool) : List Bool := pair c (pair acc (pair ru rv))

@[simp] theorem addPack_length (c acc ru rv : List Bool) :
    (addPack c acc ru rv).length
      = 2 * c.length + 2 * acc.length + 2 * ru.length + rv.length + 6 := by
  rw [addPack, pair_length, pair_length, pair_length]
  omega

/-- One step of the packed scan. -/
def addStepP (z : List Bool) : List Bool :=
  selectHead (lenLeFlag (pairFst (pairSnd (pairSnd z))) [false])
    (addPack
      (majBit (pairFst z) (bit1 (pairFst (pairSnd (pairSnd z))))
        (bit1 (pairSnd (pairSnd (pairSnd z)))))
      (pairFst (pairSnd z) ++
        sumBit (pairFst z) (bit1 (pairFst (pairSnd (pairSnd z))))
          (bit1 (pairSnd (pairSnd (pairSnd z)))))
      ((pairFst (pairSnd (pairSnd z))).drop 1)
      ((pairSnd (pairSnd (pairSnd z))).drop 1))
    z

/-- **The packed step is the unpacked step.** -/
theorem addStepP_pack (c acc ru rv : List Bool) :
    addStepP (addPack c acc ru rv)
      = addPack (addStep (c, acc, ru, rv)).1 (addStep (c, acc, ru, rv)).2.1
          (addStep (c, acc, ru, rv)).2.2.1 (addStep (c, acc, ru, rv)).2.2.2 := by
  rw [addStepP, addPack]
  simp only [pairFst_pair, pairSnd_pair]
  cases ru with
  | nil =>
      have hflag : lenLeFlag ([] : List Bool) [false] = [false] := rfl
      rw [selectHead, hflag]
      simp [addPack]
  | cons b t =>
      have hflag : lenLeFlag (b :: t) [false] = [true] :=
        (lenLeFlag_eq_true_iff (b :: t) [false]).mpr (by simp)
      rw [selectHead, hflag]
      simp only [List.head?_cons, reduceIte]
      rw [addStep, addPack]
      simp [addPack]

/-- **The packed iteration is the unpacked one.** -/
theorem addStepP_iterate (s : List Bool × List Bool × List Bool × List Bool) (n : ℕ) :
    addStepP^[n] (addPack s.1 s.2.1 s.2.2.1 s.2.2.2)
      = addPack (addStep^[n] s).1 (addStep^[n] s).2.1 (addStep^[n] s).2.2.1
          (addStep^[n] s).2.2.2 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, addStepP_pack, ih (addStep s),
        Function.iterate_succ_apply]

theorem addStepP_iterate_args (c acc ru rv : List Bool) (n : ℕ) :
    addStepP^[n] (addPack c acc ru rv)
      = addPack (addStep^[n] (c, acc, ru, rv)).1 (addStep^[n] (c, acc, ru, rv)).2.1
          (addStep^[n] (c, acc, ru, rv)).2.2.1 (addStep^[n] (c, acc, ru, rv)).2.2.2 :=
  addStepP_iterate (c, acc, ru, rv) n

/-! ## The verdicts -/

/-- The packed addition run to completion. -/
def addRun (u v : List Bool) : List Bool := addStepP^[u.length] (addPack [false] [] u v)

/-- The sum bits of `u` and `v`. -/
def addBits (u v : List Bool) : List Bool := pairFst (pairSnd (addRun u v))

/-- The carry out of `u + v`. -/
def addCarry (u v : List Bool) : List Bool := pairFst (addRun u v)

theorem addRun_eq (u v : List Bool) (h : v.length = u.length) :
    addRun u v = addPack [(addBitsLE false u v).1] (addBitsLE false u v).2 [] [] := by
  rw [addRun, addStepP_iterate_args, addStep_iterate_run false [] u v h]
  simp

@[simp] theorem addBits_eq (u v : List Bool) (h : v.length = u.length) :
    addBits u v = (addBitsLE false u v).2 := by
  rw [addBits, addRun_eq u v h, addPack]
  simp

@[simp] theorem addCarry_eq (u v : List Bool) (h : v.length = u.length) :
    addCarry u v = [(addBitsLE false u v).1] := by
  rw [addCarry, addRun_eq u v h, addPack]
  simp

/-- **What the packed addition computes.** -/
theorem addBits_binValLE (u v : List Bool) (h : v.length = u.length)
    (hc : addCarry u v = [false]) : binValLE (addBits u v) = binValLE u + binValLE v := by
  have hk := addBitsLE_binValLE false u v h
  rw [addCarry_eq u v h] at hc
  have hc' : (addBitsLE false u v).1 = false := by
    have := congrArg (fun l => l.headD false) hc
    simpa using this
  rw [hc'] at hk
  simp at hk
  rw [addBits_eq u v h]
  exact hk

theorem addBits_length (u v : List Bool) (h : v.length = u.length) :
    (addBits u v).length = u.length := by
  rw [addBits_eq u v h, addBitsLE_length]

/-! ## Addition is polynomial-time -/

theorem addStepP_mem_FP : addStepP ∈ FP := by
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
  have hacc := hfst hw
  have hww := hsnd hw
  have hru := hfst hww
  have hrv := hsnd hww
  have hone : (fun _ : List Bool => ([false] : List Bool)) ∈ FP := constFn_mem_FP [false]
  have htakeU : (fun z => bit1 (pairFst (pairSnd (pairSnd z)))) ∈ FP := by
    have := Cobham.takeLenFn_mem_FP hone (Cobham.appendFn_mem_FP hru hone)
    simpa [bit1] using this
  have htakeV : (fun z => bit1 (pairSnd (pairSnd (pairSnd z)))) ∈ FP := by
    have := Cobham.takeLenFn_mem_FP hone (Cobham.appendFn_mem_FP hrv hone)
    simpa [bit1] using this
  have hdropU : (fun z => (pairFst (pairSnd (pairSnd z))).drop 1) ∈ FP := by
    have := dropLenFn_mem_FP hone hru
    simpa using this
  have hdropV : (fun z => (pairSnd (pairSnd (pairSnd z))).drop 1) ∈ FP := by
    have := dropLenFn_mem_FP hone hrv
    simpa using this
  have hxor : ∀ {a b : List Bool → List Bool}, a ∈ FP → b ∈ FP →
      (fun z => xorBit (a z) (b z)) ∈ FP := fun ha hb =>
    Cobham.selectHeadFn_mem_FP ha (notBitFn_mem_FP hb) hb
  have hmaj : (fun z => majBit (pairFst z) (bit1 (pairFst (pairSnd (pairSnd z))))
      (bit1 (pairSnd (pairSnd (pairSnd z))))) ∈ FP :=
    orBitFn_mem_FP (andBitFn_mem_FP hc htakeU)
      (orBitFn_mem_FP (andBitFn_mem_FP hc htakeV) (andBitFn_mem_FP htakeU htakeV))
  have hsum : (fun z => sumBit (pairFst z) (bit1 (pairFst (pairSnd (pairSnd z))))
      (bit1 (pairSnd (pairSnd (pairSnd z))))) ∈ FP :=
    hxor (hxor hc htakeU) htakeV
  exact Cobham.selectHeadFn_mem_FP (lenLeFlagFn_mem_FP hru hone)
    (Cobham.pairFn_mem_FP hmaj
      (Cobham.pairFn_mem_FP (Cobham.appendFn_mem_FP hacc hsum)
        (Cobham.pairFn_mem_FP hdropU hdropV))) hid

theorem addRunFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => addRun (a z) (b z)) ∈ FP := by
  have hinit : (fun z => addPack [false] [] (a z) (b z)) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP [false])
      (Cobham.pairFn_mem_FP (constFn_mem_FP []) (Cobham.pairFn_mem_FP ha hb))
  have hwidth : (fun z => addPack [false] (a z) (a z) (b z)) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP [false])
      (Cobham.pairFn_mem_FP ha (Cobham.pairFn_mem_FP ha hb))
  have hbound : ∀ z, ∀ n ≤ (a z).length,
      (addStepP^[n] (addPack [false] [] (a z) (b z))).length
        ≤ (addPack [false] (a z) (a z) (b z)).length := by
    intro z n _
    rw [addStepP_iterate_args]
    obtain ⟨h1, h2, h3⟩ := addStep_iterate_length false [] (a z) (b z) n
    have hone1 : ([false] : List Bool).length = 1 := rfl
    rw [addPack_length, addPack_length]
    simp only [List.length_nil] at h2
    omega
  exact Cobham.iterate_mem_FP addStepP_mem_FP hinit ha hwidth hbound

theorem addBitsFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => addBits (a z) (b z)) ∈ FP := by
  have h1 := mem_FP_comp (addRunFn_mem_FP ha hb) Cobham.sndBlock_mem_FP
  have h2 := mem_FP_comp h1 Cobham.fstBlock_mem_FP
  simp [addBits]
  exact h2
theorem addCarryFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => addCarry (a z) (b z)) ∈ FP := by
  have h := mem_FP_comp (addRunFn_mem_FP ha hb) Cobham.fstBlock_mem_FP
  simp [addCarry]
  exact h
/-! ## Comparison as a recursion -/

/-- Scan two little-endian bitstrings from the bottom, keeping the verdict of the highest
position at which they have differed so far. -/
def ltBitsLE : Bool → List Bool → List Bool → Bool
  | f, [], _ => f
  | f, b :: tu, v =>
      ltBitsLE (if b = v.headD false then f else v.headD false) tu (v.drop 1)

@[simp] theorem ltBitsLE_nil (f : Bool) (v : List Bool) : ltBitsLE f [] v = f := rfl

theorem ltBitsLE_cons (f b : Bool) (tu v : List Bool) :
    ltBitsLE f (b :: tu) v
      = ltBitsLE (if b = v.headD false then f else v.headD false) tu (v.drop 1) := rfl

/-- **The comparator is correct.** -/
theorem ltBitsLE_spec (f : Bool) (u v : List Bool) (h : v.length = u.length) :
    ltBitsLE f u v = if binValLE u < binValLE v then true
      else if binValLE v < binValLE u then false else f := by
  induction u generalizing f v with
  | nil =>
      have hv : v = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst hv
      simp [binValLE]
  | cons b tu ih =>
      obtain ⟨d, tv, rfl⟩ : ∃ d tv, v = d :: tv := by
        cases v with
        | nil => simp at h
        | cons d tv => exact ⟨d, tv, rfl⟩
      have htv : tv.length = tu.length := by simpa using h
      rw [ltBitsLE_cons]
      simp only [List.headD_cons, List.drop_succ_cons, List.drop_zero]
      rw [ih _ tv htv, binValLE_cons, binValLE_cons]
      have hb : b.toNat ≤ 1 := by cases b <;> simp
      have hd : d.toNat ≤ 1 := by cases d <;> simp
      rcases lt_trichotomy (binValLE tu) (binValLE tv) with hlt | heq | hgt
      · rw [ite_eq_left hlt, ite_eq_left (by omega)]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), heq]
        cases b <;> cases d <;> simp
      · rw [ite_eq_right (by omega), ite_eq_left hgt, ite_eq_right (by omega),
        ite_eq_left (by omega)]

/-! ## Comparison as a scan -/

/-- One step of the comparison scan. -/
def ltStep : List Bool × List Bool × List Bool → List Bool × List Bool × List Bool
  | (f, [], v) => (f, [], v)
  | (f, b :: tu, v) => (selectHead (eqFlag [b] (bit1 v)) f (bit1 v), tu, v.drop 1)

@[simp] theorem ltStep_nil (f v : List Bool) : ltStep (f, [], v) = (f, [], v) := rfl

theorem ltStep_flag (f b : Bool) (tu v : List Bool) :
    ltStep ([f], b :: tu, v)
      = ([if b = v.headD false then f else v.headD false], tu, v.drop 1) := by
  rw [ltStep, bit1_eq]
  by_cases hb : b = v.headD false
  · rw [ite_eq_left hb, hb]
    have : eqFlag [v.headD false] [v.headD false] = [true] :=
      (eqFlag_eq_true_iff _ _).mpr rfl
    rw [this]
    rfl
  · rw [ite_eq_right hb]
    have : eqFlag [b] [v.headD false] = [false] := by
      rcases eqFlag_flag [b] [v.headD false] with hh | hh
      · exact absurd (by simpa using (eqFlag_eq_true_iff [b] [v.headD false]).mp hh) hb
      · exact hh
    rw [this]
    rfl

/-- **The scan computes the comparison.** -/
theorem ltStep_iterate_run (f : Bool) (u v : List Bool) (h : v.length = u.length) :
    ltStep^[u.length] ([f], u, v) = ([ltBitsLE f u v], [], []) := by
  induction u generalizing f v with
  | nil =>
      have hv : v = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst hv
      simp
  | cons b tu ih =>
      obtain ⟨d, tv, rfl⟩ : ∃ d tv, v = d :: tv := by
        cases v with
        | nil => simp at h
        | cons d tv => exact ⟨d, tv, rfl⟩
      have htv : tv.length = tu.length := by simpa using h
      rw [List.length_cons, Function.iterate_succ_apply, ltStep_flag]
      simp only [List.headD_cons, List.drop_succ_cons, List.drop_zero]
      rw [ih _ tv htv, ltBitsLE_cons]
      rfl

theorem ltStep_iterate_length (f : Bool) (u v : List Bool) (n : ℕ) :
    (ltStep^[n] ([f], u, v)).1.length = 1 ∧
      (ltStep^[n] ([f], u, v)).2.1.length ≤ u.length ∧
      (ltStep^[n] ([f], u, v)).2.2.length ≤ v.length := by
  induction n generalizing f u v with
  | zero => exact ⟨rfl, le_rfl, le_rfl⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      cases u with
      | nil => simpa using ih f [] v
      | cons b tu =>
          rw [ltStep_flag]
          have := ih (if b = v.headD false then f else v.headD false) tu (v.drop 1)
          exact ⟨this.1, le_trans this.2.1 (by simp), le_trans this.2.2 (by simp)⟩

/-! ## The packed comparison -/

/-- The packed comparison state. -/
def ltPack (f ru rv : List Bool) : List Bool := pair f (pair ru rv)

@[simp] theorem ltPack_length (f ru rv : List Bool) :
    (ltPack f ru rv).length = 2 * f.length + 2 * ru.length + rv.length + 4 := by
  rw [ltPack, pair_length, pair_length]
  omega

/-- One step of the packed comparison. -/
def ltStepP (z : List Bool) : List Bool :=
  selectHead (lenLeFlag (pairFst (pairSnd z)) [false])
    (ltPack
      (selectHead (eqFlag (bit1 (pairFst (pairSnd z))) (bit1 (pairSnd (pairSnd z))))
        (pairFst z) (bit1 (pairSnd (pairSnd z))))
      ((pairFst (pairSnd z)).drop 1)
      ((pairSnd (pairSnd z)).drop 1))
    z

theorem ltStepP_pack (f ru rv : List Bool) :
    ltStepP (ltPack f ru rv)
      = ltPack (ltStep (f, ru, rv)).1 (ltStep (f, ru, rv)).2.1 (ltStep (f, ru, rv)).2.2 := by
  rw [ltStepP, ltPack]
  simp only [pairFst_pair, pairSnd_pair]
  cases ru with
  | nil =>
      have hflag : lenLeFlag ([] : List Bool) [false] = [false] := rfl
      rw [selectHead, hflag]
      simp [ltPack]
  | cons b t =>
      have hflag : lenLeFlag (b :: t) [false] = [true] :=
        (lenLeFlag_eq_true_iff (b :: t) [false]).mpr (by simp)
      rw [selectHead, hflag]
      simp only [List.head?_cons, reduceIte]
      rw [ltStep, ltPack]
      simp [ltPack]

theorem ltStepP_iterate (s : List Bool × List Bool × List Bool) (n : ℕ) :
    ltStepP^[n] (ltPack s.1 s.2.1 s.2.2)
      = ltPack (ltStep^[n] s).1 (ltStep^[n] s).2.1 (ltStep^[n] s).2.2 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, ltStepP_pack, ih (ltStep s), Function.iterate_succ_apply]

theorem ltStepP_iterate_args (f ru rv : List Bool) (n : ℕ) :
    ltStepP^[n] (ltPack f ru rv)
      = ltPack (ltStep^[n] (f, ru, rv)).1 (ltStep^[n] (f, ru, rv)).2.1
          (ltStep^[n] (f, ru, rv)).2.2 :=
  ltStepP_iterate (f, ru, rv) n

/-- The packed comparison run to completion. -/
def ltRun (u v : List Bool) : List Bool := ltStepP^[u.length] (ltPack [false] u v)

/-- Is `u` below `v`, as a flag. -/
def ltFlag (u v : List Bool) : List Bool := pairFst (ltRun u v)

theorem ltFlag_eq (u v : List Bool) (h : v.length = u.length) :
    ltFlag u v = [ltBitsLE false u v] := by
  rw [ltFlag, ltRun, ltStepP_iterate_args, ltStep_iterate_run false u v h, ltPack]
  simp

/-- **The flag decides the comparison.** -/
theorem ltFlag_eq_true_iff (u v : List Bool) (h : v.length = u.length) :
    ltFlag u v = [true] ↔ binValLE u < binValLE v := by
  rw [ltFlag_eq u v h, ltBitsLE_spec false u v h]
  rcases lt_trichotomy (binValLE u) (binValLE v) with hlt | heq | hgt
  · rw [ite_eq_left hlt]
    simp [hlt]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    simp
    omega
  · rw [ite_eq_right (by omega), ite_eq_left hgt]
    simp
    omega

theorem ltFlag_flag (u v : List Bool) (h : v.length = u.length) :
    ltFlag u v = [true] ∨ ltFlag u v = [false] := by
  rw [ltFlag_eq u v h]
  cases ltBitsLE false u v
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ## Comparison is polynomial-time -/

theorem ltStepP_mem_FP : ltStepP ∈ FP := by
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
  have hf := hfst hid
  have hw := hsnd hid
  have hru := hfst hw
  have hrv := hsnd hw
  have hone : (fun _ : List Bool => ([false] : List Bool)) ∈ FP := constFn_mem_FP [false]
  have hbU : (fun z => bit1 (pairFst (pairSnd z))) ∈ FP := by
    have := Cobham.takeLenFn_mem_FP hone (Cobham.appendFn_mem_FP hru hone)
    simpa [bit1] using this
  have hbV : (fun z => bit1 (pairSnd (pairSnd z))) ∈ FP := by
    have := Cobham.takeLenFn_mem_FP hone (Cobham.appendFn_mem_FP hrv hone)
    simpa [bit1] using this
  have hdU : (fun z => (pairFst (pairSnd z)).drop 1) ∈ FP := by
    have := dropLenFn_mem_FP hone hru
    simpa using this
  have hdV : (fun z => (pairSnd (pairSnd z)).drop 1) ∈ FP := by
    have := dropLenFn_mem_FP hone hrv
    simpa using this
  exact Cobham.selectHeadFn_mem_FP (lenLeFlagFn_mem_FP hru hone)
    (Cobham.pairFn_mem_FP
      (Cobham.selectHeadFn_mem_FP (eqFlagFn_mem_FP hbU hbV) hf hbV)
      (Cobham.pairFn_mem_FP hdU hdV)) hid

theorem ltFlagFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => ltFlag (a z) (b z)) ∈ FP := by
  have hinit : (fun z => ltPack [false] (a z) (b z)) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP [false]) (Cobham.pairFn_mem_FP ha hb)
  have hwidth : (fun z => ltPack [false] (a z) (b z)) ∈ FP := hinit
  have hbound : ∀ z, ∀ n ≤ (a z).length,
      (ltStepP^[n] (ltPack [false] (a z) (b z))).length
        ≤ (ltPack [false] (a z) (b z)).length := by
    intro z n _
    rw [ltStepP_iterate_args]
    obtain ⟨h1, h2, h3⟩ := ltStep_iterate_length false (a z) (b z) n
    have hone1 : ([false] : List Bool).length = 1 := rfl
    rw [ltPack_length, ltPack_length]
    omega
  have h := Cobham.iterate_mem_FP ltStepP_mem_FP hinit ha hwidth hbound
  have h1 := mem_FP_comp h Cobham.fstBlock_mem_FP
  simp [ltFlag, ltRun]
  exact h1

/-! ## The larger of two numbers -/
/-- The larger of two equal-width numbers. -/
def maxBits (u v : List Bool) : List Bool := selectHead (ltFlag u v) v u

theorem maxBits_eq (u v : List Bool) (h : v.length = u.length) :
    maxBits u v = if binValLE u < binValLE v then v else u := by
  rw [maxBits]
  by_cases hlt : binValLE u < binValLE v
  · rw [ite_eq_left hlt, (ltFlag_eq_true_iff u v h).mpr hlt]
    rfl
  · rw [ite_eq_right hlt]
    rcases ltFlag_flag u v h with hf | hf
    · exact absurd ((ltFlag_eq_true_iff u v h).mp hf) hlt
    · rw [hf]
      rfl

theorem maxBitsFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => maxBits (a z) (b z)) ∈ FP :=
  Cobham.selectHeadFn_mem_FP (ltFlagFn_mem_FP ha hb) hb ha

/-! ## Arithmetic without overflow -/

/-- **Adding below the width is exact.** -/
theorem binValLE_addBits (u v : List Bool) (h : v.length = u.length)
    (hlt : binValLE u + binValLE v < 2 ^ u.length) :
    binValLE (addBits u v) = binValLE u + binValLE v := by
  have hk := addBitsLE_binValLE false u v h
  simp only [Bool.toNat_false, Nat.add_zero] at hk
  have hc : (addBitsLE false u v).1 = false := by
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    rw [hc, Bool.toNat_true, Nat.one_mul] at hk
    have := binValLE_lt (addBitsLE false u v).2
    omega
  rw [hc, Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at hk
  rw [addBits_eq u v h]
  exact hk

theorem binValLE_maxBits (u v : List Bool) (h : v.length = u.length) :
    binValLE (maxBits u v) = max (binValLE u) (binValLE v) := by
  rw [maxBits_eq u v h]
  by_cases hlt : binValLE u < binValLE v
  · rw [ite_eq_left hlt]; omega
  · rw [ite_eq_right hlt]; omega

theorem maxBits_length (u v : List Bool) (h : v.length = u.length) :
    (maxBits u v).length = u.length := by
  rw [maxBits_eq u v h]
  split
  · exact h
  · rfl

theorem bumpOver_eq_false_of_lt {w : List Bool} (h : binValLE w + 1 < 2 ^ w.length) :
    bumpOver w = false := by
  by_contra hc
  simp only [Bool.not_eq_false] at hc
  rw [bumpOver_iff] at hc
  omega

/-! ## Powers of two as bitstrings -/

theorem binValLE_replicate_false : ∀ n : ℕ, binValLE (List.replicate n false) = 0
  | 0 => rfl
  | n + 1 => by
      simp [List.replicate_succ, binValLE, binValLE_replicate_false n]

theorem padTo_nil (r : List Bool) : padTo r [] = List.replicate r.length false := by
  rw [padTo_eq_append r [] (by simp)]
  simp


theorem binValLE_replicate_false_append : ∀ (n : ℕ) (z : List Bool),
    binValLE (List.replicate n false ++ z) = 2 ^ n * binValLE z
  | 0, z => by simp
  | n + 1, z => by
      rw [List.replicate_succ, List.cons_append, binValLE_cons,
        binValLE_replicate_false_append n z, pow_succ]
      simp
      ring

/-- The bitstring of `2 ^ t`, one bit wider than `t` bits so that it can be compared with a
doubled `t + 1`-bit count. -/
def twoPowBits (t : ℕ) : List Bool := List.replicate t false ++ [true, false]

@[simp] theorem twoPowBits_length (t : ℕ) : (twoPowBits t).length = t + 2 := by
  rw [twoPowBits]
  simp

@[simp] theorem binValLE_twoPowBits (t : ℕ) : binValLE (twoPowBits t) = 2 ^ t := by
  rw [twoPowBits, binValLE_replicate_false_append]
  simp [binValLE]

/-- **The threshold comparison, as the algebra performs it.** A count `w` of `t + 1` bits exceeds
half of `2 ^ t` exactly when the doubled count is above `2 ^ t`. -/
theorem two_pow_lt_two_mul_iff (t : ℕ) (w : List Bool) (hw : w.length = t + 1) :
    2 ^ t < 2 * binValLE w ↔ ltFlag (twoPowBits t) (false :: w) = [true] := by
  have hlen : (false :: w).length = (twoPowBits t).length := by
    rw [List.length_cons, hw, twoPowBits_length]
  rw [ltFlag_eq_true_iff _ _ hlen, binValLE_twoPowBits, binValLE_cons]
  simp

/-! ## Selection on a literal flag -/

@[simp] theorem selectHead_cons_true (x y : List Bool) :
    Cobham.selectHead [true] x y = x := by
  rw [Cobham.selectHead]; simp

@[simp] theorem selectHead_cons_false (x y : List Bool) :
    Cobham.selectHead [false] x y = y := by
  rw [Cobham.selectHead]; simp

/-! ## Emptiness and the leading bit -/

/-- Is the string empty, as a flag. -/
def emptyFlag (y : List Bool) : List Bool := lenLeFlag [] y

@[simp] theorem emptyFlag_nil : emptyFlag [] = [true] := rfl

theorem emptyFlag_cons (b : Bool) (y : List Bool) : emptyFlag (b :: y) = [false] := by
  rw [emptyFlag, lenLeFlag]
  simp [nonemptyFlag, notBit]

theorem emptyFlag_pair (a b : List Bool) : emptyFlag (pair a b) = [false] := by
  cases a with
  | nil => rw [pair]; rfl
  | cons c a => rw [pair_cons_eq]; exact emptyFlag_cons _ _

theorem emptyFlagFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => emptyFlag (a z)) ∈ FP :=
  lenLeFlagFn_mem_FP (constFn_mem_FP []) ha

/-- Drop the leading bit. -/
def dropOne (y : List Bool) : List Bool := y.drop 1

theorem dropOneFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => dropOne (a z)) ∈ FP := by
  have := dropLenFn_mem_FP (constFn_mem_FP [false]) ha
  simpa [dropOne] using this

/-! ## The strings of a given length -/

/-- The bitstrings of length exactly `ℓ`. -/
def strsOfLen (ℓ : ℕ) : Finset (List Bool) :=
  (Finset.range (2 ^ ℓ)).image (bitsOfLenLE ℓ)

@[simp] theorem mem_strsOfLen {ℓ : ℕ} {l : List Bool} : l ∈ strsOfLen ℓ ↔ l.length = ℓ := by
  rw [strsOfLen, Finset.mem_image]
  constructor
  · rintro ⟨v, _, rfl⟩
    exact bitsOfLenLE_length ℓ v
  · intro h
    refine ⟨binValLE l, Finset.mem_range.mpr ?_, ?_⟩
    · have := binValLE_lt l
      rwa [h] at this
    · rw [← h, bitsOfLenLE_binValLE]

/-- The bitstrings of length at most `m`. -/
def strsLe (m : ℕ) : Finset (List Bool) :=
  (Finset.range (m + 1)).biUnion strsOfLen

@[simp] theorem mem_strsLe {m : ℕ} {l : List Bool} : l ∈ strsLe m ↔ l.length ≤ m := by
  rw [strsLe, Finset.mem_biUnion]
  constructor
  · rintro ⟨j, hj, hl⟩
    rw [mem_strsOfLen] at hl
    rw [hl]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  · intro h
    exact ⟨l.length, Finset.mem_range.mpr (by omega), mem_strsOfLen.mpr rfl⟩

theorem strsLe_nonempty (m : ℕ) : (strsLe m).Nonempty :=
  ⟨[], mem_strsLe.mpr (by simp)⟩

/-! ## Enumerating every short string with one counter

A search that sums over all strings of length at most `m` must visit each exactly once. One
counter suffices: order the strings by length and then by value, so the successor of the
all-ones string of length `ℓ` is the all-zeros string of length `ℓ + 1`. The position of a string
in that order is `Complexity.strIdx`, and it increases by one at every step, which is what makes
the enumeration a bijection. -/

/-- The position of a string in the order: by length first, then by value. -/
def strIdx (w : List Bool) : ℕ := 2 ^ w.length - 1 + binValLE w

/-- The next string in the order. -/
def nextStr (w : List Bool) : List Bool :=
  if bumpOver w then List.replicate (w.length + 1) false else bumpBits w

@[simp] theorem strIdx_nil : strIdx [] = 0 := rfl

theorem strIdx_lower (w : List Bool) : 2 ^ w.length - 1 ≤ strIdx w := by
  rw [strIdx]; omega

theorem strIdx_upper (w : List Bool) : strIdx w + 2 ≤ 2 ^ (w.length + 1) := by
  have hlt := binValLE_lt w
  have : 2 ^ (w.length + 1) = 2 ^ w.length * 2 := by rw [pow_succ]
  have hpos : 0 < 2 ^ w.length := Nat.two_pow_pos _
  rw [strIdx]
  omega

/-- **The counter steps one place along the order.** -/
theorem strIdx_nextStr (w : List Bool) : strIdx (nextStr w) = strIdx w + 1 := by
  rw [nextStr]
  by_cases hov : bumpOver w
  · rw [ite_eq_left hov, strIdx, strIdx, List.length_replicate, binValLE_replicate_false,
      (bumpOver_iff w).mp hov]
    have hpos : 0 < 2 ^ w.length := Nat.two_pow_pos _
    have : 2 ^ (w.length + 1) = 2 ^ w.length * 2 := by rw [pow_succ]
    omega
  · rw [ite_eq_right hov, strIdx, strIdx, bumpBits_length,
      binValLE_bumpBits_of_not_over w (by simpa using hov)]
    omega

theorem strIdx_iterate : ∀ i : ℕ, strIdx (nextStr^[i] []) = i := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', strIdx_nextStr, ih]

theorem strIdx_injective {w w' : List Bool} (h : strIdx w = strIdx w') : w = w' := by
  have hlen : w.length = w'.length := by
    by_contra hne
    rcases Nat.lt_or_ge w.length w'.length with hlt | hge
    · have h1 := strIdx_upper w
      have h2 := strIdx_lower w'
      have h3 : 2 ^ (w.length + 1) ≤ 2 ^ w'.length :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · have hlt : w'.length < w.length := by omega
      have h1 := strIdx_upper w'
      have h2 := strIdx_lower w
      have h3 : 2 ^ (w'.length + 1) ≤ 2 ^ w.length :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
  have hval : binValLE w = binValLE w' := by
    rw [strIdx, strIdx, hlen] at h
    omega
  rw [← bitsOfLenLE_binValLE w, ← bitsOfLenLE_binValLE w', hlen, hval]

theorem strIdx_lt_iff (m : ℕ) (w : List Bool) :
    strIdx w < 2 ^ (m + 1) - 1 ↔ w.length ≤ m := by
  constructor
  · intro h
    by_contra hlen
    have h1 := strIdx_lower w
    have h2 : 2 ^ (m + 1) ≤ 2 ^ w.length := Nat.pow_le_pow_right (by omega) (by omega)
    have hpos : 0 < 2 ^ (m + 1) := Nat.two_pow_pos _
    omega
  · intro h
    have h1 := strIdx_upper w
    have h2 : 2 ^ (w.length + 1) ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hpos : 0 < 2 ^ (m + 1) := Nat.two_pow_pos _
    omega

/-- **The counter enumerates every short string exactly once.** -/
theorem strsLe_eq_image (m : ℕ) :
    strsLe m = (Finset.range (2 ^ (m + 1) - 1)).image fun i => nextStr^[i] [] := by
  classical
  ext w
  rw [mem_strsLe, Finset.mem_image]
  constructor
  · intro h
    refine ⟨strIdx w, Finset.mem_range.mpr ((strIdx_lt_iff m w).mpr h), ?_⟩
    exact strIdx_injective (by rw [strIdx_iterate])
  · rintro ⟨i, hi, rfl⟩
    refine (strIdx_lt_iff m _).mp ?_
    rw [strIdx_iterate]
    exact Finset.mem_range.mp hi

theorem nextStr_injOn (m : ℕ) :
    Set.InjOn (fun i => nextStr^[i] []) (↑(Finset.range (2 ^ (m + 1) - 1)) : Set ℕ) := by
  intro i _ j _ h
  have := congrArg strIdx h
  rwa [strIdx_iterate, strIdx_iterate] at this

theorem bitsOfLenLE_zero (ℓ : ℕ) : bitsOfLenLE ℓ 0 = List.replicate ℓ false := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => rw [bitsOfLenLE, ih, List.replicate_succ]; simp

/-- **The counter enumerates the strings of one length too**, starting from the zeros. -/
theorem strsOfLen_eq_image (ℓ : ℕ) :
    strsOfLen ℓ
      = (Finset.range (2 ^ ℓ)).image fun i => bumpBits^[i] (List.replicate ℓ false) := by
  rw [strsOfLen]
  refine Finset.image_congr fun i hi => ?_
  rw [← bitsOfLenLE_zero, bumpBits_iterate ℓ i (Finset.mem_range.mp hi)]

theorem bumpBits_injOn (ℓ : ℕ) :
    Set.InjOn (fun i => bumpBits^[i] (List.replicate ℓ false))
      (↑(Finset.range (2 ^ ℓ)) : Set ℕ) := by
  intro i hi j hj h
  rw [Finset.mem_coe, Finset.mem_range] at hi hj
  simp only [← bitsOfLenLE_zero] at h
  rw [bumpBits_iterate ℓ i hi, bumpBits_iterate ℓ j hj] at h
  have := congrArg binValLE h
  rwa [binValLE_bitsOfLenLE ℓ i hi, binValLE_bitsOfLenLE ℓ j hj] at this

theorem nextStrFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => nextStr (a z)) ∈ FP := by
  have heq : (fun z => selectHead (bumpFlag (a z)) (padTo (a z ++ [false]) []) (bumpCode (a z)))
      = fun z => nextStr (a z) := by
    funext z
    rw [nextStr, bumpFlag_eq, bumpCode_eq]
    by_cases hov : bumpOver (a z)
    · rw [ite_eq_left hov, hov, selectHead, padTo_nil]
      simp
    · rw [ite_eq_right hov, selectHead]
      simp only [Bool.not_eq_true] at hov
      rw [hov]
      simp
  refine mem_FP_of_eq ?_ fun z => congrFun heq z
  exact Cobham.selectHeadFn_mem_FP (bumpFlagFn_mem_FP ha)
    (padToFn_mem_FP (Cobham.appendFn_mem_FP ha (constFn_mem_FP [false])) (constFn_mem_FP []))
    (bumpCodeFn_mem_FP ha)

end Complexity
