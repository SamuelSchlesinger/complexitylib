/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PH
public import Mathlib.Data.Nat.Bits

/-!
# Enumerating the witnesses of a bounded existential

⚠️ Unreviewed by Bolton

`polyExistsLang` quantifies over witnesses `w` with `|w| ≤ p |x|`. A machine cannot quantify; it
counts. This file replaces the quantifier over strings by a quantifier over a *length* and a
*value* — the two numbers a loop actually iterates — by exhibiting the round trip between a
bitstring and its length-plus-binary-value.

Nothing here is about machines: it is the arithmetic that makes an enumeration faithful.

## Main definitions

- `binVal` — the big-endian value of a bitstring
- `bitsOfLen` — the bitstring of a given length and value

## Main results

- `bitsOfLen_binVal`, `binVal_bitsOfLen` — the round trip, both ways: a bijection between
  bitstrings and length-plus-value pairs
- `exists_bounded_iff`, `exists_bounded_iff_le` — the bounded existential over strings is one
  over two numbers, in either bit order
- `choicesOfNat`, `natOfChoices` — choice sequences as counter values, for the path-counting
  machine
- `bitsOfLenLE_getElem`, `choicesOfNat_apply` — each bit of the enumeration is a bit of the
  counter, in the form a tape encoding produces
- `binValLE_bits`, `bits_injective` — the canonical counter representation determines its value
- `getD_eq_bit` — reading a bitstring past its end agrees with reading the number's bits
- `dropTop`, `topPlus`, `exists_bounded_iff_count` — the same existential as a single count, over
  the counter values below `2 ^ (m + 1)`
- `bumpLE`, `dropTop_succ` — the witness advances in step with the counter, so a machine can
  carry it on a tape instead of computing it
-/

@[expose] public section

namespace Complexity

/-- The big-endian value of a bitstring. -/
def binVal : List Bool → ℕ
  | [] => 0
  | b :: w => (if b then 2 ^ w.length else 0) + binVal w

/-- The bitstring of a given length and value, big-endian. -/
def bitsOfLen : ℕ → ℕ → List Bool
  | 0, _ => []
  | ℓ + 1, v => decide (v / 2 ^ ℓ % 2 = 1) :: bitsOfLen ℓ (v % 2 ^ ℓ)

@[simp] theorem bitsOfLen_length (ℓ v : ℕ) : (bitsOfLen ℓ v).length = ℓ := by
  induction ℓ generalizing v with
  | zero => rfl
  | succ ℓ ih => simp [bitsOfLen, ih]

/-- A bitstring's value fits in its length. -/
theorem binVal_lt (w : List Bool) : binVal w < 2 ^ w.length := by
  induction w with
  | nil => simp [binVal]
  | cons b w ih =>
      have h2 : (0 : ℕ) < 2 ^ w.length := by positivity
      simp only [binVal, List.length_cons, pow_succ]
      cases b <;> simp <;> omega

/-- **The round trip.** A bitstring is recovered from its length together with its value, so
iterating over lengths and values enumerates every bitstring exactly once. -/
theorem bitsOfLen_binVal (w : List Bool) : bitsOfLen w.length (binVal w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      have hlt := binVal_lt w
      have hdiv : binVal (b :: w) / 2 ^ w.length = if b then 1 else 0 := by
        simp only [binVal]
        cases b <;> simp [Nat.div_eq_of_lt hlt]
      have hmod : binVal (b :: w) % 2 ^ w.length = binVal w := by
        simp only [binVal]
        cases b <;> simp [Nat.mod_eq_of_lt hlt]
      cases b <;> simp [bitsOfLen, hdiv, hmod, ih]

/-- **The other half of the round trip.** The value of the bitstring of length `ℓ` and value `v`
is `v` again, provided `v` fits. Together with `bitsOfLen_binVal` this makes the correspondence a
bijection, which is what lets a loop's counter *be* the witness: incrementing the counter advances
the witness by exactly one place in the enumeration. -/
theorem binVal_bitsOfLen : ∀ (ℓ v : ℕ), v < 2 ^ ℓ → binVal (bitsOfLen ℓ v) = v := by
  intro ℓ
  induction ℓ with
  | zero =>
      intro v hv
      simp only [pow_zero] at hv
      simp [bitsOfLen, binVal]
      omega
  | succ ℓ ih =>
      intro v hv
      have h2 : (0 : ℕ) < 2 ^ ℓ := by positivity
      have hmodlt : v % 2 ^ ℓ < 2 ^ ℓ := Nat.mod_lt _ h2
      have hdm : 2 ^ ℓ * (v / 2 ^ ℓ) + v % 2 ^ ℓ = v := Nat.div_add_mod v (2 ^ ℓ)
      have hdiv2 : v / 2 ^ ℓ < 2 := by
        have : v < 2 ^ ℓ * 2 := by
          have : (2 : ℕ) ^ (ℓ + 1) = 2 ^ ℓ * 2 := by ring
          omega
        exact Nat.div_lt_of_lt_mul (by omega)
      have hmod2 : v / 2 ^ ℓ % 2 = v / 2 ^ ℓ := Nat.mod_eq_of_lt hdiv2
      simp only [bitsOfLen, binVal, bitsOfLen_length, ih _ hmodlt, hmod2]
      by_cases hb : v / 2 ^ ℓ = 1
      · rw [hb] at hdm
        simp [hb]
        omega
      · have hb0 : v / 2 ^ ℓ = 0 := by omega
        rw [hb0] at hdm
        simp [hb0]
        omega

/-- **A bounded existential over strings is a bounded existential over two numbers.** This is the
form a counting loop can implement: iterate the length, then the value. -/
theorem exists_bounded_iff (m : ℕ) (P : List Bool → Prop) :
    (∃ w : List Bool, w.length ≤ m ∧ P w) ↔ ∃ ℓ ≤ m, ∃ v < 2 ^ ℓ, P (bitsOfLen ℓ v) := by
  constructor
  · rintro ⟨w, hlen, hP⟩
    exact ⟨w.length, hlen, binVal w, binVal_lt w, by rwa [bitsOfLen_binVal]⟩
  · rintro ⟨ℓ, hℓ, v, -, hP⟩
    exact ⟨bitsOfLen ℓ v, by simpa using hℓ, hP⟩


/-! ## The little-endian enumeration

Every binary subroutine in the library — `TM.binarySuccTM` and the rest — uses canonical
little-endian bit lists. Since the *order* in which witnesses are enumerated is immaterial, only
that the enumeration is a bijection, the machine should use the convention its counter already
speaks. These are the little-endian counterparts of the definitions above. -/

/-- The little-endian value of a bitstring. -/
def binValLE : List Bool → ℕ
  | [] => 0
  | b :: w => (if b then 1 else 0) + 2 * binValLE w

/-- The little-endian bitstring of a given length and value. -/
def bitsOfLenLE : ℕ → ℕ → List Bool
  | 0, _ => []
  | ℓ + 1, v => decide (v % 2 = 1) :: bitsOfLenLE ℓ (v / 2)

@[simp] theorem bitsOfLenLE_length (ℓ v : ℕ) : (bitsOfLenLE ℓ v).length = ℓ := by
  induction ℓ generalizing v with
  | zero => rfl
  | succ ℓ ih => simp [bitsOfLenLE, ih]

theorem binValLE_lt (w : List Bool) : binValLE w < 2 ^ w.length := by
  induction w with
  | nil => simp [binValLE]
  | cons b w ih =>
      simp only [binValLE, List.length_cons, pow_succ]
      cases b <;> simp <;> omega

/-- The round trip, one way. -/
theorem bitsOfLenLE_binValLE (w : List Bool) : bitsOfLenLE w.length (binValLE w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      have hmod : binValLE (b :: w) % 2 = if b then 1 else 0 := by
        simp only [binValLE]
        cases b <;> simp [Nat.add_mul_mod_self_left]
      have hdiv : binValLE (b :: w) / 2 = binValLE w := by
        simp only [binValLE]
        cases b <;> simp [Nat.add_mul_div_left]
      cases b <;> simp [bitsOfLenLE, hdiv, hmod, ih]

/-- The round trip, the other way. -/
theorem binValLE_bitsOfLenLE : ∀ (ℓ v : ℕ), v < 2 ^ ℓ → binValLE (bitsOfLenLE ℓ v) = v := by
  intro ℓ
  induction ℓ with
  | zero =>
      intro v hv
      simp only [pow_zero] at hv
      simp [bitsOfLenLE, binValLE]
      omega
  | succ ℓ ih =>
      intro v hv
      have hhalf : v / 2 < 2 ^ ℓ := by
        have : (2 : ℕ) ^ (ℓ + 1) = 2 ^ ℓ * 2 := by ring
        omega
      have hdm : 2 * (v / 2) + v % 2 = v := by omega
      simp only [bitsOfLenLE, binValLE, ih _ hhalf]
      by_cases hb : v % 2 = 1
      · simp [hb]
        omega
      · simp [hb]
        omega

/-- **The little-endian form of the enumeration.** -/
theorem exists_bounded_iff_le (m : ℕ) (P : List Bool → Prop) :
    (∃ w : List Bool, w.length ≤ m ∧ P w) ↔ ∃ ℓ ≤ m, ∃ v < 2 ^ ℓ, P (bitsOfLenLE ℓ v) := by
  constructor
  · rintro ⟨w, hlen, hP⟩
    exact ⟨w.length, hlen, binValLE w, binValLE_lt w, by rwa [bitsOfLenLE_binValLE]⟩
  · rintro ⟨ℓ, hℓ, v, -, hP⟩
    exact ⟨bitsOfLenLE ℓ v, by simpa using hℓ, hP⟩


/-! ## Choice sequences as counter values

The counting machine iterates a binary counter, but `NTM.acceptCount` ranges over functions
`Fin T → Bool`. These convert between the two, reusing the bitstring enumeration. -/

/-- The choice sequence of length `T` with counter value `v`. -/
def choicesOfNat (T v : ℕ) : Fin T → Bool :=
  fun j => (bitsOfLenLE T v)[j.val]'(by simp)

/-- The counter value of a choice sequence. -/
def natOfChoices (T : ℕ) (ch : Fin T → Bool) : ℕ := binValLE (List.ofFn ch)

theorem natOfChoices_lt (T : ℕ) (ch : Fin T → Bool) : natOfChoices T ch < 2 ^ T := by
  have h := binValLE_lt (List.ofFn ch)
  rwa [List.length_ofFn] at h

theorem choicesOfNat_natOfChoices (T : ℕ) (ch : Fin T → Bool) :
    choicesOfNat T (natOfChoices T ch) = ch := by
  have hlen : (List.ofFn ch).length = T := List.length_ofFn
  have hround : bitsOfLenLE T (natOfChoices T ch) = List.ofFn ch := by
    have h := bitsOfLenLE_binValLE (List.ofFn ch)
    rwa [hlen] at h
  funext j
  simp only [choicesOfNat]
  simp [hround]

theorem natOfChoices_choicesOfNat (T v : ℕ) (hv : v < 2 ^ T) :
    natOfChoices T (choicesOfNat T v) = v := by
  have hofFn : List.ofFn (choicesOfNat T v) = bitsOfLenLE T v := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp [choicesOfNat]
  rw [natOfChoices, hofFn, binValLE_bitsOfLenLE T v hv]


/-- **Each bit of the enumeration is a bit of the counter.** The `j`-th entry of the length-`ℓ`
little-endian string for `v` is bit `j` of `v`. This is the form in which the correspondence meets
a tape: whatever encoding a counter tape uses, its `j`-th cell holds this bit — and cells beyond
the counter's own digits read as `false`, which is bit `j` of `v` too. -/
theorem bitsOfLenLE_getElem :
    ∀ (ℓ v j : ℕ) (h : j < ℓ), (bitsOfLenLE ℓ v)[j]'(by simpa using h)
      = decide (v / 2 ^ j % 2 = 1) := by
  intro ℓ
  induction ℓ with
  | zero => intro v j h; omega
  | succ ℓ ih =>
      intro v j h
      cases j with
      | zero => simp [bitsOfLenLE]
      | succ j =>
          have hj : j < ℓ := by omega
          have hstep := ih (v / 2) j hj
          simp only [bitsOfLenLE, List.getElem_cons_succ]
          rw [hstep, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]

/-- The `j`-th choice bit of counter value `v` is bit `j` of `v`. -/
theorem choicesOfNat_apply (T v : ℕ) (j : Fin T) :
    choicesOfNat T v j = decide (v / 2 ^ j.val % 2 = 1) :=
  bitsOfLenLE_getElem T v j.val j.isLt


/-! ## Canonical bits and their value

The library's counter subroutines represent a number by `Nat.bits`. Reading that representation
back as a value is `binValLE`, and the two are mutually inverse — which is what makes a counter
tape determine the number it holds. -/

/-- **The canonical representation reads back as its value.** -/
theorem binValLE_bits : ∀ n : ℕ, binValLE n.bits = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n, ih with
      | 0, _ => rfl
      | (m + 1), ih =>
          rcases Nat.even_or_odd (m + 1) with ⟨q, hq⟩ | ⟨q, hq⟩
          · have hq0 : q ≠ 0 := by omega
            have h2 : m + 1 = 2 * q := by omega
            rw [h2, Nat.bit0_bits q hq0, binValLE, ih q (by omega)]
            simp
          · have h2 : m + 1 = 2 * q + 1 := by omega
            rw [h2, Nat.bit1_bits q, binValLE, ih q (by omega)]
            simp
            omega

/-- The canonical representation determines the number. -/
theorem bits_injective : Function.Injective Nat.bits := by
  intro a b h
  rw [← binValLE_bits a, ← binValLE_bits b, h]


/-- **Reading a bitstring past its end agrees with reading the number's bits.** Entry `j` of a
little-endian string, taken as `false` beyond the end, is bit `j` of the number it denotes — the
high bits of that number being zero. This is what lets a counter tape be read as a choice
sequence with no padding step. -/
theorem getD_eq_bit : ∀ (w : List Bool) (j : ℕ),
    w.getD j false = decide (binValLE w / 2 ^ j % 2 = 1) := by
  intro w
  induction w with
  | nil =>
      intro j
      simp [binValLE, List.getD]
  | cons b w ih =>
      intro j
      cases j with
      | zero =>
          simp only [pow_zero, Nat.div_one, binValLE, List.getD]
          cases b <;> simp [Nat.add_mul_mod_self_left]
      | succ j =>
          have hstep : binValLE (b :: w) / 2 ^ (j + 1) = binValLE w / 2 ^ j := by
            simp only [binValLE, pow_succ]
            rw [Nat.mul_comm (2 ^ j) 2, ← Nat.div_div_eq_div_mul]
            cases b <;> simp [Nat.add_mul_div_left]
          have hgd : (b :: w).getD (j + 1) false = w.getD j false := rfl
          rw [hgd, hstep, ih j]

/-! ## The single-counter enumeration

A nested loop over a length and then a value is two loops; a machine that enumerates witnesses
would rather run one. Appending a marker bit turns the enumeration into a plain count: the
numbers in `[1, 2 ^ (m + 1))` are in bijection with the bitstrings of length at most `m`, a
number denoting its canonical bits with the leading one removed. -/

/-- The witness a counter value denotes: the value's canonical bits, less the leading one. -/
def dropTop (v : ℕ) : List Bool := v.bits.dropLast

/-- The counter value at which a witness is enumerated: its value with a marker bit above it. -/
def topPlus (w : List Bool) : ℕ := binValLE w + 2 ^ w.length

theorem one_le_topPlus (w : List Bool) : 1 ≤ topPlus w :=
  le_trans Nat.one_le_two_pow (Nat.le_add_left _ _)

/-- **The marker bit is the leading one.** -/
theorem bits_topPlus : ∀ w : List Bool, (topPlus w).bits = w ++ [true]
  | [] => by decide
  | b :: w => by
      have hpos : topPlus w ≠ 0 := by have := one_le_topPlus w; omega
      have hsplit : topPlus (b :: w) = 2 * topPlus w + (if b then 1 else 0) := by
        simp only [topPlus, binValLE, List.length_cons, pow_succ]
        cases b <;> simp <;> ring
      cases b with
      | false =>
          have h0 : topPlus (false :: w) = 2 * topPlus w := by rw [hsplit]; simp
          rw [h0, Nat.bit0_bits _ hpos, bits_topPlus w]
          rfl
      | true =>
          have h1 : topPlus (true :: w) = 2 * topPlus w + 1 := by rw [hsplit]; simp
          rw [h1, Nat.bit1_bits, bits_topPlus w]
          rfl

/-- **The round trip.** -/
theorem dropTop_topPlus (w : List Bool) : dropTop (topPlus w) = w := by
  rw [dropTop, bits_topPlus]
  simp

theorem topPlus_lt {m : ℕ} {w : List Bool} (h : w.length ≤ m) : topPlus w < 2 ^ (m + 1) := by
  have hv := binValLE_lt w
  have hmono : (2 : ℕ) ^ w.length ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
  have : topPlus w < 2 ^ w.length + 2 ^ w.length := by
    rw [topPlus]; omega
  calc topPlus w < 2 ^ w.length + 2 ^ w.length := this
    _ ≤ 2 ^ m + 2 ^ m := by omega
    _ = 2 ^ (m + 1) := by ring

/-- A counter value below `2 ^ (m + 1)` denotes a witness of length at most `m`. -/
theorem length_dropTop_le {m v : ℕ} (hv : v < 2 ^ (m + 1)) : (dropTop v).length ≤ m := by
  have hsize : v.size ≤ m + 1 := Nat.size_le.mpr hv
  have hlen : v.bits.length = v.size := Nat.size_eq_bits_len v
  rw [dropTop, List.length_dropLast, hlen]
  omega

/-- **The bounded existential is a count.** A witness of length at most `m` exists exactly when
some counter value below `2 ^ (m + 1)` denotes one — a single loop over a single register, with
the same shape the path-counting machine of `PP ⊆ PSPACE` already runs.

The enumeration is not injective at the bottom — `0` and `1` both denote the empty witness — but
it does not have to be: only that every witness is denoted, and that every value denotes one. -/
theorem exists_bounded_iff_count (m : ℕ) (P : List Bool → Prop) :
    (∃ w : List Bool, w.length ≤ m ∧ P w) ↔ ∃ v < 2 ^ (m + 1), P (dropTop v) := by
  constructor
  · rintro ⟨w, hlen, hP⟩
    exact ⟨topPlus w, topPlus_lt hlen, by rwa [dropTop_topPlus]⟩
  · rintro ⟨v, hlt, hP⟩
    exact ⟨dropTop v, length_dropTop_le hlt, hP⟩

/-! ## Enumerating the witness alongside the counter

The machine will not compute `dropTop` from the counter; it will carry the witness on a tape of
its own and advance it in step with the counter. `bumpLE` is that advance — the counter's
increment seen through `dropTop`. It is the ordinary little-endian increment except at the end of
the string, where the carry *extends* the witness by a zero instead of writing a one: the bit it
would have written is the counter's leading one, which `dropTop` discards. -/

/-- One step of the witness enumeration: increment the string, extending it on overflow. -/
def bumpLE : List Bool → List Bool
  | [] => [false]
  | false :: w => true :: w
  | true :: w => false :: bumpLE w

@[simp] theorem topPlus_nil : topPlus [] = 1 := rfl

/-- **The advance is the counter's increment.** -/
theorem topPlus_bumpLE : ∀ w : List Bool, topPlus (bumpLE w) = topPlus w + 1
  | [] => rfl
  | false :: w => by
      simp only [bumpLE, topPlus, binValLE, List.length_cons]
      simp
      omega
  | true :: w => by
      have ih := topPlus_bumpLE w
      have hdouble : ∀ u : List Bool, topPlus (false :: u) = 2 * topPlus u := by
        intro u
        simp only [topPlus, binValLE, List.length_cons, pow_succ]
        simp
        omega
      rw [bumpLE, hdouble, ih]
      simp only [topPlus, binValLE, List.length_cons, pow_succ]
      simp
      omega

/-- **A positive number's canonical bits end in one**, so they are its witness and that one. -/
theorem bits_eq_dropTop : ∀ v : ℕ, 1 ≤ v → v.bits = dropTop v ++ [true] := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
      match v, ih with
      | 0, _ => intro h; omega
      | (m + 1), ih =>
          intro _
          have key : ∀ (b : Bool) (q : ℕ), 1 ≤ q → q < m + 1 → (m + 1).bits = b :: q.bits →
              (m + 1).bits = dropTop (m + 1) ++ [true] := by
            intro b q hq0 hlt hb
            have hqb := ih q hlt hq0
            have hd : dropTop (m + 1) = b :: dropTop q := by
              show (m + 1).bits.dropLast = b :: q.bits.dropLast
              rw [hb, hqb, List.dropLast_cons_of_ne_nil (by simp), List.dropLast_concat]
            rw [hb, hqb, hd]
            rfl
          rcases Nat.even_or_odd (m + 1) with ⟨q, hq⟩ | ⟨q, hq⟩
          · have hb : (m + 1).bits = false :: q.bits := by
              rw [show m + 1 = 2 * q from by omega]; exact Nat.bit0_bits q (by omega)
            exact key false q (by omega) (by omega) hb
          · rcases Nat.eq_zero_or_pos q with hq0 | hq0
            · rw [show m + 1 = 1 from by omega]
              rfl
            · have hb : (m + 1).bits = true :: q.bits := by
                rw [show m + 1 = 2 * q + 1 from by omega]; exact Nat.bit1_bits q
              exact key true q hq0 (by omega) hb

/-- **The counter is recovered from its witness.** -/
theorem topPlus_dropTop {v : ℕ} (h : 1 ≤ v) : topPlus (dropTop v) = v :=
  bits_injective ((bits_topPlus _).trans (bits_eq_dropTop v h).symm)

/-- **The witness advances with the counter.** This is the loop invariant the enumerating machine
carries: one tape holds the counter, another holds the witness it denotes, and each iteration
advances both. -/
theorem dropTop_succ {v : ℕ} (h : 1 ≤ v) : dropTop (v + 1) = bumpLE (dropTop v) := by
  conv_lhs => rw [← topPlus_dropTop h, ← topPlus_bumpLE]
  exact dropTop_topPlus _

/-- **Every witness of the admitted lengths is still reached**, with the counter starting at one:
the value `0`, which the count above admits, denotes the same empty witness as `1`. -/
theorem exists_bounded_iff_count_pos (m : ℕ) (P : List Bool → Prop) :
    (∃ w : List Bool, w.length ≤ m ∧ P w) ↔
      ∃ v, 1 ≤ v ∧ v < 2 ^ (m + 1) ∧ P (dropTop v) := by
  rw [exists_bounded_iff_count]
  constructor
  · rintro ⟨v, hlt, hP⟩
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · exact ⟨1, le_refl 1, Nat.one_lt_two_pow (by omega), hP⟩
    · exact ⟨v, hv, hlt, hP⟩
  · rintro ⟨v, -, hlt, hP⟩
    exact ⟨v, hlt, hP⟩

end Complexity
