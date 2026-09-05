/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Numbering a structured index

The index types of Dinur's construction are built from a few formers: a pair of
indices, a choice between two, an optional one, a tuple. `Fintype` numbers such
a type too, but by an enumeration no algorithm can follow. This module numbers
them explicitly instead: a pair is numbered by mixed radix, a choice by
offsetting the second summand, a tuple by its digits.

The decoding is partial — a number out of range names nothing — which is what
makes the numbering compose without needing any type to be inhabited.

## Main definitions

- `Complexity.NumEnc` — an explicit numbering of a finite type

## Main results

- the instances for `Fin`, `Bool`, `Unit`, products, sums, options and tuples
-/

@[expose] public section

namespace Complexity

/-- An explicit numbering of a finite type: every value has a number below
`card`, and every number below `card` names a value. -/
class NumEnc (α : Type) where
  /-- How many values there are. -/
  card : ℕ
  /-- The number of a value. -/
  enc : α → ℕ
  /-- The value a number names, if any. -/
  dec : ℕ → Option α
  /-- Numbers are below the count. -/
  enc_lt : ∀ a, enc a < card
  /-- Decoding a number back gives the value. -/
  dec_enc : ∀ a, dec (enc a) = some a
  /-- And a number in range is the number of what it names. -/
  enc_dec : ∀ i a, dec i = some a → enc a = i
  /-- Every number below the count names something. -/
  dec_isSome : ∀ i, i < card → (dec i).isSome

namespace NumEnc

open NumEnc (card enc dec)

variable {α β : Type}

theorem enc_injective [NumEnc α] : Function.Injective (enc : α → ℕ) := by
  intro a b h
  have ha := dec_enc a
  rw [h, dec_enc b] at ha
  exact (Option.some_injective _ ha).symm

theorem dec_eq_none_of_le [NumEnc α] {i : ℕ} (h : card α ≤ i) : dec i = (none : Option α) := by
  cases hd : (dec i : Option α) with
  | none => rfl
  | some a =>
      have := enc_dec i a hd
      have := enc_lt a
      omega

/-- The value a number in range names. -/
def get [NumEnc α] {i : ℕ} (h : i < card α) : α := (dec i).get (dec_isSome i h)

@[simp] theorem dec_get [NumEnc α] {i : ℕ} (h : i < card α) : dec (α := α) i = some (get h) :=
  (Option.some_get _).symm

@[simp] theorem enc_get [NumEnc α] {i : ℕ} (h : i < card α) : enc (get h) = i :=
  enc_dec i _ (dec_get h)

@[simp] theorem get_enc [NumEnc α] (a : α) : get (enc_lt a) = a := by
  have h := dec_get (enc_lt a)
  rw [dec_enc a] at h
  exact (Option.some_injective _ h).symm

/-- **The count is the number of values.** -/
theorem card_eq_fintype_card (α : Type) [Fintype α] [NumEnc α] :
    card α = Fintype.card α := by
  have hbij : Function.Bijective (fun i : Fin (card α) => get i.isLt) := by
    constructor
    · intro i j h
      have hi : enc (get i.isLt) = i.val := enc_get i.isLt
      have hj : enc (get j.isLt) = j.val := enc_get j.isLt
      have hij : enc (get i.isLt) = enc (get j.isLt) := congrArg enc h
      rw [hi, hj] at hij
      exact Fin.ext hij
    · intro a
      exact ⟨⟨enc a, enc_lt a⟩, get_enc a⟩
  have := Fintype.card_of_bijective hbij
  rw [Fintype.card_fin] at this
  exact this

/-- The numbering, as an equivalence with an initial segment. -/
def equivFin (α : Type) [NumEnc α] : α ≃ Fin (card α) where
  toFun a := ⟨enc a, enc_lt a⟩
  invFun i := get i.isLt
  left_inv a := by simp
  right_inv i := Fin.ext (enc_get i.isLt)

/-- The numbering, as an equivalence with `Fin` of the type's own cardinality —
a drop-in replacement for `Fintype.equivFin` that an algorithm can follow. -/
noncomputable def equivFinCard (α : Type) [Fintype α] [NumEnc α] : α ≃ Fin (Fintype.card α) :=
  (equivFin α).trans (finCongr (card_eq_fintype_card α))

@[simp] theorem val_equivFinCard (α : Type) [Fintype α] [NumEnc α] (a : α) :
    (equivFinCard α a).val = enc a := rfl

/-! ### The formers -/

instance instFin (n : ℕ) : NumEnc (Fin n) where
  card := n
  enc i := i.val
  dec i := if h : i < n then some ⟨i, h⟩ else none
  enc_lt i := i.isLt
  dec_enc i := by rw [dite_eq_left i.isLt]
  enc_dec i a h := by
    by_cases hi : i < n
    · rw [dite_eq_left hi] at h
      exact congrArg Fin.val (Option.some_injective _ h).symm
    · rw [dite_eq_right hi] at h
      exact absurd h (by simp)
  dec_isSome i hi := by rw [dite_eq_left hi]; rfl

instance instBool : NumEnc Bool where
  card := 2
  enc b := if b then 0 else 1
  dec i := if i = 0 then some true else if i = 1 then some false else none
  enc_lt b := by cases b <;> norm_num
  dec_enc b := by cases b <;> norm_num
  enc_dec i a h := by
    by_cases h0 : i = 0
    · subst h0
      simp at h
      subst h
      norm_num
    · by_cases h1 : i = 1
      · subst h1
        simp at h
        subst h
        norm_num
      · rw [ite_eq_right h0, ite_eq_right h1] at h
        exact absurd h (by simp)
  dec_isSome i hi := by
    by_cases h0 : i = 0
    · subst h0; rfl
    · have h1 : i = 1 := by omega
      subst h1; rfl

instance instUnit : NumEnc Unit where
  card := 1
  enc _ := 0
  dec i := if i = 0 then some () else none
  enc_lt _ := by norm_num
  dec_enc _ := by norm_num
  enc_dec i a h := by
    by_cases h0 : i = 0
    · subst h0; rfl
    · rw [ite_eq_right h0] at h
      exact absurd h (by simp)
  dec_isSome i hi := by
    have h0 : i = 0 := by omega
    subst h0
    rfl

theorem prod_lt [NumEnc α] [NumEnc β] (a : α) (b : β) :
    enc a * card β + enc b < card α * card β := by
  have h1 := enc_lt a
  have h2 := enc_lt b
  calc enc a * card β + enc b < enc a * card β + card β := by omega
    _ = (enc a + 1) * card β := by ring
    _ ≤ card α * card β := Nat.mul_le_mul_right _ h1

theorem prod_div [NumEnc α] [NumEnc β] (a : α) (b : β) :
    (enc a * card β + enc b) / card β = enc a := by
  have h2 := enc_lt b
  have hb : 0 < card β := by omega
  rw [show enc a * card β + enc b = enc b + card β * enc a by ring,
    Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt h2, Nat.zero_add]

theorem prod_mod [NumEnc α] [NumEnc β] (a : α) (b : β) :
    (enc a * card β + enc b) % card β = enc b := by
  have h2 := enc_lt b
  rw [show enc a * card β + enc b = enc b + card β * enc a by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]

instance instProd [NumEnc α] [NumEnc β] : NumEnc (α × β) where
  card := card α * card β
  enc p := enc p.1 * card β + enc p.2
  dec i :=
    if i < card α * card β then
      (dec (i / card β)).bind fun a => (dec (i % card β)).map fun b => (a, b)
    else none
  enc_lt p := prod_lt p.1 p.2
  dec_enc p := by
    rw [ite_eq_left (prod_lt p.1 p.2), prod_div, prod_mod, dec_enc, dec_enc]
    rfl
  enc_dec i p h := by
    by_cases hlt : i < card α * card β
    · rw [ite_eq_left hlt] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨a, ha, hb⟩ := h
      rw [Option.map_eq_some_iff] at hb
      obtain ⟨b, hbb, hp⟩ := hb
      have hea := enc_dec _ a ha
      have heb := enc_dec _ b hbb
      show enc p.1 * card β + enc p.2 = i
      rw [← hp]
      show enc a * card β + enc b = i
      rw [hea, heb, Nat.mul_comm]
      exact Nat.div_add_mod i (card β)
    · rw [ite_eq_right hlt] at h
      exact absurd h (by simp)

  dec_isSome i hi := by
    have hb : 0 < card β := by
      rcases Nat.eq_zero_or_pos (card β) with h | h
      · rw [h, Nat.mul_zero] at hi; omega
      · exact h
    have hia : i / card β < card α := (Nat.div_lt_iff_lt_mul hb).mpr hi
    have him : i % card β < card β := Nat.mod_lt _ hb
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (dec_isSome _ hia)
    obtain ⟨b, hbb⟩ := Option.isSome_iff_exists.mp (dec_isSome _ him)
    rw [ite_eq_left hi, ha, hbb]
    rfl

instance instSum [NumEnc α] [NumEnc β] : NumEnc (α ⊕ β) where
  card := card α + card β
  enc := Sum.elim enc fun b => card α + enc b
  dec i := if i < card α then (dec i).map Sum.inl else (dec (i - card α)).map Sum.inr
  enc_lt x := by
    cases x with
    | inl a => have := enc_lt a; simpa using by omega
    | inr b => have := enc_lt b; simpa using by omega
  dec_enc x := by
    cases x with
    | inl a =>
        have ha := enc_lt a
        show (if enc a < card α then _ else _) = _
        simp only [Sum.elim_inl]
        rw [ite_eq_left ha, dec_enc]
        rfl
    | inr b =>
        have hb : ¬ card α + enc b < card α := by omega
        show (if card α + enc b < card α then _ else _) = _
        simp only [Sum.elim_inr]
        rw [ite_eq_right hb, Nat.add_sub_cancel_left, dec_enc]
        rfl
  enc_dec i x h := by
    by_cases hi : i < card α
    · rw [ite_eq_left hi, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, hx⟩ := h
      have := enc_dec _ a ha
      rw [← hx]
      show enc a = i
      exact this
    · rw [ite_eq_right hi, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, hx⟩ := h
      have := enc_dec _ b hb
      rw [← hx]
      show card α + enc b = i
      omega

  dec_isSome i hi := by
    by_cases h : i < card α
    · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (dec_isSome (α := α) _ h)
      rw [ite_eq_left h, ha]
      rfl
    · have hb : i - card α < card β := by omega
      obtain ⟨b, hbb⟩ := Option.isSome_iff_exists.mp (dec_isSome (α := β) _ hb)
      rw [ite_eq_right h, hbb]
      rfl

instance instOption [NumEnc α] : NumEnc (Option α) where
  card := card α + 1
  enc o := match o with | none => 0 | some a => 1 + enc a
  dec i := if i = 0 then some none else (dec (i - 1)).map some
  enc_lt o := by
    cases o with
    | none => show 0 < card α + 1; omega
    | some a => have := enc_lt a; show 1 + enc a < _; omega
  dec_enc o := by
    cases o with
    | none => show (if (0 : ℕ) = 0 then _ else _) = _; rw [ite_eq_left rfl]
    | some a =>
        show (if 1 + enc a = 0 then _ else _) = _
        rw [ite_eq_right (by omega), show 1 + enc a - 1 = enc a by omega, dec_enc]
        rfl
  enc_dec i o h := by
    by_cases h0 : i = 0
    · rw [ite_eq_left h0] at h
      rw [← Option.some_injective _ h]
      show 0 = i
      omega
    · rw [ite_eq_right h0, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, ho⟩ := h
      have := enc_dec _ a ha
      rw [← ho]
      show 1 + enc a = i
      omega
  dec_isSome i hi := by
    by_cases h0 : i = 0
    · rw [ite_eq_left h0]
      rfl
    · have hb : i - 1 < card α := by omega
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (dec_isSome (α := α) _ hb)
      rw [ite_eq_right h0, ha]
      rfl

/-- Any finite type is numbered by its own enumeration. For a type whose size
is a constant, that is all an algorithm needs: the numbering is a lookup on a
bounded key. -/
@[reducible] noncomputable def ofFintype (α : Type) [Fintype α] : NumEnc α where
  card := Fintype.card α
  enc a := (Fintype.equivFin α a).val
  dec i := if h : i < Fintype.card α then some ((Fintype.equivFin α).symm ⟨i, h⟩) else none
  enc_lt a := (Fintype.equivFin α a).isLt
  dec_enc a := by
    rw [dite_eq_left (Fintype.equivFin α a).isLt]
    simp
  enc_dec i a h := by
    by_cases hi : i < Fintype.card α
    · rw [dite_eq_left hi] at h
      rw [← Option.some_injective _ h]
      simp
    · rw [dite_eq_right hi] at h
      exact absurd h (by simp)
  dec_isSome i hi := by
    rw [dite_eq_left hi]
    rfl

end NumEnc

end Complexity
