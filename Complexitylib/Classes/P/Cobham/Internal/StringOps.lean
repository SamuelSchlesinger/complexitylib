/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Cobham.Internal.Algebra

/-!
# Length tests and bitwise operations inside the algebra

Two utilities the algebra needs for block-structured data: comparing the
lengths of two strings, and taking the bitwise exclusive-or of two strings of
equal length.

Both are built from the dispatchers of
`Complexitylib.Classes.P.Cobham.Internal.Blocks`: a length comparison is a
`drop` followed by an emptiness test, and the exclusive-or is one limited
recursion whose step reads the matching bit of the second argument through a
ruler cut to the right width.

## Main definitions

- `Cobham.lenLeFlag`, `Cobham.lenEqFlag` — length comparison flags
- `Cobham.xorSuffix` — exclusive-or of a string with the matching suffix of a
  second string

## Main results

- `Cobham.lenLeFlag_eq_true_iff`, `Cobham.lenEqFlag_eq_true_iff`
- `Cobham.lenLeFlag_mem`, `Cobham.lenEqFlag_mem`
- `Cobham.andBit_eq_true_iff` — conjunction of flags
-/

@[expose] public section

namespace Complexity

namespace Cobham

/-- Conjunction of two flags is `[true]` exactly when both are. -/
theorem andBit_eq_true_iff {x y : List Bool}
    (hx : x = [true] ∨ x = [false]) (hy : y = [true] ∨ y = [false]) :
    andBit x y = [true] ↔ x = [true] ∧ y = [true] := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [andBit]

/-- Disjunction of two flags is `[true]` exactly when one is. -/
theorem orBit_eq_true_iff {x y : List Bool}
    (hx : x = [true] ∨ x = [false]) (hy : y = [true] ∨ y = [false]) :
    orBit x y = [true] ↔ x = [true] ∨ y = [true] := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [orBit]

/-- Disjunction of flags is a flag. -/
theorem orBit_flag {x y : List Bool}
    (hx : x = [true] ∨ x = [false]) (hy : y = [true] ∨ y = [false]) :
    orBit x y = [true] ∨ orBit x y = [false] := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [orBit]

/-- A disjunction is always exactly one bit long. -/
theorem orBit_length (x y : List Bool) : (orBit x y).length = 1 := by
  rw [orBit]
  rcases x with _ | ⟨a, x⟩
  · rcases y with _ | ⟨c, y⟩
    · rfl
    · cases c <;> rfl
  · cases a
    · rcases y with _ | ⟨c, y⟩
      · rfl
      · cases c <;> rfl
    · rfl

/-- Negation of a flag. -/
theorem notBit_eq_true_iff {x : List Bool} (hx : x = [true] ∨ x = [false]) :
    notBit x = [true] ↔ x = [false] := by
  rcases hx with rfl | rfl <;> simp [notBit]

/-- The flag `|b| ≤ |a|`: nothing is left of `b` after dropping `|a|` bits. -/
def lenLeFlag (a b : List Bool) : List Bool := notBit (nonemptyFlag (b.drop a.length))

/-- The flag `|a| = |b|`. -/
def lenEqFlag (a b : List Bool) : List Bool := andBit (lenLeFlag a b) (lenLeFlag b a)

theorem lenLeFlag_flag (a b : List Bool) :
    lenLeFlag a b = [true] ∨ lenLeFlag a b = [false] := by
  rw [lenLeFlag, nonemptyFlag]
  rcases hb : b.drop a.length with _ | ⟨c, z⟩
  · exact Or.inl rfl
  · cases c <;> exact Or.inr rfl

@[simp] theorem lenLeFlag_eq_true_iff (a b : List Bool) :
    lenLeFlag a b = [true] ↔ b.length ≤ a.length := by
  rw [lenLeFlag, nonemptyFlag]
  rcases hb : b.drop a.length with _ | ⟨c, z⟩
  · have : b.length ≤ a.length := by
      have := List.length_drop (i := a.length) (l := b)
      rw [hb] at this
      simp at this
      omega
    simp [notBit, this]
  · have hlt : a.length < b.length := by
      have hlen := List.length_drop (i := a.length) (l := b)
      rw [hb] at hlen
      simp at hlen
      omega
    cases c <;> simp [notBit, Nat.not_le.mpr hlt]

theorem lenEqFlag_flag (a b : List Bool) :
    lenEqFlag a b = [true] ∨ lenEqFlag a b = [false] := by
  rw [lenEqFlag]
  rcases lenLeFlag_flag a b with h | h <;> rcases lenLeFlag_flag b a with h' | h' <;>
    rw [h, h'] <;> simp [andBit]

@[simp] theorem lenEqFlag_eq_true_iff (a b : List Bool) :
    lenEqFlag a b = [true] ↔ a.length = b.length := by
  rw [lenEqFlag, andBit_eq_true_iff (lenLeFlag_flag a b) (lenLeFlag_flag b a),
    lenLeFlag_eq_true_iff, lenLeFlag_eq_true_iff]
  omega

/-- **The length tests are in the algebra.** -/
theorem lenLeFlag_mem {n : ℕ} {ga gb : (Fin n → List Bool) → List Bool}
    (ha : Cobham ga) (hb : Cobham gb) :
    Cobham fun v : Fin n → List Bool => lenLeFlag (ga v) (gb v) :=
  (notFn (nonemptyFn (dropFn ha hb))).of_eq fun _ => rfl

theorem lenEqFlag_mem {n : ℕ} {ga gb : (Fin n → List Bool) → List Bool}
    (ha : Cobham ga) (hb : Cobham gb) :
    Cobham fun v : Fin n → List Bool => lenEqFlag (ga v) (gb v) :=
  (andFn (lenLeFlag_mem ha hb) (lenLeFlag_mem hb ha)).of_eq fun _ => rfl

/-! ## Exclusive-or -/

/-- Exclusive-or of `a` with the suffix of `b` of the same length. The bit of
`b` paired with the head of `a` sits at index `|b| - |x| - 1`, which is the
length of `b.drop (|x| + 1)` — a ruler the algebra can build from the
recursion's own tail. -/
def xorSuffix : List Bool → List Bool → List Bool
  | [], _ => []
  | true :: x, b =>
      caseBit₀ (notBit (bitAt (b.drop (false :: x).length) b))
        (true :: xorSuffix x b) (false :: xorSuffix x b)
  | false :: x, b =>
      caseBit₀ (bitAt (b.drop (false :: x).length) b)
        (true :: xorSuffix x b) (false :: xorSuffix x b)

@[simp] theorem xorSuffix_nil (b : List Bool) : xorSuffix [] b = [] := rfl

@[simp] theorem xorSuffix_length (a b : List Bool) :
    (xorSuffix a b).length = a.length := by
  induction a with
  | nil => rfl
  | cons β x ih =>
      cases β <;>
        · rw [xorSuffix]
          rcases hb : (bitAt (b.drop (false :: x).length) b) with _ | ⟨d, z⟩
          · simp [notBit, ih]
          · cases d <;> simp [notBit, ih]

/-- The bit read at the matching position. -/
private theorem bitAt_drop_eq (x b : List Bool) (h : x.length < b.length) :
    bitAt (b.drop (false :: x).length) b
      = [b[b.length - x.length - 1]'(by omega)] := by
  have hlen : (b.drop (false :: x).length).length = b.length - x.length - 1 := by
    rw [List.length_drop, List.length_cons]
    omega
  rw [bitAt, hlen]
  have hd : b.drop (b.length - x.length - 1)
      = b[b.length - x.length - 1]'(by omega) :: b.drop (b.length - x.length) := by
    have hcons := List.drop_eq_getElem_cons (l := b) (i := b.length - x.length - 1)
      (by omega)
    rw [hcons, show b.length - x.length - 1 + 1 = b.length - x.length from by omega]
  rw [hd]
  cases b[b.length - x.length - 1]'(by omega) <;> rfl

/-- **The exclusive-or is the pointwise one against the matching suffix.** -/
theorem xorSuffix_eq_zipWith (a b : List Bool) (h : a.length ≤ b.length) :
    xorSuffix a b = List.zipWith xor a (b.drop (b.length - a.length)) := by
  induction a with
  | nil => simp
  | cons β x ih =>
      have hx : x.length < b.length := by
        rw [List.length_cons] at h
        omega
      have hdrop : b.drop (b.length - (β :: x).length)
          = b[b.length - x.length - 1]'(by omega) :: b.drop (b.length - x.length) := by
        have h1 : b.length - (β :: x).length = b.length - x.length - 1 := by
          rw [List.length_cons]
          omega
        have hcons := List.drop_eq_getElem_cons (l := b) (i := b.length - x.length - 1)
          (by omega)
        rw [h1, hcons, show b.length - x.length - 1 + 1 = b.length - x.length from by omega]
      rw [hdrop, List.zipWith_cons_cons, ← ih (by omega)]
      cases β <;>
        · rw [xorSuffix, bitAt_drop_eq x b hx]
          cases b[b.length - x.length - 1]'(by omega) <;> simp [notBit]

/-- Two strings of equal length are combined bit by bit. -/
theorem xorSuffix_eq_zipWith_of_length (a b : List Bool) (h : a.length = b.length) :
    xorSuffix a b = List.zipWith xor a b := by
  rw [xorSuffix_eq_zipWith a b h.le, h]
  simp

/-- The step functions of the exclusive-or recursion. -/
private def xorStep (β : Bool) (w : Fin 3 → List Bool) : List Bool :=
  caseBit₀
    ((bif β then notBit else id) (bitAt ((w 2).drop (false :: w 0).length) (w 2)))
    (true :: w 1) (false :: w 1)

private theorem xorStep_mem (β : Bool) : Cobham (xorStep β) := by
  have hprepend : Cobham fun w : Fin 3 → List Bool => false :: w 0 :=
    (Cobham.comp (Cobham.bit false) fun _ : Fin 1 => Cobham.proj 0).of_eq fun _ => rfl
  have hbit : Cobham fun w : Fin 3 → List Bool =>
      bitAt ((w 2).drop (false :: w 0).length) (w 2) :=
    (comp₂ bitAtFn (dropFn hprepend (Cobham.proj 2)) (Cobham.proj 2)).of_eq fun _ => rfl
  have hcons1 : Cobham fun w : Fin 3 → List Bool => true :: w 1 :=
    (Cobham.comp (Cobham.bit true) fun _ : Fin 1 => Cobham.proj 1).of_eq fun _ => rfl
  have hcons0 : Cobham fun w : Fin 3 → List Bool => false :: w 1 :=
    (Cobham.comp (Cobham.bit false) fun _ : Fin 1 => Cobham.proj 1).of_eq fun _ => rfl
  cases β
  · exact (iteFn hbit hcons1 hcons0).of_eq fun _ => rfl
  · exact (iteFn (notFn hbit) hcons1 hcons0).of_eq fun _ => rfl

private theorem xorStep_length (β : Bool) (w : Fin 3 → List Bool) :
    (xorStep β w).length = (w 1).length + 1 := by
  rw [xorStep]
  rcases hc : ((bif β then notBit else id)
      (bitAt ((w 2).drop (false :: w 0).length) (w 2))) with _ | ⟨d, z⟩
  · simp
  · cases d <;> simp

private theorem recNotation_xor (a b : List Bool) :
    recNotation (fun _ : Fin 1 → List Bool => ([] : List Bool)) (xorStep false)
      (xorStep true) a (fun _ => b) = xorSuffix a b := by
  induction a with
  | nil => rfl
  | cons β x ih =>
      cases β <;>
        · rw [recNotation_cons, xorSuffix]
          simp only [Bool.cond_false, Bool.cond_true, xorStep, Fin.cons_zero, Fin.cons_one, id]
          rw [ih]
          rfl

private theorem recNotation_xor_length (a b : List Bool) :
    (recNotation (fun _ : Fin 1 → List Bool => ([] : List Bool)) (xorStep false)
      (xorStep true) a (fun _ => b)).length ≤ a.length := by
  rw [recNotation_xor, xorSuffix_length]

/-- **The exclusive-or is in the algebra.** -/
theorem xorSuffix_mem {n : ℕ} {ga gb : (Fin n → List Bool) → List Bool}
    (ha : Cobham ga) (hb : Cobham gb) :
    Cobham fun v : Fin n → List Bool => xorSuffix (ga v) (gb v) := by
  have hrec := Cobham.boundedRec (g := fun _ : Fin 1 → List Bool => ([] : List Bool))
    (h₀ := xorStep false) (h₁ := xorStep true)
    (j := fun w : Fin 2 → List Bool => w 0)
    Cobham.empty (xorStep_mem false) (xorStep_mem true) (Cobham.proj 0)
    (by
      intro x v
      have := recNotation_xor_length x (v 0)
      have hv : (fun _ : Fin 1 => v 0) = v := by
        funext i
        rw [Subsingleton.elim i 0]
      rw [hv] at this
      simpa using this)
  have hg : ∀ i : Fin 2, Cobham (![ga, gb] i) := by
    intro i
    match i with
    | 0 => exact ha
    | 1 => exact hb
  refine (Cobham.comp hrec hg).of_eq fun v => ?_
  have hb2 : (Fin.tail fun i => ![ga, gb] i v) = fun _ : Fin 1 => gb v := by
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  show recNotation _ _ _ (ga v) (Fin.tail fun i => ![ga, gb] i v) = _
  rw [hb2, recNotation_xor]

/-! ## Equality of strings -/

/-- Flag: every bit of `x` is `false`. -/
def allZeroFlag : List Bool → List Bool
  | [] => [true]
  | true :: _ => [false]
  | false :: x => allZeroFlag x

@[simp] theorem allZeroFlag_nil : allZeroFlag [] = [true] := rfl

theorem allZeroFlag_flag (x : List Bool) : allZeroFlag x = [true] ∨ allZeroFlag x = [false] := by
  induction x with
  | nil => exact Or.inl rfl
  | cons b x ih =>
      cases b
      · exact ih
      · exact Or.inr rfl

@[simp] theorem allZeroFlag_eq_true_iff (x : List Bool) :
    allZeroFlag x = [true] ↔ ∀ b ∈ x, b = false := by
  induction x with
  | nil => simp
  | cons b x ih =>
      cases b
      · simpa [allZeroFlag] using ih
      · simp [allZeroFlag]

private theorem recNotation_allZero (x : List Bool) (v : Fin 0 → List Bool) :
    recNotation (fun _ : Fin 0 → List Bool => ([true] : List Bool))
      (fun w : Fin 2 → List Bool => w 1)
      (fun _ : Fin 2 → List Bool => ([false] : List Bool)) x v = allZeroFlag x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
      cases b
      · simpa [allZeroFlag] using ih
      · rfl

/-- **The all-zero test is in the algebra.** -/
theorem allZeroFlag_mem_one : Cobham fun v : Fin 1 → List Bool => allZeroFlag (v 0) := by
  have hrec := Cobham.boundedRec (g := fun _ : Fin 0 → List Bool => ([true] : List Bool))
    (h₀ := fun w : Fin 2 → List Bool => w 1)
    (h₁ := fun _ : Fin 2 → List Bool => ([false] : List Bool))
    (j := fun _ : Fin 1 → List Bool => ([false] : List Bool))
    (Cobham.const _) (Cobham.proj 1) (Cobham.const _) (Cobham.const _)
    (by
      intro x v
      rw [recNotation_allZero]
      rcases allZeroFlag_flag x with h | h <;> simp [h])
  exact hrec.of_eq fun v => recNotation_allZero (v 0) _

theorem allZeroFlag_mem {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool => allZeroFlag (g v) :=
  (Cobham.comp allZeroFlag_mem_one fun _ : Fin 1 => hg).of_eq fun _ => rfl

/-- Flag: the two strings are equal. -/
def eqFlag (a b : List Bool) : List Bool := andBit (lenEqFlag a b) (allZeroFlag (xorSuffix a b))

theorem eqFlag_flag (a b : List Bool) : eqFlag a b = [true] ∨ eqFlag a b = [false] :=
  andBit_flag _ _

@[simp] theorem eqFlag_eq_true_iff (a b : List Bool) : eqFlag a b = [true] ↔ a = b := by
  rw [eqFlag, andBit_eq_true_iff (lenEqFlag_flag a b) (allZeroFlag_flag _),
    lenEqFlag_eq_true_iff, allZeroFlag_eq_true_iff]
  constructor
  · rintro ⟨hlen, hzero⟩
    rw [xorSuffix_eq_zipWith_of_length a b hlen] at hzero
    refine List.ext_getElem hlen fun i h₁ h₂ => ?_
    have hlt : i < (List.zipWith xor a b).length := by
      rw [List.length_zipWith]
      omega
    have hmem := List.getElem_mem hlt
    have hval := hzero _ hmem
    rw [List.getElem_zipWith] at hval
    cases ha : a[i] <;> cases hb : b[i] <;> simp_all
  · rintro rfl
    refine ⟨rfl, fun c hc => ?_⟩
    rw [xorSuffix_eq_zipWith_of_length a a rfl] at hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    rw [List.getElem_zipWith]
    simp

/-- **String equality is in the algebra.** -/
theorem eqFlag_mem {n : ℕ} {ga gb : (Fin n → List Bool) → List Bool}
    (ha : Cobham ga) (hb : Cobham gb) :
    Cobham fun v : Fin n → List Bool => eqFlag (ga v) (gb v) :=
  (andFn (lenEqFlag_mem ha hb) (allZeroFlag_mem (xorSuffix_mem ha hb))).of_eq fun _ => rfl

end Cobham

end Complexity
