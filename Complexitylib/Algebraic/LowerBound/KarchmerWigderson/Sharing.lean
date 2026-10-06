/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Khrapchenko
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Group.Real

/-!
# Khrapchenko's bound for circuits with few shared gates

A `SharedProgram n k` is a sequence of `k + 1` De Morgan formulas on `n` inputs in which each
formula also reads the values of the earlier ones: `share G P` computes the formula `G`,
appends its value to the inputs as a new last variable, and continues with `P`, and
`output F` returns the value of the formula `F`. A shared value is read through literals of
either sign, any number of times. Unfolded, this is a circuit of fan-in-two AND and OR gates
with negations free on wires in which only the `k` shared gates can have fan-out at least two,
and cutting such a circuit at its gates of fan-out at least two gives a program with the same
AND and OR gates; that correspondence is not formalized here. `SharedProgram.gates` counts the
AND and OR gates and `SharedProgram.inputLeaves` the literal leaves that read an input rather
than a shared value.

**Theorem.** If a program with `k` shared gates is `1` on `A` and `0` on `B`, and `X` is its
number of input leaves, then `|edges A B|² ≤ (k + 1) · X · |A| · |B|`
(`SharedProgram.sq_card_edges_le`). For `k = 0` this is Khrapchenko's theorem.

The proof extends the inductive proof of Khrapchenko's theorem. Call an edge of `A × B`
*uncut* when its endpoints agree on every shared value computed so far. For a single formula,
`|uncut edges|² ≤ X · |A| · |B|`, where `X` counts input literals only: a literal on a shared
variable separates only pairs that the shared value cuts, so it contributes no uncut edge
(`Formula.sq_card_uncutEdges_le`). For `share G P`, an uncut edge on which `G` is constant
stays uncut for `P`, and the others are separated by `G` or by its De Morgan dual on the
rectangles `{G = 1} × {G = 0}` and `{G = 0} × {G = 1}`, which together contain at most
`√(X_G · |A| · |B|)` of them by the Cauchy–Schwarz inequality. Summing over the `k + 1`
formulas, Cauchy–Schwarz gives the factor `k + 1` (`SharedProgram.sq_card_uncutEdges_le`).

Through `KhrapchenkoBound` the theorem inherits Khrapchenko's corollaries. For all `n ≥ 1` and
`k`, every program with `k` shared gates computing the parity of `n` bits satisfies
`n² ≤ (k + 1) · (gates + k + 1)`, so it has at least `n² / (k + 1) - (k + 1)` gates
(`SharedProgram.parity_sq_le_gates`). If `(k + 1) · (C + 1) ≤ n` it has at least `C · n`
gates (`SharedProgram.mul_le_gates_of_parity`), so parity needs superlinear size whenever
`k = o(n)` (`SharedProgram.isLittleO_gates_of_parity`). The threshold and majority bounds
transfer the same way (`SharedProgram.threshold_mul_le_gates`,
`SharedProgram.majority_mul_le_gates`).
-/

@[expose] public section

namespace Algebraic
namespace KW

/-! ### Counting gates and input leaves of a formula -/

namespace Formula

variable {N : Nat}

/-- The number of literal leaves on the variables `0, …, m - 1`. Constants and literals on
later variables are not counted. -/
def inputLeaves : Formula N → Nat → Nat
  | lit i _, m => if i.val < m then 1 else 0
  | const _, _ => 0
  | and l r, m => l.inputLeaves m + r.inputLeaves m
  | or l r, m => l.inputLeaves m + r.inputLeaves m

/-- The number of binary AND and OR gates. -/
def gates : Formula N → Nat
  | lit _ _ => 0
  | const _ => 0
  | and l r => l.gates + r.gates + 1
  | or l r => l.gates + r.gates + 1

theorem leaves_eq_gates_add_one : ∀ F : Formula N, F.leaves = F.gates + 1
  | lit _ _ => rfl
  | const _ => rfl
  | and l r => by
    simp only [leaves, gates, leaves_eq_gates_add_one l, leaves_eq_gates_add_one r]
    omega
  | or l r => by
    simp only [leaves, gates, leaves_eq_gates_add_one l, leaves_eq_gates_add_one r]
    omega

theorem inputLeaves_le_leaves (m : Nat) : ∀ F : Formula N, F.inputLeaves m ≤ F.leaves
  | lit i _ => by
    simp only [inputLeaves, leaves]
    split <;> omega
  | const _ => Nat.zero_le _
  | and l r => by
    simp only [inputLeaves, leaves]
    have := inputLeaves_le_leaves m l
    have := inputLeaves_le_leaves m r
    omega
  | or l r => by
    simp only [inputLeaves, leaves]
    have := inputLeaves_le_leaves m l
    have := inputLeaves_le_leaves m r
    omega

theorem inputLeaves_le_gates_add_one (m : Nat) (F : Formula N) :
    F.inputLeaves m ≤ F.gates + 1 :=
  (F.inputLeaves_le_leaves m).trans F.leaves_eq_gates_add_one.le

@[simp] theorem inputLeaves_neg (m : Nat) : ∀ F : Formula N, F.neg.inputLeaves m = F.inputLeaves m
  | lit _ _ => rfl
  | const _ => rfl
  | and l r => by simp [neg, inputLeaves, inputLeaves_neg m l, inputLeaves_neg m r]
  | or l r => by simp [neg, inputLeaves, inputLeaves_neg m l, inputLeaves_neg m r]

end Formula

/-! ### Programs with shared gates -/

/-- A De Morgan program on `n` inputs with `k` shared gates: `k + 1` De Morgan formulas, where
each formula reads the inputs and the values of the earlier ones. `output F` returns the
formula `F`. `share G P` computes the formula `G`, appends its value to the inputs as the new
last variable `n`, and runs `P` on the `n + 1` resulting variables. Unfolded, this is a circuit
in which only the roots of the `k` shared formulas can have fan-out at least two: inputs and
shared values are read through literals of either sign, and every other gate lies inside one
formula. -/
inductive SharedProgram : Nat → Nat → Type
  /-- Return a formula of the current variables. -/
  | output {n : Nat} (F : Formula n) : SharedProgram n 0
  /-- Compute a shared value and continue with it as a new last variable. -/
  | share {n k : Nat} (G : Formula n) (P : SharedProgram (n + 1) k) : SharedProgram n (k + 1)

namespace SharedProgram

variable {n N k : Nat}

/-- Evaluate a program. -/
def eval : {n k : Nat} → SharedProgram n k → (Fin n → Bool) → Bool
  | _, _, output F, x => F.eval x
  | _, _, share G P, x => P.eval (Fin.snoc x (G.eval x))

@[simp] theorem eval_output (F : Formula n) (x : Fin n → Bool) :
    (output F).eval x = F.eval x := rfl

@[simp] theorem eval_share (G : Formula n) (P : SharedProgram (n + 1) k) (x : Fin n → Bool) :
    (share G P).eval x = P.eval (Fin.snoc x (G.eval x)) := rfl

/-- The number of binary AND and OR gates, summed over the formulas. -/
def gates : {n k : Nat} → SharedProgram n k → Nat
  | _, _, output F => F.gates
  | _, _, share G P => G.gates + P.gates

/-- The number of literal leaves on the variables `0, …, m - 1`, summed over the formulas. For
a program on `n` inputs, `inputLeaves n` counts the leaves reading an input rather than a
shared value. -/
def inputLeaves : {N k : Nat} → SharedProgram N k → Nat → Nat
  | _, _, output F, m => F.inputLeaves m
  | _, _, share G P, m => G.inputLeaves m + P.inputLeaves m

/-- A program computes `f` when it agrees with `f` everywhere. -/
def Computes (P : SharedProgram n k) (f : Cslib.BooleanFunction n) : Prop :=
  ∀ x, P.eval x = f x

/-- A program separates `A` from `B` when it is `1` on `A` and `0` on `B`. -/
def Separates (P : SharedProgram n k) (A B : Finset (Fin n → Bool)) : Prop :=
  (∀ x ∈ A, P.eval x = true) ∧ ∀ y ∈ B, P.eval y = false

/-- The input leaves number at most the gates plus one leaf per formula. -/
theorem inputLeaves_le_gates (m : Nat) : ∀ {N k : Nat} (P : SharedProgram N k),
    P.inputLeaves m ≤ P.gates + k + 1
  | _, _, output F => F.inputLeaves_le_gates_add_one m
  | _, _, share G P => by
    simp only [inputLeaves, gates]
    have := G.inputLeaves_le_gates_add_one m
    have := inputLeaves_le_gates m P
    omega

end SharedProgram

/-! ### Uncut edges -/

variable {n N k : Nat}

/-- The edges of `A × B` whose endpoints agree, under `val`, on every variable from `n` on.
When `val` appends shared values to the inputs, these are the edges no shared value cuts. -/
noncomputable def uncutEdges (val : (Fin n → Bool) → Fin N → Bool)
    (A B : Finset (Fin n → Bool)) : Finset ((Fin n → Bool) × (Fin n → Bool)) :=
  (edges A B).filter fun p => ∀ i : Fin N, n ≤ i.val → val p.1 i = val p.2 i

theorem mem_uncutEdges {val : (Fin n → Bool) → Fin N → Bool} {A B : Finset (Fin n → Bool)}
    {p : (Fin n → Bool) × (Fin n → Bool)} :
    p ∈ uncutEdges val A B ↔
      (p.1 ∈ A ∧ p.2 ∈ B) ∧ (diff p.1 p.2).card = 1 ∧
        ∀ i : Fin N, n ≤ i.val → val p.1 i = val p.2 i := by
  simp only [uncutEdges, edges, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- Splitting the zero side of a rectangle splits its uncut edges. -/
theorem card_uncutEdges_split_right (val : (Fin n → Bool) → Fin N → Bool)
    (A B : Finset (Fin n → Bool)) (p : (Fin n → Bool) → Prop) [DecidablePred p] :
    (uncutEdges val A B).card =
      (uncutEdges val A (B.filter p)).card +
        (uncutEdges val A (B.filter fun y => ¬ p y)).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext ⟨x, y⟩
    by_cases hy : p y <;> simp [mem_uncutEdges, hy]
  · rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h₁ h₂
    rw [mem_uncutEdges] at h₁ h₂
    exact (Finset.mem_filter.mp h₂.1.2).2 (Finset.mem_filter.mp h₁.1.2).2

/-- Splitting the one side of a rectangle splits its uncut edges. -/
theorem card_uncutEdges_split_left (val : (Fin n → Bool) → Fin N → Bool)
    (A B : Finset (Fin n → Bool)) (p : (Fin n → Bool) → Prop) [DecidablePred p] :
    (uncutEdges val A B).card =
      (uncutEdges val (A.filter p) B).card +
        (uncutEdges val (A.filter fun x => ¬ p x) B).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext ⟨x, y⟩
    by_cases hx : p x <;> simp [mem_uncutEdges, hx]
  · rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h₁ h₂
    rw [mem_uncutEdges] at h₁ h₂
    exact (Finset.mem_filter.mp h₂.1.1).2 (Finset.mem_filter.mp h₁.1.1).2

/-- The Cauchy–Schwarz inequality for two terms, without square roots: if `x² ≤ p · q` and
`y² ≤ r · s` then `(x + y)² ≤ (p + r) · (q + s)`. -/
theorem sq_add_le_add_mul_add {x y p q r s : Nat} (h₁ : x ^ 2 ≤ p * q) (h₂ : y ^ 2 ≤ r * s) :
    (x + y) ^ 2 ≤ (p + r) * (q + s) := by
  have hprod : ((x * y) ^ 2 : ℤ) ≤ (p * s : ℤ) * (r * q) := by
    have : (x * y) ^ 2 ≤ (p * s) * (r * q) :=
      calc (x * y) ^ 2 = x ^ 2 * y ^ 2 := by ring
        _ ≤ (p * q) * (r * s) := Nat.mul_le_mul h₁ h₂
        _ = (p * s) * (r * q) := by ring
    exact_mod_cast this
  have hsq : (2 * (x * y)) ^ 2 ≤ (p * s + r * q) ^ 2 := by
    have : ((2 * (x * y)) ^ 2 : ℤ) ≤ (p * s + r * q : ℤ) ^ 2 := by
      nlinarith [sq_nonneg ((p * s : ℤ) - r * q)]
    exact_mod_cast this
  have hmid : 2 * (x * y) ≤ p * s + r * q := (Nat.pow_le_pow_iff_left two_ne_zero).mp hsq
  nlinarith

/-- **Khrapchenko's theorem with shared variables.** Let `val` extend each input by further
variables, keeping the first `n` variables equal to the input. If a formula `F` over the
extended variables is `1` on `val '' A` and `0` on `val '' B`, the edges of `A × B` that agree
on the extra variables satisfy `|uncut edges|² ≤ X · |A| · |B|`, where `X` counts only the
literal leaves on the first `n` variables. -/
theorem Formula.sq_card_uncutEdges_le (val : (Fin n → Bool) → Fin N → Bool)
    (hval : ∀ x (i : Fin N) (hi : i.val < n), val x i = x ⟨i.val, hi⟩) :
    ∀ (F : Formula N) (A B : Finset (Fin n → Bool)), (∀ x ∈ A, F.eval (val x) = true) →
      (∀ y ∈ B, F.eval (val y) = false) →
      (uncutEdges val A B).card ^ 2 ≤ F.inputLeaves n * A.card * B.card
  | .lit i b, A, B, hA, hB => by
    by_cases hi : i.val < n
    · have hsep : (Formula.lit (⟨i.val, hi⟩ : Fin n) b).Separates A B :=
        ⟨fun x hx => by simpa [hval x i hi] using hA x hx,
          fun y hy => by simpa [hval y i hi] using hB y hy⟩
      have hsub : (uncutEdges val A B).card ≤ (edges A B).card := Finset.card_filter_le _ _
      simp only [inputLeaves, hi, ↓reduceIte, one_mul, sq]
      exact Nat.mul_le_mul (hsub.trans (card_edges_le_left_of_lit hsep))
        (hsub.trans (card_edges_le_right_of_lit hsep))
    · have hempty : uncutEdges val A B = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        rintro ⟨x, y⟩ hxy
        rw [mem_uncutEdges] at hxy
        have hx := hA x hxy.1.1
        have hy := hB y hxy.1.2
        rw [eval_lit, hxy.2.2 i (by omega)] at hx
        rw [eval_lit, hx] at hy
        exact Bool.noConfusion hy
      simp [hempty]
  | .const b, A, B, hA, hB => by
    have hempty : uncutEdges val A B = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      rintro ⟨x, y⟩ hxy
      rw [mem_uncutEdges] at hxy
      have hx := hA x hxy.1.1
      have hy := hB y hxy.1.2
      rw [eval_const] at hx hy
      rw [hx] at hy
      exact Bool.noConfusion hy
    simp [hempty]
  | .and l r, A, B, hA, hB => by
    have hl := Formula.sq_card_uncutEdges_le val hval l A
      (B.filter fun y => l.eval (val y) = false)
      (fun x hx => by
        have := hA x hx
        simp only [eval_and, Bool.and_eq_true] at this
        exact this.1)
      (fun y hy => (Finset.mem_filter.mp hy).2)
    have hr := Formula.sq_card_uncutEdges_le val hval r A
      (B.filter fun y => ¬ l.eval (val y) = false)
      (fun x hx => by
        have := hA x hx
        simp only [eval_and, Bool.and_eq_true] at this
        exact this.2)
      (fun y hy => by
        obtain ⟨hyB, hyl⟩ := Finset.mem_filter.mp hy
        have := hB y hyB
        simp only [Bool.not_eq_false] at hyl
        simpa [eval_and, hyl] using this)
    rw [card_uncutEdges_split_right val A B fun y => l.eval (val y) = false,
      ← Finset.card_filter_add_card_filter_not (s := B) (fun y => l.eval (val y) = false)]
    simp only [inputLeaves]
    exact sq_add_le_of_sq_le hl hr
  | .or l r, A, B, hA, hB => by
    have hl := Formula.sq_card_uncutEdges_le val hval l
      (A.filter fun x => l.eval (val x) = true) B
      (fun x hx => (Finset.mem_filter.mp hx).2)
      (fun y hy => by
        have := hB y hy
        simp only [eval_or, Bool.or_eq_false_iff] at this
        exact this.1)
    have hr := Formula.sq_card_uncutEdges_le val hval r
      (A.filter fun x => ¬ l.eval (val x) = true) B
      (fun x hx => by
        obtain ⟨hxA, hxl⟩ := Finset.mem_filter.mp hx
        have := hA x hxA
        simp only [Bool.not_eq_true] at hxl
        simpa [eval_or, hxl] using this)
      (fun y hy => by
        have := hB y hy
        simp only [eval_or, Bool.or_eq_false_iff] at this
        exact this.2)
    have key := sq_add_le_of_sq_le (a := B.card)
      (b₁ := (A.filter fun x => l.eval (val x) = true).card)
      (b₂ := (A.filter fun x => ¬ l.eval (val x) = true).card)
      (by simpa only [Nat.mul_right_comm] using hl) (by simpa only [Nat.mul_right_comm] using hr)
    rw [card_uncutEdges_split_left val A B fun x => l.eval (val x) = true,
      ← Finset.card_filter_add_card_filter_not (s := A) (fun x => l.eval (val x) = true)]
    simp only [inputLeaves]
    calc _ ≤ _ := key
      _ = (l.inputLeaves n + r.inputLeaves n) * ((A.filter fun x => l.eval (val x) = true).card +
          (A.filter fun x => ¬ l.eval (val x) = true).card) * B.card := by ring

namespace SharedProgram

/-- **Khrapchenko's theorem for programs, with shared variables.** Let `val` extend each input
by further variables, keeping the first `n` variables equal to the input. If a program `P` with
`k` shared gates over the extended variables is `1` on `val '' A` and `0` on `val '' B`, the
edges of `A × B` that agree on the extra variables satisfy
`|uncut edges|² ≤ (k + 1) · X · |A| · |B|`, where `X` counts the literal leaves on the first
`n` variables. -/
theorem sq_card_uncutEdges_le :
    ∀ {N k : Nat} (P : SharedProgram N k) (val : (Fin n → Bool) → Fin N → Bool), n ≤ N →
      (∀ x (i : Fin N) (hi : i.val < n), val x i = x ⟨i.val, hi⟩) →
      ∀ A B : Finset (Fin n → Bool), (∀ x ∈ A, P.eval (val x) = true) →
      (∀ y ∈ B, P.eval (val y) = false) →
      (uncutEdges val A B).card ^ 2 ≤ (k + 1) * P.inputLeaves n * A.card * B.card
  | _, _, output F, val, _, hval, A, B, hA, hB => by
    simpa [inputLeaves] using F.sq_card_uncutEdges_le val hval A B hA hB
  | N, k + 1, share G P, val, hn, hval, A, B, hA, hB => by
    let val' : (Fin n → Bool) → Fin (N + 1) → Bool := fun x => Fin.snoc (val x) (G.eval (val x))
    have hval' : ∀ x (i : Fin (N + 1)) (hi : i.val < n), val' x i = x ⟨i.val, hi⟩ := by
      intro x i hi
      obtain ⟨j, rfl⟩ : ∃ j : Fin N, Fin.castSucc j = i := ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
      simp only [val', Fin.snoc_castSucc]
      exact hval x j hi
    have ih := sq_card_uncutEdges_le P val' (by omega) hval' A B hA hB
    set A₁ := A.filter fun x => G.eval (val x) = true
    set A₀ := A.filter fun x => ¬ G.eval (val x) = true
    set B₀ := B.filter fun y => G.eval (val y) = false
    set B₁ := B.filter fun y => ¬ G.eval (val y) = false
    have h₁ := G.sq_card_uncutEdges_le val hval A₁ B₀ (fun x hx => (Finset.mem_filter.mp hx).2)
      (fun y hy => (Finset.mem_filter.mp hy).2)
    have h₀ := G.neg.sq_card_uncutEdges_le val hval A₀ B₁
      (fun x hx => by simpa using (Finset.mem_filter.mp hx).2)
      (fun y hy => by simpa using (Finset.mem_filter.mp hy).2)
    rw [Formula.inputLeaves_neg] at h₀
    have hsub : uncutEdges val A B ⊆
        uncutEdges val' A B ∪ (uncutEdges val A₁ B₀ ∪ uncutEdges val A₀ B₁) := by
      rintro ⟨x, y⟩ hxy
      rw [mem_uncutEdges] at hxy
      obtain ⟨⟨hx, hy⟩, hcard, hagree⟩ := hxy
      simp only [Finset.mem_union, mem_uncutEdges, A₁, A₀, B₀, B₁, Finset.mem_filter]
      by_cases hG : G.eval (val x) = G.eval (val y)
      · refine Or.inl ⟨⟨hx, hy⟩, hcard, fun i hi => ?_⟩
        induction i using Fin.lastCases with
        | last => simp only [val', Fin.snoc_last, hG]
        | cast j =>
          simp only [val', Fin.snoc_castSucc]
          exact hagree j (by simpa using hi)
      · right
        cases hGx : G.eval (val x) <;> rw [hGx] at hG
        · right
          have hGy : G.eval (val y) = true := by cases h : G.eval (val y) <;> simp_all
          exact ⟨⟨⟨hx, by simp⟩, ⟨hy, by simp [hGy]⟩⟩, hcard, hagree⟩
        · left
          have hGy : G.eval (val y) = false := by cases h : G.eval (val y) <;> simp_all
          exact ⟨⟨⟨hx, rfl⟩, ⟨hy, hGy⟩⟩, hcard, hagree⟩
    have hcard : (uncutEdges val A B).card ≤ (uncutEdges val' A B).card +
        ((uncutEdges val A₁ B₀).card + (uncutEdges val A₀ B₁).card) :=
      (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left (Finset.card_union_le _ _) _))
    have hA' : A₁.card + A₀.card = A.card := Finset.card_filter_add_card_filter_not _
    have hB' : B₀.card + B₁.card = B.card := Finset.card_filter_add_card_filter_not _
    have hG : ((uncutEdges val A₁ B₀).card + (uncutEdges val A₀ B₁).card) ^ 2 ≤
        1 * (G.inputLeaves n * A.card * B.card) := by
      have := sq_add_le_add_mul_add (p := G.inputLeaves n * A₁.card) (q := B₀.card)
        (r := G.inputLeaves n * A₀.card) (s := B₁.card) h₁ h₀
      calc _ ≤ _ := this
        _ = 1 * (G.inputLeaves n * A.card * B.card) := by rw [← hA', ← hB']; ring
    have hP : (uncutEdges val' A B).card ^ 2 ≤ (k + 1) * (P.inputLeaves n * A.card * B.card) := by
      simpa only [mul_assoc] using ih
    have hsum := sq_add_le_add_mul_add hP hG
    calc (uncutEdges val A B).card ^ 2
        ≤ ((uncutEdges val' A B).card +
            ((uncutEdges val A₁ B₀).card + (uncutEdges val A₀ B₁).card)) ^ 2 :=
          Nat.pow_le_pow_left hcard 2
      _ ≤ (k + 1 + 1) * (P.inputLeaves n * A.card * B.card + G.inputLeaves n * A.card * B.card) :=
          hsum
      _ = (k + 1 + 1) * (share G P).inputLeaves n * A.card * B.card := by
          simp only [inputLeaves]
          ring

/-- **Khrapchenko's theorem for circuits with `k` shared gates.** If a program with `k` shared
gates is `1` on `A` and `0` on `B`, then `|edges A B|² ≤ (k + 1) · X · |A| · |B|`, where `X`
is the number of literal leaves reading an input. -/
theorem sq_card_edges_le (P : SharedProgram n k) (A B : Finset (Fin n → Bool))
    (h : P.Separates A B) :
    (edges A B).card ^ 2 ≤ (k + 1) * P.inputLeaves n * A.card * B.card := by
  have := P.sq_card_uncutEdges_le (fun x => x) le_rfl (fun _ _ _ => rfl) A B h.1 h.2
  have huncut : uncutEdges (fun x : Fin n → Bool => x) A B = edges A B :=
    Finset.filter_true_of_mem fun _ _ i hi => absurd i.isLt (by omega)
  rwa [huncut] at this

/-- A program with `k` shared gates computing `f` bounds the Khrapchenko measure of `f` by
`(k + 1) · X`, where `X` is its number of input leaves. -/
theorem khrapchenkoBound {P : SharedProgram n k} {f : Cslib.BooleanFunction n}
    (hP : P.Computes f) : KhrapchenkoBound f ((k + 1) * P.inputLeaves n) :=
  fun A B hA hB => P.sq_card_edges_le A B
    ⟨fun x hx => (hP x).trans (hA x hx), fun y hy => (hP y).trans (hB y hy)⟩

/-! ### Parity, threshold functions, and majority -/

/-- **Parity with `k` shared gates, input leaves.** Every program with `k` shared gates
computing the parity of `n ≥ 1` bits has at least `n² / (k + 1)` literal leaves reading an
input. -/
theorem parity_sq_le_inputLeaves [NeZero n] {P : SharedProgram n k}
    (hP : P.Computes GateElimination.Xor.parity) : n ^ 2 ≤ (k + 1) * P.inputLeaves n :=
  (khrapchenkoBound hP).parity_sq_le

/-- **Parity with `k` shared gates.** Every De Morgan program with `k` shared gates computing
the parity of `n ≥ 1` bits has at least `n² / (k + 1) - (k + 1)` binary gates:
`n² ≤ (k + 1) · (gates + k + 1)`. -/
theorem parity_sq_le_gates [NeZero n] {P : SharedProgram n k}
    (hP : P.Computes GateElimination.Xor.parity) : n ^ 2 ≤ (k + 1) * (P.gates + k + 1) :=
  (parity_sq_le_inputLeaves hP).trans (Nat.mul_le_mul_left _ (P.inputLeaves_le_gates n))

/-- **Superlinear size for parity with few shared gates.** If `(k + 1) · (C + 1) ≤ n`, every
program with `k` shared gates computing the parity of `n` bits has at least `C · n` gates. -/
theorem mul_le_gates_of_parity {C : Nat} (hkn : (k + 1) * (C + 1) ≤ n) {P : SharedProgram n k}
    (hP : P.Computes GateElimination.Xor.parity) : C * n ≤ P.gates := by
  have hk : k + 1 ≤ n := le_trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos C)) hkn
  have : NeZero n := ⟨by omega⟩
  have h : (k + 1) * (n * (C + 1)) ≤ (k + 1) * (P.gates + k + 1) :=
    calc (k + 1) * (n * (C + 1)) = n * ((k + 1) * (C + 1)) := by ring
      _ ≤ n * n := Nat.mul_le_mul_left _ hkn
      _ = n ^ 2 := (sq n).symm
      _ ≤ _ := parity_sq_le_gates hP
  have h' := Nat.le_of_mul_le_mul_left h (Nat.succ_pos k)
  nlinarith

/-- **Threshold functions with `k` shared gates.** For `1 ≤ t ≤ n`, every program with `k`
shared gates computing "at least `t` of `n` inputs are one" satisfies
`t · (n + 1 - t) ≤ (k + 1) · (gates + k + 1)`. -/
theorem threshold_mul_le_gates {t : Nat} (ht : 1 ≤ t) (htn : t ≤ n) {P : SharedProgram n k}
    (hP : P.Computes (threshold t)) : (n + 1 - t) * t ≤ (k + 1) * (P.gates + k + 1) :=
  ((khrapchenkoBound hP).threshold_mul_le ht htn).trans
    (Nat.mul_le_mul_left _ (P.inputLeaves_le_gates n))

/-- **Majority with `k` shared gates.** Every program with `k` shared gates computing strict
majority of `n ≥ 1` inputs satisfies
`(n - ⌊n/2⌋) · (⌊n/2⌋ + 1) ≤ (k + 1) · (gates + k + 1)`. -/
theorem majority_mul_le_gates (hn : 1 ≤ n) {P : SharedProgram n k}
    (hP : P.Computes majority) : (n - n / 2) * (n / 2 + 1) ≤ (k + 1) * (P.gates + k + 1) :=
  ((khrapchenkoBound hP).majority_mul_le hn).trans
    (Nat.mul_le_mul_left _ (P.inputLeaves_le_gates n))

/-- **Parity needs superlinear size when `k = o(n)`.** If `k n = o(n)` and, for every `n`,
`P n` is a program with `k n` shared gates computing the parity of `n` bits, then the number
of gates of `P n` grows faster than `n`. -/
theorem isLittleO_gates_of_parity {k : ℕ → ℕ}
    (hk : (fun n => (k n : ℝ)) =o[Filter.atTop] fun n : ℕ => (n : ℝ))
    (P : (n : ℕ) → SharedProgram n (k n))
    (hP : ∀ n, (P n).Computes GateElimination.Xor.parity) :
    (fun n : ℕ => (n : ℝ)) =o[Filter.atTop] fun n => ((P n).gates : ℝ) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨C, hC⟩ := exists_nat_ge (1 / c)
  have hε : (0 : ℝ) < 1 / (2 * (C + 1)) := by positivity
  filter_upwards [hk.bound hε, Filter.eventually_ge_atTop (2 * (C + 1))] with n hkn hn
  simp only [Real.norm_natCast] at hkn ⊢
  have hkn' : 2 * (C + 1) * k n ≤ n := by
    have h : ((2 * (C + 1) * k n : ℕ) : ℝ) ≤ n :=
      calc ((2 * (C + 1) * k n : ℕ) : ℝ) = 2 * (C + 1) * (k n : ℝ) := by push_cast; ring
        _ ≤ 2 * (C + 1) * (1 / (2 * (C + 1)) * n) := by gcongr
        _ = n := by field_simp
    exact_mod_cast h
  have hgates : (C * n : ℝ) ≤ (P n).gates := by
    exact_mod_cast mul_le_gates_of_parity (C := C) (by nlinarith) (hP n)
  calc (n : ℝ) = c * (1 / c * n) := by field_simp
    _ ≤ c * (C * n) := by gcongr
    _ ≤ c * (P n).gates := by gcongr

end SharedProgram

end KW
end Algebraic
