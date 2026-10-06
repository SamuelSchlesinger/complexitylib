/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Composition
public import Complexitylib.Algebraic.LowerBound.GateElimination.Xor
public import Mathlib.Tactic.NormNum

/-!
# Khrapchenko's bound

For sets `A` of inputs where a formula is `1` and `B` of inputs where it is `0`,
let `edges A B` be the pairs in `A × B` at Hamming distance one. Khrapchenko's
theorem says that every De Morgan formula separating `A` from `B` has at least
`|edges A B|² / (|A| · |B|)` leaves (`Formula.sq_card_edges_le`, stated without
division). A literal leaf can only separate along its own coordinate, so its
edges form a partial matching, and a gate splits one side of the rectangle,
where the Cauchy–Schwarz inequality makes the measure subadditive.

If every input of a nonempty `A` has at least `s₁` neighbours in a nonempty `B` and
every input of `B` has at least `s₀` neighbours in `A`, every formula separating them
has at least `s₀ · s₁` leaves (`Formula.mul_le_leaves_of_neighbours`); taking the
one-inputs and zero-inputs of `f` gives the bound for sensitive functions
(`leaves_ge_of_sensitive`). Parity is sensitive to every coordinate everywhere, so
every De Morgan formula for parity on `n ≥ 1` bits has at least `n²` leaves
(`parity_sq_le_leaves`). The inputs of weight `k` and `k - 1` show that the threshold
function "at least `k` ones" needs `k · (n + 1 - k)` leaves for `1 ≤ k ≤ n`
(`threshold_mul_le_leaves`), so strict majority needs `((n + 1) / 2)²` leaves for odd
`n` (`majority_mul_le_leaves`).

These corollaries use only the rectangle bound `|edges A B|² ≤ M · |A| · |B|` for sets `A`
of one-inputs and `B` of zero-inputs of `f` (`KhrapchenkoBound f M`). They are proved for
every such `M` (`KhrapchenkoBound.mul_le_of_sensitive`, `KhrapchenkoBound.parity_sq_le`,
`KhrapchenkoBound.threshold_mul_le`, `KhrapchenkoBound.majority_mul_le`) and specialized to
formulas, where `M` is the number of leaves (`Formula.khrapchenkoBound`), so other models
that satisfy the rectangle bound inherit them.

Splitting the inputs in half gives formulas with exactly `4 ^ k` leaves for
parity on `2 ^ k` bits, so `formulaSize parity = n²` when `n` is a power of two
(`formulaSize_parity_two_pow`).
-/

@[expose] public section

namespace Algebraic
namespace KW

variable {n : Nat}

/-! ### The Khrapchenko measure -/

/-- The coordinates where two inputs differ. -/
def diff (x y : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i ≠ y i

/-- Pairs from `A × B` at Hamming distance one. -/
noncomputable def edges (A B : Finset (Fin n → Bool)) :
    Finset ((Fin n → Bool) × (Fin n → Bool)) :=
  (A ×ˢ B).filter fun p => (diff p.1 p.2).card = 1

/-- The input `x` with coordinate `i` flipped. -/
def flip (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)

theorem diff_flip (x : Fin n → Bool) (i : Fin n) : diff x (flip x i) = {i} := by
  ext j
  rw [Finset.mem_singleton]
  unfold diff flip
  rw [Finset.mem_filter_univ]
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

/-- An input at distance one from `x` whose difference contains `i` is `x` flipped at `i`. -/
theorem eq_flip_of_diff {x y : Fin n → Bool} {i : Fin n} (hcard : (diff x y).card = 1)
    (hi : x i ≠ y i) : y = flip x i := by
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have hij : i = j := by
    have : i ∈ diff x y := by simp [diff, hi]
    rw [hj] at this
    exact Finset.mem_singleton.mp this
  subst hij
  funext k
  by_cases hk : k = i
  · subst hk
    simp only [flip, Function.update_self]
    cases hx : x k <;> cases hy : y k <;> simp_all
  · have : k ∉ diff x y := by rw [hj]; simpa using hk
    simp only [diff, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at this
    simp [flip, Function.update_of_ne hk, this]

/-- A formula separates `A` from `B` when it is `1` on `A` and `0` on `B`. -/
def Formula.Separates (F : Formula n) (A B : Finset (Fin n → Bool)) : Prop :=
  (∀ x ∈ A, F.eval x = true) ∧ ∀ y ∈ B, F.eval y = false

/-- The arithmetic heart of Khrapchenko's bound: the measure `r² / (a · b)` is
subadditive when one side of the rectangle is split. -/
theorem sq_add_le_of_sq_le {r₁ r₂ L₁ L₂ a b₁ b₂ : Nat}
    (h₁ : r₁ ^ 2 ≤ L₁ * a * b₁) (h₂ : r₂ ^ 2 ≤ L₂ * a * b₂) :
    (r₁ + r₂) ^ 2 ≤ (L₁ + L₂) * a * (b₁ + b₂) := by
  have hprod : (r₁ * r₂) ^ 2 ≤ (L₁ * a * b₂) * (L₂ * a * b₁) := by
    calc (r₁ * r₂) ^ 2 = r₁ ^ 2 * r₂ ^ 2 := by ring
      _ ≤ (L₁ * a * b₁) * (L₂ * a * b₂) := Nat.mul_le_mul h₁ h₂
      _ = (L₁ * a * b₂) * (L₂ * a * b₁) := by ring
  have hsq : (2 * (r₁ * r₂)) ^ 2 ≤ (L₁ * a * b₂ + L₂ * a * b₁) ^ 2 := by
    have : ((2 * (r₁ * r₂)) ^ 2 : ℤ) ≤ (L₁ * a * b₂ + L₂ * a * b₁ : ℤ) ^ 2 := by
      have hprod' : ((r₁ * r₂) ^ 2 : ℤ) ≤ (L₁ * a * b₂ : ℤ) * (L₂ * a * b₁) := by
        exact_mod_cast hprod
      nlinarith [sq_nonneg ((L₁ * a * b₂ : ℤ) - L₂ * a * b₁)]
    exact_mod_cast this
  have hmid : 2 * (r₁ * r₂) ≤ L₁ * a * b₂ + L₂ * a * b₁ :=
    (Nat.pow_le_pow_iff_left two_ne_zero).mp hsq
  nlinarith

/-- Splitting the zero side of a rectangle splits its edges. -/
theorem card_edges_split_right (A B : Finset (Fin n → Bool)) (p : (Fin n → Bool) → Prop)
    [DecidablePred p] :
    (edges A B).card = (edges A (B.filter p)).card + (edges A (B.filter fun y => ¬ p y)).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext ⟨x, y⟩
    by_cases hy : p y <;> simp [edges, hy]
  · rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h₁ h₂
    simp only [edges, Finset.mem_filter, Finset.mem_product] at h₁ h₂
    exact h₂.1.2.2 h₁.1.2.2

/-- Splitting the one side of a rectangle splits its edges. -/
theorem card_edges_split_left (A B : Finset (Fin n → Bool)) (p : (Fin n → Bool) → Prop)
    [DecidablePred p] :
    (edges A B).card = (edges (A.filter p) B).card + (edges (A.filter fun x => ¬ p x) B).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext ⟨x, y⟩
    by_cases hx : p x <;> simp [edges, hx]
  · rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h₁ h₂
    simp only [edges, Finset.mem_filter, Finset.mem_product] at h₁ h₂
    exact h₂.1.1.2 h₁.1.1.2

/-- A literal separating `A` from `B` has at most `|A|` edges: each one-input has
only one candidate partner, obtained by flipping the literal's coordinate. -/
theorem card_edges_le_left_of_lit {i : Fin n} {b : Bool} {A B : Finset (Fin n → Bool)}
    (h : (Formula.lit i b).Separates A B) : (edges A B).card ≤ A.card := by
  have hsub : edges A B ⊆ A.image fun x => (x, flip x i) := by
    rintro ⟨x, y⟩ hxy
    simp only [edges, Finset.mem_filter, Finset.mem_product] at hxy
    obtain ⟨⟨hx, hy⟩, hcard⟩ := hxy
    have hxi := h.1 x hx
    have hyi := h.2 y hy
    simp only [Formula.eval_lit] at hxi hyi
    have hne : x i ≠ y i := by
      intro heq
      rw [heq] at hxi
      rw [hxi] at hyi
      exact Bool.noConfusion hyi
    exact Finset.mem_image.mpr ⟨x, hx, by rw [eq_flip_of_diff hcard hne]⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- A literal separating `A` from `B` has at most `|B|` edges. -/
theorem card_edges_le_right_of_lit {i : Fin n} {b : Bool} {A B : Finset (Fin n → Bool)}
    (h : (Formula.lit i b).Separates A B) : (edges A B).card ≤ B.card := by
  have hsub : edges A B ⊆ B.image fun y => (flip y i, y) := by
    rintro ⟨x, y⟩ hxy
    simp only [edges, Finset.mem_filter, Finset.mem_product] at hxy
    obtain ⟨⟨hx, hy⟩, hcard⟩ := hxy
    have hxi := h.1 x hx
    have hyi := h.2 y hy
    simp only [Formula.eval_lit] at hxi hyi
    have hne : y i ≠ x i := by
      intro heq
      rw [← heq] at hxi
      rw [hxi] at hyi
      exact Bool.noConfusion hyi
    have hcard' : (diff y x).card = 1 := by
      have : diff y x = diff x y := by
        ext j
        simp [diff, ne_comm]
      rw [this, hcard]
    exact Finset.mem_image.mpr ⟨y, hy, by rw [eq_flip_of_diff hcard' hne]⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- **Khrapchenko's theorem.** If a De Morgan formula `F` is `1` on `A` and `0` on
`B`, then `|edges A B|² ≤ leaves F · |A| · |B|`. -/
theorem Formula.sq_card_edges_le :
    ∀ (F : Formula n) (A B : Finset (Fin n → Bool)), F.Separates A B →
      (edges A B).card ^ 2 ≤ F.leaves * A.card * B.card
  | .lit i b, A, B, h => by
    have h₁ := card_edges_le_left_of_lit h
    have h₂ := card_edges_le_right_of_lit h
    simp only [leaves, one_mul, sq]
    exact Nat.mul_le_mul h₁ h₂
  | .const b, A, B, h => by
    have hempty : edges A B = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      rintro ⟨x, y⟩ hxy
      simp only [edges, Finset.mem_filter, Finset.mem_product] at hxy
      have hx := h.1 x hxy.1.1
      have hy := h.2 y hxy.1.2
      simp only [eval_const] at hx hy
      rw [hx] at hy
      exact Bool.noConfusion hy
    simp [hempty]
  | .and l r, A, B, h => by
    have hl := Formula.sq_card_edges_le l A (B.filter fun y => l.eval y = false)
      ⟨fun x hx => by
        have := h.1 x hx
        simp only [eval_and, Bool.and_eq_true] at this
        exact this.1,
      fun y hy => (Finset.mem_filter.mp hy).2⟩
    have hr := Formula.sq_card_edges_le r A (B.filter fun y => ¬ l.eval y = false)
      ⟨fun x hx => by
        have := h.1 x hx
        simp only [eval_and, Bool.and_eq_true] at this
        exact this.2,
      fun y hy => by
        obtain ⟨hyB, hyl⟩ := Finset.mem_filter.mp hy
        have := h.2 y hyB
        simp only [Bool.not_eq_false] at hyl
        simpa [eval_and, hyl] using this⟩
    rw [card_edges_split_right A B fun y => l.eval y = false,
      ← Finset.card_filter_add_card_filter_not (s := B) (fun y => l.eval y = false)]
    simp only [leaves]
    exact sq_add_le_of_sq_le hl hr
  | .or l r, A, B, h => by
    have hl := Formula.sq_card_edges_le l (A.filter fun x => l.eval x = true) B
      ⟨fun x hx => (Finset.mem_filter.mp hx).2,
      fun y hy => by
        have := h.2 y hy
        simp only [eval_or, Bool.or_eq_false_iff] at this
        exact this.1⟩
    have hr := Formula.sq_card_edges_le r (A.filter fun x => ¬ l.eval x = true) B
      ⟨fun x hx => by
        obtain ⟨hxA, hxl⟩ := Finset.mem_filter.mp hx
        have := h.1 x hxA
        simp only [Bool.not_eq_true] at hxl
        simpa [eval_or, hxl] using this,
      fun y hy => by
        have := h.2 y hy
        simp only [eval_or, Bool.or_eq_false_iff] at this
        exact this.2⟩
    have key := sq_add_le_of_sq_le (a := B.card)
      (b₁ := (A.filter fun x => l.eval x = true).card)
      (b₂ := (A.filter fun x => ¬ l.eval x = true).card)
      (by simpa only [Nat.mul_right_comm] using hl) (by simpa only [Nat.mul_right_comm] using hr)
    rw [card_edges_split_left A B fun x => l.eval x = true,
      ← Finset.card_filter_add_card_filter_not (s := A) (fun x => l.eval x = true)]
    simp only [leaves]
    calc _ ≤ _ := key
      _ = (l.leaves + r.leaves) * ((A.filter fun x => l.eval x = true).card +
          (A.filter fun x => ¬ l.eval x = true).card) * B.card := by ring

/-- Khrapchenko's theorem for a formula computing `f`, on the full rectangle of
one-inputs and zero-inputs. -/
theorem Formula.sq_card_edges_le_of_computes {F : Formula n} {f : Cslib.BooleanFunction n}
    (hF : F.Computes f) :
    (edges (Finset.univ.filter fun x => f x = true) (Finset.univ.filter fun y => f y = false)).card
        ^ 2 ≤
      F.leaves * (Finset.univ.filter fun x => f x = true).card *
        (Finset.univ.filter fun y => f y = false).card :=
  F.sq_card_edges_le _ _
    ⟨fun x hx => (hF x).trans (Finset.mem_filter.mp hx).2,
      fun y hy => (hF y).trans (Finset.mem_filter.mp hy).2⟩

/-- `M` bounds the Khrapchenko measure of `f`: for every set `A` of one-inputs and every
set `B` of zero-inputs of `f`, `|edges A B|² ≤ M · |A| · |B|`. A formula computing `f`
gives this bound with `M` its number of leaves (`Formula.khrapchenkoBound`); the
corollaries below depend only on this bound, not on the model of computation. -/
def KhrapchenkoBound (f : Cslib.BooleanFunction n) (M : Nat) : Prop :=
  ∀ A B : Finset (Fin n → Bool), (∀ x ∈ A, f x = true) → (∀ y ∈ B, f y = false) →
    (edges A B).card ^ 2 ≤ M * A.card * B.card

/-- Khrapchenko's theorem as a bound on the measure of the computed function. -/
theorem Formula.khrapchenkoBound {F : Formula n} {f : Cslib.BooleanFunction n}
    (hF : F.Computes f) : KhrapchenkoBound f F.leaves :=
  fun A B hA hB => F.sq_card_edges_le A B
    ⟨fun x hx => (hF x).trans (hA x hx), fun y hy => (hF y).trans (hB y hy)⟩

/-! ### Neighbour counts -/

/-- The coordinates at which flipping `x` lands in `S`. -/
def neighbours (S : Finset (Fin n → Bool)) (x : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => flip x i ∈ S

/-- Each input of `A` contributes its neighbours in `B` as edges. -/
theorem sum_card_neighbours_le_card_edges (A B : Finset (Fin n → Bool)) :
    ∑ x ∈ A, (neighbours B x).card ≤ (edges A B).card := by
  rw [← Finset.card_sigma]
  refine Finset.card_le_card_of_injOn (fun p => (p.1, flip p.1 p.2)) ?_ ?_
  · rintro ⟨x, i⟩ hp
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, neighbours,
      Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_coe, edges, Finset.mem_filter, Finset.mem_product, diff_flip,
      Finset.card_singleton, and_true]
    exact hp
  · rintro ⟨x, i⟩ _ ⟨x', i'⟩ _ heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, hflip⟩ := heq
    have : i = i' := by
      have := congrArg (fun y => diff x y) hflip
      simp only [diff_flip, Finset.singleton_inj] at this
      exact this
    subst this
    rfl

theorem diff_comm (x y : Fin n → Bool) : diff x y = diff y x := by
  ext j
  simp [diff, ne_comm]

/-- The edge count is symmetric in the two sides. -/
theorem card_edges_comm (A B : Finset (Fin n → Bool)) :
    (edges B A).card = (edges A B).card := by
  refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [edges, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, by rw [diff_comm, hp.2]⟩
  · rintro ⟨x, y⟩ _ ⟨x', y'⟩ _ h
    simp only [Prod.mk.injEq] at h
    rw [h.1, h.2]
  · rintro ⟨x, y⟩ hp
    refine ⟨(y, x), ?_, rfl⟩
    simp only [edges, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, by rw [diff_comm, hp.2]⟩

/-- **Neighbour counts against a measure bound.** If `|edges A B|² ≤ M · |A| · |B|` for
nonempty `A` and `B`, every input of `A` has at least `s₁` neighbours in `B`, and every
input of `B` has at least `s₀` neighbours in `A`, then `s₀ · s₁ ≤ M`. -/
theorem mul_le_of_neighbours {A B : Finset (Fin n → Bool)} {s₀ s₁ M : Nat}
    (hE : (edges A B).card ^ 2 ≤ M * A.card * B.card) (hA : A.Nonempty) (hB : B.Nonempty)
    (h₁ : ∀ x ∈ A, s₁ ≤ (neighbours B x).card) (h₀ : ∀ y ∈ B, s₀ ≤ (neighbours A y).card) :
    s₀ * s₁ ≤ M := by
  have hEA : s₁ * A.card ≤ (edges A B).card := by
    refine le_trans ?_ (sum_card_neighbours_le_card_edges A B)
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum h₁
  have hEB : s₀ * B.card ≤ (edges A B).card := by
    refine le_trans ?_ ((sum_card_neighbours_le_card_edges B A).trans
      (card_edges_comm A B).le)
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum h₀
  have hprod : (s₀ * s₁) * (A.card * B.card) ≤ M * (A.card * B.card) := by
    calc (s₀ * s₁) * (A.card * B.card) = (s₁ * A.card) * (s₀ * B.card) := by ring
      _ ≤ (edges A B).card * (edges A B).card := Nat.mul_le_mul hEA hEB
      _ = (edges A B).card ^ 2 := (sq _).symm
      _ ≤ M * A.card * B.card := hE
      _ = M * (A.card * B.card) := by ring
  exact Nat.le_of_mul_le_mul_right hprod (Nat.mul_pos hA.card_pos hB.card_pos)

/-- **Khrapchenko's bound from neighbour counts.** If a formula separates nonempty
`A` from nonempty `B`, every input of `A` has at least `s₁` neighbours in `B`, and
every input of `B` has at least `s₀` neighbours in `A`, the formula has at least
`s₀ · s₁` leaves. -/
theorem Formula.mul_le_leaves_of_neighbours {F : Formula n} {A B : Finset (Fin n → Bool)}
    {s₀ s₁ : Nat} (hF : F.Separates A B) (hA : A.Nonempty) (hB : B.Nonempty)
    (h₁ : ∀ x ∈ A, s₁ ≤ (neighbours B x).card) (h₀ : ∀ y ∈ B, s₀ ≤ (neighbours A y).card) :
    s₀ * s₁ ≤ F.leaves :=
  mul_le_of_neighbours (F.sq_card_edges_le A B hF) hA hB h₁ h₀

/-! ### Sensitive functions -/

/-- The coordinates of `x` at which flipping changes `f`. -/
def sensitiveCoordinates (f : Cslib.BooleanFunction n) (x : Fin n → Bool) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => f (flip x i) ≠ f x

/-- **Sensitivity against a measure bound.** If every one-input of `f` is sensitive on at
least `s₁` coordinates, every zero-input on at least `s₀`, and `f` takes both values, then
every bound `M` on the Khrapchenko measure of `f` satisfies `s₀ · s₁ ≤ M`. -/
theorem KhrapchenkoBound.mul_le_of_sensitive {f : Cslib.BooleanFunction n} {s₀ s₁ M : Nat}
    (hM : KhrapchenkoBound f M) (hone : ∃ x, f x = true) (hzero : ∃ y, f y = false)
    (h₁ : ∀ x, f x = true → s₁ ≤ (sensitiveCoordinates f x).card)
    (h₀ : ∀ y, f y = false → s₀ ≤ (sensitiveCoordinates f y).card) : s₀ * s₁ ≤ M := by
  have hsens : ∀ b x, f x = b →
      sensitiveCoordinates f x = neighbours (Finset.univ.filter fun y => f y = !b) x := by
    intro b x hx
    ext i
    simp only [sensitiveCoordinates, neighbours, Finset.mem_filter, Finset.mem_univ, true_and,
      hx]
    cases b <;> cases f (flip x i) <;> simp
  refine mul_le_of_neighbours (A := Finset.univ.filter fun x => f x = true)
    (B := Finset.univ.filter fun y => f y = false)
    (hM _ _ (fun x hx => (Finset.mem_filter.mp hx).2) fun y hy => (Finset.mem_filter.mp hy).2)
    (by obtain ⟨x, hx⟩ := hone; exact ⟨x, by simp [hx]⟩)
    (by obtain ⟨y, hy⟩ := hzero; exact ⟨y, by simp [hy]⟩)
    (fun x hx => ?_) (fun y hy => ?_)
  · have hx' := (Finset.mem_filter.mp hx).2
    simpa only [hsens true x hx', Bool.not_true] using h₁ x hx'
  · have hy' := (Finset.mem_filter.mp hy).2
    simpa only [hsens false y hy', Bool.not_false] using h₀ y hy'

/-- **Khrapchenko's bound for sensitive functions.** If every one-input of `f` is
sensitive on at least `s₁` coordinates, every zero-input on at least `s₀`, and `f`
takes both values, every De Morgan formula for `f` has at least `s₀ · s₁` leaves. -/
theorem leaves_ge_of_sensitive {f : Cslib.BooleanFunction n} {s₀ s₁ : Nat}
    (hone : ∃ x, f x = true) (hzero : ∃ y, f y = false)
    (h₁ : ∀ x, f x = true → s₁ ≤ (sensitiveCoordinates f x).card)
    (h₀ : ∀ y, f y = false → s₀ ≤ (sensitiveCoordinates f y).card)
    {F : Formula n} (hF : F.Computes f) : s₀ * s₁ ≤ F.leaves :=
  (Formula.khrapchenkoBound hF).mul_le_of_sensitive hone hzero h₁ h₀

/-! ### Parity -/

open GateElimination.Xor in
theorem parity_flip (x : Fin n → Bool) (i : Fin n) : parity (flip x i) = !parity x := by
  unfold parity flip
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self,
    Finset.sum_congr rfl fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) _ x]
  cases x i <;> cases (∑ j ∈ Finset.univ.erase i, x j) <;> decide

open GateElimination.Xor in
theorem sensitiveCoordinates_parity (x : Fin n → Bool) :
    sensitiveCoordinates parity x = Finset.univ := by
  ext i
  simp [sensitiveCoordinates, parity_flip]

/-- **Parity against a measure bound.** Every bound on the Khrapchenko measure of the
parity of `n ≥ 1` bits is at least `n²`. -/
theorem KhrapchenkoBound.parity_sq_le [NeZero n] {M : Nat}
    (hM : KhrapchenkoBound (GateElimination.Xor.parity (n := n)) M) : n ^ 2 ≤ M := by
  have hzero : GateElimination.Xor.parity (fun _ : Fin n => false) = false :=
    Finset.sum_eq_zero fun _ _ => rfl
  have hone : GateElimination.Xor.parity (flip (fun _ : Fin n => false) 0) = true := by
    rw [parity_flip, hzero]; rfl
  have := hM.mul_le_of_sensitive (s₀ := n) (s₁ := n) ⟨_, hone⟩ ⟨_, hzero⟩
    (fun x _ => by simp [sensitiveCoordinates_parity])
    (fun y _ => by simp [sensitiveCoordinates_parity])
  simpa [sq] using this

/-- **Khrapchenko's bound for parity.** Every De Morgan formula computing the
parity of `n ≥ 1` bits has at least `n²` leaves. -/
theorem parity_sq_le_leaves [NeZero n] {F : Formula n}
    (hF : F.Computes GateElimination.Xor.parity) : n ^ 2 ≤ F.leaves :=
  (Formula.khrapchenkoBound hF).parity_sq_le

theorem le_formulaSize_parity [NeZero n] :
    ((n ^ 2 : Nat) : ℕ∞) ≤ formulaSize (GateElimination.Xor.parity (n := n)) :=
  le_iInf fun F => by exact_mod_cast parity_sq_le_leaves F.2

/-! ### Threshold functions -/

/-- The number of ones in an input. -/
def weight (x : Fin n → Bool) : Nat :=
  (Finset.univ.filter fun i => x i = true).card

/-- The threshold function: at least `k` of the inputs are one. -/
def threshold (k : Nat) : Cslib.BooleanFunction n :=
  fun x => decide (k ≤ weight x)

/-- Strict majority: more than half of the inputs are one (ties are `false`). -/
def majority : Cslib.BooleanFunction n :=
  threshold (n / 2 + 1)

theorem weight_flip_of_true {x : Fin n → Bool} {i : Fin n} (hi : x i = true) :
    weight (flip x i) + 1 = weight x := by
  unfold weight
  have hsplit : (Finset.univ.filter fun j => x j = true) =
      insert i (Finset.univ.filter fun j => flip x i j = true) := by
    ext j
    rw [Finset.mem_insert, Finset.mem_filter_univ, Finset.mem_filter_univ]
    by_cases hj : j = i
    · subst hj; simp [hi]
    · simp [flip, hj]
  rw [hsplit, Finset.card_insert_of_notMem (by simp [flip, hi])]

theorem weight_flip_of_false {x : Fin n → Bool} {i : Fin n} (hi : x i = false) :
    weight (flip x i) = weight x + 1 := by
  have hflip : flip (flip x i) i = x := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [flip]
    · simp [flip, Function.update_of_ne hj]
  have := weight_flip_of_true (x := flip x i) (i := i) (by simp [flip, hi])
  rw [hflip] at this
  omega

/-- An input whose first `k` coordinates are one and the rest zero. -/
def prefixOnes (k : Nat) : Fin n → Bool :=
  fun i => decide (i.val < k)

theorem weight_prefixOnes {k : Nat} (hk : k ≤ n) : weight (prefixOnes (n := n) k) = k := by
  unfold weight prefixOnes
  simp only [decide_eq_true_eq]
  rw [Fin.card_filter_val_lt]
  omega

/-- **Threshold functions against a measure bound.** For `1 ≤ k ≤ n`, every bound on the
Khrapchenko measure of "at least `k` of `n` inputs are one" is at least `k · (n + 1 - k)`:
the inputs of weight `k` and `k - 1` form the rectangle. -/
theorem KhrapchenkoBound.threshold_mul_le {k M : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hM : KhrapchenkoBound (threshold (n := n) k) M) : (n + 1 - k) * k ≤ M := by
  set A := Finset.univ.filter fun x : Fin n → Bool => weight x = k
  set B := Finset.univ.filter fun y : Fin n → Bool => weight y = k - 1
  refine mul_le_of_neighbours (A := A) (B := B)
    (hM A B (fun x hx => by
      simp only [threshold, (Finset.mem_filter.mp hx).2, le_refl, decide_true])
      fun y hy => by
        simp only [threshold, (Finset.mem_filter.mp hy).2, decide_eq_false_iff_not]
        omega)
    ⟨prefixOnes k, by simp [A, weight_prefixOnes hkn]⟩
    ⟨prefixOnes (k - 1), by simp [B, weight_prefixOnes (by omega : k - 1 ≤ n)]⟩
    (fun x hx => ?_) (fun y hy => ?_)
  · have hx' : weight x = k := (Finset.mem_filter.mp hx).2
    refine le_of_eq (hx'.symm.trans ?_)
    unfold weight
    congr 1
    ext i
    simp only [neighbours, Finset.mem_filter, Finset.mem_univ, true_and, B]
    constructor
    · intro hi
      have := weight_flip_of_true hi
      omega
    · intro hi
      cases hxi : x i
      · have := weight_flip_of_false hxi
        omega
      · rfl
  · have hy' : weight y = k - 1 := (Finset.mem_filter.mp hy).2
    have hcompl : (Finset.univ.filter fun i => y i = false).card = n - weight y := by
      have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun i : Fin n => y i = true)
      simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at h
      unfold weight
      omega
    have hle : weight y ≤ n := by
      unfold weight
      exact (Finset.card_filter_le _ _).trans (by simp)
    refine le_of_eq (Eq.trans (by omega : n + 1 - k = n - weight y) (hcompl.symm.trans ?_))
    congr 1
    ext i
    simp only [neighbours, Finset.mem_filter, Finset.mem_univ, true_and, A]
    constructor
    · intro hi
      have := weight_flip_of_false hi
      omega
    · intro hi
      cases hyi : y i
      · rfl
      · have := weight_flip_of_true hyi
        omega

/-- **Khrapchenko's bound for threshold functions.** For `1 ≤ k ≤ n`, every De Morgan
formula computing "at least `k` of `n` inputs are one" has at least `k · (n + 1 - k)`
leaves: the inputs of weight `k` and `k - 1` form the rectangle. -/
theorem threshold_mul_le_leaves {k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) {F : Formula n}
    (hF : F.Computes (threshold k)) : (n + 1 - k) * k ≤ F.leaves :=
  (Formula.khrapchenkoBound hF).threshold_mul_le hk hkn

/-- **Majority against a measure bound.** For `n ≥ 1`, every bound on the Khrapchenko
measure of strict majority of `n` inputs is at least `(n - ⌊n/2⌋) · (⌊n/2⌋ + 1)`. -/
theorem KhrapchenkoBound.majority_mul_le {M : Nat} (hn : 1 ≤ n)
    (hM : KhrapchenkoBound (majority (n := n)) M) : (n - n / 2) * (n / 2 + 1) ≤ M := by
  have := KhrapchenkoBound.threshold_mul_le (k := n / 2 + 1) (by omega) (by omega) hM
  rwa [show n + 1 - (n / 2 + 1) = n - n / 2 by omega] at this

/-- **Khrapchenko's bound for majority.** Every De Morgan formula computing strict
majority of `n ≥ 1` inputs has at least `(n - ⌊n/2⌋) · (⌊n/2⌋ + 1)` leaves, which is
`((n + 1)/2)²` for odd `n`. -/
theorem majority_mul_le_leaves (hn : 1 ≤ n) {F : Formula n} (hF : F.Computes majority) :
    (n - n / 2) * (n / 2 + 1) ≤ F.leaves :=
  (Formula.khrapchenkoBound hF).majority_mul_le hn

/-! ### A matching upper bound at powers of two -/

open GateElimination.Xor in
theorem parity_append {a b : Nat} (x : Fin (a + b) → Bool) :
    parity x = (parity (x ∘ Fin.castAdd b) ^^ parity (x ∘ Fin.natAdd a)) := by
  unfold parity
  rw [Fin.sum_univ_add]
  rfl

/-- The formula `(L ∧ ¬R) ∨ (¬L ∧ R)` for the exclusive or of two formulas. -/
def Formula.xor (L R : Formula n) : Formula n :=
  .or (.and L R.neg) (.and L.neg R)

@[simp] theorem Formula.eval_xor (L R : Formula n) (x : Fin n → Bool) :
    (L.xor R).eval x = (L.eval x ^^ R.eval x) := by
  simp only [xor, eval_or, eval_and, eval_neg]
  cases L.eval x <;> cases R.eval x <;> rfl

@[simp] theorem Formula.leaves_xor (L R : Formula n) :
    (L.xor R).leaves = 2 * (L.leaves + R.leaves) := by
  simp only [xor, leaves, leaves_neg]
  ring

/-- Parity on `2 ^ k` bits as a balanced formula with `4 ^ k` leaves. -/
def parityFormula : (k : Nat) → Formula (2 ^ k)
  | 0 => .lit 0 true
  | k + 1 =>
    ((parityFormula k).mapIndex (Fin.castAdd (2 ^ k))).xor
        ((parityFormula k).mapIndex (Fin.natAdd (2 ^ k))) |>.mapIndex
      (Fin.cast (by rw [pow_succ, mul_two]))

theorem parityFormula_computes :
    ∀ k : Nat, (parityFormula k).Computes GateElimination.Xor.parity
  | 0 => fun x => by
    have hzero : ∀ c : Fin (2 ^ 0), c = 0 := fun c => Fin.ext (by
      have := c.isLt
      simp only [pow_zero] at this
      simp only [Fin.coe_ofNat_eq_mod, pow_zero, Nat.zero_mod]
      omega)
    simp only [parityFormula, Formula.eval_lit, GateElimination.Xor.parity]
    rw [Finset.sum_eq_single (0 : Fin (2 ^ 0)) (fun c _ hc => absurd (hzero c) hc)
      (fun h => absurd (Finset.mem_univ _) h)]
    cases x 0 <;> rfl
  | k + 1 => fun x => by
    have ih := parityFormula_computes k
    have hcast : (2 ^ k + 2 ^ k) = 2 ^ (k + 1) := by rw [pow_succ, mul_two]
    simp only [parityFormula, Formula.eval_mapIndex, Formula.eval_xor]
    rw [ih, ih, ← parity_append (x ∘ Fin.cast hcast)]
    unfold GateElimination.Xor.parity
    exact Fintype.sum_equiv (finCongr hcast) _ _ fun _ => rfl

theorem leaves_parityFormula : ∀ k : Nat, (parityFormula k).leaves = 4 ^ k
  | 0 => rfl
  | k + 1 => by
    simp only [parityFormula, Formula.leaves_mapIndex, Formula.leaves_xor,
      leaves_parityFormula k, pow_succ]
    ring

/-- **Formula size of parity.** At `n = 2 ^ k` bits the minimum number of leaves
of a De Morgan formula computing parity is exactly `n²`. -/
theorem formulaSize_parity_two_pow (k : Nat) :
    formulaSize (GateElimination.Xor.parity (n := 2 ^ k)) = ((2 ^ k) ^ 2 : Nat) := by
  have : NeZero (2 ^ k) := ⟨by positivity⟩
  refine le_antisymm ?_ le_formulaSize_parity
  refine (formulaSize_le (parityFormula_computes k)).trans ?_
  rw [leaves_parityFormula, ← pow_mul, mul_comm, pow_mul]
  norm_num

end KW
end Algebraic
