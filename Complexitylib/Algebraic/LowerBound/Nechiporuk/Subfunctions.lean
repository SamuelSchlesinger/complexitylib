/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Binary.Formula
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Rectangle
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# Subfunctions of formulas and of rectangle-free functions

The *subfunctions* of `f` on a block `Y` of coordinates are the functions of
the coordinates in `Y` obtained by fixing the coordinates outside `Y`.

Nechiporuk's lemma bounds their number for a formula: fixing the outside
coordinates turns every leaf outside `Y` into a constant, which then collapses
the adjacent gate into one of the four unary functions of its other input.
Since unary functions are closed under composition, a formula with `l` leaves
in `Y` has at most `4 ^ (2 l - 1)` subfunctions on `Y` up to unary
post-composition (`card_unaryClosure_subfunctions_le`), hence at most
`2 · 16 ^ l` subfunctions.

A rectangle-free function has many subfunctions on every block: grouping the
outside assignments by the subfunction they induce gives one-rectangles, so
every class is small or its subfunction accepts few inputs, and the count of
accepting inputs forces at least `2 ^ |Yᶜ| / (8 K)` classes
(`two_pow_card_compl_le`).
-/

@[expose] public section

namespace Algebraic
namespace Nechiporuk

open scoped Classical
open Binary Cutwidth

variable {n : Nat}

/-- The subfunctions of `f` on the block `Y`: fix the coordinates outside `Y`. -/
noncomputable def subfunctions (f : Cslib.BooleanFunction n) (Y : Finset (Fin n)) :
    Finset ((↥Y → Bool) → Bool) :=
  Finset.univ.image fun z : ↥Yᶜ → Bool => fun y => f (glue Y y z)

theorem mem_subfunctions {f : Cslib.BooleanFunction n} {Y : Finset (Fin n)}
    {g : (↥Y → Bool) → Bool} :
    g ∈ subfunctions f Y ↔ ∃ z : ↥Yᶜ → Bool, (fun y => f (glue Y y z)) = g := by
  simp [subfunctions]

theorem restrict_mem_subfunctions (f : Cslib.BooleanFunction n) (Y : Finset (Fin n))
    (z : ↥Yᶜ → Bool) : (fun y => f (glue Y y z)) ∈ subfunctions f Y :=
  Finset.mem_image_of_mem _ (Finset.mem_univ z)

/-! ### Closure under unary post-composition -/

variable {Y : Finset (Fin n)}

/-- Compositions of the functions in `S` with the four unary Boolean functions. -/
noncomputable def unaryClosure (S : Finset ((↥Y → Bool) → Bool)) : Finset ((↥Y → Bool) → Bool) :=
  (Finset.univ ×ˢ S).image fun p : (Bool → Bool) × ((↥Y → Bool) → Bool) => p.1 ∘ p.2

theorem mem_unaryClosure {S : Finset ((↥Y → Bool) → Bool)} {g : (↥Y → Bool) → Bool} :
    g ∈ unaryClosure S ↔ ∃ u : Bool → Bool, ∃ h ∈ S, u ∘ h = g := by
  constructor
  · intro hg
    obtain ⟨⟨u, h⟩, hp, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨u, h, (Finset.mem_product.mp hp).2, rfl⟩
  · rintro ⟨u, h, hh, rfl⟩
    exact Finset.mem_image.mpr ⟨(u, h), Finset.mem_product.mpr ⟨Finset.mem_univ _, hh⟩, rfl⟩

theorem subset_unaryClosure (S : Finset ((↥Y → Bool) → Bool)) : S ⊆ unaryClosure S :=
  fun g hg => mem_unaryClosure.mpr ⟨id, g, hg, rfl⟩

theorem unaryClosure_mono {S T : Finset ((↥Y → Bool) → Bool)} (h : S ⊆ T) :
    unaryClosure S ⊆ unaryClosure T := by
  intro g hg
  obtain ⟨u, k, hk, rfl⟩ := mem_unaryClosure.mp hg
  exact mem_unaryClosure.mpr ⟨u, k, h hk, rfl⟩

/-- Unary functions compose, so the closure is idempotent. -/
theorem unaryClosure_unaryClosure (S : Finset ((↥Y → Bool) → Bool)) :
    unaryClosure (unaryClosure S) ⊆ unaryClosure S := by
  intro g hg
  obtain ⟨u, k, hk, rfl⟩ := mem_unaryClosure.mp hg
  obtain ⟨v, k', hk', rfl⟩ := mem_unaryClosure.mp hk
  exact mem_unaryClosure.mpr ⟨u ∘ v, k', hk', rfl⟩

theorem card_unaryClosure_le (S : Finset ((↥Y → Bool) → Bool)) :
    (unaryClosure S).card ≤ 4 * S.card := by
  calc (unaryClosure S).card ≤ (Finset.univ ×ˢ S).card := Finset.card_image_le
    _ = 4 * S.card := by
        rw [Finset.card_product, Finset.card_univ]
        simp [Fintype.card_bool]

/-- Unary compositions of constant functions are constant, so there are at most two. -/
theorem card_unaryClosure_le_two {S : Finset ((↥Y → Bool) → Bool)}
    (h : ∀ g ∈ S, ∃ c, ∀ y, g y = c) : (unaryClosure S).card ≤ 2 := by
  calc (unaryClosure S).card
      ≤ ({fun _ => false, fun _ => true} : Finset ((↥Y → Bool) → Bool)).card := by
        apply Finset.card_le_card
        intro g hg
        obtain ⟨u, k, hk, rfl⟩ := mem_unaryClosure.mp hg
        obtain ⟨c, hc⟩ := h k hk
        have : u ∘ k = fun _ => u c := by
          funext y
          simp [Function.comp, hc y]
        rw [this]
        cases u c <;> simp
    _ ≤ 2 := Finset.card_le_two

/-! ### Nechiporuk's counting lemma -/

/-- The bound on the unary closure of the subfunctions of a formula with `l`
leaves in the block: `2` for `l = 0` and `4 ^ (2 l - 1)` otherwise. -/
def bound : Nat → Nat
  | 0 => 2
  | l + 1 => 4 ^ (2 * l + 1)

theorem bound_le (l : Nat) : bound l ≤ 2 * 16 ^ l := by
  cases l with
  | zero => simp [bound]
  | succ l =>
    show 4 ^ (2 * l + 1) ≤ 2 * 16 ^ (l + 1)
    calc 4 ^ (2 * l + 1) ≤ 4 ^ (2 * (l + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 16 ^ (l + 1) := by rw [pow_mul]; norm_num
      _ ≤ 2 * 16 ^ (l + 1) := by omega

theorem four_mul_bound_mul_bound (a b : Nat) :
    4 * bound (a + 1) * bound (b + 1) = bound (a + 1 + (b + 1)) := by
  show 4 * 4 ^ (2 * a + 1) * 4 ^ (2 * b + 1) = 4 ^ (2 * (a + 1 + b) + 1)
  rw [← pow_succ', ← pow_add]
  congr 1
  ring

/-- Nechiporuk's lemma: up to unary post-composition, a formula with `l`
leaves in `Y` has at most `bound l` subfunctions on `Y`. -/
theorem card_unaryClosure_subfunctions_le (Y : Finset (Fin n)) :
    ∀ F : Formula n, (unaryClosure (subfunctions F.eval Y)).card ≤ bound (F.leavesIn Y)
  | .var i => by
    by_cases hi : i ∈ Y
    · simp only [Formula.leavesIn_var, hi, ↓reduceIte]
      have hsub : subfunctions (Formula.var i).eval Y ⊆ {fun y : ↥Y → Bool => y ⟨i, hi⟩} := by
        intro g hg
        obtain ⟨z, rfl⟩ := mem_subfunctions.mp hg
        rw [Finset.mem_singleton]
        funext y
        simp [glue, hi]
      calc (unaryClosure (subfunctions (Formula.var i).eval Y)).card
          ≤ 4 * (subfunctions (Formula.var i).eval Y).card := card_unaryClosure_le _
        _ ≤ 4 * 1 := by
            have := Finset.card_le_card hsub
            rw [Finset.card_singleton] at this
            omega
        _ = bound 1 := by simp [bound]
    · simp only [Formula.leavesIn_var, hi, ↓reduceIte]
      apply card_unaryClosure_le_two
      intro g hg
      obtain ⟨z, rfl⟩ := mem_subfunctions.mp hg
      refine ⟨z ⟨i, Finset.mem_compl.mpr hi⟩, fun y => ?_⟩
      simp [glue, hi]
  | .const b => by
    rw [Formula.leavesIn_const]
    apply card_unaryClosure_le_two
    intro g hg
    obtain ⟨z, rfl⟩ := mem_subfunctions.mp hg
    exact ⟨b, fun _ => rfl⟩
  | .gate op left right => by
    rw [Formula.leavesIn_gate]
    have ihl := card_unaryClosure_subfunctions_le Y left
    have ihr := card_unaryClosure_subfunctions_le Y right
    -- Assignments differing only inside `Y` agree outside `Y`.
    have agree : ∀ (y : ↥Y → Bool) (z : ↥Yᶜ → Bool), ∀ i, i ∉ Y →
        glue Y y z i = glue Y (fun _ => false) z i := by
      intro y z i hi
      simp [glue, hi]
    rcases Nat.eq_zero_or_pos (right.leavesIn Y) with hr | hr
    · -- The right subformula is constant on every fiber.
      have hsub : subfunctions (Formula.gate op left right).eval Y ⊆
          unaryClosure (subfunctions left.eval Y) := by
        intro g hg
        obtain ⟨z, rfl⟩ := mem_subfunctions.mp hg
        refine mem_unaryClosure.mpr ⟨fun v => op v (right.eval (glue Y (fun _ => false) z)), _,
          restrict_mem_subfunctions left.eval Y z, ?_⟩
        funext y
        simp only [Function.comp, Formula.eval_gate]
        rw [Formula.eval_eq_of_leavesIn_eq_zero (agree y z) right hr]
      calc (unaryClosure (subfunctions (Formula.gate op left right).eval Y)).card
          ≤ (unaryClosure (unaryClosure (subfunctions left.eval Y))).card :=
            Finset.card_le_card (unaryClosure_mono hsub)
        _ ≤ (unaryClosure (subfunctions left.eval Y)).card :=
            Finset.card_le_card (unaryClosure_unaryClosure _)
        _ ≤ bound (left.leavesIn Y) := ihl
        _ = bound (left.leavesIn Y + right.leavesIn Y) := by rw [hr, Nat.add_zero]
    rcases Nat.eq_zero_or_pos (left.leavesIn Y) with hl | hl
    · -- The left subformula is constant on every fiber.
      have hsub : subfunctions (Formula.gate op left right).eval Y ⊆
          unaryClosure (subfunctions right.eval Y) := by
        intro g hg
        obtain ⟨z, rfl⟩ := mem_subfunctions.mp hg
        refine mem_unaryClosure.mpr ⟨fun v => op (left.eval (glue Y (fun _ => false) z)) v, _,
          restrict_mem_subfunctions right.eval Y z, ?_⟩
        funext y
        simp only [Function.comp, Formula.eval_gate]
        rw [Formula.eval_eq_of_leavesIn_eq_zero (agree y z) left hl]
      calc (unaryClosure (subfunctions (Formula.gate op left right).eval Y)).card
          ≤ (unaryClosure (unaryClosure (subfunctions right.eval Y))).card :=
            Finset.card_le_card (unaryClosure_mono hsub)
        _ ≤ (unaryClosure (subfunctions right.eval Y)).card :=
            Finset.card_le_card (unaryClosure_unaryClosure _)
        _ ≤ bound (right.leavesIn Y) := ihr
        _ = bound (left.leavesIn Y + right.leavesIn Y) := by rw [hl, Nat.zero_add]
    -- Both subformulas read the block: subfunctions combine pairwise.
    obtain ⟨a, ha⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.pos_iff_ne_zero.mp hl)
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.pos_iff_ne_zero.mp hr)
    have hsub : subfunctions (Formula.gate op left right).eval Y ⊆
        (subfunctions left.eval Y ×ˢ subfunctions right.eval Y).image
          fun p : ((↥Y → Bool) → Bool) × ((↥Y → Bool) → Bool) => fun y => op (p.1 y) (p.2 y) := by
      intro g hg
      obtain ⟨z, rfl⟩ := mem_subfunctions.mp hg
      exact Finset.mem_image.mpr ⟨(fun y => left.eval (glue Y y z), fun y => right.eval (glue Y y z)),
        Finset.mem_product.mpr ⟨restrict_mem_subfunctions _ _ _, restrict_mem_subfunctions _ _ _⟩,
        rfl⟩
    calc (unaryClosure (subfunctions (Formula.gate op left right).eval Y)).card
        ≤ 4 * (subfunctions (Formula.gate op left right).eval Y).card := card_unaryClosure_le _
      _ ≤ 4 * ((subfunctions left.eval Y).card * (subfunctions right.eval Y).card) := by
          apply Nat.mul_le_mul_left
          rw [← Finset.card_product]
          exact (Finset.card_le_card hsub).trans Finset.card_image_le
      _ ≤ 4 * (bound (left.leavesIn Y) * bound (right.leavesIn Y)) := by
          apply Nat.mul_le_mul_left
          apply Nat.mul_le_mul
          · exact (Finset.card_le_card (subset_unaryClosure _)).trans ihl
          · exact (Finset.card_le_card (subset_unaryClosure _)).trans ihr
      _ = bound (left.leavesIn Y + right.leavesIn Y) := by
          rw [ha, hb, ← mul_assoc, four_mul_bound_mul_bound]

/-- A formula with `l` leaves in `Y` has at most `2 · 16 ^ l` subfunctions on `Y`. -/
theorem card_subfunctions_le (Y : Finset (Fin n)) (F : Formula n) :
    (subfunctions F.eval Y).card ≤ 2 * 16 ^ F.leavesIn Y :=
  ((Finset.card_le_card (subset_unaryClosure _)).trans
    (card_unaryClosure_subfunctions_le Y F)).trans (bound_le _)

/-! ### Rectangle-free functions have many subfunctions -/

/-- The number of inputs on which a function of the block is `1`. -/
noncomputable def ones (g : (↥Y → Bool) → Bool) : Nat :=
  (Finset.univ.filter fun y => g y = true).card

theorem ones_le (g : (↥Y → Bool) → Bool) : ones g ≤ 2 ^ Y.card := by
  unfold ones
  calc (Finset.univ.filter fun y => g y = true).card
      ≤ (Finset.univ : Finset (↥Y → Bool)).card := Finset.card_le_univ _
    _ = 2 ^ Y.card := by simp [Finset.card_univ, Fintype.card_bool]

/-- The outside assignments inducing a given subfunction. -/
noncomputable def fiber (f : Cslib.BooleanFunction n) (Y : Finset (Fin n))
    (g : (↥Y → Bool) → Bool) : Finset (↥Yᶜ → Bool) :=
  Finset.univ.filter fun z => (fun y => f (glue Y y z)) = g

theorem mem_fiber {f : Cslib.BooleanFunction n} {Y : Finset (Fin n)} {g : (↥Y → Bool) → Bool}
    {z : ↥Yᶜ → Bool} : z ∈ fiber f Y g ↔ (fun y => f (glue Y y z)) = g := by
  simp [fiber]

/-- Accepting inputs, counted fiber by fiber over the outside assignments. -/
theorem card_accepting_eq_sum (f : Cslib.BooleanFunction n) (Y : Finset (Fin n)) :
    (accepting f).card = ∑ z : ↥Yᶜ → Bool, ones fun y => f (glue Y y z) := by
  have key : (accepting f).card = ((Finset.univ : Finset ((↥Y → Bool) × (↥Yᶜ → Bool))).filter
      fun p => f (glue Y p.1 p.2) = true).card := by
    refine Finset.card_bij (fun x _ => (fun i => x i, fun i => x i)) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [glue_restrict]
      exact mem_accepting.mp hx
    · intro x _ x' _ h
      have := congrArg (fun p : (↥Y → Bool) × (↥Yᶜ → Bool) => glue Y p.1 p.2) h
      simpa [glue_restrict] using this
    · intro p hp
      refine ⟨glue Y p.1 p.2, mem_accepting.mpr (Finset.mem_filter.mp hp).2, ?_⟩
      refine Prod.ext ?_ ?_
      · funext i
        exact glue_apply_mem Y p.1 p.2 i
      · funext i
        exact glue_apply_compl Y p.1 p.2 i
  rw [key, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [ones, Finset.card_filter]

/-- Grouping outside assignments by the subfunction they induce. -/
theorem sum_ones_eq (f : Cslib.BooleanFunction n) (Y : Finset (Fin n)) :
    (∑ z : ↥Yᶜ → Bool, ones fun y => f (glue Y y z)) =
      ∑ g ∈ subfunctions f Y, ones g * (fiber f Y g).card := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun z : ↥Yᶜ → Bool => fun y => f (glue Y y z))
    (t := subfunctions f Y) (fun z _ => restrict_mem_subfunctions f Y z)]
  apply Finset.sum_congr rfl
  intro g _
  calc (∑ z ∈ Finset.univ.filter fun z : ↥Yᶜ → Bool => (fun y => f (glue Y y z)) = g,
          ones fun y => f (glue Y y z))
      = ∑ z ∈ fiber f Y g, ones g := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [(Finset.mem_filter.mp hz).2]
    _ = ones g * (fiber f Y g).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Rectangle-free functions have many subfunctions on every block.** With
`2 ^ (n - 2)` accepting inputs, `K`-rectangle-freeness, and `2 ^ |Y| ≥ 8 K`,
the block `Y` carries at least `2 ^ |Yᶜ| / (8 K)` distinct subfunctions. -/
theorem two_pow_card_compl_le {f : Cslib.BooleanFunction n} {K : Nat}
    (hrect : RectangleFree f K) (hacc : 2 ^ (n - 2) ≤ (accepting f).card)
    {Y : Finset (Fin n)} (hY : 8 * K ≤ 2 ^ Y.card) :
    2 ^ Yᶜ.card ≤ 8 * K * (subfunctions f Y).card := by
  -- Each class is small or its subfunction accepts few inputs.
  have term : ∀ g ∈ subfunctions f Y,
      ones g * (fiber f Y g).card ≤ K * (fiber f Y g).card + K * 2 ^ Y.card := by
    intro g _
    rcases hrect Y (Finset.univ.filter fun y => g y = true) (fiber f Y g) (by
      intro p hp q hq
      rw [Finset.mem_filter] at hp
      have := congrFun (mem_fiber.mp hq) p
      rw [this]
      exact hp.2) with h | h
    · exact (Nat.mul_le_mul_right _ h.le).trans (Nat.le_add_right _ _)
    · calc ones g * (fiber f Y g).card ≤ 2 ^ Y.card * K := Nat.mul_le_mul (ones_le g) h.le
        _ ≤ K * (fiber f Y g).card + K * 2 ^ Y.card := by rw [mul_comm]; exact Nat.le_add_left _ _
  have total : (accepting f).card ≤
      K * 2 ^ Yᶜ.card + (subfunctions f Y).card * (K * 2 ^ Y.card) := by
    rw [card_accepting_eq_sum f Y, sum_ones_eq f Y]
    calc (∑ g ∈ subfunctions f Y, ones g * (fiber f Y g).card)
        ≤ ∑ g ∈ subfunctions f Y, (K * (fiber f Y g).card + K * 2 ^ Y.card) :=
          Finset.sum_le_sum term
      _ = K * (∑ g ∈ subfunctions f Y, (fiber f Y g).card) +
          (subfunctions f Y).card * (K * 2 ^ Y.card) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, smul_eq_mul]
      _ = K * 2 ^ Yᶜ.card + (subfunctions f Y).card * (K * 2 ^ Y.card) := by
          congr 2
          unfold fiber
          rw [← Finset.card_eq_sum_card_fiberwise
            (f := fun z : ↥Yᶜ → Bool => fun y => f (glue Y y z))
            (fun z _ => restrict_mem_subfunctions f Y z)]
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  -- Arithmetic.
  have hacc_pos : 0 < (accepting f).card := lt_of_lt_of_le (Nat.two_pow_pos _) hacc
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp hacc_pos
  have hK : 1 < K := hrect.one_lt (mem_accepting.mp hx₀)
  have hYcard : 4 ≤ Y.card := by
    by_contra h
    have : 2 ^ Y.card ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hn : Y.card + Yᶜ.card = n := by
    rw [Finset.card_add_card_compl, Fintype.card_fin]
  set A := 2 ^ Y.card with hA
  set B := 2 ^ Yᶜ.card with hB
  set T := 2 ^ (n - 2) with hT
  set s := (subfunctions f Y).card with hs
  have hAB : A * B = 4 * T := by
    rw [hA, hB, hT, ← pow_add, hn, show n = (n - 2) + 2 by omega, Nat.add_sub_cancel, pow_add]
    ring
  have h1 : 8 * (K * B) ≤ A * B := by
    rw [← mul_assoc]
    exact Nat.mul_le_mul_right B hY
  have h3 : T ≤ K * B + s * (K * A) := hacc.trans total
  have key : 4 * T ≤ 8 * (s * (K * A)) := by omega
  have hApos : 0 < A := Nat.two_pow_pos _
  have : A * B ≤ A * (8 * K * s) := by
    rw [hAB, show A * (8 * K * s) = 8 * (s * (K * A)) by ring]
    exact key
  exact Nat.le_of_mul_le_mul_left this hApos

end Nechiporuk
end Algebraic
