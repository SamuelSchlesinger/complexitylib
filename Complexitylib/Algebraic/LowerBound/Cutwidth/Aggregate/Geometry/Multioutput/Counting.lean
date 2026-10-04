/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Pairing
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Message.Bias

/-!
# Balanced outputs avoid multiple-primary conjunctions

A permutation has balanced, distinct output coordinates. Each multiple-primary
conjunction has a nondefault fibre of size at most one quarter of the cube, so it
cannot be one of those outputs. Nonprojection outputs must be actual gate wires.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

open scoped Classical

/-- Every primary-coordinate fibre occupies exactly half of the Boolean cube. -/
theorem two_mul_card_coordinate_fibre {n : ℕ} (i : Fin n) (b : Bool) :
    2 * Fintype.card {x : Fin n → Bool // x i = b} = 2 ^ n := by
  let e : Bool × {x : Fin n → Bool // x i = b} ≃ (Fin n → Bool) :=
    { toFun := fun s => Function.update s.2.val i s.1
      invFun := fun x => ⟨x i, ⟨Function.update x i b, by simp⟩⟩
      left_inv := by
        rintro ⟨a, x, hx⟩
        apply Prod.ext
        · simp
        apply Subtype.ext
        funext j
        by_cases h : j = i
        · subst j; simp [hx]
        · simp [h]
      right_inv := by intro x; ext j; by_cases h : j = i <;> simp [h] }
  simpa using Fintype.card_congr e

/-- Every coordinate of a permutation is balanced. -/
theorem two_mul_card_permutation_fibre {n : ℕ} (F : (Fin n → Bool) → (Fin n → Bool))
    (bijective : Function.Bijective F) (i : Fin n) (b : Bool) :
    2 * Fintype.card {x : Fin n → Bool // F x i = b} = 2 ^ n := by
  let e := Equiv.ofBijective F bijective
  have same := Fintype.card_congr (e.subtypeEquivOfSubtype (p := fun x => x i = b))
  change Fintype.card {x // F x i = b} = _ at same
  rw [same, two_mul_card_coordinate_fibre]

/-- A marked line forces two primary coordinates in its nondefault fibre. -/
theorem multiPrimary_line_quarter {n g : ℕ} (p : Program signature n g)
    (line : Line signature n g) (marked : multiPrimary line = true) :
    ∃ b, 4 * Fintype.card {x : Fin n → Bool // lineFunction p line x = b} ≤ 2 ^ n := by
  obtain ⟨hc, i, hi, j, hj, distinct⟩ := (multiPrimary_iff_exists_pair _).mp marked
  obtain ⟨s, hs⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨t, ht⟩ := (Finset.mem_filter.mp hj).2
  rcases line with ⟨op, wires⟩
  cases op with
  | affine r bias coefficient => simp [Op.isConjunction] at hc
  | conjunction r polarity negated =>
    refine ⟨!negated, ?_⟩
    conv_rhs => rw [← Fintype.card_fin n]
    apply four_mul_card_le_of_forces_pair _ i j distinct (polarity s) (polarity t)
    intro x hx
    have all : ∀ slot, Wire.elim x (p.eval interpretation x) (wires slot) =
        polarity slot := by
      cases negated <;> simpa [lineFunction, Line.eval, interpretation,
        conjunctionValue] using hx
    change wires s = .input i at hs
    change wires t = .input j at ht
    exact ⟨by simpa [hs] using all s, by simpa [ht] using all t⟩

/-- A marked actual gate has a nondefault fibre of at most one quarter of all inputs. -/
theorem multiPrimary_quarter {n g : ℕ} (p : Program signature n g) (gate : Fin g)
    (marked : multiPrimary (p.lines gate) = true) :
    ∃ b, 4 * Fintype.card {x : Fin n → Bool // p.gateFunction interpretation gate x = b}
      ≤ 2 ^ n := by
  have same : lineFunction p (p.lines gate) = p.gateFunction interpretation gate := by
    funext x
    exact p.lines_eval interpretation x gate
  simpa only [same] using multiPrimary_line_quarter p (p.lines gate) marked

/-- Distinct nonprojection outputs of a permutation occupy unmarked actual gates. -/
theorem input_add_multiCount_le_size {n : ℕ} (c : Circuit signature n n)
    (bijective : Function.Bijective (c.eval interpretation))
    (nonprojection : ∀ i j, c.outputFunction interpretation i ≠ fun x => x j) :
    n + multiCount c.program ≤ c.size := by
  have gates : ∀ i, ∃ gate, c.outputs i = Wire.gate gate := by
    intro i
    cases eq : c.outputs i with
    | gate gate => exact ⟨gate, rfl⟩
    | input j =>
      apply (nonprojection i j).elim
      funext x
      change c.program.wireFunction interpretation (c.outputs i) x = x j
      rw [eq]
      rfl
  choose gate hg using gates
  have same (i : Fin n) : c.outputFunction interpretation i =
      c.program.gateFunction interpretation (gate i) := by
    funext x
    change c.program.wireFunction interpretation (c.outputs i) x = _
    rw [hg i]
    rfl
  have inj : Function.Injective gate := by
    intro i j heq
    by_contra different
    obtain ⟨x, hx⟩ := bijective.surjective (Function.update (fun _ => false) i true)
    have equality : c.eval interpretation x i = c.eval interpretation x j := by
      change c.outputFunction interpretation i x = c.outputFunction interpretation j x
      rw [same i, same j, heq]
    rw [hx] at equality
    simp [Ne.symm different] at equality
  have unmarked (i : Fin n) : ¬ multiPrimary (c.program.lines (gate i)) = true := by
    intro marked
    obtain ⟨b, small⟩ := multiPrimary_quarter c.program (gate i) marked
    have half := two_mul_card_permutation_fibre (c.eval interpretation) bijective i b
    change 2 * Fintype.card {x // c.outputFunction interpretation i x = b} = _ at half
    rw [same i] at half
    have positive := Nat.two_pow_pos n
    lia
  let remaining := Finset.univ.filter fun gate => ¬ multiPrimary (c.program.lines gate) = true
  have sub : Finset.univ.image gate ⊆ remaining := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, unmarked i⟩
  have lower : n ≤ remaining.card := by
    have := Finset.card_le_card sub
    simpa only [Finset.card_image_of_injective _ inj, Finset.card_univ,
      Fintype.card_fin] using this
  have partition := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin c.size)))
    (p := fun gate => multiPrimary (c.program.lines gate) = true)
  rw [← multiCount_eq_card_filter, Finset.card_univ, Fintype.card_fin] at partition
  dsimp only [remaining] at lower
  lia

end Algebraic.Aggregate.Geometry
