/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Defs

/-!
# Elementary affine-flat operations

Restrictions preserve affineness and constants. Every nonconstant affine Boolean
function has two equally large fibers, and each fiber is again an affine flat.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

open Algebraic.Cutwidth
open scoped Classical

variable {n : Nat} {S T : AffineFlat n} {f g : (Fin n → Bool) → Bool}

/-- Adding the same translation twice cancels it. -/
@[simp] theorem xorThree_self_right (x y : Fin n → Bool) : xorThree x y y = x := by
  funext i
  simp only [xorThree, xorInput]
  cases x i <;> cases y i <;> rfl

/-- Translation by the difference of two points is an involution. -/
@[simp] theorem xorThree_translate_translate (x a b : Fin n → Bool) :
    xorThree (xorThree x a b) a b = x := by
  funext i
  simp only [xorThree, xorInput]
  cases x i <;> cases a i <;> cases b i <;> rfl

/-- The full Boolean cube is an affine flat. -/
noncomputable def AffineFlat.full (n : Nat) : AffineFlat n where
  carrier := Finset.univ
  nonempty := Finset.univ_nonempty
  closed := by simp

/-- The full Boolean cube contains exactly one point per input assignment. -/
@[simp] theorem AffineFlat.card_full (n : Nat) :
    (AffineFlat.full n).carrier.card = 2 ^ n := by
  simp [AffineFlat.full, Fintype.card_bool]

/-- Restricting to a smaller flat preserves affineness. -/
theorem AffineOn.mono (h : AffineOn S f) (sub : T.carrier ⊆ S.carrier) : AffineOn T f :=
  fun x hx y hy z hz => h x (sub hx) y (sub hy) z (sub hz)

/-- A function made constant remains constant on every later restriction. -/
theorem ConstantOn.mono (h : ConstantOn S f) (sub : T.carrier ⊆ S.carrier) :
    ConstantOn T f := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun x hx => hb x (sub hx)⟩

/-- Only values on the flat matter for affineness. -/
theorem AffineOn.congr (h : AffineOn S f) (same : ∀ x ∈ S.carrier, f x = g x) :
    AffineOn S g := by
  intro x hx y hy z hz
  rw [← same _ (S.closed x hx y hy z hz), h x hx y hy z hz,
    same x hx, same y hy, same z hz]

/-- Every constant function preserves ternary XOR. -/
theorem ConstantOn.affine (h : ConstantOn S f) : AffineOn S f := by
  obtain ⟨b, hb⟩ := h
  intro x hx y hy z hz
  rw [hb _ (S.closed x hx y hy z hz), hb x hx, hb y hy, hb z hz]
  cases b <;> rfl

/-- Constant Boolean functions are affine on every flat. -/
theorem affineOn_const (b : Bool) : AffineOn S (fun _ => b) :=
  (ConstantOn.affine ⟨b, by simp⟩)

/-- Each original input coordinate is an affine function. -/
theorem affineOn_coordinate (i : Fin n) : AffineOn S (fun x => x i) := by
  intro x _ y _ z _
  rfl

/-- XOR of two affine Boolean functions remains affine. -/
theorem AffineOn.xor (hf : AffineOn S f) (hg : AffineOn S g) :
    AffineOn S (fun x => Bool.xor (f x) (g x)) := by
  intro x hx y hy z hz
  dsimp only
  rw [hf x hx y hy z hz, hg x hx y hy z hz]
  cases f x <;> cases f y <;> cases f z <;>
    cases g x <;> cases g y <;> cases g z <;> rfl

/-- Every unary Boolean operation preserves affineness. -/
theorem AffineOn.unary (hf : AffineOn S f) (u : Bool → Bool) :
    AffineOn S (fun x => u (f x)) := by
  intro x hx y hy z hz
  dsimp only
  rw [hf x hx y hy z hz]
  cases f x <;> cases f y <;> cases f z <;> simp
  all_goals cases u false <;> cases u true <;> rfl

/-- A nonconstant Boolean function takes both values on a nonempty flat. -/
theorem exists_mem_eq_of_not_constant (h : ¬ ConstantOn S f) (b : Bool) :
    ∃ x ∈ S.carrier, f x = b := by
  by_contra absent
  push Not at absent
  apply h
  refine ⟨!b, fun x hx => ?_⟩
  have ne := absent x hx
  cases b <;> cases hf : f x <;> simp_all

/-- Each fiber of a nonconstant affine Boolean function is a half-sized affine flat. -/
theorem AffineOn.exists_half (affine : AffineOn S f) (nonconstant : ¬ ConstantOn S f)
    (b : Bool) : ∃ T : AffineFlat n, T.carrier ⊆ S.carrier ∧
      (∀ x ∈ T.carrier, f x = b) ∧ 2 * T.carrier.card = S.carrier.card := by
  classical
  obtain ⟨a, ha, hfa⟩ := exists_mem_eq_of_not_constant nonconstant false
  obtain ⟨c, hc, hfc⟩ := exists_mem_eq_of_not_constant nonconstant true
  let F (v : Bool) := S.carrier.filter fun x => f x = v
  have Fnonempty (v : Bool) : (F v).Nonempty := by
    obtain ⟨x, hx, hfx⟩ := exists_mem_eq_of_not_constant nonconstant v
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hfx⟩⟩
  have translate (x : Fin n → Bool) (hx : x ∈ S.carrier) :
      f (xorThree x a c) = !(f x) := by
    rw [affine x hx a ha c hc, hfa, hfc]
    cases f x <;> rfl
  have same : (F b).card = (F (!b)).card := by
    apply Finset.card_bij (fun x _ => xorThree x a c)
    · intro x hx
      obtain ⟨hx, hfx⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨S.closed x hx a ha c hc, by rw [translate x hx, hfx]⟩
    · intro x _ y _ hxy
      have := congrArg (fun z => xorThree z a c) hxy
      simpa only [xorThree_translate_translate] using this
    · intro y hy
      obtain ⟨hy, hfy⟩ := Finset.mem_filter.mp hy
      refine ⟨xorThree y a c, ?_, xorThree_translate_translate y a c⟩
      exact Finset.mem_filter.mpr ⟨S.closed y hy a ha c hc, by rw [translate y hy, hfy]; simp⟩
  have total : (F b).card + (F (!b)).card = S.carrier.card := by
    have complement : F (!b) = S.carrier.filter fun x => ¬ f x = b := by
      ext x
      cases b <;> cases f x <;> simp [F]
    rw [complement]
    exact Finset.card_filter_add_card_filter_not _
  let T : AffineFlat n :=
    { carrier := F b
      nonempty := Fnonempty b
      closed := by
        intro x hx y hy z hz
        obtain ⟨hx, hfx⟩ := Finset.mem_filter.mp hx
        obtain ⟨hy, hfy⟩ := Finset.mem_filter.mp hy
        obtain ⟨hz, hfz⟩ := Finset.mem_filter.mp hz
        refine Finset.mem_filter.mpr ⟨S.closed x hx y hy z hz, ?_⟩
        rw [affine x hx y hy z hz, hfx, hfy, hfz]
        cases b <;> rfl }
  refine ⟨T, Finset.filter_subset _ _, fun x hx => (Finset.mem_filter.mp hx).2, ?_⟩
  change 2 * (F b).card = S.carrier.card
  lia

end Algebraic.Aggregate.Geometry
