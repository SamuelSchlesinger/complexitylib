/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Family.Defs
public import Complexitylib.Asymptotics
public import Complexitylib.Circuits.BitString

/-!
# Boolean circuit families

This module provides the public API for circuit-family semantics, concrete
size/depth bounds, and the equivalence between pointwise polynomial bounds and
the power big-O convention used by complexity classes.
-/


public section

namespace Complexity

namespace Circuit

variable {B : Basis} {N G : ℕ} [NeZero N]

/-- `Computes` respects equality of the target function. -/
theorem computes_congr (c : Circuit B N 1 G) {f g : BitString N → Bool}
    (h : f = g) : c.Computes f ↔ c.Computes g := by
  subst g
  rfl

/-- `ComputesOnLength` depends only on the family's component at length `N`. -/
theorem computesOnLength_congr (c : Circuit B N 1 G) {f g : BoolFunFamily}
    (h : f N = g N) : c.ComputesOnLength f ↔ c.ComputesOnLength g :=
  c.computes_congr h

/-- A circuit computing `f` evaluates to `f x` on each input `x`. -/
theorem Computes.apply {c : Circuit B N 1 G} {f : BitString N → Bool}
    (h : c.Computes f) (x : BitString N) :
    (c.eval x) 0 = f x :=
  congrFun h x

/-- A circuit computing a family at length `N` evaluates to `f N x` on each input `x`. -/
theorem ComputesOnLength.apply {c : Circuit B N 1 G} {f : BoolFunFamily}
    (h : c.ComputesOnLength f) (x : BitString N) :
    (c.eval x) 0 = f N x :=
  Circuit.Computes.apply h x

/-- Any circuit computing `f` witnesses an upper bound on its generic extended
size complexity. -/
theorem Computes.sizeComplexityWithTop_le {c : Circuit B N 1 G}
    {f : BitString N → Bool} (h : c.Computes f) :
    sizeComplexityWithTop B f ≤ c.size :=
  Circuit.sizeComplexityWithTop_le c f h

/-- Over a complete basis, any circuit computing `f` witnesses a natural-valued
upper bound on its size complexity. -/
theorem Computes.sizeComplexity_le {c : Circuit B N 1 G}
    {f : BitString N → Bool} (h : c.Computes f) :
    sizeComplexity B f ≤ c.size :=
  Circuit.sizeComplexity_le c f h

end Circuit

namespace CircuitFamily

variable {B : Basis}

/-- At length `0` the family's function is the designated empty-input output. -/
@[simp] theorem function_zero (F : CircuitFamily B) (x : BitString 0) :
    F.function 0 x = F.emptyOutput := rfl

/-- At positive lengths the family's function is evaluation of the length-`n + 1` circuit. -/
@[simp] theorem function_succ (F : CircuitFamily B) (n : ℕ)
    (x : BitString (n + 1)) :
    F.function (n + 1) x = (F.circuit (n + 1)).eval x 0 := rfl

/-- The size of a circuit family at length `0` is `0`. -/
@[simp] theorem size_zero (F : CircuitFamily B) : F.size 0 = 0 := rfl

/-- At positive lengths the family's size is the size of the length-`n + 1` circuit. -/
@[simp] theorem size_succ (F : CircuitFamily B) (n : ℕ) :
    F.size (n + 1) = (F.circuit (n + 1)).size := rfl

/-- The depth of a circuit family at length `0` is `0`. -/
@[simp] theorem depth_zero (F : CircuitFamily B) : F.depth 0 = 0 := rfl

/-- At positive lengths the family's depth is the depth of the length-`n + 1` circuit. -/
@[simp] theorem depth_succ (F : CircuitFamily B) (n : ℕ) :
    F.depth (n + 1) = (F.circuit (n + 1)).depth := rfl

/-- A size bound may be weakened to any pointwise larger bound. -/
theorem sizeBoundedBy_mono (F : CircuitFamily B) {s t : ℕ → ℕ}
    (hF : F.SizeBoundedBy s) (hst : ∀ n, s n ≤ t n) :
    F.SizeBoundedBy t :=
  fun n => (hF n).trans (hst n)

/-- A depth bound may be weakened to any pointwise larger bound. -/
theorem depthBoundedBy_mono (F : CircuitFamily B) {d e : ℕ → ℕ}
    (hF : F.DepthBoundedBy d) (hde : ∀ n, d n ≤ e n) :
    F.DepthBoundedBy e :=
  fun n => (hF n).trans (hde n)

section BigO

open Complexity

/-- A pointwise size bound yields a big-O size bound. -/
theorem SizeBoundedBy.bigO {F : CircuitFamily B} {s : ℕ → ℕ}
    (h : F.SizeBoundedBy s) : F.size =O s :=
  Complexity.BigO.of_le h

/-- Pointwise polynomial size is equivalent to a big-O power bound. -/
theorem polynomialSize_iff_bigO (F : CircuitFamily B) :
    F.PolynomialSize ↔ ∃ k, F.size =O ((· ^ k) : ℕ → ℕ) := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.natDegree, Complexity.BigO.of_polynomial_bound p hp⟩
  · rintro ⟨k, hk⟩
    obtain ⟨p, hp⟩ := Complexity.BigO.pow_polynomial_bound hk
    exact ⟨p, hp⟩

end BigO

/-- `Computes` respects equality of the target function family. -/
theorem computes_congr (F : CircuitFamily B) {f g : BoolFunFamily}
    (h : f = g) : F.Computes f ↔ F.Computes g := by
  subst g
  rfl

/-- A circuit family computes at most one function family. -/
theorem computes_unique (F : CircuitFamily B) {f g : BoolFunFamily}
    (hf : F.Computes f) (hg : F.Computes g) : f = g :=
  hf.symm.trans hg

/-- Evaluating the serialized fixed-length input agrees with family
    evaluation at that length. -/
@[simp] theorem evalList_ofFn (F : CircuitFamily B) {n : ℕ}
    (x : BitString n) :
    F.evalList (List.ofFn x) = F.function n x := by
  unfold evalList
  have h := List.equivSigmaTuple.apply_symm_apply
    (⟨n, x⟩ : Σ n, BitString n)
  exact congrArg (fun p : Σ n, BitString n => F.function p.1 p.2) h

/-- Evaluating the list form of a fixed-length input agrees with family
    evaluation at that length. -/
@[simp] theorem evalList_toList (F : CircuitFamily B) {n : ℕ}
    (x : BitString n) : F.evalList x.toList = F.function n x :=
  F.evalList_ofFn x

/-- Evaluating the empty list yields the designated empty-input output. -/
@[simp] theorem evalList_nil (F : CircuitFamily B) :
    F.evalList [] = F.emptyOutput := rfl

/-- A family computing `f` agrees with `f` at every length and input. -/
theorem Computes.apply {F : CircuitFamily B} {f : BoolFunFamily}
    (h : F.Computes f) (n : ℕ) (x : BitString n) :
    F.function n x = f n x := by
  rw [h]

/-- A family computing `f` evaluates any list input to `f` at the list's length. -/
theorem Computes.evalList {F : CircuitFamily B} {f : BoolFunFamily}
    (h : F.Computes f) (x : List Bool) :
    F.evalList x = f x.length x.get :=
  h.apply x.length x.get

end CircuitFamily

end Complexity
