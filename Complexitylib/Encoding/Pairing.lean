/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.Delimit
public import Mathlib.Data.Nat.Init
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Widget.Calc
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Pairing binary strings

This file defines the low-level self-delimiting pairing codec used by machine
inputs throughout Complexitylib. It deliberately has no dependency on the
machine or complexity-class layers, so parsers and encoders can reuse it
without introducing an import cycle.
-/


@[expose] public section

namespace Complexity

/-- Encode a pair of binary strings as a single binary string.
    Each bit of `x` is doubled (`false ↦ [false, false]`, `true ↦ [true, true]`),
    followed by the separator `[false, true]`, followed by `y` verbatim.
    The output has length `2|x| + 2 + |y|` (`pair_length`) and the encoding is
    injective (`pair_inj`). Machine-level cost is recorded elsewhere: `pair` of
    two `FP` functions is in `FP` (`mem_FP_pair`), and `x ↦ pair (f x) x` has
    an explicit bound (`TM.pairWithInputTM_computesInTime`); no linear-time
    bound for `pair` itself is stated. -/
def pair (x y : List Bool) : List Bool :=
  delimit x ++ y

private theorem pair_nil_eq (y : List Bool) :
    pair [] y = false :: true :: y := by
  simp [pair]

/-- One step of the doubling encoder: `pair` on `b :: x` prepends the
    doubled bit `b, b`. -/
theorem pair_cons_eq (b : Bool) (x y : List Bool) :
    pair (b :: x) y = b :: b :: pair x y := by
  simp [pair]

/-- `|pair x y| = 2·|x| + 2 + |y|`. The `2·|x|` comes from doubling every
    bit of `x`; the `+2` is the separator `[false, true]`. -/
@[simp] theorem pair_length (x y : List Bool) :
    (pair x y).length = 2 * x.length + 2 + y.length := by
  induction x with
  | nil => simp [pair]; omega
  | cons b xs ih =>
    rw [pair_cons_eq, List.length_cons, List.length_cons, List.length_cons, ih]
    omega

/-- `pair` is injective: if `pair x₁ y₁ = pair x₂ y₂` then `x₁ = x₂` and
`y₁ = y₂`. -/
theorem pair_inj {x₁ x₂ : List Bool} {y₁ y₂ : List Bool}
    (h : pair x₁ y₁ = pair x₂ y₂) : x₁ = x₂ ∧ y₁ = y₂ := by
  induction x₁ generalizing x₂ with
  | nil =>
    rw [pair_nil_eq] at h
    cases x₂ with
    | nil =>
      rw [pair_nil_eq] at h
      exact ⟨rfl, (List.cons.inj (List.cons.inj h).2).2⟩
    | cons b x₂' =>
      rw [pair_cons_eq] at h
      have h1 := (List.cons.inj h).1           -- false = b
      have h2 := (List.cons.inj (List.cons.inj h).2).1  -- true = b
      exact absurd (h1.trans h2.symm) Bool.false_ne_true
  | cons b₁ x₁' ih =>
    rw [pair_cons_eq] at h
    cases x₂ with
    | nil =>
      rw [pair_nil_eq] at h
      have h1 := (List.cons.inj h).1           -- b₁ = false
      have h2 := (List.cons.inj (List.cons.inj h).2).1  -- b₁ = true
      exact absurd (h1.symm.trans h2) Bool.false_ne_true
    | cons b₂ x₂' =>
      rw [pair_cons_eq] at h
      have hb := (List.cons.inj h).1           -- b₁ = b₂
      have htail := (List.cons.inj (List.cons.inj h).2).2  -- pair x₁' y₁ = pair x₂' y₂
      have ⟨hx, hy⟩ := ih htail
      subst hb; subst hx
      exact ⟨rfl, hy⟩

/-- `unpair?` is a left inverse of `pair`: decoding an encoded pair
    recovers exactly its two components. -/
@[simp] theorem unpair?_pair (x y : List Bool) :
    unpair? (pair x y) = some (x, y) :=
  unpair?_delimit_append x y

/-- Soundness of the decoder: if `unpair?` succeeds on `z`, producing `(x, y)`,
    then `z` was exactly the encoding `pair x y`. -/
theorem eq_pair_of_unpair?_eq_some {z x y : List Bool} (h : unpair? z = some (x, y)) :
    z = pair x y :=
  eq_delimit_append_of_unpair?_eq_some h

/-- `unpair? z` returns `some (x, y)` if and only if `z = pair x y`,
    characterizing exactly which strings are valid pair encodings. -/
theorem unpair?_eq_some_iff {z x y : List Bool} :
    unpair? z = some (x, y) ↔ z = pair x y := by
  constructor
  · exact eq_pair_of_unpair?_eq_some
  · intro hz
    subst hz
    exact unpair?_pair x y

/-- In `pair x y`, the first duplicated copy of `x[i]` sits at position `2*i`. -/
theorem pair_getElem_left_first (x y : List Bool) (i : ℕ) (hi : i < x.length) :
    (pair x y)[2 * i]'(by rw [pair_length]; omega) = x[i]'hi := by
  induction x generalizing i with
  | nil =>
      cases hi
  | cons b xs ih =>
      cases i with
      | zero =>
          simp [pair_cons_eq]
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          change (b :: b :: pair xs y)[2 * (i + 1)]'(
            by simp [pair_length]; omega) = xs[i]'hi'
          have hshift :
              (b :: b :: pair xs y)[2 * (i + 1)]'(by simp [pair_length]; omega) =
                (pair xs y)[2 * i]'(by rw [pair_length]; omega) := by
            calc
              (b :: b :: pair xs y)[2 * (i + 1)]'(by simp [pair_length]; omega)
                  = (b :: pair xs y)[2 * i + 1]'(by simp [pair_length]; omega) := by
                      exact List.getElem_cons_succ b (b :: pair xs y) (2 * i + 1)
                        (by simp [pair_length]; omega)
              _ = (pair xs y)[2 * i]'(by rw [pair_length]; omega) := by
                      exact List.getElem_cons_succ b (pair xs y) (2 * i)
                        (by simp [pair_length]; omega)
          rw [hshift]
          exact ih i hi'

/-- In `pair x y`, the second duplicated copy of `x[i]` sits at position `2*i+1`. -/
theorem pair_getElem_left_second (x y : List Bool) (i : ℕ) (hi : i < x.length) :
    (pair x y)[2 * i + 1]'(by rw [pair_length]; omega) = x[i]'hi := by
  induction x generalizing i with
  | nil =>
      cases hi
  | cons b xs ih =>
      cases i with
      | zero =>
          simp [pair_cons_eq]
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          change (b :: b :: pair xs y)[2 * (i + 1) + 1]'(
            by simp [pair_length]; omega) = xs[i]'hi'
          have hshift :
              (b :: b :: pair xs y)[2 * (i + 1) + 1]'(by simp [pair_length]; omega) =
                (pair xs y)[2 * i + 1]'(by rw [pair_length]; omega) := by
            calc
              (b :: b :: pair xs y)[2 * (i + 1) + 1]'(by simp [pair_length]; omega)
                  = (b :: pair xs y)[2 * i + 2]'(by simp [pair_length]; omega) := by
                      exact List.getElem_cons_succ b (b :: pair xs y) (2 * i + 2)
                        (by simp [pair_length]; omega)
              _ = (pair xs y)[2 * i + 1]'(by rw [pair_length]; omega) := by
                      exact List.getElem_cons_succ b (pair xs y) (2 * i + 1)
                        (by simp [pair_length]; omega)
          rw [hshift]
          exact ih i hi'

/-- The first separator bit in `pair x y` is `false`. -/
theorem pair_getElem_sep_zero (x y : List Bool) :
    (pair x y)[2 * x.length]'(by rw [pair_length]; omega) = false := by
  induction x with
  | nil =>
      simp [pair]
  | cons b xs ih =>
      change (b :: b :: pair xs y)[2 * (xs.length + 1)]'(
        by simp [pair_length]; omega) = false
      have hshift :
          (b :: b :: pair xs y)[2 * (xs.length + 1)]'(by simp [pair_length]; omega) =
            (pair xs y)[2 * xs.length]'(by rw [pair_length]; omega) := by
        calc
          (b :: b :: pair xs y)[2 * (xs.length + 1)]'(by simp [pair_length]; omega)
              = (b :: pair xs y)[2 * xs.length + 1]'(by simp [pair_length]; omega) := by
                  exact List.getElem_cons_succ b (b :: pair xs y) (2 * xs.length + 1)
                    (by simp [pair_length]; omega)
          _ = (pair xs y)[2 * xs.length]'(by rw [pair_length]; omega) := by
                  exact List.getElem_cons_succ b (pair xs y) (2 * xs.length)
                    (by simp [pair_length]; omega)
      rw [hshift]
      exact ih

/-- The second separator bit in `pair x y` is `true`. -/
theorem pair_getElem_sep_one (x y : List Bool) :
    (pair x y)[2 * x.length + 1]'(by rw [pair_length]; omega) = true := by
  induction x with
  | nil =>
      simp [pair]
  | cons b xs ih =>
      change (b :: b :: pair xs y)[2 * (xs.length + 1) + 1]'(
        by simp [pair_length]; omega) = true
      have hshift :
          (b :: b :: pair xs y)[2 * (xs.length + 1) + 1] =
            (pair xs y)[2 * xs.length + 1] := by
        have h₁ : 2 * xs.length + 2 + 1 < (b :: b :: pair xs y).length := by
          simp [pair_length]
          omega
        have h₂ : 2 * xs.length + 1 + 1 < (b :: pair xs y).length := by
          simp [pair_length]
          omega
        calc
          (b :: b :: pair xs y)[2 * (xs.length + 1) + 1]
              = (b :: pair xs y)[2 * xs.length + 2] := by
                  simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using
                    List.getElem_cons_succ b (b :: pair xs y) (2 * xs.length + 2)
                      (h := h₁)
          _ = (pair xs y)[2 * xs.length + 1] := by
                  simpa only [Nat.add_assoc] using
                    List.getElem_cons_succ b (pair xs y) (2 * xs.length + 1)
                      (h := h₂)
      rw [hshift]
      exact ih

/-- Length of the doubled prefix used in `pair x y`. -/
private theorem pair_flatMap_doubled_length (x : List Bool) :
    (x.flatMap fun b => [b, b]).length = 2 * x.length := by
  induction x with
  | nil =>
      simp
  | cons b xs ih =>
      rw [List.flatMap_cons, List.length_append, ih]
      simp
      omega

/-- In `pair x y`, the suffix after the separator is exactly `y`. -/
theorem pair_getElem_right (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    (pair x y)[2 * x.length + 2 + j]'(by rw [pair_length]; omega) = y[j]'hj := by
  have hdecomp : pair x y = (x.flatMap fun b => [b, b]) ++ [false, true] ++ y := rfl
  have hflat := pair_flatMap_doubled_length x
  have hprefix :
      ((x.flatMap fun b => [b, b]) ++ [false, true]).length = 2 * x.length + 2 := by
    rw [List.length_append, hflat]
    rfl
  have hge :
      ((x.flatMap fun b => [b, b]) ++ [false, true]).length ≤ 2 * x.length + 2 + j := by
    rw [hprefix]
    omega
  have hj' :
      (2 * x.length + 2 + j) -
        ((x.flatMap fun b => [b, b]) ++ [false, true]).length < y.length := by
    rw [hprefix]
    omega
  calc
    (pair x y)[2 * x.length + 2 + j]'(by rw [pair_length]; omega)
        = ((x.flatMap fun b => [b, b]) ++ [false, true] ++ y)[2 * x.length + 2 + j]'
            (by rw [← hdecomp, pair_length]; omega) := by
              exact List.getElem_of_eq hdecomp _
    _ = y[(2 * x.length + 2 + j) - ((x.flatMap fun b => [b, b]) ++ [false, true]).length]'hj' :=
          List.getElem_append_right hge
    _ = y[j]'hj := by
          congr 1
          rw [hprefix]
          omega

/-! ## The projections

Total decoders for the two components. `pairFst` is defined by scanning rather
than through `unpair?` so that a single-pass machine can compute it; only the
behaviour of either projection on canonical pairs is ever used. -/

/-- The first component of a canonical pair: read doubled bits until the
`[false, true]` separator. On `pair x y` this returns `x` (see `pairFst_pair`);
on malformed input it returns the bits decoded so far. -/
def pairFst : List Bool → List Bool
  | false :: false :: z => false :: pairFst z
  | true :: true :: z => true :: pairFst z
  | _ => []

/-- The second component of a canonical pair: the suffix after the leading
self-delimiting block, or `[]` if the input is not a valid pair. -/
def pairSnd (z : List Bool) : List Bool :=
  match unpair? z with
  | some (_, s) => s
  | none => []

@[simp] theorem pairFst_pair (x y : List Bool) : pairFst (pair x y) = x := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> (rw [pair_cons_eq]; simp [pairFst, ih])

@[simp] theorem pairSnd_pair (x y : List Bool) : pairSnd (pair x y) = y := by
  simp [pairSnd]

/-- `pairSnd` agrees with the partial decoder `unpair?`, defaulting to `[]`. -/
theorem pairSnd_eq_unpair? (z : List Bool) :
    pairSnd z = ((unpair? z).map Prod.snd).getD [] := by
  unfold pairSnd
  cases unpair? z <;> rfl

/-- The first component of a pair is no longer than the pair. -/
theorem pairFst_length_le (z : List Bool) : (pairFst z).length ≤ z.length := by
  induction z using pairFst.induct <;> simp [pairFst] <;> omega

/-- The second component of a pair is no longer than the pair. -/
theorem pairSnd_length_le (z : List Bool) : (pairSnd z).length ≤ z.length := by
  rcases hu : unpair? z with _ | ⟨p, q⟩
  · rw [show pairSnd z = [] from by rw [pairSnd, hu]]
    simp
  · have hz : z = pair p q := unpair?_eq_some_iff.mp hu
    rw [show pairSnd z = q from by rw [pairSnd, hu], hz, pair_length]
    omega

end Complexity
