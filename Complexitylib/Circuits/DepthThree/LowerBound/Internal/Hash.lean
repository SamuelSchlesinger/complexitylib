/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.AlgebraBits
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Lean.Elab.Tactic.Omega

/-!
# Unrestricted depth-three lower bound: hash

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/Hash.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound.BinaryHash

open scoped BigOperators

/-- The two-element field. -/
abbrev F2 := BinaryAlgebra.F2
/-- Input vectors over the two-element field. -/
abbrev Data (d : ℕ) := Fin d → F2
/-- Seed vectors for the binary linear hash family. -/
abbrev Seed (d r : ℕ) := Fin (d + r - 1) → F2
/-- Output vectors of the binary linear hash family. -/
abbrev Output (r : ℕ) := Fin r → F2

/-- Index a hash-seed coordinate by the sum of input and output positions. -/
def sumIndex {d r : ℕ} (i : Fin r) (s : Fin d) : Fin (d + r - 1) :=
  ⟨i.val + s.val, by have := i.isLt; have := s.isLt; omega⟩

@[simp] theorem sumIndex_val {d r : ℕ} (i : Fin r) (s : Fin d) :
    (sumIndex i s).val = i.val + s.val := rfl

theorem sumIndex_left_injective {d r : ℕ} (s : Fin d) :
    Function.Injective (fun i : Fin r => sumIndex i s) := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simpa only [sumIndex_val, Nat.add_right_cancel_iff] using hval

/-- The seeded linear hash over the two-element field. -/
def hashF2 {d r : ℕ} (u : Seed d r) (x : Data d) : Output r :=
  fun i => ∑ s : Fin d, u (sumIndex i s) * x s

@[simp] theorem hashF2_apply {d r : ℕ} (u : Seed d r) (x : Data d) (i : Fin r) :
    hashF2 u x i = ∑ s : Fin d, u (sumIndex i s) * x s := rfl

@[simp] theorem hashF2_zero_data {d r : ℕ} (u : Seed d r) :
    hashF2 u 0 = 0 := by
  funext i
  simp [hashF2]

@[simp] theorem hashF2_zero_seed {d r : ℕ} (x : Data d) :
    hashF2 (0 : Seed d r) x = 0 := by
  funext i
  simp [hashF2]

theorem hashF2_add_data {d r : ℕ} (u : Seed d r) (x y : Data d) :
    hashF2 u (x + y) = hashF2 u x + hashF2 u y := by
  funext i
  simp [hashF2, mul_add, Finset.sum_add_distrib]

theorem hashF2_sub_data {d r : ℕ} (u : Seed d r) (x y : Data d) :
    hashF2 u (x - y) = hashF2 u x - hashF2 u y := by
  funext i
  simp [hashF2, mul_sub, Finset.sum_sub_distrib]

theorem hashF2_add_seed {d r : ℕ} (u v : Seed d r) (x : Data d) :
    hashF2 (u + v) x = hashF2 u x + hashF2 v x := by
  funext i
  simp [hashF2, add_mul, Finset.sum_add_distrib]

theorem hashF2_sub_seed {d r : ℕ} (u v : Seed d r) (x : Data d) :
    hashF2 (u - v) x = hashF2 u x - hashF2 v x := by
  funext i
  simp [hashF2, sub_mul, Finset.sum_sub_distrib]

/-- The same seeded hash expressed on Boolean bit vectors. -/
def hashBool {d r : ℕ} (u : Fin (d + r - 1) → Bool) (x : Fin d → Bool) :
    Fin r → Bool :=
  fun i => BinaryAlgebra.fieldBit
    (hashF2 (fun j => BinaryAlgebra.bitValue (u j))
      (fun s => BinaryAlgebra.bitValue (x s)) i)

@[simp] theorem bitValue_hashBool {d r : ℕ}
    (u : Fin (d + r - 1) → Bool) (x : Fin d → Bool) (i : Fin r) :
    BinaryAlgebra.bitValue (hashBool u x i) =
      hashF2 (fun j => BinaryAlgebra.bitValue (u j))
        (fun s => BinaryAlgebra.bitValue (x s)) i := by
  simp [hashBool]

theorem bitsEquivF2_hashBool {d r : ℕ}
    (u : Fin (d + r - 1) → Bool) (x : Fin d → Bool) :
    BinaryAlgebra.bitsEquivF2 (Fin r) (hashBool u x) =
      hashF2 (BinaryAlgebra.bitsEquivF2 (Fin (d + r - 1)) u)
        (BinaryAlgebra.bitsEquivF2 (Fin d) x) := by
  funext i
  exact bitValue_hashBool u x i

end DepthThreeLowerBound.BinaryHash

end Complexity
