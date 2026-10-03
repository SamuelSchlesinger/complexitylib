/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Level.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite recursive block condensation and splitting

The initial map may already depend on an earlier seed. Each further level
adds one fresh seed, uses it on every current block, and splits the resulting
pairs in order. The seed type retains the earlier seed and every fresh seed
exactly once. Alphabets and fresh-seed types may vary between levels.

These are deterministic finite maps and an explicit error sum. They model
the recursion in Chattopadhyay--Goodman--Liao, Theorem 5.6 of *Affine Extractors
for Almost Logarithmic Entropy*, <https://eccc.weizmann.ac.il/report/2021/075/>.
An encoded uniform evaluator and a concrete parameter schedule are separate.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

universe u v w

/-- Retain the initial seed and one fresh seed for every completed level. -/
def RecursiveSeeds (Earlier : Type u) (Fresh : Nat → Type u) : Nat → Type u
  | 0 => Earlier
  | n + 1 => RecursiveSeeds Earlier Fresh n × Fresh n

instance (Earlier : Type u) (Fresh : Nat → Type u)
    [Fintype Earlier] [∀ i, Fintype (Fresh i)] (n : Nat) :
    Fintype (RecursiveSeeds Earlier Fresh n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Earlier)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (RecursiveSeeds Earlier Fresh n × Fresh n))

instance (Earlier : Type u) (Fresh : Nat → Type u)
    [Nonempty Earlier] [∀ i, Nonempty (Fresh i)] (n : Nat) :
    Nonempty (RecursiveSeeds Earlier Fresh n) := by
  induction n with
  | zero => exact inferInstanceAs (Nonempty Earlier)
  | succ n ih =>
    let := ih
    exact inferInstanceAs (Nonempty (RecursiveSeeds Earlier Fresh n × Fresh n))

/-- Every level splits each current block into two successive blocks. -/
def recursiveBlockCount (t : Nat) : Nat → Nat
  | 0 => t
  | n + 1 => 2 * recursiveBlockCount t n

/-- Run the initial map, then one shared-seed condenser and split per level. -/
def recursiveBlockMap {X : Type v} {Earlier : Type u} {Fresh : Nat → Type u}
    {α : Nat → Type w} {t : Nat}
    (initial : X → Earlier → (Fin t → α 0))
    (C : ∀ i, α i → Fresh i → α (i + 1) × α (i + 1)) :
    (n : Nat) → X → RecursiveSeeds Earlier Fresh n → (Fin (recursiveBlockCount t n) → α n)
  | 0, x, y => initial x y
  | n + 1, x, y => condenseSplitMap (C n) (recursiveBlockCount t n)
      (recursiveBlockMap initial C n x y.1) y.2

/-- Sum the condenser and splitting errors over all blocks entering each level. -/
noncomputable def recursiveBlockError (t : Nat) (ε : Nat → ℝ) (e : Nat → Nat)
    (n : Nat) : ℝ :=
  ∑ i ∈ Finset.range n, (recursiveBlockCount t i : ℝ) * (ε i + ((2 : ℝ) ^ e i)⁻¹)

end Algebraic.Cutwidth.Extractor
