/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.SingleCut.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.ZMod.Basic

/-!
# Multi-output cuts: definitions

The single-cut infrastructure (`SingleCut`) splits the wires of a straight-line program into a
set `S` and its complement and counts the forward and backward signals crossing the split. This
file collects the notions used to apply it to programs with several outputs.

* `Linked p u v`: one of the wires `u`, `v` is a gate reading the other. These are the edges of
  the undirected *wire graph*.
* `component p w`: the wires joined to `w` by a path of linked wires.
* `gatesIn S`: the gates whose wires lie in `S` (the inputs are `SingleCut.inputsIn S`).
* `prefixUpTo rank w` and `prefixBelow rank t`: the prefixes of a ranking of the wires.
* `outputsIn out S`: the output indices whose wires lie in `S`.
* `leftFibre out f S x` and `rightFibre out f S x`: the inputs that differ from `x` only on the
  coordinates placed in `S` (respectively outside `S`) and keep every output carried outside
  `S` (respectively in `S`).
* `blockRank M Y X`: the rank of the block of a matrix with rows `Y` and columns `X`.
* `TotallyRegular M`: every square submatrix of `M` is nonsingular.
* `cauchy x y`: the Cauchy matrix `(1 / (x i - y j))`, and `cauchyZMod q N`, its instance over
  `ZMod q` with nodes `x i = i` and `y j = N + j`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

open SingleCut

variable {σ : Signature} {n s m : Nat}

/-! ## The wire graph -/

/-- Two wires are linked when one of them is a gate reading the other. -/
def Linked (p : Program σ n s) (u v : Wire n s) : Prop :=
  (∃ g : Fin s, u = Wire.gate g ∧ p.Reads g v) ∨ (∃ g : Fin s, v = Wire.gate g ∧ p.Reads g u)

/-- The connected component of a wire in the wire graph: the wires joined to it by a path of
linked wires. -/
noncomputable def component (p : Program σ n s) (w : Wire n s) : Finset (Wire n s) := by
  classical
  exact Finset.univ.filter fun v => Relation.ReflTransGen (Linked p) w v

/-- The gates whose wires lie in `S`. -/
def gatesIn (S : Finset (Wire n s)) : Finset (Fin s) :=
  Finset.univ.filter fun g => Wire.gate g ∈ S

/-! ## Prefixes of a ranking -/

/-- The wires ranked at most as high as `w`. -/
def prefixUpTo (rank : Wire n s → Nat) (w : Wire n s) : Finset (Wire n s) :=
  Finset.univ.filter fun v => rank v ≤ rank w

/-- The wires ranked below `t`. -/
def prefixBelow (rank : Wire n s → Nat) (t : Nat) : Finset (Wire n s) :=
  Finset.univ.filter fun v => rank v < t

/-! ## Outputs and fibres -/

/-- The output indices whose wires lie in `S`. -/
def outputsIn (out : Fin m → Wire n s) (S : Finset (Wire n s)) : Finset (Fin m) :=
  Finset.univ.filter fun i => out i ∈ S

/-- The inputs that agree with `x` on every coordinate placed outside `S` and on which `f`
takes the values it takes at `x` on every output whose wire lies outside `S`. -/
def leftFibre {U : Type*} [Fintype U] [DecidableEq U] (out : Fin m → Wire n s)
    (f : (Fin n → U) → Fin m → U) (S : Finset (Wire n s)) (x : Fin n → U) :
    Finset (Fin n → U) :=
  Finset.univ.filter fun x' =>
    (∀ j, j ∉ inputsIn S → x' j = x j) ∧ ∀ i, i ∉ outputsIn out S → f x' i = f x i

/-- The inputs that agree with `x` on every coordinate placed in `S` and on which `f` takes
the values it takes at `x` on every output whose wire lies in `S`. -/
def rightFibre {U : Type*} [Fintype U] [DecidableEq U] (out : Fin m → Wire n s)
    (f : (Fin n → U) → Fin m → U) (S : Finset (Wire n s)) (x : Fin n → U) :
    Finset (Fin n → U) :=
  Finset.univ.filter fun x' =>
    (∀ j ∈ inputsIn S, x' j = x j) ∧ ∀ i ∈ outputsIn out S, f x' i = f x i

/-! ## Matrices -/

section Matrix

variable {F : Type*} [Field F]

/-- The rank of the block of `M` with rows in `Y` and columns in `X`. -/
noncomputable def blockRank (M : Matrix (Fin m) (Fin n) F) (Y : Finset (Fin m))
    (X : Finset (Fin n)) : Nat :=
  (M.submatrix (fun i : ↥Y => (i : Fin m)) (fun j : ↥X => (j : Fin n))).rank

/-- A matrix is *totally regular* when every square submatrix is nonsingular: for every `k`
and all injective choices of `k` rows and `k` columns, the determinant is nonzero. -/
def TotallyRegular (M : Matrix (Fin m) (Fin n) F) : Prop :=
  ∀ (k : Nat) (r : Fin k → Fin m) (c : Fin k → Fin n), Function.Injective r →
    Function.Injective c → (M.submatrix r c).det ≠ 0

/-- The Cauchy matrix with entries `1 / (x i - y j)`. -/
def cauchy (x : Fin m → F) (y : Fin n → F) : Matrix (Fin m) (Fin n) F :=
  Matrix.of fun i j => (x i - y j)⁻¹

end Matrix

/-- The `N × N` Cauchy matrix over `ZMod q` with nodes `x i = i` and `y j = N + j`. For a prime
`q ≥ 2 N` the nodes are distinct, so it is totally regular. -/
def cauchyZMod (q N : Nat) : Matrix (Fin N) (Fin N) (ZMod q) :=
  Matrix.of fun i j => (((i : Nat) : ZMod q) - ((N + j : Nat) : ZMod q))⁻¹

end Algebraic.Cutwidth.MultiOutput
