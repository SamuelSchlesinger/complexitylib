/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.DepthClasses.Defs
public import Complexitylib.Circuits.DepthClasses.Internal

/-!
# Circuit depth classes

This module defines nonuniform `DEPTH`, `NC^i`, `AC^i`, and `TC^i` classes using the
library's total circuit-family convention. Every class therefore includes a
specified answer on the empty input. `NC i` uses fan-in two, `AC i` uses
unbounded AND/OR gates, `TC i` uses unbounded threshold gates, and all impose
polynomial size.

The concrete polylogarithmic envelope is
`c * (Nat.log 2 n + 1) ^ i`. Thus `NC0` and `AC0` are constant-depth classes,
while `NC1` is logarithmic depth with the same `c * log₂ n + c` convention as
the Barrington formula-family development.

These definitions are explicitly nonuniform. Generator uniformity is an
additional predicate and is not implicit in the names `NC`, `AC`, or `TC`.
-/

@[expose] public section

namespace Complexity

/-- The exponent-zero polylogarithmic envelope is the constant `c`. -/
theorem polylogDepth_zero (c n : ℕ) : polylogDepth 0 c n = c :=
  polylogDepth_zero_internal c n

/-- The exponent-one envelope agrees with the Barrington convention
`c * log₂ n + c`. -/
theorem polylogDepth_one (c n : ℕ) :
    polylogDepth 1 c n = c * Nat.log 2 n + c :=
  polylogDepth_one_internal c n

/-- Increasing the multiplicative constant weakens a polylogarithmic depth
bound. -/
theorem polylogDepth_mono_constant {c c' : ℕ} (hcc' : c ≤ c')
    (i n : ℕ) :
    polylogDepth i c n ≤ polylogDepth i c' n :=
  polylogDepth_mono_constant_internal hcc' i n

/-- Increasing the polylogarithmic exponent weakens the depth bound. -/
theorem polylogDepth_mono_exponent {i j : ℕ} (hij : i ≤ j)
    (c n : ℕ) :
    polylogDepth i c n ≤ polylogDepth j c n :=
  polylogDepth_mono_exponent_internal hij c n

/-- `DEPTHWithBasis` is monotone in its pointwise depth envelope. -/
theorem DEPTHWithBasis_mono (B : Basis) {d e : ℕ → ℕ}
    (hde : ∀ n, d n ≤ e n) :
    DEPTHWithBasis B d ⊆ DEPTHWithBasis B e :=
  DEPTHWithBasis_mono_internal B hde

/-- The `NC` hierarchy is monotone in its polylogarithmic exponent. -/
theorem NC_mono {i j : ℕ} (hij : i ≤ j) : NC i ⊆ NC j :=
  NC_mono_internal hij

/-- The `AC` hierarchy is monotone in its polylogarithmic exponent. -/
theorem AC_mono {i j : ℕ} (hij : i ≤ j) : AC i ⊆ AC j :=
  AC_mono_internal hij

/-- The `TC` hierarchy is monotone in its polylogarithmic exponent. -/
theorem TC_mono {i j : ℕ} (hij : i ≤ j) : TC i ⊆ TC j :=
  TC_mono_internal hij

/-- Exact gatewise simulation gives `AC^i ⊆ TC^i` without changing size or
depth. -/
theorem AC_subset_TC (i : ℕ) : AC i ⊆ TC i :=
  AC_subset_TC_internal i

/-- In particular, nonuniform `AC0` is contained in nonuniform `TC0`. -/
theorem AC0_subset_TC0 : AC0 ⊆ TC0 :=
  AC_subset_TC 0

/-- In particular, constant-depth bounded-fan-in families are logarithmic
depth. -/
theorem NC0_subset_NC1 : NC0 ⊆ NC1 :=
  NC_mono (by omega)

/-- Membership in `NC1` is exactly polynomial size and a
`c * log₂ n + c` pointwise depth bound for one fan-in-two family. -/
theorem mem_NC1_iff {f : BoolFunFamily} :
    f ∈ NC1 ↔
      ∃ (F : CircuitFamily Basis.andOr2) (c : ℕ),
        F.Computes f ∧ F.PolynomialSize ∧
          F.DepthBoundedBy (fun n => c * Nat.log 2 n + c) :=
  mem_NC1_iff_internal

/-- Membership in `AC0` is exactly polynomial size and a constant pointwise
depth bound for one total unbounded-fan-in circuit family. -/
theorem mem_AC0_iff {f : BoolFunFamily} :
    f ∈ AC0 ↔
      ∃ (F : CircuitFamily Basis.unboundedAndOr) (c : ℕ),
        F.Computes f ∧ F.PolynomialSize ∧
          F.DepthBoundedBy (fun _ => c) :=
  mem_AC0_iff_internal

/-- Membership in `TC0` is exactly polynomial size and a constant pointwise
depth bound for one total threshold-circuit family. -/
theorem mem_TC0_iff {f : BoolFunFamily} :
    f ∈ TC0 ↔
      ∃ (F : CircuitFamily Basis.threshold) (c : ℕ),
        F.Computes f ∧ F.PolynomialSize ∧
          F.DepthBoundedBy (fun _ => c) :=
  mem_TC0_iff_internal

end Complexity
