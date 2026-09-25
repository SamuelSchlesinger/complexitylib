/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Hierarchy.Polynomial

/-!
# Circuit size hierarchy

The argument follows the Boolean cube of truth tables:

* `BooleanCube.exists_between` gives discrete intermediate values from a
  bound on coordinate updates.
* `DeMorgan.complexity_dist_le` bounds changes in minimum internal gate count
  by `2 * n` times the ordinary Hamming distance between truth tables.
* `DeMorgan.eventually_exists_complexity_between` combines interpolation with
  Shannon counting, reaching every threshold through `2^n / n`.
* `DeMorgan.polynomialSize_ssubset` proves `SIZE(n^a) ⊊ SIZE(n^b)` for all
  real `1 ≤ a < b`, including multiplicative constants in the size classes.

These are nonuniform existence results over the native shared circuit model.
They do not assert a uniform construction of the separating family.
-/

@[expose] public section
