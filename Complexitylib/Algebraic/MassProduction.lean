/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.BlockInduction
public import Complexitylib.Algebraic.MassProduction.LupanovSynthesis
public import Complexitylib.Algebraic.MassProduction.RoutingPasses
public import Complexitylib.Algebraic.MassProduction.Nonuniform
public import Complexitylib.Algebraic.MassProduction.HighRate

/-!
# Boolean circuit mass production

This umbrella formalizes the exact results developed in the
[Boolean mass-production manuscript](https://github.com/SamuelSchlesinger/boolean-mass-production).
Its principal endpoints are:

* `BlockInduction.exponentialMassProduction`, which gives a uniform
  `O(2 ^ n / n)` upper bound for every fixed rational copy exponent below one;
* `Nonuniform.realSharpMassProduction`, which gives the improved coefficient
  `1/(1-gamma) + o(1)` for every fixed real copy exponent below one;
* `LupanovSynthesis.uhlig_massProduction`, which gives coefficient-one mass
  production through every copy bound `2 ^ o(n / log n)`.

The imported implementation develops independent direct products, explicit
De Morgan circuits, finite-field local recovery, disjoint-line scheduling,
routing, and the finite cost bounds used by those theorems. Approximation
results are intentionally outside this formalization.

The nonuniform extension proves universal scheduling menus, a complete
scheduler with near-linear record-count cost, batched lookup and routing,
high-rate systematic line-recovery codes, and the complete raw-input circuit
composition. Exact parameter estimates and a checked conversion to real rates
establish the improved coefficient; see the `Nonuniform` and `HighRate`
umbrella docstrings.
-/

@[expose] public section
