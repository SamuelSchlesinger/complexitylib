/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Mathlib.Computability.TuringMachine.Computable
public import Complexitylib.RationalHitting.Internal.StackLanguage

/-!
# Execution of finite Mathlib stack machines

Reuse the exact-run definition from the rational hitting-list development.
The TM2 bridge keeps its original definition and proofs in place and exposes
that execution convention alongside the bundled Mathlib computation types.
-/

@[expose] public section

namespace Complexity.MathlibTM2

export RationalHitting.TMTime (exec)

end Complexity.MathlibTM2
