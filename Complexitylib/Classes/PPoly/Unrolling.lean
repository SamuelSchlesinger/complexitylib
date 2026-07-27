/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Unrolling.Defs
public import Complexitylib.Classes.PPoly.Unrolling.Internal

/-!
# Deterministic time has nonuniform circuits

This module specializes bounded NTM acceptance circuits to deterministic
machines by fixing the choice prefix of `tm.toNTM`. It packages the resulting
circuits into a family, proves exact language semantics and cubic-in-time size,
and concludes `P ⊆ P/poly` directly from the unrolling construction.

## Main results

- `TM.unrollingCircuitFamily_function`: exact fixed-horizon semantics.
- `TM.DecidesInTime.unrollingCircuitFamily_decides`: language correctness.
- `TM.unrollingCircuitFamily_size_bigO`: size `O(n^(3d))` for time `O(n^d)`.
- `TM.DecidesInTime.mem_PPoly`: package one polynomial-time decider.
- `P_subset_PPoly`: deterministic polynomial time has polynomial-size circuits.
-/

@[expose] public section

namespace Complexity

namespace TM

/-- The deterministic unrolling family computes the exact bounded acceptance
predicate at every input length. -/
theorem unrollingCircuitFamily_function
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) (x : BitString n) :
    (tm.unrollingCircuitFamily f).function n x =
      CircuitUnrolling.boundedAcceptanceBit tm.toNTM (f n) x
        (fun _ => false) :=
  tm.unrollingCircuitFamily_function_internal f n x

/-- A deterministic decider's exact-horizon bounded acceptance bit agrees with
language membership, for every choice string of its deterministic embedding. -/
theorem DecidesInTime.boundedAcceptanceBit_iff
    {tm : TM k} {L : Language} {f : ℕ → ℕ}
    (hdec : tm.DecidesInTime L f) (n : ℕ) (x : BitString n)
    (choices : BitString (f n)) :
    CircuitUnrolling.boundedAcceptanceBit tm.toNTM (f n) x choices = true ↔
      x.toList ∈ L :=
  hdec.boundedAcceptanceBit_iff_internal n x choices

/-- A deterministic decider's unrolling family agrees with its language on
every fixed-length input. -/
theorem DecidesInTime.unrollingCircuitFamily_function_iff
    {tm : TM k} {L : Language} {f : ℕ → ℕ}
    (hdec : tm.DecidesInTime L f) (n : ℕ) (x : BitString n) :
    (tm.unrollingCircuitFamily f).function n x = true ↔ x.toList ∈ L :=
  hdec.unrollingCircuitFamily_function_iff_internal n x

/-- The unrolling family of a deterministic decider decides the same language. -/
theorem DecidesInTime.unrollingCircuitFamily_decides
    {tm : TM k} {L : Language} {f : ℕ → ℕ}
    (hdec : tm.DecidesInTime L f) :
    (tm.unrollingCircuitFamily f).Decides L :=
  hdec.unrollingCircuitFamily_decides_internal

/-- If the deterministic horizon is `O(n^d)`, its unrolling family has size
`O(n^(3d))`. -/
theorem unrollingCircuitFamily_size_bigO
    (tm : TM k) {f : ℕ → ℕ} {d : ℕ}
    (hf : f =O ((· ^ d) : ℕ → ℕ)) :
    (tm.unrollingCircuitFamily f).size =O
      ((· ^ (3 * d)) : ℕ → ℕ) :=
  tm.unrollingCircuitFamily_size_bigO_internal hf

/-- A deterministic decider with a polynomial time horizon decides a language
in `P/poly` through its explicit unrolling family. -/
theorem DecidesInTime.mem_PPoly
    {tm : TM k} {L : Language} {f : ℕ → ℕ} {d : ℕ}
    (hdec : tm.DecidesInTime L f)
    (hf : f =O ((· ^ d) : ℕ → ℕ)) : L ∈ PPoly :=
  hdec.mem_PPoly_internal hf

end TM

/-- **P ⊆ P/poly**, directly by bounded deterministic unrolling. -/
theorem P_subset_PPoly : P ⊆ PPoly :=
  P_subset_PPoly_internal

end Complexity
