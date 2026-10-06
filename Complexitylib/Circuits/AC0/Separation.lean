/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthClasses
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Majority
public import Complexitylib.Circuits.Smolensky
public import Complexitylib.Circuits.Threshold.Parity
public import Complexitylib.Circuits.XOR
public import Complexitylib.Circuits.AC0.Separation.Internal

/-!
# Separations for `AC0`, `AC0[3]`, and `TC0`

The parity family `Schnorr.xorBool` and the majority family `majority` are not
in the library's nonuniform `AC0`: no family of polynomial-size, constant-depth,
unbounded-fan-in AND/OR circuits with free negation on gate inputs computes
either family at every input length.

For parity, the proof normalizes each circuit to a negation-normal formula of no
larger depth and polynomial size (`Circuit.outputAC0Formula_spec`) and
contradicts the finite iterated-switching obstruction
(`AC0Formula.parity_counting_obstruction`) at one explicit large input length.
For majority, the proof applies the top-down Karchmer–Wigderson gate-count lower
bound (`Circuit.majority_superpolynomial_gates`).

Since parity is in `TC0` (`xorBool_mem_TC0`), `AC0 ⊆ TC0` is strict, and since
parity is not in `AC0[3]` (`xorBool_not_mem_AC0Mod_three`), `TC0` is not
contained in `AC0[3]`.
-/


public section

namespace Complexity

/-- **Parity is not in `AC0`.** No polynomial-size, constant-depth family of
unbounded-fan-in AND/OR circuits computes the parity family. -/
theorem xorBool_not_mem_AC0 : Schnorr.xorBool ∉ AC0 :=
  xorBool_not_mem_AC0_internal

/-- **Majority is not in `AC0`.** No polynomial-size, constant-depth family of
unbounded-fan-in AND/OR circuits computes the majority family. -/
theorem majority_not_mem_AC0 : (fun _ => majority) ∉ AC0 := by
  intro hmem
  obtain ⟨F, c, hcomputes, ⟨p, hp⟩, hdepth⟩ := mem_AC0_iff.mp hmem
  obtain ⟨C, N, hbound⟩ := BigO.exists_nat_bound (BigO.of_polynomial_bound p hp)
  obtain ⟨n₀, hn₀⟩ := Circuit.majority_superpolynomial_gates c p.natDegree C
  let m := max n₀ N
  have hdepth_m : (F.circuit (m + 1)).depth ≤ c := hdepth (m + 1)
  have heval_m : ∀ x : BitString (m + 1), (F.circuit (m + 1)).eval x 0 = majority x :=
    fun x => hcomputes.apply (m + 1) x
  have hlt := hn₀ (m + 1) (by omega) (F.internalGateCount (m + 1))
    (F.circuit (m + 1)) hdepth_m heval_m
  have hsize_m : F.internalGateCount (m + 1) + 1 ≤ C * (m + 1) ^ p.natDegree :=
    hbound (m + 1) (by omega)
  omega

/-- **`AC0` is strictly contained in `TC0`**, as nonuniform classes of Boolean
function families. Parity separates them. -/
theorem AC0_ssubset_TC0 : AC0 ⊂ TC0 :=
  Set.ssubset_iff_subset_ne.mpr
    ⟨AC0_subset_TC0, fun h => xorBool_not_mem_AC0 (h ▸ xorBool_mem_TC0)⟩

/-- **`TC0` is not contained in `AC0[3]`.** Parity is in `TC0` (`xorBool_mem_TC0`)
by symmetric threshold decomposition, while Razborov–Smolensky shows that parity
is not in `AC0[3]` (`xorBool_not_mem_AC0Mod_three`). -/
theorem not_TC0_subset_AC0Mod_three : ¬ (TC0 ⊆ AC0Mod 3) :=
  fun h => xorBool_not_mem_AC0Mod_three (h xorBool_mem_TC0)

end Complexity
