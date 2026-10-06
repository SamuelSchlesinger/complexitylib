/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthClasses
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Majority

/-!
# Strict majority is not in `AC0` -- proof internals

A polynomial-size, depth-`c` family has at most `C * n ^ K` internal gates at
every large length `n`. The top-down Karchmer–Wigderson bound
`Circuit.majority_superpolynomial_gates` says that every depth-`c` circuit for
strict majority eventually needs more than `C * n ^ K + C` internal gates, so the
two bounds clash at one large length.
-/

public section

namespace Complexity

theorem majority_not_mem_AC0_internal : (fun _ => majority) ∉ AC0 := by
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

end Complexity
