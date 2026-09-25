/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.NP.Witness
import Complexitylib.Classes.PCP.Internal.GuessVerifyGeneric

/-!
# The guess-and-verify NTM construction

This file discharges `NP.WitnessNTMConstruction`, the machine-construction
interface stated in `Complexitylib.Classes.NP.Witness`. The machine is the
generic guess-and-verify NTM behind `mem_NP_of_poly_witness`: guess a
certificate, pair it with the input, and run the deterministic verifier. This
file only repackages that theorem. A polynomial-time decider for `pairLang R`
is a verifier in `P`, the witness-length bound transfers through
`mem_pairLang_pair`, and `NP` membership unfolds to the required NTM.

With the construction proved, the FNP witness characterization of `NP` holds
unconditionally.

## Main results

- `NP.witnessNTMConstruction` — the construction interface holds
- `NP.mem_NP_of_FNP` — a language characterized by an FNP relation is in `NP`
- `NP.witnessLang_mem_NP` — the witness language of an FNP relation is in `NP`
-/


public section

namespace Complexity

namespace NP

/-- **The guess-and-verify NTM construction.** A polynomial-time DTM deciding
`pairLang R`, together with a polynomial bound on witness length, yields a
polynomial-time NTM deciding `witnessLang R`. -/
theorem witnessNTMConstruction : WitnessNTMConstruction := by
  intro R p c k M f hbal hM hfO
  have hpair : pairLang R ∈ P := Set.mem_iUnion.mpr ⟨c, k, M, f, hM, hfO⟩
  have hmem : witnessLang R ∈ NP :=
    mem_NP_of_poly_witness p hpair
      (fun x y hxy => hbal x y ((mem_pairLang_pair R x y).mp hxy))
      (fun x => by simp)
  obtain ⟨d, k', N, g, hN, hgO⟩ := Set.mem_iUnion.mp hmem
  exact ⟨k', d, N, g, hN, hgO⟩

/-- **FNP ⇒ NP.** If `R ∈ FNP` and `x ∈ L ↔ ∃ y, R x y`, then `L ∈ NP`. -/
theorem mem_NP_of_FNP {R : List Bool → List Bool → Prop} {L : Language}
    (hR : R ∈ FNP) (hchar : ∀ x, x ∈ L ↔ ∃ y, R x y) :
    L ∈ NP :=
  mem_NP_of_FNP_witness witnessNTMConstruction hR hchar

/-- The witness language of an FNP relation is in `NP`. -/
theorem witnessLang_mem_NP {R : List Bool → List Bool → Prop} (hR : R ∈ FNP) :
    witnessLang R ∈ NP :=
  witnessLang_mem_NP_of_FNP witnessNTMConstruction hR

end NP

end Complexity
