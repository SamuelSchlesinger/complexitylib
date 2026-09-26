/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.NP
public import Complexitylib.Classes.FNP.Defs

/-!
# NP witness characterization

This file states the textbook characterization of `NP` via FNP witness
relations:

> A language `L` is in `NP` iff there is an FNP relation `R` such that
> `x ∈ L ↔ ∃ y, R x y`.

The forward direction (`NP ⊆ witness form`) is a *computation-path* witness
argument and is left for a later pass.

The reverse direction — **the FNP ⇒ NP bridge** — is captured here by
`mem_NP_of_FNP_witness`, parameterized by the single TM-engineering
construction interface `WitnessNTMConstruction`: build the nondeterministic
"guess-and-verify" machine from a deterministic verifier of `pairLang R`.
Everything above that construction — unpacking FNP, computing polynomial
bounds, and packaging the result as membership in `NP` — is proved here.

The construction itself is proved as `NP.witnessNTMConstruction` in
`Complexitylib.Classes.NP.WitnessConstruction`, which also states the
unconditional forms `NP.mem_NP_of_FNP` and `NP.witnessLang_mem_NP`. It lives
downstream because the guess-and-verify machine is built from modules that
import this one.

## How `WitnessNTMConstruction` is proved

The proof (`mem_NP_of_poly_witness`, in
`Complexitylib.Classes.NP.Internal.GuessVerify`) has two steps.

1. **Linear witnesses** (`mem_NP_of_linear_witness`). The guess-and-verify NTM
   `SAT.satGuessVerifyNTM M` guesses a string `y` of length at most `|x| + 1`,
   forms `pair x y`, and runs the deterministic verifier `M` on it. It decides
   every language whose members are exactly the inputs with such a short
   certificate accepted by `M`, in time polynomial when `M`'s is.
2. **Polynomial witnesses by padding.** For a witness bound `p`, the input `x`
   is padded to `pair x r` with a ruler `r` long enough that the bound becomes
   linear in the padded length (`padWith`). The language is the preimage of
   the padded language `padLang p L₀` under this polynomial-time map, and `NP`
   is closed under such preimages (`mem_NP_preimage`).

The result is stated only as membership in `NP`; no explicit running-time
bound for the composed machine is recorded.
-/


public section

namespace Complexity


namespace NP

/-- The witness language of a relation `R` — the set of inputs `x` that
    admit some witness. Isolated as a definition so the statement of
    `mem_NP_of_FNP_witness` reads cleanly. -/
def witnessLang (R : List Bool → List Bool → Prop) : Language :=
  {x | ∃ y, R x y}

/-- Membership in `witnessLang R` unfolds to the existence of a witness:
    `x ∈ witnessLang R ↔ ∃ y, R x y`. -/
@[simp] theorem mem_witnessLang {R : List Bool → List Bool → Prop} {x : List Bool} :
    x ∈ witnessLang R ↔ ∃ y, R x y := Iff.rfl

-- ════════════════════════════════════════════════════════════════════════
-- The core TM-engineering construction interface
-- ════════════════════════════════════════════════════════════════════════

/-- **Guess-and-verify NTM construction interface.** Given a DTM `M` deciding
    `pairLang R` within a time bound `T(n) ≤ O(n^c)` and a polynomial `p`
    bounding witness length, there exists an NTM deciding
    `witnessLang R = {x | ∃ y, R x y}` in polynomial time.

    The textbook (Arora–Barak) machine nondeterministically writes a witness
    of length `≤ p(|x|)`, builds `pair(x, y)`, and simulates `M`. The library's
    proof instead guesses witnesses of length at most `|x| + 1` and reaches a
    general polynomial bound by padding the input (see the module docstring).

    This is isolated as a named proposition so that this file's results can
    be stated before the machine is available in the import graph. It is
    proved as `NP.witnessNTMConstruction` in
    `Complexitylib.Classes.NP.WitnessConstruction`. -/
@[expose]
def WitnessNTMConstruction : Prop :=
  ∀ {R : List Bool → List Bool → Prop}
    {p : Polynomial ℕ} {c k : ℕ}
    {M : TM k} {f : ℕ → ℕ},
    (∀ x y, R x y → y.length ≤ p.eval x.length) →
    M.DecidesInTime (pairLang R) f →
    f =O (· ^ c) →
    ∃ (k' d : ℕ) (N : NTM k') (g : ℕ → ℕ),
      N.DecidesInTime (witnessLang R) g ∧ g =O (· ^ d)

-- ════════════════════════════════════════════════════════════════════════
-- Main theorem: FNP witness relations put L in NP
-- ════════════════════════════════════════════════════════════════════════

/-- **FNP ⇒ NP via witnesses.** If the generic guess-and-verify construction
    has been implemented, `R ∈ FNP`, and `x ∈ L ↔ ∃ y, R x y`, then
    `L ∈ NP`. Proof: unpack FNP to get a polynomial-time DTM verifier
    `M` for `pairLang R` and a polynomial witness-length bound, apply the
    construction to build the guess-and-verify NTM, and package the result as
    NP membership. -/
theorem mem_NP_of_FNP_witness
    (hwitness : WitnessNTMConstruction)
    {R : List Bool → List Bool → Prop} {L : Language}
    (hR : R ∈ FNP)
    (hchar : ∀ x, x ∈ L ↔ ∃ y, R x y) :
    L ∈ NP := by
  obtain ⟨hPB, hPairP⟩ := hR
  -- Unpack `pairLang R ∈ P` to a DTM and a poly time bound.
  obtain ⟨c, k, M, f, hM, hfO⟩ := Set.mem_iUnion.mp hPairP
  -- Unpack `PolyBalanced R` to a polynomial witness-length bound.
  obtain ⟨p, hp⟩ := hPB
  -- Build the NTM via the core construction.
  obtain ⟨k', d, N, g, hN, hgO⟩ := hwitness hp hM hfO
  -- `L = witnessLang R` up to set extensionality.
  have hLeq : L = witnessLang R := Set.ext fun x => by
    simpa [witnessLang] using hchar x
  -- Conclude.
  rw [hLeq]
  exact Set.mem_iUnion.mpr ⟨d, k', N, g, hN, hgO⟩

-- ════════════════════════════════════════════════════════════════════════
-- Immediate corollary: FNP ⇔ NP-witness (the "reverse direction" only)
-- ════════════════════════════════════════════════════════════════════════

/-- **Restatement in terms of `witnessLang`.** If `R ∈ FNP`, then
    `witnessLang R ∈ NP`. This is the useful form for applying to
    concrete relations like `Witness`. -/
theorem witnessLang_mem_NP_of_FNP
    (hwitness : WitnessNTMConstruction)
    {R : List Bool → List Bool → Prop} (hR : R ∈ FNP) :
    witnessLang R ∈ NP :=
  mem_NP_of_FNP_witness hwitness hR fun _ => Iff.rfl

end NP

end Complexity
