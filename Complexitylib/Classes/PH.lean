/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments
public import Complexitylib.Classes.P.Pairing
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The polynomial hierarchy

This file defines the polynomial hierarchy via certificate quantifiers, following
the quantified-formula definition (Arora–Barak Definition 5.4, stated over the
library's `pair` codec): `polyExistsLang p L` holds of `x` when some witness `w`
of length at most `p.eval |x|` puts the encoded pair `pair x w` in `L`, and
`polyForallLang p L` requires this of every such witness. Lifting these to class
operators gives the levels `SigmaP 0 = P`, `SigmaP (n + 1) =
polyExistsClass (PiP n)`, `PiP n = complClass (SigmaP n)`, and their union `PH`.

The level inclusions `SigmaP n ⊆ SigmaP (n + 1)` and `PiP n ⊆ PiP (n + 1)` need
one computational fact: decoding the first component of a canonical pair is
polynomial-time computable (`pairFst_mem_FP`, from
`Complexitylib.Classes.P.Pairing`), so every result in this file is
unconditional.

## Main definitions

- `polyExistsLang`, `polyForallLang` — witness quantifiers on languages
- `polyExistsClass`, `polyForallClass` — the induced operators on classes
- `SigmaP`, `PiP`, `PH` — the hierarchy levels and their union

## Main results

- `compl_polyExistsLang` / `compl_polyForallLang` — quantifier duality
- `complClass_polyExistsClass` / `complClass_polyForallClass` — class duality
- `SigmaP_zero`, `PiP_zero`, `SigmaP_succ`, `PiP_succ` — recursion laws
- `pairFst_mem_FP` — the pair decoder is polynomial-time
- `P_subset_polyExistsClass_P` / `P_subset_polyForallClass_P` — base inclusions
- `SigmaP_subset_SigmaP_succ` / `PiP_subset_PiP_succ` — level inclusions
- `SigmaP_subset_PH`, `P_subset_PH`

## TODO

- Relate `SigmaP 1` to the NTM-based `NP` through the witness characterization
  interface in `Complexitylib.Classes.NP.Witness`.
-/

@[expose] public section

namespace Complexity

/-! ## Witness quantifiers on languages -/

/-- The language of inputs `x` admitting a witness `w` of length at most
`p.eval |x|` such that the encoded pair `pair x w` lies in `L`. -/
def polyExistsLang (p : Polynomial ℕ) (L : Language) : Language :=
  {x | ∃ w, w.length ≤ p.eval x.length ∧ pair x w ∈ L}

/-- The language of inputs `x` such that every witness `w` of length at most
`p.eval |x|` puts the encoded pair `pair x w` in `L`. -/
def polyForallLang (p : Polynomial ℕ) (L : Language) : Language :=
  {x | ∀ w, w.length ≤ p.eval x.length → pair x w ∈ L}

/-- Membership in `polyExistsLang` unfolds to a bounded existential. -/
@[simp] theorem mem_polyExistsLang {p : Polynomial ℕ} {L : Language} {x : List Bool} :
    x ∈ polyExistsLang p L ↔ ∃ w, w.length ≤ p.eval x.length ∧ pair x w ∈ L :=
  Iff.rfl

/-- Membership in `polyForallLang` unfolds to a bounded universal. -/
@[simp] theorem mem_polyForallLang {p : Polynomial ℕ} {L : Language} {x : List Bool} :
    x ∈ polyForallLang p L ↔ ∀ w, w.length ≤ p.eval x.length → pair x w ∈ L :=
  Iff.rfl

/-- Complementing a bounded existential yields a bounded universal over the
complement: some-witness failure is all-witness exclusion. -/
theorem compl_polyExistsLang (p : Polynomial ℕ) (L : Language) :
    (polyExistsLang p L)ᶜ = polyForallLang p Lᶜ := by
  ext x
  simp [polyExistsLang, polyForallLang]

/-- Complementing a bounded universal yields a bounded existential over the
complement. -/
theorem compl_polyForallLang (p : Polynomial ℕ) (L : Language) :
    (polyForallLang p L)ᶜ = polyExistsLang p Lᶜ := by
  ext x
  simp [polyExistsLang, polyForallLang]

/-! ## Quantifier operators on classes -/

/-- The class of languages expressible as a polynomially-bounded existential
over some language of `C`. -/
def polyExistsClass (C : Set Language) : Set Language :=
  {L | ∃ (p : Polynomial ℕ), ∃ L' ∈ C, L = polyExistsLang p L'}

/-- The class of languages expressible as a polynomially-bounded universal
over some language of `C`. -/
def polyForallClass (C : Set Language) : Set Language :=
  {L | ∃ (p : Polynomial ℕ), ∃ L' ∈ C, L = polyForallLang p L'}

/-- `polyExistsClass` is monotone in the base class. -/
theorem polyExistsClass_mono {C D : Set Language} (h : C ⊆ D) :
    polyExistsClass C ⊆ polyExistsClass D := by
  rintro L ⟨p, L', hL', rfl⟩
  exact ⟨p, L', h hL', rfl⟩

/-- `polyForallClass` is monotone in the base class. -/
theorem polyForallClass_mono {C D : Set Language} (h : C ⊆ D) :
    polyForallClass C ⊆ polyForallClass D := by
  rintro L ⟨p, L', hL', rfl⟩
  exact ⟨p, L', h hL', rfl⟩

/-- Class-level quantifier duality: the complement class of a bounded
existential class is the bounded universal class over the complement class. -/
theorem complClass_polyExistsClass (C : Set Language) :
    complClass (polyExistsClass C) = polyForallClass (complClass C) := by
  ext L
  simp only [mem_complClass, polyExistsClass, polyForallClass, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, L', hL', hEq⟩
    refine ⟨p, L'ᶜ, by simpa [mem_complClass, compl_compl] using hL', ?_⟩
    rw [← compl_compl L, hEq, compl_polyExistsLang]
  · rintro ⟨p, L', hL', rfl⟩
    exact ⟨p, L'ᶜ, hL', by rw [compl_polyForallLang]⟩

/-- Class-level quantifier duality: the complement class of a bounded universal
class is the bounded existential class over the complement class. -/
theorem complClass_polyForallClass (C : Set Language) :
    complClass (polyForallClass C) = polyExistsClass (complClass C) := by
  ext L
  simp only [mem_complClass, polyExistsClass, polyForallClass, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, L', hL', hEq⟩
    refine ⟨p, L'ᶜ, by simpa [mem_complClass, compl_compl] using hL', ?_⟩
    rw [← compl_compl L, hEq, compl_polyForallLang]
  · rintro ⟨p, L', hL', rfl⟩
    exact ⟨p, L'ᶜ, hL', by rw [compl_polyExistsLang]⟩

/-! ## Base inclusions -/
/-- Every language of `P` is a bounded existential over `P`: take the zero
witness bound, so the only witness is `[]`, and decide `pair x []` by decoding
the first component and running the original decider. -/
theorem P_subset_polyExistsClass_P : P ⊆ polyExistsClass P := by
  intro L hL
  refine ⟨0, pairFst ⁻¹' L, mem_P_preimage_pairFst hL, ?_⟩
  ext x
  simp only [mem_polyExistsLang, Polynomial.eval_zero, Nat.le_zero,
    List.length_eq_zero_iff, Set.mem_preimage]
  constructor
  · intro hx
    exact ⟨[], rfl, by simpa using hx⟩
  · rintro ⟨w, rfl, hmem⟩
    simpa using hmem

/-- Every language of `P` is a bounded universal over `P`: with the zero
witness bound the only witness is `[]`, decided as in
`P_subset_polyExistsClass_P`. -/
theorem P_subset_polyForallClass_P : P ⊆ polyForallClass P := by
  intro L hL
  refine ⟨0, pairFst ⁻¹' L, mem_P_preimage_pairFst hL, ?_⟩
  ext x
  simp only [mem_polyForallLang, Polynomial.eval_zero, Nat.le_zero,
    List.length_eq_zero_iff, Set.mem_preimage]
  constructor
  · rintro hx w rfl
    simpa using hx
  · intro h
    simpa using h [] rfl

/-! ## The hierarchy -/

/-- The Σ levels of the polynomial hierarchy: `SigmaP 0 = P` and
`SigmaP (n + 1)` is a bounded existential over the complement class of
`SigmaP n` (that is, over `PiP n`). -/
def SigmaP : ℕ → Set Language
  | 0 => P
  | n + 1 => polyExistsClass (complClass (SigmaP n))

/-- The Π levels of the polynomial hierarchy: `PiP n` is the complement class
of `SigmaP n`. -/
def PiP (n : ℕ) : Set Language :=
  complClass (SigmaP n)

/-- The polynomial hierarchy: the union of all Σ levels. -/
def PH : Set Language :=
  ⋃ n : ℕ, SigmaP n

/-- The zeroth Σ level is `P`. -/
@[simp] theorem SigmaP_zero : SigmaP 0 = P := rfl

/-- The complement class of a Σ level is the corresponding Π level. -/
@[simp] theorem complClass_SigmaP (n : ℕ) : complClass (SigmaP n) = PiP n := rfl

/-- The complement class of a Π level is the corresponding Σ level. -/
@[simp] theorem complClass_PiP (n : ℕ) : complClass (PiP n) = SigmaP n := by
  rw [PiP, complClass_complClass]

/-- The zeroth Π level is `P`, since `P` is closed under complement. -/
@[simp] theorem PiP_zero : PiP 0 = P := by
  rw [PiP, SigmaP_zero, complClass_P]

/-- Recursion law for Σ levels: `SigmaP (n + 1)` is a bounded existential over
`PiP n`. -/
theorem SigmaP_succ (n : ℕ) : SigmaP (n + 1) = polyExistsClass (PiP n) := rfl

/-- Recursion law for Π levels: `PiP (n + 1)` is a bounded universal over
`SigmaP n`. -/
theorem PiP_succ (n : ℕ) : PiP (n + 1) = polyForallClass (SigmaP n) := by
  rw [PiP]
  show complClass (polyExistsClass (complClass (SigmaP n))) = _
  rw [complClass_polyExistsClass, complClass_complClass]

/-- The first Σ level is the bounded existential closure of `P` — the
certificate form of `NP`. -/
theorem SigmaP_one : SigmaP 1 = polyExistsClass P := by
  rw [SigmaP_succ, PiP_zero]

/-- The first Π level is the bounded universal closure of `P` — the
certificate form of `coNP`. -/
theorem PiP_one : PiP 1 = polyForallClass P := by
  rw [PiP_succ, SigmaP_zero]

/-! ## Level inclusions -/

/-- Both level inclusions, proved simultaneously by induction: the base case is
the pair of base inclusions of `P`, and each successor case is monotonicity of
the opposite quantifier applied to the other component. -/
private theorem piP_sigmaP_subset_succ (n : ℕ) :
    PiP n ⊆ PiP (n + 1) ∧ SigmaP n ⊆ SigmaP (n + 1) := by
  induction n with
  | zero =>
    constructor
    · rw [PiP_zero, PiP_one]
      exact P_subset_polyForallClass_P
    · rw [SigmaP_zero, SigmaP_one]
      exact P_subset_polyExistsClass_P
  | succ n ih =>
    constructor
    · rw [PiP_succ, PiP_succ]
      exact polyForallClass_mono ih.2
    · rw [SigmaP_succ, SigmaP_succ]
      exact polyExistsClass_mono ih.1

/-- Each Σ level is contained in the next. -/
theorem SigmaP_subset_SigmaP_succ (n : ℕ) : SigmaP n ⊆ SigmaP (n + 1) :=
  (piP_sigmaP_subset_succ n).2

/-- Each Π level is contained in the next. -/
theorem PiP_subset_PiP_succ (n : ℕ) : PiP n ⊆ PiP (n + 1) :=
  (piP_sigmaP_subset_succ n).1

/-! ## PH -/

/-- Membership in `PH` is membership in some Σ level. -/
theorem mem_PH_iff {L : Language} : L ∈ PH ↔ ∃ n : ℕ, L ∈ SigmaP n :=
  Set.mem_iUnion

/-- Every Σ level is contained in the hierarchy. -/
theorem SigmaP_subset_PH (n : ℕ) : SigmaP n ⊆ PH :=
  fun _ h => Set.mem_iUnion.mpr ⟨n, h⟩

/-- `P` is contained in the polynomial hierarchy. -/
theorem P_subset_PH : P ⊆ PH :=
  SigmaP_subset_PH 0

end Complexity
