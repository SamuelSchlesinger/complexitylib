/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.DecisionFn
public import Complexitylib.Classes.PH
public import Complexitylib.Classes.PH.SipserLautemann.Matrix
public import Complexitylib.Classes.PH.SipserLautemann.Verdict

/-!
# The Sipser–Lautemann theorem

The Sipser–Lautemann theorem (Arora–Barak Theorem 7.15) places bounded-error
probabilistic polynomial time inside the second level of the polynomial
hierarchy: `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ`. This file states that containment against the
library's concrete `BPP` (`Complexitylib.Classes.Randomized`) and the
certificate-quantifier levels `SigmaP` / `PiP` (`Complexitylib.Classes.PH`),
and proves it: `sipserLautemann`.

## How it is proved

The development lives in the `SipserLautemann` subdirectory:

- `Covering` — Lautemann's covering lemma in both directions, by counting
  shifts of an event in the seed space;
- `TimeBound` — the acceptance probability is frozen past the halting time, so
  a machine's arbitrary time bound may be replaced by a dominating polynomial;
- `Amplified` — majority amplification plus the covering lemma give the `∃∀`
  characterization `x ∈ L ↔ ∃ shifts, ∀ seeds, some shift accepts`, and its
  complementary form for `x ∉ L`;
- `Encode` — bitstring codecs for seeds and shift tuples;
- `Matrix` — the quantifier-free matrix as a language of encoded triples, and
  the identity exhibiting `L` and `Lᶜ` as polynomially bounded `∃∀` forms over
  it;
- `Verdict` — the matrix verdict as a member of Cobham's algebra, hence in
  `FP`.

What remained was the polynomial-time decidability of the matrix, isolated as
the interfaces `MatrixInP` and — as a statement about a *function* —
`MatrixVerdictInFP`. It is discharged by `matrixVerdictInFP` with no machine
construction at all: `CobhamFP_eq_FP` turns it into a programming task inside
Cobham's algebra, and `mem_P_of_decisionFn_bool` converts the result back to
`P`. The verdict is computed in `SipserLautemann.Verdict` — decode the triple
with the payload scanners, build the trial count and seed length as `smash`
lengths from the polynomial time bound, and take the disjunction over shift
blocks of the majority vote over trial blocks — with each trial one run of the
machine along the choice bits of its block, via `NTM.choiceTM` and its
in-algebra simulation in `Complexitylib.Classes.P.Cobham.Internal.ChoiceSim`.
The matrix is taken at a *polynomial* time bound, which is what makes the
per-trial step count computable from the input; `TimeBound` supplies the
normalization.

## Main definitions

- `SipserLautemann` — the statement `BPP ⊆ SigmaP 2 ∩ PiP 2`
- `MatrixInP` — the polynomial-time decidability interface for the matrix
- `MatrixVerdictInFP` — the same interface as a statement about a function

## Main results

- `sipserLautemann` — **the theorem**, `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ`
- `BPP_subset_SigmaP_two`, `BPP_subset_PiP_two`, `BPP_subset_PH` — its halves
  and the corollary
- `matrixVerdictInFP` — the matrix interface, discharged
- `sipserLautemann_of_matrixInP`, `sipserLautemann_of_verdictInFP` — the
  theorem from either form of the interface
- `matrixInP_of_verdictInFP` — the function form implies the language form
- `mem_SigmaP_two_of_matrixInP`, `mem_PiP_two_of_matrixInP` — the two halves
- `sipserLautemann_iff` — the statement splits into its `Σ₂` and `Π₂` halves
- `sipserLautemann_of_subset_SigmaP` — the `Σ₂` half suffices, given that
  `BPP` is closed under complement
- `BPP_subset_SigmaP_two_of_sipserLautemann`,
  `BPP_subset_PiP_two_of_sipserLautemann` — the two halves
- `BPP_subset_PH_of_sipserLautemann` — `BPP ⊆ PH`
-/

@[expose] public section

namespace Complexity

/-- **Sipser–Lautemann**: bounded-error probabilistic polynomial time lies in
the second level of the polynomial hierarchy, `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ`.

Stated as a `Prop` so that results can depend on it explicitly. It is proved
unconditionally as `sipserLautemann` (via `sipserLautemann_of_verdictInFP` and
`matrixVerdictInFP`); `sipserLautemann_of_matrixInP` derives it from the
alternative `MatrixInP` interface. -/
def SipserLautemann : Prop :=
  BPP ⊆ SigmaP 2 ∩ PiP 2

/-- **The matrix-decidability interface.** For every machine and every
polynomial time bound, the quantifier-free matrix of the Lautemann
characterization is decidable in deterministic polynomial time.

A decider parses `pair (pair x w) r`, computes the per-trial step count
`pt.eval |x|` and the amplified seed length from it, decodes the shift tuple
and the seed, and for each shift runs the fixed machine on the shifted seed,
block by block, taking the majority verdict; all of this is polynomial in the
input length. Isolating it here keeps the probabilistic and combinatorial
content of the theorem free of machine engineering. -/
def MatrixInP : Prop :=
  ∀ (k : ℕ) (tm : NTM k) (pt : Polynomial ℕ) (b : Bool),
    Lautemann.matrixLang tm pt.eval b ∈ P

/-- **The matrix interface as a function statement.** For every machine and
every polynomial time bound, the matrix verdict is computable in deterministic
polynomial time.

This is the form to discharge: by `CobhamFP_eq_FP` it suffices to build the
verdict inside Cobham's algebra, with `NTM.choiceTM_simulates` supplying the
semantics of running the machine along given choice bits. -/
def MatrixVerdictInFP : Prop :=
  ∀ (k : ℕ) (tm : NTM k) (pt : Polynomial ℕ) (b : Bool),
    (fun z => [Lautemann.matrixVerdict tm pt.eval b z]) ∈ FP

/-- A polynomial-time verdict function gives the polynomial-time matrix
language. -/
theorem matrixInP_of_verdictInFP (h : MatrixVerdictInFP) : MatrixInP :=
  fun k tm pt b =>
    mem_P_of_decisionFn_bool (h k tm pt b)
      (fun z => Lautemann.mem_matrixLang_iff_verdict tm pt.eval b z)

/-- Every `BPP` language is in `Σ₂ᵖ`, given the matrix interface. -/
theorem mem_SigmaP_two_of_matrixInP (hmatrix : MatrixInP) {L : Language}
    (hL : L ∈ BPP) : L ∈ SigmaP 2 := by
  obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hL
  obtain ⟨k, tm, f, hhalt, haccept, hreject, hO⟩ := hd
  obtain ⟨pt, hpt⟩ := BigO.pow_polynomial_bound hO
  obtain ⟨hq, hp⟩ := Lautemann.boundPoly_bounds (f := pt.eval) (P := pt) (fun n => le_rfl)
  have haccept' : tm.AcceptsWithProb L pt.eval (2 / 3) :=
    NTM.acceptsWithProb_of_le hhalt hpt haccept
  have hreject' : tm.RejectsWithProb L pt.eval (1 / 3) :=
    NTM.rejectsWithProb_of_le hhalt hpt hreject
  have hEq := Lautemann.eq_polyExistsLang_of_boundedError haccept' hreject' hp hq
  show L ∈ SigmaP (1 + 1)
  rw [SigmaP_succ, PiP_one]
  exact ⟨(Lautemann.boundPoly pt + 1) * Lautemann.boundPoly pt, _,
    ⟨Lautemann.boundPoly pt, _, hmatrix k tm pt true, rfl⟩, hEq⟩

/-- Every `BPP` language is in `Π₂ᵖ`, given the matrix interface: the
complementary covering characterization puts the complement in `Σ₂ᵖ`. -/
theorem mem_PiP_two_of_matrixInP (hmatrix : MatrixInP) {L : Language}
    (hL : L ∈ BPP) : L ∈ PiP 2 := by
  obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hL
  obtain ⟨k, tm, f, hhalt, haccept, hreject, hO⟩ := hd
  obtain ⟨pt, hpt⟩ := BigO.pow_polynomial_bound hO
  obtain ⟨hq, hp⟩ := Lautemann.boundPoly_bounds (f := pt.eval) (P := pt) (fun n => le_rfl)
  have haccept' : tm.AcceptsWithProb L pt.eval (2 / 3) :=
    NTM.acceptsWithProb_of_le hhalt hpt haccept
  have hreject' : tm.RejectsWithProb L pt.eval (1 / 3) :=
    NTM.rejectsWithProb_of_le hhalt hpt hreject
  have hEq := Lautemann.compl_eq_polyExistsLang_of_boundedError haccept' hreject' hp hq
  show Lᶜ ∈ SigmaP (1 + 1)
  rw [SigmaP_succ, PiP_one]
  exact ⟨(Lautemann.boundPoly pt + 1) * Lautemann.boundPoly pt, _,
    ⟨Lautemann.boundPoly pt, _, hmatrix k tm pt false, rfl⟩, hEq⟩

/-- **The Sipser–Lautemann theorem**, given the matrix-decidability
interface: `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ`. -/
theorem sipserLautemann_of_matrixInP (hmatrix : MatrixInP) : SipserLautemann :=
  fun _ hL => ⟨mem_SigmaP_two_of_matrixInP hmatrix hL, mem_PiP_two_of_matrixInP hmatrix hL⟩

/-- **The Sipser–Lautemann theorem**, given the matrix interface in its
function form. -/
theorem sipserLautemann_of_verdictInFP (h : MatrixVerdictInFP) : SipserLautemann :=
  sipserLautemann_of_matrixInP (matrixInP_of_verdictInFP h)

/-- The statement splits into its two halves: containment in `Σ₂ᵖ` and
containment in `Π₂ᵖ`. -/
theorem sipserLautemann_iff : SipserLautemann ↔ BPP ⊆ SigmaP 2 ∧ BPP ⊆ PiP 2 :=
  Set.subset_inter_iff

/-- The `Σ₂ᵖ` half of the statement. -/
theorem BPP_subset_SigmaP_two_of_sipserLautemann (h : SipserLautemann) :
    BPP ⊆ SigmaP 2 :=
  fun _ hL => (h hL).1

/-- The `Π₂ᵖ` half of the statement. -/
theorem BPP_subset_PiP_two_of_sipserLautemann (h : SipserLautemann) :
    BPP ⊆ PiP 2 :=
  fun _ hL => (h hL).2

/-- The `Σ₂ᵖ` half implies the full statement, given that `BPP` is closed under
complement: a language of `BPP` lies in `Π₂ᵖ` exactly when its complement lies
in `Σ₂ᵖ`, and the complement is again a `BPP` language. -/
theorem sipserLautemann_of_subset_SigmaP (hcompl : ∀ L ∈ BPP, Lᶜ ∈ BPP)
    (h : BPP ⊆ SigmaP 2) : SipserLautemann :=
  fun L hL => ⟨h hL, h (hcompl L hL)⟩

/-- Sipser–Lautemann puts `BPP` inside the polynomial hierarchy. -/
theorem BPP_subset_PH_of_sipserLautemann (h : SipserLautemann) : BPP ⊆ PH :=
  fun _ hL => SigmaP_subset_PH 2 (h hL).1

/-- **The matrix interface holds.** The verdict is computed inside Cobham's
algebra — decode the triple with the payload scanners, build the trial count
and seed length as `smash` lengths from the time bound, and take the
disjunction over shift blocks of the majority vote over trial blocks, each
trial being one run of the machine along the choice bits of its block — and
`CobhamFP_eq_FP` makes that a polynomial-time function. -/
theorem matrixVerdictInFP : MatrixVerdictInFP :=
  fun _ tm pt b => Lautemann.matrixVerdict_mem_FP tm pt b

/-- **The Sipser–Lautemann theorem**: bounded-error probabilistic polynomial
time lies in the second level of the polynomial hierarchy,
`BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ` (Arora–Barak Theorem 7.15). -/
theorem sipserLautemann : SipserLautemann :=
  sipserLautemann_of_verdictInFP matrixVerdictInFP

/-- `BPP ⊆ Σ₂ᵖ`. -/
theorem BPP_subset_SigmaP_two : BPP ⊆ SigmaP 2 :=
  BPP_subset_SigmaP_two_of_sipserLautemann sipserLautemann

/-- `BPP ⊆ Π₂ᵖ`. -/
theorem BPP_subset_PiP_two : BPP ⊆ PiP 2 :=
  BPP_subset_PiP_two_of_sipserLautemann sipserLautemann

/-- **`BPP` lies inside the polynomial hierarchy.** -/
theorem BPP_subset_PH : BPP ⊆ PH :=
  BPP_subset_PH_of_sipserLautemann sipserLautemann

end Complexity
