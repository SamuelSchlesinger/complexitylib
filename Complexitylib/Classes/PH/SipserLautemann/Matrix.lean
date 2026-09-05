/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PH
public import Complexitylib.Classes.P.Cobham.Internal.BlockScan
public import Complexitylib.Classes.PH.SipserLautemann.Amplified
public import Complexitylib.Classes.PH.SipserLautemann.Encode
public import Complexitylib.Classes.PH.SipserLautemann.TimeBound

/-!
# The Lautemann matrix language and the `Σ₂` form

The `∃∀` characterization of
`Complexitylib.Classes.PH.SipserLautemann.Amplified` quantifies over shift
tuples and seeds; the polynomial hierarchy quantifies over bitstrings. This
file bridges the two: `matrixLang` is the innermost, quantifier-free predicate
as a language of encoded triples, and `eq_polyExistsLang_polyForallLang` says
that a bounded-error language is literally a polynomially bounded `∃∀` over it.

Both the language and the identity are stated for a general time-bound
function `f`, but the intended instance takes `f` to be the evaluation of a
polynomial — see `NTM.acceptsWithProb_of_le`, which replaces a machine's
arbitrary halting bound by a dominating polynomial. That is what makes the
matrix predicate computable: a decider must recover the per-trial step count
from the input length, which it can do when the count is a fixed polynomial in
`|x|`, and cannot do for an arbitrary `f`.

## Main definitions

- `matrixLang tm f b` — on `pair (pair x w) r`: the decoded shifts of the
  decoded seed contain one whose amplified majority verdict is `b`
- `boundPoly` — the polynomial bounding the amplified seed length

## Main results

- `mem_matrixLang_pair` — membership on an encoded triple
- `eq_polyExistsLang_polyForallLang` — the `Σ₂` form of a bounded-error
  language, and `compl_eq_polyExistsLang_polyForallLang` for its complement
- `boundPoly_bounds` — the amplified lengths are polynomially bounded
-/

@[expose] public section

namespace Complexity

namespace Lautemann

variable {k : ℕ}

/-! ## The matrix language -/

/-- The quantifier-free predicate of the Lautemann characterization, on the
three decoded components. -/
def matrixPred (tm : NTM k) (f : ℕ → ℕ) (b : Bool) (x w r : List Bool) : Prop :=
  r.length = ampRuns f x.length * f x.length →
    ∃ i : Fin (ampShifts f x.length),
      blockMajority (NTM.repeatAcceptEvent tm x (f x.length))
        (shift (seedOfList (ampRuns f x.length * f x.length) r)
          (shiftsOfList (ampShifts f x.length)
            (ampRuns f x.length * f x.length) w i)) = b

/-- The same predicate as a `Bool`-valued verdict. -/
noncomputable def matrixVerdictOn (tm : NTM k) (f : ℕ → ℕ) (b : Bool) (x w r : List Bool) :
    Bool :=
  if r.length = ampRuns f x.length * f x.length then
    decide (∃ i : Fin (ampShifts f x.length),
      blockMajority (NTM.repeatAcceptEvent tm x (f x.length))
        (shift (seedOfList (ampRuns f x.length * f x.length) r)
          (shiftsOfList (ampShifts f x.length)
            (ampRuns f x.length * f x.length) w i)) = b)
  else true

/-- The verdict decides the predicate. -/
theorem matrixVerdictOn_eq_true_iff (tm : NTM k) (f : ℕ → ℕ) (b : Bool) (x w r : List Bool) :
    matrixVerdictOn tm f b x w r = true ↔ matrixPred tm f b x w r := by
  rw [matrixVerdictOn, matrixPred]
  by_cases h : r.length = ampRuns f x.length * f x.length
  · rw [ite_eq_left h]
    simp [h]
  · rw [ite_eq_right h]
    simp [h]

/-- The innermost predicate of the Lautemann characterization, as a language of
encoded triples. The components are decoded with the polynomial-time payload
scanners `pairFst` and `pairSnd`, which recover them from a
canonical pair; on malformed input the decoders return their partial reads, and
the language's contents there are irrelevant to the `Σ₂` identity below. -/
def matrixLang (tm : NTM k) (f : ℕ → ℕ) (b : Bool) : Language :=
  {z | matrixPred tm f b (pairFst (pairFst z))
    (pairSnd (pairFst z)) (pairSnd z)}

/-- Membership of an encoded triple in the matrix language. -/
theorem mem_matrixLang_pair (tm : NTM k) (f : ℕ → ℕ) (b : Bool) (x w r : List Bool) :
    pair (pair x w) r ∈ matrixLang tm f b ↔ matrixPred tm f b x w r := by
  rw [matrixLang]
  simp

/-- The matrix as a `Bool`-valued verdict function, so that the remaining
polynomial-time obligation is about a *function*, which
`Complexitylib.Classes.P.Cobham` can discharge inside Cobham's algebra without
constructing a machine. -/
noncomputable def matrixVerdict (tm : NTM k) (f : ℕ → ℕ) (b : Bool) (z : List Bool) : Bool :=
  matrixVerdictOn tm f b (pairFst (pairFst z))
    (pairSnd (pairFst z)) (pairSnd z)

/-- The verdict function on an encoded triple. -/
@[simp] theorem matrixVerdict_pair (tm : NTM k) (f : ℕ → ℕ) (b : Bool) (x w r : List Bool) :
    matrixVerdict tm f b (pair (pair x w) r) = matrixVerdictOn tm f b x w r := by
  rw [matrixVerdict]
  simp

/-- The verdict function decides the matrix language. -/
theorem mem_matrixLang_iff_verdict (tm : NTM k) (f : ℕ → ℕ) (b : Bool) (z : List Bool) :
    z ∈ matrixLang tm f b ↔ matrixVerdict tm f b z = true := by
  rw [matrixLang, matrixVerdict, matrixVerdictOn_eq_true_iff]
  rfl

/-! ## The `Σ₂` form -/

/-- **The `Σ₂` form of a covering characterization.** Given a family of events
whose covering-by-shifts characterizes a language `A`, that language is a
polynomially bounded existential over a polynomially bounded universal over
the matrix language. The existential witness encodes a covering tuple of
shifts, and the universal variable ranges over seeds. -/
theorem eq_polyExistsLang_polyForallLang {tm : NTM k} {f : ℕ → ℕ} {b : Bool}
    {A : Language}
    (E : ∀ x : List Bool, Finset (Fin (ampRuns f x.length * f x.length) → Bool))
    (hmem : ∀ (x : List Bool) (w : Fin (ampRuns f x.length * f x.length) → Bool),
      w ∈ E x ↔ blockMajority (NTM.repeatAcceptEvent tm x (f x.length)) w = b)
    (hA : ∀ x : List Bool, x ∈ A ↔ ∃ u : Fin (ampShifts f x.length) →
        Fin (ampRuns f x.length * f x.length) → Bool, Covers (E x) u)
    {p q : Polynomial ℕ}
    (hp : ∀ n, ampShifts f n * (ampRuns f n * f n) ≤ p.eval n)
    (hq : ∀ n, ampRuns f n * f n ≤ q.eval n) :
    A = polyExistsLang p (polyForallLang q (matrixLang tm f b)) := by
  ext x
  rw [hA x]
  simp only [mem_polyExistsLang, mem_polyForallLang]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨listOfShifts u, ?_, ?_⟩
    · rw [length_listOfShifts]
      exact hp x.length
    · intro r _
      rw [mem_matrixLang_pair]
      intro hrlen
      obtain ⟨i, hi⟩ := hu (seedOfList (ampRuns f x.length * f x.length) r)
      rw [hmem] at hi
      exact ⟨i, by simpa using hi⟩
  · rintro ⟨w, _, hw⟩
    refine ⟨shiftsOfList (ampShifts f x.length) (ampRuns f x.length * f x.length) w, ?_⟩
    intro s
    have hxle : x.length ≤ (pair x w).length := by
      rw [pair_length]
      omega
    have hlen : (listOfSeed s).length ≤ q.eval (pair x w).length := by
      rw [length_listOfSeed]
      exact le_trans (hq x.length) (polynomial_eval_mono_nat q hxle)
    have hmatrix := hw (listOfSeed s) hlen
    rw [mem_matrixLang_pair] at hmatrix
    obtain ⟨i, hi⟩ := hmatrix (by simp)
    refine ⟨i, ?_⟩
    rw [hmem]
    simpa using hi

/-- The `Σ₂` form of a bounded-error language: `L` itself. -/
theorem eq_polyExistsLang_of_boundedError {tm : NTM k} {L : Language} {f : ℕ → ℕ}
    (haccept : tm.AcceptsWithProb L f (2 / 3)) (hreject : tm.RejectsWithProb L f (1 / 3))
    {p q : Polynomial ℕ}
    (hp : ∀ n, ampShifts f n * (ampRuns f n * f n) ≤ p.eval n)
    (hq : ∀ n, ampRuns f n * f n ≤ q.eval n) :
    L = polyExistsLang p (polyForallLang q (matrixLang tm f true)) :=
  eq_polyExistsLang_polyForallLang (fun x => ampEvent tm f x)
    (fun x w => mem_ampEvent tm f x w) (mem_iff_exists_covers haccept hreject) hp hq

/-- The `Σ₂` form of a bounded-error language: its complement. -/
theorem compl_eq_polyExistsLang_of_boundedError {tm : NTM k} {L : Language} {f : ℕ → ℕ}
    (haccept : tm.AcceptsWithProb L f (2 / 3)) (hreject : tm.RejectsWithProb L f (1 / 3))
    {p q : Polynomial ℕ}
    (hp : ∀ n, ampShifts f n * (ampRuns f n * f n) ≤ p.eval n)
    (hq : ∀ n, ampRuns f n * f n ≤ q.eval n) :
    Lᶜ = polyExistsLang p (polyForallLang q (matrixLang tm f false)) :=
  eq_polyExistsLang_polyForallLang (fun x => (ampEvent tm f x)ᶜ)
    (fun x w => mem_compl_ampEvent tm f x w)
    (fun x => notMem_iff_exists_covers_compl haccept hreject x) hp hq

/-! ## Polynomial bounds -/

/-- The polynomial bounding the amplified seed length, given a polynomial `P`
dominating the machine's time bound. -/
noncomputable def boundPoly (P : Polynomial ℕ) : Polynomial ℕ :=
  (Polynomial.C 12 * P + Polynomial.C 133) * P

@[simp] theorem boundPoly_eval (P : Polynomial ℕ) (n : ℕ) :
    (boundPoly P).eval n = (12 * P.eval n + 133) * P.eval n := by
  simp [boundPoly]

/-- The amplified seed length is bounded by `boundPoly P`, and the amplified
witness length by `(boundPoly P + 1) * boundPoly P`. -/
theorem boundPoly_bounds {f : ℕ → ℕ} {P : Polynomial ℕ} (hf : ∀ n, f n ≤ P.eval n) :
    (∀ n, ampRuns f n * f n ≤ (boundPoly P).eval n) ∧
      (∀ n, ampShifts f n * (ampRuns f n * f n) ≤
        ((boundPoly P + 1) * boundPoly P).eval n) := by
  have hseed : ∀ n, ampRuns f n * f n ≤ (boundPoly P).eval n := by
    intro n
    rw [boundPoly_eval]
    have hr : ampRuns f n = 12 * f n + 133 := by simp [ampRuns, ampExp]; ring
    rw [hr]
    exact Nat.mul_le_mul (by have := hf n; omega) (hf n)
  refine ⟨hseed, fun n => ?_⟩
  have hs : ampShifts f n = ampRuns f n * f n + 1 := rfl
  rw [hs, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one]
  exact Nat.mul_le_mul (by have := hseed n; omega) (hseed n)

end Lautemann

end Complexity
