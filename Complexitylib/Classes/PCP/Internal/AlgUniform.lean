/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.NormalForm
public import Complexitylib.Classes.PCP.Internal.UnaryList
public import Complexitylib.SAT.Encoding
public import Complexitylib.Classes.Containments.Internal.LogSpaceBound

/-!
# A size that only the length decides

A `PCP` verifier's coin count is a function of the input's *length*. The graph
it reads therefore has to have a size the length alone decides, which the graph
of a formula does not. The remedy is to pad every graph up to one common size —
and for that one needs a size that is both computable and large enough for every
input of that length.

Any `FP` function has one: a machine that runs in time `p` writes at most
`p |x|` bits (`Cobham.output_length_poly_of_mem_FP`), so `p` bounds the output
length uniformly over inputs of a given length, and `Cobham.exists_exact_ruler`
writes `p |x|` marks.

## Main results

- `Complexity.exists_padRuler` — a uniform, computable padding size
-/

@[expose] public section

namespace Complexity

/-- A formula is no longer than its encoding. -/
theorem length_le_length_encode (φ : SAT.CNF) : φ.length ≤ φ.encode.length := by
  induction φ with
  | nil => simp
  | cons c cs ih =>
      rw [SAT.CNF.encode_cons, List.length_cons, List.length_append, List.length_append]
      simp only [List.length_cons, List.length_nil]
      omega

/-- **A uniform padding size**: marks, as many as any input of that length can
force, and as many for one input as for any other of the same length. -/
theorem exists_padRuler {f : List Bool → List Bool} (hf : f ∈ FP) (c : ℕ) :
    ∃ (padU : List Bool → List Bool) (q : Polynomial ℕ), padU ∈ FP
      ∧ (∀ x, padU x = List.replicate (padU x).length true)
      ∧ (∀ x, (padU x).length = q.eval x.length)
      ∧ ∀ x, c * (f x).length ≤ (padU x).length := by
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP hf
  obtain ⟨R, hR, hRlen⟩ := Cobham.exists_exact_ruler (Polynomial.C c * p)
  refine ⟨fun z => marks (R z), Polynomial.C c * p, marks_mem_FP hR, fun x => ?_, ?_, ?_⟩
  · show marks (R x) = List.replicate (marks (R x)).length true
    rw [marks_eq, List.length_replicate]
  · intro x
    show (marks (R x)).length = _
    rw [marks_eq, List.length_replicate, hRlen]
  · intro x
    show c * (f x).length ≤ (marks (R x)).length
    rw [marks_eq, List.length_replicate, hRlen, Polynomial.eval_mul, Polynomial.eval_C]
    exact Nat.mul_le_mul_left c (hp x)

/-! ### Rulers, structurally

Writing a polynomial out and evaluating it is unworkable here: the constants
involved are the alphabet's constraint count and the round's growth factor, and
no tactic may be allowed near them. So the width is built from closure
properties instead — a sum of rulers is an append, a product is a length
multiplication — and no arithmetic is ever performed on a constant. -/

/-- A function of the input's length that an `FP` string is long enough for. -/
def HasRuler (f : ℕ → ℕ) : Prop :=
  ∃ R : List Bool → List Bool, R ∈ FP ∧ ∀ z : List Bool, f z.length ≤ (R z).length

/-- A polynomial's own values are polynomially bounded. -/
theorem polyBounded_eval (p : Polynomial ℕ) : PolyBounded fun n => p.eval n := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i, p.natDegree, fun n => ?_⟩
  show p.eval n ≤ _
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ p.natDegree := by
    rw [Finset.mem_range] at hi
    omega
  exact Nat.mul_le_mul_left _
    (le_trans (Nat.pow_le_pow_left (by omega) i) (Nat.pow_le_pow_right (by omega) hi'))

namespace HasRuler

theorem of_poly (p : Polynomial ℕ) : HasRuler fun n => p.eval n := Cobham.exists_ruler p

theorem const (c : ℕ) : HasRuler fun _ => c :=
  ⟨fun _ => List.replicate c false, constFn_mem_FP _, fun _ => by rw [List.length_replicate]⟩

theorem mono {f g : ℕ → ℕ} (hg : HasRuler g) (h : ∀ n, f n ≤ g n) : HasRuler f := by
  obtain ⟨R, hR, hlen⟩ := hg
  exact ⟨R, hR, fun z => le_trans (h z.length) (hlen z)⟩

theorem add {f g : ℕ → ℕ} (hf : HasRuler f) (hg : HasRuler g) :
    HasRuler fun n => f n + g n := by
  obtain ⟨R, hR, hRlen⟩ := hf
  obtain ⟨S, hS, hSlen⟩ := hg
  refine ⟨fun z => R z ++ S z, Cobham.appendFn_mem_FP hR hS, fun z => ?_⟩
  rw [List.length_append]
  exact Nat.add_le_add (hRlen z) (hSlen z)

theorem mul {f g : ℕ → ℕ} (hf : HasRuler f) (hg : HasRuler g) :
    HasRuler fun n => f n * g n := by
  obtain ⟨R, hR, hRlen⟩ := hf
  obtain ⟨S, hS, hSlen⟩ := hg
  refine ⟨fun z => List.replicate ((R z).length * (S z).length) false,
    Cobham.mulLenFn_mem_FP hR hS, fun z => ?_⟩
  rw [List.length_replicate]
  exact Nat.mul_le_mul (hRlen z) (hSlen z)

theorem pow {f : ℕ → ℕ} (hf : HasRuler f) (d : ℕ) : HasRuler fun n => f n ^ d := by
  induction d with
  | zero => exact mono (const 1) fun n => by rw [pow_zero]
  | succ d ih => exact mono (mul ih hf) fun n => by rw [pow_succ]

end HasRuler

end Complexity
