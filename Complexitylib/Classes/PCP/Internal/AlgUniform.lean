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
length uniformly over inputs of a given length, and `p |x|` marks are written by
`UnaryFn.polyEval`.

## Main results

- `Complexity.exists_padRuler` — a uniform, computable padding size
- `Complexity.polyBounded_eval` — a polynomial's values are polynomially bounded
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
  refine ⟨fun x => List.replicate ((Polynomial.C c * p).eval x.length) true, Polynomial.C c * p,
    UnaryFn.polyEval _ (UnaryFn.length id_mem_FP), fun x => by rw [List.length_replicate],
    fun x => List.length_replicate .., fun x => ?_⟩
  rw [List.length_replicate, Polynomial.eval_mul, Polynomial.eval_C]
  exact Nat.mul_le_mul_left c (hp x)

/-- A polynomial's own values are polynomially bounded. -/
theorem polyBounded_eval (p : Polynomial ℕ) : PolyBounded fun n => p.eval n :=
  (PolyBound.eval p).exists_mul_pow_bound

end Complexity
