/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
public import Complexitylib.Asymptotics.PolyBound
public import Complexitylib.Classes.P.Cobham.Internal
public import Complexitylib.Classes.P.Composition
public import Complexitylib.Classes.P.PairWithInput

/-!
# Polynomial-time loops — proof internals

The helper facts behind `Complexitylib.Classes.P.Iterate`. The two machines are
Cobham's: `Cobham.iterate_mem_FP` runs a step under a width clamp, and
`Cobham.recFoldClamp_mem_FP` runs a fold with every intermediate value truncated.
What is proved here is that the clamps never fire under the hypotheses the
surface statements ask for, and how to feed a fold with an arbitrary workspace
and an arbitrary string to fold over.

## Contents

- `iterate_length_le_of_step_le` — per-step growth adds up along an orbit
- `recFoldClamp_eq_of_eqns` — a clamped fold computes any function obeying the
  fold's equations, as long as that function's values on the suffixes fit
- `foldUnpack` — the step argument the fold hands over, with a workspace that
  also carries the input, rewritten to the workspace the caller asked for
- `recFold_mem_FP_of_bound_internal` — the fold with a polynomially short state
-/

@[expose] public section

namespace Complexity

/-! ## Iterating a step that grows by a bounded amount -/

/-- If each of the first `N` steps adds at most `c` bits, then after `m ≤ N` steps
the state is at most `c * m` bits longer than the start. -/
theorem iterate_length_le_of_step_le {F : List Bool → List Bool} {x : List Bool}
    {N c : ℕ} (hstep : ∀ n < N, (F^[n + 1] x).length ≤ (F^[n] x).length + c) :
    ∀ m ≤ N, (F^[m] x).length ≤ x.length + c * m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      intro hm
      have h1 := hstep m (by omega)
      have h2 := ih (by omega)
      rw [Nat.mul_succ]
      omega

/-! ## Folds whose values stay short -/

/-- **A clamped fold computes its specification.** If `f` obeys the equations of
the fold of `A` (on a `false` bit) and `B` (on a `true` bit) from `e` with
workspace `W`, and `f` is at most `bound` bits long on every suffix of `s`, then
the fold clamped to `bound` bits computes `f s`: the truncation never fires. -/
theorem recFoldClamp_eq_of_eqns {A B : List Bool → List Bool} {bound : ℕ}
    {e W : List Bool} {f : List Bool → List Bool} (s : List Bool)
    (hnil : f [] = e)
    (hfalse : ∀ t, f (false :: t) = A (pair (pair W (f t)) t))
    (htrue : ∀ t, f (true :: t) = B (pair (pair W (f t)) t))
    (hle : ∀ t, t <:+ s → (f t).length ≤ bound) :
    Cobham.recFoldClamp A B bound e W s = f s := by
  induction s with
  | nil =>
      have h := hle [] List.suffix_rfl
      rw [hnil] at h
      rw [Cobham.recFoldClamp, hnil]
      exact List.take_of_length_le h
  | cons b t ih =>
      have htail : Cobham.recFoldClamp A B bound e W t = f t :=
        ih fun u hu => hle u (hu.trans (List.suffix_cons b t))
      have h := hle (b :: t) List.suffix_rfl
      rw [Cobham.recFoldClamp, htail]
      cases b with
      | false =>
          rw [hfalse] at h ⊢
          exact List.take_of_length_le h
      | true =>
          rw [htrue] at h ⊢
          exact List.take_of_length_le h

/-- The fold of `recFold_mem_FP_of_bound_internal` runs with the workspace
`pair W z`, so that the start can read the input `z`. Each step first rewrites
its argument `pair (pair (pair W z) acc) t` to `pair (pair W acc) t`, the argument
the caller's step expects. -/
def foldUnpack (y : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst (pairFst y))) (pairSnd (pairFst y))) (pairSnd y)

theorem foldUnpack_pair (W z acc t : List Bool) :
    foldUnpack (pair (pair (pair W z) acc) t) = pair (pair W acc) t := by
  rw [foldUnpack, pairFst_pair, pairFst_pair, pairFst_pair, pairSnd_pair, pairSnd_pair]

theorem foldUnpack_mem_FP : foldUnpack ∈ FP := by
  have h1 : (fun y : List Bool => pairFst (pairFst (pairFst y))) ∈ FP :=
    mem_FP_comp (mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP)
      Cobham.fstBlock_mem_FP
  have h2 : (fun y : List Bool => pairSnd (pairFst y)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  exact Cobham.pairFn_mem_FP (Cobham.pairFn_mem_FP h1 h2) Cobham.sndBlock_mem_FP

/-- **A fold with a polynomially short state is polynomial-time.** The value is
Cobham's clamped fold, run on `pair (pair (w z) z) (s z)` with the steps
precomposed with `foldUnpack` and a clamp polynomial in the length of that
argument. The clamp never fires (`recFoldClamp_eq_of_eqns`), because the length
of the argument is at least `|z|`. -/
theorem recFold_mem_FP_of_bound_internal {A B E w s : List Bool → List Bool}
    {g : List Bool → List Bool → List Bool}
    (hA : A ∈ FP) (hB : B ∈ FP) (hE : E ∈ FP) (hw : w ∈ FP) (hs : s ∈ FP)
    (hnil : ∀ z, g z [] = E z)
    (hfalse : ∀ z t, g z (false :: t) = A (pair (pair (w z) (g z t)) t))
    (htrue : ∀ z t, g z (true :: t) = B (pair (pair (w z) (g z t)) t))
    {bound : ℕ → ℕ} (hbound : PolyBound bound)
    (hle : ∀ z t, t <:+ s z → (g z t).length ≤ bound z.length) :
    (fun z => g z (s z)) ∈ FP := by
  obtain ⟨p, hp⟩ := hbound
  have hE' : (fun y : List Bool => E (pairSnd (pairFst y))) ∈ FP :=
    mem_FP_comp (mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP) hE
  have hfold := Cobham.recFoldClamp_mem_FP (mem_FP_comp foldUnpack_mem_FP hA)
    (mem_FP_comp foldUnpack_mem_FP hB) hE' p
  have harg : (fun z : List Bool => pair (pair (w z) z) (s z)) ∈ FP :=
    Cobham.pairFn_mem_FP (mem_FP_pairWithInput hw) hs
  have heq : (fun y : List Bool => Cobham.recFoldClamp (A ∘ foldUnpack) (B ∘ foldUnpack)
        (p.eval y.length) (E (pairSnd (pairFst y))) (pairFst y) (pairSnd y))
      ∘ (fun z : List Bool => pair (pair (w z) z) (s z)) = fun z => g z (s z) := by
    funext z
    simp only [Function.comp_apply, pairFst_pair, pairSnd_pair]
    refine recFoldClamp_eq_of_eqns (s z) (hnil z) (fun t => ?_) (fun t => ?_)
      (fun t ht => ?_)
    · rw [hfalse, Function.comp_apply, foldUnpack_pair]
    · rw [htrue, Function.comp_apply, foldUnpack_pair]
    · refine (hle z t ht).trans ((hp _).trans (polynomial_eval_mono_nat p ?_))
      rw [pair_length, pair_length]
      omega
  rw [← heq]
  exact mem_FP_comp harg hfold

end Complexity
