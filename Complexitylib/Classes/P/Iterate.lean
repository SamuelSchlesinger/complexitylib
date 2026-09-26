/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
public import Complexitylib.Asymptotics.PolyBound
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Encoding.Pairing
import Complexitylib.Classes.P.Iterate.Internal

/-!
# Polynomial-time loops

Two ways of writing a loop whose every round is a polynomial-time string
function, and whose whole run is then polynomial-time too.

*Iteration* applies one step `F` a number of times given in unary, as the length
of a polynomial-time `ruler`. The loop is polynomial-time as long as no state
along the way grows beyond a polynomial in the input length. That bound can be
given as the length of a polynomial-time `width` string (`iterate_mem_FP`), as a
polynomial bound on natural numbers (`iterate_mem_FP_of_polyBound`), or, most
conveniently, as a constant bound on how much one step can add
(`iterate_mem_FP_of_step_le`). When the states encode values of another type and
the step computes a map on that type, the bound can be stated on the values
(`iterate_mem_FP_along`).

*A fold* reads a string bit by bit, from its last bit to its first, and updates
a state with one of two polynomial-time steps: `A` on a `false` bit and `B` on a
`true` bit. Each step sees a fixed workspace, the state built from the tail so
far, and the tail itself. The fold is polynomial-time as long as its states stay
polynomially short (`recFold_mem_FP_of_bound`). The statement takes the fold as
any function obeying the fold's equations, so the specification a caller has in
mind can be used directly.

Both are thin wrappers around Cobham's loop machines,
`Cobham.iterate_mem_FP` and `Cobham.recFoldClamp_mem_FP`, which clamp every
intermediate state to a prescribed width. The hypotheses here are what shows
that the clamp never fires.

## Main results

- `iterate_mem_FP` — iterating a step under a width given as a string
- `iterate_mem_FP_of_polyBound` — under a polynomial bound on the states
- `iterate_mem_FP_of_step_le` — when each step adds at most a constant
- `iterate_mem_FP_along` — with the bound stated on encoded values
- `recFold_mem_FP_of_bound` — a fold with polynomially short states
-/

public section

namespace Complexity

/-! ## Iteration -/

/-- **Iteration in `FP`.** If `F`, `init`, `ruler` and `width` are
polynomial-time and the first `|ruler z|` iterates of `F` from `init z` are never
longer than `width z`, then running `F` for `|ruler z|` rounds from `init z` is
polynomial-time. -/
theorem iterate_mem_FP {F init ruler width : List Bool → List Bool}
    (hF : F ∈ FP) (hinit : init ∈ FP) (hruler : ruler ∈ FP) (hwidth : width ∈ FP)
    (hbound : ∀ z, ∀ n ≤ (ruler z).length,
      (F^[n] (init z)).length ≤ (width z).length) :
    (fun z => F^[(ruler z).length] (init z)) ∈ FP :=
  Cobham.iterate_mem_FP hF hinit hruler hwidth hbound

/-- **Iteration under a polynomial bound.** `iterate_mem_FP` with the states
bounded by a polynomial bound `B` in the input length instead of a width
string. -/
theorem iterate_mem_FP_of_polyBound {F init ruler : List Bool → List Bool}
    (hF : F ∈ FP) (hinit : init ∈ FP) (hruler : ruler ∈ FP) {B : ℕ → ℕ}
    (hB : PolyBound B)
    (hbound : ∀ z, ∀ n ≤ (ruler z).length, (F^[n] (init z)).length ≤ B z.length) :
    (fun z => F^[(ruler z).length] (init z)) ∈ FP := by
  obtain ⟨p, hp⟩ := hB
  obtain ⟨R, hR, hRlen⟩ := Cobham.exists_ruler p
  exact Cobham.iterate_mem_FP hF hinit hruler hR fun z n hn =>
    (hbound z n hn).trans ((hp _).trans (hRlen z))

/-- **Iteration of a step that grows by a bounded amount.** If each of the first
`|ruler z|` rounds adds at most `c` bits to the state, then the loop is
polynomial-time: the start and the number of rounds are both polynomially
bounded, because they are outputs of polynomial-time functions. -/
theorem iterate_mem_FP_of_step_le {F init ruler : List Bool → List Bool}
    (hF : F ∈ FP) (hinit : init ∈ FP) (hruler : ruler ∈ FP) (c : ℕ)
    (hstep : ∀ z, ∀ n < (ruler z).length,
      (F^[n + 1] (init z)).length ≤ (F^[n] (init z)).length + c) :
    (fun z => F^[(ruler z).length] (init z)) ∈ FP := by
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP hinit
  obtain ⟨q, hq⟩ := Cobham.output_length_poly_of_mem_FP hruler
  refine iterate_mem_FP_of_polyBound hF hinit hruler
    ((PolyBound.eval p).add ((PolyBound.const c).mul (PolyBound.eval q))) fun z n hn => ?_
  have h1 := iterate_length_le_of_step_le (hstep z) n hn
  have h2 := hp z
  have h3 : c * n ≤ c * q.eval z.length := Nat.mul_le_mul_left c (hn.trans (hq z))
  show _ ≤ p.eval z.length + c * q.eval z.length
  omega

/-- **Iteration along an encoding.** Suppose the step `F` computes a map `T` on
encoded values, `F (enc a) = enc (T a)`, and `init` always writes an encoded
value. Then the bound `iterate_mem_FP` asks for can be stated on the values: the
encodings of the first `|ruler z|` iterates of `T` from the start are never longer
than `width z`. The iterate of `F` then writes the iterate of `T`, by
`Function.Semiconj.iterate_right`. -/
theorem iterate_mem_FP_along {α : Type*} (enc : α → List Bool) {T : α → α}
    {F init ruler width : List Bool → List Bool}
    (hF : F ∈ FP) (hinit : init ∈ FP) (hruler : ruler ∈ FP) (hwidth : width ∈ FP)
    (hstep : ∀ a, F (enc a) = enc (T a))
    (hinit_enc : ∀ z, ∃ a, init z = enc a)
    (hbound : ∀ z a, init z = enc a → ∀ n ≤ (ruler z).length,
      (enc (T^[n] a)).length ≤ (width z).length) :
    (fun z => F^[(ruler z).length] (init z)) ∈ FP := by
  refine iterate_mem_FP hF hinit hruler hwidth fun z n hn => ?_
  obtain ⟨a, ha⟩ := hinit_enc z
  have hsemi : Function.Semiconj enc T F := fun a => (hstep a).symm
  rw [ha, ← hsemi.iterate_right n a]
  exact hbound z a ha n hn

/-! ## Folds -/

/-- **A fold with polynomially short states is polynomial-time.** Let `g z t` be
the fold over the bits of `t` that starts from `E z` and, reading the bit `b` in
front of a tail `t`, applies `A` (if `b` is `false`) or `B` (if `b` is `true`) to
`pair (pair (w z) (g z t)) t`: the workspace `w z`, the state built from the
tail, and the tail itself. If `A`, `B`, `E`, `w` and `s` are polynomial-time and
the fold's state on every suffix of `s z` is polynomially short in `|z|`, then
folding over `s z` is polynomial-time.

The fold is any `g` obeying the three equations, so a caller can supply the
function it wants computed and check the equations for it. -/
theorem recFold_mem_FP_of_bound {A B E w s : List Bool → List Bool}
    {g : List Bool → List Bool → List Bool}
    (hA : A ∈ FP) (hB : B ∈ FP) (hE : E ∈ FP) (hw : w ∈ FP) (hs : s ∈ FP)
    (hnil : ∀ z, g z [] = E z)
    (hfalse : ∀ z t, g z (false :: t) = A (pair (pair (w z) (g z t)) t))
    (htrue : ∀ z t, g z (true :: t) = B (pair (pair (w z) (g z t)) t))
    {bound : ℕ → ℕ} (hbound : PolyBound bound)
    (hle : ∀ z t, t <:+ s z → (g z t).length ≤ bound z.length) :
    (fun z => g z (s z)) ∈ FP :=
  recFold_mem_FP_of_bound_internal hA hB hE hw hs hnil hfalse htrue hbound hle

end Complexity
