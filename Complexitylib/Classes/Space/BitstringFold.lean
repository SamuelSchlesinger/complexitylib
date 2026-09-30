/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Space.BitstringFold.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Encoding.Pairing
import Complexitylib.Classes.Space.BitstringFold.Internal

/-!
# Polynomial-space ordered folds over bitstrings

`SpaceIter.mem_PSPACE_of_bitstring_fold` folds over exponentially many
fixed-width candidates using a polynomial-time update and a polynomial-size
accumulator. Every prefix accumulator, including the seed and final value,
must satisfy the stated bound. A polynomial-time test of the result defines
a language in `PSPACE`.

Candidates have exactly `w.eval x.length` bits and are visited in increasing
little-endian numeric order. There is one candidate even at width zero. Empty
accumulators are allowed, and no algebraic laws on the update are required.

The proof uses `initializedStep` and `SpaceIter.mem_PSPACE_of_iterate`. Its
packed states have length at most `4*W + 2*V + |x| + 22`, and completion is
signalled at iteration `2^W + 1`. This is a depth-one exponential fold; a
polynomial-depth game-tree evaluator still requires a stack construction.
-/

@[expose] public section

namespace Complexity.SpaceIter

/-- An ordered fold over all polynomial-width bitstrings is computable for
decision purposes in polynomial space. The update receives `pair x (pair c a)`;
the final test receives `pair x a`. All accumulator prefixes must be short. -/
theorem mem_PSPACE_of_bitstring_fold {seed : List Bool → List Bool}
    {update : List Bool → List Bool → List Bool → List Bool}
    {accept : List Bool → List Bool → Bool} (w v : Polynomial ℕ) (hs : seed ∈ FP)
    (hu : (fun z => update (pairFst z) (pairFst (pairSnd z))
      (pairSnd (pairSnd z))) ∈ FP)
    (ha : (fun z => [accept (pairFst z) (pairSnd z)]) ∈ FP)
    (hbound : ∀ x i, i ≤ 2 ^ w.eval x.length →
      (bitstringFoldPrefix (update x) (seed x) (w.eval x.length) i).length ≤
        v.eval x.length) :
    {x | accept x (bitstringFold (update x) (seed x) (w.eval x.length)) = true} ∈ PSPACE :=
  BitstringFold.mem_PSPACE_internal w v hs hu ha hbound

/-- Fixed-width witness search is the Boolean-OR instance of the ordered fold.
The polynomial-time predicate receives `pair x candidate`; width zero tests `[]`. -/
theorem mem_PSPACE_of_exists_bitstring {p : List Bool → List Bool → Bool}
    (w : Polynomial ℕ) (hp : (fun z => [p (pairFst z) (pairSnd z)]) ∈ FP) :
    {x | ∃ c, c.length = w.eval x.length ∧ p x c = true} ∈ PSPACE :=
  BitstringFold.exists_bitstring_mem_PSPACE_internal w hp

/-! Small kernel-checked examples fix the order and boundary conventions. -/

-- Appending candidates is order-sensitive: 00, 10, 01, 11 in little-endian order.
example : bitstringFold (fun c a => a ++ c) [] 2 =
    [false, false, true, false, false, true, true, true] := by decide

-- Width zero processes its one candidate even from an empty accumulator.
example : bitstringFold (fun _ _ => [true]) [] 0 = [true] := rfl

-- An empty result remains a legitimate value, rather than an initialization sentinel.
example : bitstringFold (fun _ _ => []) [] 2 = [] := rfl

-- The fold theorem has concrete instances with an empty accumulator and either verdict.
example (answer : Bool) : {_x : List Bool | answer = true} ∈ PSPACE := by
  have h := mem_PSPACE_of_bitstring_fold (seed := fun _ => [])
    (update := fun _ _ _ => []) (accept := fun _ _ => answer) (2 : Polynomial ℕ) 0
    (constFn_mem_FP []) (constFn_mem_FP []) (constFn_mem_FP [answer])
    (fun _ i _ => by cases i <;> simp [bitstringFoldPrefix])
  exact h

-- A concrete search predicate, with input-dependent width and a one-bit accumulator.
example : {x | ∃ c : List Bool, c.length = x.length ∧ c.headD false = true} ∈ PSPACE := by
  simpa only [Polynomial.eval_X] using
    mem_PSPACE_of_exists_bitstring (p := fun _ c => c.headD false) Polynomial.X
      (BitstringFold.head_mem_FP pairSnd_mem_FP)

end Complexity.SpaceIter
