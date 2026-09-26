/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Preimage
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Classes.P.FinsetDomain
public import Complexitylib.Languages.Contains

/-!
# From a polynomial-time decision function to membership in `P`

A language whose verdict is computed by a polynomial-time *function* is in
`P`. This is the bridge that lets a development establish membership in `P`
by exhibiting a function — in particular by building one in Cobham's algebra,
where `Complexitylib.Classes.P.Cobham` supplies `CobhamFP_eq_FP` — instead of
constructing a decider machine by hand.

The proof reads the verdict off the output through the polynomial-time
language `Language.containsOne`: a verdict string is accepted exactly when it
contains a `1`, and `P` is closed under polynomial-time preimages.

## Main results

- `mem_P_of_decisionFn` — a verdict function in `FP` puts its language in `P`
- `mem_P_of_decisionFn_bool` — the same with a `Bool`-valued verdict
- `FPPred.mem_P` — a language whose membership test is `FPPred` is in `P`
- `mem_P_of_bounded_key` — a test of a bounded polynomial-time key decides a
  language in `P`
-/

@[expose] public section

namespace Complexity

/-- **A polynomial-time verdict function decides a polynomial-time language.**
If `f ∈ FP` and `x ∈ L` exactly when `f x` contains a `1`-bit, then `L ∈ P`. -/
theorem mem_P_of_decisionFn {f : List Bool → List Bool} {L : Language}
    (hf : f ∈ FP) (hL : ∀ x, x ∈ L ↔ ∃ b ∈ f x, b = true) : L ∈ P := by
  have hpre : L = f ⁻¹' Language.containsOne := by
    ext x
    rw [Set.mem_preimage, Language.mem_containsOne]
    exact hL x
  rw [hpre]
  exact mem_P_preimage hf containsOne_mem_P

/-- The `Bool`-valued form: a polynomial-time function that emits the verdict
as a one-bit string decides its language. -/
theorem mem_P_of_decisionFn_bool {g : List Bool → Bool} {L : Language}
    (hf : (fun x => [g x]) ∈ FP) (hL : ∀ x, x ∈ L ↔ g x = true) : L ∈ P := by
  refine mem_P_of_decisionFn hf (fun x => ?_)
  rw [hL x]
  simp

/-- **A polynomial-time membership test decides a language in `P`.** The form of
`mem_P_of_decisionFn_bool` for the tests of `Complexitylib.Classes.P.Unary`. -/
theorem FPPred.mem_P {L : Language} (hL : FPPred fun x => x ∈ L) : L ∈ P := by
  obtain ⟨g, hg, hgL⟩ := hL
  exact mem_P_of_decisionFn_bool hg hgL

/-- **A bounded-key predicate is in `P`.** If `key` is polynomial-time and its
outputs have length at most `L`, then `{z | Q (key z)}` is in `P` for every `Q`;
the predicate itself need not be computable. -/
theorem mem_P_of_bounded_key {key : List Bool → List Bool} (hkey : key ∈ FP)
    {L : ℕ} (hL : ∀ z, (key z).length ≤ L) (Q : List Bool → Prop) :
    {z : List Bool | Q (key z)} ∈ P :=
  FPPred.mem_P (FPPred.of_bounded_key hkey hL Q)

end Complexity
