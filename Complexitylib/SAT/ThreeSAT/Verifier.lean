/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.ThreeSAT.Syntax
public import Complexitylib.Classes.Pairing
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Scanner

/-!
# Exact-3 syntax on paired verifier inputs

The SAT verifier receives `pair(z, α)`, where every bit of `z` is doubled
and the pair separator is `01`. This module gives a small finite-state scanner
that feeds the decoded left component into `ThreeSAT.Syntax` and ignores the
witness suffix. It recognizes `pair(z, α)` exactly when `z` passes the
exact-3 syntax checker.

## Main results

- `ThreeSAT.PairSyntax.pair_mem_language_iff` -- paired-input correctness
- `ThreeSAT.PairSyntax.language_mem_P` -- the paired syntax language is in P
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace PairSyntax

/-- State of the paired-input scanner. `first` and `second` decode the doubled
left component, `right` ignores the witness suffix, and `reject` is absorbing. -/
inductive State where
  | first (syn : Syntax.BitState)
  | second (syn : Syntax.BitState) (firstBit : Bool)
  | right
  | reject
  deriving DecidableEq, Fintype

/-- Initial paired-input scanner state. -/
def initial : State := .first Syntax.bitStart

/-- Consume one concrete bit of a paired verifier input. -/
def step : State → Bool → State
  | .first syn, bit => .second syn bit
  | .second syn false, false => .first (Syntax.bitStep syn false)
  | .second syn true, true => .first (Syntax.bitStep syn true)
  | .second syn false, true =>
      if Syntax.accept syn then .right else .reject
  | .second _ true, false => .reject
  | .right, _ => .right
  | .reject, _ => .reject

/-- Accept after seeing the pair separator with an exact-3 left component. -/
def accept : State → Bool
  | .right => true
  | _ => false

/-- Regular language of paired words whose left component has exact-3 syntax. -/
def language : Language :=
  {z | accept (z.foldl step initial) = true}

@[simp] private theorem foldl_right (suffix : List Bool) :
    suffix.foldl step .right = .right := by
  induction suffix with
  | nil => rfl
  | cons bit suffix ih =>
      rw [List.foldl_cons]
      exact ih

@[simp] private theorem foldl_reject (suffix : List Bool) :
    suffix.foldl step .reject = .reject := by
  induction suffix with
  | nil => rfl
  | cons bit suffix ih =>
      rw [List.foldl_cons]
      exact ih

/-- Folding over the doubled left component feeds each original bit exactly
once to the exact-3 syntax automaton. -/
private theorem foldl_doubled (x : List Bool) (syn : Syntax.BitState) :
    (x.flatMap fun bit => [bit, bit]).foldl step (.first syn) =
      .first (x.foldl Syntax.bitStep syn) := by
  induction x generalizing syn with
  | nil => rfl
  | cons bit x ih =>
      cases bit <;> simp [step, ih]

/-- A canonical pair belongs to the paired syntax language exactly when its
left component belongs to the exact-3 syntax language. -/
@[simp] theorem pair_mem_language_iff (z witness : List Bool) :
    pair z witness ∈ language ↔ z ∈ Syntax.language := by
  change accept ((pair z witness).foldl step initial) = true ↔
    Syntax.accept (z.foldl Syntax.bitStep Syntax.bitStart) = true
  rw [pair, List.foldl_append, List.foldl_append]
  simp only [initial]
  rw [foldl_doubled]
  cases hsyntax : Syntax.accept (z.foldl Syntax.bitStep Syntax.bitStart) <;>
    simp [step, accept, hsyntax]

/-- Zero-work-tape scanner for exact-3 syntax on paired inputs. -/
def pairSyntaxTM : TM 0 :=
  TM.scannerTM initial step (fun state => if accept state then .one else .zero)

/-- The paired syntax scanner decides its language in exactly `n + 2` steps. -/
theorem pairSyntaxTM_decidesInTime :
    pairSyntaxTM.DecidesInTime language (fun n => n + 2) := by
  exact TM.scannerTM_decidesInTime initial step accept (fun _ => Iff.rfl)

/-- Exact-3 syntax on paired inputs is decidable in linear time. -/
theorem language_mem_P : language ∈ P := by
  refine Set.mem_iUnion.mpr ⟨1, 0, pairSyntaxTM, fun n => n + 2,
    pairSyntaxTM_decidesInTime, ?_⟩
  refine BigO.add ?_ (BigO.const_le_pow 2 1)
  simpa using BigO.refl (fun n : ℕ => n)

end PairSyntax

end ThreeSAT

end SAT

end Complexity
