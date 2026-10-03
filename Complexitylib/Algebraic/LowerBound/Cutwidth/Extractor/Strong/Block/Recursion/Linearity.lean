/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Extraction.Defs
public import Mathlib.Algebra.Notation.Prod
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Linearity.Internal

/-!
# Fixed-seed additivity of recursive block extraction

Pair splitting preserves pointwise addition. The recursive block map and
its final extractor therefore preserve addition whenever their supplied
component maps do so at each fixed seed. Only the levels below the chosen
recursion depth need an addition law.

This is the algebraic composition invariant for the linear maps used in
Chattopadhyay--Goodman--Liao, Theorem 5.6 of *Affine Extractors for Almost
Logarithmic Entropy*, <https://eccc.weizmann.ac.il/report/2021/075/>.
The statements require only addition operations; statistical guarantees,
an encoded evaluator, and the short-seed parameter schedule are separate.
-/

public section

namespace Algebraic.Cutwidth.Extractor

universe u v w z r

/-- Splitting pairs into successive coordinates preserves pointwise addition. -/
theorem splitBlockEquiv_add {α : Type*} [Add α] {t : Nat}
    (x x' : Fin t → α × α) :
    splitBlockEquiv α t (x + x') = splitBlockEquiv α t x + splitBlockEquiv α t x' :=
  Internal.splitBlockEquiv_add x x'

/-- One shared-seed condensation and splitting step preserves addition. -/
theorem condenseSplitMap_add {α β Fresh : Type*} [Add α] [Add β]
    (C : α → Fresh → β × β) (C_add : ∀ a b y, C (a + b) y = C a y + C b y)
    (t : Nat) (x x' : Fin t → α) (y : Fresh) :
    condenseSplitMap C t (x + x') y =
      condenseSplitMap C t x y + condenseSplitMap C t x' y :=
  Internal.condenseSplitMap_add C C_add t x x' y

/-- Fixed-seed recursive block condensation is additive when its executed maps are additive. -/
theorem recursiveBlockMap_add {X : Type v} {Earlier : Type u} {Fresh : Nat → Type u}
    {α : Nat → Type w} [Add X] [∀ i, Add (α i)] {t : Nat}
    (initial : X → Earlier → (Fin t → α 0))
    (C : ∀ i, α i → Fresh i → α (i + 1) × α (i + 1)) (n : Nat)
    (initial_add : ∀ x x' y, initial (x + x') y = initial x y + initial x' y)
    (C_add : ∀ i < n, ∀ a b y, C i (a + b) y = C i a y + C i b y)
    (x x' : X) (seeds : RecursiveSeeds Earlier Fresh n) :
    recursiveBlockMap initial C n (x + x') seeds =
      recursiveBlockMap initial C n x seeds + recursiveBlockMap initial C n x' seeds :=
  Internal.recursiveBlockMap_add initial C n initial_add C_add x x' seeds

/-- The complete finite recursive extractor preserves addition for every fixed retained seed. -/
theorem recursiveBlockExtractor_add {X : Type v} {Earlier : Type u}
    {Fresh : Nat → Type u} {α : Nat → Type w} {Last : Type z} {Ω : Type r}
    [Add X] [∀ i, Add (α i)] [Add Ω]
    (initial : X → Earlier → α 0)
    (C : ∀ i, α i → Fresh i → α (i + 1) × α (i + 1)) (n : Nat)
    (E : α n → Last → Ω)
    (initial_add : ∀ x x' y, initial (x + x') y = initial x y + initial x' y)
    (C_add : ∀ i < n, ∀ a b y, C i (a + b) y = C i a y + C i b y)
    (E_add : ∀ a b y, E (a + b) y = E a y + E b y)
    (x x' : X) (seeds : RecursiveSeeds Earlier Fresh n × Last) :
    recursiveBlockExtractor initial C n E (x + x') seeds =
      recursiveBlockExtractor initial C n E x seeds +
        recursiveBlockExtractor initial C n E x' seeds :=
  Internal.recursiveBlockExtractor_add initial C n E initial_add C_add E_add x x' seeds

end Algebraic.Cutwidth.Extractor
