/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Extraction.Defs
public import Mathlib.Algebra.Notation.Prod
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated

/-!
# Additivity of finite recursive block maps

Splitting only reindexes coordinates. Induction therefore transfers the
supplied fixed-seed addition laws through precisely the executed levels.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

universe u v w z r

theorem splitBlockEquiv_add {α : Type*} [Add α] {t : Nat}
    (x x' : Fin t → α × α) :
    splitBlockEquiv α t (x + x') = splitBlockEquiv α t x + splitBlockEquiv α t x' := by
  funext j
  obtain ⟨⟨i, k⟩, rfl⟩ := (splitBlockIndexEquiv t).surjective j
  revert k
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · simp only [Pi.add_apply, splitBlockEquiv_apply_fst, Prod.fst_add]
  · simp only [Pi.add_apply, splitBlockEquiv_apply_snd, Prod.snd_add]

theorem condenseSplitMap_add {α β Fresh : Type*} [Add α] [Add β]
    (C : α → Fresh → β × β) (C_add : ∀ a b y, C (a + b) y = C a y + C b y)
    (t : Nat) (x x' : Fin t → α) (y : Fresh) :
    condenseSplitMap C t (x + x') y =
      condenseSplitMap C t x y + condenseSplitMap C t x' y := by
  have pairs : (fun i => C ((x + x') i) y) =
      (fun i => C (x i) y) + (fun i => C (x' i) y) := by
    funext i
    exact C_add (x i) (x' i) y
  change splitBlockEquiv β t (fun i => C ((x + x') i) y) = _
  rw [pairs]
  exact splitBlockEquiv_add _ _

theorem recursiveBlockMap_add {X : Type v} {Earlier : Type u} {Fresh : Nat → Type u}
    {α : Nat → Type w} [Add X] [∀ i, Add (α i)] {t : Nat}
    (initial : X → Earlier → (Fin t → α 0))
    (C : ∀ i, α i → Fresh i → α (i + 1) × α (i + 1)) (n : Nat)
    (initial_add : ∀ x x' y, initial (x + x') y = initial x y + initial x' y)
    (C_add : ∀ i < n, ∀ a b y, C i (a + b) y = C i a y + C i b y)
    (x x' : X) (seeds : RecursiveSeeds Earlier Fresh n) :
    recursiveBlockMap initial C n (x + x') seeds =
      recursiveBlockMap initial C n x seeds + recursiveBlockMap initial C n x' seeds := by
  induction n with
  | zero => exact initial_add x x' seeds
  | succ n ih =>
    change condenseSplitMap (C n) (recursiveBlockCount t n)
      (recursiveBlockMap initial C n (x + x') seeds.1) seeds.2 = _
    rw [ih (fun i hi => C_add i (Nat.lt_succ_of_lt hi)) seeds.1]
    exact condenseSplitMap_add (C n) (C_add n (Nat.lt_succ_self n)) _ _ _ _

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
        recursiveBlockExtractor initial C n E x' seeds := by
  have initial_vector_add : ∀ x x' y,
      (fun _ : Fin 1 => initial (x + x') y) =
        (fun _ : Fin 1 => initial x y) + (fun _ : Fin 1 => initial x' y) := by
    intro x x' y
    funext i
    exact initial_add x x' y
  have blocks := recursiveBlockMap_add (fun x y (_ : Fin 1) => initial x y)
    C n initial_vector_add C_add x x' seeds.1
  funext i
  change E (recursiveBlockMap _ C n (x + x') seeds.1 i) seeds.2 = _
  rw [blocks]
  exact E_add _ _ seeds.2

end Algebraic.Cutwidth.Extractor.Internal
