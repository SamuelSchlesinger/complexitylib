/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Defs

/-!
# A finite recursive block extractor

An initial condenser produces one block. Each recursive level applies its
condenser with one shared fresh seed and splits the resulting pairs. A final
extractor uses one further seed on every leaf block. All these seeds remain
in the seed type, and the output is the complete tuple of leaf outputs.

This is the deterministic finite composition underlying
Chattopadhyay--Goodman--Liao, Theorem 5.6 of *Affine Extractors for Almost
Logarithmic Entropy*, <https://eccc.weizmann.ac.il/report/2021/075/>.
The component maps are supplied; an encoded evaluator and numerical
short-seed schedule are separate constructions.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

universe u v w z r

/-- Initial condensation, recursive shared-seed splitting, and shared-seed leaf extraction. -/
def recursiveBlockExtractor {X : Type v} {Earlier : Type u} {Fresh : Nat → Type u}
    {α : Nat → Type w} {Last : Type z} {Ω : Type r}
    (initial : X → Earlier → α 0)
    (C : ∀ i, α i → Fresh i → α (i + 1) × α (i + 1)) (n : Nat)
    (E : α n → Last → Ω) :
    X → (RecursiveSeeds Earlier Fresh n × Last) → (Fin (recursiveBlockCount 1 n) → Ω) :=
  fun x seeds i =>
    E (recursiveBlockMap (fun x y (_ : Fin 1) => initial x y) C n x seeds.1 i) seeds.2

end Algebraic.Cutwidth.Extractor
