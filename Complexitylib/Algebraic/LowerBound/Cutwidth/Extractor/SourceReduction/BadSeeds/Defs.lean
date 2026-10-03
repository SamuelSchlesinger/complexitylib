/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Fintype.Powerset

/-!
# The seed tests used by low-order parity reduction

The bad-seed union in Chattopadhyay and Liao, *Extractors for Sum of Two
Sources* (2021), Lemma 5.4 ranges over nonempty coordinate subsets of size
at most `t` and over every candidate seed. Keeping this union explicit lets
one somewhere sampler supply all the required parity tests simultaneously.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open scoped Classical

/-- The nonempty coordinate sets of size at most `t`. -/
noncomputable def parityTests (ι : Type*) [Fintype ι] (t : Nat) : Finset (Finset ι) :=
  Finset.univ.filter fun U => U.Nonempty ∧ U.card ≤ t

/-- All bad seeds for all low-order parity tests and all candidate positions. -/
noncomputable def parityBadSeeds {ι Choice Seed : Type*} [Fintype ι] [Fintype Choice]
    (bad : Finset ι → Choice → Finset Seed) (t : Nat) : Finset Seed :=
  (parityTests ι t).biUnion fun U => Finset.univ.biUnion (bad U)

end Algebraic.Cutwidth.Extractor
