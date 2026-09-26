/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Order.Lattice.Nat
public import Complexitylib.Circuits.Basis.Defs
public import Complexitylib.Circuits.Typed.Defs

/-! # Boolean Circuit Complexity

This file establishes the circuit size complexity measure for Boolean functions
over a basis. It re-exports the bases of `Complexitylib.Circuits.Basis.Defs` and
the typed circuits of `Complexitylib.Circuits.Typed.Defs`, so importing it
provides the whole circuit model.

## Main definitions

* `Circuit.Realizable` — whether a function is computed by some circuit over a basis
* `Circuit.realizationSizes` — the sizes of the circuits over a basis that compute a function
* `Circuit.sizeComplexityWithTop` — generic minimum size, with `⊤` for unrealizable functions
* `Circuit.sizeComplexity` — natural-valued minimum size over a complete basis

## Main results

* `Circuit.sizeComplexity_pos` — for complete bases, size complexity is positive
-/


@[expose] public section

namespace Complexity

namespace Circuit
variable {B : Basis} {N : Nat} [NeZero N]

/-- A Boolean function is realizable over `B` when some single-output circuit
over `B` computes it. -/
def Realizable (B : Basis) (f : BitString N → Bool) : Prop :=
  ∃ G, ∃ c : Circuit B N 1 G, (fun x => (c.eval x) 0) = f

/-- Sizes of all single-output circuits over `B` that realize `f`. -/
def realizationSizes (B : Basis) (f : BitString N → Bool) : Set Nat :=
  {s | ∃ G, ∃ c : Circuit B N 1 G,
    c.size = s ∧ (fun x => (c.eval x) 0) = f}

/-- The minimum circuit size over an arbitrary basis, as an extended natural.

A single-output circuit `Circuit B N 1 G` has size `G + 1`. The value is `⊤`
exactly when no circuit over `B` computes `f`; thus an unrealizable function
cannot be confused with a zero-size function. -/
noncomputable def sizeComplexityWithTop
    (B : Basis) (f : BitString N → Bool) : WithTop Nat :=
  sInf ((fun s : Nat => (s : WithTop Nat)) '' realizationSizes B f)

/-- The minimum circuit size over a complete basis `B` computing `f`.

This natural-valued interface requires completeness so that the set of
realizing circuits is nonempty. Use `sizeComplexityWithTop` when the basis may
be incomplete. -/
-- Completeness is an intentional API precondition. The infimum expression
-- itself does not inspect the selected witness.
@[nolint unusedArguments]
noncomputable def sizeComplexity
    (B : Basis) [CompleteBasis B] (f : BitString N → Bool) : Nat :=
  sInf (realizationSizes B f)

private theorem realizationSizes_nonempty [CompleteBasis B]
    (f : BitString N → Bool) :
    (realizationSizes B f).Nonempty := by
  obtain ⟨G, c, hc⟩ := CompleteBasis.complete (B := B) (fun x => (fun _ : Fin 1 => f x))
  refine ⟨c.size, G, c, rfl, ?_⟩
  funext x
  exact congrFun (congrFun hc x) 0

/-- Any circuit computing `f` gives an upper bound on the generic extended
size complexity. -/
theorem sizeComplexityWithTop_le {G : Nat}
    (c : Circuit B N 1 G) (f : BitString N → Bool)
    (hf : (fun x => (c.eval x) 0) = f) :
    sizeComplexityWithTop B f ≤ c.size := by
  apply sInf_le
  exact ⟨c.size, ⟨G, c, rfl, hf⟩, rfl⟩

/-- Generic size complexity is infinite exactly for functions that cannot be
realized over the chosen basis. -/
theorem sizeComplexityWithTop_eq_top_iff
    (f : BitString N → Bool) :
    sizeComplexityWithTop B f = ⊤ ↔ ¬ Realizable B f := by
  rw [sizeComplexityWithTop, sInf_eq_top]
  constructor
  · intro h hrealizable
    obtain ⟨G, c, hc⟩ := hrealizable
    have htop := h (c.size : WithTop Nat)
      ⟨c.size, ⟨G, c, rfl, hc⟩, rfl⟩
    exact (WithTop.coe_ne_top : (c.size : WithTop Nat) ≠ ⊤) htop
  · intro h a ha
    obtain ⟨s, ⟨G, c, _, hc⟩, rfl⟩ := ha
    exact (h ⟨G, c, hc⟩).elim

/-- Generic size complexity is finite exactly for realizable functions. -/
theorem sizeComplexityWithTop_ne_top_iff
    (f : BitString N → Bool) :
    sizeComplexityWithTop B f ≠ ⊤ ↔ Realizable B f := by
  rw [ne_eq, sizeComplexityWithTop_eq_top_iff]
  simp only [not_not]

/-- Whenever the generic size complexity is finite, a circuit realizes its
minimum value. -/
theorem sizeComplexityWithTop_witness
    (f : BitString N → Bool)
    (hfinite : sizeComplexityWithTop B f ≠ ⊤) :
    ∃ G, ∃ c : Circuit B N 1 G,
      (c.size : WithTop Nat) = sizeComplexityWithTop B f ∧
        (fun x => (c.eval x) 0) = f := by
  have hrealizable := (sizeComplexityWithTop_ne_top_iff (B := B) f).mp hfinite
  obtain ⟨G₀, c₀, hc₀⟩ := hrealizable
  have hset : ((fun s : Nat => (s : WithTop Nat)) ''
      realizationSizes B f).Nonempty :=
    ⟨c₀.size, c₀.size, ⟨G₀, c₀, rfl, hc₀⟩, rfl⟩
  have hmem := csInf_mem hset
  obtain ⟨s, ⟨G, c, hs, hc⟩, hcoe⟩ := hmem
  exact ⟨G, c, hs ▸ hcoe, hc⟩

/-- Over a complete basis, the generic extended measure agrees with the
natural-valued minimum. -/
theorem sizeComplexityWithTop_eq_coe [CompleteBasis B]
    (f : BitString N → Bool) :
    sizeComplexityWithTop B f = (sizeComplexity B f : WithTop Nat) := by
  apply le_antisymm
  · apply sInf_le
    exact ⟨sizeComplexity B f,
      Nat.sInf_mem (realizationSizes_nonempty (B := B) f), rfl⟩
  · apply le_sInf
    rintro _ ⟨s, hs, rfl⟩
    exact WithTop.coe_le_coe.mpr (Nat.sInf_le hs)

/-- For a complete basis, circuit size complexity is always positive. -/
theorem sizeComplexity_pos [CompleteBasis B]
    (f : BitString N → Bool) :
    0 < sizeComplexity B f := by
  obtain ⟨_, _, hs, _⟩ := Nat.sInf_mem (realizationSizes_nonempty (B := B) f)
  simp only [sizeComplexity]
  rw [← hs, size]
  omega

/-- Any circuit computing `f` has size at least `sizeComplexity B f`. -/
theorem sizeComplexity_le [CompleteBasis B] {G : Nat}
    (c : Circuit B N 1 G) (f : BitString N → Bool)
    (hf : (fun x => (c.eval x) 0) = f) :
    sizeComplexity B f ≤ c.size :=
  Nat.sInf_le ⟨G, c, rfl, hf⟩

/-- For a complete basis, `sizeComplexity` is realized by some circuit. -/
theorem sizeComplexity_witness [CompleteBasis B]
    (f : BitString N → Bool) :
    ∃ G, ∃ c : Circuit B N 1 G,
      c.size = sizeComplexity B f ∧ (fun x => (c.eval x) 0) = f :=
  Nat.sInf_mem (realizationSizes_nonempty (B := B) f)

end Circuit

end Complexity
