/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Circuit.Complexity
public import Cslib.Computability.Languages.Slice
public import Cslib.Foundations.Data.BitString

/-!
# Circuit families

A circuit has a fixed number of inputs, while the words of a language have every length, so a
language is decided by a family of circuits, one for each input length. The circuit on `n` inputs
only has to handle the words of length `n`, the slice `L.slice n` of the language, and nothing
relates the circuits for different lengths: families are a nonuniform model of computation.

The letters of a word are fed to the circuit as values of the carrier, and the single output
letter is read as a verdict by a function `accept` into `Bool`. A language is decidable within a
size bound `s` when some family decides it with at most `s n` gates on `n` inputs, exactly at
every length. Over a carrier `Bool` read by `id`, this is a bound on the complexity of every
slice. The classes `SIZE` and P/poly of the literature, over the De Morgan basis, are in
`Complexitylib.Cslib.Circuit.Boolean.Family`.

Ported from `Cslib.Computability.Circuit.Family` at commit `2a4389b` of the author's CSLib fork
(branch `complexitylib-integration`); upstream CSLib does not have this module. It keeps its
`Cslib.Circuits` namespace as a candidate for upstreaming.
-/

@[expose] public section

namespace Cslib.Circuits

universe v u

variable {σ : Signature.{v}} {α : Type u}

/-- A family of single-output circuits, one for each number of inputs. -/
abbrev CircuitFamily (σ : Signature.{v}) := (n : ℕ) → Circuit σ n 1

/-- A circuit family decides `L` under `I` when, for every `n`, reading the output of its circuit
on `n` inputs through `accept` gives the slice of `L` at length `n`. -/
def CircuitFamily.Decides (F : CircuitFamily σ) (I : Interpretation σ α) (accept : α → Bool)
    (L : Language α) : Prop :=
  ∀ n (x : Fin n → α), accept ((F n).eval I x 0) = L.slice n x

/-- A language is decidable within the size bound `s` by circuits over `I` when some family
decides it, reading outputs through `accept`, with at most `s n` gates on `n` inputs. -/
def DecidableInSize (L : Language α) (I : Interpretation σ α) (accept : α → Bool)
    (s : ℕ → ℕ) : Prop :=
  ∃ F : CircuitFamily σ, F.Decides I accept L ∧ ∀ n, (F n).size ≤ s n

variable {F : CircuitFamily σ} {I : Interpretation σ α} {accept : α → Bool} {L : Language α}
  {s s' : ℕ → ℕ}

theorem CircuitFamily.decides_iff :
    F.Decides I accept L ↔
      ∀ n (x : Fin n → α), accept ((F n).eval I x 0) = true ↔ List.ofFn x ∈ L := by
  unfold CircuitFamily.Decides
  refine forall₂_congr fun n x => ?_
  rw [← Language.slice_eq_true_iff]
  exact Bool.eq_iff_iff

/-- The size bound can be weakened. -/
theorem DecidableInSize.mono (h : DecidableInSize L I accept s) (hs : ∀ n, s n ≤ s' n) :
    DecidableInSize L I accept s' :=
  h.imp fun _ ⟨hF, hsize⟩ => ⟨hF, fun n => (hsize n).trans (hs n)⟩

/-- A language is decidable within `s` exactly when each slice is `accept` of some function of
extended complexity at most the bound. -/
theorem decidableInSize_iff_exists_ecomplexity_le :
    DecidableInSize L I accept s ↔
      ∀ n, ∃ f : (Fin n → α) → α, accept ∘ f = L.slice n ∧
        ecomplexity I (fun x (_ : Fin 1) => f x) ≤ s n := by
  constructor
  · rintro ⟨F, hF, hs⟩ n
    refine ⟨fun x => (F n).eval I x 0, funext (hF n), ?_⟩
    refine (ecomplexity_le_of_computes (F n) fun x => ?_).trans (by exact_mod_cast hs n)
    funext i
    rw [Fin.fin_one_eq_zero i]
  · intro h
    choose f hf hs using h
    choose F hF hsize using fun n => ecomplexity_le_iff.mp (hs n)
    refine ⟨F, fun n x => ?_, hsize⟩
    rw [congrFun (hF n x) 0, ← hf n]
    rfl

/-! ### Boolean carrier

Over the carrier `Bool`, reading the output by `id` makes the circuit compute the slice itself. -/

section Bool

variable {I : Interpretation σ Bool} {L : Language Bool}

theorem CircuitFamily.decides_id_iff :
    F.Decides I id L ↔ ∀ n, (F n).Computes I (fun x _ => L.slice n x) := by
  simp only [CircuitFamily.Decides, Circuit.Computes, funext_iff, Fin.forall_fin_one, id]

/-- Over the carrier `Bool`, a language is decidable within `s` exactly when every slice has
extended complexity at most the bound, so a slice with no circuit keeps the language out. -/
theorem decidableInSize_id_iff_ecomplexity_le :
    DecidableInSize L I id s ↔ ∀ n, ecomplexity I (fun x (_ : Fin 1) => L.slice n x) ≤ s n := by
  simp only [DecidableInSize, CircuitFamily.decides_id_iff]
  constructor
  · rintro ⟨F, hF, hs⟩ n
    exact (ecomplexity_le_of_computes (F n) (hF n)).trans (by exact_mod_cast hs n)
  · intro h
    choose F hF hs using fun n => ecomplexity_le_iff.mp (h n)
    exact ⟨F, hF, hs⟩

/-- Over a complete basis on `Bool`, a language is decidable within `s` exactly when every slice
has complexity at most the bound. -/
theorem decidableInSize_id_iff_complexity_le [I.IsComplete] :
    DecidableInSize L I id s ↔ ∀ n, complexity I (fun x (_ : Fin 1) => L.slice n x) ≤ s n := by
  simp only [decidableInSize_id_iff_ecomplexity_le, ← natCast_complexity, ENat.natCast_le_natCast]

end Bool

end Cslib.Circuits
