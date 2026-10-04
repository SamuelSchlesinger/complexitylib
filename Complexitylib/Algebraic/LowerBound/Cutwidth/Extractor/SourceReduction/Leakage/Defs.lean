/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Defs

/-!
# Actual affine outputs after deterministic seed leakage

Each call uses the same shifted source. Its seed is the XOR of a fixed
seed and a deterministic observation of the source. A bad honest seed
admits some shift and some collection of tampered seeds for which the
honest output fails to be uniform conditioned on all tampered outputs.
The witnesses may depend on the honest seed.

This is the finite bad-seed construction of Chattopadhyay--Liao,
*Extractors for Sum of Two Sources*, Lemma 5.3:
<https://arxiv.org/abs/2110.12652>.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- All actual tampered outputs and the honest output after source-dependent seed leakage. -/
noncomputable def affineLeakageOutputWeight {n d t : Nat} {Out : Type*}
    (cb : (Fin n → Bool) → (Fin d → Bool) → List Bool → Out)
    (p : (Fin n → Bool) → ℝ)
    (leak : (Fin n → Bool) → Option (Fin t) → Fin d → Bool)
    (advice : Option (Fin t) → List Bool)
    (b : Fin n → Bool) (y : Fin d → Bool) (ys : Fin t → Fin d → Bool) :
    (Fin t → Out) × Out → ℝ :=
  mapWeight (fun x =>
    ((fun i => cb (xorInput x b) (xorInput (ys i) (leak x (some i))) (advice (some i))),
      cb (xorInput x b) (xorInput y (leak x none)) (advice none))) p

/-- Honest seeds for which some shift and tampered seed choices exceed the requested error. -/
noncomputable def affineLeakageBadSeeds {n d t : Nat} {Out : Type*} [Fintype Out]
    (cb : (Fin n → Bool) → (Fin d → Bool) → List Bool → Out)
    (p : (Fin n → Bool) → ℝ)
    (leak : (Fin n → Bool) → Option (Fin t) → Fin d → Bool)
    (advice : Option (Fin t) → List Bool) (γ : ℝ) : Finset (Fin d → Bool) := by
  classical
  exact Finset.univ.filter fun y => ∃ b ys,
    γ < weightDist (affineLeakageOutputWeight cb p leak advice b y ys)
      (uniformSecondWeight (affineLeakageOutputWeight cb p leak advice b y ys))

end Algebraic.Cutwidth.Extractor
