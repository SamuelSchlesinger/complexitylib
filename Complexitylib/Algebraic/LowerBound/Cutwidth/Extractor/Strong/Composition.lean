/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Composition.Internal

/-!
# Condensing and then strongly extracting from flat mixtures

A condenser may approximate a mixture of flat distributions whose supports
vary with its retained seed. A strong extractor applied with a fresh,
independent seed extracts from every component. The two errors add, and the
conclusion retains both seeds. Witness injections describe the ideal
conditional sources; no injectivity of the actual condenser is assumed.

This is a finite mixture formulation of the condense-then-extract argument
in Guruswami--Umans--Vadhan, Proposition 4.5 and Remark 5.15
(<https://people.seas.harvard.edu/~salil/research/PVcondenser-jacm.pdf>), and
Chattopadhyay--Goodman--Liao, Lemma 4.9
(<https://eccc.weizmann.ac.il/report/2021/075/download/>). The hypotheses
supply the condenser witnesses and the extractor guarantee. They do not
construct an extractor, prove seed-length bounds, or decompose arbitrary
weighted sources into flat distributions.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Extraction after a supplied normalized mixture of seedwise flat witnesses.
Each component has at least `K` points, and its support may depend on the
condenser seed. Tests retain both independent seeds; their errors add. -/
theorem seededTestProb_comp_of_flat_mixture {α ι Seed Fresh Z Ω : Type*}
    [Fintype α] [Fintype ι] [Fintype Seed] [Nonempty Seed]
    [Fintype Fresh] [Nonempty Fresh] [Fintype Z] [Fintype Ω]
    {Source : ι → Type*} [∀ i, Fintype (Source i)]
    (C : α → Seed → Z) (H : Z → Fresh → Ω)
    (w : ι → ℝ) (g : ∀ i, Seed → (Source i ↪ Z))
    (nonnegative : ∀ i, 0 ≤ w i) (mass : ∑ i, w i = 1)
    {K : Nat} (positive : 0 < K) (size : ∀ i, K ≤ Fintype.card (Source i))
    {δ ε : ℝ} (extract : FlatStrongSeededExtractor H K ε)
    (close : ∀ T : Finset (Seed × Z),
      |seededTestProb C T -
        seededMixtureTestProb w (fun i x y => g i y x) T| ≤ δ)
    (T : Finset ((Seed × Fresh) × Ω)) :
    |seededTestProb (fun x ya => H (C x ya.1) ya.2) T -
      uniformSeededTestProb T| ≤ δ + ε :=
  Internal.seededTestProb_comp_of_flat_mixture C H w g nonnegative mass
    positive size extract close T

open scoped Classical in
/-- The subset-mixture witness contract of a lossless condenser composes with
a strong extractor. The resulting extractor retains both independent seeds. -/
theorem FlatStrongSeededExtractor.comp_of_flat_mixture {α Seed Fresh Z Ω : Type*}
    [Fintype Seed] [Nonempty Seed] [Fintype Fresh] [Nonempty Fresh]
    [Fintype Z] [Fintype Ω] {H : Z → Fresh → Ω}
    {K : Nat} {δ ε : ℝ} (extract : FlatStrongSeededExtractor H K ε)
    (C : α → Seed → Z) (positive : 0 < K)
    (lossless : ∀ P : Finset α, P.Nonempty → K ≤ P.card →
      ∃ g : ∀ S : P.powersetCard K, Seed → (S.val ↪ Z),
        ∀ T : Finset (Seed × Z),
          |seededTestProb (fun x : P => C x.val) T -
            seededMixtureTestProb (fun _ : P.powersetCard K =>
              ((P.powersetCard K).card : ℝ)⁻¹) (fun S x y => g S y x) T| ≤ δ) :
    FlatStrongSeededExtractor (fun x (ya : Seed × Fresh) => H (C x ya.1) ya.2)
      K (δ + ε) :=
  Internal.flatStrongSeededExtractor_comp_of_flat_mixture C H positive extract lossless

end Algebraic.Cutwidth.Extractor
