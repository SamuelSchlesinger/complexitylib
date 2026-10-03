/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Nondeterministic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding.Asymptotics.Internal

/-!
# Coefficient-four hardness from balanced padding

One fixed extractor family with any fixed error strictly below one half and
sublinear source entropy yields one fixed padded family that requires more
than `(4 - ε)` times its padded input length in gates, for every positive
`ε` and all sufficiently large inputs. The same result holds for
nondeterministic circuits with unrestricted witness lengths. The extractor
family remains an assumption; all graph bounds and padding steps are proved.
-/

@[expose] public section

namespace Algebraic.Cutwidth

/-- Balanced padding turns extraction with any fixed error below one half
and `log₂ K = o(n)` into a lower bound measured at the full padded length.
The family and its threshold are fixed before choosing the circuit slack. -/
theorem eventually_lt_size_balancePad_of_flatSumsetExtractor
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) {ν : ℝ} (hν : ν < 1 / 2)
    (positive : ∀ᶠ n in Filter.atTop, 0 < K n)
    (hK : (fun n => Real.logb 2 (K n)) =o[Filter.atTop] (fun n => (n : ℝ)))
    (extract : ∀ᶠ n in Filter.atTop, FlatSumsetExtractor (f n) (K n) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ circuit : Circuit Binary.signature (n + 1) 1,
      circuit.Computes Binary.interpretation (fun x _ => balancePad (f n) x) →
        (4 - ε) * (n + 1) < circuit.size :=
  Extractor.Internal.eventually_lt_size_balancePad_of_flatSumsetExtractor
    f K hν positive hK extract hε

/-- The same padded family is hard for nondeterministic circuits with any
number of witness inputs; the lower bound counts its `n + 1` ordinary inputs. -/
theorem nondet_eventually_lt_size_balancePad_of_flatSumsetExtractor
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) {ν : ℝ} (hν : ν < 1 / 2)
    (positive : ∀ᶠ n in Filter.atTop, 0 < K n)
    (hK : (fun n => Real.logb 2 (K n)) =o[Filter.atTop] (fun n => (n : ℝ)))
    (extract : ∀ᶠ n in Filter.atTop, FlatSumsetExtractor (f n) (K n) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ (m : Nat) (circuit : Circuit Binary.signature (n + 1 + m) 1),
      NondetComputes circuit (balancePad (f n)) → (4 - ε) * (n + 1) < circuit.size :=
  Extractor.Internal.nondet_eventually_lt_size_balancePad_of_flatSumsetExtractor
    f K hν positive hK extract hε

end Algebraic.Cutwidth
