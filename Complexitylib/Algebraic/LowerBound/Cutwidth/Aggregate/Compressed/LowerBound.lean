/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Compressed.Components
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Compressed.Compilation
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.LowerBound

/-!
# Lower bounds from sublinear joint aggregate state

The graph-ordering coefficient transfers using only the cardinality of a joint
factorization. The number of special gates is unrestricted and all gates are counted.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Compressed

open scoped Classical
open Filter MultiOutput SingleCut

variable {J : Type} {State : J → Type} [∀ j, CommMonoid (State j)]

/-- Every dense rectangle-free mixed circuit admits the finite slice estimate.
The budget counts the joint final-state guess and its independent accumulator. -/
theorem sliceBound_of_circuit {M : Type} [CommMonoid M] [Fintype M]
    {n g D K : Nat}
    (p : Program (Algebraic.Aggregate.signature State) n g)
    (compression : Algebraic.Aggregate.Compressed.Factorization p M) (out : Wire n g)
    (budget : Algebraic.Aggregate.Compressed.budget M ≤ D)
    (free : RectangleFree (fun x => p.trace Algebraic.Aggregate.interpretation x out) K)
    (dense : 2 ^ (n - 2) ≤
      (accepting fun x => p.trace Algebraic.Aggregate.interpretation x out).card)
    (hK : 1 < K) (big : 3 * (D + Nat.clog 2 K + 3) ≤ n)
    {A η C : ℝ} (hAη : 0 ≤ A + η) (hC : 0 ≤ C)
    (order : Multigraph.OrderingBound A η C) : SliceBound A η C n g D K := by
  let a : Algebraic.Aggregate.Guess p := fun _ => false
  obtain ⟨w, hw⟩ := exists_large_component p compression out a free dense (by lia)
  let Q : MultiOutput.Internal.ClosedSet (Algebraic.Aggregate.erase p a) :=
    ⟨component (Algebraic.Aggregate.erase p a) w,
      component_closed (Algebraic.Aggregate.erase p a) w⟩
  let U := inputsIn Q.carrier
  let m := U.card
  let e : Fin m ≃ U := (Finset.equivFin U).symm
  have hm : 2 ≤ m := by dsimp [m, U, Q]; lia
  have hmn : m ≤ n := by simpa [m] using Finset.card_le_univ U
  obtain ⟨z, hz⟩ := exists_dense_restriction U e.symm hm dense
  have count := card_restriction_le p compression out a Q e z hm
    (component_connected (Algebraic.Aggregate.erase p a) w) hAη hC order hK free
  refine ⟨m, hm, hmn, ?_, ?_⟩
  · dsimp [m, U, Q]
    lia
  · have lower : (2 : ℝ) ^ ((m : ℝ) - 2) ≤
        ((accepting (restriction (fun x => p.trace Algebraic.Aggregate.interpretation x out)
          U e.symm z)).card : ℝ) := by
      have h : (2 : ℝ) ^ (m - 2) ≤
          ((accepting (restriction (fun x => p.trace Algebraic.Aggregate.interpretation x out)
            U e.symm z)).card : ℝ) := by exact_mod_cast hz
      rwa [← Real.rpow_natCast, Nat.cast_sub hm, Nat.cast_ofNat] at h
    apply lower.trans (count.trans ?_)
    rw [← Real.rpow_natCast]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact_mod_cast Nat.add_le_add_right budget 1


/-- The general-coefficient lower bound for binary gates augmented by arbitrary finite
commutative-monoid gates with a sublinear joint-state budget. -/
theorem eventually_lt_size_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C)
    (f : ∀ n, Cslib.BooleanFunction n) (D K : Nat → Nat)
    (hD : (fun n => (D n : ℝ)) =o[atTop] (fun n => (n : ℝ)))
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hard : ∀ᶠ n in atTop, RectangleFree (f n) (K n) ∧
      2 ^ (n - 2) ≤ (accepting (f n)).card) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (M : Type) [CommMonoid M] [Fintype M],
      ∀ c : Circuit (Algebraic.Aggregate.signature State) n 1,
      Algebraic.Aggregate.Compressed.Factorization c.program M →
      c.Computes Algebraic.Aggregate.interpretation (fun x _ => f n x) →
      Algebraic.Aggregate.Compressed.budget M ≤ D n →
        (1 + 1 / A - ε) * n < c.size := by
  let Good (n g : Nat) := ∃ (M : Type) (instM : CommMonoid M) (instF : Fintype M),
    letI := instM
    letI := instF
    ∃ p : Program (Algebraic.Aggregate.signature State) n g,
      ∃ out : Wire n g, ∃ _compression : Algebraic.Aggregate.Compressed.Factorization p M,
        (∀ x, p.trace Algebraic.Aggregate.interpretation x out = f n x) ∧
          Algebraic.Aggregate.Compressed.budget M ≤ D n
  have hKtwo : ∀ᶠ n in atTop, 1 < K n := by
    filter_upwards [hard] with n hn
    have hpos := (Nat.two_pow_pos (n - 2)).trans_le hn.2
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    exact hn.1.one_lt (x := x) (by simpa [accepting] using hx)
  have slices : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ g, Good n g → SliceBound A η C n g (D n) (K n) := by
    intro η hη
    obtain ⟨C, hC⟩ := order η hη
    refine ⟨C, orderingBound_nonneg hC, ?_⟩
    filter_upwards [hard, hKtwo, eventually_component_guard D K hD hK hKtwo]
      with n hn hKpos hguard g hg
    obtain ⟨M, instM, instF, p, out, compression, agrees, budget⟩ := hg
    let := instM
    let := instF
    have equality : (fun x => p.trace Algebraic.Aggregate.interpretation x out) = f n :=
      funext agrees
    exact sliceBound_of_circuit p compression out budget (equality ▸ hn.1) (equality ▸ hn.2)
      hKpos hguard (by positivity) (orderingBound_nonneg hC) hC
  have result := eventually_lt_size_of_sliceBound hA Good D K hD hK hKtwo slices hε
  filter_upwards [result] with n hn M instM instF c compression computes budget
  apply hn c.size
  refine ⟨M, instM, instF, c.program, c.outputs 0, compression, ?_, budget⟩
  intro x
  exact congrFun (computes x) 0


end Algebraic.Cutwidth.Aggregate.Compressed
