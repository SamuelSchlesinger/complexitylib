/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Rectangle
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Circuit.Count
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Circuit.Mixing
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Ordering

/-!
# A large component after aggregate-gate erasure

The input sets of the erased circuit's components partition the coordinates. Every
union of components has a mixing summary with at most `2 ^ budget` possible values.
Rectangle-freeness rules out a balanced union, forcing one component to contain all
but `budget + clog 2 K + 3` inputs. No assumption about cancellation is used.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate

open scoped Classical
open MultiOutput SingleCut

/-- A finite partition with short mixing summaries has a part containing almost all inputs. -/
theorem exists_large_fibre_of_mixing {n K D : Nat} {f : Cslib.BooleanFunction n}
    (free : RectangleFree f K) (dense : 2 ^ (n - 2) ≤ (accepting f).card)
    {ι T : Type*} [Fintype ι] [DecidableEq ι] [Fintype T] (color : Fin n → ι)
    (short : Fintype.card T ≤ 2 ^ D)
    (keys : ∀ S : Finset ι, ∃ key : (Fin n → Bool) → T,
      ∀ x ∈ accepting f, ∀ y ∈ accepting f, key x = key y →
        f (mix (Finset.univ.filter fun i => color i ∈ S) x y) = true)
    (big : 3 * (D + Nat.clog 2 K + 3) ≤ n) :
    ∃ i, n - (D + Nat.clog 2 K + 3) <
      (Finset.univ.filter fun j => color j = i).card := by
  classical
  let weight (i : ι) := (Finset.univ.filter fun j => color j = i).card
  have total : ∑ i, weight i = n := by
    simpa [weight] using (Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ) (t := Finset.univ) (f := color)
      (fun _ _ => Finset.mem_univ _)).symm
  apply exists_large_part weight (by lia) total big
  intro S
  obtain ⟨key, closed⟩ := keys S
  have h := min_card_lt_of_mixing free dense _ key short closed
  have count : (∑ i ∈ S, weight i) =
      (Finset.univ.filter fun j => color j ∈ S).card := by
    exact Finset.sum_card_fiberwise_eq_card_filter Finset.univ S color
  simpa only [count, Finset.card_compl, Fintype.card_fin] using h

/-- For a dense rectangle-free output, one component of any guessed erasure contains
almost all input coordinates. This includes guesses that are never realized by an input. -/
theorem exists_large_component {J : Type} {State : J → Type}
    [∀ j, CommMonoid (State j)] [∀ j, Fintype (State j)]
    {n g K : Nat} (p : Program (Algebraic.Aggregate.signature State) n g)
    (out : Wire n g) (a : Algebraic.Aggregate.Guess p)
    (free : RectangleFree (fun x => p.trace Algebraic.Aggregate.interpretation x out) K)
    (dense : 2 ^ (n - 2) ≤
      (accepting fun x => p.trace Algebraic.Aggregate.interpretation x out).card)
    (big : 3 * (Algebraic.Aggregate.budget p + Nat.clog 2 K + 3) ≤ n) :
    ∃ w : Wire n g, n - (Algebraic.Aggregate.budget p + Nat.clog 2 K + 3) <
      (inputsIn (component (Algebraic.Aggregate.erase p a) w)).card := by
  classical
  let e := Algebraic.Aggregate.erase p a
  let color (w : Wire n g) := component e w
  have linked_color (gate : Fin g) (wire : Wire n g) (h : e.Reads gate wire) :
      color (.gate gate) = color wire := by
    exact component_eq_of_mem ((component_closed e wire gate wire h).mpr
      (mem_component_self e wire))
  have keys : ∀ S : Finset (Finset (Wire n g)),
      ∃ key : (Fin n → Bool) → Algebraic.Aggregate.Guess p × Algebraic.Aggregate.Registers p,
        ∀ x ∈ accepting (fun x => p.trace Algebraic.Aggregate.interpretation x out),
        ∀ y ∈ accepting (fun x => p.trace Algebraic.Aggregate.interpretation x out),
          key x = key y → (p.trace Algebraic.Aggregate.interpretation
            (mix (Finset.univ.filter fun i => color (.input i) ∈ S) x y) out) = true := by
    intro S
    let W := Finset.univ.filter fun w => color w ∈ S
    have closed : Algebraic.Aggregate.ClosedSet p W := by
      apply Algebraic.Aggregate.closedSet_of_erase_closed p a W
      intro gate wire h
      simp only [W, Finset.mem_filter, Finset.mem_univ, true_and, linked_color gate wire h]
    refine ⟨Algebraic.Aggregate.componentKey p W, ?_⟩
    intro x hx y hy key
    have hx : p.trace Algebraic.Aggregate.interpretation x out = true := by
      simpa [accepting] using hx
    have hy : p.trace Algebraic.Aggregate.interpretation y out = true := by
      simpa [accepting] using hy
    have hm := Algebraic.Aggregate.accepts_mix_of_componentKey_eq p W closed out x y hx hy key
    convert hm using 1
    congr 1
    funext i
    simp [mix, glue, SingleCut.mix, W]

  obtain ⟨part, hpart⟩ := exists_large_fibre_of_mixing
    (n := n) (K := K) (D := Algebraic.Aggregate.budget p)
    (T := Algebraic.Aggregate.Guess p × Algebraic.Aggregate.Registers p) free dense
    (fun j => color (.input j)) (Algebraic.Aggregate.card_componentKey_le p) keys big
  have nonempty : (Finset.univ.filter fun j => color (.input j) = part).Nonempty :=
    Finset.card_pos.mp (by lia)
  obtain ⟨j, hj⟩ := nonempty
  have hj := (Finset.mem_filter.mp hj).2
  refine ⟨.input j, ?_⟩
  have same : (Finset.univ.filter fun i => color (.input i) = part) =
      inputsIn (component e (.input j)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, inputsIn]
    rw [← hj]
    constructor
    · intro h
      change Wire.input i ∈ color (.input j)
      rw [← h]
      exact mem_component_self e (.input i)
    · exact component_eq_of_mem
  rwa [same] at hpart

end Algebraic.Cutwidth.Aggregate
