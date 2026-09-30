/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Cslib.Circuit.Boolean.Correction.Defs
public import Cslib.Computability.Circuit.Boolean.Counting
import Mathlib.Tactic

/-!
# Counting hard sparse functions

The graphs of all maps from `p` bits to `p` bits have exactly `2 ^ p` points
and give `2 ^ (p * 2 ^ p)` distinct scalar functions on `2 * p` bits.
Even the circuit count without its factorial saving proves that some graph
needs more than `2 ^ (p - 4)` gates, for every `p ≥ 4`.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis.Internal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Correction

/-- A graph, viewed as a sparse set of inputs on two equal blocks. -/
noncomputable def graphSupport {p : ℕ} (f : (Fin p → Bool) → (Fin p → Bool)) :
    Finset (Fin (p + p) → Bool) := by
  classical
  exact Finset.univ.image (fun x => Fin.append x (f x))

/-- Membership in the graph of a map on bit strings. -/
def graphFunction {p : ℕ} (f : (Fin p → Bool) → (Fin p → Bool)) :
    BooleanFunction (p + p) :=
  fun x => decide ((fun j => x (Fin.natAdd p j)) = f (fun j => x (Fin.castAdd p j)))

theorem card_graphSupport {p : ℕ} (f : (Fin p → Bool) → (Fin p → Bool)) :
    (graphSupport f).card = 2 ^ p := by
  classical
  rw [graphSupport, Finset.card_image_of_injective]
  · simp
  · intro x y equal
    simpa using congrArg (fun z => fun j => z (Fin.castAdd p j)) equal

theorem indicator_graphSupport {p : ℕ} (f : (Fin p → Bool) → (Fin p → Bool)) :
    indicator (n := p + p) (graphSupport f : Set _) =
      (fun x (_ : Fin 1) => graphFunction f x) := by
  classical
  funext x j
  apply Bool.eq_iff_iff.mpr
  simp only [indicator, graphFunction, decide_eq_true_eq, Finset.mem_coe, graphSupport,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, rfl⟩
    simp only [Fin.append_left, Fin.append_right]
  · intro h
    refine ⟨fun j => x (Fin.castAdd p j), ?_⟩
    rw [← h]
    exact Fin.append_castAdd_natAdd

theorem graphFunction_injective (p : ℕ) :
    Function.Injective (graphFunction (p := p)) := by
  intro f g equal
  funext x
  have h : graphFunction g (Fin.append x (f x)) = true := by
    rw [← equal]
    simp only [graphFunction, Fin.append_left, Fin.append_right, decide_true]
  simpa only [graphFunction, Fin.append_left, Fin.append_right, decide_eq_true_eq] using h

theorem circuit_count_lt_graph_count {p : ℕ} (large : 4 ≤ p) :
    (Boolean.computableFunctions (p + p) (2 ^ (p - 4))).card < 2 ^ (p * 2 ^ p) := by
  let s := 2 ^ (p - 4)
  have split : 2 ^ p = 16 * s := by
    dsimp [s]
    rw [show p = 4 + (p - 4) from by omega, pow_add]
    norm_num
  have spos : 1 ≤ s := Nat.one_le_pow _ _ (by decide)
  have inputs : p + p ≤ 2 ^ p := by
    have h : ∀ p, 1 ≤ p → 2 * p ≤ 2 ^ p := by
      intro p hp
      induction p, hp using Nat.le_induction with
      | base => decide
      | succ p hp ih => rw [pow_succ]; omega
    simpa [two_mul] using h p (by omega)
  have small : s + 1 ≤ 2 ^ p := by omega
  have wires : p + p + s + 1 ≤ 2 ^ (p + 1) := by rw [pow_succ]; omega
  have lines : 5 * (p + p + s + 1) ^ 2 ≤ 2 ^ (2 * p + 5) := by
    calc
      _ ≤ 8 * (2 ^ (p + 1)) ^ 2 := by gcongr; decide
      _ = _ := by rw [← pow_mul, show 8 = 2 ^ 3 from rfl, ← pow_add]; congr 1; omega
  have count := Boolean.card_computableFunctions_mul_factorial_le (p + p) s
  have coarse : (Boolean.computableFunctions (p + p) s).card ≤
      (s + 1) * (5 * (p + p + s + 1) ^ 2) ^ s * (p + p + s) :=
    (Nat.le_mul_of_pos_right _ (Nat.factorial_pos s)).trans count
  have exponent : p + (2 * p + 5) * s + (p + 1) < p * 2 ^ p := by
    rw [split]
    nlinarith
  calc
    _ ≤ (2 ^ p) * (2 ^ (2 * p + 5)) ^ s * 2 ^ (p + 1) :=
      coarse.trans (Nat.mul_le_mul (Nat.mul_le_mul small
        (Nat.pow_le_pow_left lines s)) (by omega))
    _ = 2 ^ (p + (2 * p + 5) * s + (p + 1)) := by rw [← pow_mul, ← pow_add, ← pow_add]
    _ < _ := Nat.pow_lt_pow_right (by decide) exponent

theorem exists_hard_graph {p : ℕ} (large : 4 ≤ p) :
    ∃ domain : Finset (Fin (p + p) → Bool), domain.card = 2 ^ p ∧
      2 ^ (p - 4) < complexity interpretation (indicator (n := p + p) (domain : Set _)) := by
  classical
  let family := Finset.univ.image (graphFunction (p := p))
  have card : family.card = 2 ^ (p * 2 ^ p) := by
    rw [Finset.card_image_of_injective _ (graphFunction_injective p)]
    simp [← pow_mul]
  have count := circuit_count_lt_graph_count large
  rw [← card] at count
  obtain ⟨f, hf, hard⟩ := Finset.exists_mem_notMem_of_card_lt_card count
  obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hf
  refine ⟨graphSupport g, card_graphSupport g, ?_⟩
  rw [indicator_graphSupport]
  by_contra small
  exact hard (Boolean.mem_computableFunctions.mpr (complexity_le_iff.mp (not_lt.mp small)))

end Complexity.CircuitSparseSynthesis.Internal
