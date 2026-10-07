/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapePower
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeStoreRepresentation
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeUnaryCompare

/-!
# Unrestricted depth-three lower bound: tape power compare

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapePowerCompare.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapePowerCompare

open TapeMultiProgram TapeRouting TapeUnary TapeCopy

theorem resultTapes_eq_frame (k : ℕ)
    (outer source scratch destination : TapeRegister) (T : TapeTapes) (n m : ℕ) :
    TapePower.resultTapes k outer source scratch destination T n m =
      TapeMultiply.tapes (TapePower.resultRegister k outer destination) source scratch
        (TapePower.resultRegister k destination outer) T (n * m ^ k) m 0 0 := by
  induction k generalizing outer destination n with
  | zero => simp [TapePower.resultTapes, TapePower.resultRegister]
  | succ k ih =>
      change TapePower.resultTapes k destination source scratch outer T (n * m) m =
        TapeMultiply.tapes (TapePower.resultRegister k destination outer) source scratch
          (TapePower.resultRegister k outer destination) T (n * m ^ (k + 1)) m 0 0
      rw [ih]
      congr 1
      rw [pow_succ]
      ring

theorem resultRegister_pair (k : ℕ) (outer destination : TapeRegister) :
    (TapePower.resultRegister k outer destination = outer ∧
      TapePower.resultRegister k destination outer = destination) ∨
    (TapePower.resultRegister k outer destination = destination ∧
      TapePower.resultRegister k destination outer = outer) := by
  induction k with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ k ih =>
      rcases ih with h | h
      · exact Or.inr ⟨h.2, h.1⟩
      · exact Or.inl ⟨h.2, h.1⟩

theorem resultRegister_ne (k : ℕ) {outer destination target : TapeRegister}
    (hot : outer ≠ target) (hdt : destination ≠ target) :
    TapePower.resultRegister k outer destination ≠ target := by
  rcases resultRegister_pair k outer destination with h | h
  · simpa only [h.1] using hot
  · simpa only [h.1] using hdt

private theorem frame_store {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (hoc : outer ≠ scratch) (hod : outer ≠ destination)
    (hsc : source ≠ scratch) (hsd : source ≠ destination) (hcd : scratch ≠ destination)
    (σ : TapeStore) (n m : ℕ)
    (hs : σ source = List.replicate m true) (hc : σ scratch = [])
    (hd : σ destination = []) :
    TapeMultiply.tapes outer source scratch destination (storeTapes σ) n m 0 0 =
      storeTapes (Function.update σ outer (List.replicate n true)) := by
  funext r
  by_cases ho : r = outer
  · subst r
    simp [TapeMultiply.tapes, storeTapes, counterTape]
  · by_cases hr : r = source
    · subst r
      simp [TapeMultiply.tapes, onPair, storeTapes, Function.update, Ne.symm hos,
        hs, counterTape]
    · by_cases hr' : r = scratch
      · subst r
        simp [TapeMultiply.tapes, onPair, storeTapes, Function.update, Ne.symm hoc,
          Ne.symm hsc, hc, counterTape]
      · by_cases hr'' : r = destination
        · subst r
          simp [TapeMultiply.tapes, onPair, storeTapes, Function.update, Ne.symm hod,
            Ne.symm hsd, Ne.symm hcd, hd, counterTape]
        · simp [TapeMultiply.tapes, onPair, storeTapes, Function.update, ho, hr, hr', hr'']

/-- Tape-store contents at the output stage of the power compare routine. -/
def outputStore (k : ℕ) (outer destination : TapeRegister) (σ : TapeStore) (c : ℕ) :
    TapeStore :=
  Function.update σ (TapePower.resultRegister k outer destination) (List.replicate (c ^ k) true)

theorem result_store (k : ℕ) {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (hoc : outer ≠ scratch) (hod : outer ≠ destination)
    (hsc : source ≠ scratch) (hsd : source ≠ destination) (hcd : scratch ≠ destination)
    (σ : TapeStore) (c : ℕ) (ho : σ outer = [])
    (hs : σ source = List.replicate c true) (hc : σ scratch = [])
    (hd : σ destination = []) :
    TapePower.resultTapes k outer source scratch destination (storeTapes σ) 1 c =
      storeTapes (outputStore k outer destination σ c) := by
  rw [resultTapes_eq_frame]
  simp only [Nat.one_mul]
  unfold outputStore
  rcases resultRegister_pair k outer destination with ⟨hr, hr'⟩ | ⟨hr, hr'⟩
  · rw [hr, hr']
    exact frame_store hos hoc hod hsc hsd hcd σ (c ^ k) c hs hc hd
  · rw [hr, hr']
    exact frame_store (Ne.symm hsd) (Ne.symm hcd) (Ne.symm hod)
      hsc (Ne.symm hos) (Ne.symm hoc) σ (c ^ k) c hs hc ho

@[simp] theorem outputStore_result (k : ℕ) (outer destination : TapeRegister)
    (σ : TapeStore) (c : ℕ) :
    outputStore k outer destination σ c (TapePower.resultRegister k outer destination) =
      List.replicate (c ^ k) true := by
  simp [outputStore]

theorem outputStore_other (k : ℕ) (outer destination : TapeRegister)
    (σ : TapeStore) (c : ℕ) (r : TapeRegister)
    (hr : r ≠ TapePower.resultRegister k outer destination) :
    outputStore k outer destination σ c r = σ r := by
  simp [outputStore, Function.update, hr]

theorem outputStore_clear (k : ℕ) (outer destination : TapeRegister)
    (σ : TapeStore) (c : ℕ) (ho : σ outer = []) (hd : σ destination = []) :
    Function.update (outputStore k outer destination σ c)
      (TapePower.resultRegister k outer destination) [] = σ := by
  unfold outputStore
  rw [Function.update_idem]
  apply Function.update_eq_self_iff.mpr
  rcases resultRegister_pair k outer destination with h | h
  · simpa only [h.1] using ho.symm
  · simpa only [h.1] using hd.symm

/-- Control states of the power compare routine. -/
abbrev State (k : ℕ) := IncState ⊕ (TapePower.State k ⊕ TapeUnaryCompare.State)

/-- Transition function of the power compare routine. -/
def program (k : ℕ) (outer source scratch destination target : TapeRegister) :
    TapeMultiProgram (State k) :=
  joinCode (incProgram outer)
    (joinCode (TapePower.program k outer source scratch destination)
      (TapeUnaryCompare.program (TapePower.resultRegister k outer destination) target)
      (fun _ => TapeUnaryCompare.State.scan .beginR))
    (fun _ => Sum.inl (TapePower.start k))

/-- Initial control state of the power compare routine. -/
def start (k : ℕ) : State k := .inl IncState.start
/-- Terminal control state of the power compare routine. -/
def done (k : ℕ) (o : Ordering) : State k := .inr (.inr (.done o))

/-- Transition budget for the power compare routine. -/
def cost (k c D : ℕ) : ℕ :=
  2 + 1 + TapePower.cost k 1 c + 1 + (4 * min (c ^ k) D + 7)

theorem runs_compare (k : ℕ) {outer source scratch destination target : TapeRegister}
    (hos : outer ≠ source) (hoc : outer ≠ scratch) (hod : outer ≠ destination)
    (hsc : source ≠ scratch) (hsd : source ≠ destination) (hcd : scratch ≠ destination)
    (hot : outer ≠ target) (hdt : destination ≠ target)
    (σ : TapeStore) (c D : ℕ) (ho : σ outer = [])
    (hs : σ source = List.replicate c true) (hc : σ scratch = [])
    (hd : σ destination = []) (ht : σ target = List.replicate D true) :
    RunsIn (program k outer source scratch destination target).step
      (cfg (start k) (storeTapes σ))
      (cfg (done k (TapeUnaryCompareScan.result (c ^ k) D))
        (storeTapes (outputStore k outer destination σ c))) (cost k c D) := by
  have hinc := increment outer (storeTapes σ) 0 (by simp [storeTapes, counterTape, ho])
  have hi : TapeMultiply.tapes outer source scratch destination (storeTapes σ) 1 c 0 0 =
      Function.update (storeTapes σ) outer (counterTape 1) := by
    simpa only [storeTapes_update, counterTape] using
      (frame_store hos hoc hod hsc hsd hcd σ 1 c hs hc hd)
  have hp := TapePower.runs_power k hos hoc hod hsc hsd hcd (storeTapes σ) 1 c
  rw [hi, result_store k hos hoc hod hsc hsd hcd σ c ho hs hc hd] at hp
  have hr : TapePower.resultRegister k outer destination ≠ target :=
    resultRegister_ne k hot hdt
  have hcmp := TapeUnaryCompare.runs_compare hr
    (storeTapes (outputStore k outer destination σ c)) (c ^ k) D
    (by simp [storeTapes])
    (by simp [storeTapes, outputStore, Function.update, Ne.symm hr, ht])
  have hpowerCompare := join_runs (TapePower.program k outer source scratch destination)
    (TapeUnaryCompare.program (TapePower.resultRegister k outer destination) target)
    (fun _ => TapeUnaryCompare.State.scan .beginR)
    hp (TapePower.program_done k outer source scratch destination _) hcmp
  have h := join_runs (incProgram outer)
    (joinCode (TapePower.program k outer source scratch destination)
      (TapeUnaryCompare.program (TapePower.resultRegister k outer destination) target)
      (fun _ => TapeUnaryCompare.State.scan .beginR))
    (fun _ => Sum.inl (TapePower.start k)) hinc rfl hpowerCompare
  simpa only [program, start, done, cost, Nat.add_assoc] using h

@[simp] theorem program_done (k : ℕ)
    (outer source scratch destination target : TapeRegister) (o : Ordering) (h : TapeHeads) :
    program k outer source scratch destination target (done k o) h = none := rfl

end TapePowerCompare
end DepthThreeLowerBound

end Complexity
