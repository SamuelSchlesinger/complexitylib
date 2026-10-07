/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeHash

/-!
# Unrestricted depth-three lower bound: tape hash clean

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeHashClean.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeHashClean

open TapeMultiProgram TapeRouting TapeRegister

/-- Control states of the hash clean routine. -/
abbrev State := TapeHash.State ⊕ TapeErase.State

/-- Transition function of the hash clean routine. -/
def program : TapeMultiProgram State :=
  joinCode TapeHash.program (TapeErase.code indexC) (fun _ => TapeErase.State.start)

/-- Initial control state of the hash clean routine. -/
def start : State := .inl TapeHash.start
/-- Terminal control state of the hash clean routine. -/
def done : State := .inr TapeErase.State.done

theorem cost_le (d r : ℕ) :
    200 * (d + r + 1) ^ 3 + 1 + (2 * r + 5) ≤ 210 * (d + r + 1) ^ 3 := by
  let N := d + r + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hr : r < N := by dsimp [N]; omega
  have hsq : N ≤ N ^ 2 := by
    simpa only [Nat.mul_one, pow_two] using Nat.mul_le_mul_left N hN
  have hcube : N ≤ N ^ 3 := by
    have h := Nat.mul_le_mul_left N (show 1 ≤ N ^ 2 by omega)
    calc
      N ≤ N * N ^ 2 := by simpa only [Nat.mul_one] using h
      _ = N ^ 3 := by ring
  change 200 * N ^ 3 + 1 + (2 * r + 5) ≤ 210 * N ^ 3
  nlinarith

theorem runs_wordHash (σ : TapeStore) {d r : ℕ}
    (u : BitWord (d + r - 1)) (x : BitWord d)
    (hd : σ dataLength = List.replicate d true)
    (hr : σ ringDegree = List.replicate r true)
    (ha : σ indexA = []) (hb : σ indexB = []) (hc : σ indexC = [])
    (hs : σ scratchA = []) (hh : σ hashBits = [])
    (hkey : σ keyBits = List.ofFn u) (hdata : σ dataBits = List.ofFn x) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update σ hashBits (List.ofFn (wordHash u x)))))
      (210 * (d + r + 1) ^ 3) := by
  let τ := Function.update (Function.update σ hashBits (List.ofFn (wordHash u x)))
    indexC (List.replicate r true)
  have hhash := TapeHash.runs_wordHash σ u x hd hr ha hb hc hs hh hkey hdata
  have herase := TapeStoreRuns.erase indexC τ
  have hall := join_runs TapeHash.program (TapeErase.code indexC)
    (fun _ => TapeErase.State.start) hhash rfl herase
  have hC : (Function.update σ hashBits (List.ofFn (wordHash u x))) indexC = [] := by
    simp [hc, indexC, hashBits]
  have hstore : Function.update τ indexC [] =
      Function.update σ hashBits (List.ofFn (wordHash u x)) := by
    simp only [τ, Function.update_idem, ← hC, Function.update_eq_self]
  have hlen : (τ indexC).length = r := by simp [τ]
  have hall' : RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update σ hashBits (List.ofFn (wordHash u x)))))
      (200 * (d + r + 1) ^ 3 + 1 + (2 * r + 5)) := by
    simpa only [program, start, done, hstore, hlen] using hall
  exact hall'.mono (cost_le d r)

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeHashClean
end DepthThreeLowerBound

end Complexity
