/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeHashInitialize
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeHashOuter

/-!
# Unrestricted depth-three lower bound: tape hash

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeHash.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeHash

open TapeMultiProgram TapeRouting TapeRegister

/-- Control states of the hash routine. -/
abbrev State := TapeHashInitialize.State ⊕ TapeHashOuter.State

/-- Transition function of the hash routine. -/
def program : TapeMultiProgram State :=
  joinCode TapeHashInitialize.program TapeHashOuter.program (fun _ => TapeHashOuter.start)

/-- Initial control state of the hash routine. -/
def start : State := .inl TapeHashInitialize.start
/-- Terminal control state of the hash routine. -/
def done : State := .inr TapeHashOuter.done

/-- Tape-store contents at the result stage of the hash routine. -/
def resultStore (σ : TapeStore) (r : ℕ) : TapeStore :=
  Function.update (Function.update σ hashBits (hashByUpdates r (σ keyBits) (σ dataBits)))
    indexC (List.replicate r true)

theorem cost_le (d r : ℕ) :
    10 * r + 8 + 1 + (r * (64 * (d + r + 1) ^ 2 + 4 * r + 12) + (4 * r + 8)) ≤
      200 * (d + r + 1) ^ 3 := by
  let N := d + r + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hr : r ≤ N := by dsimp [N]; omega
  have hsq : N ≤ N ^ 2 := by
    have h := Nat.mul_le_mul_left N hN
    simpa only [Nat.mul_one, pow_two] using h
  have hterm : 64 * N ^ 2 + 4 * r + 12 ≤ 80 * N ^ 2 := by nlinarith
  have hprod := Nat.mul_le_mul hr hterm
  have hprod' : r * (64 * N ^ 2 + 4 * r + 12) ≤ 80 * N ^ 3 := by
    calc
      _ ≤ N * (80 * N ^ 2) := hprod
      _ = _ := by ring
  have hcube : N ≤ N ^ 3 := by
    have h := Nat.mul_le_mul_left N (show 1 ≤ N ^ 2 by omega)
    calc
      N ≤ N * N ^ 2 := by simpa only [Nat.mul_one] using h
      _ = N ^ 3 := by ring
  change 10 * r + 8 + 1 + (r * (64 * N ^ 2 + 4 * r + 12) + (4 * r + 8)) ≤ 200 * N ^ 3
  nlinarith

theorem runs_hash (σ : TapeStore) (d r : ℕ)
    (hd : σ dataLength = List.replicate d true)
    (hr : σ ringDegree = List.replicate r true)
    (ha : σ indexA = []) (hb : σ indexB = []) (hc : σ indexC = [])
    (hs : σ scratchA = []) (hh : σ hashBits = [])
    (hkey : (σ keyBits).length = d + r - 1) (hdata : (σ dataBits).length = d) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (resultStore σ r))) (200 * (d + r + 1) ^ 3) := by
  let τ := Function.update σ hashBits (List.replicate r false)
  have hinit := TapeHashInitialize.runs_initialize σ r hr hs hh
  have houter := TapeHashOuter.runs_outer τ d r
    (by simp [τ, hd, dataLength, hashBits])
    (by simp [τ, hr, ringDegree, hashBits])
    (by simp [τ, ha, indexA, hashBits])
    (by simp [τ, hb, indexB, hashBits])
    (by simp [τ, hc, indexC, hashBits])
    (by simpa [τ, keyBits, hashBits] using hkey)
    (by simpa [τ, dataBits, hashBits] using hdata)
    (by simp [τ])
  have hall := join_runs TapeHashInitialize.program TapeHashOuter.program
    (fun _ => TapeHashOuter.start) hinit rfl houter
  have hstore : TapeHashOuter.progressStore τ r = resultStore σ r := by
    funext q
    by_cases hc' : q = indexC
    · subst q
      simp [TapeHashOuter.progressStore, resultStore]
    · by_cases hh' : q = hashBits
      · subst q
        simp [TapeHashOuter.progressStore, resultStore, hashByUpdates, τ,
          indexC, hashBits, keyBits, dataBits]
      · simp [TapeHashOuter.progressStore, resultStore, τ, hc', hh']
  have hbounded := hall.mono (cost_le d r)
  simpa only [program, start, done, hstore] using hbounded

theorem runs_wordHash (σ : TapeStore) {d r : ℕ}
    (u : BitWord (d + r - 1)) (x : BitWord d)
    (hd : σ dataLength = List.replicate d true)
    (hr : σ ringDegree = List.replicate r true)
    (ha : σ indexA = []) (hb : σ indexB = []) (hc : σ indexC = [])
    (hs : σ scratchA = []) (hh : σ hashBits = [])
    (hkey : σ keyBits = List.ofFn u) (hdata : σ dataBits = List.ofFn x) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update (Function.update σ hashBits
        (List.ofFn (wordHash u x))) indexC (List.replicate r true))))
      (200 * (d + r + 1) ^ 3) := by
  have h := runs_hash σ d r hd hr ha hb hc hs hh
    (by simp [hkey]) (by simp [hdata])
  simpa only [resultStore, hkey, hdata, hashByUpdates_ofFn_eq] using h

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeHash
end DepthThreeLowerBound

end Complexity
