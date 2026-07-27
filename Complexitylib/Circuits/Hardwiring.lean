/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Nondeterminism

/-!
# Hardwiring Prefixes of Circuit Inputs

Fix a prefix of a fan-in-two AND/OR circuit's inputs without changing its gate
count. This is the circuit-level operation used to turn length-dependent advice
or random seeds into nonuniform constants while leaving the ordinary input live.

The live suffix has positive arity, matching the typed `Circuit` convention.
Circuit families represent the zero-input member separately with `emptyOutput`.

## Main definitions

- `Circuit.castInputArity`: transport a circuit across equal input arities.
- `Circuit.restrictPrefix`: hardwire the first `k` inputs to a fixed bit string.

## Main results

- `Circuit.restrictPrefix_eval`: evaluation agrees with supplying `seed ++ input`.
- `Circuit.restrictPrefix_size`: hardwiring preserves the exact circuit size.
-/

@[expose] public section

namespace Complexity

namespace Circuit

/-- Transport a circuit across an equality of input arities. -/
def castInputArity {B : Basis} {N N' M G : ℕ} [NeZero N] [NeZero N']
    [NeZero M] (h : N = N') (circuit : Circuit B N M G) :
    Circuit B N' M G := by
  subst N'
  exact circuit

/-- Fix the first `k` inputs of a fan-in-two AND/OR circuit to `seed`.

The remaining positive number `m` of inputs retain their order, and the
internal gate count `G` is unchanged. The zero-length prefix is the identity
after canonical input-arity transport. -/
def restrictPrefix {m G : ℕ} [NeZero m] :
    {k : ℕ} → BitString k → Circuit Basis.andOr2 (k + m) 1 G →
      Circuit Basis.andOr2 m 1 G
  | 0, _, circuit => castInputArity (Nat.zero_add m) circuit
  | k + 1, seed, circuit =>
      restrictPrefix (Fin.tail seed)
        (Complexity.restrictCircuit (k := k) (seed 0) circuit)

/-- Prepending the head of `seed` to its tail and then appending `input`
recovers `seed ++ input` in the indexing convention used by `restrictFirst`. -/
private theorem prepend_tail_append {k m : ℕ} (seed : BitString (k + 1))
    (input : BitString m) :
    (fun i : Fin ((k + 1) + m) =>
      if h : i.val = 0 then seed 0
      else Fin.append (Fin.tail seed) input ⟨i.val - 1, by omega⟩) =
      Fin.append seed input := by
  ext i
  rcases i with ⟨i, hi⟩
  simp only [Fin.append, Fin.addCases, Fin.tail]
  split_ifs with hzero hleft hright <;> simp_all <;> try omega
  all_goals congr 1 <;> simp_all [Fin.ext_iff] <;> omega

/-- Evaluation commutes with transporting a circuit's input arity. -/
private theorem eval_castInputArity {N N' G : ℕ} [NeZero N] [NeZero N']
    (h : N = N') (circuit : Circuit Basis.andOr2 N 1 G)
    (input : BitString N') :
    ((castInputArity h circuit).eval input) 0 =
      (circuit.eval (input ∘ Fin.cast h)) 0 := by
  subst N'
  rfl

/-- Prefix hardwiring agrees with evaluating the original circuit on the fixed
prefix followed by the live input. -/
theorem restrictPrefix_eval {k m G : ℕ} [NeZero m]
    (seed : BitString k) (circuit : Circuit Basis.andOr2 (k + m) 1 G)
    (input : BitString m) :
    ((restrictPrefix seed circuit).eval input) 0 =
      (circuit.eval (Fin.append seed input)) 0 := by
  induction k with
  | zero =>
      have hseed : seed = Fin.elim0 := Subsingleton.elim _ _
      subst seed
      simpa only [restrictPrefix, Fin.elim0_append] using
        eval_castInputArity (Nat.zero_add m) circuit input
  | succ k ih =>
      rw [restrictPrefix]
      rw [ih]
      have hstep := congrFun
        (Complexity.restrictCircuit_eval (k := k) (seed 0) circuit
          (fun x => (circuit.eval x) 0) rfl)
        (Fin.append (Fin.tail seed) input)
      rw [hstep]
      simp only [restrictFirst]
      rw [prepend_tail_append seed input]

/-- Prefix hardwiring preserves the exact circuit size. -/
@[simp] theorem restrictPrefix_size {k m G : ℕ} [NeZero m]
    (seed : BitString k) (circuit : Circuit Basis.andOr2 (k + m) 1 G) :
    (restrictPrefix seed circuit).size = circuit.size := by
  rfl

end Circuit

end Complexity
