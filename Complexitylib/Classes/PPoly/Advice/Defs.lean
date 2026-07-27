/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Asymptotics
public import Complexitylib.Classes.Pairing
public import Complexitylib.Classes.PPoly.Defs
public import Complexitylib.Circuits.Unrolling.Acceptance.Hardwiring

/-!
# Polynomial advice — definitions

Advice is a length-indexed binary string. An advised machine receives the
self-delimiting encoding `pair (advice n) x` on its read-only input tape, while
time remains charged against the original input length `n`.

This file also defines the nonuniform circuit family obtained by fixing both
the deterministic choice prefix and the length-dependent advice prefix of a
bounded acceptance circuit.
-/

@[expose] public section

namespace Complexity

/-- A binary advice string for every original input length. -/
abbrev Advice := ℕ → List Bool

/-- Put the length-dependent advice before the ordinary input using the
self-delimiting pairing encoding. -/
def advisedInput (a : Advice) (x : List Bool) : List Bool :=
  pair (a x.length) x

/-- Advice has polynomial length when one natural-coefficient polynomial
bounds every advice string. -/
def PolynomialAdvice (a : Advice) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, (a n).length ≤ p.eval n

namespace Advice

/-- The fixed prefix preceding an ordinary `n`-bit input. -/
def fixedPrefix (a : Advice) (n : ℕ) : List Bool :=
  pair (a n) []

/-- The full advised input as a fixed-length bit string, factored into its
fixed prefix followed by the live ordinary input. -/
def inputBits (a : Advice) {n : ℕ} (x : BitString n) :
    BitString ((a.fixedPrefix n).length + n) :=
  Fin.append (a.fixedPrefix n).get x

end Advice

namespace TM

/-- A DTM decides `L` with advice `a` in time `T` when it starts on
`pair (a |x|) x`, halts within `T |x|`, and writes the ordinary language verdict.
The resource bound is indexed by the original input length, not the paired
input length. -/
def DecidesWithAdviceInTime (tm : TM k) (a : Advice) (L : Language)
    (T : ℕ → ℕ) : Prop :=
  ∀ x, ∃ c' t, t ≤ T x.length ∧
    tm.reachesIn t (tm.initCfg (advisedInput a x)) c' ∧ tm.halted c' ∧
    (x ∈ L → c'.output.cells 1 = Γ.one) ∧
    (x ∉ L → c'.output.cells 1 = Γ.zero)

/-- Exact fixed-horizon advised acceptance predicate on a fixed-length live
input. -/
def advisedBoundedAcceptanceBit (tm : TM k) (a : Advice)
    (T : ℕ → ℕ) {n : ℕ} (x : BitString n) : Bool :=
  CircuitUnrolling.boundedAcceptanceBit tm.toNTM (T n) (a.inputBits x)
    (fun _ => false)

/-- The nonuniform family obtained by hardwiring the advice for each length
into the bounded deterministic acceptance circuit. -/
noncomputable def adviceCircuitFamily (tm : TM k) (a : Advice)
    (T : ℕ → ℕ) : CircuitFamily Basis.andOr2 := by
  classical
  exact
    { emptyOutput := tm.advisedBoundedAcceptanceBit a T (fun i => Fin.elim0 i)
      circuits := fun n _ =>
        ⟨_, Circuit.restrictPrefix (a.fixedPrefix n).get
          (CircuitUnrolling.fixedChoicesAcceptanceCircuit tm.toNTM (T n)
            ((a.fixedPrefix n).length + n) (fun _ => false))⟩ }

end TM

/-- Languages decided in polynomial time with polynomial-length advice. -/
def PAdvice : Set Language :=
  {L | ∃ (d k : ℕ) (tm : TM k) (a : Advice) (T : ℕ → ℕ),
    PolynomialAdvice a ∧ tm.DecidesWithAdviceInTime a L T ∧
      T =O ((· ^ d) : ℕ → ℕ)}

end Complexity
