/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Defs
import Complexitylib.Circuits.Encoding.Machine.NatCode.Defs

/-!
# Machine emission of width-five branching-program instructions -- definitions

A serialized instruction consists of a terminated-unary variable field followed
by two fixed seven-bit permutation ranks.  The variable is read from a preserved
canonical binary work tape, while the two permutations are baked into finite
control.  One reusable zero scratch tape drives the natural-code emitter.
-/

namespace Complexity

namespace BPCode

namespace Machine

/-- Emit one width-five instruction from a canonical binary variable tape and
two finite-control permutations. -/
def emitInstrTM {n : ℕ} (counterIdx varIdx : Fin n)
    (perm0 perm1 : Equiv.Perm (Fin 5)) : TM n :=
  TM.seqTM
    (CircuitCode.Machine.emitNatCodeTM counterIdx varIdx)
    (TM.emitBitsTM (Perm5.encode perm0 ++ Perm5.encode perm1))

/-- Concrete time bound for one serialized instruction. -/
def emitInstrTime (varValue : ℕ) : ℕ :=
  CircuitCode.Machine.emitNatCodeTime varValue + 15

/-- All-prefix auxiliary-space bound for one serialized instruction. -/
def emitInstrSpace (initialSpace varValue : ℕ) : ℕ :=
  initialSpace + 2 * varValue.size + 14

/-- Emit the constant instruction selected by a `true` formula leaf. -/
def emitConstInstrTM {n : ℕ} (counterIdx zeroIdx : Fin n)
    (target : Equiv.Perm (Fin 5)) : TM n :=
  emitInstrTM counterIdx zeroIdx target target

/-- Emit the variable instruction selected by a variable formula leaf. -/
def emitVarInstrTM {n : ℕ} (counterIdx varIdx : Fin n)
    (target : Equiv.Perm (Fin 5)) : TM n :=
  emitInstrTM counterIdx varIdx 1 target

end Machine

end BPCode

end Complexity
