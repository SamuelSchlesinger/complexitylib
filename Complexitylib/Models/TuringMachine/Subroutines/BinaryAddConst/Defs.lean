/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Registers.RegisterOps
public import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc.Defs

/-!
# Addition of a fixed natural to a canonical binary tape — definitions

A fixed constant is compiled into finitely many sequential applications of
canonical binary successor. No work tape is needed for the hardwired value,
so the construction preserves every tape except its destination.
-/

@[expose] public section

namespace Complexity

namespace TM

/-- Add a hardwired natural to one canonical binary work tape. -/
def binaryAddConstTM {n : ℕ} (idx : Fin n) : ℕ → TM n
  | 0 => skipTM
  | constant + 1 =>
      seqTM (binaryAddConstTM idx constant) (binarySuccTM idx)

/-- Exact runtime of fixed-constant binary addition. -/
def binaryAddConstTime (constant dstValue : ℕ) : ℕ :=
  match constant with
  | 0 => 1
  | constant + 1 =>
      binaryAddConstTime constant dstValue + 1 +
        binarySuccTime (dstValue + constant)

/-- All-prefix width-based space bound for fixed-constant addition. -/
def binaryAddConstSpace
    (initialSpace constant dstValue : ℕ) : ℕ :=
  initialSpace + 2 * (dstValue + constant).size + 3

end TM

end Complexity
