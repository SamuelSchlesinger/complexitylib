/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Hoare.Defs

/-!
# State-independent safety contracts

`TM.HoareSafety` requires a tape predicate at every reachable configuration.
Unlike a fixed space predicate, it can charge only selected work tapes while
still bounding the output. Ordinary time contracts supply termination separately.
-/

@[expose] public section

namespace Complexity
namespace TM

/-- Every configuration reachable from a permitted entry satisfies `safe`. -/
def HoareSafety (M : TM n) (pre safe : TapePred n) : Prop :=
  ∀ inp work out, pre inp work out →
    ∀ c, M.reaches { state := M.qstart, input := inp, work := work, output := out } c →
      safe c.input c.work c.output

end TM
end Complexity
