/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Aesop

/-! # Rule set for Complexitylib's polynomial-time certificates -/

public section

namespace Complexity

declare_aesop_rule_sets [ComplexityPolyTime]

/-- Register a proved closure rule or algorithm certificate for `polytime`.
Unindexed matching also finds a closure rule when its input function simplifies to identity. -/
macro "polytime" : attr =>
  `(attr| aesop safe apply (transparency := reducible)
    (index := [unindexed]) (rule_sets := [ComplexityPolyTime]))

end Complexity
