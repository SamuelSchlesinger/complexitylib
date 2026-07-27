/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.DescriptiveComplexity.Encoding
public import Complexitylib.DescriptiveComplexity.Query
public import Complexitylib.Models.TuringMachine

/-!
# The language induced by a Boolean query

The bridge from descriptive complexity to the machine model: a Boolean query over
finite structures induces a **language** (a set of bit strings) — the encodings of
the structures satisfying it. This is where a logical characterization of a query
becomes a statement about a machine-model `Language`, the connection Fagin's
theorem (`NP = ∃SO`) and the other logic/complexity correspondences on track L6
ultimately rest on.

## Main definitions and results

- `DescriptiveComplexity.queryLanguage` — the language of a query.
- `DescriptiveComplexity.mem_queryLanguage` — a `Q`-satisfying structure's encoding
  is in `Q`'s language.
-/

@[expose] public section

namespace Complexity

namespace DescriptiveComplexity

variable {V : Vocabulary}

/-- The **language induced by a Boolean query** `Q`: the set of bit strings that
    encode a (decidable) structure satisfying `Q`. -/
def queryLanguage (Q : BooleanQuery V) : Language :=
  { x | ∃ A : DecFinStruct V, encodeStruct A = x ∧ Q A.toFinStruct }

/-- Encoding a `Q`-satisfying structure lands in `Q`'s induced language. -/
theorem mem_queryLanguage (Q : BooleanQuery V) (A : DecFinStruct V)
    (hQ : Q A.toFinStruct) : encodeStruct A ∈ queryLanguage Q :=
  ⟨A, rfl, hQ⟩

end DescriptiveComplexity

end Complexity
