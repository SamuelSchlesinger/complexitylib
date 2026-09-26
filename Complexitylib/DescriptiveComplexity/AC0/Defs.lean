/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Language
public import Complexitylib.Circuits.Family.Defs

/-!
# Characteristic Boolean families of structural queries

`queryFamily` is the characteristic family of the existing binary
`queryLanguage`, at every input length. It rejects all strings that are not
structure encodings. The definition uses classical decidability of a general
query; membership in a circuit class will be proved separately from a logical
definability witness.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

/-- The characteristic Boolean-function family of an encoded structural query. -/
noncomputable def queryFamily {V : Vocabulary} (Q : BooleanQuery V) : BoolFunFamily :=
  fun _ input => by classical exact decide (List.ofFn input ∈ queryLanguage Q)

end Complexity.DescriptiveComplexity
