/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Linear hashing by field multiplication and additive projection

Multiply the source by a uniformly chosen field element, then apply an
additive projection. Surjectivity of the projection gives the universal
collision bound. In binary coefficient coordinates, projection onto an
initial segment is the multiply-and-truncate construction used in
Guruswami--Umans--Vadhan (2009), Lemma 5.1:
https://people.seas.harvard.edu/~salil/research/PVcondenser-jacm.pdf.
The seed ranges over the entire field, including zero.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Multiply by the field seed and apply an additive projection. -/
def fieldHash {F Ω : Type*} [Field F] [AddCommGroup Ω]
    (projection : F →+ Ω) (source seed : F) : Ω :=
  projection (seed * source)

end Algebraic.Cutwidth.Extractor
