/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Field.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Field.Internal

/-!
# Universal linear hashing from a finite field

Field multiplication followed by any surjective additive projection is a
universal family, with exact collision fraction reciprocal to the output
cardinality. Every fixed-seed map is additive and sends zero to zero. This
does not assert pairwise independence: all maps agree at the zero input.
The multiply-and-truncate source is credited in `Hashing.Field.Defs`.
-/

public section

namespace Algebraic.Cutwidth.Extractor

variable {F Ω : Type*} [Field F] [AddCommGroup Ω]

/-- Every fixed-seed field hash preserves source addition. -/
theorem fieldHash_add (projection : F →+ Ω) (a b seed : F) :
    fieldHash projection (a + b) seed =
      fieldHash projection a seed + fieldHash projection b seed :=
  Internal.fieldHash_add projection a b seed

/-- Every fixed-seed field hash sends zero to zero. -/
theorem fieldHash_zero (projection : F →+ Ω) (seed : F) :
    fieldHash projection 0 seed = 0 :=
  Internal.fieldHash_zero projection seed

/-- Colliding hashes are exactly the seeds whose scaled difference lies in the kernel. -/
theorem fieldHash_collision_iff (projection : F →+ Ω) (a b seed : F) :
    fieldHash projection a seed = fieldHash projection b seed ↔
      projection (seed * (a - b)) = 0 :=
  Internal.fieldHash_collision_iff projection a b seed

open scoped Classical in
/-- A surjective projection gives the exact number of collision seeds. -/
theorem fieldHash_collision_count [Fintype F] [Fintype Ω]
    (projection : F →+ Ω) (surjective : Function.Surjective projection)
    {a b : F} (distinct : a ≠ b) :
    (Finset.univ.filter fun seed => fieldHash projection a seed =
      fieldHash projection b seed).card * Fintype.card Ω = Fintype.card F :=
  Internal.fieldHash_collision_count projection surjective distinct

/-- Multiplication followed by a surjective additive projection is universal. -/
theorem fieldHash_universal [Fintype F] [Fintype Ω]
    (projection : F →+ Ω) (surjective : Function.Surjective projection) :
    UniversalHashFamily (fieldHash projection) :=
  Internal.fieldHash_universal projection surjective

end Algebraic.Cutwidth.Extractor
