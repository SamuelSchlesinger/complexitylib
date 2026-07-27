/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.XOR

/-!
# Parity on a finite support -- definitions

Random restrictions leave parity on the remaining free coordinates, possibly
complemented by the fixed coordinates. `xorOn` makes that support explicit.
-/

@[expose] public section

namespace Complexity
namespace Schnorr

/-- Boolean exclusive-or as an explicitly named commutative fold operation. -/
def xorOp (left right : Bool) : Bool :=
  left.xor right

instance xorOp_commutative : Std.Commutative xorOp :=
  ⟨by
    intro left right
    cases left <;> cases right <;> rfl⟩

instance xorOp_associative : Std.Associative xorOp :=
  ⟨by
    intro left middle right
    cases left <;> cases middle <;> cases right <;> rfl⟩

/-- XOR of exactly the coordinates in `support`. -/
def xorOn (support : Finset (Fin N)) (input : BitString N) : Bool :=
  support.fold xorOp false input

end Schnorr
end Complexity
