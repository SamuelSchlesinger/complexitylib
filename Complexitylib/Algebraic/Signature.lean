/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Cslib.Computability.Circuit.Signature

/-!
# Circuit signatures from CSLib

The library uses CSLib's finite-arity signatures directly. This re-export
preserves the `Algebraic.Signature` name without introducing a second model.
-/

@[expose] public section

namespace Algebraic

export Cslib.Circuits (Signature)

end Algebraic
