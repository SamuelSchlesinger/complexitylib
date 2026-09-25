/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Interpretation
public import Cslib.Computability.Circuit.Homomorphism

/-!
# Interpretation homomorphisms from CSLib

The homomorphism structure, identities, composition, and their laws are supplied
by CSLib. The names here preserve the existing public imports.
-/

@[expose] public section

namespace Algebraic

export Cslib.Circuits (Homomorphism)

namespace Homomorphism

export Cslib.Circuits.Homomorphism
  (ext id comp id_map comp_map id_comp comp_id comp_assoc)

end Homomorphism
end Algebraic
