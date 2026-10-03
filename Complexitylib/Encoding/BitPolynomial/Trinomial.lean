/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Trinomial.Defs
import Complexitylib.Encoding.BitPolynomial.Trinomial.Internal

/-!
# Exact binary trinomial generation

The runtime coefficient generator denotes `X^(2*d) + X^d + 1` and has
exact length `2*d+1`, including `d=0`. Irreducibility at selected degrees
is a separate algebraic theorem. The uniform polynomial-time certificate
is supplied by `Complexitylib.Classes.P.BitPolynomial.Trinomial`.
-/

public section

namespace Complexity
namespace BitPolynomial

/-- The generated coefficient list retains its leading coefficient. -/
theorem trinomialBits_length (d : Nat) : (trinomialBits d).length = 2 * d + 1 :=
  Internal.trinomialBits_length d

/-- The concrete list represents the three-term polynomial, even at degree zero. -/
theorem ofBits_trinomialBits (d : Nat) :
    ofBits (trinomialBits d) =
      Polynomial.X ^ (2 * d) + Polynomial.X ^ d + 1 :=
  Internal.ofBits_trinomialBits d

end BitPolynomial
end Complexity
