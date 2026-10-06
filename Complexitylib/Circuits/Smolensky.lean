/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Smolensky.Defs
public import Complexitylib.Circuits.Smolensky.Internal.Circuit

/-!
# Smolensky's polynomial approximation

Smolensky's lower bound approximates circuits with `MOD_3` gates by low-degree
functions over `ZMod 3` (`Smolensky.lowDegree`, functions `{0,1}^n → ZMod 3` in
place of formal polynomials). This module proves the approximation theorem
`Smolensky.exists_lowDegree_approx`: with a fixed choice of `ℓ` subsets per OR
or AND gate, a depth-`d` circuit agrees with a function of degree at most
`(2ℓ)^d` on all but `size · 2^n / 2^ℓ` inputs. The random choices of the usual
proof are replaced by exact double counting over all tuples of subsets.

The circuits are the library's typed circuits over `Basis.unboundedAndOrMod 3`:
a `MOD_3` gate outputs `true` exactly when the number of its true inputs is not
divisible by `3`, negations are free per-input flags, the size `G + 1` counts the
internal gates and the output gate, and the depth counts the output gate.
-/


public section

namespace Complexity

namespace Smolensky

/-- **Smolensky's approximation theorem.** A single-output circuit of
unbounded-fan-in AND, OR, and `MOD_3` gates of depth at most `d` agrees with a
function `{0,1}^n → ZMod 3` of degree at most `(2ℓ)^d` on all but at most
`size · 2^n / 2^ℓ` inputs, for every `ℓ ≥ 1`. -/
theorem exists_lowDegree_approx {n G d ℓ : ℕ} [NeZero n]
    (C : Circuit (Basis.unboundedAndOrMod 3) n 1 G) (hdepth : C.depth ≤ d)
    (hℓ : 1 ≤ ℓ) :
    ∃ P ∈ lowDegree n ((2 * ℓ) ^ d),
      (Finset.univ.filter fun x => P x ≠ bitVal (C.eval x 0)).card * 2 ^ ℓ ≤
        C.size * 2 ^ n :=
  exists_lowDegree_approx_internal C hdepth hℓ

end Smolensky

end Complexity
