/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.XOR

/-!
# The deterministic XOR source reduction

At each outer coordinate, XOR the correlation-breaker bits obtained from
all sampler candidates. The sampler and correlation breaker read the same
original input. This is the actual reduction in Chattopadhyay--Liao,
*Extractors for Sum of Two Sources*, Lemma 5.4:
<https://arxiv.org/abs/2110.12652>.

The definition imposes no statistical premise. Those premises belong to
the bad-seed and parity theorems for its component calls.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- XOR all candidate outputs at each outer sampler coordinate. -/
def affineSourceReduction {n N C : Nat} {Seed Advice : Type*}
    (cb : (Fin n → Bool) → Seed → Advice → Bool)
    (sampler : (Fin n → Bool) → Fin N → Fin C → Seed)
    (advice : Fin N → Fin C → Advice) (x : Fin n → Bool) (i : Fin N) : Bool :=
  Complexity.Schnorr.xorBool C (fun z => cb x (sampler x i z) (advice i z))

end Algebraic.Cutwidth.Extractor
