/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Containment.Internal

/-!
# Deterministic unrolling into uniform P/poly

This module packages the verified log-space tableau serializer into the
machines-to-circuits direction of uniform P/poly. The conditional seams remain
available for alternate serializers, while the canonical padded serializer
discharges them unconditionally.

## Main results

- `TM.DecidesInTime.mem_UniformPPoly_of_directUnrollingCode_mem_FL` packages
  one polynomial-time decider and direct-code generator.
- `P_subset_UniformPPoly_of_directUnrollingCode_mem_FL` packages the resulting
  conditional class containment.
- The corresponding `paddedDirectUnrollingCode` theorems target the regular
  family whose gate-count header is known before gate emission begins.
- `P_subset_UniformPPoly` and `UniformPPoly_eq_P` are the completed headline.
-/

@[expose] public section

namespace Complexity

namespace TM

/-- A polynomial-time decider belongs to uniform P/poly whenever its direct
unrolling code map is computable in logarithmic space. -/
theorem DecidesInTime.mem_UniformPPoly_of_directUnrollingCode_mem_FL
    {tm : TM k} {L : Language} (q : Polynomial ℕ)
    (hdec : tm.DecidesInTime L q.eval)
    (hgen : (fun x : List Bool =>
      tm.directUnrollingCode q.eval x.length) ∈ FL) :
    L ∈ UniformPPoly :=
  hdec.mem_UniformPPoly_of_directUnrollingCode_mem_FL_internal q hgen

/-- A polynomial-time decider belongs to uniform P/poly whenever its regularly
padded exact code map is computable in logarithmic space. -/
theorem DecidesInTime.mem_UniformPPoly_of_paddedDirectUnrollingCode_mem_FL
    {tm : TM k} {L : Language} (q : Polynomial ℕ)
    (hdec : tm.DecidesInTime L q.eval)
    (hgen : (fun x : List Bool =>
      tm.paddedDirectUnrollingCode q.eval x.length) ∈ FL) :
    L ∈ UniformPPoly :=
  hdec.mem_UniformPPoly_of_paddedDirectUnrollingCode_mem_FL_internal q hgen

end TM

/-- If every polynomial-horizon direct unrolling code map belongs to `FL`,
then every language in `P` has a logspace-uniform polynomial-size circuit
family. -/
theorem P_subset_UniformPPoly_of_directUnrollingCode_mem_FL
    (hgen : ∀ {k : ℕ} (tm : TM k) (q : Polynomial ℕ),
      (fun x : List Bool => tm.directUnrollingCode q.eval x.length) ∈ FL) :
    P ⊆ UniformPPoly :=
  P_subset_UniformPPoly_of_directUnrollingCode_mem_FL_internal hgen

/-- If every polynomial-horizon padded unrolling code map belongs to `FL`,
then every language in `P` has a logspace-uniform polynomial-size family. -/
theorem P_subset_UniformPPoly_of_paddedDirectUnrollingCode_mem_FL
    (hgen : ∀ {k : ℕ} (tm : TM k) (q : Polynomial ℕ),
      (fun x : List Bool =>
        tm.paddedDirectUnrollingCode q.eval x.length) ∈ FL) :
    P ⊆ UniformPPoly :=
  P_subset_UniformPPoly_of_paddedDirectUnrollingCode_mem_FL_internal hgen

namespace TM

/-- The canonical streaming transducer computes every regularly padded direct
unrolling code at the normalized polynomial horizon in logarithmic space. -/
theorem paddedDirectUnrollingCode_mem_FL (tm : TM k) (q : Polynomial ℕ) :
    (fun input : List Bool => tm.paddedDirectUnrollingCode
      (directSerializerHorizonPolynomial q).eval input.length) ∈ FL :=
  tm.paddedDirectUnrollingCode_mem_FL_internal q

/-- Every language decided by a deterministic machine within a polynomial
time bound has a logspace-uniform polynomial-size circuit family. -/
theorem DecidesInTime.mem_UniformPPoly
    {tm : TM k} {L : Language} (q : Polynomial ℕ)
    (hdec : tm.DecidesInTime L q.eval) : L ∈ UniformPPoly :=
  hdec.mem_UniformPPoly_internal q

end TM

/-- Deterministic polynomial time is contained in logspace-uniform P/poly. -/
theorem P_subset_UniformPPoly : P ⊆ UniformPPoly :=
  P_subset_UniformPPoly_internal

/-- Logspace-uniform polynomial-size circuits characterize deterministic
polynomial time. -/
theorem UniformPPoly_eq_P : UniformPPoly = P :=
  UniformPPoly_eq_P_internal

end Complexity
