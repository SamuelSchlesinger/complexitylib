/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.P.NormalForm
public import Complexitylib.Classes.PPoly.Uniform
public import Complexitylib.Classes.PPoly.Uniform.Containment
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Tableau
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Padded

/-!
# Deterministic unrolling into uniform P/poly -- proof internals

This module packages the direct deterministic unrolling family first through
conditional `FL` seams and then through the verified canonical padded
serializer, yielding the unconditional machines-to-circuits containment.
-/

@[expose] public section

namespace Complexity

namespace TM

/-- Internal packaging of one polynomial-time decider and its direct-code
generator as a logspace-uniform polynomial-size circuit family. -/
theorem DecidesInTime.mem_UniformPPoly_of_directUnrollingCode_mem_FL_internal
    {tm : TM k} {L : Language} (q : Polynomial ℕ)
    (hdec : tm.DecidesInTime L q.eval)
    (hgen : (fun x : List Bool =>
      tm.directUnrollingCode q.eval x.length) ∈ FL) :
    L ∈ UniformPPoly := by
  let F := tm.directUnrollingCircuitFamily q.eval
  have hq : q.eval =O ((· ^ q.natDegree) : ℕ → ℕ) :=
    BigO.of_polynomial_bound q (fun _ => le_rfl)
  have hsizeO : F.size =O ((· ^ (3 * q.natDegree)) : ℕ → ℕ) := by
    dsimp only [F]
    exact tm.directUnrollingCircuitFamily_size_bigO hq
  obtain ⟨sizePoly, hsize⟩ := BigO.pow_polynomial_bound hsizeO
  refine ⟨F, sizePoly, ?_, hsize, ?_⟩
  · dsimp only [F]
    exact hdec.directUnrollingCircuitFamily_decides
  · refine ⟨(fun x => tm.directUnrollingCode q.eval x.length), hgen, ?_⟩
    intro n
    simpa only [F, unaryList, List.length_replicate] using
      (tm.directUnrollingCircuitFamily_encodeAt q.eval n).symm

/-- Internal packaging through the regularly padded family. Unlike the direct
family, its positive gate-count header is a closed polynomial expression. -/
theorem DecidesInTime.mem_UniformPPoly_of_paddedDirectUnrollingCode_mem_FL_internal
    {tm : TM k} {L : Language} (q : Polynomial ℕ)
    (hdec : tm.DecidesInTime L q.eval)
    (hgen : (fun x : List Bool =>
      tm.paddedDirectUnrollingCode q.eval x.length) ∈ FL) :
    L ∈ UniformPPoly := by
  let F := tm.paddedDirectUnrollingCircuitFamily q.eval
  have hq : q.eval =O ((· ^ q.natDegree) : ℕ → ℕ) :=
    BigO.of_polynomial_bound q (fun _ => le_rfl)
  have hsizeO : F.size =O ((· ^ (3 * q.natDegree)) : ℕ → ℕ) := by
    dsimp only [F]
    exact tm.paddedDirectUnrollingCircuitFamily_size_bigO hq
  obtain ⟨sizePoly, hsize⟩ := BigO.pow_polynomial_bound hsizeO
  refine ⟨F, sizePoly, ?_, hsize, ?_⟩
  · dsimp only [F]
    exact hdec.paddedDirectUnrollingCircuitFamily_decides
  · refine ⟨(fun x => tm.paddedDirectUnrollingCode q.eval x.length), hgen, ?_⟩
    intro n
    simpa only [F, unaryList, List.length_replicate] using
      (tm.paddedDirectUnrollingCircuitFamily_encodeAt q.eval n).symm

end TM

/-- Internal conditional containment: if every polynomial-horizon direct
unrolling code map belongs to `FL`, then `P` is contained in uniform P/poly. -/
theorem P_subset_UniformPPoly_of_directUnrollingCode_mem_FL_internal
    (hgen : ∀ {k : ℕ} (tm : TM k) (q : Polynomial ℕ),
      (fun x : List Bool => tm.directUnrollingCode q.eval x.length) ∈ FL) :
    P ⊆ UniformPPoly := by
  intro L hL
  obtain ⟨k, tm, q, hdec⟩ :=
    mem_P_iff_decidesInTime_polynomial.mp hL
  exact hdec.mem_UniformPPoly_of_directUnrollingCode_mem_FL_internal
    q (hgen tm q)

/-- Internal conditional containment through the padded exact-code target. -/
theorem P_subset_UniformPPoly_of_paddedDirectUnrollingCode_mem_FL_internal
    (hgen : ∀ {k : ℕ} (tm : TM k) (q : Polynomial ℕ),
      (fun x : List Bool =>
        tm.paddedDirectUnrollingCode q.eval x.length) ∈ FL) :
    P ⊆ UniformPPoly := by
  intro L hL
  obtain ⟨k, tm, q, hdec⟩ :=
    mem_P_iff_decidesInTime_polynomial.mp hL
  exact hdec.mem_UniformPPoly_of_paddedDirectUnrollingCode_mem_FL_internal
    q (hgen tm q)

namespace TM

open CircuitUnrolling.Serializer.DirectGenerator in
/-- Internal `FL` witness for the regularly padded serializer at the
normalized polynomial horizon. -/
theorem paddedDirectUnrollingCode_mem_FL_internal (tm : TM k)
    (q : Polynomial ℕ) :
    (fun input : List Bool => tm.paddedDirectUnrollingCode
      (directSerializerHorizonPolynomial q).eval input.length) ∈ FL := by
  refine ⟨WorkCount,
    BinaryRoutine.afterInputLength Work.inputLength
      (paddedDirectUnrollingProgram tm q),
    BinaryRoutine.afterInputLengthSpace Work.inputLength
      (paddedDirectUnrollingProgram tm q), ?_, ?_⟩
  · exact paddedDirectUnrollingGenerator_computesInSpace tm q
  · exact paddedDirectUnrollingGenerator_space_bigO_log tm q

/-- Internal unconditional packaging of one polynomial-time decider as a
logspace-uniform polynomial-size circuit family. -/
theorem DecidesInTime.mem_UniformPPoly_internal
    {tm : TM k} {L : Language} (q : Polynomial ℕ)
    (hdec : tm.DecidesInTime L q.eval) : L ∈ UniformPPoly := by
  have hnormalized := hdec.directSerializerHorizon q
  exact hnormalized.mem_UniformPPoly_of_paddedDirectUnrollingCode_mem_FL_internal
    (directSerializerHorizonPolynomial q)
    (tm.paddedDirectUnrollingCode_mem_FL_internal q)

end TM

/-- Internal machines-to-uniform-circuits containment. -/
theorem P_subset_UniformPPoly_internal : P ⊆ UniformPPoly := by
  intro L hL
  obtain ⟨k, tm, q, hdec⟩ := mem_P_iff_decidesInTime_polynomial.mp hL
  exact hdec.mem_UniformPPoly_internal q

/-- Internal logspace-uniform circuit characterization of deterministic
polynomial time. -/
theorem UniformPPoly_eq_P_internal : UniformPPoly = P :=
  Set.Subset.antisymm UniformPPoly_subset_P P_subset_UniformPPoly_internal

end Complexity
