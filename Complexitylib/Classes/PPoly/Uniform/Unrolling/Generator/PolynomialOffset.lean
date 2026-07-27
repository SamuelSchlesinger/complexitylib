/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.PolynomialOffset.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.PolynomialOffset.Internal

/-!
# Polynomial recent-wire offsets

Proof-carrying evaluation and raw-gate emission for recent-wire offsets that
are fixed polynomials in the run-time tableau horizon.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Fixed-polynomial offset preparation is sound. -/
theorem preparePolynomialOffset_sound (polynomial : Polynomial ℕ)
    (extra : ℕ := 0) :
    (preparePolynomialOffset polynomial extra).Sound :=
  preparePolynomialOffset_sound_internal polynomial extra

/-- Exact zero-scratch domain for fixed-polynomial offset preparation. -/
theorem preparePolynomialOffset_requires (polynomial : Polynomial ℕ)
    (extra : ℕ) (values : BinaryValues WorkCount) :
    (preparePolynomialOffset polynomial extra).requires values ↔
      values Work.temporary₃ = 0 ∧
        values Work.polynomialScratch = 0 ∧
        values Work.multiplyCounter = 0 ∧
        values Work.addCounter = 0 :=
  preparePolynomialOffset_requires_internal polynomial extra values

/-- Exact evaluated polynomial offset. -/
@[simp] theorem preparePolynomialOffset_effect (polynomial : Polynomial ℕ)
    (extra : ℕ) (values : BinaryValues WorkCount) :
    (preparePolynomialOffset polynomial extra).effect values =
      Function.update values Work.temporary₃
        (polynomial.eval (values Work.horizon) + extra) :=
  preparePolynomialOffset_effect_internal polynomial extra values

/-- Polynomial-offset preparation emits no circuit-code bits. -/
@[simp] theorem preparePolynomialOffset_emitted (polynomial : Polynomial ℕ)
    (extra : ℕ) (values : BinaryValues WorkCount) :
    (preparePolynomialOffset polynomial extra).emitted values = [] :=
  preparePolynomialOffset_emitted_internal polynomial extra values

/-- Fixed-polynomial offset preparation has a pointwise width certificate
when both its explicit Horner-prefix cap and final evaluated offset fit the
shared width. -/
theorem preparePolynomialOffset_spaceBoundByWidth
    (polynomial : Polynomial ℕ) (extra : ℕ)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hpolynomialCap : ∀ inputLength,
      2 * TM.binaryPolynomialValueCap polynomial
          (values inputLength Work.horizon) ≤ width inputLength)
    (hoffset : ∀ inputLength,
      polynomial.eval (values inputLength Work.horizon) + extra ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (preparePolynomialOffset polynomial extra) initialSpace values width :=
  preparePolynomialOffset_spaceBoundByWidth_internal polynomial extra
    hpolynomialCap hoffset

/-- Polynomial recent-gate emission is sound. -/
theorem emitPolynomialRecentGate_sound (polynomial : Polynomial ℕ)
    (extra : ℕ) (op : AndOrOp) (negated₀ negated₁ : Bool)
    (fixedOffset₁ : ℕ) :
    (emitPolynomialRecentGate polynomial extra op negated₀ negated₁
        fixedOffset₁).Sound :=
  emitPolynomialRecentGate_sound_internal polynomial extra op negated₀
    negated₁ fixedOffset₁

/-- Polynomial recent-gate emission has a pointwise width certificate when
the evaluator cap, width-bounded wire frontier and old references, zero loop
controller, and both valid offsets are supplied explicitly. -/
theorem emitPolynomialRecentGate_spaceBoundByWidth
    (polynomial : Polynomial ℕ) (extra : ℕ) (op : AndOrOp)
    (negated₀ negated₁ : Bool) (fixedOffset₁ : ℕ)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hpolynomialCap : ∀ inputLength,
      2 * TM.binaryPolynomialValueCap polynomial
          (values inputLength Work.horizon) ≤ width inputLength)
    (havailable : ∀ inputLength,
      values inputLength Work.available ≤ width inputLength)
    (hreference₀ : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength)
    (hreference₁ : ∀ inputLength,
      values inputLength Work.reference₁ ≤ width inputLength)
    (hloop : ∀ inputLength, values inputLength Work.loop₃ = 0)
    (hoffsetAvailable : ∀ inputLength,
      polynomial.eval (values inputLength Work.horizon) + extra ≤
        values inputLength Work.available)
    (hfixedOffset₁ : ∀ inputLength,
      fixedOffset₁ ≤ values inputLength Work.available) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitPolynomialRecentGate polynomial extra op negated₀ negated₁
        fixedOffset₁) initialSpace values width :=
  emitPolynomialRecentGate_spaceBoundByWidth_internal polynomial extra op
    negated₀ negated₁ fixedOffset₁ hpolynomialCap havailable hreference₀
    hreference₁ hloop hoffsetAvailable hfixedOffset₁

/-- Exact zero-scratch and valid-offset domain for polynomial recent-gate
emission. -/
theorem emitPolynomialRecentGate_requires (polynomial : Polynomial ℕ)
    (extra : ℕ) (op : AndOrOp) (negated₀ negated₁ : Bool)
    (fixedOffset₁ : ℕ) (values : BinaryValues WorkCount) :
    (emitPolynomialRecentGate polynomial extra op negated₀ negated₁
        fixedOffset₁).requires values ↔
      values Work.temporary₃ = 0 ∧
        values Work.polynomialScratch = 0 ∧
        values Work.multiplyCounter = 0 ∧
        values Work.addCounter = 0 ∧
        values Work.copyCounter = 0 ∧
        values Work.loop₃ = 0 ∧
        polynomial.eval (values Work.horizon) + extra ≤
          values Work.available ∧
        fixedOffset₁ ≤ values Work.available ∧
        values Work.emitCounter = 0 :=
  emitPolynomialRecentGate_requires_internal polynomial extra op negated₀
    negated₁ fixedOffset₁ values

/-- Polynomial recent-gate emission advances `available` once and restores
its offset, controller, and reference scratch registers. -/
theorem emitPolynomialRecentGate_effect (polynomial : Polynomial ℕ)
    (extra : ℕ) (op : AndOrOp) (negated₀ negated₁ : Bool)
    (fixedOffset₁ : ℕ) (values : BinaryValues WorkCount)
    (hloop : values Work.loop₃ = 0) :
    (emitPolynomialRecentGate polynomial extra op negated₀ negated₁
        fixedOffset₁).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update values Work.loop₃ 0) Work.available
                (values Work.available + 1)) Work.reference₀ 0)
          Work.reference₁ 0) Work.temporary₃ 0 :=
  emitPolynomialRecentGate_effect_internal polynomial extra op negated₀
    negated₁ fixedOffset₁ values hloop

/-- Exact raw gate emitted from the polynomial and fixed recent-wire offsets. -/
theorem emitPolynomialRecentGate_emitted (polynomial : Polynomial ℕ)
    (extra : ℕ) (op : AndOrOp) (negated₀ negated₁ : Bool)
    (fixedOffset₁ : ℕ) (values : BinaryValues WorkCount)
    (hloop : values Work.loop₃ = 0) :
    (emitPolynomialRecentGate polynomial extra op negated₀ negated₁
        fixedOffset₁).emitted values =
      CircuitCode.RawGate.encode
        { op := op
          input₀ := values Work.available -
            (polynomial.eval (values Work.horizon) + extra)
          input₁ := values Work.available - fixedOffset₁
          negated₀ := negated₀
          negated₁ := negated₁ } :=
  emitPolynomialRecentGate_emitted_internal polynomial extra op negated₀
    negated₁ fixedOffset₁ values hloop

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
