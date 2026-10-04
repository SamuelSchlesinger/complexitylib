/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Uniform.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding

/-!
# Exact Boolean semantics and balancing of the uniform family

Both evaluators always return exactly one bit. The hard family at every
positive length is precisely the balanced padding of the preceding length
of the source-reduction family, including while the candidate cap is active.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem sourceReductionFamilyEval_length (source : List Bool) :
    (sourceReductionFamilyEval source).length = 1 := rfl

theorem sourceReductionFamilyEval_ofFn (n : Nat) (x : Fin n → Bool) :
    sourceReductionFamilyEval (List.ofFn x) = [sourceReductionFamily n x] := rfl

theorem sourceReductionHardEval_ofFn (n : Nat) (x : Fin n → Bool) :
    sourceReductionHardEval (List.ofFn x) = [sourceReductionHardFamily n x] := rfl

theorem mem_sourceReductionHardLanguage_ofFn (n : Nat) (x : Fin n → Bool) :
    List.ofFn x ∈ sourceReductionHardLanguage ↔ sourceReductionHardFamily n x = true := Iff.rfl

theorem sourceReductionHardFamily_succ (n : Nat) :
    sourceReductionHardFamily (n + 1) = balancePad (sourceReductionFamily n) := by
  funext x
  simp only [sourceReductionHardFamily, sourceReductionHardEval, balancePadEval,
    List.ofFn_succ, List.tail_cons, List.headD_cons, balancePad, sourceReductionFamily]
  rfl

theorem sourceReductionHardFamily_card_accepting (n : Nat) :
    (accepting (sourceReductionHardFamily (n + 1))).card = 2 ^ n := by
  rw [sourceReductionHardFamily_succ]
  exact card_accepting_balancePad _

end Algebraic.Cutwidth.Extractor.Internal
