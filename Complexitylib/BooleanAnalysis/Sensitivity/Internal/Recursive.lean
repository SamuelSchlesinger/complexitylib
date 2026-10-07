/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.RecursiveBlocks
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.RecursiveOne
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.RecursiveZero
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.RecursiveJointZero

/-!
# Sensitivity separation: recursive

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity/Recursive.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.Sensitivity

/- Four sensitivity recurrences for a regular tournament and a good labeling. -/

noncomputable section
open scoped Classical

namespace Internal

theorem recursive_four_recurrences {M r h : ℕ} {I : Type} [Fintype I]
    (T : RegularTournament M) (A : GoodLabeling T.toTournament r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r) :
    let P := recursiveFamily T.toTournament A.label F
    (sideSensitivity P true ≤ M ^ 2 * sideSensitivity F false + r * sideSensitivity F true) ∧
    (jointSensitivity P true ≤ M ^ 2 * jointSensitivity F false + r * sideSensitivity F true) ∧
    (sideSensitivity P false ≤ 16 * sideSensitivity F false + sideSensitivity F true +
      3 * jointSensitivity F true) ∧
    (jointSensitivity P false ≤ 16 * sideSensitivity F false + 3 * jointSensitivity F true) := by
  exact ⟨recursive_side_one T.toTournament A.label F (M ^ 2) T.outdegree,
    recursive_joint_one T.toTournament A.label F hF (M ^ 2) T.outdegree,
    recursive_side_zero T.toTournament A F hF hr,
    recursive_joint_zero T.toTournament A F hF hr⟩

end Internal

end

end Complexity.BooleanAnalysis.Sensitivity
