/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/
module
public import Complexitylib.Classes.P.DecisionFn
public import Complexitylib.Classes.Containments.Internal.PVerdict

/-!
# Languages in `P` are those with a polynomial-time verdict function

`mem_P_of_decisionFn_bool` puts a language in `P` given a one-bit verdict function in `FP`.
The converse, `exists_decisionFn_of_mem_P`, runs a polynomial-time decider inside Cobham's
algebra (`Complexitylib.Classes.Containments.Internal.PVerdict`). Together they characterize
`P`.

## Main results

- `mem_P_iff_exists_decisionFn` — `L ∈ P` iff a one-bit verdict function in `FP` decides `L`
-/

@[expose] public section

namespace Complexity

/-- **`P` is characterized by one-bit verdict functions.** A language is in `P` exactly when
some Boolean function `g`, with `x ↦ [g x]` computable in polynomial time, satisfies
`x ∈ L ↔ g x = true` for every `x`. The forward direction is `exists_decisionFn_of_mem_P`; the
reverse is `mem_P_of_decisionFn_bool`. -/
theorem mem_P_iff_exists_decisionFn {L : Language} :
    L ∈ P ↔ ∃ g : List Bool → Bool, (fun x => [g x]) ∈ FP ∧ ∀ x, x ∈ L ↔ g x = true :=
  ⟨exists_decisionFn_of_mem_P, fun ⟨_, hg, hL⟩ => mem_P_of_decisionFn_bool hg hL⟩

end Complexity
