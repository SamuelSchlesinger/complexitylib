/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.Tseitin.Internal.Streaming

/-!
# Register bounds for the streaming Tseitin transformation

This proof-only module bounds every natural number retained by the streaming
transducer. A successful token step raises the largest retained value by at
most one, so a run is bounded by its initial state plus the number of tokens
consumed. The concrete reduction machine uses this invariant to select one
uniform register-operation budget for its entire input scan.
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Streaming

/-- Largest variable index retained by a pending-clause window. -/
def Pending.maxValue : Pending → ℕ
  | .zero => 0
  | .one a => a.var
  | .two a b => max a.var b.var
  | .three a b c => max a.var (max b.var c.var)

/-- Variable counter retained by the raw-literal scanner. -/
def Scan.maxValue : Scan → ℕ
  | .boundary => 0
  | .literal _ var => var

/-- Largest natural number retained anywhere in a streaming state. -/
def State.maxValue (st : State) : ℕ :=
  max st.next (max st.pending.maxValue st.scan.maxValue)

/-- One successful token step raises the largest retained value by at most
one. Output growth is deliberately absent: emitted bits are not work-register
contents. -/
theorem maxValue_step_le_internal {st st' : State} {tok : EncToken}
    (hstep : step st tok = some st') :
    st'.maxValue ≤ st.maxValue + 1 := by
  rcases st with ⟨next, pending, scan, emitted⟩
  cases pending <;> cases scan <;> cases tok
  all_goals simp only [step] at hstep
  all_goals try split at hstep
  all_goals
    simp [pushLiteral, closeClause, Pending.toClause,
      Clause.tseitinFreshCount] at hstep
  all_goals cases hstep
  all_goals
    simp [State.maxValue, Pending.maxValue, Scan.maxValue, Lit.negVar] <;> omega

/-- A successful run raises the largest retained value by at most the number
of tokens consumed. -/
theorem maxValue_run_le_internal {st st' : State} {toks : List EncToken}
    (hrun : run st toks = some st') :
    st'.maxValue ≤ st.maxValue + toks.length := by
  induction toks generalizing st with
  | nil =>
      simp only [run, Option.some.injEq] at hrun
      subst st'
      omega
  | cons tok toks ih =>
      simp only [run] at hrun
      cases htok : step st tok with
      | none => simp [htok] at hrun
      | some mid =>
          simp only [htok] at hrun
          have hfirst := maxValue_step_le_internal htok
          have hrest := ih hrun
          simp only [List.length_cons]
          omega

end Streaming

end ThreeSAT

end SAT

end Complexity
