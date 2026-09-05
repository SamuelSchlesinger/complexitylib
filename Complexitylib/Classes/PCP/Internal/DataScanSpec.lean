/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Encoding.DataEncode

/-!
# What the bracket scan computes

A model of the left-to-right pass over a serialized `Data` value: a bracket
depth, a count of the top-level children already passed, and the bits collected
while inside the child that was asked for. This file is about the model alone —
that it really does extract the requested child — and says nothing about
computability.

Two facts drive everything. The depth and the count evolve without looking at
the collected bits, and the collected bits only ever grow at the end
(`runSpec_append_acc`); and a serialized value read at any depth returns to that
depth, having contributed exactly its own serialization when it was the child
being sought (`runSpec_toBits`).

## Main definitions

- `Complexity.DataScan.runSpec` — the model of the pass

## Main results

- `Complexity.DataScan.runSpec_toBits` — reading one serialized value
- `Complexity.DataScan.runSpec_flatten` — reading a whole run of children
- `Complexity.DataScan.runSpec_inner` — the pass over a serialized list returns
  the requested child
-/

@[expose] public section

namespace Complexity

namespace DataScan

/-- One step of the pass: `false` opens a bracket, `true` closes one, and the
bit joins the output exactly when the count matches the child sought. -/
def stepSpec (i : ℕ) (st : ℕ × ℕ × List Bool) (b : Bool) : ℕ × ℕ × List Bool :=
  let acc' := if st.2.1 = i then st.2.2 ++ [b] else st.2.2
  if b then (st.1 - 1, if st.1 - 1 = 0 then st.2.1 + 1 else st.2.1, acc')
  else (st.1 + 1, st.2.1, acc')

/-- The pass over a whole string. -/
def runSpec (i : ℕ) (st : ℕ × ℕ × List Bool) (s : List Bool) : ℕ × ℕ × List Bool :=
  s.foldl (stepSpec i) st

@[simp] theorem runSpec_nil (i : ℕ) (st : ℕ × ℕ × List Bool) : runSpec i st [] = st := rfl

theorem runSpec_append (i : ℕ) (st : ℕ × ℕ × List Bool) (s t : List Bool) :
    runSpec i st (s ++ t) = runSpec i (runSpec i st s) t := by
  rw [runSpec, runSpec, runSpec, List.foldl_append]

theorem runSpec_cons (i : ℕ) (st : ℕ × ℕ × List Bool) (b : Bool) (s : List Bool) :
    runSpec i st (b :: s) = runSpec i (stepSpec i st b) s := rfl

/-- **The collected bits only grow at the end.** A prefix already present in the
output is carried through untouched, and the depth and count do not see it. -/
theorem runSpec_append_acc (i : ℕ) (s : List Bool) :
    ∀ (d c : ℕ) (pre acc : List Bool),
      runSpec i (d, c, pre ++ acc) s
        = ((runSpec i (d, c, acc) s).1, (runSpec i (d, c, acc) s).2.1,
            pre ++ (runSpec i (d, c, acc) s).2.2) := by
  induction s with
  | nil => intro d c pre acc; rfl
  | cons b s ih =>
      intro d c pre acc
      rw [runSpec_cons, runSpec_cons]
      have hstep : stepSpec i (d, c, pre ++ acc) b
          = ((stepSpec i (d, c, acc) b).1, (stepSpec i (d, c, acc) b).2.1,
              pre ++ (stepSpec i (d, c, acc) b).2.2) := by
        by_cases hb : b <;> by_cases hc : c = i <;>
          simp [stepSpec, hb, hc, List.append_assoc]
      rw [hstep]
      exact ih _ _ _ _

/-- **Reading one serialized value.** Starting at depth `d` with `c` children
already passed, the pass over `y.toBits` returns to depth `d`; it counts one
more child exactly when it was at the top level, and it contributes `y.toBits`
to the output exactly when `y` is the child sought. -/
theorem runSpec_toBits (i : ℕ) (y : Data) :
    ∀ (d c : ℕ) (acc : List Bool),
      runSpec i (d, c, acc) y.toBits
        = (d, (if d = 0 then c + 1 else c), if c = i then acc ++ y.toBits else acc) := by
  induction y using Data.inductionL with
  | nil =>
      intro d c acc
      have hnil : (Data.l ([] : List Data)).toBits = [false, true] := by
        rw [Data.toBits_l]; simp
      rw [hnil]
      by_cases hc : c = i <;>
        simp [runSpec_cons, stepSpec, hc]
  | cons x xs ihx ihxs =>
      intro d c acc
      have hsplit : (Data.l (x :: xs)).toBits
          = false :: (x.toBits ++ ((xs.map Data.toBits).flatten ++ [true])) := by
        rw [Data.toBits_l]
        simp
      have htail : (Data.l xs).toBits = false :: ((xs.map Data.toBits).flatten ++ [true]) := by
        rw [Data.toBits_l]
      set F := (xs.map Data.toBits).flatten ++ [true] with hF
      set acc₁ := if c = i then acc ++ [false] else acc with hacc₁
      -- The behaviour of `F` from depth `d + 1`, read off from the tail's statement.
      have hxs := ihxs d c acc
      rw [htail, runSpec_cons] at hxs
      have hstep0 : stepSpec i (d, c, acc) false = (d + 1, c, acc₁) := by
        by_cases hc : c = i <;> simp [stepSpec, hc, hacc₁]
      rw [hstep0] at hxs
      -- Uniformity: read `F` from the empty output instead.
      have huni : ∀ a : List Bool, runSpec i (d + 1, c, a) F
          = ((runSpec i (d + 1, c, []) F).1, (runSpec i (d + 1, c, []) F).2.1,
              a ++ (runSpec i (d + 1, c, []) F).2.2) := by
        intro a
        have := runSpec_append_acc i F (d + 1) c a []
        simpa using this
      have hR := huni acc₁
      rw [hxs] at hR
      set R := (runSpec i (d + 1, c, []) F).2.2 with hRdef
      have hD : (runSpec i (d + 1, c, []) F).1 = d := by
        have := congrArg Prod.fst hR
        simpa using this.symm
      have hC : (runSpec i (d + 1, c, []) F).2.1 = (if d = 0 then c + 1 else c) := by
        have := congrArg (fun p => p.2.1) hR
        simpa using this.symm
      have hacc : (if c = i then acc ++ (false :: F) else acc) = acc₁ ++ R := by
        have := congrArg (fun p => p.2.2) hR
        simpa using this
      -- Now the value at hand.
      rw [hsplit, runSpec_cons, hstep0, runSpec_append, ihx (d + 1) c acc₁,
        ite_eq_right (Nat.succ_ne_zero d)]
      set acc₂ := if c = i then acc₁ ++ x.toBits else acc₁ with hacc₂
      rw [huni acc₂, hD, hC]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      by_cases hc : c = i
      · have hR' : R = F := by
          simp only [hc, hacc₁] at hacc
          simpa using hacc.symm
        rw [hacc₂, hacc₁, ite_eq_left hc, ite_eq_left hc, ite_eq_left hc, hR']
        simp
      · have hR' : R = [] := by
          simp only [ite_eq_right hc, hacc₁] at hacc
          simpa using hacc.symm
        rw [hacc₂, hacc₁, ite_eq_right hc, ite_eq_right hc, ite_eq_right hc, hR']
        simp

/-! ### A run of children -/

/-- The child a pass looking for index `i` picks out of `xs`, having already
passed `c` children. -/
def selFrom (xs : List Data) (i c : ℕ) : List Bool :=
  if c ≤ i then ((xs[i - c]?).map Data.toBits).getD [] else []

@[simp] theorem selFrom_nil (i c : ℕ) : selFrom [] i c = [] := by
  rw [selFrom]
  split <;> simp

/-- **Reading a run of children.** At the top level the pass counts every child
and contributes exactly the one it was asked for. -/
theorem runSpec_flatten (i : ℕ) :
    ∀ (xs : List Data) (c : ℕ) (acc : List Bool),
      runSpec i (0, c, acc) ((xs.map Data.toBits).flatten)
        = (0, c + xs.length, acc ++ selFrom xs i c) := by
  intro xs
  induction xs with
  | nil => intro c acc; simp
  | cons x xs ih =>
      intro c acc
      rw [List.map_cons, List.flatten_cons, runSpec_append, runSpec_toBits, ite_eq_left rfl, ih]
      refine Prod.ext rfl (Prod.ext (by simp [List.length_cons]; omega) ?_)
      simp only
      by_cases hlt : c < i
      · have h : c < i := hlt
        have h1 : selFrom (x :: xs) i c = selFrom xs i (c + 1) := by
          rw [selFrom, selFrom, ite_eq_left (by omega : c ≤ i), ite_eq_left (by omega)]
          have : i - c = (i - (c + 1)) + 1 := by omega
          rw [this]
          simp
        rw [ite_eq_right (by omega), h1]
      by_cases heq : c = i
      · subst heq
        have h1 : selFrom (x :: xs) c c = x.toBits := by
          rw [selFrom, ite_eq_left (by omega : c ≤ c)]
          simp
        have h2 : selFrom xs c (c + 1) = [] := by
          rw [selFrom, ite_eq_right (by omega)]
        rw [ite_eq_left rfl, h1, h2, List.append_assoc, List.append_nil]
      · have h : i < c := by omega
        have h1 : selFrom (x :: xs) i c = [] := by rw [selFrom, ite_eq_right (by omega)]
        have h2 : selFrom xs i (c + 1) = [] := by rw [selFrom, ite_eq_right (by omega)]
        rw [ite_eq_right (by omega), h1, h2]

/-- **The pass over a serialized list.** Reading the bits strictly between the
outer brackets returns the requested child's own serialization. -/
theorem runSpec_inner (i : ℕ) (xs : List Data) :
    runSpec i (0, 0, []) ((xs.map Data.toBits).flatten)
      = (0, xs.length, ((xs[i]?).map Data.toBits).getD []) := by
  rw [runSpec_flatten, selFrom, ite_eq_left (Nat.zero_le i)]
  simp

end DataScan

end Complexity
