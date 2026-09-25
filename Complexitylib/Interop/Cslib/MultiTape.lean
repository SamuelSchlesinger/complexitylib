/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Cslib.MultiTape.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.DTISP
public import Complexitylib.Asymptotics
import Complexitylib.Interop.Cslib.MultiTape.Internal
import Complexitylib.Interop.Cslib.MultiTape.Space
import Complexitylib.Interop.Cslib.MultiTape.Fun
import all Complexitylib.Classes.DTISP

/-!
# Complexitylib time classes on CSLib multi-tape machines

CSLib measures the complexity of a language through its multi-tape machines
(`Turing.MultiTapeTM`): `MultiTapeTM.DecidableInTimeAndSpace L enc t s` says
that some machine over the binary alphabet with finitely many states decides
`L` within time `t x` and space `s x` on every input `x`, emitting the single
bit `true` on inputs in `L` and `false` otherwise. Space counts the work cells
its heads visit. Our languages are sets of binary strings, so they are passed
to CSLib with the identity encoding.

This file shows that our deterministic time classes run on those machines
with a constant-factor overhead. The simulator `TM.toMultiTape`
(`Complexitylib.Interop.Cslib.MultiTape.Defs`) executes a machine
`tm : TM n` step for step on `2n + 3` CSLib work tapes and then reads off the
verdict.

## Main results

- `Complexity.TM.DecidesInTime.decidableInTimeAndSpace` — a decider within
  time `f` yields a CSLib decider within time and space `(2n + 3) (2 f + 5)`
- `Complexity.decidableInTimeAndSpace_of_mem_DTIME` — `DTIME(T)` languages are
  CSLib-decidable within time and space `O(T)`
- `Complexity.decidableInTimeAndSpace_of_mem_P` — `P` languages are
  CSLib-decidable within polynomial time and space
- `Complexity.TM.DecidesInTimeSpace.decidableInTimeAndSpace` — a decider
  within time `T` and space `S` yields a CSLib decider within time `2 T + 4`
  and space `(2n + 3) (S + 2)`
- `Complexity.decidableInTimeAndSpace_of_mem_DTISP` — `DTISP(T, S)` languages
  are CSLib-decidable within time `O(T)` and space `O(S + 1)`
- `Complexity.TM.ComputesInTime.computableInTimeAndSpace` — a machine computing
  `f` within time `T` yields a CSLib machine computing `f` within time
  `3 T + 4` and space `(2n + 3) (3 T + 5)`
- `Complexity.computableInTimeAndSpace_of_mem_FP` — `FP` functions are
  CSLib-computable within polynomial time and space

The converse is `Complexitylib.Interop.Cslib.FromMultiTape`, and together the
two directions give `mem_P_iff_decidableInTimeAndSpace`.
-/


public section

namespace Complexity

open Turing

/-- **A Complexitylib decider runs on CSLib.** If `tm` decides `L` within time
`f`, a CSLib multi-tape machine decides `L` within time and space
`(2n + 3) (2 f + 5)`. -/
theorem TM.DecidesInTime.decidableInTimeAndSpace {n : ℕ} {tm : TM n} {L : Language}
    {f : ℕ → ℕ} (h : tm.DecidesInTime L f) :
    MultiTapeTM.DecidableInTimeAndSpace L (Function.Embedding.refl _)
      (fun x => (2 * n + 3) * (2 * f x.length + 5))
      (fun x => (2 * n + 3) * (2 * f x.length + 5)) :=
  ⟨TM.simTapes n, TM.MultiTapeState tm.Q, inferInstance, tm.toMultiTape,
    (tm.toMultiTape_computesFun h).mono (fun x => by nlinarith)
      (fun x => Nat.le_of_eq (by simp only [TM.simTapes]; ring))⟩

/-- **`DTIME` transfers to CSLib.** Every language in `DTIME(T)` is decided by a
CSLib multi-tape machine within time and space `O(T)` in the input length. -/
theorem decidableInTimeAndSpace_of_mem_DTIME {L : Language} {T : ℕ → ℕ}
    (hL : L ∈ DTIME T) :
    ∃ t : ℕ → ℕ, t =O T ∧ MultiTapeTM.DecidableInTimeAndSpace L (Function.Embedding.refl _)
      (fun x => t x.length) (fun x => t x.length) := by
  obtain ⟨n, tm, f, hdec, hf⟩ := hL
  refine ⟨fun m => (2 * n + 3) * (2 * f m + 5),
    BigO.trans (BigO.of_le fun m => ?_) (BigO.const_mul_left (7 * (2 * n + 3)) hf),
    hdec.decidableInTimeAndSpace⟩
  have := hdec.one_le m
  calc (2 * n + 3) * (2 * f m + 5) ≤ (2 * n + 3) * (7 * f m) :=
        Nat.mul_le_mul_left _ (by omega)
    _ = 7 * (2 * n + 3) * f m := by ring

/-- **`P` transfers to CSLib.** Every language in `P` is decided by a CSLib
multi-tape machine within polynomial time and space in the input length. -/
theorem decidableInTimeAndSpace_of_mem_P {L : Language} (hL : L ∈ P) :
    ∃ p : Polynomial ℕ, MultiTapeTM.DecidableInTimeAndSpace L (Function.Embedding.refl _)
      (fun x => p.eval x.length) (fun x => p.eval x.length) := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hL
  obtain ⟨t, ht, hdec⟩ := decidableInTimeAndSpace_of_mem_DTIME hk
  obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound ht
  exact ⟨p, MultiTapeTM.ComputableInTimeAndSpace.mono hdec (fun x => hp _) (fun x => hp _)⟩

/-- **A space-bounded Complexitylib decider runs on CSLib in the same space.**
If `tm` decides `L` within time `T` and space `S` (`TM.DecidesInTimeSpace`), a
CSLib multi-tape machine decides `L` within time `2 T + 4` and space
`(2n + 3) (S + 2)`. -/
theorem TM.DecidesInTimeSpace.decidableInTimeAndSpace {n : ℕ} {tm : TM n} {L : Language}
    {T S : ℕ → ℕ} (h : tm.DecidesInTimeSpace L T S) :
    MultiTapeTM.DecidableInTimeAndSpace L (Function.Embedding.refl _)
      (fun x => 2 * T x.length + 4) (fun x => (2 * n + 3) * (S x.length + 2)) :=
  ⟨TM.simTapes n, TM.MultiTapeState tm.Q, inferInstance, tm.toMultiTape,
    (tm.toMultiTape_computesFun_space h).mono (fun _ => le_rfl)
      (fun x => Nat.le_of_eq (by simp only [TM.simTapes]; ring))⟩

/-- **`DTISP` transfers to CSLib.** Every language in `DTISP(T, S)` is decided
by a CSLib multi-tape machine within time `O(T)` and space `O(S + 1)` in the
input length. -/
theorem decidableInTimeAndSpace_of_mem_DTISP {L : Language} {T S : ℕ → ℕ}
    (hL : L ∈ DTISP T S) :
    ∃ t s : ℕ → ℕ, t =O T ∧ s =O (fun m => S m + 1) ∧
      MultiTapeTM.DecidableInTimeAndSpace L (Function.Embedding.refl _)
        (fun x => t x.length) (fun x => s x.length) := by
  obtain ⟨n, tm, f, g, hdec, hf, hg⟩ := hL
  refine ⟨fun m => 2 * f m + 4, fun m => (2 * n + 3) * (g m + 2),
    BigO.trans (BigO.of_le fun m => ?_) (BigO.const_mul_left 6 hf), ?_,
    hdec.decidableInTimeAndSpace⟩
  · have := TM.DecidesInTime.one_le (tm := tm) hdec.2 m
    omega
  · have hg1 : (fun m => g m + 1) =O (fun m => S m + 1) :=
      BigO.add (BigO.trans hg (BigO.of_le fun m => Nat.le_succ (S m)))
        (BigO.of_le fun m => Nat.le_add_left 1 (S m))
    refine BigO.trans (BigO.of_le fun m => ?_) (BigO.const_mul_left (2 * (2 * n + 3)) hg1)
    calc (2 * n + 3) * (g m + 2) ≤ (2 * n + 3) * (2 * (g m + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (2 * n + 3) * (g m + 1) := by ring

/-- **A Complexitylib function computation runs on CSLib.** If `tm` computes
`f` within time `T`, a CSLib multi-tape machine computes `f` (with identity
encodings) within time `3 T + 4` and space `(2n + 3) (3 T + 5)`. -/
theorem TM.ComputesInTime.computableInTimeAndSpace {n : ℕ} {tm : TM n}
    {f : List Bool → List Bool} {T : ℕ → ℕ} (h : tm.ComputesInTime f T) :
    MultiTapeTM.ComputableInTimeAndSpace f (Function.Embedding.refl _)
      (Function.Embedding.refl _) (fun x => 3 * T x.length + 4)
      (fun x => (2 * n + 3) * (3 * T x.length + 5)) :=
  ⟨TM.simTapes n, TM.MultiTapeState tm.Q, inferInstance, tm.toMultiTapeFun,
    (tm.toMultiTapeFun_computesFun h).mono (fun _ => le_rfl)
      (fun x => Nat.le_of_eq (by simp only [TM.simTapes]; ring))⟩

/-- **`FP` transfers to CSLib.** Every function in `FP` is computed by a CSLib
multi-tape machine within polynomial time and space in the input length. -/
theorem computableInTimeAndSpace_of_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) :
    ∃ p : Polynomial ℕ, MultiTapeTM.ComputableInTimeAndSpace f (Function.Embedding.refl _)
      (Function.Embedding.refl _) (fun x => p.eval x.length) (fun x => p.eval x.length) := by
  obtain ⟨d, k, tm, T, hT, hTd⟩ := hf
  have hb : (fun m => (2 * k + 3) * (3 * T m + 5)) =O (· ^ d) :=
    BigO.trans (BigO.of_le fun m => le_of_eq (show (2 * k + 3) * (3 * T m + 5) =
        (2 * k + 3) * 3 * T m + (2 * k + 3) * 5 by ring))
      (BigO.add (BigO.const_mul_left _ hTd) (BigO.const_le_pow _ d))
  obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound hb
  exact ⟨p, MultiTapeTM.ComputableInTimeAndSpace.mono hT.computableInTimeAndSpace
    (fun x => le_trans (by nlinarith) (hp x.length)) (fun x => hp x.length)⟩

end Complexity
