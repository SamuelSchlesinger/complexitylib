/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Cobham
public import Complexitylib.Classes.P.Composition
public import Complexitylib.Classes.P.Cobham.Internal
public import Complexitylib.Classes.P.Cobham.Internal.StringOps

/-!
# Programming with polynomial-time string functions

⚠️ Unreviewed by Bolton

Cobham's theorem makes `FP` a *programming language*: a function is
polynomial-time exactly when it belongs to the algebra, so a construction can be
written as a composition of small pieces instead of assembled as a machine. This
file collects the glue that makes the two levels interoperate.

The algebra is stated at every arity, over vectors of arguments, while `FP` is
unary; the bridge is the pairing. `binFn_mem_FP` turns a two-argument member of
the algebra into an `FP` closure rule, and the rest of the file is that rule
applied to the toolkit of
`Complexitylib.Classes.P.Cobham.Internal.StringOps` and
`Complexitylib.Classes.P.Cobham.Internal.Algebra`.

## Main results

- `Cobham.fstBlockFn`, `Cobham.sndBlockFn` — the pair decoders, in the algebra
- `unFn_mem_FP`, `binFn_mem_FP` — algebra members become `FP` closure rules
- `dropLenFn_mem_FP`, `orBitFn_mem_FP`, `lenLeFlagFn_mem_FP`, `eqFlagFn_mem_FP` —
  the rules this gives
- `constFn_mem_FP` — every constant is polynomial-time
- `mem_FP_of_eq` — `FP` respects pointwise equality
-/

@[expose] public section

namespace Complexity

namespace Cobham

/-- The first pair decoder is in the algebra, being polynomial-time. -/
theorem fstBlockFn {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool => pairFst (g v) :=
  (Cobham.comp (FP_subset_CobhamFP fstBlock_mem_FP) fun _ : Fin 1 => hg).of_eq fun _ => rfl

/-- The second pair decoder is in the algebra. -/
theorem sndBlockFn {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool => pairSnd (g v) :=
  (Cobham.comp (FP_subset_CobhamFP sndBlock_mem_FP) fun _ : Fin 1 => hg).of_eq fun _ => rfl

end Cobham

/-- `FP` respects pointwise equality of functions — the counterpart of
`Cobham.of_eq`, needed because these closure rules produce syntactically
specific lambda terms. -/
theorem mem_FP_of_eq {f g : List Bool → List Bool} (hf : f ∈ FP) (h : ∀ z, f z = g z) :
    g ∈ FP := by
  have hfg : f = g := funext h
  rwa [hfg] at hf

/-! ## From the algebra to `FP` closure rules -/

/-- **A one-argument member of the algebra is an `FP` closure rule.** -/
theorem unFn_mem_FP {g : List Bool → List Bool}
    (hg : Cobham fun v : Fin 1 → List Bool => g (v 0))
    {a : List Bool → List Bool} (ha : a ∈ FP) : (fun z => g (a z)) ∈ FP := by
  have hg' : g ∈ FP := CobhamFP_subset_FP hg
  have h := mem_FP_comp ha hg'
  exact h

/-- **A two-argument member of the algebra is an `FP` closure rule.** The two
levels differ only in how arguments are presented: the algebra takes a vector,
`FP` takes the pairing of the two values. -/
theorem binFn_mem_FP {g : List Bool → List Bool → List Bool}
    (hg : Cobham fun v : Fin 2 → List Bool => g (v 0) (v 1))
    {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => g (a z) (b z)) ∈ FP := by
  have hpacked : Cobham fun v : Fin 1 → List Bool =>
      g (pairFst (v 0)) (pairSnd (v 0)) :=
    (Cobham.comp₂ hg (Cobham.fstBlockFn (Cobham.proj 0))
      (Cobham.sndBlockFn (Cobham.proj 0))).of_eq fun _ => rfl
  have hfp : (fun w => g (pairFst w) (pairSnd w)) ∈ FP :=
    CobhamFP_subset_FP hpacked
  have h := mem_FP_comp (Cobham.pairFn_mem_FP ha hb) hfp
  have heq : ((fun w => g (pairFst w) (pairSnd w)) ∘ fun z => pair (a z) (b z))
      = fun z => g (a z) (b z) := by
    funext z
    simp [Function.comp]
  rwa [heq] at h

/-! ## The rules -/

/-- Dropping a prefix at another value's width is polynomial-time. -/
theorem dropLenFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => (b z).drop (a z).length) ∈ FP :=
  binFn_mem_FP (g := fun p q => q.drop p.length)
    (Cobham.dropFn (Cobham.proj 0) (Cobham.proj 1)) ha hb

/-- Disjunction of flags is polynomial-time. -/
theorem orBitFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => orBit (a z) (b z)) ∈ FP :=
  binFn_mem_FP (g := orBit) (Cobham.orFn (Cobham.proj 0) (Cobham.proj 1)) ha hb

/-- Conjunction of flags is polynomial-time. -/
theorem andBitFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => andBit (a z) (b z)) ∈ FP :=
  binFn_mem_FP (g := andBit) (Cobham.andFn (Cobham.proj 0) (Cobham.proj 1)) ha hb

/-- Negation of a flag is polynomial-time. -/
theorem notBitFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => notBit (a z)) ∈ FP :=
  unFn_mem_FP (g := notBit) (Cobham.notFn (Cobham.proj 0)) ha

/-- The length comparison is polynomial-time. -/
theorem lenLeFlagFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => Cobham.lenLeFlag (a z) (b z)) ∈ FP :=
  binFn_mem_FP (g := Cobham.lenLeFlag)
    (Cobham.lenLeFlag_mem (Cobham.proj 0) (Cobham.proj 1)) ha hb

/-- The equality test is polynomial-time. -/
theorem eqFlagFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => Cobham.eqFlag (a z) (b z)) ∈ FP :=
  binFn_mem_FP (g := Cobham.eqFlag)
    (Cobham.eqFlag_mem (Cobham.proj 0) (Cobham.proj 1)) ha hb

/-- Reading a fixed field of a block-aligned string is polynomial-time. -/
theorem blockAtFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP)
    (i : ℕ) : (fun z => blockAt (a z) (b z) i) ∈ FP :=
  binFn_mem_FP (g := fun p q => blockAt p q i)
    (Cobham.blockFn (Cobham.proj 0) (Cobham.proj 1) i) ha hb

/-- Padding to a ruler's width is polynomial-time. -/
theorem padToFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => padTo (a z) (b z)) ∈ FP :=
  binFn_mem_FP (g := padTo) (Cobham.padFn (Cobham.proj 0) (Cobham.proj 1)) ha hb

end Complexity
