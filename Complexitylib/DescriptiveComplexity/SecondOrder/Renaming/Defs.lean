/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.SecondOrder.Semantics

/-!
# Arity-preserving renaming of second-order relation variables

A relation renaming maps indices while preserving their arities. Lifting fixes
the newly bound relation and renames the older variables. Formula renaming thus
avoids capture under both sorts of second-order quantifier. Element variables
and vocabulary symbols are unchanged.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

/-- A map between relation contexts that preserves the arity of every variable. -/
structure RelRenaming (rctx sctx : List Nat) where
  /-- The target index of each source relation variable. -/
  index : Fin rctx.length → Fin sctx.length
  /-- Renaming preserves the relation's arity. -/
  arity : ∀ r, sctx.get (index r) = rctx.get r

namespace RelRenaming

/-- The identity renaming. -/
def id (rctx : List Nat) : RelRenaming rctx rctx := ⟨fun r => r, fun _ => rfl⟩

/-- Successive renamings compose in application order. -/
def comp {rctx sctx tctx : List Nat} (g : RelRenaming sctx tctx)
    (f : RelRenaming rctx sctx) : RelRenaming rctx tctx :=
  ⟨fun r => g.index (f.index r), fun r => (g.arity (f.index r)).trans (f.arity r)⟩

/-- Lift a renaming through a relation binder of arity `k`. -/
def lift {rctx sctx : List Nat} (f : RelRenaming rctx sctx) (k : Nat) :
    RelRenaming (k :: rctx) (k :: sctx) where
  index := Fin.cases 0 (fun r => (f.index r).succ)
  arity := Fin.cases rfl (fun r => f.arity r)

/-- Make room for a fresh relation variable at index zero. -/
def weaken (rctx : List Nat) (k : Nat) : RelRenaming rctx (k :: rctx) :=
  ⟨Fin.succ, fun _ => rfl⟩

/-- Read a target relation environment at the renamed source indices. -/
def pull {rctx sctx : List Nat} (f : RelRenaming rctx sctx) {card : Nat}
    (ρ : REnv card sctx) : REnv card rctx :=
  fun r args => ρ (f.index r) (fun i => args (Fin.cast (f.arity r) i))

end RelRenaming

/-- Rename the free relation variables, lifting the map beneath SO binders. -/
def SOFormula.renameRel {V : Vocabulary} : {rctx sctx : List Nat} → {n : Nat} →
    RelRenaming rctx sctx → SOFormula V rctx n → SOFormula V sctx n
  | _, _, _, _, .relApp i args => .relApp i args
  | _, _, _, f, .soRelApp r args =>
    .soRelApp (f.index r) (fun i => args (Fin.cast (f.arity r) i))
  | _, _, _, _, .eq a b => .eq a b
  | _, _, _, f, .neg φ => .neg (φ.renameRel f)
  | _, _, _, f, .conj φ ψ => .conj (φ.renameRel f) (ψ.renameRel f)
  | _, _, _, f, .disj φ ψ => .disj (φ.renameRel f) (ψ.renameRel f)
  | _, _, _, f, .exist φ => .exist (φ.renameRel f)
  | _, _, _, f, .all φ => .all (φ.renameRel f)
  | _, _, _, f, .soExist k φ => .soExist k (φ.renameRel (f.lift k))
  | _, _, _, f, .soAll k φ => .soAll k (φ.renameRel (f.lift k))

end Complexity.DescriptiveComplexity
