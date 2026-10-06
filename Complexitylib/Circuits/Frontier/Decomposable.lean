/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Rectangle
public import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Threshold counting for decomposable representations

A smooth decomposable DAG has unions on a common scope and binary products on disjoint
scopes. Leaves have at most one assignment. Its denotations satisfy the usual local
semantics; a decreasing rank rules out cycles. Unions need not be disjoint, and different
branches may use different partitions.

An occurrence in an accepting certificate supplies an outside context. Substituting any
assignment accepted by that node preserves acceptance at the root. Thus a node and all its
contexts form a rectangle. Descending a certificate to the cardinality threshold charges
at most `(K - 1)^2` inputs to a union edge and `(K - 1)^3` to a product node.

The certificate-context rectangle construction is standard in the DNNF literature; see
Bova, Capelli, Mengel and Slivovsky, IJCAI 2016. The threshold estimate here does not require
deterministic unions or a single tree of coordinate partitions.
-/

@[expose] public section

namespace Complexity.Frontier

open Set

/-- The three node types of a smooth decomposable representation. -/
inductive DecomposableGate (N : Type*)
  | leaf
  | union (children : Finset N)
  | product (left right : N)

/-- A finite acyclic union/product representation, with its local denotational semantics.
Literal leaves and constants satisfy `leaf_small`; arbitrary predicates are not free leaves.
Finiteness of the node type is needed only for the size bound. -/
structure Decomposable (ι U N : Type*) where
  /-- The coordinates each node is about. -/
  scope : N → Set ι
  /-- The root node, whose scope is everything. -/
  root : N
  scope_root : scope root = univ
  /-- The gate at each node: a leaf, a union of children, or a product of two. -/
  gate : N → DecomposableGate N
  /-- A rank that decreases from each node to its children. -/
  rank : N → ℕ
  /-- The partial inputs each node accepts, on its scope. -/
  values : (v : N) → Set (scope v → U)
  leaf_small : ∀ v, gate v = .leaf → (values v).ncard ≤ 1
  union_scope : ∀ v c, gate v = .union c → ∀ u ∈ c, scope u = scope v
  union_rank : ∀ v c, gate v = .union c → ∀ u ∈ c, rank u < rank v
  union_values : ∀ v c, gate v = .union c → ∀ x : ι → U,
    (scope v).domRestrict x ∈ values v ↔
      ∃ u ∈ c, (scope u).domRestrict x ∈ values u
  product_scope : ∀ v l r, gate v = .product l r → scope v = scope l ∪ scope r
  product_disjoint : ∀ v l r, gate v = .product l r → Disjoint (scope l) (scope r)
  product_rank : ∀ v l r, gate v = .product l r → rank l < rank v ∧ rank r < rank v
  product_values : ∀ v l r, gate v = .product l r → ∀ x : ι → U,
    (scope v).domRestrict x ∈ values v ↔
      (scope l).domRestrict x ∈ values l ∧ (scope r).domRestrict x ∈ values r

namespace Decomposable

variable {ι U N : Type*} (P : Decomposable ι U N)

/-- Acceptance by a node, viewed on full inputs. -/
def accepts (v : N) : Set (ι → U) := {x | (P.scope v).domRestrict x ∈ P.values v}

/-- The set represented by the root. -/
def accepted : Set (ι → U) := P.accepts P.root

theorem accepts_congr {v : N} {x y : ι → U} (h : EqOn x y (P.scope v)) :
    x ∈ P.accepts v ↔ y ∈ P.accepts v := by
  change _ ∈ P.values v ↔ _ ∈ P.values v
  rw [domRestrict_eq_domRestrict_iff.mpr h]

/-- A node occurs on an accepting certificate for `x`. At a union, any accepting child
can be selected. At a product, both children occur. -/
inductive Occurs (x : ι → U) : N → Prop
  | root : x ∈ P.accepted → Occurs x P.root
  | union {v u : N} {c : Finset N} : Occurs x v → P.gate v = .union c →
      u ∈ c → x ∈ P.accepts u → Occurs x u
  | left {v l r : N} : Occurs x v → P.gate v = .product l r → Occurs x l
  | right {v l r : N} : Occurs x v → P.gate v = .product l r → Occurs x r

theorem Occurs.accepts {x : ι → U} {v : N} (h : P.Occurs x v) : x ∈ P.accepts v := by
  induction h with
  | root h => exact h
  | union _ _ _ h _ => exact h
  | left _ hg ih => exact ((P.product_values _ _ _ hg x).mp ih).1
  | right _ hg ih => exact ((P.product_values _ _ _ hg x).mp ih).2

/-- The substitution property follows from the syntax and decomposability. -/
theorem Occurs.substitute {x : ι → U} {v : N} (h : P.Occurs x v)
    {y : ι → U} (hy : y ∈ P.accepts v) (hout : EqOn y x (P.scope v)ᶜ) :
    y ∈ P.accepted := by
  induction h with
  | root _ => exact hy
  | @union v u c hv hg hu _ ih =>
    apply ih ((P.union_values v c hg y).mpr ⟨u, hu, hy⟩)
    simpa only [P.union_scope v c hg u hu] using hout
  | @left v l r hv hg ih =>
    have hs := P.product_scope v l r hg
    have hr : y ∈ P.accepts r :=
      (P.accepts_congr (fun i hi =>
        hout ((P.product_disjoint v l r hg).symm.notMem_of_mem_left hi))).mpr
        ((P.product_values v l r hg x).mp hv.accepts).2
    apply ih ((P.product_values v l r hg y).mpr ⟨hy, hr⟩)
    exact fun i hi => hout (fun hil => hi (hs ▸ Or.inl hil))
  | @right v l r hv hg ih =>
    have hs := P.product_scope v l r hg
    have hl : y ∈ P.accepts l :=
      (P.accepts_congr (fun i hi => hout ((P.product_disjoint v l r hg).notMem_of_mem_left hi))).mpr
        ((P.product_values v l r hg x).mp hv.accepts).1
    apply ih ((P.product_values v l r hg y).mpr ⟨hl, hy⟩)
    exact fun i hi => hout (fun hir => hi (hs ▸ Or.inr hir))

/-- Outside assignments supplied by accepting certificates through a node. -/
def contexts (v : N) : Set (↥(P.scope v)ᶜ → U) :=
  (P.scope v)ᶜ.domRestrict '' {x | P.Occurs x v}

theorem rectangle_subset (v : N) :
    rectangle (P.scope v) (P.values v) (P.contexts v) ⊆ P.accepted := by
  rintro y ⟨hy, x, hx, hxy⟩
  exact Occurs.substitute P hx hy (domRestrict_eq_domRestrict_iff.mp hxy).symm

section Finite

variable [Finite ι] [Finite U] {K : ℕ}

omit [Finite ι] [Finite U] in
theorem contexts_small (hS : RectangleFree P.accepted K) {v : N}
    (hv : K ≤ (P.values v).ncard) : (P.contexts v).ncard ≤ K - 1 := by
  rcases hS _ _ _ (P.rectangle_subset v) with h | h <;> lia

/-- Inputs for which threshold descent can stop at this node. -/
def stops (K : ℕ) (v : N) : Set (ι → U) := {x | P.Occurs x v ∧ K ≤ (P.values v).ncard ∧
  match P.gate v with
  | .leaf => False
  | .union c => ∃ u ∈ c, x ∈ P.accepts u ∧ (P.values u).ncard < K
  | .product l r => (P.values l).ncard < K ∧ (P.values r).ncard < K}

/-- Every accepted input has a stopping node. Rank makes the descent finite even with sharing. -/
theorem exists_stop (hK : 1 < K) (hS : K ≤ P.accepted.ncard)
    {x : ι → U} (hx : x ∈ P.accepted) : ∃ v, x ∈ P.stops K v := by
  classical
  have hroot : K ≤ (P.values P.root).ncard := hS.trans
    (ncard_le_ncard_of_injOn (P.scope P.root).domRestrict (fun _ hy => hy)
      (fun _ _ _ _ h => funext fun i =>
        domRestrict_eq_domRestrict_iff.mp h (P.scope_root ▸ mem_univ i)))
  have hex : ∃ k, ∃ v, P.rank v = k ∧ P.Occurs x v ∧ K ≤ (P.values v).ncard :=
    ⟨_, P.root, rfl, .root hx, hroot⟩
  obtain ⟨v, hv, hxv, hlarge⟩ := Nat.find_spec hex
  have hsmall {u : N} (hu : P.rank u < P.rank v) (hxu : P.Occurs x u) :
      (P.values u).ncard < K := by
    by_contra! h
    exact Nat.find_min hex (hv ▸ hu) ⟨u, rfl, hxu, h⟩
  refine ⟨v, hxv, hlarge, ?_⟩
  cases hg : P.gate v with
  | leaf => have := P.leaf_small v hg; lia
  | union c =>
    obtain ⟨u, hu, hxu⟩ := (P.union_values v c hg x).mp hxv.accepts
    exact ⟨u, hu, hxu, hsmall (P.union_rank v c hg u hu) (.union hxv hg hu hxu)⟩
  | product l r => exact
    ⟨hsmall (P.product_rank v l r hg).1 (.left hxv hg),
      hsmall (P.product_rank v l r hg).2 (.right hxv hg)⟩

/-- The local threshold budget of a node. -/
def budget (K : ℕ) (v : N) : ℕ := match P.gate v with
  | .leaf => 0
  | .union c => (K - 1) ^ 2 * c.card
  | .product _ _ => (K - 1) ^ 3

theorem ncard_stops_le (hS : RectangleFree P.accepted K) (v : N) :
    (P.stops K v).ncard ≤ P.budget K v := by
  classical
  by_cases hlarge : K ≤ (P.values v).ncard
  · have hout := P.contexts_small hS hlarge
    cases hg : P.gate v with
    | leaf => simp [stops, budget, hg]
    | union c =>
      let T (u : N) := {x | P.Occurs x v ∧ x ∈ P.accepts u ∧ (P.values u).ncard < K}
      have hcover : P.stops K v ⊆ ⋃ u ∈ c, T u := by
        rintro x ⟨hx, _, hs⟩
        simp only [hg] at hs
        obtain ⟨u, hu, hxu, hsmall⟩ := hs
        exact mem_iUnion₂.mpr ⟨u, hu, hx, hxu, hsmall⟩
      calc (P.stops K v).ncard
          ≤ (⋃ u ∈ c, T u).ncard := ncard_le_ncard hcover
        _ ≤ ∑ u ∈ c, (T u).ncard := Finset.set_ncard_biUnion_le _ _
        _ ≤ ∑ _u ∈ c, (K - 1) ^ 2 := by
          refine Finset.sum_le_sum fun u hu => ?_
          by_cases hsmall : (P.values u).ncard < K
          · calc (T u).ncard
                ≤ (P.values u ×ˢ P.contexts v).ncard := by
                  refine ncard_le_ncard_of_injOn
                    (fun x => ((P.scope u).domRestrict x, (P.scope v)ᶜ.domRestrict x)) ?_ ?_
                  · rintro x ⟨hx, hxu, _⟩; exact ⟨hxu, x, hx, rfl⟩
                  · intro x _ y _ h
                    have hparts := Prod.mk.inj h
                    rw [P.union_scope v c hg u hu] at hparts
                    exact eq_of_domRestrict_eq hparts.1 hparts.2
              _ ≤ (K - 1) ^ 2 := by
                rw [ncard_prod, sq]
                exact Nat.mul_le_mul (by lia) hout
          · have : T u = ∅ := by ext x; simp [T, hsmall]
            simp [this]
        _ = P.budget K v := by simp [budget, hg, Nat.mul_comm]
    | product l r =>
      by_cases hsmall : (P.values l).ncard < K ∧ (P.values r).ncard < K
      · calc (P.stops K v).ncard
            ≤ (P.values l ×ˢ P.values r ×ˢ P.contexts v).ncard := by
              refine ncard_le_ncard_of_injOn
                (fun x => ((P.scope l).domRestrict x, (P.scope r).domRestrict x,
                  (P.scope v)ᶜ.domRestrict x)) ?_ ?_
              · rintro x ⟨hx, _, _⟩
                have h := (P.product_values v l r hg x).mp hx.accepts
                exact ⟨h.1, h.2, x, hx, rfl⟩
              · intro x _ y _ h
                simp only [Prod.mk.injEq, domRestrict_eq_domRestrict_iff] at h
                apply eq_of_domRestrict_eq (X := P.scope v)
                · apply domRestrict_eq_domRestrict_iff.mpr
                  intro i hi
                  rw [P.product_scope v l r hg] at hi
                  exact hi.elim (fun hil => h.1 hil) (fun hir => h.2.1 hir)
                · exact domRestrict_eq_domRestrict_iff.mpr h.2.2
          _ ≤ (K - 1) ^ 3 := by
            rw [ncard_prod, ncard_prod, show (K - 1) ^ 3 = (K - 1) * ((K - 1) * (K - 1)) by ring]
            exact Nat.mul_le_mul (by lia) (Nat.mul_le_mul (by lia) hout)
          _ = P.budget K v := by simp [budget, hg]
      · have : P.stops K v = ∅ := by ext x; simp [stops, hg, hsmall]
        simp [this]
  · have : P.stops K v = ∅ := by ext x; simp [stops, hlarge]
    simp [this]

variable [Fintype N]

/-- Count outgoing union edges, including shared children once for each parent. -/
def unionEdges : ℕ := ∑ v, match P.gate v with | .union c => c.card | _ => 0

/-- Count binary product nodes. -/
def products : ℕ := ∑ v, match P.gate v with | .product _ _ => 1 | _ => 0

/-- **Decomposable threshold counting.** The denotation of a smooth decomposable DAG cannot
be both large and rectangle-free unless the DAG has many nodes or edges. -/
theorem ncard_le (hK : 1 < K) (hS : K ≤ P.accepted.ncard)
    (hrect : RectangleFree P.accepted K) :
    P.accepted.ncard ≤ (K - 1) ^ 2 * P.unionEdges + (K - 1) ^ 3 * P.products := by
  classical
  calc P.accepted.ncard
      ≤ (⋃ v ∈ (Finset.univ : Finset N), P.stops K v).ncard :=
        ncard_le_ncard fun x hx => by
          obtain ⟨v, hv⟩ := P.exists_stop hK hS hx
          exact mem_iUnion₂.mpr ⟨v, Finset.mem_univ v, hv⟩
    _ ≤ ∑ v, (P.stops K v).ncard := Finset.set_ncard_biUnion_le _ _
    _ ≤ ∑ v, P.budget K v := Finset.sum_le_sum fun v _ => P.ncard_stops_le hrect v
    _ = (K - 1) ^ 2 * P.unionEdges + (K - 1) ^ 3 * P.products := by
      simp only [unionEdges, products, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v _
      cases hg : P.gate v <;> simp [budget, hg]

/-- A simpler bound charging the same cubic budget to each union edge or product node. -/
theorem ncard_le_size (hK : 1 < K) (hS : K ≤ P.accepted.ncard)
    (hrect : RectangleFree P.accepted K) :
    P.accepted.ncard ≤ (K - 1) ^ 3 * (P.unionEdges + P.products) := by
  have hpow : (K - 1) ^ 2 ≤ (K - 1) ^ 3 := by
    have : 1 ≤ K - 1 := by lia
    calc (K - 1) ^ 2 ≤ (K - 1) ^ 2 * (K - 1) := Nat.le_mul_of_pos_right _ this
      _ = (K - 1) ^ 3 := by ring
  exact (P.ncard_le hK hS hrect).trans (by
    rw [Nat.mul_add]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hpow) _)

end Finite

end Decomposable

end Complexity.Frontier
