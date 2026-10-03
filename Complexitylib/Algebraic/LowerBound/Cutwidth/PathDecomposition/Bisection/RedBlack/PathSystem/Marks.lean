/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Marks.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Marks.Internal.Endpoints

/-!
# Marks and the cycle budget of shaded thin paths

Each shaded path contributes exactly two marks to its small attachments.
Consequently at most one component with two marks can be charged to each
shaded path. Because shading occurs in large original components, it leaves
small cyclic components untouched. They retain a separate unit of cycle
rank each: doubly marked components and small cyclic components together
number at most the original cycle rank.

Each shaded degree-two path also gives two endpoint marks, all outside the
eligible set. These marks record exactly the lost outside degrees. In
particular, a degree-three vertex made degree two receives a mark, keeping
it out of future unmarked paths. Simultaneous restoration charges at most
`3 M` added vertices per endpoint mark on the witness for the constructed
thin-path family.

The constructed isolation and core-forest theorems retain the stronger
cycle budget. These statements count the initial shading step. Preservation
through the later color swaps and leaf reorganization remains a separate
obligation.

Source: Burkhard Monien and Robert Preis, *Upper bounds on the bisection
width of 3- and 4-regular graphs*, Journal of Discrete Algorithms 4 (2006),
475–498, https://doi.org/10.1016/j.jda.2005.12.009, steps 3–4.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSystem

open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] (B : SimpleGraph V) (R : Multigraph V E)
  (U : Finset V) (M : Nat) (shaded : Finset (thinComponents B R U M))

/-- The mark count records every red attachment, including repeated target components. -/
theorem attachmentMarks_apply (C : B.ConnectedComponent) :
    attachmentMarks B R U M shaded C =
      ∑ i ∈ shaded, ∑ e ∈ attachmentEdges B R (region B U i.val) M,
        if attachmentComponent B R (region B U i.val) M e = C then
          3 - (attachmentEdges B R (region B U i.val) M).card else 0 :=
  Internal.attachmentMarks_apply B R U M shaded C

/-- Only original black components of size at most `M` receive attachment marks. -/
theorem attachmentMarks_eq_zero_of_large (C : B.ConnectedComponent)
    (large : M < Fintype.card C) : attachmentMarks B R U M shaded C = 0 :=
  Internal.attachmentMarks_eq_zero_of_large B R U M shaded C large

/-- Each shaded thin path contributes exactly two attachment marks. -/
theorem degree_attachmentMarks (degree : ∀ v ∈ U, B.degree v ≤ 2)
    (noPositive : ¬ ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X) :
    (attachmentMarks B R U M shaded).degree = 2 * shaded.card :=
  Internal.degree_attachmentMarks B R U M shaded degree noPositive

/-- At most one doubly marked component can be charged to each shaded path. -/
theorem card_doublyMarked_le (degree : ∀ v ∈ U, B.degree v ≤ 2)
    (noPositive : ¬ ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X)
    (components : Finset B.ConnectedComponent)
    (marked : ∀ C ∈ components, 2 ≤ attachmentMarks B R U M shaded C) :
    components.card ≤ shaded.card :=
  Internal.card_doublyMarked_le B R U M shaded degree noPositive components marked

/-- Shading paths in large components reserves one unit of cycle rank for each
untouched small cyclic component, in addition to the cost of shading. -/
theorem smallCycleBudget
    (large : ∀ v ∈ U, M < Fintype.card (B.connectedComponentMk v))
    (chosen : thinComponents B R U M → Sym2 V) (injective : Function.Injective chosen)
    (boundary : ∀ i, chosen i ∈ B.cutFinset (region B U i.val))
    (reachable : (B.deleteEdges (shaded.image chosen : Set (Sym2 V))).Reachable = B.Reachable) :
    SmallCycleBudget B M shaded.card :=
  Internal.smallCycleBudget B R U M shaded large chosen injective boundary reachable

/-- Doubly marked components and small cyclic components fit together within
the original cycle rank. -/
theorem smallCycleBudget_of_doublyMarked (degree : ∀ v ∈ U, B.degree v ≤ 2)
    (noPositive : ¬ ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X)
    (budget : SmallCycleBudget B M shaded.card) (marked : Finset B.ConnectedComponent)
    (twoMarks : ∀ C ∈ marked, 2 ≤ attachmentMarks B R U M shaded C) :
    SmallCycleBudget B M marked.card :=
  Internal.smallCycleBudget_of_doublyMarked B R U M shaded degree noPositive budget marked twoMarks

variable (F : RestorationFamily B R (thinComponents B R U M))
  (regions : ∀ C, F.region C = region B U C.val)

include regions

/-- Each shaded thin path gives exactly two endpoint marks, counting multiplicities. -/
theorem degree_endpointMarks (degree : ∀ v ∈ U, B.degree v = 2)
    (noPositive : ¬ ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X) :
    (F.restrict shaded).endpointMarks.degree = 2 * shaded.card :=
  Internal.degree_endpointMarks B R U M shaded F regions degree noPositive

/-- Endpoint marks lie outside the entire eligible set, including unshaded regions. -/
theorem endpointMarks_eq_zero_of_mem {v : V} (eligible : v ∈ U) :
    (F.restrict shaded).endpointMarks v = 0 :=
  Internal.endpointMarks_eq_zero_of_mem B R U M shaded F regions eligible

/-- The degree lost at an ineligible vertex is exactly its endpoint mark count. -/
theorem degree_isolated_add_endpointMarks {v : V} (outside : v ∉ U) :
    (F.restrict shaded).deletedGraph.degree v + (F.restrict shaded).endpointMarks v =
      B.degree v :=
  Internal.degree_isolated_add_endpointMarks B R U M shaded F regions outside

/-- A degree-three vertex made degree two by isolation receives a mark, so it
does not enter the next family of unmarked degree-two paths. -/
theorem newly_degree_two_marked (degree : ∀ v ∈ U, B.degree v ≤ 2)
    {v : V} (original : B.degree v = 3) (remaining : (F.restrict shaded).deletedGraph.degree v = 2) :
    (F.restrict shaded).endpointMarks v = 1 :=
  Internal.newly_degree_two_marked B R U M shaded F regions degree original remaining

end Algebraic.Cutwidth.Bisection.RedBlack.PathSystem
