/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Superconcentrator.Internal.Split

/-!
# Splitting the terminal component of a superconcentrator

Keep the edges whose tail lies in the undirected component of a vertex `r`. The split graph
of these edges is connected: the slots of one vertex are joined along its path, and an
undirected walk to `r` crosses from path to path along kept edges. Every directed walk inside
the component lifts to a directed walk of the split graph from any entering slot of its first
vertex to the last slot of its last vertex, staying in the paths of the vertices of the walk.

Lifting each walk of a vertex-disjoint family from the first slot of its first vertex to the
last slot of its last vertex gives a vertex-disjoint family of the split graph
(`exists_lift_walks`). All terminals of a superconcentrator lie in the component of its first
input, each input has a kept edge leaving it, and each output a kept edge entering it. Placing
every input at the first slot of its path and every output at the last slot, the split graph
is again a superconcentrator.
-/

@[expose] public section

open scoped Classical

namespace Algebraic.Cutwidth.Superconcentrator.Internal

open Multigraph Relation

variable {V E : Type} {G : Multigraph V E}

/-! ### Walks and undirected reachability -/

theorem adj_of_dirAdj {u v : V} (h : G.DirAdj u v) : G.Adj u v := by
  obtain ⟨e, h₁, h₂⟩ := h
  exact ⟨e, Or.inl ⟨h₁, h₂⟩⟩

/-- The ends of a directed walk are joined by an undirected walk. -/
theorem reflTransGen_of_isDirWalk {p : List V} {u v : V} (h : G.IsDirWalk p u v) :
    ReflTransGen G.Adj u v := by
  obtain ⟨l, -, hc, hlast⟩ := exists_eq_cons_of_isDirWalk h
  exact ReflTransGen.mono (fun _ _ => adj_of_dirAdj) _ _
    (List.relationReflTransGen_of_exists_isChain_cons l hc hlast)

/-- Every vertex of a directed walk is joined to its first vertex by an undirected walk. -/
theorem reflTransGen_of_mem_isDirWalk {p : List V} {u v : V} (h : G.IsDirWalk p u v) {z : V}
    (hz : z ∈ p) : ReflTransGen G.Adj u z := by
  obtain ⟨l, rfl, hc, -⟩ := exists_eq_cons_of_isDirWalk h
  exact List.IsChain.induction (fun z => ReflTransGen G.Adj u z) _ hc
    (fun _ _ hxy hx => hx.tail (adj_of_dirAdj hxy)) (fun _ => .refl) z hz

/-- In a superconcentrator, every input reaches every output. -/
theorem exists_isDirWalk {N : ℕ} {input output : Fin N → V}
    (h : G.Superconcentrator input output) (i j : Fin N) :
    ∃ p, G.IsDirWalk p (input i) (output j) := by
  obtain ⟨target, walk, hwalk, -⟩ := h.exists_walks {i} {j} (by simp)
  obtain ⟨hj, hw⟩ := hwalk i (Finset.mem_singleton_self i)
  rw [Finset.mem_singleton] at hj
  exact ⟨walk i, hj ▸ hw⟩

/-! ### The component of a vertex -/

variable [Fintype E]

/-- The edges of the undirected component of `r`, identified by their tails. -/
noncomputable def compEdges (G : Multigraph V E) (r : V) : Finset E :=
  Finset.univ.filter fun e => ReflTransGen G.Adj (G.fst e) r

theorem mem_compEdges {r : V} {e : E} :
    e ∈ compEdges G r ↔ ReflTransGen G.Adj (G.fst e) r := by
  simp [compEdges]

theorem reflTransGen_snd_of_mem_compEdges {r : V} {e : E} (he : e ∈ compEdges G r) :
    ReflTransGen G.Adj (G.snd e) r :=
  ReflTransGen.head ⟨e, Or.inr ⟨rfl, rfl⟩⟩ (mem_compEdges.1 he)

/-- A vertex with a slot lies in the component. -/
theorem reflTransGen_of_slots_pos {r w : V} (hw : 0 < slots G (compEdges G r) w) :
    ReflTransGen G.Adj w r := by
  unfold slots at hw
  rcases Nat.eq_zero_or_pos (inEdges G (compEdges G r) w).card with h | h
  · obtain ⟨e, he⟩ := Finset.card_pos.1 (by omega : 0 < (outEdges G (compEdges G r) w).card)
    simp only [outEdges, Finset.mem_filter] at he
    exact he.2 ▸ mem_compEdges.1 he.1
  · obtain ⟨e, he⟩ := Finset.card_pos.1 h
    simp only [inEdges, Finset.mem_filter] at he
    exact he.2 ▸ reflTransGen_snd_of_mem_compEdges he.1

/-- The split graph of a component is connected. -/
theorem split_connected {r : V} (hr : 0 < slots G (compEdges G r) r) :
    (split G (compEdges G r)).Connected := by
  set K := compEdges G r
  let ρ : SplitVertex G K := ⟨r, ⟨0, hr⟩⟩
  have key : ∀ w, ReflTransGen G.Adj w r →
      ∀ x : SplitVertex G K, x.1 = w → ReflTransGen (split G K).Adj x ρ := by
    intro w hw
    induction hw using ReflTransGen.head_induction_on with
    | refl => exact fun x hx => reflTransGen_adj_of_fst_eq hx
    | head hstep hrest ih =>
      intro x hx
      have ha := ReflTransGen.head hstep hrest
      obtain ⟨e, he⟩ := hstep
      have heK : e ∈ K := by
        rw [mem_compEdges]
        rcases he with ⟨h₁, -⟩ | ⟨h₁, -⟩ <;> rw [h₁] <;> assumption
      have hadj : (split G K).Adj (tail G K ⟨e, heK⟩) (head G K ⟨e, heK⟩) :=
        ⟨.inl ⟨e, heK⟩, Or.inl ⟨rfl, rfl⟩⟩
      rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact (reflTransGen_adj_of_fst_eq (y := tail G K ⟨e, heK⟩) (hx.trans h₁.symm)).trans
          (ReflTransGen.head hadj (ih _ h₂))
      · exact (reflTransGen_adj_of_fst_eq (y := head G K ⟨e, heK⟩) (hx.trans h₂.symm)).trans
          (ReflTransGen.head hadj.symm (ih _ h₁))
  exact connected_of_forall_reflTransGen ρ fun x =>
    key x.1 (reflTransGen_of_slots_pos (r := r) (w := x.1)
      (Nat.lt_of_le_of_lt (Nat.zero_le _) x.2.isLt)) x rfl

/-! ### Lifting walks -/

/-- A directed walk in the component lifts from any entering slot of its first vertex to the
last slot of its last vertex, through the paths of vertices of `P ⊇` the walk. -/
theorem reflTransGen_lift {r : V} (P : Set V) :
    ∀ (u : V) (l : List V), (u :: l).IsChain G.DirAdj → ReflTransGen G.Adj u r →
      (∀ z ∈ u :: l, z ∈ P) → ∀ x y : SplitVertex G (compEdges G r), x.1 = u →
        (x.2 : ℕ) ≤ (inEdges G (compEdges G r) u).card →
          y.1 = (u :: l).getLast (List.cons_ne_nil u l) →
            (y.2 : ℕ) + 1 = slots G (compEdges G r) y.1 → ReflTransGen (stepIn P) x y
  | u, [], _, _, hP, x, y, hx, _, hy, hlast => by
    have hxy : x.1 = y.1 := hx.trans (by simpa using hy.symm)
    have hs : slots G (compEdges G r) x.1 = slots G (compEdges G r) y.1 := by rw [hxy]
    have := x.2.isLt
    exact reflTransGen_forward P hxy (hx ▸ hP u List.mem_cons_self) (by omega)
  | u, w :: l, hc, hu, hP, x, y, hx, hxk, hy, hlast => by
    rw [List.isChain_cons_cons] at hc
    obtain ⟨⟨e, he₁, he₂⟩, hc⟩ := hc
    have heK : e ∈ compEdges G r := mem_compEdges.2 (he₁ ▸ hu)
    have hw : ReflTransGen G.Adj w r := ReflTransGen.head ⟨e, Or.inr ⟨he₁, he₂⟩⟩ hu
    have hcu : (inEdges G (compEdges G r) (G.fst e)).card =
        (inEdges G (compEdges G r) u).card := by rw [he₁]
    have hcw : (inEdges G (compEdges G r) (G.snd e)).card =
        (inEdges G (compEdges G r) w).card := by rw [he₂]
    have h₁ : ReflTransGen (stepIn P) x (tail G _ ⟨e, heK⟩) := by
      refine reflTransGen_forward P (hx.trans he₁.symm) (hx ▸ hP u List.mem_cons_self) ?_
      show (x.2 : ℕ) ≤ (inEdges G (compEdges G r) (G.fst e)).card + _
      omega
    have h₂ : stepIn P (tail G _ ⟨e, heK⟩) (head G _ ⟨e, heK⟩) :=
      ⟨⟨.inl ⟨e, heK⟩, rfl, rfl⟩, by
          show G.fst e ∈ P
          rw [he₁]
          exact hP u List.mem_cons_self, by
          show G.snd e ∈ P
          rw [he₂]
          exact hP w (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    have hpos : pos (inEdges G (compEdges G r) (G.snd e)) e
        (mem_inEdges_snd G (compEdges G r) ⟨e, heK⟩) <
          (inEdges G (compEdges G r) (G.snd e)).card :=
      pos_lt _
    have h₃ := reflTransGen_lift P w l hc hw (fun z hz => hP z (List.mem_cons_of_mem _ hz))
      (head G _ ⟨e, heK⟩) y he₂
      (by
        show pos (inEdges G (compEdges G r) (G.snd e)) e
          (mem_inEdges_snd G (compEdges G r) ⟨e, heK⟩) ≤ (inEdges G (compEdges G r) w).card
        omega) (by rw [hy, List.getLast_cons_cons]) hlast
    exact h₁.trans (ReflTransGen.head h₂ h₃)

/-- **Lifting one walk.** A directed walk from `u` to `v` in the component of `r`, where `u`
and `v` have slots, lifts to a directed walk of the split graph from the first slot of `u` to
the last slot of `v` that stays in the paths of the vertices of the walk. -/
theorem exists_lift_isDirWalk {r : V} {p : List V} {u v : V} (h : G.IsDirWalk p u v)
    (hr : ReflTransGen G.Adj u r) (hu : 0 < slots G (compEdges G r) u)
    (hv : 0 < slots G (compEdges G r) v) :
    ∃ q : List (SplitVertex G (compEdges G r)),
      (split G (compEdges G r)).IsDirWalk q ⟨u, ⟨0, hu⟩⟩
          ⟨v, ⟨slots G (compEdges G r) v - 1, Nat.sub_lt hv one_pos⟩⟩ ∧
        ∀ z ∈ q, z.1 ∈ p := by
  obtain ⟨l, hl, hc, hlast⟩ := exists_eq_cons_of_isDirWalk h
  have hR := reflTransGen_lift {z | z ∈ p} u l hc hr
    (fun z hz => by show z ∈ p; rw [hl]; exact hz) ⟨u, ⟨0, hu⟩⟩
    ⟨v, ⟨slots G (compEdges G r) v - 1, Nat.sub_lt hv one_pos⟩⟩ rfl (Nat.zero_le _) hlast.symm
    (by show slots G (compEdges G r) v - 1 + 1 = slots G (compEdges G r) v; omega)
  obtain ⟨l', hc', hlast'⟩ := List.exists_isChain_cons_of_relationReflTransGen hR
  refine ⟨⟨u, ⟨0, hu⟩⟩ :: l', ?_, ?_⟩
  · have := isDirWalk_of_isChain (hc'.imp fun _ _ hab => hab.1)
    rwa [hlast'] at this
  · exact List.IsChain.induction (fun z => z.1 ∈ p) _ hc'
      (fun _ _ hab _ => hab.2.2) (fun _ => by show u ∈ p; rw [hl]; simp)

/-- **Lifting a family of vertex-disjoint walks.** Let all terminals `input i` lie in the
component of `r`, and let every `input i` and every `output j` have a slot. Vertex-disjoint
directed walks from `input i` to `output (target i)` lift to vertex-disjoint directed walks of
the split graph from the first slot of `input i` to the last slot of `output (target i)`. -/
theorem exists_lift_walks {ι κ : Type*} {r : V} {input : ι → V} {output : κ → V}
    (hr : ∀ i, ReflTransGen G.Adj (input i) r)
    (hin : ∀ i, 0 < slots G (compEdges G r) (input i))
    (hout : ∀ j, 0 < slots G (compEdges G r) (output j)) {X : Finset ι} {target : ι → κ}
    {walk : ι → List V}
    (hwalk : ∀ i ∈ X, G.IsDirWalk (walk i) (input i) (output (target i)))
    (hdisj : ∀ i ∈ X, ∀ j ∈ X, i ≠ j → (walk i).Disjoint (walk j)) :
    ∃ walk' : ι → List (SplitVertex G (compEdges G r)),
      (∀ i ∈ X, (split G (compEdges G r)).IsDirWalk (walk' i) ⟨input i, ⟨0, hin i⟩⟩
          ⟨output (target i), ⟨slots G (compEdges G r) (output (target i)) - 1,
            Nat.sub_lt (hout (target i)) one_pos⟩⟩) ∧
        ∀ i ∈ X, ∀ j ∈ X, i ≠ j → (walk' i).Disjoint (walk' j) := by
  have H : ∀ i ∈ X, ∃ q : List (SplitVertex G (compEdges G r)),
      (split G (compEdges G r)).IsDirWalk q ⟨input i, ⟨0, hin i⟩⟩
          ⟨output (target i), ⟨slots G (compEdges G r) (output (target i)) - 1,
            Nat.sub_lt (hout (target i)) one_pos⟩⟩ ∧ ∀ z ∈ q, z.1 ∈ walk i :=
    fun i hi => exists_lift_isDirWalk (hwalk i hi) (hr i) (hin i) (hout (target i))
  choose! walk' hwalk' using H
  exact ⟨walk', fun i hi => (hwalk' i hi).1, fun i hi j hj hij z hzi hzj =>
    hdisj i hi j hj hij ((hwalk' i hi).2 z hzi) ((hwalk' j hj).2 z hzj)⟩

/-- **The split graph of a superconcentrator.** If all inputs lie in the component of `r`,
every input has a slot, and every output has a slot, then the split graph of the component is
a superconcentrator with inputs at first slots and outputs at last slots. -/
theorem split_superconcentrator {N : ℕ} {input output : Fin N → V}
    (h : G.Superconcentrator input output) {r : V} (hr : ∀ i, ReflTransGen G.Adj (input i) r)
    (hin : ∀ i, 0 < slots G (compEdges G r) (input i))
    (hout : ∀ j, 0 < slots G (compEdges G r) (output j)) :
    (split G (compEdges G r)).Superconcentrator (fun i => ⟨input i, ⟨0, hin i⟩⟩)
      (fun j => ⟨output j, ⟨slots G (compEdges G r) (output j) - 1,
        Nat.sub_lt (hout j) one_pos⟩⟩) where
  input_injective _ _ hij := h.input_injective (sigma_fin_eq_iff.1 hij).1
  output_injective _ _ hij := h.output_injective (sigma_fin_eq_iff.1 hij).1
  input_ne_output i j hij := h.input_ne_output i j (sigma_fin_eq_iff.1 hij).1
  exists_walks X Y hXY := by
    obtain ⟨target, walk, hwalk, hdisj⟩ := h.exists_walks X Y hXY
    obtain ⟨walk', hwalk', hdisj'⟩ := exists_lift_walks hr hin hout (X := X) (target := target)
      (fun i hi => (hwalk i hi).2) hdisj
    exact ⟨target, walk', fun i hi => ⟨(hwalk i hi).1, hwalk' i hi⟩, hdisj'⟩

end Algebraic.Cutwidth.Superconcentrator.Internal
