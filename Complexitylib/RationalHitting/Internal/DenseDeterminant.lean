/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.SignedArithmetic

/-!
# Rational hitting lists: dense determinant

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/DenseDeterminant.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open Function

@[simp] lemma list_code_length_nil {A : Type} [Coding A] : (code ([] : List A)).length=0 := rfl
@[simp] lemma list_code_cons {A : Type} [Coding A] (a : A) (l : List A) :
    (code (a::l)).length=2*(code a).length+1+(code l).length := by
  change (listCode code (a::l)).length=2*(code a).length+1+(listCode code l).length
  simp

lemma code_le_of_mem {A : Type} [Coding A] {a : A} {l : List A} (h : a∈l) :
    (code a).length≤(code l).length := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.mem_cons] at h
    simp only [list_code_cons]
    rcases h with rfl|h
    · omega
    · have hh:=ih h;omega

lemma list_code_length_le {A : Type} [Coding A] (l : List A) (B : ℕ)
    (h : ∀ a∈l,(code a).length≤B) : (code l).length≤l.length*(2*B+1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih (by intro b hb;exact h b (by simp [hb]))
    simp only [list_code_cons,List.length_cons]
    nlinarith only [ha,hl]

lemma drop_headD_getElem {A : Type} (l : List A) (z : A) (i : ℕ) (hi : i<l.length) :
    (l.drop i).headD z=l[i] := by
  rw [List.headD_eq_getD,List.getD_eq_getElem]
  · exact List.getElem_drop
  · simp;omega

lemma finRows_access {A : Type} (z : A) {n : ℕ} (f : Fin n → A) (i : Fin n) :
    (((List.finRange n).map f).drop i.val).headD z=f i := by
  rw [drop_headD_getElem _ _ i.val (by simp)]
  simp

lemma finRange_map_val (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

lemma range_map_to_finRange {A : Type} (n : ℕ) (f : ℕ → A) :
    (List.range n).map f=(List.finRange n).map (fun i=>f i.val) := by
  rw [←finRange_map_val,List.map_map]
  rfl

/-- A square integer matrix carrying its dimension. -/
structure DenseSquare where
  /-- Number of rows and columns. -/
  dim : ℕ
  /-- Integer matrix entries. -/
  val : Matrix (Fin dim) (Fin dim) ℤ

/-- Enumerate the matrix entries as a list of rows. -/
def DenseSquare.rows (a : DenseSquare) : List (List ℤ) :=
  (List.finRange a.dim).map fun i => (List.finRange a.dim).map fun j => a.val i j

instance : Coding DenseSquare := ⟨fun a => code (Unary.mk a.dim,a.rows)⟩

instance : Inhabited DenseSquare := ⟨⟨0,0⟩⟩

/-- Read a matrix entry, returning zero outside the stored dimension. -/
def DenseSquare.get (a : DenseSquare) (i j : ℕ) : ℤ :=
  if hi : i<a.dim then if hj : j<a.dim then a.val ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0

@[simp] lemma DenseSquare.get_fin (a : DenseSquare) (i j : Fin a.dim) :
    a.get i.val j.val=a.val i j := by simp [DenseSquare.get]

lemma DenseSquare.rows_get (a : DenseSquare) (i j : ℕ) :
    (((a.rows.drop i).headD []).drop j).headD 0=a.get i j := by
  unfold DenseSquare.get
  by_cases hi : i<a.dim
  · rw [dite_eq_left hi]
    have he := finRows_access ([] : List ℤ) (fun i : Fin a.dim =>
      (List.finRange a.dim).map (fun j => a.val i j)) ⟨i,hi⟩
    change (List.drop j ((List.drop i a.rows).headD [])).headD 0 = _
    change (a.rows.drop i).headD [] = (List.finRange a.dim).map (fun j => a.val ⟨i,hi⟩ j) at he
    rw [he]
    by_cases hj : j<a.dim
    · rw [dite_eq_left hj]
      exact finRows_access 0 _ ⟨j,hj⟩
    · rw [dite_eq_right hj,List.drop_eq_nil_iff.mpr (by simpa using Nat.le_of_not_lt hj)]
      rfl
  · rw [dite_eq_right hi]
    have he : a.rows.drop i=[] := List.drop_eq_nil_iff.mpr (by
      simpa [rows] using Nat.le_of_not_lt hi)
    rw [he];simp

lemma DenseSquare.dim_le_code (a : DenseSquare) : a.dim≤(code a).length := by
  change a.dim≤(code (Unary.mk a.dim,a.rows)).length
  simp only [prod_code_length,unary_code_length];omega

lemma DenseSquare.entry_bits_le_code (a : DenseSquare) (i j : Fin a.dim) :
    (a.val i j).natAbs.bits.length≤(code a).length := by
  have hi : ((List.finRange a.dim).map (fun j => a.val i j))∈a.rows := by
    exact List.mem_map.mpr ⟨i,by simp,rfl⟩
  have hj : a.val i j∈((List.finRange a.dim).map (fun j => a.val i j)) := by simp
  have h := (code_le_of_mem hj).trans (code_le_of_mem hi)
  change _≤(code (Unary.mk a.dim,a.rows)).length
  simp only [int_code_length] at h
  simp only [prod_code_length,unary_code_length]
  omega

lemma DenseSquare.get_bits_le_code (a : DenseSquare) (i j : ℕ) :
    (a.get i j).natAbs.bits.length≤(code a).length := by
  unfold DenseSquare.get
  split_ifs with hi hj
  · exact a.entry_bits_le_code ⟨i,hi⟩ ⟨j,hj⟩
  all_goals simp

lemma DenseSquare.code_length_le (a : DenseSquare) (b : ℕ)
    (h : ∀ i j,(a.val i j).natAbs.bits.length≤b) :
    (code a).length≤4*a.dim^2*b+14*a.dim^2+3*a.dim+1 := by
  have hr : ∀ l∈a.rows,(code l).length≤a.dim*(2*b+7) := by
    intro l hl
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hl
    have hh := list_code_length_le ((List.finRange a.dim).map (fun j => a.val i j)) (b+3)
      (by
        intro x hx
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
        simp only [int_code_length]
        have := h i j
        omega)
    convert hh using 1 ; simp only [List.length_map,List.length_finRange] ; ring
  have hl := list_code_length_le a.rows (a.dim*(2*b+7)) hr
  have hlen : a.rows.length=a.dim := by simp [rows]
  rw [hlen] at hl
  change (code (Unary.mk a.dim,a.rows)).length≤_
  simp only [prod_code_length,unary_code_length]
  nlinarith only [hl]

namespace Poly
@[fun_prop] theorem denseDim : Poly (fun a : DenseSquare => Unary.mk a.dim) :=
  (Feasible.fst (code : Unary→List Bool) (code : List (List ℤ)→List Bool)).recode
    _ _ _ (fun a => (Unary.mk a.dim,a.rows)) (by intro a;rfl) (by intro a;rfl)
@[fun_prop] theorem denseRows : Poly DenseSquare.rows :=
  (Feasible.snd (code : Unary→List Bool) (code : List (List ℤ)→List Bool)).recode
    _ _ _ (fun a => (Unary.mk a.dim,a.rows)) (by intro a;rfl) (by intro a;rfl)

@[fun_prop] theorem denseGet : Poly (fun a : DenseSquare×(Unary×Unary) => a.1.get a.2.1.val
    a.2.2.val) := by
  have hr := (listGetD ([] : List ℤ)).comp
    (show Poly (fun a : DenseSquare×(Unary×Unary) => (a.2.1,a.1.rows)) by fun_prop)
  have hh := (listGetD (0 : ℤ)).comp
    ((show Poly (fun a : DenseSquare×(Unary×Unary) => a.2.2) by fun_prop).pair hr)
  exact hh.of_eq (fun a => a.1.rows_get _ _)

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

namespace Poly
variable {A : Type} [Coding A]

theorem denseBuild {n : A → Unary} {f : A×(Unary×Unary) → ℤ}
    (hn : Poly n) (hf : Poly f) :
    Poly (fun a : A => (⟨(n a).val,fun i j => f (a,(⟨i.val⟩,⟨j.val⟩))⟩ : DenseSquare)) := by
  have hc : Poly (fun a : (A×Unary)×Unary => f (a.1.1,(a.1.2,a.2))) :=
    hf.comp (by fun_prop)
  have hr := hc.tabulate.comp
    ((hn.comp (show Poly (Prod.fst : A×Unary → A) from fst)).pair
      (show Poly (fun a : A×Unary => a) from id))
  have hm := hr.tabulate.comp (hn.pair (show Poly (fun a : A => a) from id))
  have hh := hn.pair hm
  refine hh.recode _ _ _ (fun x => x) (by intro a;rfl) ?_
  intro a
  change code (n a,(List.range (n a).val).map (fun i =>
      (List.range (n a).val).map (fun j => f (a,(⟨i⟩,⟨j⟩))))) =
    code ((n a), (List.finRange (n a).val).map (fun i =>
      (List.finRange (n a).val).map (fun j => f (a,(⟨i.val⟩,⟨j.val⟩)))))
  simp only [range_map_to_finRange]

theorem sumRange {f : A×Unary → ℤ} (hf : Poly f) :
    Poly (fun a : Unary×A => ((List.range a.1.val).map (fun i => f (a.2,⟨i⟩))).sum) :=
  listSum.comp hf.tabulate

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function
open scoped BigOperators

/-- Package an indexed matrix with its dimension. -/
def DenseSquare.of {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : DenseSquare := ⟨n,A⟩

/-- One Bird determinant stage on dimension-carrying matrices. -/
def DenseSquare.step (A F : DenseSquare) : DenseSquare :=
  ⟨A.dim, BirdDet.Spec.stepEntry A.val (fun i j => F.get i.val j.val)⟩

@[simp] lemma DenseSquare.step_dim (A F : DenseSquare) : (A.step F).dim=A.dim := rfl
@[simp] lemma DenseSquare.step_of {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℤ) :
    (DenseSquare.of A).step (DenseSquare.of F)=DenseSquare.of (BirdDet.Spec.stepEntry A F) := by
  simp [DenseSquare.step,DenseSquare.of,DenseSquare.get]

lemma sum_diag_range (A : DenseSquare) (F : DenseSquare) (i : Fin A.dim) :
    ((List.range A.dim).map (fun k => if i.val<k then F.get k k else 0)).sum =
      ∑ k ∈ Finset.Ioi i, F.get k.val k.val := by
  rw [range_map_to_finRange,←List.ofFn_eq_map,List.sum_ofFn]
  simp [←Finset.sum_filter,Finset.filter_lt_eq_Ioi]

lemma sum_product_range (A : DenseSquare) (F : DenseSquare) (i j : Fin A.dim) :
    ((List.range A.dim).map (fun k => if i.val<k then F.get i.val k*A.get k j.val else 0)).sum =
      ∑ k ∈ Finset.Ioi i, F.get i.val k.val*A.val k j := by
  rw [range_map_to_finRange,←List.ofFn_eq_map,List.sum_ofFn]
  simp [←Finset.sum_filter,Finset.filter_lt_eq_Ioi]

namespace Poly

@[fun_prop] theorem denseStep : Poly (fun a : DenseSquare×DenseSquare => a.1.step a.2) := by
  have hd : Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×Unary =>
      if a.1.2.1.val<a.2.val then a.1.1.2.get a.2.val a.2.val else (0:ℤ)) := by
    have ht := unaryLt.comp (show Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×Unary =>
      (a.1.2.1,a.2)) by fun_prop)
    have hg := denseGet.comp (show Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×Unary =>
      (a.1.1.2,(a.2,a.2))) by fun_prop)
    exact (ht.cond hg (const 0)).of_eq (by intro a;simp)
  have hp : Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×Unary =>
      if a.1.2.1.val<a.2.val then a.1.1.2.get a.1.2.1.val a.2.val *
        a.1.1.1.get a.2.val a.1.2.2.val else (0:ℤ)) := by
    have ht := unaryLt.comp (show Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×Unary =>
      (a.1.2.1,a.2)) by fun_prop)
    have hg1 := denseGet.comp (show Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×Unary =>
      (a.1.1.2,(a.1.2.1,a.2))) by fun_prop)
    have hg2 := denseGet.comp (show Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×Unary =>
      (a.1.1.1,(a.2,a.1.2.2))) by fun_prop)
    exact (ht.cond (intMul.comp (hg1.pair hg2)) (const 0)).of_eq (by intro a;simp)
  have hn := denseDim.comp (show Poly (fun a : (DenseSquare×DenseSquare)×(Unary×Unary) => a.1.1)
    by fun_prop)
  have hs1 := hd.sumRange.comp (hn.pair (show Poly (fun a :
    (DenseSquare×DenseSquare)×(Unary×Unary) => a) from id))
  have hs2 := hp.sumRange.comp (hn.pair (show Poly (fun a :
    (DenseSquare×DenseSquare)×(Unary×Unary) => a) from id))
  have hget := denseGet.comp (show Poly (fun a : (DenseSquare×DenseSquare)×(Unary×Unary) =>
    (a.1.1,a.2)) by fun_prop)
  have he := intAdd.comp ((intMul.comp ((intNeg.comp hs1).pair hget)).pair hs2)
  have hh := denseBuild (denseDim.comp (show Poly (Prod.fst : DenseSquare×DenseSquare →
    DenseSquare) from fst)) he
  refine hh.of_eq ?_
  intro a
  congr 1
  funext i j
  simp only [sum_diag_range,sum_product_range,DenseSquare.get_fin]
  exact (congrFun (congrFun (BirdDet.Spec.stepEntry_eq a.1.val
    (fun i j => a.2.get i.val j.val)) i) j).symm

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

lemma abs_le_pow_of_bits_le (z : ℤ) (b : ℕ) (h : z.natAbs.bits.length≤b) :
    |z|≤(2:ℤ)^b := by
  rw [Nat.size_eq_bits_len] at h
  have hh := (Nat.size_le.mp h).le
  rw [←Int.natCast_natAbs]
  exact_mod_cast hh

lemma bits_le_of_abs_le_pow (z : ℤ) (b : ℕ) (h : |z|≤(2:ℤ)^b) :
    z.natAbs.bits.length≤b+1 := by
  rw [←Int.natCast_natAbs] at h
  have hn : z.natAbs≤2^b := by exact_mod_cast h
  calc _ ≤ (2^b).bits.length := nat_bits_mono hn
       _ = b+1 := by rw [Nat.size_eq_bits_len,Nat.size_pow]

lemma DenseSquare.get_abs_le (A : DenseSquare) (i j : ℕ) :
    |A.get i j|≤(2:ℤ)^(code A).length :=
  abs_le_pow_of_bits_le _ _ (A.get_bits_le_code i j)

lemma DenseSquare.step_get_bound (A F : DenseSquare) (B C : ℕ)
    (hA : ∀ i j,|A.get i j|≤B) (hF : ∀ i j,|F.get i j|≤C) (i j : ℕ) :
    |(A.step F).get i j|≤(2*A.dim*B*C:ℕ) := by
  have he : ∀ u v : Fin A.dim, |A.val u v|≤(B:ℤ) := by
    intro u v
    have hh := hA u.val v.val
    rw [DenseSquare.get_fin] at hh
    exact hh
  have hh := DeterminantAlgorithm.step_bound A.val (fun u v => F.get u.val v.val) B C he
    (fun u v => hF u.val v.val)
  change |(if hi : i<A.dim then if hj : j<A.dim then
    BirdDet.Spec.stepEntry A.val (fun u v => F.get u.val v.val) ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0)|≤_
  split_ifs with hi hj
  · exact hh ⟨i,hi⟩ ⟨j,hj⟩
  all_goals simp only [abs_zero]; positivity

lemma DenseSquare.iterate_get_bound (A F : DenseSquare) (b : ℕ)
    (hA : ∀ i j,|A.get i j|≤(2:ℤ)^b) (hF : ∀ i j,|F.get i j|≤(2:ℤ)^b)
    (k i j : ℕ) : |((A.step)^[k] F).get i j|≤(2:ℤ)^(b+k*(1+A.dim+b)) := by
  induction k generalizing i j with
  | zero => simpa using hF i j
  | succ k ih =>
    rw [iterate_succ_apply']
    have hf : 2*A.dim*2^b≤2^(1+A.dim+b) := by
      calc _ ≤2*2^A.dim*2^b := Nat.mul_le_mul_right _
            (Nat.mul_le_mul_left _ (DeterminantAlgorithm.self_le_two_pow A.dim))
           _ = _ := by rw [pow_add,pow_add];norm_num
    have ht := A.step_get_bound ((A.step)^[k] F) (2^b) (2^(b+k*(1+A.dim+b)))
      (by simpa using hA) (by intro u v;simpa using ih u v) i j
    calc _ ≤ ((2*A.dim*2^b*2^(b+k*(1+A.dim+b)):ℕ):ℤ) := ht
         _ ≤ ((2^(1+A.dim+b)*2^(b+k*(1+A.dim+b)):ℕ):ℤ) := by
           exact_mod_cast Nat.mul_le_mul_right (2^(b+k*(1+A.dim+b))) hf
         _ = _ := by push_cast;rw [←pow_add];congr 1;ring

lemma DenseSquare.iterate_dim (A F : DenseSquare) (k : ℕ) :
    ((A.step)^[k+1] F).dim=A.dim := by rw [iterate_succ_apply'];rfl

lemma DenseSquare.iterate_code_bound (A F : DenseSquare) (b k : ℕ)
    (hA : (code A).length≤b) (hF : (code F).length≤b) :
    (code ((A.step)^[k+1] F)).length≤
      4*A.dim^2*(b+(k+1)*(1+A.dim+b)+1)+14*A.dim^2+3*A.dim+1 := by
  have hg := DenseSquare.iterate_get_bound A F b
    (fun i j => abs_le_pow_of_bits_le _ _ ((A.get_bits_le_code i j).trans hA))
    (fun i j => abs_le_pow_of_bits_le _ _ ((F.get_bits_le_code i j).trans hF)) (k+1)
  have hh := DenseSquare.code_length_le ((A.step)^[k+1] F) (b+(k+1)*(1+A.dim+b)+1)
    (by
      intro i j
      apply bits_le_of_abs_le_pow
      rw [←DenseSquare.get_fin ((A.step)^[k+1] F) i j]
      exact hg i.val j.val)
  simpa only [DenseSquare.iterate_dim] using hh

/-- Advance the Bird stage while preserving the original matrix. -/
def birdState (a : DenseSquare×DenseSquare) : DenseSquare×DenseSquare := (a.1,a.1.step a.2)

lemma birdState_iterate (a : DenseSquare×DenseSquare) (k : ℕ) :
    birdState^[k] a=(a.1,(a.1.step)^[k] a.2) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [iterate_succ_apply',ih,birdState]

lemma birdState_iterate_size (n : ℕ) (a : DenseSquare×DenseSquare) (i : ℕ) (hi : i≤n) :
    (code (birdState^[i] a)).length≤
      (64*(TimeBound.variable+1)^4).eval ((pairCode unaryCode code (n,a)).length+1) := by
  let L := (pairCode unaryCode code (n,a)).length+1
  have hL : L=2*n+2+2*(code a.1).length+1+(code a.2).length := by
    simp [L,pairCode_length,unaryCode_length,prod_code_length];omega
  have hA : (code a.1).length≤L := by omega
  have hF : (code a.2).length≤L := by omega
  have hn : n≤L := by omega
  have hd : a.1.dim≤L := a.1.dim_le_code.trans hA
  simp only [TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_pow,TimeBound.eval_add,
    TimeBound.eval_variable]
  change _≤64*(L+1)^4
  rw [birdState_iterate,prod_code_length]
  cases i with
  | zero => simp;nlinarith only [hA,hF,Nat.zero_le (L^2),Nat.zero_le (L^3),Nat.zero_le (L^4)]
  | succ k =>
    have hh := a.1.iterate_code_bound a.2 L k hA hF
    have hek : L+(k+1)*(1+a.1.dim+L)+1≤2*(L+1)^2 := by
      have hk : k+1≤L := hi.trans hn
      have hm := Nat.mul_le_mul hk (show 1+a.1.dim+L≤1+L+L by omega)
      nlinarith only [hm]
    have hm := Nat.mul_le_mul (Nat.pow_le_pow_left hd 2) hek
    have h2 := Nat.pow_le_pow_left hd 2
    nlinarith only [hh,hm,h2,hd,hA,Nat.zero_le (L^2),Nat.zero_le (L^3),Nat.zero_le (L^4)]

namespace Poly
@[fun_prop] theorem birdState_poly : Poly birdState :=
  (show Poly (Prod.fst : DenseSquare×DenseSquare → DenseSquare) from fst).pair denseStep

@[fun_prop] theorem birdStages : Poly (fun a : Unary×DenseSquare => (a.2.step)^[a.1.val] a.2) := by
  have hh := birdState_poly.iterate (64*(TimeBound.variable+1)^4) birdState_iterate_size
  have hs := (show Poly (Prod.snd : DenseSquare×DenseSquare → DenseSquare) from snd).comp
    (hh.comp (show Poly (fun a : Unary×DenseSquare => (a.1,(a.2,a.2))) by fun_prop))
  exact hs.of_eq (by intro a;simp [birdState_iterate])
end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

/-- The executable determinant obtained from bounded Bird iteration. -/
def DenseSquare.detAlgorithm (A : DenseSquare) : ℤ :=
  if A.dim=0 then 1 else (-1:ℤ)^(A.dim-1)*((A.step)^[A.dim-1] A).get 0 0

lemma DenseSquare.iterate_of {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) :
    ((DenseSquare.of A).step)^[k] (DenseSquare.of A)=
      DenseSquare.of ((BirdDet.Spec.stepEntry A)^[k] A) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply',ih,DenseSquare.step_of,iterate_succ_apply']

lemma DenseSquare.detAlgorithm_eq (A : DenseSquare) : A.detAlgorithm=A.val.det := by
  obtain ⟨n,A⟩:=A
  change (DenseSquare.of A).detAlgorithm=A.det
  rw [←DeterminantAlgorithm.spec_eq_det]
  cases n with
  | zero => simp [DenseSquare.detAlgorithm,DenseSquare.of,BirdDet.Spec.birdDetSpec_zero]
  | succ k =>
    rw [BirdDet.Spec.birdDetSpec_succ]
    unfold DenseSquare.detAlgorithm
    change (if k+1=0 then (1:ℤ) else (-1:ℤ)^((k+1)-1)*
      (((DenseSquare.of A).step)^[(k+1)-1] (DenseSquare.of A)).get 0 0)=_
    simp only [Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,DenseSquare.iterate_of]
    simp [DenseSquare.get,DenseSquare.of]

namespace Poly
@[fun_prop] theorem denseDet : Poly (fun A : DenseSquare => A.val.det) := by
  have hn := unaryPred.comp denseDim
  have hs := birdStages.comp (hn.pair (show Poly (fun A : DenseSquare => A) from id))
  have he := denseGet.comp (hs.pair (const ((⟨0⟩:Unary),(⟨0⟩:Unary))))
  have hsign := intPow.comp ((const (-1:ℤ)).pair hn)
  have hv := intMul.comp (hsign.pair he)
  have hz := unaryZero.comp denseDim
  exact (hz.cond (const (1:ℤ)) hv).of_eq (by
    intro A
    simpa only [decide_eq_true_eq,DenseSquare.detAlgorithm] using A.detAlgorithm_eq)
end Poly
end RationalHitting.StackLanguage

end Complexity
