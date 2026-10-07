/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.InputAdapter

/-!
# Rational hitting lists: output adapter

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/OutputAdapter.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.TMTime.OutputAdapter
open Turing
/-- The fixed four-symbol alphabet of the tape adapter. -/
abbrev A := Fin 4
/-- The ten control states used by the tape adapter. -/
abbrev Q := Fin 10
/-- A fixed-width encoded block stored in the finite control. -/
abbrev Word (b : ℕ) := Fin b → Bool
/-- Finite auxiliary storage used by the tape adapter. -/
abbrev V (b : ℕ) := Word b × Option Bool
/-- A tape-adapter instruction with finite auxiliary storage. -/
abbrev Stmt (b : ℕ) := TM1.Stmt A Q (V b)
/-- A configuration of the tape adapter. -/
abbrev Cfg (b : ℕ) := TM1.Cfg A Q (V b)
/-- Encode a literal output or input bit by a nonblank tape symbol. -/
def raw (x : Bool) : A := if x then 2 else 1
/-- Encode a bit inside the compiler's binary tape representation. -/
def bit (x : Bool) : A := if x then 1 else 0

/-- Jump to the specified adapter control state. -/
def jump {b} (q : Q) : Stmt b := .goto (fun _ _ => q)
/-- Move the tape head and jump to the specified state. -/
def move {b} (d : Dir) (q : Q) : Stmt b := .move d (jump q)
/-- Move left and branch according to whether the delimiter was reached. -/
def leftTo {b} (q r : Q) : Stmt b :=
  .move .left (.branch (fun a _ => a==3) (jump r) (jump q))

/-- Read the designated block coordinates into the finite auxiliary storage. -/
def readBlock {b} : List (Fin b) → Stmt b → Stmt b
  | [],q => q
  | i::is,q => .load (fun a v => (Function.update v.1 i (a==1),v.2))
      (.write (fun _ _ => 0) (.move .right (readBlock is q)))

/-- Write a fixed-width Boolean block as tape symbols. -/
def block {b} (w : Word b) : List A := (List.finRange b).map (fun i => bit (w i))
/-- Copy the designated coordinates from one stored block to another. -/
def fill {b} (is : List (Fin b)) (w v : Word b) : Word b :=
  is.foldl (fun u i => Function.update u i (w i)) v

lemma fill_apply {b} (is : List (Fin b)) (w v : Word b) (j : Fin b) :
    fill is w v j=if j∈is then w j else v j := by
  induction is generalizing v with
  | nil => simp [fill]
  | cons i is ih =>
    simp only [fill,List.foldl_cons] at *
    rw [ih]
    by_cases hi : j=i <;> by_cases hj : j∈is <;> simp_all

@[simp] lemma fill_all {b} (w v : Word b) : fill (List.finRange b) w v=w := by
  funext j
  simp [fill_apply]

@[simp] lemma head₂ (L R : List A) : (Tape.mk₂ L R).head=R.headI := rfl
lemma right₂ (L : List A) (a : A) (R : List A) :
    (Tape.mk₂ L (a::R)).move .right=Tape.mk₂ (a::L) R := by simp [Tape.mk₂]
lemma left₂ (a : A) (L R : List A) :
    (Tape.mk₂ (a::L) R).move .left=Tape.mk₂ L (a::R) := by simp [Tape.mk₂]

attribute [local simp] left₂

lemma left_empty (R : List A) :
    (Tape.mk₂ [] R).move .left=Tape.mk₂ [] (0::R) := by simp [Tape.mk₂]
lemma write₂ (L R : List A) (a : A) :
    (Tape.mk₂ L R).write a=Tape.mk₂ L (a::R.tail) := by simp [Tape.mk₂]
@[simp] lemma bit_beq_one (x : Bool) : (bit x==1)=x := by cases x <;> decide
@[simp] lemma bit_ne_three (x : Bool) : bit x≠3 := by cases x <;> decide
@[simp] lemma raw_ne_three (x : Bool) : raw x≠3 := by cases x <;> decide

lemma readBlock_spec {b} (is : List (Fin b)) (w v : Word b) (x : Option Bool)
    (q : Stmt b) (L R : List A) :
    TM1.stepAux (readBlock is q) (v,x) (Tape.mk₂ L (is.map (fun i => bit (w i))++R))=
      TM1.stepAux q (fill is w v,x) (Tape.mk₂ (List.replicate is.length 0++L) R) := by
  induction is generalizing v L with
  | nil => simp [readBlock,fill]
  | cons i is ih =>
    simp only [readBlock,List.map_cons,List.cons_append,TM1.stepAux,head₂,List.headI_cons,
      bit_beq_one,write₂,List.tail_cons,right₂,ih,fill,List.foldl_cons,List.length_cons]
    congr 2
    simp [List.replicate_succ',List.append_assoc]

/-- The fixed finite control map of the tape adapter. -/
def machine {b} (get : Word b → Option Bool) : Q → Stmt b
  | 0 => .move .left (.write (fun _ _ => 3) (.move .left (.write (fun _ _ => 3)
      (.move .left (.write (fun _ _ => 3) (.move .right (move .right 1)))))))
  | 1 => .write (fun _ _ => 0) (.move .right (readBlock (List.finRange b)
      (.load (fun _ v => (v.1,get v.1)) (.branch (fun _ v => v.2.isSome)
        (.move .left (.write (fun _ _ => 3) (jump 2))) (jump 5)))))
  | 2 => leftTo 2 3
  | 3 => .write (fun _ v => raw (v.2.getD false)) (.move .right
      (.write (fun _ _ => 3) (move .right 4)))
  | 4 => .branch (fun a _ => a==3) (jump 1) (move .right 4)
  | 5 => leftTo 5 6
  | 6 => .write (fun _ _ => 0) (jump 7)
  | 7 => leftTo 7 8
  | _ => .write (fun _ _ => 0) (.move .right .halt)

/-- Assemble a configuration from the control state and the two tape halves. -/
def state {b} (q : Q) (v : V b) (L R : List A) : Cfg b := ⟨some q,v,Tape.mk₂ L R⟩
/-- The tape layout preserved by the adapter's main scanning loop. -/
def invariant {b} (gap : ℕ) (out : List Bool) (R : List A) (v : V b) : Cfg b :=
  state 1 v (List.replicate gap 0++3::(out.reverse.map raw)++[3]) (3::R)

lemma scan_right {b} (F : Q → Stmt b) (q : Q) (v : V b) (l L R : List A)
    (h : ∀ a∈l, ∀ L R, TM1.step F (state q v L (a::R))=some (state q v (a::L) R)) :
    exec (TM1.step F) l.length (state q v L (l++R))=
      some (state q v (l.reverse++L) R) := by
  induction l generalizing L R with
  | nil => simp
  | cons a l ih =>
    have hs := h a (by simp) L (l++R)
    simp only [List.cons_append,List.length_cons,exec,hs,Option.bind_some]
    simpa [List.reverse_cons,List.append_assoc] using ih (a::L) R (fun z hz => h z (by simp [hz]))

lemma scan_left {b} (F : Q → Stmt b) (q r : Q) (v : V b) (l L R : List A)
    (hF : F q=leftTo q r) (hl : ∀ a∈l, a≠3) :
    exec (TM1.step F) (l.length+1) (state q v (l++3::L) R)=
      some (state r v L (3::l.reverse++R)) := by
  induction l generalizing R with
  | nil => simp [exec,state,TM1.step,hF,leftTo,jump,TM1.stepAux,Tape.mk₂]
  | cons a l ih =>
    have ha := hl a (by simp)
    have hh := ih (a::R) (fun z hz => hl z (by simp [hz]))
    have hs : TM1.step F (state q v ((a::l)++3::L) R)=
        some (state q v (l++3::L) (a::R)) := by
      simp [state,TM1.step,hF,leftTo,TM1.stepAux,beq_eq_false_iff_ne.mpr ha,jump]
    change (TM1.step F _).bind (exec (TM1.step F) (l.length+1)) = _
    rw [hs,Option.bind_some]
    simpa [List.reverse_cons,List.append_assoc] using hh

lemma zeros_cons (k : ℕ) (L : List A) :
    List.replicate k (0:A)++0::L=0::(List.replicate k 0++L) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons 0) ih

lemma consume_some {b} (get : Word b → Option Bool) (w : Word b) (x : Bool)
    (hx : get w=some x) (gap : ℕ) (out : List Bool) (R : List A) (v : V b) :
    exec (TM1.step (machine get)) 1 (invariant gap out (block w++R) v)=
      some (state 2 (w,some x) (List.replicate (gap+b) 0++3::out.reverse.map raw++[3]) (3::R)) := by
  rcases v with ⟨va,vo⟩
  simp only [exec,TM1.step,invariant,state,machine,TM1.stepAux,write₂,List.tail_cons,right₂,
    block,readBlock_spec,fill_all,List.length_finRange,hx,Option.isSome_some,Bool.cond_true,
    zeros_cons,left₂,jump,Option.bind_some]
  simp only [List.replicate_add,List.append_assoc,Nat.add_comm,List.cons_append]

lemma emit_one {b} (hb : 1≤b) (get : Word b → Option Bool) (w : Word b) (x : Bool)
    (hx : get w=some x) (gap : ℕ) (out : List Bool) (R : List A) (v : V b) :
    exec (TM1.step (machine get)) (2*(gap+b)+3) (invariant gap out (block w++R) v)=
      some (invariant (gap+b-1) (out++[x]) R (w,some x)) := by
  let L := out.reverse.map raw++[3]
  let Z := List.replicate (gap+b) (0:A)
  let Z' := List.replicate (gap+b-1) (0:A)
  have h1 := consume_some get w x hx gap out R v
  have h2 : exec (TM1.step (machine get)) (gap+b+1)
      (state 2 (w,some x) (Z++3::L) (3::R))=
      some (state 3 (w,some x) L (3::Z++3::R)) := by
    simpa [Z] using scan_left (machine get) 2 3 (w,some x) Z L (3::R) rfl (by
      intro a ha
      have hz : a=0 := by exact (List.mem_replicate.mp ha).2
      subst a
      decide)
  have hZ : Z=0::Z' := by
    dsimp [Z,Z']
    have ht : gap+b=(gap+b-1)+1 := by omega
    rw [ht,List.replicate_succ]
    simp only [Nat.add_sub_cancel]
  have h3 : exec (TM1.step (machine get)) 1 (state 3 (w,some x) L (3::Z++3::R))=
      some (state 4 (w,some x) (3::raw x::L) (Z'++3::R)) := by
    simp [state,exec,TM1.step,machine,TM1.stepAux,jump,move,hZ]
  have h4 : exec (TM1.step (machine get)) Z'.length (state 4 (w,some x) (3::raw x::L) (Z'++3::R))=
      some (state 4 (w,some x) (Z'.reverse++3::raw x::L) (3::R)) := by
    apply scan_right
    intro a ha L R
    have hz : a=0 := by exact (List.mem_replicate.mp ha).2
    subst a
    simp [state,TM1.step,machine,TM1.stepAux,jump,move]
  have h5 : exec (TM1.step (machine get)) 1 (state 4 (w,some x) (Z'.reverse++3::raw x::L) (3::R))=
      some (invariant (gap+b-1) (out++[x]) R (w,some x)) := by
    simp [state,invariant,exec,TM1.step,machine,TM1.stepAux,jump,move,Z',L,
      List.reverse_append,List.append_assoc]
  have h1' : exec (TM1.step (machine get)) 1 (invariant gap out (block w++R) v)=
      some (state 2 (w,some x) (Z++3::L) (3::R)) := by
    simpa only [Z,L,List.cons_append,List.append_assoc] using h1
  have he := exec_trans (exec_trans (exec_trans (exec_trans h1' h2) h3) h4) h5
  have ht : 2*(gap+b)+3=1+(gap+b+1)+1+Z'.length+1 := by
    simp only [Z',List.length_replicate]
    omega
  rw [ht]
  exact he

lemma consume_none {b} (get : Word b → Option Bool) (w : Word b)
    (hx : get w=none) (gap : ℕ) (out : List Bool) (v : V b) :
    exec (TM1.step (machine get)) 1 (invariant gap out (block w) v)=
      some (state 5 (w,none) (List.replicate (gap+b+1) 0++3::out.reverse.map raw++[3]) []) := by
  rcases v with ⟨va,vo⟩
  have he : block w=block w++[] := by simp
  rw [he]
  simp only [exec,TM1.step,invariant,state,machine,TM1.stepAux,write₂,List.tail_cons,right₂,
    block,readBlock_spec,fill_all,List.length_finRange,hx,Option.isSome_none,Bool.cond_false,
    jump,Option.bind_some]
  simp only [List.replicate_add,List.replicate_succ,List.append_assoc,
    List.cons_append,zeros_cons]
  congr 3
  simp only [←List.append_assoc,←List.replicate_add,Nat.add_comm]

lemma clear_blanks (l r : ℕ) (w : List A) :
    Tape.mk₂ (List.replicate l (0:A)) (w++List.replicate r 0)=Tape.mk₁ w := by
  have hl : ListBlank.mk (List.replicate l (0:A))=ListBlank.mk ([] : List A) := by
    apply Quotient.sound
    exact Or.inr ⟨l,by simp⟩
  have hr : ListBlank.mk (w++List.replicate r (0:A))=ListBlank.mk w := by
    apply Quotient.sound
    exact Or.inr ⟨r,rfl⟩
  simp only [Tape.mk₂,Tape.mk₁,hl,hr]

lemma finish {b} (get : Word b → Option Bool) (w : Word b)
    (hx : get w=none) (gap : ℕ) (out : List Bool) (v : V b) :
    exec (TM1.step (machine get)) (gap+b+out.length+6) (invariant gap out (block w) v)=
      some ⟨none,(w,none),Tape.mk₁ (out.map raw)⟩ := by
  let L := out.reverse.map raw
  let Z := List.replicate (gap+b+1) (0:A)
  have h1 := consume_none get w hx gap out v
  have h2 : exec (TM1.step (machine get)) (gap+b+2)
      (state 5 (w,none) (Z++3::L++[3]) [])=
      some (state 6 (w,none) (L++[3]) (3::Z)) := by
    simpa [Z,List.append_assoc] using scan_left (machine get) 5 6 (w,none) Z (L++[3]) [] rfl (by
      intro a ha
      have ha' : a=0 := (List.mem_replicate.mp ha).2
      subst a
      decide)
  have h3 : exec (TM1.step (machine get)) 1 (state 6 (w,none) (L++[3]) (3::Z))=
      some (state 7 (w,none) (L++[3]) (0::Z)) := by
    simp [exec,state,TM1.step,machine,TM1.stepAux,jump]
  have h4 : exec (TM1.step (machine get)) (out.length+1)
      (state 7 (w,none) (L++[3]) (0::Z))=
      some (state 8 (w,none) [] (3::L.reverse++0::Z)) := by
    simpa [L] using scan_left (machine get) 7 8 (w,none) L [] (0::Z) rfl (by
      intro a ha
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
      exact raw_ne_three x)
  have h5 : exec (TM1.step (machine get)) 1 (state 8 (w,none) [] (3::L.reverse++0::Z))=
      some ⟨none,(w,none),Tape.mk₁ (out.map raw)⟩ := by
    simp only [exec,TM1.step,state,machine,TM1.stepAux,write₂,List.cons_append,List.tail_cons,
      right₂,Option.bind_some]
    have he : L.reverse++0::Z=out.map raw++List.replicate (gap+b+2) 0 := by
      simp [L,Z,List.replicate_succ]
    rw [he]
    have hc := clear_blanks 1 (gap+b+2) (out.map raw)
    exact congrArg (fun t => some (TM1.Cfg.mk none (w,none) t)) hc
  have h1' : exec (TM1.step (machine get)) 1 (invariant gap out (block w) v)=
      some (state 5 (w,none) (Z++3::L++[3]) []) := h1
  have he := exec_trans (exec_trans (exec_trans (exec_trans h1' h2) h3) h4) h5
  have ht : gap+b+out.length+6=1+(gap+b+2)+1+(out.length+1)+1 := by omega
  rw [ht]
  exact he

/-- Encode a sequence of bits and its terminal block. -/
def stream {b} (code : Bool → Bool → Word b) (stop : Bool → Word b) : Bool → List Bool → List A
  | f,[] => block (stop f)
  | f,x::xs => block (code f x)++stream code stop false xs

/-- Exact recursive step bound for the adapter's scanning loop. -/
def cost (b gap len : ℕ) : ℕ → ℕ
  | 0 => gap+b+len+6
  | n+1 => 2*(gap+b)+3+cost b (gap+b-1) (len+1) n

lemma decode_stream {b} (hb : 1≤b) (get : Word b → Option Bool)
    (code : Bool → Bool → Word b) (stop : Bool → Word b)
    (hc : ∀ f x,get (code f x)=some x) (hs : ∀ f,get (stop f)=none)
    (xs : List Bool) (f : Bool) (gap : ℕ) (out : List Bool) (v : V b) :
    ∃ u : V b, exec (TM1.step (machine get)) (cost b gap out.length xs.length)
      (invariant gap out (stream code stop f xs) v)=
      some ⟨none,u,Tape.mk₁ ((out++xs).map raw)⟩ := by
  induction xs generalizing f gap out v with
  | nil =>
    refine ⟨(stop f,none),?_⟩
    simpa only [stream,List.length_nil,cost,List.append_nil] using finish get (stop f) (hs f)
      gap out v
  | cons x xs ih =>
    obtain ⟨u,hu⟩ := ih false (gap+b-1) (out++[x]) (code f x,some x)
    refine ⟨u,?_⟩
    have he := exec_trans (emit_one hb get (code f x) x (hc f x) gap out
      (stream code stop false xs) v) hu
    simpa only [stream,List.length_cons,cost,List.length_append,List.length_singleton,
      List.length_nil,Nat.zero_add,
      List.append_assoc,List.singleton_append] using he

lemma cost_bound (b gap len n : ℕ) :
    cost b gap len n≤(n+1)*(3*(gap+b*(n+1)+len+n+10)) := by
  induction n generalizing gap len with
  | zero => simp only [cost,Nat.zero_add,Nat.add_zero,Nat.mul_one,Nat.one_mul]; omega
  | succ n ih =>
    rw [cost]
    have hi := ih (gap+b-1) (len+1)
    let H := gap+b*(n+1+1)+len+(n+1)+10
    have hH : gap+b-1+b*(n+1)+(len+1)+n+10≤H := by
      dsimp [H]
      simp only [Nat.mul_add,Nat.mul_one]
      omega
    have hh : 2*(gap+b)+3≤3*H := by
      dsimp [H]
      nlinarith [Nat.zero_le (b*n)]
    calc _ ≤ 2*(gap+b)+3+(n+1)*(3*(gap+b-1+b*(n+1)+(len+1)+n+10)) := Nat.add_le_add_left hi _
         _ ≤ 2*(gap+b)+3+(n+1)*(3*H) := Nat.add_le_add_left (Nat.mul_le_mul_left _
           (Nat.mul_le_mul_left _ hH)) _
         _ ≤ (n+1+1)*(3*H) := by nlinarith only [hh]

lemma start {b} (get : Word b → Option Bool) (R : List A) (v : V b) :
    exec (TM1.step (machine get)) 1 ⟨some 0,v,Tape.mk₁ R⟩=
      some (invariant 0 [] R v) := by
  change exec (TM1.step (machine get)) 1 (state 0 v [] R)=_
  simp [state,invariant,exec,TM1.step,machine,TM1.stepAux,jump,move]

/-- Literal block input to literal digit output; both head position and blank
outside the output are guaranteed, with quadratic bit-time. -/
theorem prepare {b} (hb : 1≤b) (get : Word b → Option Bool)
    (code : Bool → Bool → Word b) (stop : Bool → Word b)
    (hc : ∀ f x,get (code f x)=some x) (hs : ∀ f,get (stop f)=none)
    (xs : List Bool) :
    ∃ t≤(3*b+34)*(xs.length+1)^2, ∃ u : V b,
      exec (TM1.step (machine get)) t (TM1.init (stream code stop true xs))=
        some ⟨none,u,Tape.mk₁ (xs.map raw)⟩ := by
  obtain ⟨u,hu⟩ := decode_stream hb get code stop hc hs xs true 0 [] default
  refine ⟨1+cost b 0 0 xs.length,?_,u,?_⟩
  · have hh := cost_bound b 0 0 xs.length
    simp only [Nat.zero_add,Nat.add_zero] at hh
    nlinarith [Nat.zero_le (b*(xs.length+1)^2)]
  · exact exec_trans (start get _ default) hu

/-- A genuine Fin4 finite TM0 output transducer; the encoding/decoding functions
are fixed finite tables and no unbounded state or oracle is used. -/
theorem finite_output {b} (hb : 1≤b) (get : Word b → Option Bool)
    (code : Bool → Bool → Word b) (stop : Bool → Word b)
    (hc : ∀ f x,get (code f x)=some x) (hs : ∀ f,get (stop f)=none) :
    ∃ (m : ℕ) (G : TM0.Machine A (Fin (m+1))) (C : ℕ), 0<C ∧
      ∀ xs : List Bool, ∃ t≤C*(xs.length+1)^2, ∃ a,
        exec (TM0.step G) t (TM0.init (stream code stop true xs))=some a ∧
        TM0.step G a=none ∧ a.Tape=Tape.mk₁ (xs.map raw) := by
  obtain ⟨m,G,D,hD,hG⟩ := OneToZero.finite_compiler (machine get)
  refine ⟨m,G,D*(3*b+34),by positivity,?_⟩
  intro xs
  obtain ⟨t,ht,u,hu⟩ := prepare hb get code stop hc hs xs
  obtain ⟨v,hv,a,ha,hh,he⟩ := hG _ t _ hu rfl
  refine ⟨v,hv.trans ?_,a,ha,hh,he⟩
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left D ht

end RationalHitting.TMTime.OutputAdapter

namespace RationalHitting.TMTime.StackTape
open Turing

/-- At the boundary of a stack macrostep, the simulator's tape is determined
by the actual stack contents. There is no junk-cell assumption. -/
lemma unique {K Λ σ : Type*} {Γ : K → Type*}
    {a b : TM2.Cfg Γ Λ σ} {c d : TM1.Cfg (TM2to1.Γ' K Γ) (TM2to1.Λ' K Γ Λ σ) σ}
    (h : TM2to1.TrCfg a c) (h' : TM2to1.TrCfg b d) (hs : a.stk=b.stk) : c.Tape=d.Tape := by
  cases h with
  | mk L hL =>
    cases h' with
    | mk L' hL' =>
      have he : L=L' := by
        apply ListBlank.ext
        intro i
        funext k
        have hh := (hL k).trans ((congrArg (fun S => ListBlank.mk ((S k).map some).reverse)
          hs).trans (hL' k).symm)
        have hh' := congrArg (fun T => T.nth i) hh
        simpa only [ListBlank.nth_map,proj,PointedMap.mk_val] using hh'
      rw [he]

lemma clean {K Λ σ : Type*} [DecidableEq K] [Inhabited Λ] [Inhabited σ]
    (k : K) (w : List Bool)
    {c : TM1.Cfg (TM2to1.Γ' K (fun _ => Bool)) (TM2to1.Λ' K (fun _ => Bool) Λ σ) σ}
    (h : TM2to1.TrCfg
      (⟨none,default,Function.update (fun _ => []) k w⟩ : TM2.Cfg (fun _ : K => Bool) Λ σ) c) :
    c.Tape=Tape.mk₁ (TM2to1.trInit k w) := by
  exact unique h (TM2to1.trCfg_init (Γ:=fun _ => Bool) (Λ:=Λ) (σ:=σ) k w) rfl

end RationalHitting.TMTime.StackTape

namespace RationalHitting.TMTime.OutputAdapter
open Turing

lemma blockVector {b} (v : List.Vector Bool b) :
    block v.get=v.toList.map bit := by
  have he : List.ofFn v.get=v.toList := by
    rw [←List.Vector.toList_ofFn,List.Vector.ofFn_get]
  rw [block,←List.ofFn_eq_map]
  change List.ofFn (bit ∘ v.get)=_
  rw [←List.map_ofFn,he]

variable {K : Type} [DecidableEq K]
/-- The tape alphabet encoding a marked family of Boolean stacks. -/
abbrev StackAlphabet (K : Type) := TM2to1.Γ' K (fun _ => Bool)
/-- Encode a stack cell holding one bit in the selected register. -/
def code {b} (k : K) (enc : StackAlphabet K → List.Vector Bool b) (f x : Bool) : Word b :=
  (enc (f,Function.update (fun _ => none) k (some x))).get
/-- Encode a terminal cell with all stacks empty. -/
def stop {b} (enc : StackAlphabet K → List.Vector Bool b) (f : Bool) : Word b :=
  (enc (f,fun _ => none)).get

/-- Decode the selected stack's bit from a fixed-width encoded block. -/
def getter {b} (k : K) (dec : List.Vector Bool b → StackAlphabet K) (w : Word b) : Option Bool :=
  (dec (List.Vector.ofFn w)).2 k

lemma getter_code {b} (k : K) (enc : StackAlphabet K → List.Vector Bool b)
    (dec : List.Vector Bool b → StackAlphabet K) (hd : ∀ a,dec (enc a)=a) (f x : Bool) :
    getter k dec (code k enc f x)=some x := by
  unfold getter code
  rw [List.Vector.ofFn_get]
  exact (congrArg (fun a : StackAlphabet K => a.2 k) (hd (f,Function.update (fun _ => none) k
    (some x)))).trans (Function.update_self k (some x) (fun _ => none))

lemma getter_stop {K : Type}  {b : ℕ} (k : K)
  (enc : RationalHitting.TMTime.OutputAdapter.StackAlphabet K → List.Vector Bool b)
  (dec : List.Vector Bool b → RationalHitting.TMTime.OutputAdapter.StackAlphabet K)
  (hd : ∀ (a : RationalHitting.TMTime.OutputAdapter.StackAlphabet K), dec (enc a) = a)
  (f : Bool) :
  RationalHitting.TMTime.OutputAdapter.getter k dec
      (RationalHitting.TMTime.OutputAdapter.stop enc f) =
    none := by
  unfold getter stop
  rw [List.Vector.ofFn_get]
  exact congrArg (fun a : StackAlphabet K => a.2 k) (hd (f,fun _ => none))

lemma stream_false {b} (k : K) (enc : StackAlphabet K → List.Vector Bool b) (xs : List Bool) :
    stream (code k enc) (stop enc) false xs=
      (xs.flatMap (fun x => (enc (false,Function.update (fun _ => none) k (some
        x))).toList)).map bit ++
      block (stop enc false) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [stream,code,blockVector,List.flatMap_cons,List.map_append,List.append_assoc,ih]

lemma stream_encoding {b} (k : K) (enc : StackAlphabet K → List.Vector Bool b)
    (h0 : enc default=List.Vector.replicate b false) (xs : List Bool) :
    Tape.mk₁ (stream (code k enc) (stop enc) true xs)=
      Tape.mk₁ (((TM2to1.trInit k xs.reverse).flatMap (fun z => (enc z).toList)).map bit) := by
  cases xs with
  | nil =>
    change Tape.mk₁ (block (enc (true,fun _ => none)).get)=_
    rw [blockVector]
    have he : TM2to1.trInit (Γ:=fun _ : K => Bool) k ([] : List Bool)=[(true,fun _ => none)] := rfl
    rw [List.reverse_nil,he]
    change Tape.mk₁ ((enc (true,fun _ => none)).toList.map bit)=
      Tape.mk₁ (((enc (true,fun _ => none)).toList++[]).map bit)
    rw [List.append_nil]
  | cons x xs =>
    have he := InputAdapter.stack_encoding k b enc (x::xs).reverse (by simp)
    simp only [List.reverse_reverse] at he
    have ht : stream (code k enc) (stop enc) true (x::xs)=
        (InputAdapter.emit (fun f x => (enc (f,Function.update (fun _ => none) k (some x))).toList)
          true (x::xs)).map bit ++ List.replicate b 0 := by
      rw [stream,stream_false]
      simp only [code,blockVector,InputAdapter.emit,InputAdapter.emit_false,List.map_append,
        List.append_assoc]
      have hh : block (stop enc false)=List.replicate b 0 := by
        change block (enc default).get=_
        rw [blockVector,h0]
        change (List.replicate b false).map bit=List.replicate b 0
        exact List.map_replicate
      rw [hh]
    rw [ht,he]
    exact clear_blanks 0 b _

lemma width_pos {K : Type}  {b : ℕ}
  (enc : RationalHitting.TMTime.OutputAdapter.StackAlphabet K → List.Vector Bool b)
  (dec : List.Vector Bool b → RationalHitting.TMTime.OutputAdapter.StackAlphabet K)
  (hd : ∀ (a : RationalHitting.TMTime.OutputAdapter.StackAlphabet K), dec (enc a) = a) : 1 ≤ b := by
  by_contra hb
  have hb' : b=0 := by omega
  subst b
  have hh : enc default=enc (true,fun _ => none) := Subsingleton.elim _ _
  have he : (default : StackAlphabet K)=(true,fun _ => none) :=
    (hd _).symm.trans ((congrArg dec hh).trans (hd _))
  have hf := congrArg Prod.fst he
  exact Bool.false_ne_true hf

/-- Exact inverse interface for a clean output stack, including the bottom
marker, right-side blank padding and output order. -/
theorem raw_stack_output {b} (k : K) (enc : StackAlphabet K → List.Vector Bool b)
    (dec : List.Vector Bool b → StackAlphabet K) (h0 : enc default=List.Vector.replicate b false)
    (hd : ∀ a,dec (enc a)=a) :
    ∃ (m : ℕ) (G : TM0.Machine A (Fin (m+1))) (C : ℕ), 0<C ∧
      ∀ xs : List Bool, ∃ t≤C*(xs.length+1)^2, ∃ a,
        exec (TM0.step G) t (TM0.init
          (((TM2to1.trInit k xs.reverse).flatMap (fun z => (enc z).toList)).map bit))=some a ∧
        TM0.step G a=none ∧ a.Tape=Tape.mk₁ (xs.map raw) := by
  obtain ⟨m,G,C,hC,hG⟩ := finite_output (width_pos enc dec hd) (getter k dec) (code k enc) (stop
    enc)
    (getter_code k enc dec hd) (getter_stop k enc dec hd)
  refine ⟨m,G,C,hC,?_⟩
  intro xs
  obtain ⟨t,ht,a,ha,hh,he⟩ := hG xs
  refine ⟨t,ht,a,?_,hh,he⟩
  have hi : TM0.init (stream (code k enc) (stop enc) true xs)=
      (TM0.init (((TM2to1.trInit k xs.reverse).flatMap (fun z => (enc z).toList)).map bit) :
        TM0.Cfg A (Fin (m+1))) := by
    exact congrArg (TM0.Cfg.mk default) (stream_encoding k enc h0 xs)
  rwa [hi] at ha

end RationalHitting.TMTime.OutputAdapter

/- Literal tape-preserving linkage for the raw-input/stack/output compiler.
There is no implicit recoding between machines. -/

end Complexity
