/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.FiniteCompiler

/-!
# Rational hitting lists: input adapter

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/InputAdapter.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.TMTime.InputAdapter
open Turing
/-- The fixed four-symbol alphabet of the tape adapter. -/
abbrev A := Fin 4
/-- The ten control states used by the tape adapter. -/
abbrev Q := Fin 10
/-- Finite auxiliary storage used by the tape adapter. -/
abbrev V := Bool × Bool
/-- A configuration of the tape adapter. -/
abbrev Cfg := TM1.Cfg A Q V
/-- A tape-adapter instruction with finite auxiliary storage. -/
abbrev Stmt := TM1.Stmt A Q V

/-- Encode a literal output or input bit by a nonblank tape symbol. -/
def raw (b : Bool) : A := if b then 2 else 1
/-- Encode a bit inside the compiler's binary tape representation. -/
def bit (b : Bool) : A := if b then 1 else 0

/-- Jump to the specified adapter control state. -/
def jump (q : Q) : Stmt := .goto (fun _ _ => q)
/-- Move the tape head and jump to the specified state. -/
def move (d : Dir) (q : Q) : Stmt := .move d (jump q)
/-- Move left and branch according to whether the delimiter was reached. -/
def leftTo (q r : Q) : Stmt :=
  .move .left (.branch (fun a _ => a==3) (jump r) (jump q))

/-- Write a finite encoded block before continuing with the next instruction. -/
def writeBits : List Bool → Stmt → Stmt
  | [],q => q
  | b::bs,q => .write (fun _ _ => bit b) (.move .right (writeBits bs q))

/-- The fixed finite control map of the tape adapter. -/
def machine (code : Bool → Bool → List Bool) : Q → Stmt
  | 0 => .branch (fun a _ => a==0)
      (.write (fun _ _ => 3) (.move .right (.write (fun _ _ => 3)
        (.move .right (.write (fun _ _ => 3) (.move .left (.move .left
          (.load (fun _ _ => (true,false)) (jump 1))))))))) (move .right 0)
  | 1 => .write (fun _ _ => 0) (.move .left
      (.branch (fun a _ => a==0) (jump 6)
        (.load (fun a v => (v.1,a==2)) (.write (fun _ _ => 3) (move .right 2)))))
  | 2 => .branch (fun a _ => a==3) (move .right 3) (move .right 2)
  | 3 => .branch (fun a _ => a==3)
      (.branch (fun _ v => v.1)
        (.branch (fun _ v => v.2)
          (writeBits (code true true) (.write (fun _ _ => 3) (.load (fun _ v => (false,v.2))
            (jump 4))))
          (writeBits (code true false) (.write (fun _ _ => 3) (.load (fun _ v => (false,v.2))
            (jump 4)))))
        (.branch (fun _ v => v.2)
          (writeBits (code false true) (.write (fun _ _ => 3) (.load (fun _ v => (false,v.2))
            (jump 4))))
          (writeBits (code false false) (.write (fun _ _ => 3) (.load (fun _ v => (false,v.2))
            (jump 4))))))
      (move .right 3)
  | 4 => leftTo 4 5
  | 5 => leftTo 5 1
  | 6 => .branch (fun a _ => a==3) (move .right 7) (move .right 6)
  | 7 => .branch (fun a _ => a==3) (.write (fun _ _ => 0) (jump 8)) (move .right 7)
  | 8 => leftTo 8 9
  | _ => .write (fun _ _ => 0) (.move .right .halt)

@[simp] lemma head₂ (L R : List A) : (Tape.mk₂ L R).head=R.headI := rfl
@[simp] lemma right₂ (L : List A) (a : A) (R : List A) :
    (Tape.mk₂ L (a::R)).move .right=Tape.mk₂ (a::L) R := by simp [Tape.mk₂]
lemma left₂ (a : A) (L R : List A) :
    (Tape.mk₂ (a::L) R).move .left=Tape.mk₂ L (a::R) := by simp [Tape.mk₂]

attribute [local simp] left₂

@[simp] lemma write₂ (L R : List A) (a : A) :
    (Tape.mk₂ L R).write a=Tape.mk₂ L (a::R.tail) := by simp [Tape.mk₂]

lemma stepAux_writeBits (bs : List Bool) (q : Stmt) (v : V) (L R : List A) :
    TM1.stepAux (writeBits bs q) v (Tape.mk₂ L R)=
      TM1.stepAux q v (Tape.mk₂ ((bs.map bit).reverse++L) (R.drop bs.length)) := by
  induction bs generalizing L R with
  | nil => simp [writeBits]
  | cons b bs ih =>
    simp only [writeBits,TM1.stepAux,write₂,right₂,ih,List.map_cons,List.reverse_cons,
      List.append_assoc,List.singleton_append,List.length_cons]
    have hd : R.tail.drop bs.length = R.drop (bs.length+1) := by
      rw [←List.drop_one,List.drop_drop]
      simp [Nat.add_comm]
    rw [hd]

lemma scan_right (F : Q → Stmt) (q : Q) (v : V) (l L R : List A)
    (h : ∀ a∈l, ∀ L R, TM1.step F (⟨some q,v,Tape.mk₂ L (a::R)⟩ : Cfg)=
      some ⟨some q,v,Tape.mk₂ (a::L) R⟩) :
    exec (TM1.step F) l.length (⟨some q,v,Tape.mk₂ L (l++R)⟩ : Cfg)=
      some ⟨some q,v,Tape.mk₂ (l.reverse++L) R⟩ := by
  induction l generalizing L R with
  | nil => simp []
  | cons a l ih =>
    have hs := h a (by simp) L (l++R)
    simp only [List.cons_append,List.length_cons,exec,hs,Option.bind_some]
    simpa [List.reverse_cons,List.append_assoc] using ih (a::L) R (fun b hb => h b (by simp [hb]))

lemma scan_left (F : Q → Stmt) (q r : Q) (v : V) (l L R : List A)
    (hF : F q=leftTo q r) (hl : ∀ a∈l, a≠3) :
    exec (TM1.step F) (l.length+1) (⟨some q,v,Tape.mk₂ (l++3::L) R⟩ : Cfg)=
      some ⟨some r,v,Tape.mk₂ L (3::l.reverse++R)⟩ := by
  induction l generalizing R with
  | nil =>
    simp [exec,TM1.step,hF,leftTo,jump,TM1.stepAux,Tape.mk₂]
  | cons a l ih =>
    have ha := hl a (by simp)
    have hh := ih (a::R) (fun b hb => hl b (by simp [hb]))
    have hs : TM1.step F (⟨some q,v,Tape.mk₂ ((a::l)++3::L) R⟩ : Cfg)=
        some ⟨some q,v,Tape.mk₂ (l++3::L) (a::R)⟩ := by
      simp [TM1.step,hF,leftTo,TM1.stepAux,beq_eq_false_iff_ne.mpr ha,jump]
    change (TM1.step F _).bind (exec (TM1.step F) (l.length+1)) = _
    rw [hs,Option.bind_some]
    simpa [List.reverse_cons,List.append_assoc] using hh

@[simp] lemma bit_ne_three (b : Bool) : bit b ≠ 3 := by cases b <;> decide
@[simp] lemma raw_ne_zero (b : Bool) : raw b ≠ 0 := by cases b <;> decide

/-- Assemble a configuration from the control state and the two tape halves. -/
def state (q : Q) (f b : Bool) (L R : List A) : Cfg := ⟨some q,(f,b),Tape.mk₂ L R⟩

/-- The tape layout preserved by the adapter's main scanning loop. -/
def invariant (xs : List Bool) (k : ℕ) (out : List Bool) (f b : Bool) : Cfg :=
  state 1 f b (xs.map raw) (3::List.replicate k 0 ++ 3::out.map bit ++ [3])

lemma process (code : Bool → Bool → List Bool) (x f b : Bool) (xs out : List Bool) (k : ℕ) :
    exec (TM1.step (machine code)) (2*k+2*out.length+(code f x).length+7)
      (invariant (x::xs) k out f b)=
      some (invariant xs (k+1) (out++code f x) false x) := by
  let X := xs.map raw
  let O := out.map bit
  let Z := List.replicate (k+1) (0:A)
  let c := code f x
  let C := c.map bit
  have h1 : exec (TM1.step (machine code)) 1 (invariant (x::xs) k out f b)=
      some (state 2 f x (3::X) (Z++3::O++[3])) := by
    cases x <;> simp [exec,TM1.step,TM1.stepAux,machine,invariant,state,raw,jump,move,X,O,Z,
      List.replicate_succ]
  have h2 : exec (TM1.step (machine code)) Z.length (state 2 f x (3::X) (Z++3::O++[3]))=
      some (state 2 f x (Z.reverse++3::X) (3::O++[3])) := by
    simp only [state,List.append_assoc,List.cons_append]
    apply scan_right
    intro a ha L R
    have ha0 : a=0 := by simpa [Z] using ha
    subst a
    simp [TM1.step,TM1.stepAux,machine,jump,move]
  have h3 : exec (TM1.step (machine code)) 1 (state 2 f x (Z.reverse++3::X) (3::O++[3]))=
      some (state 3 f x (3::Z.reverse++3::X) (O++[3])) := by
    simp [exec,state,TM1.step,TM1.stepAux,machine,jump,move]
  have h4 : exec (TM1.step (machine code)) O.length (state 3 f x (3::Z.reverse++3::X) (O++[3]))=
      some (state 3 f x (O.reverse++3::Z.reverse++3::X) [3]) := by
    simp only [state,List.append_assoc,List.cons_append]
    apply scan_right
    intro a ha L R
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp ha
    simp [TM1.step,TM1.stepAux,machine,jump,move,beq_eq_false_iff_ne.mpr (bit_ne_three y)]
  have h5 : exec (TM1.step (machine code)) 1 (state 3 f x (O.reverse++3::Z.reverse++3::X) [3])=
      some (state 4 false x (C.reverse++O.reverse++3::Z.reverse++3::X) [3]) := by
    cases f <;> cases x <;>
      simp [exec,state,TM1.step,machine,TM1.stepAux,stepAux_writeBits,write₂,head₂,jump,
        List.append_assoc,C,c]
  have h6 : exec (TM1.step (machine code)) ((O++C).length+1)
      (state 4 false x (C.reverse++O.reverse++3::Z.reverse++3::X) [3])=
      some (state 5 false x (Z.reverse++3::X) (3::(O++C)++[3])) := by
    have hn : ∀ a ∈ (O++C).reverse, a≠3 := by
      intro a ha
      rcases List.mem_append.mp (List.mem_reverse.mp ha) with ho|hc
      · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp ho
        exact bit_ne_three y
      · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hc
        exact bit_ne_three y
    simpa only [state,List.reverse_reverse,List.reverse_append,List.append_assoc,List.cons_append,
      List.length_reverse,List.length_append,Nat.add_comm] using
      scan_left (machine code) 4 5 (false,x) (O++C).reverse (Z.reverse++3::X) [3] rfl hn
  have h7 : exec (TM1.step (machine code)) (Z.length+1)
      (state 5 false x (Z.reverse++3::X) (3::(O++C)++[3]))=
      some (invariant xs (k+1) (out++code f x) false x) := by
    have hn : ∀ a∈Z.reverse, a≠3 := by
      intro a ha
      have ha0 : a=0 := by simpa [Z] using ha
      subst a
      decide
    have hh := scan_left (machine code) 5 1 (false,x) Z.reverse X (3::(O++C)++[3]) rfl hn
    dsimp [state,invariant,X,Z,O,C,c] at hh ⊢
    simp only [List.reverse_replicate,List.map_append] at hh ⊢
    simp only [List.cons_append,List.append_assoc] at hh ⊢
    exact hh
  have he := exec_trans (exec_trans (exec_trans (exec_trans (exec_trans
    (exec_trans h1 h2) h3) h4) h5) h6) h7
  have ht : 2*k+2*out.length+(code f x).length+7 =
      1+Z.length+1+O.length+1+((O++C).length+1)+(Z.length+1) := by
    simp [Z,O,C,c,List.length_append]
    omega
  rw [ht]
  exact he

/-- Encode all literal input bits, using a distinguished first-block marker. -/
def emit (code : Bool → Bool → List Bool) : Bool → List Bool → List Bool
  | _,[] => []
  | f,x::xs => code f x ++ emit code false xs

/-- Exact recursive step bound for the adapter's scanning loop. -/
def cost (code : Bool → Bool → List Bool) : Bool → List Bool → ℕ → ℕ → ℕ
  | _,[],_,_ => 0
  | f,x::xs,k,L => 2*k+2*L+(code f x).length+7 +
      cost code false xs (k+1) (L+(code f x).length)

lemma all_process (code : Bool → Bool → List Bool) (xs out : List Bool) (k : ℕ) (f b : Bool) :
    ∃ f' b', exec (TM1.step (machine code)) (cost code f xs k out.length)
      (invariant xs k out f b)=
      some (invariant [] (k+xs.length) (out++emit code f xs) f' b') := by
  induction xs generalizing out k f b with
  | nil => exact ⟨f,b,by simp [cost,emit]⟩
  | cons x xs ih =>
    obtain ⟨f',b',hh⟩ := ih (out++code f x) (k+1) false x
    refine ⟨f',b',?_⟩
    have he := exec_trans (process code x f b xs out k) hh
    simpa [cost,emit,List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using he

lemma emit_length (code : Bool → Bool → List Bool) (B : ℕ)
    (hb : ∀ f x, (code f x).length≤B) (f : Bool) (xs : List Bool) :
    (emit code f xs).length≤B*xs.length := by
  induction xs generalizing f with
  | nil => simp [emit]
  | cons x xs ih =>
    simp only [emit,List.length_append,List.length_cons]
    have hh := ih false
    have hc := hb f x
    nlinarith

lemma cost_bound (code : Bool → Bool → List Bool) (B : ℕ)
    (hb : ∀ f x, (code f x).length≤B) (f : Bool) (xs : List Bool) (k L : ℕ) :
    cost code f xs k L ≤ xs.length*(2*(k+xs.length)+2*(L+B*xs.length)+B+7) := by
  induction xs generalizing f k L with
  | nil => simp [cost]
  | cons x xs ih =>
    have hh := ih false (k+1) (L+(code f x).length)
    have hc := hb f x
    simp only [cost,List.length_cons]
    calc
      _ ≤ 2*k+2*L+(code f x).length+7 +
          xs.length*(2*((k+1)+xs.length)+2*((L+(code f x).length)+B*xs.length)+B+7) :=
        Nat.add_le_add_left hh _
      _ ≤ 2*(k+(xs.length+1))+2*(L+B*(xs.length+1))+B+7 +
          xs.length*(2*(k+(xs.length+1))+2*(L+B*(xs.length+1))+B+7) := by
        apply Nat.add_le_add
        · nlinarith
        · apply Nat.mul_le_mul_left
          nlinarith
      _ = _ := by ring

@[simp] lemma left_empty (R : List A) :
    (Tape.mk₂ [] R).move .left = Tape.mk₂ [] (0::R) := by simp [Tape.mk₂]

lemma clear_blanks (O : List A) (k : ℕ) :
    Tape.mk₂ (List.replicate k (0:A)) (O++[0])=Tape.mk₁ O := by
  unfold Tape.mk₂ Tape.mk₁
  have hL : ListBlank.mk (List.replicate k (0:A))=ListBlank.mk [] :=
    Quotient.sound (Or.inr ⟨k,by simp⟩)
  have hR : ListBlank.mk (O++[(0:A)])=ListBlank.mk O :=
    Quotient.sound (Or.inr ⟨1,by rfl⟩)
  rw [hL,hR]
  rfl

lemma scan_six_zero (code : Bool → Bool → List Bool) (f b : Bool) (L R : List A) :
    TM1.step (machine code) (state 6 f b L (0::R))=some (state 6 f b (0::L) R) := by
  simp [state,TM1.step,TM1.stepAux,machine,jump,move]

lemma enter_finish (code : Bool → Bool → List Bool) (out : List Bool) (k : ℕ) (f b : Bool) :
    exec (TM1.step (machine code)) 1 (invariant [] k out f b)=
      some (state 6 f b [] (List.replicate (k+2) 0++3::out.map bit++[3])) := by
  simp [exec,invariant,state,TM1.step,machine,TM1.stepAux,left_empty,jump,List.replicate_succ]

lemma finish (code : Bool → Bool → List Bool) (out : List Bool) (k : ℕ) (f b : Bool) :
    exec (TM1.step (machine code)) (k+2*out.length+7) (invariant [] k out f b)=
      some ⟨none,(f,b),Tape.mk₁ (out.map bit)⟩ := by
  let O := out.map bit
  let Z := List.replicate (k+2) (0:A)
  have h1 : exec (TM1.step (machine code)) 1 (invariant [] k out f b)=
      some (state 6 f b [] (Z++3::O++[3])) := by
    simpa only [Z,O] using enter_finish code out k f b
  have h2 : exec (TM1.step (machine code)) Z.length (state 6 f b [] (Z++3::O++[3]))=
      some (state 6 f b Z.reverse (3::O++[3])) := by
    have hh := scan_right (machine code) 6 (f,b) Z [] (3::O++[3]) (by
      intro a ha L R
      have ha0 : a=0 := by simpa [Z] using ha
      subst a
      exact scan_six_zero code f b L R)
    dsimp [state] at hh ⊢
    simpa only [List.append_nil,List.append_assoc,List.cons_append] using hh

  have h3 : exec (TM1.step (machine code)) 1 (state 6 f b Z.reverse (3::O++[3]))=
      some (state 7 f b (3::Z.reverse) (O++[3])) := by
    simp [exec,state,TM1.step,TM1.stepAux,machine,jump,move]
  have h4 : exec (TM1.step (machine code)) O.length (state 7 f b (3::Z.reverse) (O++[3]))=
      some (state 7 f b (O.reverse++3::Z.reverse) [3]) := by
    apply scan_right
    intro a ha L R
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp ha
    simp [TM1.step,TM1.stepAux,machine,jump,move,beq_eq_false_iff_ne.mpr (bit_ne_three y)]
  have h5 : exec (TM1.step (machine code)) 1 (state 7 f b (O.reverse++3::Z.reverse) [3])=
      some (state 8 f b (O.reverse++3::Z.reverse) [0]) := by
    simp [exec,state,TM1.step,TM1.stepAux,machine,jump]
  have h6 : exec (TM1.step (machine code)) (O.length+1)
      (state 8 f b (O.reverse++3::Z.reverse) [0])=
      some (state 9 f b Z.reverse (3::O++[0])) := by
    simpa [state,List.reverse_reverse] using
      scan_left (machine code) 8 9 (f,b) O.reverse Z.reverse [0] rfl (by
        intro a ha
        obtain ⟨y,hy,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
        exact bit_ne_three y)
  have h7 : exec (TM1.step (machine code)) 1 (state 9 f b Z.reverse (3::O++[0]))=
      some (⟨none,(f,b),Tape.mk₁ O⟩ : Cfg) := by
    have hc : Tape.mk₂ (0::Z.reverse) (O++[0])=Tape.mk₁ O := by
      have hz : Z.reverse=List.replicate (k+2) (0:A) := by simp only [Z,List.reverse_replicate]
      rw [hz,←List.replicate_succ]
      exact clear_blanks O (k+3)
    simp [exec,state,TM1.step,TM1.stepAux,machine,hc]
  have he := exec_trans (exec_trans (exec_trans (exec_trans (exec_trans
    (exec_trans h1 h2) h3) h4) h5) h6) h7
  have ht : k+2*out.length+7 = 1+Z.length+1+O.length+1+(O.length+1)+1 := by
    simp [Z,O]
    omega
  rw [ht]
  exact he

lemma scan_zero_raw (code : Bool → Bool → List Bool) (x : Bool) (v : V) (L R : List A) :
    TM1.step (machine code) (⟨some 0,v,Tape.mk₂ L (raw x::R)⟩ : Cfg)=
      some ⟨some 0,v,Tape.mk₂ (raw x::L) R⟩ := by
  simp [TM1.step,TM1.stepAux,machine,jump,move,beq_eq_false_iff_ne.mpr (raw_ne_zero x)]

lemma start_markers (code : Bool → Bool → List Bool) (w : List Bool) (v : V) :
    exec (TM1.step (machine code)) 1 (⟨some 0,v,Tape.mk₂ (w.map raw) []⟩ : Cfg)=
      some (invariant w 0 [] true false) := by
  simp [exec,TM1.step,machine,TM1.stepAux,jump,state,invariant,Tape.mk₂]

lemma start (code : Bool → Bool → List Bool) (w : List Bool) (v : V) :
    exec (TM1.step (machine code)) (w.length+1) (⟨some 0,v,Tape.mk₁ (w.map raw)⟩ : Cfg)=
      some (invariant w.reverse 0 [] true false) := by
  have hh := scan_right (machine code) 0 v (w.map raw) [] [] (by
    intro a ha L R
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    exact scan_zero_raw code x v L R)
  have hs : exec (TM1.step (machine code)) w.length (⟨some 0,v,Tape.mk₁ (w.map raw)⟩ : Cfg)=
      some ⟨some 0,v,Tape.mk₂ (w.reverse.map raw) []⟩ := by
    simpa [Tape.mk₁,List.map_reverse] using hh
  exact exec_trans hs (start_markers code w.reverse v)

/-- Literal Fin4 raw input is physically erased; no hidden encoded-input
precondition is used. The macrotransition charge is quadratic; TM1 compilation
adds a fixed multiplicative constant for this one fixed adapter machine. -/
theorem prepare (code : Bool → Bool → List Bool) (B : ℕ)
    (hb : ∀ f x, (code f x).length≤B) (w : List Bool) (v : V) :
    ∃ t ≤ (4*B+12)*(w.length+1)^2, ∃ v',
      exec (TM1.step (machine code)) t (⟨some 0,v,Tape.mk₁ (w.map raw)⟩ : Cfg)=
        some ⟨none,v',Tape.mk₁ ((emit code true w.reverse).map bit)⟩ := by
  obtain ⟨f,b,hh⟩ := all_process code w.reverse [] 0 true false
  simp only [Nat.zero_add,List.nil_append,List.length_nil,List.length_reverse] at hh
  have hf := finish code (emit code true w.reverse) w.length f b
  have he := exec_trans (exec_trans (start code w v) hh) hf
  refine ⟨_,?_,(f,b),he⟩
  have ht := cost_bound code B hb true w.reverse 0 0
  have hl := emit_length code B hb true w.reverse
  simp only [List.length_reverse,Nat.zero_add] at ht hl
  calc
    _ ≤ (w.length+1)+w.length*(2*w.length+2*(B*w.length)+B+7)+
        (w.length+2*(B*w.length)+7) := by omega
    _ ≤ (4*B+12)*(w.length+1)^2 := by
      nlinarith [Nat.zero_le (B*w.length*w.length),Nat.zero_le (B*w.length),
        Nat.zero_le (w.length*w.length)]

end RationalHitting.TMTime.InputAdapter

namespace RationalHitting.TMTime.InputAdapter
open Turing

lemma emit_false (code : Bool → Bool → List Bool) (xs : List Bool) :
    emit code false xs=xs.flatMap (code false) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [emit,ih]

lemma stack_encoding {K : Type} [DecidableEq K] (k : K) (b : ℕ)
    (enc : TM2to1.Γ' K (fun _ => Bool) → List.Vector Bool b)
    (w : List Bool) (hw : w≠[]) :
    emit (fun f x => (enc (f,Function.update (fun _ => none) k (some x))).toList) true w.reverse=
      (TM2to1.trInit k w).flatMap (fun a => (enc a).toList) := by
  cases he : w.reverse with
  | nil => simp only [List.reverse_eq_nil_iff] at he; exact False.elim (hw he)
  | cons x xs =>
    unfold TM2to1.trInit
    rw [he]
    change (enc (true,Function.update (fun _ => none) k (some x))).toList ++
      emit (fun f x => (enc (f,Function.update (fun _ => none) k (some x))).toList) false xs =
      (enc (true,Function.update (fun _ => none) k (some x))).toList ++
        ((xs.map (fun a => (false,Function.update (fun _ => none) k (some a)))).flatMap
          (fun a => (enc a).toList))
    rw [emit_false]
    exact congrArg (fun l => (enc (true,Function.update (fun _ => none) k (some x))).toList ++ l)
      (List.flatMap_map (fun a => (false,Function.update (fun _ => none) k (some a)))
        (fun a => (enc a).toList) xs).symm


/-- Real finite TM0 raw-input adapter, at quadratic bit cost, reaching exactly
Mathlib's initial tape for the binary stack simulator, not an assumed encoding. -/
theorem raw_stack_input {K : Type} [DecidableEq K] (k : K) (b : ℕ)
    (enc : TM2to1.Γ' K (fun _ => Bool) → List.Vector Bool b) :
    ∃ (m : ℕ) (G : TM0.Machine A (Fin (m+1))) (C : ℕ), 0<C ∧
      ∀ w : List Bool, w≠[] → ∃ t≤C*(w.length+1)^2, ∃ a : TM0.Cfg A (Fin (m+1)),
        exec (TM0.step G) t (TM0.init (w.map raw))=some a ∧ TM0.step G a=none ∧
        a.Tape=Tape.mk₁ (((TM2to1.trInit k w).flatMap (fun z => (enc z).toList)).map bit) := by
  let code := fun f x => (enc (f,Function.update (fun _ => none) k (some x))).toList
  obtain ⟨m,G,D,hD,hG⟩ := OneToZero.finite_compiler (machine code)
  refine ⟨m,G,D*(4*b+12),by positivity,?_⟩
  intro w hw
  obtain ⟨t,ht,v,hx⟩ := prepare code b (by intro f x; simp [code]) w default
  obtain ⟨u,hu,a,ha,hh,he⟩ := hG (w.map raw) t _ hx (by rfl)
  refine ⟨u,hu.trans ?_,a,ha,hh,?_⟩
  · simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left D ht
  · simpa only [TM1.Cfg.Tape,code,stack_encoding k b enc w hw] using he

end RationalHitting.TMTime.InputAdapter

/- Required reverse interface from a block-coded finite stack simulator to
literal Fin4 output digits. All registers of this transducer are finite. -/

end Complexity
