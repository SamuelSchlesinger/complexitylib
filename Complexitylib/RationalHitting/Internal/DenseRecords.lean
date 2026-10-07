/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.BinomialBounds

/-!
# Rational hitting lists: dense records

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/DenseRecords.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open Function

/-- Self-delimiting word records (distinct from the final output encoding). -/
def codeWord : List Bool → List Bool
  | [] => [true]
  | b::w => false::b::codeWord w

@[simp] theorem codeWord_length (w : List Bool) : (codeWord w).length = 2*w.length+1 := by
  induction w <;> simp_all [codeWord] ; omega

/-- Escape each data bit by prefixing it with a false marker. -/
def pairWord (w : List Bool) : List Bool := w.flatMap (fun b => [false,b])
@[simp] lemma pairWord_nil : pairWord [] = [] := rfl
@[simp] lemma pairWord_cons (b : Bool) (w : List Bool) :
    pairWord (b::w) = false::b::pairWord w := rfl
@[simp] lemma pairWord_append (u v : List Bool) : pairWord (u++v) = pairWord u++pairWord v := by
  simp [pairWord]
lemma codeWord_pair (w : List Bool) : codeWord w = pairWord w++[true] := by
  induction w <;> simp_all [codeWord]

/-- Move and escape the bits of one record. -/
def packLoop (a b : Fin 3) : Program (Fin 3) :=
  .loop a (.seq (.transfer a b) (.push b false))

lemma eval_packLoop (a b : Fin 3) (hab : a ≠ b) (s : Store (Fin 3)) :
    Eval (packLoop a b) s (update (update s a []) b (pairWord (s a).reverse++s b))
      (4*(s a).length+1) := by
  generalize he : s a = w
  induction w generalizing s with
  | nil =>
    have hh : update (update s a []) b (s b) = s := by
      funext k; by_cases hka : k=a <;> by_cases hkb : k=b <;> simp_all
    simpa [packLoop,he,hh] using
      (Eval.whileNil (p := Program.seq (.transfer a b) (.push b false)) he)
  | cons x w ih =>
    let u := update (update s a w) b (x::s b)
    let v := update u b (false::x::s b)
    have h1 : Eval (Program.transfer a b) s u 1 := by
      simpa [u,transfer_cons hab s x w he] using Eval.transfer a b s
    have h2 : Eval (Program.push b false) u v 1 := by simpa [u,v] using Eval.push b false u
    have h3 := ih v (by simp [v,u,hab])
    have hh := Eval.whileCons (by simp [he]) (Eval.seq h1 h2) h3
    have heq : update (update v a []) b (pairWord w.reverse++v b) =
        update (update s a []) b (pairWord (x::w).reverse++s b) := by
      funext k; by_cases hka : k=a <;> by_cases hkb : k=b <;>
        simp_all [v,u,List.reverse_cons,List.append_assoc]
    rw [heq] at hh
    convert hh using 1 <;> simp [packLoop] ; omega

/-- Consume a binary word, prepending one encoded reversed record. -/
def packRecord : Program (Fin 3) := .seq (.push 1 true) (packLoop 0 1)

lemma eval_packRecord (s : Store (Fin 3)) :
    Eval packRecord s (update (update s 0 []) 1 (codeWord (s 0).reverse++s 1))
      (4*(s 0).length+3) := by
  have h1 := Eval.push (1 : Fin 3) true s
  have h2 := eval_packLoop 0 1 (by decide) (update s 1 (true::s 1))
  have hh := Eval.seq h1 h2
  have heq : update (update (update s 1 (true::s 1)) 0 []) 1
      (pairWord (s 0).reverse++true::s 1) =
      update (update s 0 []) 1 (codeWord (s 0).reverse++s 1) := by
    funext k; by_cases h0 : k=0 <;> by_cases h1 : k=1 <;>
      simp_all [codeWord_pair,List.append_assoc]
  simp only [update_of_ne (by decide : (0 : Fin 3) ≠ 1),update_self,heq] at hh
  convert hh using 1 <;> simp [packRecord] ; omega

/-- Read one escaped data bit or consume the record terminator. -/
def unpackBody : Program (Fin 3) :=
  .branch 0 (.drop 2) (.seq (.drop 0) (.transfer 0 1)) (.seq (.drop 0) (.drop 2))

lemma eval_unpackLoop (w tail : List Bool) (s : Store (Fin 3))
    (h0 : s 0 = codeWord w++tail) (h2 : s 2 = [true]) :
    Eval (Program.loop 2 unpackBody) s
      (update (update (update s 0 tail) 1 (w.reverse++s 1)) 2 []) (5*w.length+6) := by
  induction w generalizing s with
  | nil =>
    let u := update s 0 tail
    let v := update u 2 []
    have h01 : s 0 = true::tail := by simpa [codeWord] using h0
    have hd0 : Eval (Program.drop 0) s u 1 := by simpa [u,h01] using Eval.drop (0 : Fin 3) s
    have hd2 : Eval (Program.drop 2) u v 1 := by simpa [v,u,h2] using Eval.drop (2 : Fin 3) u
    have hb : Eval unpackBody s v 4 := Eval.branchTrue h01 (Eval.seq hd0 hd2)
    have hnil := Eval.whileNil (p:=unpackBody) (by simp [v] : v 2 = [])
    have hh := Eval.whileCons (by simp [h2]) hb hnil
    have heq : v = update (update (update s 0 tail) 1 (([] : List Bool).reverse++s 1)) 2 [] := by
      funext k; fin_cases k <;> simp [v,u]
    simpa [heq] using hh
  | cons b w ih =>
    let u := update s 0 (b::codeWord w++tail)
    let v := update (update u 0 (codeWord w++tail)) 1 (b::s 1)
    have h01 : s 0 = false::b::codeWord w++tail := by simpa [codeWord] using h0
    have hd : Eval (Program.drop 0) s u 1 := by simpa [u,h01] using Eval.drop (0 : Fin 3) s
    have ht : Eval (Program.transfer 0 1) u v 1 := by
      have ht := Eval.transfer (0 : Fin 3) 1 u
      rw [transfer_cons (by decide : (0 : Fin 3) ≠ 1) u b (codeWord w++tail) (by simp [u])] at ht
      simpa [v,u] using ht
    have hb : Eval unpackBody s v 4 := Eval.branchFalse h01 (Eval.seq hd ht)
    have hi := ih v (by simp [v]) (by simp [v,u,h2])
    have hh := Eval.whileCons (by simp [h2]) hb hi
    have heq : update (update (update v 0 tail) 1 (w.reverse++v 1)) 2 [] =
        update (update (update s 0 tail) 1 ((b::w).reverse++s 1)) 2 [] := by
      funext k; fin_cases k <;> simp [v,u,List.reverse_cons,List.append_assoc]
    rw [heq] at hh
    convert hh using 1 ; simp ; omega

/-- Remove one self-delimiting record; produce its reversed binary word. -/
def unpackRecord : Program (Fin 3) := .seq (.push 2 true) (.loop 2 unpackBody)

lemma eval_unpackRecord (w tail : List Bool) (s : Store (Fin 3))
    (h0 : s 0 = codeWord w++tail) (h2 : s 2 = []) :
    Eval unpackRecord s
      (update (update (update s 0 tail) 1 (w.reverse++s 1)) 2 []) (5*w.length+8) := by
  have h1 := Eval.push (2 : Fin 3) true s
  have h2' := eval_unpackLoop w tail (update s 2 [true]) (by simp [h0]) (by simp)
  have hh := Eval.seq h1 (by simpa [h2] using h2')
  have heq : update (update (update (update s 2 [true]) 0 tail) 1 (w.reverse++s 1)) 2 [] =
      update (update (update s 0 tail) 1 (w.reverse++s 1)) 2 [] := by
    funext k; fin_cases k <;> simp
  simp only [heq] at hh
  convert hh using 1 <;> simp [unpackRecord] ; omega

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function

/-- Dense serialized arrays of variable-width binary records. -/
def codeArray (ws : List (List Bool)) : List Bool := ws.flatMap codeWord
@[simp] lemma codeArray_nil : codeArray [] = [] := rfl
@[simp] lemma codeArray_cons (w : List Bool) (ws : List (List Bool)) :
    codeArray (w::ws) = codeWord w++codeArray ws := rfl
@[simp] lemma codeArray_append (u v : List (List Bool)) :
    codeArray (u++v) = codeArray u++codeArray v := by simp [codeArray]

lemma codeArray_nonempty (w : List Bool) (ws : List (List Bool)) : codeArray (w::ws) ≠ [] := by
  have := codeWord_length w
  intro h
  have hl := congrArg List.length h
  simp only [codeArray_cons,List.length_append,List.length_nil] at hl
  omega

/-- Register embedding for the unpacking stage of a record move. -/
def unpackMove : Fin 3 ↪ Fin 4 := ⟨![0,2,3],by decide⟩
/-- Register embedding for the packing stage of a record move. -/
def packMove : Fin 3 ↪ Fin 4 := ⟨![2,1,3],by decide⟩
/-- Move one delimited record between stacks. -/
def recordMove : Program (Fin 4) :=
  .seq (unpackRecord.rename unpackMove) (packRecord.rename packMove)

lemma eval_recordMove (w tail : List Bool) (s : Store (Fin 4))
    (h0 : s 0 = codeWord w++tail) (h2 : s 2 = []) (h3 : s 3 = []) :
    Eval recordMove s (update (update s 0 tail) 1 (codeWord w++s 1)) (9*w.length+12) := by
  have h1 := eval_rename_from unpackMove unpackMove.injective s
    (eval_unpackRecord w tail (fun k => s (unpackMove k)) h0 h3)
  let u := update (update (update s 0 tail) 2 w.reverse) 3 []
  have hu : Eval (unpackRecord.rename unpackMove) s u (5*w.length+8) := by
    simp only [extend_update_store unpackMove unpackMove.injective,
      extend_pull_store unpackMove unpackMove.injective] at h1
    simpa [unpackMove,u,h2] using h1
  have h2' := eval_rename_from packMove packMove.injective u
    (eval_packRecord (fun k => u (packMove k)))
  have hv : Eval (packRecord.rename packMove) u
      (update (update s 0 tail) 1 (codeWord w++s 1)) (4*w.length+3) := by
    simp only [extend_update_store packMove packMove.injective,
      extend_pull_store packMove packMove.injective] at h2'
    have heq : extend packMove
        (update (update (fun k => u (packMove k)) 0 []) 1
          (codeWord (u (packMove 0)).reverse++u (packMove 1))) u =
        update (update s 0 tail) 1 (codeWord w++s 1) := by
      simp only [extend_update_store packMove packMove.injective,
        extend_pull_store packMove packMove.injective]
      funext k; fin_cases k <;> simp [u,packMove,h2,h3]
    -- Frame every register not allocated to the three-register packer.
    have hv' : update (update u (packMove 0) []) (packMove 1)
        (codeWord (u (packMove 0)).reverse++u (packMove 1)) =
        update (update s 0 tail) 1 (codeWord w++s 1) := by
      funext k; fin_cases k <;> simp [u,packMove,h2,h3]
    rw [hv'] at h2'
    simpa [u,packMove] using h2'
  have hh := Eval.seq hu hv
  convert hh using 1 <;> first | rfl | omega

lemma eval_recordMove_rename {K : Type} [DecidableEq K] (f : Fin 4 ↪ K)
    (w tail : List Bool) (s : Store K)
    (h0 : s (f 0) = codeWord w++tail) (h2 : s (f 2) = []) (h3 : s (f 3) = []) :
    Eval (recordMove.rename f) s
      (update (update s (f 0) tail) (f 1) (codeWord w++s (f 1))) (9*w.length+12) := by
  have hh := eval_rename_from f f.injective s
    (eval_recordMove w tail (fun k => s (f k)) h0 h2 h3)
  simpa only [extend_update_store f f.injective,extend_pull_store f f.injective] using hh

/-- Register embedding for moving records forward during a scan. -/
def arrayForward : Fin 4 ↪ Fin 8 := ⟨![0,1,2,3],by decide⟩
/-- Register embedding for restoring records after a scan. -/
def arrayBackward : Fin 4 ↪ Fin 8 := ⟨![1,0,2,3],by decide⟩
/-- Move one record and decrement the unary scan counter. -/
def scanBody : Program (Fin 8) := .seq (recordMove.rename arrayForward) (.drop 4)
/-- Scan the specified number of records using a unary counter. -/
def scan : Program (Fin 8) := .loop 4 scanBody

/-- Number of real finite-stack macrosteps for scanning a given prefix. -/
def scanCost (ws : List (List Bool)) : ℕ :=
  (ws.map (fun w => 9*w.length+15)).sum+1

lemma eval_scan (pre : List (List Bool)) (tail : List Bool) (s : Store (Fin 8))
    (h0 : s 0 = codeArray pre++tail) (h4 : s 4 = List.replicate pre.length true)
    (h2 : s 2 = []) (h3 : s 3 = []) :
    Eval scan s (update (update (update s 0 tail) 1 (codeArray pre.reverse++s 1)) 4 [])
      (scanCost pre) := by
  induction pre generalizing s with
  | nil =>
    have hs : update (update (update s 0 tail) 1 (codeArray ([] : List (List Bool)).reverse++s
      1)) 4 [] = s := by
      funext k; by_cases h0k : k=0 <;> by_cases h1k : k=1 <;> by_cases h4k : k=4 <;>
        simp_all
    simp only [List.reverse_nil,codeArray_nil,List.nil_append] at hs
    simpa [scan,scanCost,h4,hs] using (Eval.whileNil (p:=scanBody) (by simpa using h4))
  | cons w pre ih =>
    let u := update (update s 0 (codeArray pre++tail)) 1 (codeWord w++s 1)
    let v := update u 4 (List.replicate pre.length true)
    have hm : Eval (recordMove.rename arrayForward) s u (9*w.length+12) := by
      simpa [u,arrayForward] using eval_recordMove_rename arrayForward w (codeArray pre++tail) s
        (by simpa [arrayForward,List.append_assoc] using h0) h2 h3
    have hd : Eval (Program.drop 4) u v 1 := by simpa [u,v,h4] using Eval.drop (4 : Fin 8) u
    have hi := ih v (by simp [v,u]) (by simp [v]) (by simp [v,u,h2]) (by simp [v,u,h3])
    have hh := Eval.whileCons (by simp [h4]) (Eval.seq hm hd) hi
    have heq : update (update (update v 0 tail) 1 (codeArray pre.reverse++v 1)) 4 [] =
        update (update (update s 0 tail) 1 (codeArray (w::pre).reverse++s 1)) 4 [] := by
      funext k; by_cases h0k : k=0 <;> by_cases h1k : k=1 <;> by_cases h4k : k=4 <;>
        simp_all [v,u,List.reverse_cons,List.append_assoc]
    rw [heq] at hh
    convert hh using 1 <;> simp [scan,scanCost,scanBody] ; omega

lemma scanCost_bound (ws : List (List Bool)) :
    scanCost ws ≤ 15*(codeArray ws).length+1 := by
  induction ws with
  | nil => simp [scanCost]
  | cons w ws ih =>
    simp only [scanCost,List.map_cons,List.sum_cons,codeArray_cons,
      List.length_append,
        codeWord_length] at *; nlinarith

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function

/-- Restore all scanned records to the original stack. -/
def restore : Program (Fin 8) := .loop 1 (recordMove.rename arrayBackward)
/-- Stack-step count for restoring the given list of records. -/
def restoreCost (ws : List (List Bool)) : ℕ :=
  (ws.map (fun w => 9*w.length+13)).sum+1

lemma eval_restore (ws : List (List Bool)) (s : Store (Fin 8))
    (h1 : s 1 = codeArray ws) (h2 : s 2 = []) (h3 : s 3 = []) :
    Eval restore s (update (update s 1 []) 0 (codeArray ws.reverse++s 0)) (restoreCost ws) := by
  induction ws generalizing s with
  | nil =>
    have hs : update (update s 1 []) 0 (s 0) = s := by
      funext k; by_cases h0k : k=0 <;> by_cases h1k : k=1 <;> simp_all
    simpa [restore,restoreCost,h1,hs] using
      (Eval.whileNil (p:=recordMove.rename arrayBackward) (by simpa using h1))
  | cons w ws ih =>
    let u := update (update s 1 (codeArray ws)) 0 (codeWord w++s 0)
    have hm : Eval (recordMove.rename arrayBackward) s u (9*w.length+12) := by
      simpa [u,arrayBackward] using eval_recordMove_rename arrayBackward w (codeArray ws) s h1 h2 h3
    have hi := ih u (by simp [u]) (by simp [u,h2]) (by simp [u,h3])
    have hh := Eval.whileCons (by rw [h1]; exact codeArray_nonempty w ws) hm hi
    have heq : update (update u 1 []) 0 (codeArray ws.reverse++u 0) =
        update (update s 1 []) 0 (codeArray (w::ws).reverse++s 0) := by
      funext k; by_cases h0k : k=0 <;> by_cases h1k : k=1 <;>
        simp_all [u,List.reverse_cons,List.append_assoc]
    rw [heq] at hh
    convert hh using 1 <;> simp [restore,restoreCost] ; omega

lemma restoreCost_bound (ws : List (List Bool)) :
    restoreCost ws ≤ 13*(codeArray ws).length+1 := by
  induction ws with
  | nil => simp [restoreCost]
  | cons w ws ih =>
    simp only [restoreCost,List.map_cons,List.sum_cons,codeArray_cons,
      List.length_append,
        codeWord_length] at *; nlinarith

@[simp] lemma codeArray_reverse_length (ws : List (List Bool)) :
    (codeArray ws.reverse).length = (codeArray ws).length := by
  simp [codeArray,List.length_flatMap]

/-- Register embedding for unpacking a record without consuming it permanently. -/
def peekUnpack : Fin 3 ↪ Fin 8 := ⟨![0,2,3],by decide⟩
/-- Register embedding for restoring a peeked record. -/
def peekPack : Fin 3 ↪ Fin 8 := ⟨![2,0,3],by decide⟩
/-- Copy the next record while restoring its original representation. -/
def peekRecord : Program (Fin 8) :=
  .seq (unpackRecord.rename peekUnpack) (.seq (copy 2 6 7)
    (.seq (packRecord.rename peekPack) (reverse 6 5)))

lemma eval_peekRecord (w tail : List Bool) (s : Store (Fin 8))
    (h0 : s 0 = codeWord w++tail) (h2 : s 2 = []) (h3 : s 3 = [])
    (h5 : s 5 = []) (h6 : s 6 = []) (h7 : s 7 = []) :
    Eval peekRecord s (update s 5 w) (18*w.length+22) := by
  let u := update (update (update s 0 tail) 2 w.reverse) 3 []
  let v := update (update u 6 w.reverse) 7 []
  let z := update (update v 2 []) 0 (codeWord w++tail)
  have h1 := eval_rename_from peekUnpack peekUnpack.injective s
    (eval_unpackRecord w tail (fun k => s (peekUnpack k)) h0 h3)
  have hu : Eval (unpackRecord.rename peekUnpack) s u (5*w.length+8) := by
    simp only [extend_update_store peekUnpack peekUnpack.injective,
      extend_pull_store peekUnpack peekUnpack.injective] at h1
    simpa [peekUnpack,u,h2] using h1
  have hv : Eval (copy 2 6 7) u v (7*w.length+7) := by
    simpa [v,u,h6,h7] using eval_copy (a := (2 : Fin 8)) (b := 6) (tmp := 7)
      (by decide) (by decide) (by decide) u
  have h3' := eval_rename_from peekPack peekPack.injective v
    (eval_packRecord (fun k => v (peekPack k)))
  have hz : Eval (packRecord.rename peekPack) v z (4*w.length+3) := by
    simp only [extend_update_store peekPack peekPack.injective,
      extend_pull_store peekPack peekPack.injective] at h3'
    simpa [peekPack,z,v,u] using h3'
  have h4 := eval_reverse (a := (6 : Fin 8)) (b := 5) (by decide) z
  have hfinal : update (update z 6 []) 5 ((z 6).reverse++z 5) = update s 5 w := by
    funext k; fin_cases k <;> simp [z,v,u,h0,h2,h3,h5,h6,h7]
  rw [hfinal] at h4
  have hh := Eval.seq hu (Eval.seq hv (Eval.seq hz h4))
  convert hh using 1 <;> simp [peekRecord,z,v,u] ; omega

/-- Indexed read. Register 4 is a unary index; register 0 is a serialized
array and is restored byte-for-byte. Register 5 receives the exact binary word. -/
def arrayRead : Program (Fin 8) := .seq scan (.seq peekRecord restore)

theorem eval_arrayRead (pre post : List (List Bool)) (w : List Bool) (s : Store (Fin 8))
    (h0 : s 0 = codeArray (pre++w::post)) (h1 : s 1 = [])
    (h2 : s 2 = []) (h3 : s 3 = []) (h4 : s 4 = List.replicate pre.length true)
    (h5 : s 5 = []) (h6 : s 6 = []) (h7 : s 7 = []) :
    ∃ t ≤ 50*(s 0).length+30,
      Eval arrayRead s (update (update s 4 []) 5 w) t := by
  let tail := codeArray (w::post)
  let u := update (update (update s 0 tail) 1 (codeArray pre.reverse)) 4 []
  let v := update u 5 w
  have hu : Eval scan s u (scanCost pre) := by
    simpa [u,h1] using eval_scan pre tail s (by simpa [tail] using h0) h4 h2 h3
  have hv : Eval peekRecord u v (18*w.length+22) := by
    apply eval_peekRecord w (codeArray post) u <;> simp [u,tail,h2,h3,h5,h6,h7]
  have hz := eval_restore pre.reverse v (by simp [v,u]) (by simp [v,u,h2]) (by simp [v,u,h3])
  have hfinal : update (update v 1 []) 0 (codeArray pre.reverse.reverse++v 0) =
      update (update s 4 []) 5 w := by
    funext k; fin_cases k <;> simp [v,u,tail,h0,h1]
  rw [hfinal] at hz
  have hh := Eval.seq hu (Eval.seq hv hz)
  refine ⟨_,?_,hh⟩
  have hs := scanCost_bound pre
  have hr := restoreCost_bound pre.reverse
  simp only [codeArray_reverse_length] at hr
  rw [h0]
  simp only [codeArray_append,codeArray_cons,List.length_append,codeWord_length]
  omega

end RationalHitting.StackLanguage

end Complexity
