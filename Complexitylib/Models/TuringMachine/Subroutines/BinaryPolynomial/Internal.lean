/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Asymptotics
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryAddConst
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryMulAdd
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryPolynomial.Defs

/-!
# Canonical binary evaluation of a fixed natural polynomial — proof internals

Each Horner layer is verified compositionally from multiply-add,
fixed-constant addition, and clearing. The list proof alternates accumulator
roles and carries a common polynomial value cap; consequently all layers fit
one width-based space budget independent of their (potentially much larger)
running time.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Canonical parked tape encoding of a natural for polynomial evaluation. -/
def binaryPolynomialNatTape (value : ℕ) : Tape :=
  (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right

private theorem binaryPolynomialNatTape_hasBinaryNat (value : ℕ) :
    (binaryPolynomialNatTape value).HasBinaryNat value :=
  Tape.init_move_right_hasBinaryNat value

private theorem binaryPolynomialHasBinaryNat_parked {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : Parked t := by
  refine ⟨by rw [h.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start h.2.2

private theorem binaryPolynomialNatTape_parked (value : ℕ) :
    Parked (binaryPolynomialNatTape value) :=
  binaryPolynomialHasBinaryNat_parked
    (binaryPolynomialNatTape_hasBinaryNat value)

/-- Predicate fixing the tapes framing a binary polynomial evaluation. -/
abbrev binaryPolynomialFramePred
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape) : TapePred n :=
  fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀

/-- Literal work frame after one Horner layer. -/
private def binaryHornerLayerWork (work : Fin n → Tape)
    (sourceIdx targetIdx : Fin n) (inputValue accValue coeff : ℕ) :
    Fin n → Tape :=
  Function.update
    (Function.update work targetIdx
      (binaryPolynomialNatTape (accValue * inputValue + coeff)))
    sourceIdx (binaryPolynomialNatTape 0)

/-- Literal work frame after a list of alternating Horner layers. -/
private def binaryHornerWork (work : Fin n → Tape)
    (sourceIdx targetIdx : Fin n) (inputValue : ℕ) :
    List ℕ → ℕ → Fin n → Tape
  | [], _ => work
  | coeff :: coeffs, accValue =>
      binaryHornerWork
        (binaryHornerLayerWork work sourceIdx targetIdx inputValue accValue
          coeff)
        targetIdx sourceIdx inputValue coeffs
        (accValue * inputValue + coeff)

private theorem swapBinaryMulAddDistinct
    {leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n}
    (h : BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx) :
    BinaryMulAddDistinct accIdx rightIdx leftIdx mulCounterIdx addCounterIdx :=
  { left_ne_right := Ne.symm h.right_ne_acc
    left_ne_acc := Ne.symm h.left_ne_acc
    left_ne_mulCounter := h.acc_ne_mulCounter
    left_ne_addCounter := h.acc_ne_addCounter
    right_ne_acc := Ne.symm h.left_ne_right
    right_ne_mulCounter := h.right_ne_mulCounter
    right_ne_addCounter := h.right_ne_addCounter
    acc_ne_mulCounter := h.left_ne_mulCounter
    acc_ne_addCounter := h.left_ne_addCounter
    mulCounter_ne_addCounter := h.mulCounter_ne_addCounter }

private theorem resultSourceDistinct
    {inputIdx resultIdx scratchIdx mulCounterIdx addCounterIdx : Fin n}
    (h : BinaryPolynomialDistinct inputIdx resultIdx scratchIdx mulCounterIdx
      addCounterIdx) :
    BinaryMulAddDistinct resultIdx inputIdx scratchIdx mulCounterIdx
      addCounterIdx :=
  { left_ne_right := Ne.symm h.input_ne_result
    left_ne_acc := h.result_ne_scratch
    left_ne_mulCounter := h.result_ne_mulCounter
    left_ne_addCounter := h.result_ne_addCounter
    right_ne_acc := h.input_ne_scratch
    right_ne_mulCounter := h.input_ne_mulCounter
    right_ne_addCounter := h.input_ne_addCounter
    acc_ne_mulCounter := h.scratch_ne_mulCounter
    acc_ne_addCounter := h.scratch_ne_addCounter
    mulCounter_ne_addCounter := h.mulCounter_ne_addCounter }

private theorem scratchSourceDistinct
    {inputIdx resultIdx scratchIdx mulCounterIdx addCounterIdx : Fin n}
    (h : BinaryPolynomialDistinct inputIdx resultIdx scratchIdx mulCounterIdx
      addCounterIdx) :
    BinaryMulAddDistinct scratchIdx inputIdx resultIdx mulCounterIdx
      addCounterIdx :=
  swapBinaryMulAddDistinct (resultSourceDistinct h)

private theorem binaryHornerLayerWork_parked
    (work : Fin n → Tape) (sourceIdx targetIdx : Fin n)
    (inputValue accValue coeff : ℕ) (hwork : ∀ i, Parked (work i)) :
    ∀ i, Parked
      (binaryHornerLayerWork work sourceIdx targetIdx inputValue accValue
        coeff i) := by
  intro i
  by_cases his : i = sourceIdx
  · subst i
    simp [binaryHornerLayerWork]
    exact binaryPolynomialNatTape_parked 0
  · by_cases hit : i = targetIdx
    · subst i
      simp [binaryHornerLayerWork, his]
      exact binaryPolynomialNatTape_parked
        (accValue * inputValue + coeff)
    · simp [binaryHornerLayerWork, his, hit]
      exact hwork i

private theorem updatedWork_heads_le
    (work : Fin n → Tape) (idx : Fin n) (value initialSpace : ℕ)
    (hbase : ∀ i, (work i).head ≤ initialSpace)
    (hone : 1 ≤ initialSpace) :
    ∀ i, (Function.update work idx (binaryPolynomialNatTape value) i).head ≤
      initialSpace := by
  intro i
  by_cases hi : i = idx
  · subst i
    rw [Function.update_self,
      (binaryPolynomialNatTape_hasBinaryNat value).2.1]
    exact hone
  · rw [Function.update_of_ne hi]
    exact hbase i

private theorem binaryHornerLayerWork_heads_le
    (work : Fin n → Tape) (sourceIdx targetIdx : Fin n)
    (inputValue accValue coeff initialSpace : ℕ)
    (hbase : ∀ i, (work i).head ≤ initialSpace)
    (hone : 1 ≤ initialSpace) :
    ∀ i, (binaryHornerLayerWork work sourceIdx targetIdx inputValue
      accValue coeff i).head ≤ initialSpace := by
  exact updatedWork_heads_le _ sourceIdx 0 initialSpace
    (updatedWork_heads_le work targetIdx (accValue * inputValue + coeff)
      initialSpace hbase hone)
    hone

private theorem binaryPolynomialFrame_transition
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hout : Parked out₀) :
    ∀ inp work out, binaryPolynomialFramePred inp₀ work₀ out₀ inp work out →
      binaryPolynomialFramePred inp₀ work₀ out₀
        (transitionInput inp) (fun i => transitionTape (work i))
        (transitionTape out) := by
  rintro _ _ _ ⟨rfl, rfl, rfl⟩
  refine ⟨hinp.transitionInput_eq_self, ?_, hout.transitionTape_eq_self⟩
  funext i
  exact (hwork i).transitionTape_eq_self

private theorem binaryHornerLayerTM_hoareTimeSpace
    (inputIdx sourceIdx targetIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct sourceIdx inputIdx targetIdx
      mulCounterIdx addCounterIdx)
    (inputValue accValue coeff inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : (work₀ inputIdx).HasBinaryNat inputValue)
    (hsource : (work₀ sourceIdx).HasBinaryNat accValue)
    (htarget : (work₀ targetIdx).HasBinaryNat 0)
    (hmulCounter : (work₀ mulCounterIdx).HasBinaryNat 0)
    (haddCounter : (work₀ addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (binaryHornerLayerTM inputIdx sourceIdx targetIdx mulCounterIdx
      addCounterIdx coeff).HoareTimeSpace
        (binaryPolynomialFramePred inp₀ work₀ out₀)
        (binaryPolynomialFramePred inp₀
          (binaryHornerLayerWork work₀ sourceIdx targetIdx inputValue
            accValue coeff) out₀)
        (binaryHornerLayerTime inputValue accValue coeff) inputLength
        (binaryHornerLayerSpace initialSpace inputValue accValue coeff) := by
  let mulWork := Function.update work₀ targetIdx
    (binaryPolynomialNatTape (accValue * inputValue))
  let addWork := Function.update work₀ targetIdx
    (binaryPolynomialNatTape (accValue * inputValue + coeff))
  have hone : 1 ≤ initialSpace := by
    rw [← hsource.2.1]
    exact hworkSpace sourceIdx
  have hmul := binaryMulAddIntoTM_hoareTimeSpace_frame sourceIdx inputIdx
    targetIdx mulCounterIdx addCounterIdx hdistinct accValue inputValue 0
    inputLength initialSpace inp₀ work₀ out₀ hsource hinput htarget
    hmulCounter haddCounter hinp (fun i _ _ _ _ _ => hwork i) hout
    hworkSpace hinputSpace
  have hmul' :
      (binaryMulAddIntoTM sourceIdx inputIdx targetIdx mulCounterIdx
        addCounterIdx).HoareTimeSpace
          (binaryPolynomialFramePred inp₀ work₀ out₀)
          (binaryPolynomialFramePred inp₀ mulWork out₀)
          (binaryMulAddTime accValue inputValue 0) inputLength
          (binaryMulAddSpace initialSpace accValue inputValue 0) := by
    simpa [mulWork, binaryPolynomialNatTape] using hmul
  have hmulWorkParked : ∀ i, Parked (mulWork i) := by
    intro i
    by_cases hi : i = targetIdx
    · subst i
      simp [mulWork]
      exact binaryPolynomialNatTape_parked _
    · simpa [mulWork, hi] using hwork i
  have hmulWorkSpace : ∀ i, (mulWork i).head ≤ initialSpace :=
    updatedWork_heads_le work₀ targetIdx (accValue * inputValue)
      initialSpace hworkSpace hone
  have hconst := binaryAddConstTM_hoareTimeSpace_frame targetIdx coeff
    (accValue * inputValue) inputLength initialSpace inp₀ mulWork out₀
    (by
      simp [mulWork]
      exact binaryPolynomialNatTape_hasBinaryNat _)
    hinp (fun i _ => hmulWorkParked i) hout hmulWorkSpace hinputSpace
  have hconst' : (binaryAddConstTM targetIdx coeff).HoareTimeSpace
      (binaryPolynomialFramePred inp₀ mulWork out₀)
      (binaryPolynomialFramePred inp₀ addWork out₀)
      (binaryAddConstTime coeff (accValue * inputValue)) inputLength
      (binaryAddConstSpace initialSpace coeff
        (accValue * inputValue)) := by
    simpa [mulWork, addWork, binaryPolynomialNatTape] using hconst
  have haddWorkParked : ∀ i, Parked (addWork i) := by
    intro i
    by_cases hi : i = targetIdx
    · subst i
      simp [addWork]
      exact binaryPolynomialNatTape_parked _
    · simpa [addWork, hi] using hwork i
  have haddWorkSpace : ∀ i, (addWork i).head ≤ initialSpace :=
    updatedWork_heads_le work₀ targetIdx
      (accValue * inputValue + coeff) initialSpace hworkSpace hone
  have hsourceAt : (addWork sourceIdx).HasBinaryNat accValue := by
    simpa [addWork, hdistinct.left_ne_acc] using hsource
  have hclearInitial :
      ({ state := (clearWorkTM sourceIdx).qstart
         input := inp₀
         work := addWork
         output := out₀ } : Cfg n (clearWorkTM sourceIdx).Q).WithinAuxSpace
        inputLength initialSpace :=
    ⟨haddWorkSpace, hinputSpace⟩
  have hclear := clearWorkTM_hoareTimeSpace_frame sourceIdx accValue.bits
    inputLength initialSpace inp₀ addWork out₀
    (by simpa [binaryPolynomialNatTape] using hsourceAt.eq_init_move_right)
    hinp (fun i _ => haddWorkParked i) hout hclearInitial
  have hclear' : (clearWorkTM sourceIdx).HoareTimeSpace
      (binaryPolynomialFramePred inp₀ addWork out₀)
      (binaryPolynomialFramePred inp₀
        (binaryHornerLayerWork work₀ sourceIdx targetIdx inputValue
          accValue coeff) out₀)
      (clearWorkTimeBound accValue.size) inputLength
      (initialSpace + clearWorkTimeBound accValue.size) := by
    refine hclear.consequence (fun _ _ _ h => h) (fun inp work out h => ?_)
      (by simp [Nat.size_eq_bits_len]) le_rfl
      (by simp [Nat.size_eq_bits_len])
    refine ⟨h.1, h.2.1.trans ?_, h.2.2⟩
    simp [addWork, binaryHornerLayerWork, binaryPolynomialNatTape] at h ⊢
  have hmulConst := seqTM_hoareTimeSpace
    (binaryMulAddIntoTM sourceIdx inputIdx targetIdx mulCounterIdx
      addCounterIdx)
    (binaryAddConstTM targetIdx coeff) hmul'
    (binaryPolynomialFrame_transition inp₀ mulWork out₀ hinp hmulWorkParked
      hout)
    hconst'
  have hrun := seqTM_hoareTimeSpace
    (seqTM
      (binaryMulAddIntoTM sourceIdx inputIdx targetIdx mulCounterIdx
        addCounterIdx)
      (binaryAddConstTM targetIdx coeff))
    (clearWorkTM sourceIdx) hmulConst
    (binaryPolynomialFrame_transition inp₀ addWork out₀ hinp haddWorkParked
      hout)
    hclear'
  simpa [binaryHornerLayerTM, binaryHornerLayerTime,
    binaryHornerLayerSpace, max_assoc] using hrun

theorem binaryPolynomialCoeffs_length_internal (p : Polynomial ℕ) :
    (binaryPolynomialCoeffs p).length = p.natDegree + 1 := by
  simp [binaryPolynomialCoeffs]

theorem binaryPolynomialCoeffs_ne_nil_internal (p : Polynomial ℕ) :
    binaryPolynomialCoeffs p ≠ [] := by
  intro h
  have := congrArg List.length h
  simp [binaryPolynomialCoeffs] at this

theorem binaryHornerFold_nil_internal (x acc : ℕ) :
    binaryHornerFold x [] acc = acc := rfl

theorem binaryHornerFold_cons_internal
    (x coeff acc : ℕ) (coeffs : List ℕ) :
    binaryHornerFold x (coeff :: coeffs) acc =
      binaryHornerFold x coeffs (acc * x + coeff) := rfl

private theorem binaryHornerFold_reverse_range (f : ℕ → ℕ) (x : ℕ) :
    ∀ (k acc : ℕ),
      binaryHornerFold x ((List.range k).map f).reverse acc =
        acc * x ^ k + ∑ i ∈ Finset.range k, f i * x ^ i := by
  intro k
  induction k with
  | zero => intro acc; simp [binaryHornerFold_nil_internal]
  | succ k ih =>
      intro acc
      rw [List.range_succ, List.map_append, List.reverse_append]
      simp only [List.map_cons, List.map_nil, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.singleton_append]
      rw [binaryHornerFold_cons_internal, ih, Finset.sum_range_succ]
      ring

theorem binaryHornerFold_polyCoeffs_internal
    (p : Polynomial ℕ) (x : ℕ) :
    binaryHornerFold x (binaryPolynomialCoeffs p) 0 = p.eval x := by
  rw [binaryPolynomialCoeffs, binaryHornerFold_reverse_range,
    Polynomial.eval_eq_sum_range]
  simp

private theorem binaryHornerFold_le (x : ℕ) :
    ∀ (coeffs : List ℕ) (acc : ℕ),
      binaryHornerFold x coeffs acc ≤
        (acc + coeffs.sum) * (x + 1) ^ coeffs.length := by
  intro coeffs
  induction coeffs with
  | nil => intro acc; simp [binaryHornerFold_nil_internal]
  | cons coeff coeffs ih =>
      intro acc
      rw [binaryHornerFold_cons_internal]
      refine le_trans (ih (acc * x + coeff)) ?_
      rw [List.sum_cons, List.length_cons, pow_succ]
      have hstep : acc * x + coeff + coeffs.sum ≤
          (acc + (coeff + coeffs.sum)) * (x + 1) := by
        have hexp : (acc + (coeff + coeffs.sum)) * (x + 1) =
            acc * x + acc +
              ((coeff + coeffs.sum) * x + (coeff + coeffs.sum)) := by
          ring
        omega
      calc
        (acc * x + coeff + coeffs.sum) * (x + 1) ^ coeffs.length ≤
            ((acc + (coeff + coeffs.sum)) * (x + 1)) *
              (x + 1) ^ coeffs.length :=
          Nat.mul_le_mul_right _ hstep
        _ = (acc + (coeff + coeffs.sum)) *
              ((x + 1) ^ coeffs.length * (x + 1)) := by ring

theorem binaryPolynomial_eval_le_valueCap_internal
    (p : Polynomial ℕ) (x : ℕ) :
    p.eval x ≤ binaryPolynomialValueCap p x := by
  rw [← binaryHornerFold_polyCoeffs_internal]
  unfold binaryPolynomialValueCap
  have h := binaryHornerFold_le x (binaryPolynomialCoeffs p) 0
  exact le_trans h (Nat.mul_le_mul_right _ (by omega))

private theorem binaryHornerFold_take_le
    (x : ℕ) (coeffs : List ℕ) (k : ℕ) :
    binaryHornerFold x (coeffs.take k) 0 ≤
      (coeffs.sum + 1) * (x + 1) ^ coeffs.length := by
  refine le_trans (binaryHornerFold_le x _ 0) ?_
  have hsum : (coeffs.take k).sum ≤ coeffs.sum := by
    conv_rhs => rw [← List.take_append_drop k coeffs]
    rw [List.sum_append]
    omega
  have hpow : (x + 1) ^ (coeffs.take k).length ≤
      (x + 1) ^ coeffs.length :=
    Nat.pow_le_pow_right (by omega) (by rw [List.length_take]; omega)
  exact Nat.mul_le_mul (by omega) hpow

private theorem binaryPolynomial_input_le_cap
    (p : Polynomial ℕ) (inputValue : ℕ) :
    inputValue ≤ binaryPolynomialValueCap p inputValue := by
  have hlen : 0 < (binaryPolynomialCoeffs p).length := by
    rw [binaryPolynomialCoeffs_length_internal]
    omega
  have hpow : inputValue ≤
      (inputValue + 1) ^ (binaryPolynomialCoeffs p).length := by
    exact le_trans (by omega) (Nat.le_pow hlen)
  exact le_trans hpow
    (Nat.le_mul_of_pos_left _ (by
      have : 0 < (binaryPolynomialCoeffs p).sum + 1 := by omega
      exact this))

private theorem binaryHornerLayerSpace_le_polynomialSpace
    (initialSpace inputValue accValue coeff cap : ℕ)
    (hinput : inputValue ≤ cap) (hacc : accValue ≤ cap)
    (hnext : accValue * inputValue + coeff ≤ cap) :
    binaryHornerLayerSpace initialSpace inputValue accValue coeff ≤
      initialSpace + 10 * (2 * cap).size + 17 := by
  have hcap : cap ≤ 2 * cap := by omega
  have hinputSize := Nat.size_le_size (le_trans hinput hcap)
  have haccSize := Nat.size_le_size (le_trans hacc hcap)
  have hproduct : accValue * inputValue ≤ cap :=
    le_trans (Nat.le_add_right _ coeff) hnext
  have hproductAcc : accValue * inputValue + accValue ≤ 2 * cap := by
    omega
  have hproductAccSize := Nat.size_le_size hproductAcc
  have hnextSize := Nat.size_le_size (le_trans hnext hcap)
  simp [binaryHornerLayerSpace, binaryMulAddSpace,
    binaryMulAddLoopSpace, binaryAddSpace, binaryAddLoopSpace,
    binaryAddConstSpace, clearWorkTimeBound] at ⊢
  omega

private theorem binaryHornerLayerWork_source_hasBinaryNat
    (work : Fin n → Tape) (sourceIdx targetIdx : Fin n)
    (inputValue accValue coeff : ℕ) :
    (binaryHornerLayerWork work sourceIdx targetIdx inputValue accValue coeff
      sourceIdx).HasBinaryNat 0 := by
  simp [binaryHornerLayerWork]
  exact binaryPolynomialNatTape_hasBinaryNat 0

private theorem binaryHornerLayerWork_target_hasBinaryNat
    (work : Fin n → Tape) {sourceIdx targetIdx : Fin n}
    (hne : sourceIdx ≠ targetIdx) (inputValue accValue coeff : ℕ) :
    (binaryHornerLayerWork work sourceIdx targetIdx inputValue accValue coeff
      targetIdx).HasBinaryNat (accValue * inputValue + coeff) := by
  simp [binaryHornerLayerWork, Ne.symm hne]
  exact binaryPolynomialNatTape_hasBinaryNat _

private theorem binaryHornerLayerWork_other
    (work : Fin n → Tape) {sourceIdx targetIdx i : Fin n}
    (his : i ≠ sourceIdx) (hit : i ≠ targetIdx)
    (inputValue accValue coeff : ℕ) :
    binaryHornerLayerWork work sourceIdx targetIdx inputValue accValue coeff i =
      work i := by
  simp [binaryHornerLayerWork, his, hit]

private theorem binaryHornerLayersTM_hoareTimeSpace
    (inputIdx sourceIdx targetIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryMulAddDistinct sourceIdx inputIdx targetIdx
      mulCounterIdx addCounterIdx)
    (inputValue accValue inputLength initialSpace cap : ℕ)
    (coeffs : List ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : (work₀ inputIdx).HasBinaryNat inputValue)
    (hsource : (work₀ sourceIdx).HasBinaryNat accValue)
    (htarget : (work₀ targetIdx).HasBinaryNat 0)
    (hmulCounter : (work₀ mulCounterIdx).HasBinaryNat 0)
    (haddCounter : (work₀ addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1)
    (hinputCap : inputValue ≤ cap)
    (hcap : ∀ k, k ≤ coeffs.length →
      binaryHornerFold inputValue (coeffs.take k) accValue ≤ cap) :
    (binaryHornerLayersTM inputIdx sourceIdx targetIdx mulCounterIdx
      addCounterIdx coeffs).HoareTimeSpace
        (binaryPolynomialFramePred inp₀ work₀ out₀)
        (binaryPolynomialFramePred inp₀
          (binaryHornerWork work₀ sourceIdx targetIdx inputValue coeffs
            accValue) out₀)
        (binaryHornerLayersTime inputValue coeffs accValue) inputLength
        (initialSpace + 10 * (2 * cap).size + 17) := by
  induction coeffs generalizing sourceIdx targetIdx accValue work₀ with
  | nil =>
      have hbase := binaryAddConstTM_hoareTimeSpace_frame sourceIdx 0 accValue
        inputLength initialSpace inp₀ work₀ out₀ hsource hinp
        (fun i _ => hwork i) hout hworkSpace hinputSpace
      have hworkEq : Function.update work₀ sourceIdx
          (binaryPolynomialNatTape (accValue + 0)) = work₀ := by
        funext i
        by_cases hi : i = sourceIdx
        · subst i
          rw [Function.update_self]
          simpa [binaryPolynomialNatTape] using hsource.eq_init_move_right.symm
        · rw [Function.update_of_ne hi]
      have hacc : accValue ≤ cap := by
        exact hcap 0 (by simp)
      have haccSize := Nat.size_le_size (show accValue ≤ 2 * cap by omega)
      refine hbase.consequence (fun _ _ _ h => h) (fun inp work out h => ?_)
        (by simp [binaryHornerLayersTime, binaryAddConstTime]) le_rfl ?_
      · refine ⟨h.1, ?_, h.2.2⟩
        refine h.2.1.trans ?_
        change Function.update work₀ sourceIdx
          (binaryPolynomialNatTape (accValue + 0)) = work₀
        exact hworkEq
      · simp [binaryAddConstSpace]
        omega
  | cons coeff coeffs ih =>
      have hacc : accValue ≤ cap := by
        exact hcap 0 (by simp)
      have hnext : accValue * inputValue + coeff ≤ cap := by
        have h := hcap 1 (by simp)
        exact h
      have hlayer := binaryHornerLayerTM_hoareTimeSpace inputIdx sourceIdx
        targetIdx mulCounterIdx addCounterIdx hdistinct inputValue accValue
        coeff inputLength initialSpace inp₀ work₀ out₀ hinput hsource
        htarget hmulCounter haddCounter hinp hwork hout hworkSpace hinputSpace
      have hlayer' :
          (binaryHornerLayerTM inputIdx sourceIdx targetIdx mulCounterIdx
            addCounterIdx coeff).HoareTimeSpace
              (binaryPolynomialFramePred inp₀ work₀ out₀)
              (binaryPolynomialFramePred inp₀
                (binaryHornerLayerWork work₀ sourceIdx targetIdx inputValue
                  accValue coeff) out₀)
              (binaryHornerLayerTime inputValue accValue coeff) inputLength
              (initialSpace + 10 * (2 * cap).size + 17) :=
        hlayer.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) le_rfl
          le_rfl
          (binaryHornerLayerSpace_le_polynomialSpace initialSpace inputValue
            accValue coeff cap hinputCap hacc hnext)
      let work₁ := binaryHornerLayerWork work₀ sourceIdx targetIdx
        inputValue accValue coeff
      have hwork₁ : ∀ i, Parked (work₁ i) :=
        binaryHornerLayerWork_parked work₀ sourceIdx targetIdx inputValue
          accValue coeff hwork
      have hworkSpace₁ : ∀ i, (work₁ i).head ≤ initialSpace := by
        have hone : 1 ≤ initialSpace := by
          rw [← hsource.2.1]
          exact hworkSpace sourceIdx
        exact binaryHornerLayerWork_heads_le work₀ sourceIdx targetIdx
          inputValue accValue coeff initialSpace hworkSpace hone
      have hinput₁ : (work₁ inputIdx).HasBinaryNat inputValue := by
        change (binaryHornerLayerWork work₀ sourceIdx targetIdx inputValue
          accValue coeff inputIdx).HasBinaryNat inputValue
        rw [binaryHornerLayerWork_other work₀
          (Ne.symm hdistinct.left_ne_right) hdistinct.right_ne_acc]
        exact hinput
      have hsource₁ : (work₁ targetIdx).HasBinaryNat
          (accValue * inputValue + coeff) :=
        binaryHornerLayerWork_target_hasBinaryNat work₀
          hdistinct.left_ne_acc inputValue accValue coeff
      have htarget₁ : (work₁ sourceIdx).HasBinaryNat 0 :=
        binaryHornerLayerWork_source_hasBinaryNat work₀ sourceIdx targetIdx
          inputValue accValue coeff
      have hmulCounter₁ : (work₁ mulCounterIdx).HasBinaryNat 0 := by
        change (binaryHornerLayerWork work₀ sourceIdx targetIdx inputValue
          accValue coeff mulCounterIdx).HasBinaryNat 0
        rw [binaryHornerLayerWork_other work₀
          (Ne.symm hdistinct.left_ne_mulCounter)
          (Ne.symm hdistinct.acc_ne_mulCounter)]
        exact hmulCounter
      have haddCounter₁ : (work₁ addCounterIdx).HasBinaryNat 0 := by
        change (binaryHornerLayerWork work₀ sourceIdx targetIdx inputValue
          accValue coeff addCounterIdx).HasBinaryNat 0
        rw [binaryHornerLayerWork_other work₀
          (Ne.symm hdistinct.left_ne_addCounter)
          (Ne.symm hdistinct.acc_ne_addCounter)]
        exact haddCounter
      have hcap₁ : ∀ k, k ≤ coeffs.length →
          binaryHornerFold inputValue (coeffs.take k)
              (accValue * inputValue + coeff) ≤ cap := by
        intro k hk
        have h := hcap (k + 1) (by simp; omega)
        rwa [List.take_succ_cons, binaryHornerFold_cons_internal] at h
      have hrest := ih targetIdx sourceIdx
        (swapBinaryMulAddDistinct hdistinct) (accValue * inputValue + coeff)
        work₁ hinput₁ hsource₁
        htarget₁ hmulCounter₁ haddCounter₁ hwork₁ hworkSpace₁
        hcap₁
      have hrun := seqTM_hoareTimeSpace
        (binaryHornerLayerTM inputIdx sourceIdx targetIdx mulCounterIdx
          addCounterIdx coeff)
        (binaryHornerLayersTM inputIdx targetIdx sourceIdx mulCounterIdx
          addCounterIdx coeffs)
        hlayer'
        (binaryPolynomialFrame_transition inp₀ work₁ out₀ hinp hwork₁
          hout)
        hrest
      simpa [binaryHornerLayersTM, binaryHornerLayersTime,
        binaryHornerWork, work₁] using hrun

private theorem update_binaryZero_eq
    (work : Fin n → Tape) (idx : Fin n)
    (hzero : (work idx).HasBinaryNat 0) :
    Function.update work idx (binaryPolynomialNatTape 0) = work := by
  funext i
  by_cases hi : i = idx
  · subst i
    rw [Function.update_self]
    simpa [binaryPolynomialNatTape] using hzero.eq_init_move_right.symm
  · rw [Function.update_of_ne hi]

private theorem binaryHornerWork_endpoint
    (work : Fin n → Tape) (sourceIdx targetIdx : Fin n)
    (hne : sourceIdx ≠ targetIdx) (inputValue accValue : ℕ)
    (coeffs : List ℕ)
    (hsource : (work sourceIdx).HasBinaryNat accValue)
    (htarget : (work targetIdx).HasBinaryNat 0) :
    binaryHornerWork work sourceIdx targetIdx inputValue coeffs accValue =
      if Even coeffs.length then
        Function.update
          (Function.update work targetIdx (binaryPolynomialNatTape 0))
          sourceIdx
          (binaryPolynomialNatTape
            (binaryHornerFold inputValue coeffs accValue))
      else
        Function.update
          (Function.update work sourceIdx (binaryPolynomialNatTape 0))
          targetIdx
          (binaryPolynomialNatTape
            (binaryHornerFold inputValue coeffs accValue)) := by
  induction coeffs generalizing sourceIdx targetIdx accValue work with
  | nil =>
      simp only [binaryHornerWork, binaryHornerFold, List.length_nil]
      rw [ite_eq_left Even.zero]
      rw [update_binaryZero_eq work targetIdx htarget]
      funext i
      by_cases hi : i = sourceIdx
      · subst i
        rw [Function.update_self]
        simpa [binaryPolynomialNatTape] using hsource.eq_init_move_right
      · rw [Function.update_of_ne hi]
  | cons coeff coeffs ih =>
      let nextValue := accValue * inputValue + coeff
      let work₁ := binaryHornerLayerWork work sourceIdx targetIdx inputValue
        accValue coeff
      have hsource₁ : (work₁ targetIdx).HasBinaryNat nextValue := by
        exact binaryHornerLayerWork_target_hasBinaryNat work hne inputValue
          accValue coeff
      have htarget₁ : (work₁ sourceIdx).HasBinaryNat 0 :=
        binaryHornerLayerWork_source_hasBinaryNat work sourceIdx targetIdx
          inputValue accValue coeff
      have hih := ih work₁ targetIdx sourceIdx (Ne.symm hne) nextValue
        hsource₁ htarget₁
      rw [binaryHornerWork, hih]
      by_cases heven : Even coeffs.length
      · rw [ite_eq_left heven]
        have hoddCons : ¬Even (coeff :: coeffs).length := by
          rw [List.length_cons, Nat.even_add_one]
          exact not_not_intro heven
        rw [ite_eq_right hoddCons]
        funext i
        by_cases his : i = sourceIdx
        · subst i
          simp [work₁, binaryHornerLayerWork, hne]
        · by_cases hit : i = targetIdx
          · subst i
            simp [work₁, binaryHornerLayerWork, nextValue,
              binaryHornerFold_cons_internal]
          · simp [work₁, binaryHornerLayerWork, his, hit]
      · rw [ite_eq_right heven]
        have hevenCons : Even (coeff :: coeffs).length := by
          rw [List.length_cons, Nat.even_add_one]
          exact heven
        rw [ite_eq_left hevenCons]
        funext i
        by_cases his : i = sourceIdx
        · subst i
          simp [work₁, binaryHornerLayerWork, nextValue,
            binaryHornerFold_cons_internal]
        · by_cases hit : i = targetIdx
          · subst i
            simp [work₁, binaryHornerLayerWork, nextValue, Ne.symm hne,
              binaryHornerFold_cons_internal]
          · simp [work₁, binaryHornerLayerWork, his, hit]

private theorem binaryHornerLayerTM_isTransducer
    (inputIdx sourceIdx targetIdx mulCounterIdx addCounterIdx : Fin n)
    (coeff : ℕ) :
    (binaryHornerLayerTM inputIdx sourceIdx targetIdx mulCounterIdx
      addCounterIdx coeff).IsTransducer := by
  simpa [binaryHornerLayerTM] using
    ((binaryMulAddIntoTM_isTransducer sourceIdx inputIdx targetIdx
      mulCounterIdx addCounterIdx).seqTM
        (binaryAddConstTM_isTransducer targetIdx coeff)).seqTM
      (clearWorkTM_isTransducer sourceIdx)

private theorem binaryHornerLayersTM_isTransducer
    (inputIdx sourceIdx targetIdx mulCounterIdx addCounterIdx : Fin n)
    (coeffs : List ℕ) :
    (binaryHornerLayersTM inputIdx sourceIdx targetIdx mulCounterIdx
      addCounterIdx coeffs).IsTransducer := by
  induction coeffs generalizing sourceIdx targetIdx with
  | nil =>
      simpa [binaryHornerLayersTM] using
        binaryAddConstTM_isTransducer sourceIdx 0
  | cons coeff coeffs ih =>
      simpa [binaryHornerLayersTM] using
        (binaryHornerLayerTM_isTransducer inputIdx sourceIdx targetIdx
          mulCounterIdx addCounterIdx coeff).seqTM (ih targetIdx sourceIdx)

private theorem binaryPolynomialInitialWork_parked
    (inputIdx resultIdx scratchIdx mulCounterIdx addCounterIdx : Fin n)
    (work : Fin n → Tape) {inputValue : ℕ}
    (hinput : (work inputIdx).HasBinaryNat inputValue)
    (hresult : (work resultIdx).HasBinaryNat 0)
    (hscratch : (work scratchIdx).HasBinaryNat 0)
    (hmulCounter : (work mulCounterIdx).HasBinaryNat 0)
    (haddCounter : (work addCounterIdx).HasBinaryNat 0)
    (hother : ∀ i, i ≠ inputIdx → i ≠ resultIdx → i ≠ scratchIdx →
      i ≠ mulCounterIdx → i ≠ addCounterIdx → Parked (work i)) :
    ∀ i, Parked (work i) := by
  intro i
  by_cases hii : i = inputIdx
  · subst i; exact binaryPolynomialHasBinaryNat_parked hinput
  · by_cases hir : i = resultIdx
    · subst i; exact binaryPolynomialHasBinaryNat_parked hresult
    · by_cases his : i = scratchIdx
      · subst i; exact binaryPolynomialHasBinaryNat_parked hscratch
      · by_cases him : i = mulCounterIdx
        · subst i; exact binaryPolynomialHasBinaryNat_parked hmulCounter
        · by_cases hia : i = addCounterIdx
          · subst i; exact binaryPolynomialHasBinaryNat_parked haddCounter
          · exact hother i hii hir his him hia

theorem binaryPolynomialEvalTM_hoareTimeSpace_frame_internal
    (inputIdx resultIdx scratchIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryPolynomialDistinct inputIdx resultIdx scratchIdx
      mulCounterIdx addCounterIdx)
    (p : Polynomial ℕ) (inputValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : (work₀ inputIdx).HasBinaryNat inputValue)
    (hresult : (work₀ resultIdx).HasBinaryNat 0)
    (hscratch : (work₀ scratchIdx).HasBinaryNat 0)
    (hmulCounter : (work₀ mulCounterIdx).HasBinaryNat 0)
    (haddCounter : (work₀ addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ inputIdx → i ≠ resultIdx → i ≠ scratchIdx →
      i ≠ mulCounterIdx → i ≠ addCounterIdx → Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (binaryPolynomialEvalTM inputIdx resultIdx scratchIdx mulCounterIdx
      addCounterIdx p).HoareTimeSpace
        (binaryPolynomialFramePred inp₀ work₀ out₀)
        (binaryPolynomialFramePred inp₀
          (Function.update work₀ resultIdx
            (binaryPolynomialNatTape (p.eval inputValue))) out₀)
        (binaryPolynomialTime p inputValue) inputLength
        (binaryPolynomialSpace initialSpace p inputValue) := by
  let coeffs := binaryPolynomialCoeffs p
  let cap := binaryPolynomialValueCap p inputValue
  have hwork := binaryPolynomialInitialWork_parked inputIdx resultIdx
    scratchIdx mulCounterIdx addCounterIdx work₀ hinput hresult hscratch
    hmulCounter haddCounter hother
  have hinputCap : inputValue ≤ cap := by
    exact binaryPolynomial_input_le_cap p inputValue
  have hcap : ∀ k, k ≤ coeffs.length →
      binaryHornerFold inputValue (coeffs.take k) 0 ≤ cap := by
    intro k _
    simpa [coeffs, cap, binaryPolynomialValueCap] using
      binaryHornerFold_take_le inputValue (binaryPolynomialCoeffs p) k
  by_cases heven : Even coeffs.length
  · have hrun := binaryHornerLayersTM_hoareTimeSpace inputIdx resultIdx
      scratchIdx mulCounterIdx addCounterIdx (resultSourceDistinct hdistinct)
      inputValue 0 inputLength initialSpace cap coeffs inp₀ work₀ out₀
      hinput hresult hscratch hmulCounter haddCounter hinp hwork hout
      hworkSpace hinputSpace hinputCap hcap
    rw [binaryPolynomialEvalTM, ite_eq_left (by simpa [coeffs] using heven)]
    refine hrun.consequence (fun _ _ _ h => h) (fun inp work out h => ?_)
      (by simp [binaryPolynomialTime, coeffs]) le_rfl
      (by simp [binaryPolynomialSpace, cap])
    refine ⟨h.1, h.2.1.trans ?_, h.2.2⟩
    have hend := binaryHornerWork_endpoint work₀ resultIdx scratchIdx
      hdistinct.result_ne_scratch inputValue 0 coeffs hresult hscratch
    rw [ite_eq_left heven] at hend
    rw [hend, update_binaryZero_eq work₀ scratchIdx hscratch,
      binaryHornerFold_polyCoeffs_internal p inputValue]
  · have hrun := binaryHornerLayersTM_hoareTimeSpace inputIdx scratchIdx
      resultIdx mulCounterIdx addCounterIdx (scratchSourceDistinct hdistinct)
      inputValue 0 inputLength initialSpace cap coeffs inp₀ work₀ out₀
      hinput hscratch hresult hmulCounter haddCounter hinp hwork hout
      hworkSpace hinputSpace hinputCap hcap
    rw [binaryPolynomialEvalTM, ite_eq_right (by simpa [coeffs] using heven)]
    refine hrun.consequence (fun _ _ _ h => h) (fun inp work out h => ?_)
      (by simp [binaryPolynomialTime, coeffs]) le_rfl
      (by simp [binaryPolynomialSpace, cap])
    refine ⟨h.1, h.2.1.trans ?_, h.2.2⟩
    have hend := binaryHornerWork_endpoint work₀ scratchIdx resultIdx
      hdistinct.result_ne_scratch.symm inputValue 0 coeffs hscratch hresult
    rw [ite_eq_right heven] at hend
    rw [hend, update_binaryZero_eq work₀ scratchIdx hscratch,
      binaryHornerFold_polyCoeffs_internal p inputValue]

theorem binaryPolynomialEvalTM_hoareTime_frame_internal
    (inputIdx resultIdx scratchIdx mulCounterIdx addCounterIdx : Fin n)
    (hdistinct : BinaryPolynomialDistinct inputIdx resultIdx scratchIdx
      mulCounterIdx addCounterIdx)
    (p : Polynomial ℕ) (inputValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : (work₀ inputIdx).HasBinaryNat inputValue)
    (hresult : (work₀ resultIdx).HasBinaryNat 0)
    (hscratch : (work₀ scratchIdx).HasBinaryNat 0)
    (hmulCounter : (work₀ mulCounterIdx).HasBinaryNat 0)
    (haddCounter : (work₀ addCounterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ inputIdx → i ≠ resultIdx → i ≠ scratchIdx →
      i ≠ mulCounterIdx → i ≠ addCounterIdx → Parked (work₀ i))
    (hout : Parked out₀) :
    (binaryPolynomialEvalTM inputIdx resultIdx scratchIdx mulCounterIdx
      addCounterIdx p).HoareTime
        (binaryPolynomialFramePred inp₀ work₀ out₀)
        (binaryPolynomialFramePred inp₀
          (Function.update work₀ resultIdx
            (binaryPolynomialNatTape (p.eval inputValue))) out₀)
        (binaryPolynomialTime p inputValue) := by
  let initialSpace := Finset.univ.sup fun i : Fin n => (work₀ i).head
  have hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace := by
    intro i
    exact Finset.le_sup (f := fun j : Fin n => (work₀ j).head)
      (Finset.mem_univ i)
  exact (binaryPolynomialEvalTM_hoareTimeSpace_frame_internal inputIdx
    resultIdx scratchIdx mulCounterIdx addCounterIdx hdistinct p inputValue
    inp₀.head initialSpace
    inp₀ work₀ out₀ hinput hresult hscratch hmulCounter haddCounter
    hinp hother hout hworkSpace (by omega)).toHoareTime

theorem binaryPolynomialEvalTM_isTransducer_internal
    (inputIdx resultIdx scratchIdx mulCounterIdx addCounterIdx : Fin n)
    (p : Polynomial ℕ) :
    (binaryPolynomialEvalTM inputIdx resultIdx scratchIdx mulCounterIdx
      addCounterIdx p).IsTransducer := by
  simp only [binaryPolynomialEvalTM]
  split
  · exact binaryHornerLayersTM_isTransducer inputIdx resultIdx scratchIdx
      mulCounterIdx addCounterIdx (binaryPolynomialCoeffs p)
  · exact binaryHornerLayersTM_isTransducer inputIdx scratchIdx resultIdx
      mulCounterIdx addCounterIdx (binaryPolynomialCoeffs p)

theorem binaryPolynomialSpaceWidthPolynomial_eval_internal
    (p : Polynomial ℕ) (inputValue : ℕ) :
    (binaryPolynomialSpaceWidthPolynomial p).eval inputValue =
      2 * binaryPolynomialValueCap p inputValue := by
  simp only [binaryPolynomialSpaceWidthPolynomial, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X]
  dsimp only [binaryPolynomialValueCap]
  exact Nat.mul_assoc _ _ _

theorem binaryPolynomialSpace_bigO_internal
    (initialSpace : ℕ) (p : Polynomial ℕ) :
    (fun inputValue => binaryPolynomialSpace initialSpace p inputValue) =O
      (fun inputValue => Nat.log 2 inputValue) := by
  have hwidth :
      (fun inputValue => (2 * binaryPolynomialValueCap p inputValue).size) =O
        (fun inputValue => Nat.log 2 inputValue) := by
    have h := BigO.natSize_polynomial_eval
      (binaryPolynomialSpaceWidthPolynomial p)
    convert h using 1
    funext inputValue
    rw [binaryPolynomialSpaceWidthPolynomial_eval_internal]
  have hscaled := BigO.const_mul_left 10 hwidth
  have hconst := BigO.const_le_logTwo (initialSpace + 17)
  have hsum := BigO.add hconst hscaled
  convert hsum using 1
  funext inputValue
  simp [binaryPolynomialSpace]
  omega

end TM

end Complexity
