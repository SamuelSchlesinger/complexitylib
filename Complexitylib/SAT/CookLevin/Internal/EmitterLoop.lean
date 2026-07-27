/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.CookLevin.Internal.Emitter

/-!
# The emitter loop driver

`emitLoopTM body ctr fuel` runs `body` once per mark of the `fuel` register,
incrementing the counter register `ctr` after each run. Its Hoare rule
(`emitLoop_hoareTime`) is the single lemma behind every runtime loop of the
reduction emitter: the `t`-loops over tableau rows and the position loops
over tape cells. The per-iteration emission is an arbitrary word family
`E : ℕ → List Bool`, so nested loops instantiate `E` with inner loop
outputs, and leaf bodies instantiate it with `CNF.encode` images.

Also here: the arithmetic cap lemma `flatCaps` (one bound `4·A·B·C·D ≤ M`
discharges every `LitDesc.Spec` obligation) and the `encode`/`flatMap`
distribution lemma.
-/

@[expose] public section

namespace Complexity

namespace SAT

open TM

-- ════════════════════════════════════════════════════════════════════════
-- List and encode plumbing
-- ════════════════════════════════════════════════════════════════════════

/-- Peel the last iteration off a `flatMap` over `List.range`:
    `(range (i+1)).flatMap E = (range i).flatMap E ++ E i`. -/
theorem flatMap_range_succ {α : Type _} (E : ℕ → List α) (i : ℕ) :
    (List.range (i + 1)).flatMap E = (List.range i).flatMap E ++ E i := by
  rw [List.range_succ, List.flatMap_append]
  simp

/-- `CNF.encode` distributes over `flatMap`. -/
theorem CNF.encode_flatMap {α : Type _} (l : List α) (F : α → CNF) :
    CNF.encode (l.flatMap F) = l.flatMap (fun a => CNF.encode (F a)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, CNF.encode_append, ih]

-- ════════════════════════════════════════════════════════════════════════
-- The digit-cap discharger
-- ════════════════════════════════════════════════════════════════════════

/-- **One cap rules them all**: digits below their radices and
    `4·A·B·C·D ≤ M` bound every intermediate mixed-radix value. -/
theorem flatCaps {A B C D M tag a b c d : ℕ} (htag : tag ≤ 3)
    (ha : a < A) (hb : b < B) (hc : c < C) (hd : d < D)
    (hM : 4 * A * B * C * D ≤ M) :
    tag ≤ M ∧ tag * A + a ≤ M ∧ (tag * A + a) * B + b ≤ M ∧
    ((tag * A + a) * B + b) * C + c ≤ M ∧
    (((tag * A + a) * B + b) * C + c) * D + d ≤ M := by
  have hA1 : 1 ≤ A := by omega
  have hB1 : 1 ≤ B := by omega
  have hC1 : 1 ≤ C := by omega
  have hD1 : 1 ≤ D := by omega
  -- Stage bounds: each partial numeral is < 4·(product of radices so far).
  have h1 : tag * A + a < 4 * A := by
    have := Nat.mul_le_mul_right A htag
    omega
  have h2 : (tag * A + a) * B + b < 4 * A * B := by
    have hmul : (tag * A + a + 1) * B ≤ 4 * A * B :=
      Nat.mul_le_mul_right B (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega
  have h3 : ((tag * A + a) * B + b) * C + c < 4 * A * B * C := by
    have hmul : ((tag * A + a) * B + b + 1) * C ≤ 4 * A * B * C :=
      Nat.mul_le_mul_right C (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega
  have h4 : (((tag * A + a) * B + b) * C + c) * D + d < 4 * A * B * C * D := by
    have hmul : (((tag * A + a) * B + b) * C + c + 1) * D ≤ 4 * A * B * C * D :=
      Nat.mul_le_mul_right D (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega
  -- Each stage product divides into the final one.
  have g1 : 4 * A ≤ 4 * A * B * C * D := by
    calc 4 * A = 4 * A * 1 * 1 * 1 := by ring
      _ ≤ 4 * A * B * C * D := by
          exact Nat.mul_le_mul (Nat.mul_le_mul
            (Nat.mul_le_mul (le_refl _) hB1) hC1) hD1
  have g2 : 4 * A * B ≤ 4 * A * B * C * D := by
    calc 4 * A * B = 4 * A * B * 1 * 1 := by ring
      _ ≤ 4 * A * B * C * D := by
          exact Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) hC1) hD1
  have g3 : 4 * A * B * C ≤ 4 * A * B * C * D := by
    calc 4 * A * B * C = 4 * A * B * C * 1 := by ring
      _ ≤ 4 * A * B * C * D := Nat.mul_le_mul (le_refl _) hD1
  have gA : 4 ≤ 4 * A := by omega
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- The radices themselves sit below the master cap. -/
theorem radix_caps {A B C D M : ℕ} (hA1 : 1 ≤ A) (hB1 : 1 ≤ B) (hC1 : 1 ≤ C)
    (hD1 : 1 ≤ D) (hM : 4 * A * B * C * D ≤ M) :
    A ≤ M ∧ B ≤ M ∧ C ≤ M ∧ D ≤ M := by
  have base : ∀ x y z w : ℕ, 1 ≤ x → 1 ≤ y → 1 ≤ z → 1 ≤ w →
      x ≤ 4 * (x * (y * (z * w))) := by
    intro x y z w hx hy hz hw
    have h1 : 1 ≤ y * (z * w) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc x = x * 1 := (Nat.mul_one x).symm
      _ ≤ x * (y * (z * w)) := Nat.mul_le_mul_left x h1
      _ ≤ 4 * (x * (y * (z * w))) := Nat.le_mul_of_pos_left _ (by omega)
  have hre : 4 * A * B * C * D = 4 * (A * (B * (C * D))) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := base A B C D hA1 hB1 hC1 hD1
    omega
  · have := base B A C D hB1 hA1 hC1 hD1
    have hre' : 4 * (B * (A * (C * D))) = 4 * (A * (B * (C * D))) := by ring
    omega
  · have := base C A B D hC1 hA1 hB1 hD1
    have hre' : 4 * (C * (A * (B * D))) = 4 * (A * (B * (C * D))) := by ring
    omega
  · have := base D A B C hD1 hA1 hB1 hC1
    have hre' : 4 * (D * (A * (B * C))) = 4 * (A * (B * (C * D))) := by ring
    omega

-- ════════════════════════════════════════════════════════════════════════
-- The loop driver
-- ════════════════════════════════════════════════════════════════════════

/-- **The emitter loop**: run `body` once per mark of `fuel`, incrementing
    `ctr` after each run. -/
def emitLoopTM (body : TM n) (ctr fuel : Fin n) : TM n :=
  forRegTM (seqTM body (incRegTM ctr)) fuel

/-- Uniform budget of an emitter loop with at most `M` iterations whose body
    runs within `inner`. -/
def loopBudget (M inner : ℕ) : ℕ := M * (inner + 1 + opBudget M + 2) + (M + 2)

/-- `loopBudget M` is monotone in the inner budget. -/
theorem loopBudget_mono {M inner inner' : ℕ} (h : inner ≤ inner') :
    loopBudget M inner ≤ loopBudget M inner' := by
  have := Nat.mul_le_mul_left M (show inner + 1 + opBudget M + 2
    ≤ inner' + 1 + opBudget M + 2 by omega)
  rw [loopBudget, loopBudget]
  omega

/-- The raw loop bound rounds up to `loopBudget`. -/
theorem loop_le_loopBudget {v M inner : ℕ} (hv : v ≤ M) :
    v * ((inner + 1 + opBudget M) + 2) + (v + 2) ≤ loopBudget M inner := by
  rw [loopBudget]
  have := Nat.mul_le_mul_right ((inner + 1 + opBudget M) + 2) hv
  omega

/-- `clauseBudget · M` is monotone in the literal count. -/
theorem clauseBudget_mono {L L' M : ℕ} (h : L ≤ L') :
    clauseBudget L M ≤ clauseBudget L' M := by
  rw [clauseBudget, clauseBudget]
  have := Nat.mul_le_mul_right (emitVarBudget M + 1) h
  omega

/-- `cnfBudget · · M` is monotone in both the clause count and the literal count. -/
theorem cnfBudget_mono {K K' L L' M : ℕ} (hK : K ≤ K') (hL : L ≤ L') :
    cnfBudget K L M ≤ cnfBudget K' L' M := by
  rw [cnfBudget, cnfBudget]
  calc K * (clauseBudget L M + 1) + 1
      ≤ K' * (clauseBudget L' M + 1) + 1 := by
        have := Nat.mul_le_mul hK
          (show clauseBudget L M + 1 ≤ clauseBudget L' M + 1 from by
            have := clauseBudget_mono (M := M) hL
            omega)
        omega

/-- **`emitLoopTM` Hoare rule.** From `fuel = v` and `ctr = 0`, run the body
    at every `i < v`; the body sees `ctr = i` (fuel tape parked mid-loop),
    emits `E i`, and restores the work tapes. Afterwards `ctr = v` and the
    output extends by `(range v).flatMap E`. -/
theorem emitLoop_hoareTime (body : TM n) (ctr fuel : Fin n) (hcf : ctr ≠ fuel)
    (v M b_body : ℕ) (hv : v ≤ M)
    (E : ℕ → List Bool)
    (inp₀ : Tape) (W : Fin n → Tape) (ys₀ : List Bool)
    (hinp₀ : Parked inp₀) (hW : ∀ i, Parked (W i))
    (hfuel : W fuel = regTape v) (hctr : W ctr = regTape 0)
    (hbody : ∀ i, i < v → body.HoareTime
      (EmitPred inp₀
        (Function.update (Function.update W ctr (regTape i)) fuel
          ⟨i + 2, regCells v⟩)
        (ys₀ ++ (List.range i).flatMap E))
      (EmitPred inp₀
        (Function.update (Function.update W ctr (regTape i)) fuel
          ⟨i + 2, regCells v⟩)
        (ys₀ ++ (List.range (i + 1)).flatMap E))
      b_body) :
    (emitLoopTM body ctr fuel).HoareTime
      (EmitPred inp₀ W ys₀)
      (EmitPred inp₀ (Function.update W ctr (regTape v))
        (ys₀ ++ (List.range v).flatMap E))
      (v * ((b_body + 1 + opBudget M) + 2) + (v + 2)) := by
  have hfc : fuel ≠ ctr := fun h => hcf h.symm
  have hbodyseq : ∀ i, i < v → (seqTM body (incRegTM ctr)).HoareTime
      (fun inp work out => inp = inp₀ ∧
        work = Function.update (Function.update W ctr (regTape i)) fuel
          ⟨i + 2, regCells v⟩ ∧
        OutAcc (ys₀ ++ (List.range i).flatMap E) out)
      (fun inp work out => inp = inp₀ ∧
        work = Function.update (Function.update W ctr (regTape (i + 1))) fuel
          ⟨i + 2, regCells v⟩ ∧
        OutAcc (ys₀ ++ (List.range (i + 1)).flatMap E) out)
      (b_body + 1 + opBudget M) := by
    intro i hi
    set Si : Fin n → Tape :=
      Function.update (Function.update W ctr (regTape i)) fuel
        ⟨i + 2, regCells v⟩ with hSi
    have hSiP : ∀ j, Parked (Si j) := by
      intro j
      by_cases hjf : j = fuel
      · subst hjf
        rw [hSi, Function.update_self]
        exact parked_regCells (by omega)
      · rw [hSi, Function.update_of_ne hjf]
        by_cases hjc : j = ctr
        · subst hjc; rw [Function.update_self]; exact parked_regTape _
        · rw [Function.update_of_ne hjc]; exact hW j
    have hinc : (incRegTM ctr).HoareTime
        (EmitPred inp₀ Si (ys₀ ++ (List.range (i + 1)).flatMap E))
        (EmitPred inp₀
          (Function.update (Function.update W ctr (regTape (i + 1))) fuel
            ⟨i + 2, regCells v⟩)
          (ys₀ ++ (List.range (i + 1)).flatMap E))
        (opBudget M) := by
      refine ((incRegTM_hoareTime ctr i inp₀ Si _ hinp₀
        (fun j _ => hSiP j)
        (by rw [hSi, Function.update_of_ne hcf, Function.update_self])
        ).consequence (fun _ _ _ h => h) ?_ (incRegTM_le_opBudget (by omega)))
      rintro inp work out ⟨g1, g2, g3⟩
      refine ⟨g1, ?_, g3⟩
      rw [g2, hSi, Function.update_comm hfc, Function.update_idem]
    exact seqTM_hoareTime body (incRegTM ctr) (hbody i hi)
      (emitPred_transition hinp₀ hSiP _) hinc
  have hrule := forRegTM_hoareTime (seqTM body (incRegTM ctr)) fuel v inp₀
    (fun i => Function.update W ctr (regTape i))
    (fun i => ys₀ ++ (List.range i).flatMap E)
    (b_body + 1 + opBudget M) hinp₀
    (fun i => by
      show Function.update W ctr (regTape i) fuel = regTape v
      rw [Function.update_of_ne hfc]
      exact hfuel)
    (fun i j hj => by
      show Parked (Function.update W ctr (regTape i) j)
      by_cases hjc : j = ctr
      · subst hjc; rw [Function.update_self]; exact parked_regTape _
      · rw [Function.update_of_ne hjc]; exact hW j)
    hbodyseq
  refine hrule.consequence ?_ (fun _ _ _ h => h) (le_refl _)
  rintro inp work out ⟨g1, g2, g3⟩
  refine ⟨g1, ?_, ?_⟩
  · rw [g2]
    show W = Function.update W ctr (regTape 0)
    rw [show regTape 0 = W ctr from hctr.symm, Function.update_eq_self]
  · simpa using g3

/-- **`emitLoopTM` Hoare rule, offset form**: the counter starts at `s` and
    ends at `s + v`; the body at iteration `i < v` sees `ctr = s + i`. Used
    by the pairwise at-most-one families, whose inner position loops start
    just past the outer position. -/
theorem emitLoopFrom_hoareTime (body : TM n) (ctr fuel : Fin n)
    (hcf : ctr ≠ fuel) (s v M b_body : ℕ) (hsv : s + v ≤ M)
    (E : ℕ → List Bool)
    (inp₀ : Tape) (W : Fin n → Tape) (ys₀ : List Bool)
    (hinp₀ : Parked inp₀) (hW : ∀ i, Parked (W i))
    (hfuel : W fuel = regTape v) (hctr : W ctr = regTape s)
    (hbody : ∀ i, i < v → body.HoareTime
      (EmitPred inp₀
        (Function.update (Function.update W ctr (regTape (s + i))) fuel
          ⟨i + 2, regCells v⟩)
        (ys₀ ++ (List.range i).flatMap E))
      (EmitPred inp₀
        (Function.update (Function.update W ctr (regTape (s + i))) fuel
          ⟨i + 2, regCells v⟩)
        (ys₀ ++ (List.range (i + 1)).flatMap E))
      b_body) :
    (emitLoopTM body ctr fuel).HoareTime
      (EmitPred inp₀ W ys₀)
      (EmitPred inp₀ (Function.update W ctr (regTape (s + v)))
        (ys₀ ++ (List.range v).flatMap E))
      (v * ((b_body + 1 + opBudget M) + 2) + (v + 2)) := by
  have hfc : fuel ≠ ctr := fun h => hcf h.symm
  have hbodyseq : ∀ i, i < v → (seqTM body (incRegTM ctr)).HoareTime
      (fun inp work out => inp = inp₀ ∧
        work = Function.update (Function.update W ctr (regTape (s + i))) fuel
          ⟨i + 2, regCells v⟩ ∧
        OutAcc (ys₀ ++ (List.range i).flatMap E) out)
      (fun inp work out => inp = inp₀ ∧
        work = Function.update (Function.update W ctr (regTape (s + (i + 1))))
          fuel ⟨i + 2, regCells v⟩ ∧
        OutAcc (ys₀ ++ (List.range (i + 1)).flatMap E) out)
      (b_body + 1 + opBudget M) := by
    intro i hi
    set Si : Fin n → Tape :=
      Function.update (Function.update W ctr (regTape (s + i))) fuel
        ⟨i + 2, regCells v⟩ with hSi
    have hSiP : ∀ j, Parked (Si j) :=
      parked_update (parked_update hW (parked_regTape _))
        (parked_regCells (by omega))
    have hinc : (incRegTM ctr).HoareTime
        (EmitPred inp₀ Si (ys₀ ++ (List.range (i + 1)).flatMap E))
        (EmitPred inp₀
          (Function.update (Function.update W ctr (regTape (s + (i + 1)))) fuel
            ⟨i + 2, regCells v⟩)
          (ys₀ ++ (List.range (i + 1)).flatMap E))
        (opBudget M) := by
      refine ((incRegTM_hoareTime ctr (s + i) inp₀ Si _ hinp₀
        (fun j _ => hSiP j)
        (by rw [hSi, Function.update_of_ne hcf, Function.update_self])
        ).consequence (fun _ _ _ h => h) ?_ (incRegTM_le_opBudget (by omega)))
      rintro inp work out ⟨g1, g2, g3⟩
      refine ⟨g1, ?_, g3⟩
      rw [g2, hSi, Function.update_comm hfc, Function.update_idem,
        show s + i + 1 = s + (i + 1) from by omega]
    exact seqTM_hoareTime body (incRegTM ctr) (hbody i hi)
      (emitPred_transition hinp₀ hSiP _) hinc
  have hrule := forRegTM_hoareTime (seqTM body (incRegTM ctr)) fuel v inp₀
    (fun i => Function.update W ctr (regTape (s + i)))
    (fun i => ys₀ ++ (List.range i).flatMap E)
    (b_body + 1 + opBudget M) hinp₀
    (fun i => by
      show Function.update W ctr (regTape (s + i)) fuel = regTape v
      rw [Function.update_of_ne hfc]
      exact hfuel)
    (fun i j hj => by
      show Parked (Function.update W ctr (regTape (s + i)) j)
      by_cases hjc : j = ctr
      · subst hjc; rw [Function.update_self]; exact parked_regTape _
      · rw [Function.update_of_ne hjc]; exact hW j)
    hbodyseq
  refine hrule.consequence ?_ (fun _ _ _ h => h) (le_refl _)
  rintro inp work out ⟨g1, g2, g3⟩
  refine ⟨g1, ?_, ?_⟩
  · rw [g2]
    show W = Function.update W ctr (regTape (s + 0))
    rw [show regTape (s + 0) = W ctr from by rw [Nat.add_zero]; exact hctr.symm,
      Function.update_eq_self]
  · simpa using g3

/-- **`emitLoopTM` Hoare rule, general form**: the per-iteration work states
    are an arbitrary ghost family `u` (so bodies may drift registers across
    iterations — shrinking inner fuels, mirrored counters), and the counter
    value is an arbitrary ghost `ctrVal`. The body at iteration `i` carries
    `u i` to `u (i + 1)`-with-the-counter-still-old; the loop's own increment
    finishes the move. -/
theorem emitLoopGen_hoareTime (body : TM n) (ctr fuel : Fin n)
    (hcf : ctr ≠ fuel) (v M b_body : ℕ)
    (ctrVal : ℕ → ℕ) (hctrM : ∀ i, i < v → ctrVal i ≤ M)
    (E : ℕ → List Bool)
    (inp₀ : Tape) (u : ℕ → Fin n → Tape) (ys₀ : List Bool)
    (hinp₀ : Parked inp₀) (hu : ∀ i j, Parked (u i j))
    (hufuel : ∀ i, u i fuel = regTape v)
    (huctr : ∀ i, u (i + 1) ctr = regTape (ctrVal i + 1))
    (hbody : ∀ i, i < v → body.HoareTime
      (EmitPred inp₀ (Function.update (u i) fuel ⟨i + 2, regCells v⟩)
        (ys₀ ++ (List.range i).flatMap E))
      (EmitPred inp₀
        (Function.update (Function.update (u (i + 1)) ctr (regTape (ctrVal i)))
          fuel ⟨i + 2, regCells v⟩)
        (ys₀ ++ (List.range (i + 1)).flatMap E))
      b_body) :
    (emitLoopTM body ctr fuel).HoareTime
      (EmitPred inp₀ (u 0) ys₀)
      (EmitPred inp₀ (u v) (ys₀ ++ (List.range v).flatMap E))
      (v * ((b_body + 1 + opBudget M) + 2) + (v + 2)) := by
  have hfc : fuel ≠ ctr := fun h => hcf h.symm
  have hbodyseq : ∀ i, i < v → (seqTM body (incRegTM ctr)).HoareTime
      (fun inp work out => inp = inp₀ ∧
        work = Function.update (u i) fuel ⟨i + 2, regCells v⟩ ∧
        OutAcc (ys₀ ++ (List.range i).flatMap E) out)
      (fun inp work out => inp = inp₀ ∧
        work = Function.update (u (i + 1)) fuel ⟨i + 2, regCells v⟩ ∧
        OutAcc (ys₀ ++ (List.range (i + 1)).flatMap E) out)
      (b_body + 1 + opBudget M) := by
    intro i hi
    set Si : Fin n → Tape :=
      Function.update (Function.update (u (i + 1)) ctr (regTape (ctrVal i))) fuel
        ⟨i + 2, regCells v⟩ with hSi
    have hSiP : ∀ j, Parked (Si j) :=
      parked_update (parked_update (hu (i + 1)) (parked_regTape _))
        (parked_regCells (by omega))
    have hinc : (incRegTM ctr).HoareTime
        (EmitPred inp₀ Si (ys₀ ++ (List.range (i + 1)).flatMap E))
        (EmitPred inp₀ (Function.update (u (i + 1)) fuel ⟨i + 2, regCells v⟩)
          (ys₀ ++ (List.range (i + 1)).flatMap E))
        (opBudget M) := by
      refine ((incRegTM_hoareTime ctr (ctrVal i) inp₀ Si _ hinp₀
        (fun j _ => hSiP j)
        (by rw [hSi, Function.update_of_ne hcf, Function.update_self])
        ).consequence (fun _ _ _ h => h) ?_ (incRegTM_le_opBudget (hctrM i hi)))
      rintro inp work out ⟨g1, g2, g3⟩
      refine ⟨g1, ?_, g3⟩
      rw [g2, hSi, Function.update_comm hfc, Function.update_idem,
        show regTape (ctrVal i + 1) = u (i + 1) ctr from (huctr i).symm,
        Function.update_eq_self]
    exact seqTM_hoareTime body (incRegTM ctr) (hbody i hi)
      (emitPred_transition hinp₀ hSiP _) hinc
  have hrule := forRegTM_hoareTime (seqTM body (incRegTM ctr)) fuel v inp₀
    u (fun i => ys₀ ++ (List.range i).flatMap E)
    (b_body + 1 + opBudget M) hinp₀ hufuel
    (fun i j _ => hu i j)
    hbodyseq
  refine hrule.consequence ?_ (fun _ _ _ h => h) (le_refl _)
  rintro inp work out ⟨g1, g2, g3⟩
  exact ⟨g1, g2, by simpa using g3⟩

end SAT

end Complexity
