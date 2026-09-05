/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.RegularGraph
public import Complexitylib.Classes.PCP.Internal.Mixing
public import Complexitylib.Classes.PCP.Internal.Cheeger

/-!
# The zig-zag product

The expander family of `ExpanderExists` is obtained by counting, so nothing
computes it. A verifier, though, has to *build* its constraint graph, so the
`NP ⊆ PCP` direction needs a family some algorithm produces.

The zig-zag product is the standard route, and it is enough that its *base*
graph be non-constructive: the base is a single graph of constant size, which an
algorithm may carry as a table, while the family itself is built from it by an
explicit recursion. Classically, "there is a machine with this table built in"
is provable without knowing the table.

A vertex of `G ⓩ H` is a dart of `G` — a vertex of `G` together with one of its
labels — and a step takes three: a step in the small graph `H` on the label, a
step in `G` along the label reached, and a step in `H` on the label arrived at.
Reversing a zig-zag step reverses each of the three and swaps the two `H`-labels,
which is why the rotation map is an involution.

## Main definitions

- `Complexity.RegGraph.zigzag` — the product

## Main results

- `Complexity.RegGraph.order_zigzag`, `Complexity.RegGraph.deg_zigzag` — its size
  and degree
- `Complexity.RegGraph.step_zigzag` — the walk factors as cloud, cross, cloud
- `Complexity.RegGraph.sum_sq_crossStep` — the crossing move is an isometry
- `Complexity.RegGraph.cloudStep_apply` — the cloud move *is* `H`'s own walk
- `Complexity.RegGraph.sum_sq_cloudStep_le` — so it contracts what `H` contracts
- `Complexity.RegGraph.cloudStep_cloudPar` — the cloud move fixes the part
  constant along clouds, and `Complexity.RegGraph.sum_cloudPerp` — kills the rest
- `Complexity.RegGraph.ip_cloudStep`, `Complexity.RegGraph.ip_crossStep` — both
  moves are self-adjoint
- `Complexity.RegGraph.cloudMean_crossStep_cloudPar` — on the part constant
  along clouds, the crossing move is exactly `G`'s own walk
- `Complexity.RegGraph.cloudStep_decomp` — one cloud move splits `f` into its
  constant part and a contracted remainder
- `Complexity.RegGraph.sum_mul_step_le_of_spectralBound` — a spectral bound
  controls the Rayleigh quotient
- `Complexity.RegGraph.ip_cloudPar_cloudPerp` — the two parts are orthogonal
- `Complexity.RegGraph.ip_two_mul_le` — the weighted arithmetic-geometric bound
- `Complexity.RegGraph.ip_step_zigzag_le` — **the RVW estimate**
- `Complexity.RegGraph.ip_cloudStep_le` — the cloud move is a contraction
- `Complexity.RegGraph.abs_ip_step_zigzag_le` — the RVW estimate, two-sided
- `Complexity.RegGraph.spectralBound_zigzag` — **the spectral bound of the
  product**
-/

@[expose] public section

namespace Complexity

namespace RegGraph

variable (G H : RegGraph) (e : H.V ≃ G.D)

/-- One zig-zag step: turn inside the cloud, cross, then turn again. -/
def zigzagRot : (G.V × G.D) × (H.D × H.D) → (G.V × G.D) × (H.D × H.D) :=
  fun x =>
    let p := H.rot (e.symm x.1.2, x.2.1)
    let q := G.rot (x.1.1, e p.1)
    let r := H.rot (e.symm q.2, x.2.2)
    ((q.1, e r.1), (r.2, p.2))

theorem zigzagRot_involutive : Function.Involutive (zigzagRot G H e) := by
  intro x
  obtain ⟨⟨v, i⟩, ⟨a, b⟩⟩ := x
  simp only [zigzagRot]
  -- the three reversals, innermost first
  set p := H.rot (e.symm i, a) with hp
  set q := G.rot (v, e p.1) with hq
  set r := H.rot (e.symm q.2, b) with hr
  have hrr : H.rot (e.symm (e r.1), r.2) = (e.symm q.2, b) := by
    rw [Equiv.symm_apply_apply]
    have : (r.1, r.2) = r := rfl
    rw [this, hr, H.rot_involutive]
  have hqq : G.rot (q.1, e (e.symm q.2)) = (v, e p.1) := by
    rw [Equiv.apply_symm_apply]
    have : (q.1, q.2) = q := rfl
    rw [this, hq, G.rot_involutive]
  have hpp : H.rot (e.symm (e p.1), p.2) = (e.symm i, a) := by
    rw [Equiv.symm_apply_apply]
    have : (p.1, p.2) = p := rfl
    rw [this, hp, H.rot_involutive]
  simp only [hrr, hqq, hpp]
  simp

/-- **The zig-zag product.** Its vertices are the darts of `G` and its degree is
the square of `H`'s. -/
def zigzag : RegGraph where
  V := G.V × G.D
  D := H.D × H.D
  decEqV := by
    haveI := G.decEqV
    haveI := G.decEqD
    exact inferInstance
  decEqD := by
    haveI := H.decEqD
    exact inferInstance
  fintypeV := by
    haveI := G.fintypeV
    haveI := G.fintypeD
    exact inferInstance
  fintypeD := by
    haveI := H.fintypeD
    exact inferInstance
  nonemptyD := by
    have := H.nonemptyD
    exact inferInstance
  rot := zigzagRot G H e
  rot_involutive := zigzagRot_involutive G H e

@[simp] theorem order_zigzag : (zigzag G H e).order = G.order * G.deg :=
  @Fintype.card_prod G.V G.D G.fintypeV G.fintypeD

@[simp] theorem deg_zigzag : (zigzag G H e).deg = H.deg * H.deg :=
  @Fintype.card_prod H.D H.D H.fintypeD H.fintypeD

/-! ### The walk, factored -/

/-- The move inside a cloud: one step of `H` on the label, the vertex of `G`
held fixed. -/
noncomputable def cloudStep (f : G.V × G.D → ℝ) : G.V × G.D → ℝ :=
  fun x => (∑ b : H.D, f (x.1, e (H.rot (e.symm x.2, b)).1)) / (H.deg : ℝ)

/-- The crossing move: follow the dart of `G` the label names. It is composition
with `G.rot`, an involution of darts, so it merely permutes the vertices of the
product. -/
def crossStep (f : G.V × G.D → ℝ) : G.V × G.D → ℝ := fun x => f (G.rot x)

/-- **The zig-zag walk is cloud, then cross, then cloud.** -/
theorem step_zigzag (f : (zigzag G H e).V → ℝ) (x : (zigzag G H e).V) :
    (zigzag G H e).step f x
      = cloudStep G H e (crossStep G (cloudStep G H e f)) x := by
  have hd : (H.deg : ℝ) ≠ 0 := H.deg_ne_zero
  have hdeg : ((zigzag G H e).deg : ℝ) = (H.deg : ℝ) * (H.deg : ℝ) := by
    rw [deg_zigzag]
    push_cast
    ring
  have hsum : (∑ d : (zigzag G H e).D, f ((zigzag G H e).nbr x d))
      = ∑ a : H.D, ∑ b : H.D, f ((zigzagRot G H e (x, (a, b))).1) :=
    Fintype.sum_prod_type (f := fun d : H.D × H.D => f ((zigzagRot G H e (x, d)).1))
  erw [RegGraph.step, hdeg, hsum, cloudStep]
  have hinner : ∀ a : H.D,
      ∑ b : H.D, f ((zigzagRot G H e (x, (a, b))).1)
        = (H.deg : ℝ) * cloudStep G H e f
            (G.rot (x.1, e (H.rot (e.symm x.2, a)).1)) := by
    intro a
    erw [cloudStep]
    field_simp
    rfl
  erw [Finset.sum_congr rfl fun a _ => hinner a, ← Finset.mul_sum]
  show _ = (∑ b : H.D, cloudStep G H e f (G.rot (x.1, e (H.rot (e.symm x.2, b)).1)))
      / (H.deg : ℝ)
  field_simp

/-- **The crossing move is an isometry**: it permutes the darts of `G`. -/
theorem sum_sq_crossStep (f : G.V × G.D → ℝ) :
    ∑ x : G.V × G.D, (crossStep G f x) ^ 2 = ∑ x : G.V × G.D, (f x) ^ 2 :=
  Fintype.sum_equiv (G.rot_involutive.toPerm)
    (fun x => (crossStep G f x) ^ 2) (fun x => (f x) ^ 2) fun _ => rfl

/-- The crossing move preserves the inner product with itself. -/
theorem sum_sq_crossStep_aux (f : G.V × G.D → ℝ) :
    ∑ x : G.V × G.D, crossStep G f x * crossStep G f x
      = ∑ x : G.V × G.D, f x * f x :=
  Fintype.sum_equiv (G.rot_involutive.toPerm)
    (fun x => crossStep G f x * crossStep G f x) (fun x => f x * f x) fun _ => rfl

/-- The crossing move preserves sums too. -/
theorem sum_crossStep (f : G.V × G.D → ℝ) :
    ∑ x : G.V × G.D, crossStep G f x = ∑ x : G.V × G.D, f x :=
  Fintype.sum_equiv (G.rot_involutive.toPerm)
    (fun x => crossStep G f x) (fun x => f x) fun _ => rfl

/-! ### The cloud move is `H`'s walk -/

/-- One cloud of the product, read as a function on `H`'s vertices. -/
def cloudFun (f : G.V × G.D → ℝ) (v : G.V) : H.V → ℝ := fun u => f (v, e u)

/-- **The cloud move is `H`'s walk**, transported along `e`. Every property of
`H`'s step operator therefore holds cloud by cloud. -/
theorem cloudStep_apply (f : G.V × G.D → ℝ) (v : G.V) (i : G.D) :
    cloudStep G H e f (v, i) = H.step (cloudFun G H e f v) (e.symm i) := rfl

theorem sum_cloudFun (f : G.V × G.D → ℝ) (v : G.V) :
    ∑ u : H.V, cloudFun G H e f v u = ∑ i : G.D, f (v, i) :=
  Fintype.sum_equiv e (fun u => cloudFun G H e f v u) (fun i => f (v, i)) fun _ => rfl

theorem sum_sq_cloudFun (f : G.V × G.D → ℝ) (v : G.V) :
    ∑ u : H.V, (cloudFun G H e f v u) ^ 2 = ∑ i : G.D, (f (v, i)) ^ 2 :=
  Fintype.sum_equiv e (fun u => (cloudFun G H e f v u) ^ 2) (fun i => (f (v, i)) ^ 2)
    fun _ => rfl

/-- The cloud move, summed over one cloud, is what `H`'s walk does there. -/
theorem sum_cloudStep (f : G.V × G.D → ℝ) (v : G.V) :
    ∑ i : G.D, cloudStep G H e f (v, i) = ∑ i : G.D, f (v, i) := by
  have h : ∑ i : G.D, cloudStep G H e f (v, i)
      = ∑ u : H.V, H.step (cloudFun G H e f v) u :=
    (Fintype.sum_equiv e (fun u => H.step (cloudFun G H e f v) u)
      (fun i => cloudStep G H e f (v, i)) fun u => by
        rw [cloudStep_apply, Equiv.symm_apply_apply]).symm
  rw [h, H.sum_step, sum_cloudFun]

/-- **The cloud move contracts what `H` contracts.** On a cloud whose values sum
to zero, one cloud move shrinks the sum of squares by `lam ^ 2`. -/
theorem sum_sq_cloudStep_le {lam : ℝ} (hH : H.SpectralBound lam)
    (f : G.V × G.D → ℝ) (v : G.V) (hv : ∑ i : G.D, f (v, i) = 0) :
    ∑ i : G.D, (cloudStep G H e f (v, i)) ^ 2 ≤ lam ^ 2 * ∑ i : G.D, (f (v, i)) ^ 2 := by
  have hzero : ∑ u : H.V, cloudFun G H e f v u = 0 := by
    rw [sum_cloudFun]
    exact hv
  have hbound := hH (cloudFun G H e f v) hzero
  have h : ∑ i : G.D, (cloudStep G H e f (v, i)) ^ 2
      = ∑ u : H.V, (H.step (cloudFun G H e f v) u) ^ 2 :=
    (Fintype.sum_equiv e (fun u => (H.step (cloudFun G H e f v) u) ^ 2)
      (fun i => (cloudStep G H e f (v, i)) ^ 2) fun u => by
        rw [cloudStep_apply, Equiv.symm_apply_apply]).symm
  rw [h, ← sum_sq_cloudFun]
  exact hbound

/-! ### Splitting off the part constant along clouds -/

/-- The average of `f` over the cloud above a vertex of `G`. -/
noncomputable def cloudMean (f : G.V × G.D → ℝ) (v : G.V) : ℝ :=
  (∑ i : G.D, f (v, i)) / (G.deg : ℝ)

/-- The part of `f` that is constant along each cloud. -/
noncomputable def cloudPar (f : G.V × G.D → ℝ) : G.V × G.D → ℝ :=
  fun x => cloudMean G f x.1

/-- What is left over. -/
noncomputable def cloudPerp (f : G.V × G.D → ℝ) : G.V × G.D → ℝ :=
  fun x => f x - cloudPar G f x

theorem cloudPar_add_cloudPerp (f : G.V × G.D → ℝ) (x : G.V × G.D) :
    cloudPar G f x + cloudPerp G f x = f x := by
  erw [cloudPerp]
  ring

/-- **The cloud move fixes the constant part.** -/
theorem cloudStep_cloudPar (f : G.V × G.D → ℝ) (x : G.V × G.D) :
    cloudStep G H e (cloudPar G f) x = cloudPar G f x := by
  obtain ⟨v, i⟩ := x
  rw [cloudStep_apply]
  have hconst : cloudFun G H e (cloudPar G f) v = fun _ => cloudMean G f v := rfl
  rw [hconst, RegGraph.step_const]
  rfl

/-- **The leftover part sums to zero on every cloud.** -/
theorem sum_cloudPerp (f : G.V × G.D → ℝ) (v : G.V) :
    ∑ i : G.D, cloudPerp G f (v, i) = 0 := by
  have hdeg : (G.deg : ℝ) ≠ 0 := G.deg_ne_zero
  have hcard : (Finset.univ : Finset G.D).card = G.deg := Finset.card_univ
  erw [show (fun i : G.D => cloudPerp G f (v, i))
      = fun i : G.D => f (v, i) - cloudMean G f v from rfl]
  erw [Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul, cloudMean]
  field_simp
  ring

/-- The cloud move contracts the leftover part. -/
theorem sum_sq_cloudStep_cloudPerp_le {lam : ℝ} (hH : H.SpectralBound lam)
    (f : G.V × G.D → ℝ) (v : G.V) :
    ∑ i : G.D, (cloudStep G H e (cloudPerp G f) (v, i)) ^ 2
      ≤ lam ^ 2 * ∑ i : G.D, (cloudPerp G f (v, i)) ^ 2 :=
  sum_sq_cloudStep_le G H e hH (cloudPerp G f) v (sum_cloudPerp G f v)

/-! ### Both moves are self-adjoint -/

/-- One step of a graph is self-adjoint: reversing darts is a bijection. -/
theorem sum_mul_step_comm (K : RegGraph) (f g : K.V → ℝ) :
    ∑ v : K.V, f v * K.step g v = ∑ v : K.V, K.step f v * g v := by
  have hr : ∑ v : K.V, K.step f v * g v = ∑ v : K.V, g v * K.step f v :=
    Finset.sum_congr rfl fun v _ => mul_comm _ _
  rw [hr, sum_mul_step, sum_mul_step]
  congr 1
  rw [K.sum_darts_swap (fun u w => f u * g w)]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

/-- The inner product of two functions on the darts of `G`. -/
noncomputable def ip (f g : G.V × G.D → ℝ) : ℝ := ∑ x : G.V × G.D, f x * g x

theorem ip_comm (f g : G.V × G.D → ℝ) : ip G f g = ip G g f := by
  erw [ip, ip]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- Summing over the product is summing cloud by cloud. -/
theorem ip_eq_sum_clouds (f g : G.V × G.D → ℝ) :
    ip G f g = ∑ v : G.V, ∑ i : G.D, f (v, i) * g (v, i) := by
  erw [ip, Fintype.sum_prod_type]

/-- **The cloud move is self-adjoint**, because `H`'s walk is. -/
theorem ip_cloudStep (f g : G.V × G.D → ℝ) :
    ip G (cloudStep G H e f) g = ip G f (cloudStep G H e g) := by
  rw [ip_eq_sum_clouds, ip_eq_sum_clouds]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hl : ∑ i : G.D, cloudStep G H e f (v, i) * g (v, i)
      = ∑ u : H.V, H.step (cloudFun G H e f v) u * cloudFun G H e g v u :=
    (Fintype.sum_equiv e
      (fun u => H.step (cloudFun G H e f v) u * cloudFun G H e g v u)
      (fun i => cloudStep G H e f (v, i) * g (v, i)) fun u => by
        rw [cloudStep_apply, Equiv.symm_apply_apply]
        rfl).symm
  have hr : ∑ i : G.D, f (v, i) * cloudStep G H e g (v, i)
      = ∑ u : H.V, cloudFun G H e f v u * H.step (cloudFun G H e g v) u :=
    (Fintype.sum_equiv e
      (fun u => cloudFun G H e f v u * H.step (cloudFun G H e g v) u)
      (fun i => f (v, i) * cloudStep G H e g (v, i)) fun u => by
        rw [cloudStep_apply, Equiv.symm_apply_apply]
        rfl).symm
  rw [hl, hr, ← sum_mul_step_comm]

/-- **The crossing move is self-adjoint**, because `G.rot` is an involution. -/
theorem ip_crossStep (f g : G.V × G.D → ℝ) :
    ip G (crossStep G f) g = ip G f (crossStep G g) := by
  erw [ip, ip]
  refine Fintype.sum_equiv (G.rot_involutive.toPerm)
    (fun x => crossStep G f x * g x) (fun x => f x * crossStep G g x) fun x => ?_
  show f (G.rot x) * g x = f (G.rot x) * g (G.rot (G.rot x))
  rw [G.rot_involutive x]

/-- Cauchy–Schwarz for this inner product. -/
theorem ip_sq_le (f g : G.V × G.D → ℝ) : (ip G f g) ^ 2 ≤ ip G f f * ip G g g := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (G.V × G.D)) f g
  erw [ip, ip, ip]
  calc (∑ x : G.V × G.D, f x * g x) ^ 2
      ≤ (∑ x : G.V × G.D, f x ^ 2) * ∑ x : G.V × G.D, g x ^ 2 := h
    _ = (∑ x : G.V × G.D, f x * f x) * ∑ x : G.V × G.D, g x * g x := by
        rw [Finset.sum_congr rfl fun x _ => sq (f x),
          Finset.sum_congr rfl fun x _ => sq (g x)]

/-! ### The constant part is a function on `G` -/

/-- **Crossing acts on cloud-constant functions as `G`'s walk.** This is the
bridge that lets `G.SpectralBound` be applied to the product. -/
theorem cloudMean_crossStep_cloudPar (f : G.V × G.D → ℝ) (v : G.V) :
    cloudMean G (crossStep G (cloudPar G f)) v = G.step (cloudMean G f) v := by
  rw [cloudMean, RegGraph.step]
  congr 1

/-- The inner product of two cloud-constant functions is `G.deg` times the inner
product of the functions they come from. -/
theorem ip_cloudPar (f g : G.V × G.D → ℝ) :
    ip G (cloudPar G f) (cloudPar G g)
      = (G.deg : ℝ) * ∑ v : G.V, cloudMean G f v * cloudMean G g v := by
  erw [ip_eq_sum_clouds, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hconst : ∀ i : G.D, cloudPar G f (v, i) * cloudPar G g (v, i)
      = cloudMean G f v * cloudMean G g v := fun _ => rfl
  rw [Finset.sum_congr rfl fun i _ => hconst i, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rfl

/-- A mean-zero function on the product has mean-zero cloud averages. -/
theorem sum_cloudMean (f : G.V × G.D → ℝ) :
    ∑ v : G.V, cloudMean G f v = (∑ x : G.V × G.D, f x) / (G.deg : ℝ) := by
  rw [Fintype.sum_prod_type, Finset.sum_div]
  exact Finset.sum_congr rfl fun v _ => rfl

theorem sum_cloudMean_eq_zero {f : G.V × G.D → ℝ} (hf : ∑ x : G.V × G.D, f x = 0) :
    ∑ v : G.V, cloudMean G f v = 0 := by
  rw [sum_cloudMean, hf, zero_div]

/-- The sum of squares of the constant part, in terms of `G`. -/
theorem ip_cloudPar_self (f : G.V × G.D → ℝ) :
    ip G (cloudPar G f) (cloudPar G f)
      = (G.deg : ℝ) * ∑ v : G.V, (cloudMean G f v) ^ 2 := by
  rw [ip_cloudPar]
  congr 1
  exact Finset.sum_congr rfl fun v _ => (sq _).symm

/-- **The parallel–parallel term is `G`'s own quadratic form.** This is where
`G.SpectralBound` will enter the estimate. -/
theorem ip_cloudPar_crossStep (f : G.V × G.D → ℝ) :
    ip G (cloudPar G f) (crossStep G (cloudPar G f))
      = (G.deg : ℝ) * ∑ v : G.V, cloudMean G f v * G.step (cloudMean G f) v := by
  have hdeg : (G.deg : ℝ) ≠ 0 := G.deg_ne_zero
  erw [ip_eq_sum_clouds, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h : ∀ i : G.D, cloudPar G f (v, i) * crossStep G (cloudPar G f) (v, i)
      = cloudMean G f v * cloudMean G f (G.nbr v i) := fun _ => rfl
  erw [Finset.sum_congr rfl fun i _ => h i, ← Finset.mul_sum, RegGraph.step]
  field_simp

/-! ### Linearity -/

theorem cloudStep_add (f g : G.V × G.D → ℝ) (x : G.V × G.D) :
    cloudStep G H e (fun y => f y + g y) x = cloudStep G H e f x + cloudStep G H e g x := by
  erw [cloudStep, cloudStep, cloudStep, ← add_div]
  congr 1
  exact Finset.sum_add_distrib

theorem crossStep_add (f g : G.V × G.D → ℝ) (x : G.V × G.D) :
    crossStep G (fun y => f y + g y) x = crossStep G f x + crossStep G g x := rfl

theorem ip_add_left (f g h : G.V × G.D → ℝ) :
    ip G (fun x => f x + g x) h = ip G f h + ip G g h := by
  erw [ip, ip, ip, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem ip_add_right (f g h : G.V × G.D → ℝ) :
    ip G f (fun x => g x + h x) = ip G f g + ip G f h := by
  erw [ip, ip, ip, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- **One cloud move splits into the constant part and a contracted
remainder.** -/
theorem cloudStep_decomp (f : G.V × G.D → ℝ) (x : G.V × G.D) :
    cloudStep G H e f x = cloudPar G f x + cloudStep G H e (cloudPerp G f) x := by
  have hsplit : f = fun y => cloudPar G f y + cloudPerp G f y := by
    funext y
    rw [cloudPar_add_cloudPerp]
  conv_lhs => rw [hsplit]
  rw [cloudStep_add, cloudStep_cloudPar]

/-- The zig-zag walk, with the cloud move split on both sides. -/
theorem step_zigzag_decomp (f : (zigzag G H e).V → ℝ) :
    ip G f ((zigzag G H e).step f)
      = ip G (fun x => cloudPar G f x + cloudStep G H e (cloudPerp G f) x)
          (crossStep G (fun x => cloudPar G f x + cloudStep G H e (cloudPerp G f) x)) := by
  have hstep : ∀ x, (zigzag G H e).step f x
      = cloudStep G H e (crossStep G (cloudStep G H e f)) x := step_zigzag G H e f
  have hz : (zigzag G H e).step f = cloudStep G H e (crossStep G (cloudStep G H e f)) := by
    funext x
    exact hstep x
  erw [hz, ← ip_cloudStep]
  have hdec : cloudStep G H e f
      = fun x => cloudPar G f x + cloudStep G H e (cloudPerp G f) x := by
    funext x
    exact cloudStep_decomp G H e f x
  rw [hdec]

/-- **The four terms of the estimate.** -/
theorem ip_crossStep_expand (p q : G.V × G.D → ℝ) :
    ip G (fun x => p x + q x) (crossStep G (fun x => p x + q x))
      = ip G p (crossStep G p) + ip G p (crossStep G q)
        + ip G q (crossStep G p) + ip G q (crossStep G q) := by
  have hc : crossStep G (fun x => p x + q x)
      = fun x => crossStep G p x + crossStep G q x := by
    funext x
    exact crossStep_add G p q x
  erw [hc, ip_add_left, ip_add_right, ip_add_right]
  ring

/-- **The zig-zag quadratic form, expanded.** The first summand is `G`'s own
form on the cloud averages; the other three involve the contracted remainder. -/
theorem ip_step_zigzag_expand (f : (zigzag G H e).V → ℝ) :
    ip G f ((zigzag G H e).step f)
      = ip G (cloudPar G f) (crossStep G (cloudPar G f))
        + ip G (cloudPar G f) (crossStep G (cloudStep G H e (cloudPerp G f)))
        + ip G (cloudStep G H e (cloudPerp G f)) (crossStep G (cloudPar G f))
        + ip G (cloudStep G H e (cloudPerp G f))
            (crossStep G (cloudStep G H e (cloudPerp G f))) := by
  rw [step_zigzag_decomp, ip_crossStep_expand]

/-! ### The Rayleigh quotient -/

/-- **A spectral bound controls the quadratic form.** Cauchy–Schwarz turns the
bound on `‖step g‖` into one on `⟨g, step g⟩`, which is the form the zig-zag
estimate consumes. -/
theorem sum_mul_step_le_of_spectralBound (K : RegGraph) {lam : ℝ} (hK : K.SpectralBound lam)
    (hlam : 0 ≤ lam) (g : K.V → ℝ) (hg : ∑ v : K.V, g v = 0) :
    ∑ v : K.V, g v * K.step g v ≤ lam * ∑ v : K.V, (g v) ^ 2 := by
  set S := ∑ v : K.V, (g v) ^ 2 with hS
  set T := ∑ v : K.V, g v * K.step g v with hT
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset K.V) g (K.step g)
  have hspec := hK g hg
  have hT2 : T ^ 2 ≤ S * (lam ^ 2 * S) :=
    le_trans hcs (mul_le_mul_of_nonneg_left hspec hS0)
  nlinarith [hT2, mul_nonneg hlam hS0, sq_nonneg (T + lam * S)]

/-- The norm of the contracted remainder, over the whole product. -/
theorem ip_cloudStep_cloudPerp_le {lam : ℝ} (hH : H.SpectralBound lam)
    (f : G.V × G.D → ℝ) :
    ip G (cloudStep G H e (cloudPerp G f)) (cloudStep G H e (cloudPerp G f))
      ≤ lam ^ 2 * ip G (cloudPerp G f) (cloudPerp G f) := by
  erw [ip_eq_sum_clouds, ip_eq_sum_clouds, Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  have hb := sum_sq_cloudStep_cloudPerp_le G H e hH f v
  have hl : ∑ i : G.D, cloudStep G H e (cloudPerp G f) (v, i)
        * cloudStep G H e (cloudPerp G f) (v, i)
      = ∑ i : G.D, (cloudStep G H e (cloudPerp G f) (v, i)) ^ 2 :=
    Finset.sum_congr rfl fun i _ => (sq _).symm
  have hr : ∑ i : G.D, cloudPerp G f (v, i) * cloudPerp G f (v, i)
      = ∑ i : G.D, (cloudPerp G f (v, i)) ^ 2 :=
    Finset.sum_congr rfl fun i _ => (sq _).symm
  rw [hl, hr]
  exact hb

/-- **Term one of the estimate**: the constant part is bounded by `G`'s own
spectral bound. -/
theorem ip_cloudPar_crossStep_le {lam : ℝ} (hG : G.SpectralBound lam) (hlam : 0 ≤ lam)
    {f : G.V × G.D → ℝ} (hf : ∑ x : G.V × G.D, f x = 0) :
    ip G (cloudPar G f) (crossStep G (cloudPar G f))
      ≤ lam * ip G (cloudPar G f) (cloudPar G f) := by
  have hzero : ∑ v : G.V, cloudMean G f v = 0 := sum_cloudMean_eq_zero G hf
  have hray := sum_mul_step_le_of_spectralBound G hG hlam (cloudMean G f) hzero
  rw [ip_cloudPar_crossStep, ip_cloudPar_self]
  have hd : (0 : ℝ) ≤ (G.deg : ℝ) := by positivity
  calc (G.deg : ℝ) * ∑ v : G.V, cloudMean G f v * G.step (cloudMean G f) v
      ≤ (G.deg : ℝ) * (lam * ∑ v : G.V, (cloudMean G f v) ^ 2) :=
        mul_le_mul_of_nonneg_left hray hd
    _ = lam * ((G.deg : ℝ) * ∑ v : G.V, (cloudMean G f v) ^ 2) := by ring

/-! ### Orthogonality and a weighted bound -/

theorem ip_nonneg (g : G.V × G.D → ℝ) : 0 ≤ ip G g g :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- **The two parts are orthogonal.** The constant part is fixed along a cloud
while the remainder sums to zero there. -/
theorem ip_cloudPar_cloudPerp (f : G.V × G.D → ℝ) :
    ip G (cloudPar G f) (cloudPerp G f) = 0 := by
  rw [ip_eq_sum_clouds]
  refine Finset.sum_eq_zero fun v _ => ?_
  have h : ∀ i : G.D, cloudPar G f (v, i) * cloudPerp G f (v, i)
      = cloudMean G f v * cloudPerp G f (v, i) := fun _ => rfl
  erw [Finset.sum_congr rfl fun i _ => h i, ← Finset.mul_sum, sum_cloudPerp, mul_zero]

/-- **Pythagoras** for the splitting. -/
theorem ip_self_split (f : G.V × G.D → ℝ) :
    ip G f f = ip G (cloudPar G f) (cloudPar G f) + ip G (cloudPerp G f) (cloudPerp G f) := by
  have hsplit : f = fun y => cloudPar G f y + cloudPerp G f y := by
    funext y
    rw [cloudPar_add_cloudPerp]
  conv_lhs => rw [hsplit]
  rw [ip_add_left, ip_add_right, ip_add_right, ip_cloudPar_cloudPerp,
    ip_comm G (cloudPerp G f) (cloudPar G f), ip_cloudPar_cloudPerp]
  ring

/-- **The weighted arithmetic-geometric bound.** Expanding `0 ≤ ‖t u - w‖²`
avoids any square root, which keeps the estimate inside the ordered field. -/
theorem ip_two_mul_le (u w : G.V × G.D → ℝ) {t : ℝ} (ht : 0 < t) :
    2 * ip G u w ≤ t * ip G u u + ip G w w / t := by
  have hnn : 0 ≤ ∑ x : G.V × G.D, (t * u x - w x) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hexp : ∑ x : G.V × G.D, (t * u x - w x) ^ 2
      = t ^ 2 * ip G u u - 2 * t * ip G u w + ip G w w := by
    erw [ip, ip, ip, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hexp] at hnn
  have hmul : 2 * ip G u w * t ≤ (t * ip G u u + ip G w w / t) * t := by
    have ht' : t ≠ 0 := ne_of_gt ht
    field_simp
    nlinarith [hnn]
  exact le_of_mul_le_mul_right hmul ht

/-- The crossing move preserves the inner product with itself, in `ip` form. -/
theorem ip_crossStep_self (g : G.V × G.D → ℝ) :
    ip G (crossStep G g) (crossStep G g) = ip G g g := by
  erw [ip, ip]
  exact sum_sq_crossStep_aux G g

/-! ### The Reingold–Vadhan–Wigderson estimate -/

theorem eq_zero_of_ip_self_eq_zero {g : G.V × G.D → ℝ} (h : ip G g g = 0)
    (x : G.V × G.D) : g x = 0 := by
  have hmem := (Finset.sum_eq_zero_iff_of_nonneg
    (fun y (_ : y ∈ (Finset.univ : Finset (G.V × G.D))) => mul_self_nonneg (g y))).1 h x
    (Finset.mem_univ x)
  exact mul_self_eq_zero.1 hmem

/-- **The zig-zag product's quadratic form is bounded by
`lamG + lamH + lamH ^ 2`.** -/
theorem ip_step_zigzag_le {lamG lamH : ℝ} (hG : G.SpectralBound lamG)
    (hH : H.SpectralBound lamH) (hlamG : 0 ≤ lamG) (hlamH : 0 ≤ lamH)
    (f : (zigzag G H e).V → ℝ) (hf : ∑ x : G.V × G.D, f x = 0) :
    ip G f ((zigzag G H e).step f) ≤ (lamG + lamH + lamH ^ 2) * ip G f f := by
  set p := cloudPar G f with hp
  set r := cloudPerp G f with hr
  set q := cloudStep G H e r with hq
  set a := ip G p p with ha
  set b := ip G r r with hb
  have ha0 : 0 ≤ a := ip_nonneg G p
  have hb0 : 0 ≤ b := ip_nonneg G r
  have hqq : ip G q q ≤ lamH ^ 2 * b := ip_cloudStep_cloudPerp_le G H e hH f
  have hq0 : 0 ≤ ip G q q := ip_nonneg G q
  have hsplit : ip G f f = a + b := ip_self_split G f
  have hterm1 : ip G p (crossStep G p) ≤ lamG * a := ip_cloudPar_crossStep_le G hG hlamG hf
  have hsym : ip G q (crossStep G p) = ip G p (crossStep G q) := by
    erw [← ip_crossStep, ip_comm]
  have hcross : 2 * ip G p (crossStep G q) ≤ lamH * a + lamH * b := by
    rcases eq_or_lt_of_le hlamH with h0 | hpos
    · have hz : ip G q q = 0 := le_antisymm (by rw [← h0] at hqq; simpa using hqq) hq0
      have hqzero : ∀ x, q x = 0 := fun x => eq_zero_of_ip_self_eq_zero G hz x
      have : ip G p (crossStep G q) = 0 := by
        erw [ip]
        refine Finset.sum_eq_zero fun x _ => ?_
        show p x * q (G.rot x) = 0
        rw [hqzero, mul_zero]
      rw [this, ← h0]
      norm_num
    · have hb2 := ip_two_mul_le G p (crossStep G q) hpos
      rw [ip_crossStep_self] at hb2
      have hdiv : ip G q q / lamH ≤ lamH * b := by
        rw [div_le_iff₀ hpos]
        calc ip G q q ≤ lamH ^ 2 * b := hqq
          _ = lamH * b * lamH := by ring
      linarith
  have hterm4 : ip G q (crossStep G q) ≤ lamH ^ 2 * b := by
    have h1 := ip_two_mul_le G q (crossStep G q) (by norm_num : (0 : ℝ) < 1)
    rw [ip_crossStep_self] at h1
    linarith
  rw [ip_step_zigzag_expand, hsplit, ← hp, ← hr, ← hq]
  have hgb : 0 ≤ lamG * b := mul_nonneg hlamG hb0
  have hha : 0 ≤ lamH ^ 2 * a := mul_nonneg (sq_nonneg _) ha0
  linarith [hterm1, hcross, hterm4, hsym, hgb, hha]

/-! ### A walk is a contraction -/

/-- In inner-product form: the cloud move is a contraction. -/
theorem ip_cloudStep_le (g : G.V × G.D → ℝ) :
    ip G (cloudStep G H e g) (cloudStep G H e g) ≤ ip G g g := by
  rw [ip_eq_sum_clouds, ip_eq_sum_clouds]
  refine Finset.sum_le_sum fun v _ => ?_
  have hl : ∑ i : G.D, cloudStep G H e g (v, i) * cloudStep G H e g (v, i)
      = ∑ u : H.V, (H.step (cloudFun G H e g v) u) ^ 2 :=
    (Fintype.sum_equiv e (fun u => (H.step (cloudFun G H e g v) u) ^ 2)
      (fun i => cloudStep G H e g (v, i) * cloudStep G H e g (v, i)) fun u => by
        rw [cloudStep_apply, Equiv.symm_apply_apply, sq]).symm
  have hr : ∑ i : G.D, g (v, i) * g (v, i) = ∑ u : H.V, (cloudFun G H e g v u) ^ 2 :=
    (Fintype.sum_equiv e (fun u => (cloudFun G H e g v u) ^ 2)
      (fun i => g (v, i) * g (v, i)) fun u => by
        rw [sq]
        rfl).symm
  rw [hl, hr]
  exact H.sum_sq_step_le (cloudFun G H e g v)

/-! ### Two-sided forms -/

theorem ip_neg_left (u w : G.V × G.D → ℝ) :
    ip G (fun x => -u x) w = -ip G u w := by
  erw [ip, ip, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem ip_neg_self (u : G.V × G.D → ℝ) :
    ip G (fun x => -u x) (fun x => -u x) = ip G u u := by
  erw [ip, ip]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The weighted bound, two-sided. -/
theorem abs_ip_two_mul_le (u w : G.V × G.D → ℝ) {t : ℝ} (ht : 0 < t) :
    2 * |ip G u w| ≤ t * ip G u u + ip G w w / t := by
  have hpos := ip_two_mul_le G u w ht
  have hneg := ip_two_mul_le G (fun x => -u x) w ht
  rw [ip_neg_left, ip_neg_self] at hneg
  rcases abs_cases (ip G u w) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] <;> linarith

/-- **The Rayleigh quotient, two-sided.** -/
theorem abs_sum_mul_step_le (K : RegGraph) {lam : ℝ} (hK : K.SpectralBound lam)
    (hlam : 0 ≤ lam) (g : K.V → ℝ) (hg : ∑ v : K.V, g v = 0) :
    |∑ v : K.V, g v * K.step g v| ≤ lam * ∑ v : K.V, (g v) ^ 2 := by
  set S := ∑ v : K.V, (g v) ^ 2 with hS
  set T := ∑ v : K.V, g v * K.step g v with hT
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset K.V) g (K.step g)
  have hspec := hK g hg
  have hT2 : T ^ 2 ≤ S * (lam ^ 2 * S) :=
    le_trans hcs (mul_le_mul_of_nonneg_left hspec hS0)
  rw [abs_le]
  constructor
  · nlinarith [hT2, mul_nonneg hlam hS0, sq_nonneg (T - lam * S)]
  · nlinarith [hT2, mul_nonneg hlam hS0, sq_nonneg (T + lam * S)]

/-- **Term one, two-sided.** -/
theorem abs_ip_cloudPar_crossStep_le {lam : ℝ} (hG : G.SpectralBound lam) (hlam : 0 ≤ lam)
    {f : G.V × G.D → ℝ} (hf : ∑ x : G.V × G.D, f x = 0) :
    |ip G (cloudPar G f) (crossStep G (cloudPar G f))|
      ≤ lam * ip G (cloudPar G f) (cloudPar G f) := by
  have hzero : ∑ v : G.V, cloudMean G f v = 0 := sum_cloudMean_eq_zero G hf
  have hray := abs_sum_mul_step_le G hG hlam (cloudMean G f) hzero
  rw [ip_cloudPar_crossStep, ip_cloudPar_self, abs_mul,
    abs_of_nonneg (show (0:ℝ) ≤ (G.deg : ℝ) by positivity)]
  have hd : (0 : ℝ) ≤ (G.deg : ℝ) := by positivity
  calc (G.deg : ℝ) * |∑ v : G.V, cloudMean G f v * G.step (cloudMean G f) v|
      ≤ (G.deg : ℝ) * (lam * ∑ v : G.V, (cloudMean G f v) ^ 2) :=
        mul_le_mul_of_nonneg_left hray hd
    _ = lam * ((G.deg : ℝ) * ∑ v : G.V, (cloudMean G f v) ^ 2) := by ring

/-- **The RVW estimate, two-sided.** This is the form the conversion to
`SpectralBound` needs, since polarisation uses the bound on both signs. -/
theorem abs_ip_step_zigzag_le {lamG lamH : ℝ} (hG : G.SpectralBound lamG)
    (hH : H.SpectralBound lamH) (hlamG : 0 ≤ lamG) (hlamH : 0 ≤ lamH)
    (f : (zigzag G H e).V → ℝ) (hf : ∑ x : G.V × G.D, f x = 0) :
    |ip G f ((zigzag G H e).step f)| ≤ (lamG + lamH + lamH ^ 2) * ip G f f := by
  set p := cloudPar G f with hp
  set r := cloudPerp G f with hr
  set q := cloudStep G H e r with hq
  set a := ip G p p with ha
  set b := ip G r r with hb
  have ha0 : 0 ≤ a := ip_nonneg G p
  have hb0 : 0 ≤ b := ip_nonneg G r
  have hqq : ip G q q ≤ lamH ^ 2 * b := ip_cloudStep_cloudPerp_le G H e hH f
  have hq0 : 0 ≤ ip G q q := ip_nonneg G q
  have hsplit : ip G f f = a + b := ip_self_split G f
  have hterm1 : |ip G p (crossStep G p)| ≤ lamG * a :=
    abs_ip_cloudPar_crossStep_le G hG hlamG hf
  have hsym : ip G q (crossStep G p) = ip G p (crossStep G q) := by
    erw [← ip_crossStep, ip_comm]
  have hcross : 2 * |ip G p (crossStep G q)| ≤ lamH * a + lamH * b := by
    rcases eq_or_lt_of_le hlamH with h0 | hpos
    · have hz : ip G q q = 0 := le_antisymm (by rw [← h0] at hqq; simpa using hqq) hq0
      have hqzero : ∀ x, q x = 0 := fun x => eq_zero_of_ip_self_eq_zero G hz x
      have hzero2 : ip G p (crossStep G q) = 0 := by
        erw [ip]
        refine Finset.sum_eq_zero fun x _ => ?_
        show p x * q (G.rot x) = 0
        rw [hqzero, mul_zero]
      rw [hzero2, ← h0]
      norm_num
    · have hb2 := abs_ip_two_mul_le G p (crossStep G q) hpos
      rw [ip_crossStep_self] at hb2
      have hdiv : ip G q q / lamH ≤ lamH * b := by
        rw [div_le_iff₀ hpos]
        calc ip G q q ≤ lamH ^ 2 * b := hqq
          _ = lamH * b * lamH := by ring
      linarith
  have hterm4 : |ip G q (crossStep G q)| ≤ lamH ^ 2 * b := by
    have h1 := abs_ip_two_mul_le G q (crossStep G q) (by norm_num : (0 : ℝ) < 1)
    rw [ip_crossStep_self] at h1
    linarith
  rw [ip_step_zigzag_expand, hsplit, ← hp, ← hr, ← hq, hsym]
  have hgb : 0 ≤ lamG * b := mul_nonneg hlamG hb0
  have hha : 0 ≤ lamH ^ 2 * a := mul_nonneg (sq_nonneg _) ha0
  have hcross' : |ip G p (crossStep G q)| ≤ (lamH * a + lamH * b) / 2 := by linarith
  have h1 := abs_le.1 hterm1
  have h2 := abs_le.1 hcross'
  have h4 := abs_le.1 hterm4
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h4.1, h4.2, hgb, hha]

/-! ### From the quadratic form to the spectral bound -/

theorem step_sub (K : RegGraph) (f g : K.V → ℝ) (v : K.V) :
    K.step (fun w => f w - g w) v = K.step f v - K.step g v := by
  rw [RegGraph.step, RegGraph.step, RegGraph.step, ← sub_div]
  congr 1
  exact Finset.sum_sub_distrib (s := (Finset.univ : Finset K.D))
    (f := fun i => f (K.nbr v i)) (g := fun i => g (K.nbr v i))

theorem ip_sub_left (f g h : G.V × G.D → ℝ) :
    ip G (fun x => f x - g x) h = ip G f h - ip G g h := by
  erw [ip, ip, ip, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem ip_sub_right (f g h : G.V × G.D → ℝ) :
    ip G f (fun x => g x - h x) = ip G f g - ip G f h := by
  erw [ip, ip, ip, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The walk of the product is self-adjoint — it is a walk, like any other. -/
theorem ip_step_zigzag_comm (f g : G.V × G.D → ℝ) :
    ip G ((zigzag G H e).step f) g = ip G f ((zigzag G H e).step g) := by
  erw [ip, ip]
  exact (sum_mul_step_comm (zigzag G H e) f g).symm

/-- The sum of squares over the product's vertices, as an inner product. -/
theorem sum_sq_eq_ip (g : (zigzag G H e).V → ℝ) :
    ∑ v : (zigzag G H e).V, (g v) ^ 2 = ip G g g := by
  erw [ip]
  exact Finset.sum_congr rfl fun x _ => sq _

/-- **Polarisation.** -/
theorem ip_polarise (f g : G.V × G.D → ℝ) :
    4 * ip G ((zigzag G H e).step f) g
      = ip G ((zigzag G H e).step (fun x => f x + g x)) (fun x => f x + g x)
        - ip G ((zigzag G H e).step (fun x => f x - g x)) (fun x => f x - g x) := by
  have hadd : (zigzag G H e).step (fun x => f x + g x)
      = fun x => (zigzag G H e).step f x + (zigzag G H e).step g x := by
    funext x
    exact RegGraph.step_add (zigzag G H e) f g x
  have hsub : (zigzag G H e).step (fun x => f x - g x)
      = fun x => (zigzag G H e).step f x - (zigzag G H e).step g x := by
    funext x
    exact step_sub (zigzag G H e) f g x
  have hcross : ip G ((zigzag G H e).step g) f = ip G ((zigzag G H e).step f) g := by
    erw [ip_step_zigzag_comm, ip_comm]
  have key : ip G ((zigzag G H e).step (fun x => f x + g x)) (fun x => f x + g x)
      - ip G ((zigzag G H e).step (fun x => f x - g x)) (fun x => f x - g x)
      = 2 * ip G ((zigzag G H e).step f) g + 2 * ip G ((zigzag G H e).step g) f := by
    erw [hadd, hsub, ip, ip, ip, ip, ← Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [key, hcross]
  ring

/-- **The spectral bound of the zig-zag product.** -/
theorem spectralBound_zigzag {lamG lamH : ℝ} (hG : G.SpectralBound lamG)
    (hH : H.SpectralBound lamH) (hlamG : 0 ≤ lamG) (hlamH : 0 ≤ lamH) :
    (zigzag G H e).SpectralBound (lamG + lamH + lamH ^ 2) := by
  have hlam0 : (0 : ℝ) ≤ lamG + lamH + lamH ^ 2 := by positivity
  intro f hf
  have hf' : ∑ x : G.V × G.D, f x = 0 := hf
  have hmean : ∑ x : G.V × G.D, (zigzag G H e).step f x = ∑ x : G.V × G.D, f x :=
    RegGraph.sum_step (zigzag G H e) f
  have hTf0 : ∑ x : G.V × G.D, (zigzag G H e).step f x = 0 := by rw [hmean]; exact hf'
  have hA0 : 0 ≤ ip G ((zigzag G H e).step f) ((zigzag G H e).step f) := ip_nonneg G _
  -- the test vector `g = (1/lam) • T f`, or `T f` itself in the degenerate case
  have hmain : ∀ c : ℝ, 0 < c →
      2 * (ip G ((zigzag G H e).step f) ((zigzag G H e).step f) * c)
        ≤ (lamG + lamH + lamH ^ 2) * (ip G f f
            + c ^ 2 * ip G ((zigzag G H e).step f) ((zigzag G H e).step f)) := by
    intro c hc
    set g : G.V × G.D → ℝ := fun x => c * (zigzag G H e).step f x with hg
    have hg0 : ∑ x : G.V × G.D, g x = 0 := by
      erw [hg, ← Finset.mul_sum, hTf0, mul_zero]
    have hgg : ip G g g
        = c ^ 2 * ip G ((zigzag G H e).step f) ((zigzag G H e).step f) := by
      erw [hg, ip, ip, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    have hTfg : ip G ((zigzag G H e).step f) g
        = c * ip G ((zigzag G H e).step f) ((zigzag G H e).step f) := by
      erw [hg, ip, ip, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    have hpol := ip_polarise G H e f g
    have h1 := abs_ip_step_zigzag_le G H e hG hH hlamG hlamH
      (fun x => f x + g x) (by erw [Finset.sum_add_distrib, hf', hg0]; ring)
    have h2 := abs_ip_step_zigzag_le G H e hG hH hlamG hlamH
      (fun x => f x - g x) (by erw [Finset.sum_sub_distrib, hf', hg0]; ring)
    have hpar : ip G (fun x => f x + g x) (fun x => f x + g x)
        + ip G (fun x => f x - g x) (fun x => f x - g x)
        = 2 * ip G f f + 2 * ip G g g := by
      erw [ip_add_left, ip_add_right, ip_add_right, ip_sub_left, ip_sub_right,
        ip_sub_right, ip_comm G g f]
      ring
    have hb1 := abs_le.1 h1
    have hb2 := abs_le.1 h2
    have hswap1 : ip G ((zigzag G H e).step (fun x => f x + g x)) (fun x => f x + g x)
        = ip G (fun x => f x + g x) ((zigzag G H e).step (fun x => f x + g x)) :=
      ip_comm G _ _
    have hswap2 : ip G ((zigzag G H e).step (fun x => f x - g x)) (fun x => f x - g x)
        = ip G (fun x => f x - g x) ((zigzag G H e).step (fun x => f x - g x)) :=
      ip_comm G _ _
    rw [hTfg, hswap1, hswap2] at hpol
    rw [hgg] at hpar
    have hscaled : (lamG + lamH + lamH ^ 2)
        * ((ip G (fun x => f x + g x) (fun x => f x + g x))
          + ip G (fun x => f x - g x) (fun x => f x - g x))
        = (lamG + lamH + lamH ^ 2)
          * (2 * ip G f f
            + 2 * (c ^ 2 * ip G ((zigzag G H e).step f) ((zigzag G H e).step f))) := by
      rw [hpar]
    have hcomb : ip G (fun x => f x + g x) ((zigzag G H e).step (fun x => f x + g x))
        - ip G (fun x => f x - g x) ((zigzag G H e).step (fun x => f x - g x))
        ≤ (lamG + lamH + lamH ^ 2) * (ip G (fun x => f x + g x) (fun x => f x + g x))
          + (lamG + lamH + lamH ^ 2)
            * (ip G (fun x => f x - g x) (fun x => f x - g x)) := by
      have hq' : -(ip G (fun x => f x - g x)
            ((zigzag G H e).step (fun x => f x - g x)))
          ≤ (lamG + lamH + lamH ^ 2)
            * (ip G (fun x => f x - g x) (fun x => f x - g x)) :=
        neg_le_of_neg_le hb2.1
      have hsum := add_le_add hb1.2 hq'
      rw [sub_eq_add_neg]
      exact hsum
    linarith [hpol, hcomb, hscaled]
  rcases eq_or_lt_of_le hlam0 with h0 | hpos
  · have hc := hmain 1 one_pos
    rw [← h0] at hc
    have : ip G ((zigzag G H e).step f) ((zigzag G H e).step f) ≤ 0 := by linarith
    have hz : ip G ((zigzag G H e).step f) ((zigzag G H e).step f) = 0 :=
      le_antisymm this hA0
    show ∑ v : (zigzag G H e).V, ((zigzag G H e).step f v) ^ 2 ≤ _
    rw [sum_sq_eq_ip, sum_sq_eq_ip, hz, ← h0]
    norm_num
  · have hc := hmain (1 / (lamG + lamH + lamH ^ 2)) (by positivity)
    have hsimp : (lamG + lamH + lamH ^ 2)
        * (ip G f f + (1 / (lamG + lamH + lamH ^ 2)) ^ 2
            * ip G ((zigzag G H e).step f) ((zigzag G H e).step f))
        = (lamG + lamH + lamH ^ 2) * ip G f f
          + ip G ((zigzag G H e).step f) ((zigzag G H e).step f)
            / (lamG + lamH + lamH ^ 2) := by
      field_simp
    rw [hsimp] at hc
    have hkey : ip G ((zigzag G H e).step f) ((zigzag G H e).step f)
        / (lamG + lamH + lamH ^ 2) ≤ (lamG + lamH + lamH ^ 2) * ip G f f := by
      have h2c : 2 * (ip G ((zigzag G H e).step f) ((zigzag G H e).step f)
          * (1 / (lamG + lamH + lamH ^ 2)))
          = 2 * (ip G ((zigzag G H e).step f) ((zigzag G H e).step f)
              / (lamG + lamH + lamH ^ 2)) := by
        field_simp
      rw [h2c] at hc
      linarith
    rw [div_le_iff₀ hpos] at hkey
    show ∑ v : (zigzag G H e).V, ((zigzag G H e).step f v) ^ 2 ≤ _
    rw [sum_sq_eq_ip, sum_sq_eq_ip]
    nlinarith [hkey]

end RegGraph

end Complexity
