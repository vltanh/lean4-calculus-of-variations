/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Basic
public import CalculusOfVariations.Lipschitz.Gradient
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Piecewise affine maps and Kuhn–Freudenthal interpolation

* `PiecewiseAffineOn U φ`: `φ` agrees with an affine map on each of finitely many pairwise
  disjoint open subsets of `U` that cover `U` up to a null set;
* `kuhnInterpolation k ψ`: the piecewise affine interpolation of `ψ` on the Kuhn–Freudenthal
  triangulation of the grid `k⁻¹ ℤ^m` (H. Freudenthal, Ann. of Math. 43 (1942); H. W. Kuhn,
  1960), in the closed form `I_k ψ (x) = ∫_0^1 ψ (k⁻¹ ⌈k x − t 𝟙⌉) dt` (ceiling coordinatewise).
  For `x` in the open simplex `{⌊k x⌋ = a, fractional parts of k x ordered by σ}` the nodes
  `k⁻¹ ⌈k x − t 𝟙⌉` run through the vertices of that simplex, with weights the barycentric
  coordinates of `x`, so `I_k ψ` is the affine interpolant of the values of `ψ` at the vertices.

## Main results

All proved, along the closed form of the Kuhn–Freudenthal triangulation. Write `r = k x − a`.

* `kuhnInterpolation_lipschitz`: `I_k ψ` is `m K`-Lipschitz for `K`-Lipschitz `ψ` (sup norms):
  `∫_0^1 ⌈u − t⌉ dt = u` and the monotonicity of `u ↦ ⌈u − t⌉` give
  `∫_0^1 |⌈u − t⌉ − ⌈u' − t⌉| dt = |u − u'|`, and summing over the coordinates gives the bound;
* `kuhnInterpolation_eq_zero`: `I_k ψ` vanishes off the unit cube when `ψ` does, since the nodes
  of a point off the cube are off the cube for `0 < t < 1`;
* `kuhnInterpolation_eq_kuhnAffine`: on the cell `{a ≤ k x < a + 1, r ∘ σ monotone}`, `I_k ψ` is
  the affine map `kuhnAffine k ψ a σ`, `x ↦ ψ (v_m) + ∑_j r_{σ j} (ψ (v_j) − ψ (v_{j + 1}))`, with
  the vertices `v_s = kuhnVertex k a σ s = k⁻¹ (a + 𝟙_{σ '' {s, …, m − 1}})`: for `0 < t < 1` the
  node is `k⁻¹ (a + 𝟙_{r > t})`, and `ψ` of it telescopes into
  `ψ (v_m) + ∑_j 𝟙_{t < r_{σ j}} (ψ (v_j) − ψ (v_{j + 1}))`, which is integrated term by term;
* `kuhnInterpolation_piecewiseAffineOn`: for `k ≥ 1` the pieces are the open Kuhn simplices
  `kuhnSimplex k a σ` (`a ∈ {0, …, k − 1}^m`), pairwise disjoint since `a = ⌊k x⌋` and `σ` sorts
  `r`; the rest of the cube lies in the null hyperplanes `{x_i = q}`, `{x_i − x_{i'} = q}`
  (`q ∈ ℚ`, `i ≠ i'`);
* `kuhnInterpolation_grad_uniform`: for a `C¹` map `ψ` with compact support the gradients converge
  uniformly, `|∇ I_k ψ − ∇ψ| ≤ ε` entrywise almost everywhere for `k` large: this is the piecewise
  affine approximation of a smooth map on a fine regular triangulation (S. Müller, lecture notes,
  MPI MiS Leipzig 1998, proof of Theorem 4.4 (i)). Off the null hyperplanes, `x` lies for every
  `k ≥ 1` in an open Kuhn simplex, where the column `σ s` of `∇ I_k ψ` is the difference quotient
  `k (ψ (v_s) − ψ (v_{s + 1}))` along an edge of length `k⁻¹` with ends within `k⁻¹` of `x`
  (`kuhnInterpolation_grad`). By the mean value theorem its entry `i` is `∂_{σ s} ψ_i (ξ)` at a
  point `ξ` of the edge, and the uniform continuity of `Dψ` (continuous with compact support)
  makes it `ε`-close to `∂_{σ s} ψ_i (x)` once `k⁻¹` is small.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace CalculusOfVariations

variable {d m : ℕ}

/-- `φ` is piecewise affine on `U`: there are finitely many pairwise disjoint open sets `P i ⊆ U`,
covering `U` up to a null set, on each of which `φ` agrees with an affine map `L i`. -/
def PiecewiseAffineOn (U : Set (Fin m → ℝ)) (φ : (Fin m → ℝ) → Fin d → ℝ) : Prop :=
  ∃ (n : ℕ) (P : Fin n → Set (Fin m → ℝ)) (L : Fin n → (Fin m → ℝ) →ᵃ[ℝ] (Fin d → ℝ)),
    (∀ i, IsOpen (P i)) ∧ Pairwise (Function.onFun Disjoint P) ∧ (∀ i, P i ⊆ U) ∧
      volume (U \ ⋃ i, P i) = 0 ∧ ∀ i, ∀ x ∈ P i, φ x = L i x

/-- The Kuhn–Freudenthal interpolation of `ψ` on the grid `k⁻¹ ℤ^m`:
`I_k ψ (x) = ∫_0^1 ψ (k⁻¹ ⌈k x − t 𝟙⌉) dt`, the ceiling taken coordinatewise. -/
noncomputable def kuhnInterpolation (k : ℕ) (ψ : (Fin m → ℝ) → Fin d → ℝ) (x : Fin m → ℝ) :
    Fin d → ℝ :=
  ∫ t in (0 : ℝ)..1, ψ (fun i => (k : ℝ)⁻¹ * ⌈(k : ℝ) * x i - t⌉)

/-! ### One-dimensional facts -/

/-- For `a ≤ u < a + 1` and `0 ≤ t < 1`: `⌈u − t⌉ = a + 1` if `t < u − a`, and `⌈u − t⌉ = a`
otherwise. -/
private lemma kuhn_ceil_sub {u t : ℝ} {a : ℤ} (ha : (a : ℝ) ≤ u) (ha' : u < a + 1)
    (ht : 0 ≤ t) (ht' : t < 1) :
    ((⌈u - t⌉ : ℤ) : ℝ) = a + if t < u - a then 1 else 0 := by
  split_ifs with h
  · have : ⌈u - t⌉ = a + 1 := by
      rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
    rw [this]; push_cast; ring
  · have : ⌈u - t⌉ = a := by
      rw [Int.ceil_eq_iff]; have h := not_lt.1 h; constructor <;> linarith
    rw [this]; ring

/-- An interval integral over `[0, 1]` is the integral over `(0, 1)`. -/
private lemma kuhn_intervalIntegral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : ∫ t in (0 : ℝ)..1, f t = ∫ t in Set.Ioo (0 : ℝ) 1, f t := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

private lemma kuhn_step_eq_indicator {E : Type*} [Zero E] (r : ℝ) (c : E) :
    (fun t : ℝ => if t < r then c else 0) = (Set.Iio r).indicator fun _ => c := by
  funext t
  simp [Set.indicator_apply]

/-- The step function `t ↦ c 𝟙_{t < r}` is integrable on `(0, 1)`. -/
private lemma kuhn_integrableOn_step {E : Type*} [NormedAddCommGroup E] (r : ℝ) (c : E) :
    IntegrableOn (fun t : ℝ => if t < r then c else 0) (Set.Ioo 0 1) := by
  rw [kuhn_step_eq_indicator]
  exact (integrableOn_const (by simp [Real.volume_Ioo])).indicator measurableSet_Iio

/-- `∫_0^1 c 𝟙_{t < r} dt = r c` for `0 ≤ r ≤ 1`. -/
private lemma kuhn_integral_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (c : E) :
    ∫ t in Set.Ioo (0 : ℝ) 1, (if t < r then c else 0) = r • c := by
  rw [kuhn_step_eq_indicator, setIntegral_indicator measurableSet_Iio, Set.Ioo_inter_Iio,
    min_eq_right hr1, setIntegral_const, Real.volume_real_Ioo, sub_zero, max_eq_left hr0]

private lemma kuhn_volume_real_Ioo : volume.real (Set.Ioo (0 : ℝ) 1) = 1 := by
  simp [Real.volume_real_Ioo]

/-- On `(0, 1)`, `t ↦ ⌈u − t⌉` is the step function `⌊u⌋ + 𝟙_{t < u − ⌊u⌋}`. -/
private lemma kuhn_ceil_eqOn (u : ℝ) :
    Set.EqOn (fun t : ℝ => ((⌈u - t⌉ : ℤ) : ℝ))
      (fun t => (⌊u⌋ : ℝ) + if t < u - ⌊u⌋ then 1 else 0) (Set.Ioo 0 1) := fun _ ht =>
  kuhn_ceil_sub (Int.floor_le u) (Int.lt_floor_add_one u) ht.1.le ht.2

private lemma kuhn_integrableOn_ceil (u : ℝ) :
    IntegrableOn (fun t : ℝ => ((⌈u - t⌉ : ℤ) : ℝ)) (Set.Ioo 0 1) := by
  refine IntegrableOn.congr_fun ?_ (kuhn_ceil_eqOn u).symm measurableSet_Ioo
  exact (integrableOn_const (by simp [Real.volume_Ioo])).add (kuhn_integrableOn_step _ _)

/-- `∫_0^1 ⌈u − t⌉ dt = u`. -/
private lemma kuhn_integral_ceil (u : ℝ) :
    ∫ t in Set.Ioo (0 : ℝ) 1, ((⌈u - t⌉ : ℤ) : ℝ) = u := by
  rw [setIntegral_congr_fun measurableSet_Ioo (kuhn_ceil_eqOn u),
    integral_add (integrableOn_const (by simp [Real.volume_Ioo])) (kuhn_integrableOn_step _ _),
    setIntegral_const, kuhn_volume_real_Ioo,
    kuhn_integral_step (sub_nonneg.2 (Int.floor_le u)) (by linarith [Int.lt_floor_add_one u])]
  simp

/-- `∫_0^1 |⌈u − t⌉ − ⌈u' − t⌉| dt = |u − u'|`. -/
private lemma kuhn_integral_abs_ceil_sub (u u' : ℝ) :
    ∫ t in Set.Ioo (0 : ℝ) 1, |((⌈u - t⌉ : ℤ) : ℝ) - ⌈u' - t⌉| = |u - u'| := by
  wlog h : u ≤ u' generalizing u u'
  · rw [abs_sub_comm u u', ← this u' u (le_of_not_ge h)]
    congr 1
    funext t
    exact abs_sub_comm _ _
  have hle : ∀ t : ℝ, ((⌈u - t⌉ : ℤ) : ℝ) ≤ ⌈u' - t⌉ := fun t => by
    exact_mod_cast Int.ceil_mono (by linarith)
  simp_rw [abs_of_nonpos (sub_nonpos.2 (hle _)), abs_of_nonpos (sub_nonpos.2 h), neg_sub]
  rw [integral_sub (kuhn_integrableOn_ceil u') (kuhn_integrableOn_ceil u), kuhn_integral_ceil,
    kuhn_integral_ceil]

/-! ### The nodes -/

/-- The node `k⁻¹ ⌈k x − t 𝟙⌉`. -/
private noncomputable def kuhnNode (k : ℕ) (x : Fin m → ℝ) (t : ℝ) : Fin m → ℝ :=
  fun i => (k : ℝ)⁻¹ * ⌈(k : ℝ) * x i - t⌉

private lemma kuhnInterpolation_eq_setIntegral (k : ℕ) (ψ : (Fin m → ℝ) → Fin d → ℝ)
    (x : Fin m → ℝ) :
    kuhnInterpolation k ψ x = ∫ t in Set.Ioo (0 : ℝ) 1, ψ (kuhnNode k x t) :=
  kuhn_intervalIntegral_eq _

private lemma kuhn_measurable_node (k : ℕ) (x : Fin m → ℝ) : Measurable (kuhnNode k x) := by
  unfold kuhnNode
  fun_prop

/-- For `k ≥ 1` and `0 < t < 1` the node is within `1` of `x`. -/
private lemma kuhn_norm_node_sub_le {k : ℕ} (hk : 0 < k) (x : Fin m → ℝ) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) : ‖kuhnNode k x t - x‖ ≤ 1 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  have h1 := Int.le_ceil ((k : ℝ) * x i - t)
  have h2 := Int.ceil_lt_add_one ((k : ℝ) * x i - t)
  have he : kuhnNode k x t i - x i = (k : ℝ)⁻¹ * (⌈(k : ℝ) * x i - t⌉ - k * x i) := by
    simp only [kuhnNode]
    field_simp
  rw [Pi.sub_apply, Real.norm_eq_abs, he, abs_mul, abs_inv, Nat.abs_cast]
  have hb : |((⌈(k : ℝ) * x i - t⌉ : ℤ) : ℝ) - k * x i| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  calc (k : ℝ)⁻¹ * |((⌈(k : ℝ) * x i - t⌉ : ℤ) : ℝ) - k * x i| ≤ 1 * 1 := by
        gcongr
        exact inv_le_one_of_one_le₀ hk'
    _ = 1 := one_mul 1

private lemma kuhn_integrableOn_node {ψ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hψ : LipschitzWith K ψ) {k : ℕ} (hk : 0 < k) (x : Fin m → ℝ) :
    IntegrableOn (fun t => ψ (kuhnNode k x t)) (Set.Ioo 0 1) := by
  refine Measure.integrableOn_of_bounded (M := ‖ψ x‖ + K) (by simp [Real.volume_Ioo])
    ((hψ.continuous.measurable.comp (kuhn_measurable_node k x)).aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun t ht => ?_
  calc ‖ψ (kuhnNode k x t)‖ ≤ ‖ψ x‖ + ‖ψ (kuhnNode k x t) - ψ x‖ := norm_le_insert' _ _
    _ ≤ ‖ψ x‖ + K * ‖kuhnNode k x t - x‖ := by gcongr; exact hψ.norm_sub_le _ _
    _ ≤ ‖ψ x‖ + K * 1 := by gcongr; exact kuhn_norm_node_sub_le hk x ht
    _ = _ := by ring

/-! ### Lipschitz bound and vanishing off the cube -/

/-- The interpolation of a `K`-Lipschitz map is `m K`-Lipschitz (sup norms). -/
theorem kuhnInterpolation_lipschitz {ψ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hψ : LipschitzWith K ψ) (k : ℕ) : LipschitzWith (m * K) (kuhnInterpolation k ψ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : kuhnInterpolation 0 ψ = fun _ => ψ (fun _ => 0) := by
      funext x
      simp [kuhnInterpolation]
    rw [h0]
    exact LipschitzWith.const' _
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  rw [dist_eq_norm, dist_eq_norm, kuhnInterpolation_eq_setIntegral,
    kuhnInterpolation_eq_setIntegral,
    ← integral_sub (kuhn_integrableOn_node hψ hk x) (kuhn_integrableOn_node hψ hk x')]
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  set g : ℝ → ℝ := fun t => K * ∑ i, (k : ℝ)⁻¹ *
    |((⌈(k : ℝ) * x i - t⌉ : ℤ) : ℝ) - ⌈(k : ℝ) * x' i - t⌉| with hg
  have hi : ∀ i, IntegrableOn (fun t : ℝ => (k : ℝ)⁻¹ *
      |((⌈(k : ℝ) * x i - t⌉ : ℤ) : ℝ) - ⌈(k : ℝ) * x' i - t⌉|) (Set.Ioo 0 1) := fun i =>
    ((kuhn_integrableOn_ceil _).sub (kuhn_integrableOn_ceil _)).abs.const_mul _
  have hgi : IntegrableOn g (Set.Ioo 0 1) :=
    Integrable.const_mul (integrable_finsetSum _ fun i _ => hi i) _
  have hpt : ∀ t, ‖ψ (kuhnNode k x t) - ψ (kuhnNode k x' t)‖ ≤ g t := by
    intro t
    refine (hψ.norm_sub_le _ _).trans (mul_le_mul_of_nonneg_left ?_ K.2)
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)).2 fun i => ?_
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun i => (k : ℝ)⁻¹ *
      |((⌈(k : ℝ) * x i - t⌉ : ℤ) : ℝ) - ⌈(k : ℝ) * x' i - t⌉|) (fun i _ => by positivity)
      (Finset.mem_univ i))
    simp only [kuhnNode, Pi.sub_apply, Real.norm_eq_abs, ← mul_sub, abs_mul, abs_inv, Nat.abs_cast]
  have hint : ∫ t in Set.Ioo (0 : ℝ) 1, g t = K * ∑ i, |x i - x' i| := by
    rw [hg, integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, kuhn_integral_abs_ceil_sub, ← mul_sub, abs_mul, Nat.abs_cast,
      ← mul_assoc, inv_mul_cancel₀ hk'.ne', one_mul]
  calc ‖∫ t in Set.Ioo (0 : ℝ) 1, (ψ (kuhnNode k x t) - ψ (kuhnNode k x' t))‖
      ≤ ∫ t in Set.Ioo (0 : ℝ) 1, ‖ψ (kuhnNode k x t) - ψ (kuhnNode k x' t)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioo (0 : ℝ) 1, g t :=
        integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _) hgi
          (Eventually.of_forall hpt)
    _ = K * ∑ i, |x i - x' i| := hint
    _ ≤ K * ∑ _i : Fin m, ‖x - x'‖ := by
        gcongr with i
        exact norm_le_pi_norm (x - x') i
    _ = ((m * K : NNReal) : ℝ) * ‖x - x'‖ := by simp; ring

/-- The interpolation of a map vanishing off the unit cube vanishes off the unit cube. -/
theorem kuhnInterpolation_eq_zero {ψ : (Fin m → ℝ) → Fin d → ℝ}
    (hψ : ∀ x ∉ unitCube m, ψ x = 0) (k : ℕ) :
    ∀ x ∉ unitCube m, kuhnInterpolation k ψ x = 0 := by
  intro x hx
  rw [kuhnInterpolation_eq_setIntegral]
  refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => hψ _ ?_
  simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx ⊢
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, fun hn => ?_⟩
  simp only [kuhnNode, Set.mem_Ioo] at hn hi ht
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rcases le_or_gt (x i) 0 with h0 | h0
  · have hc : ⌈(k : ℝ) * x i - t⌉ ≤ 0 :=
      Int.ceil_le.2 (by push_cast; nlinarith [mul_nonpos_of_nonneg_of_nonpos hk0 h0])
    have : (k : ℝ)⁻¹ * ((⌈(k : ℝ) * x i - t⌉ : ℤ) : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hk0) (by exact_mod_cast hc)
    linarith [hn.1]
  · have h1 : 1 ≤ x i := by
      by_contra h
      exact hi ⟨h0, not_le.1 h⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hn
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hc : ((k : ℤ) - 1) < ⌈(k : ℝ) * x i - t⌉ :=
      Int.lt_ceil.2 (by push_cast; nlinarith)
    have hc' : (k : ℝ) ≤ ((⌈(k : ℝ) * x i - t⌉ : ℤ) : ℝ) := by
      have : (k : ℤ) ≤ ⌈(k : ℝ) * x i - t⌉ := by omega
      exact_mod_cast this
    have : 1 ≤ (k : ℝ)⁻¹ * ((⌈(k : ℝ) * x i - t⌉ : ℤ) : ℝ) := by
      rw [le_inv_mul_iff₀ (by linarith)]
      linarith
    linarith [hn.2]

/-! ### The affine form on a Kuhn simplex -/

/-- The vertex `k⁻¹ (a + 𝟙_{σ '' {s, …, m − 1}})` of the Kuhn simplex `kuhnSimplex k a σ`
(`s : ℕ`; for `s ≥ m` it is `k⁻¹ a`). -/
noncomputable def kuhnVertex (k : ℕ) (a : Fin m → ℤ) (σ : Equiv.Perm (Fin m)) (s : ℕ) :
    Fin m → ℝ :=
  fun i => (k : ℝ)⁻¹ * ((a i : ℝ) + if s ≤ (σ.symm i : ℕ) then 1 else 0)

/-- Consecutive vertices of a Kuhn simplex differ by `k⁻¹ e_{σ s}`. -/
theorem kuhnVertex_eq_add (k : ℕ) (a : Fin m → ℤ) (σ : Equiv.Perm (Fin m)) (s : Fin m) :
    kuhnVertex k a σ s = kuhnVertex k a σ ((s : ℕ) + 1) + (k : ℝ)⁻¹ • Pi.single (σ s) 1 := by
  funext i
  simp only [kuhnVertex, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i = σ s
  · subst hi
    simp
    ring
  · have hs : (σ.symm i : ℕ) ≠ s := fun h => hi (by rw [← Fin.ext h]; simp)
    have h : (s : ℕ) ≤ σ.symm i ↔ (s : ℕ) + 1 ≤ σ.symm i := by omega
    simp [h, Pi.single_eq_of_ne hi]

/-- The open Kuhn simplex `{x : a_i < k x_i < a_i + 1, r_{σ 0} < ⋯ < r_{σ (m − 1)}}`
(`r = k x − a`) of the grid `k⁻¹ ℤ^m`. -/
def kuhnSimplex (k : ℕ) (a : Fin m → ℤ) (σ : Equiv.Perm (Fin m)) : Set (Fin m → ℝ) :=
  {x | (∀ i, (a i : ℝ) < k * x i ∧ (k : ℝ) * x i < a i + 1) ∧
    StrictMono fun j => (k : ℝ) * x (σ j) - a (σ j)}

/-- Kuhn simplices are open. -/
theorem kuhnSimplex_isOpen (k : ℕ) (a : Fin m → ℤ) (σ : Equiv.Perm (Fin m)) :
    IsOpen (kuhnSimplex k a σ) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨hx, hσ⟩
  have h1 : ∀ᶠ y in 𝓝 x, ∀ i, (a i : ℝ) < k * y i ∧ (k : ℝ) * y i < a i + 1 :=
    eventually_all.2 fun i =>
      (ContinuousAt.eventually_lt (f := fun _ => (a i : ℝ))
        (g := fun y : Fin m → ℝ => (k : ℝ) * y i) continuousAt_const
        (continuous_const.mul (continuous_apply i)).continuousAt (hx i).1).and
      (ContinuousAt.eventually_lt (f := fun y : Fin m → ℝ => (k : ℝ) * y i)
        (g := fun _ => (a i : ℝ) + 1) (continuous_const.mul (continuous_apply i)).continuousAt
        continuousAt_const (hx i).2)
  have h2 : ∀ᶠ y in 𝓝 x, ∀ j j' : Fin m, j < j' →
      (k : ℝ) * y (σ j) - a (σ j) < (k : ℝ) * y (σ j') - a (σ j') := by
    refine eventually_all.2 fun j => eventually_all.2 fun j' => ?_
    by_cases hjj : j < j'
    · filter_upwards [ContinuousAt.eventually_lt
        (f := fun y : Fin m → ℝ => (k : ℝ) * y (σ j) - a (σ j))
        (g := fun y : Fin m → ℝ => (k : ℝ) * y (σ j') - a (σ j'))
        ((continuous_const.mul (continuous_apply _)).sub continuous_const).continuousAt
        ((continuous_const.mul (continuous_apply _)).sub continuous_const).continuousAt
        (hσ hjj)] with y hy _ using hy
    · exact Eventually.of_forall fun y h => absurd h hjj
  filter_upwards [h1, h2] with y hy1 hy2
  exact ⟨hy1, fun j j' h => hy2 j j' h⟩

/-- The affine map `x ↦ ψ (v_m) + ∑_j (k x_{σ j} − a_{σ j}) (ψ (v_j) − ψ (v_{j + 1}))`,
`v_s = kuhnVertex k a σ s`: the affine interpolant of `ψ` at the vertices of
`kuhnSimplex k a σ`. -/
noncomputable def kuhnAffine (k : ℕ) (ψ : (Fin m → ℝ) → Fin d → ℝ) (a : Fin m → ℤ)
    (σ : Equiv.Perm (Fin m)) : (Fin m → ℝ) →ᵃ[ℝ] (Fin d → ℝ) where
  toFun x := ψ (kuhnVertex k a σ m) + ∑ j : Fin m, ((k : ℝ) * x (σ j) - a (σ j)) •
    (ψ (kuhnVertex k a σ j) - ψ (kuhnVertex k a σ ((j : ℕ) + 1)))
  linear := ∑ j : Fin m, ((k : ℝ) • LinearMap.proj (σ j)).smulRight
    (ψ (kuhnVertex k a σ j) - ψ (kuhnVertex k a σ ((j : ℕ) + 1)))
  map_vadd' p v := by
    simp only [vadd_eq_add, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.smul_apply, LinearMap.proj_apply, Pi.add_apply, smul_eq_mul]
    rw [add_left_comm, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← add_smul]
    congr 1
    ring

/-- The values of `kuhnAffine k ψ a σ`. -/
theorem kuhnAffine_apply (k : ℕ) (ψ : (Fin m → ℝ) → Fin d → ℝ) (a : Fin m → ℤ)
    (σ : Equiv.Perm (Fin m)) (x : Fin m → ℝ) :
    kuhnAffine k ψ a σ x = ψ (kuhnVertex k a σ m) + ∑ j : Fin m, ((k : ℝ) * x (σ j) - a (σ j)) •
      (ψ (kuhnVertex k a σ j) - ψ (kuhnVertex k a σ ((j : ℕ) + 1))) :=
  rfl

/-- The linear part of `kuhnAffine k ψ a σ` on the basis vector `e_{σ s}`:
`k (ψ (w_s + k⁻¹ e_{σ s}) − ψ (w_s))`, `w_s = kuhnVertex k a σ (s + 1)`. -/
theorem kuhnAffine_linear_single (k : ℕ) (ψ : (Fin m → ℝ) → Fin d → ℝ) (a : Fin m → ℤ)
    (σ : Equiv.Perm (Fin m)) (s : Fin m) :
    (kuhnAffine k ψ a σ).linear (Pi.single (σ s) 1) =
      (k : ℝ) • (ψ (kuhnVertex k a σ ((s : ℕ) + 1) + (k : ℝ)⁻¹ • Pi.single (σ s) 1) -
        ψ (kuhnVertex k a σ ((s : ℕ) + 1))) := by
  rw [← kuhnVertex_eq_add]
  simp only [kuhnAffine, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single s]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne (σ.injective.ne hj)]
  · simp

/-- On the closed Kuhn cell `{a_i ≤ k x_i < a_i + 1, r_{σ 0} ≤ ⋯ ≤ r_{σ (m − 1)}}`
(`r = k x − a`) the interpolation is the affine map `kuhnAffine k ψ a σ`. For `0 < t < 1` the
node `k⁻¹ ⌈k x − t 𝟙⌉` is `k⁻¹ (a + 𝟙_{r > t})`; with the partial nodes
`N_s = k⁻¹ (a + 𝟙_{r > t, σ⁻¹ ≥ s})` it telescopes as
`ψ (node) = ψ (v_m) + ∑_j 𝟙_{t < r_{σ j}} (ψ (v_j) − ψ (v_{j + 1}))`, which integrates to the
affine form. -/
theorem kuhnInterpolation_eq_kuhnAffine (k : ℕ) (ψ : (Fin m → ℝ) → Fin d → ℝ) (a : Fin m → ℤ)
    (σ : Equiv.Perm (Fin m)) {x : Fin m → ℝ}
    (hx : ∀ i, (a i : ℝ) ≤ k * x i ∧ (k : ℝ) * x i < a i + 1)
    (hσ : Monotone fun j => (k : ℝ) * x (σ j) - a (σ j)) :
    kuhnInterpolation k ψ x = kuhnAffine k ψ a σ x := by
  set r : Fin m → ℝ := fun i => (k : ℝ) * x i - a i with hr
  set D : Fin m → Fin d → ℝ := fun j =>
    ψ (kuhnVertex k a σ j) - ψ (kuhnVertex k a σ ((j : ℕ) + 1)) with hD
  have hpt : Set.EqOn (fun t => ψ (kuhnNode k x t))
      (fun t => ψ (kuhnVertex k a σ m) + ∑ j : Fin m, if t < r (σ j) then D j else 0)
      (Set.Ioo 0 1) := by
    intro t ht
    set N : ℕ → Fin m → ℝ := fun s i =>
      (k : ℝ)⁻¹ * ((a i : ℝ) + if s ≤ (σ.symm i : ℕ) ∧ t < r i then 1 else 0) with hN
    have hN0 : kuhnNode k x t = N 0 := by
      funext i
      simp only [kuhnNode, hN, zero_le, true_and]
      rw [kuhn_ceil_sub (hx i).1 (hx i).2 ht.1.le ht.2]
    have hNm : N m = kuhnVertex k a σ m := by
      funext i
      have : ¬ m ≤ (σ.symm i : ℕ) := not_le.2 (σ.symm i).2
      simp [hN, kuhnVertex, this]
    have hstep : ∀ j : Fin m,
        ψ (N j) - ψ (N ((j : ℕ) + 1)) = if t < r (σ j) then D j else 0 := by
      intro j
      split_ifs with htj
      · have hle : ∀ i, (j : ℕ) ≤ σ.symm i → t < r i := fun i hji => by
          have := hσ (show j ≤ σ.symm i from Fin.le_def.2 hji)
          simp only [Equiv.apply_symm_apply] at this
          exact htj.trans_le this
        have e1 : N j = kuhnVertex k a σ j := by
          funext i
          simp only [hN, kuhnVertex]
          congr 2
          exact if_congr (and_iff_left_of_imp (hle i)) rfl rfl
        have e2 : N ((j : ℕ) + 1) = kuhnVertex k a σ ((j : ℕ) + 1) := by
          funext i
          simp only [hN, kuhnVertex]
          congr 2
          exact if_congr (and_iff_left_of_imp fun h => hle i (by omega)) rfl rfl
        rw [e1, e2]
      · have e : N j = N ((j : ℕ) + 1) := by
          funext i
          simp only [hN]
          congr 2
          refine if_congr ?_ rfl rfl
          by_cases hij : σ.symm i = j
          · have : i = σ j := by rw [← hij, Equiv.apply_symm_apply]
            subst this
            simp [htj]
          · have : (σ.symm i : ℕ) ≠ j := fun h => hij (Fin.ext h)
            constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
        rw [e, sub_self]
    have htel := Finset.sum_range_sub' (fun s => ψ (N s)) m
    rw [← Fin.sum_univ_eq_sum_range (fun s => ψ (N s) - ψ (N (s + 1)))] at htel
    have hsum : ∑ j : Fin m, (if t < r (σ j) then D j else 0) = ψ (N 0) - ψ (N m) := by
      rw [← htel]
      exact Finset.sum_congr rfl fun j _ => (hstep j).symm
    simp only
    rw [hsum, hN0, hNm]
    abel
  have hr01 : ∀ j, 0 ≤ r (σ j) ∧ r (σ j) ≤ 1 := fun j =>
    ⟨sub_nonneg.2 (hx (σ j)).1, by linarith [(hx (σ j)).2]⟩
  rw [kuhnInterpolation_eq_setIntegral, setIntegral_congr_fun measurableSet_Ioo hpt,
    integral_add (integrableOn_const (by simp [Real.volume_Ioo]))
      (integrable_finsetSum _ fun j _ => kuhn_integrableOn_step _ _),
    setIntegral_const, kuhn_volume_real_Ioo, one_smul,
    integral_finsetSum _ (fun j _ => kuhn_integrableOn_step _ _), kuhnAffine_apply]
  congr 1
  exact Finset.sum_congr rfl fun j _ => kuhn_integral_step (hr01 j).1 (hr01 j).2 _

/-- The interpolation agrees with `kuhnAffine k ψ a σ` on the open Kuhn simplex. -/
theorem kuhnInterpolation_eqOn_kuhnSimplex (k : ℕ) (ψ : (Fin m → ℝ) → Fin d → ℝ)
    (a : Fin m → ℤ) (σ : Equiv.Perm (Fin m)) :
    Set.EqOn (kuhnInterpolation k ψ) (kuhnAffine k ψ a σ) (kuhnSimplex k a σ) := fun _ hx =>
  kuhnInterpolation_eq_kuhnAffine k ψ a σ (fun i => ⟨(hx.1 i).1.le, (hx.1 i).2⟩) hx.2.monotone

/-- The gradient of an affine map. -/
private lemma kuhn_grad_affineMap (L : (Fin m → ℝ) →ᵃ[ℝ] (Fin d → ℝ)) (x : Fin m → ℝ) :
    grad L x = Matrix.of fun i c => L.linear (Pi.single c 1) i := by
  ext i c
  simp only [grad, Matrix.of_apply]
  have hL : (fun y => L y i) = fun y => ((LinearMap.proj i).comp L.linear) y + L 0 i := by
    funext y
    rw [congrFun L.decomp y]
    rfl
  have : HasFDerivAt (fun y => L y i)
      (LinearMap.toContinuousLinearMap ((LinearMap.proj i).comp L.linear)) x := by
    rw [hL]
    exact (LinearMap.toContinuousLinearMap
      ((LinearMap.proj i).comp L.linear)).hasFDerivAt.add_const _
  rw [this.fderiv]
  rfl

/-- On the open Kuhn simplex `kuhnSimplex k a σ`, the column `σ s` of `∇ I_k ψ` is
`k (ψ (w_s + k⁻¹ e_{σ s}) − ψ (w_s))`, `w_s = kuhnVertex k a σ (s + 1)`. -/
theorem kuhnInterpolation_grad (k : ℕ) (ψ : (Fin m → ℝ) → Fin d → ℝ) (a : Fin m → ℤ)
    (σ : Equiv.Perm (Fin m)) {x : Fin m → ℝ} (hx : x ∈ kuhnSimplex k a σ) (i : Fin d)
    (s : Fin m) :
    grad (kuhnInterpolation k ψ) x i (σ s) =
      (k : ℝ) * (ψ (kuhnVertex k a σ ((s : ℕ) + 1) + (k : ℝ)⁻¹ • Pi.single (σ s) 1) i -
        ψ (kuhnVertex k a σ ((s : ℕ) + 1)) i) := by
  rw [cv_grad_congr (Filter.eventuallyEq_of_mem ((kuhnSimplex_isOpen k a σ).mem_nhds hx)
    (kuhnInterpolation_eqOn_kuhnSimplex k ψ a σ)), kuhn_grad_affineMap, Matrix.of_apply,
    kuhnAffine_linear_single]
  rfl

/-! ### Floors and orderings determine the simplex -/

/-- On `kuhnSimplex k a σ`, `a = ⌊k x⌋`. -/
theorem kuhnSimplex_floor {k : ℕ} {a : Fin m → ℤ} {σ : Equiv.Perm (Fin m)} {x : Fin m → ℝ}
    (hx : x ∈ kuhnSimplex k a σ) (i : Fin m) : ⌊(k : ℝ) * x i⌋ = a i :=
  Int.floor_eq_iff.2 ⟨(hx.1 i).1.le, (hx.1 i).2⟩

/-- On `kuhnSimplex k a σ`, `σ` is the permutation sorting `k x − a`. -/
theorem kuhnSimplex_perm_eq {k : ℕ} {a : Fin m → ℤ} {σ : Equiv.Perm (Fin m)} {x : Fin m → ℝ}
    (hx : x ∈ kuhnSimplex k a σ) : σ = Tuple.sort fun i => (k : ℝ) * x i - a i :=
  Tuple.eq_sort_iff.2 ⟨hx.2.monotone, fun _ _ _ h => (congrArg σ (hx.2.injective h)).le⟩

/-- The vertices of the Kuhn simplex at `⌊k x⌋` are within `k⁻¹` of `x`. -/
private lemma kuhn_norm_vertex_sub_le {k : ℕ} (hk : 0 < k) (σ : Equiv.Perm (Fin m))
    (x : Fin m → ℝ) (s : ℕ) :
    ‖kuhnVertex k (fun i => ⌊(k : ℝ) * x i⌋) σ s - x‖ ≤ (k : ℝ)⁻¹ := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  refine (pi_norm_le_iff_of_nonneg (inv_nonneg.2 hk'.le)).2 fun i => ?_
  have h1 := Int.floor_le ((k : ℝ) * x i)
  have h2 := Int.lt_floor_add_one ((k : ℝ) * x i)
  have he : kuhnVertex k (fun i => ⌊(k : ℝ) * x i⌋) σ s i - x i = (k : ℝ)⁻¹ *
      ((⌊(k : ℝ) * x i⌋ : ℝ) + (if s ≤ (σ.symm i : ℕ) then 1 else 0) - k * x i) := by
    simp only [kuhnVertex]
    field_simp
  rw [Pi.sub_apply, Real.norm_eq_abs, he, abs_mul, abs_of_pos (inv_pos.2 hk')]
  refine mul_le_of_le_one_right (inv_nonneg.2 hk'.le) ?_
  rw [abs_le]
  split_ifs <;> constructor <;> linarith

/-! ### The grid hyperplanes -/

/-- The union of the hyperplanes `{x_i = q}` and `{x_i − x_{i'} = q}` (`q ∈ ℚ`, `i ≠ i'`); it
contains the boundaries of the Kuhn simplices of all the grids `k⁻¹ ℤ^m`. -/
private def kuhnBad (m : ℕ) : Set (Fin m → ℝ) :=
  (⋃ (i : Fin m) (q : ℚ), {x | x i = q}) ∪
    ⋃ (i : Fin m) (i' : Fin m) (_ : i ≠ i') (q : ℚ), {x | x i - x i' = q}

/-- A level set of a nonzero linear functional is null. -/
private lemma kuhn_volume_level (f : (Fin m → ℝ) →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) :
    volume {x | f x = c} = 0 := by
  have he : {x | f x = c} =
      (AffineSubspace.comap f.toAffineMap (affineSpan ℝ {c}) : Set (Fin m → ℝ)) := by
    ext x
    simp [AffineSubspace.coe_comap]
  rw [he]
  refine Measure.addHaar_affineSubspace _ _ fun h => hf ?_
  have hall : ∀ x, f x = c := fun x => by
    have hx : x ∈ AffineSubspace.comap f.toAffineMap (affineSpan ℝ {c}) :=
      h ▸ AffineSubspace.mem_top ℝ _ x
    simpa [AffineSubspace.mem_comap, AffineSubspace.mem_affineSpan_singleton] using hx
  have hc : c = 0 := by rw [← hall 0, map_zero]
  exact LinearMap.ext fun x => (hall x).trans (hc.trans (LinearMap.zero_apply x).symm)

private lemma kuhn_volume_bad (m : ℕ) : volume (kuhnBad m) = 0 := by
  refine measure_union_null (measure_iUnion_null fun i => measure_iUnion_null fun q => ?_)
    (measure_iUnion_null fun i => measure_iUnion_null fun i' =>
      measure_iUnion_null fun hii' => measure_iUnion_null fun q => ?_)
  · refine kuhn_volume_level (LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i)
      (fun h => ?_) q
    have := LinearMap.congr_fun h (Pi.single i 1)
    simp at this
  · refine kuhn_volume_level (LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i -
      LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i') (fun h => ?_) q
    have := LinearMap.congr_fun h (Pi.single i 1)
    simp [Pi.single_eq_of_ne' hii'] at this

/-- For `k ≥ 1`, a point off `kuhnBad m` lies in the open Kuhn simplex at `⌊k x⌋` whose ordering
sorts the fractional parts of `k x`. -/
private lemma kuhn_mem_simplex {k : ℕ} (hk : 0 < k) {x : Fin m → ℝ} (hx : x ∉ kuhnBad m) :
    x ∈ kuhnSimplex k (fun i => ⌊(k : ℝ) * x i⌋)
      (Tuple.sort fun i => (k : ℝ) * x i - ⌊(k : ℝ) * x i⌋) := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  simp only [kuhnBad, Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or,
    not_exists] at hx
  obtain ⟨h1, h2⟩ := hx
  refine ⟨fun i => ⟨lt_of_le_of_ne (Int.floor_le _) fun h =>
    h1 i ((⌊(k : ℝ) * x i⌋ : ℚ) / k) ?_, Int.lt_floor_add_one _⟩, ?_⟩
  · simp only at h
    push_cast
    rw [eq_div_iff hk']
    linarith
  · have hinj : Function.Injective fun i => (k : ℝ) * x i - ⌊(k : ℝ) * x i⌋ := by
      intro i i' h
      by_contra hne
      refine h2 i i' hne (((⌊(k : ℝ) * x i⌋ - ⌊(k : ℝ) * x i'⌋ : ℤ) : ℚ) / k) ?_
      simp only at h
      push_cast
      rw [eq_div_iff hk']
      linarith
    exact (Tuple.monotone_sort _).strictMono_of_injective (hinj.comp (Tuple.sort _).injective)

/-! ### Piecewise affinity -/

/-- The interpolation is piecewise affine on the unit cube: affine on each of the finitely many
open Kuhn simplices of the grid `k⁻¹ ℤ^m` in the cube, whose boundaries lie in finitely many
hyperplanes. -/
theorem kuhnInterpolation_piecewiseAffineOn (ψ : (Fin m → ℝ) → Fin d → ℝ) {k : ℕ} (hk : 0 < k) :
    PiecewiseAffineOn (unitCube m) (kuhnInterpolation k ψ) := by
  classical
  let ι := (Fin m → Fin k) × Equiv.Perm (Fin m)
  let A : ι → Fin m → ℤ := fun p i => ((p.1 i : ℕ) : ℤ)
  let e := Fintype.equivFin ι
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  refine ⟨Fintype.card ι, fun n => kuhnSimplex k (A (e.symm n)) (e.symm n).2,
    fun n => kuhnAffine k ψ (A (e.symm n)) (e.symm n).2, fun n => kuhnSimplex_isOpen _ _ _,
    ?_, ?_, ?_, fun n => kuhnInterpolation_eqOn_kuhnSimplex _ _ _ _⟩
  · intro n n' hnn'
    refine Set.disjoint_left.2 fun x hx hx' => hnn' (e.symm.injective ?_)
    have ha : A (e.symm n) = A (e.symm n') :=
      funext fun i => (kuhnSimplex_floor hx i).symm.trans (kuhnSimplex_floor hx' i)
    refine Prod.ext (funext fun i => Fin.ext ?_) ?_
    · have := congrFun ha i
      simp only [A] at this
      exact_mod_cast this
    · rw [kuhnSimplex_perm_eq hx, kuhnSimplex_perm_eq hx', ha]
  · intro n x hx
    simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
    intro i
    have h0 : (0 : ℝ) ≤ A (e.symm n) i := by simp [A]
    have h1 : (A (e.symm n) i : ℝ) + 1 ≤ k := by
      have := ((e.symm n).1 i).2
      simp only [A, Int.cast_natCast]
      exact_mod_cast this
    have hxi := hx.1 i
    constructor
    · by_contra hneg
      have : (k : ℝ) * x i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk'.le (not_lt.1 hneg)
      linarith [hxi.1]
    · by_contra hneg
      have : (k : ℝ) ≤ k * x i := le_mul_of_one_le_right hk'.le (not_lt.1 hneg)
      linarith [hxi.2]
  · refine measure_mono_null (fun x hx => ?_) (kuhn_volume_bad m)
    obtain ⟨hxU, hxn⟩ := hx
    by_contra hb
    have hmem := kuhn_mem_simplex hk hb
    apply hxn
    rw [Set.mem_iUnion]
    have hfl : ∀ i, 0 ≤ ⌊(k : ℝ) * x i⌋ ∧ ⌊(k : ℝ) * x i⌋ < k := fun i => by
      have hxi := hxU i (Set.mem_univ i)
      refine ⟨Int.floor_nonneg.2 (by nlinarith [hxi.1]), Int.floor_lt.2 ?_⟩
      push_cast
      nlinarith [hxi.2]
    let p : ι := (fun i => ⟨(⌊(k : ℝ) * x i⌋).toNat, by have := hfl i; omega⟩,
      Tuple.sort fun i => (k : ℝ) * x i - ⌊(k : ℝ) * x i⌋)
    refine ⟨e p, ?_⟩
    simp only [Equiv.symm_apply_apply]
    have hA : A p = fun i => ⌊(k : ℝ) * x i⌋ :=
      funext fun i => by simp [A, p, Int.toNat_of_nonneg (hfl i).1]
    rw [hA]
    exact hmem

/-! ### Convergence of the gradients -/

/-- **Interpolation of a `C¹` map** (the piecewise linear approximation of a smooth map on a fine
regular triangulation): for a `C¹` map `ψ` with compact support, the gradients of the
Kuhn–Freudenthal interpolants converge to `∇ψ` uniformly: for every `ε > 0` there is `k₀` such
that for `k ≥ k₀`, almost everywhere, every entry of `∇ I_k ψ − ∇ψ` is at most `ε`. -/
theorem kuhnInterpolation_grad_uniform {ψ : (Fin m → ℝ) → Fin d → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ᵐ x, ∀ i j,
      |grad (kuhnInterpolation k ψ) x i j - grad ψ x i j| ≤ ε := by
  have hdiff : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have huc : UniformContinuous (fderiv ℝ ψ) :=
    (hψc.fderiv ℝ).uniformContinuous_of_continuous (hψ.continuous_fderiv one_ne_zero)
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.1 huc ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt δ⁻¹
  refine ⟨max N 1, fun k hk => ?_⟩
  have hkpos : 0 < k := le_of_max_le_right hk
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hkpos
  have hkδ : (k : ℝ)⁻¹ < δ := by
    rw [inv_lt_comm₀ hk' hδ]
    exact lt_of_lt_of_le hN (by exact_mod_cast le_of_max_le_left hk)
  have hpi : ∀ y (i : Fin d), HasFDerivAt (fun z => ψ z i)
      ((ContinuousLinearMap.proj i).comp (fderiv ℝ ψ y)) y :=
    fun y i => (hasFDerivAt_pi'.1 (hdiff y).hasFDerivAt) i
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (kuhn_volume_bad m)] with x hxb
  intro i c
  set a : Fin m → ℤ := fun i => ⌊(k : ℝ) * x i⌋ with ha
  set σ := Tuple.sort fun i => (k : ℝ) * x i - ⌊(k : ℝ) * x i⌋ with hσ
  have hmem : x ∈ kuhnSimplex k a σ := kuhn_mem_simplex hkpos hxb
  obtain ⟨s, rfl⟩ : ∃ s, σ s = c := ⟨σ.symm c, by simp⟩
  have hgrad : grad ψ x i (σ s) = fderiv ℝ ψ x (Pi.single (σ s) 1) i := by
    simp only [grad, Matrix.of_apply]
    rw [(hpi x i).fderiv]
    rfl
  rw [kuhnInterpolation_grad k ψ a σ hmem i s, hgrad]
  set w := kuhnVertex k a σ ((s : ℕ) + 1) with hw_def
  set e : Fin m → ℝ := Pi.single (σ s) 1 with he_def
  have hw : ‖w - x‖ ≤ (k : ℝ)⁻¹ := kuhn_norm_vertex_sub_le hkpos σ x ((s : ℕ) + 1)
  have hv : ‖w + (k : ℝ)⁻¹ • e - x‖ ≤ (k : ℝ)⁻¹ := by
    rw [hw_def, he_def, ← kuhnVertex_eq_add]
    exact kuhn_norm_vertex_sub_le hkpos σ x s
  -- the mean value theorem on the edge `[w, w + k⁻¹ e]`
  have hderiv : ∀ τ : ℝ,
      HasDerivAt (fun τ => ψ (w + τ • e) i) (fderiv ℝ ψ (w + τ • e) e i) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ => w + τ • e) e τ := by
      simpa using ((hasDerivAt_id τ).smul_const e).const_add w
    exact (hpi (w + τ • e) i).comp_hasDerivAt τ h1
  obtain ⟨τ, hτ, hτeq⟩ := exists_hasDerivAt_eq_slope (fun τ => ψ (w + τ • e) i)
    (fun τ => fderiv ℝ ψ (w + τ • e) e i) (inv_pos.2 hk')
    (fun τ _ => (hderiv τ).continuousAt.continuousWithinAt) (fun τ _ => hderiv τ)
  have hξ : ‖w + τ • e - x‖ ≤ (k : ℝ)⁻¹ := by
    have hmemξ : w + ((k : ℝ) * τ) • ((w + (k : ℝ)⁻¹ • e) - w) ∈
        Metric.closedBall x (k : ℝ)⁻¹ :=
      (convex_closedBall x _).add_smul_sub_mem (mem_closedBall_iff_norm.2 hw)
        (mem_closedBall_iff_norm.2 hv)
        ⟨by nlinarith [hτ.1], by
          have := hτ.2
          rw [← mul_inv_cancel₀ hk'.ne']
          exact mul_le_mul_of_nonneg_left this.le hk'.le⟩
    have heq : w + ((k : ℝ) * τ) • ((w + (k : ℝ)⁻¹ • e) - w) = w + τ • e := by
      rw [add_sub_cancel_left, smul_smul, mul_comm (k : ℝ) τ, mul_assoc,
        mul_inv_cancel₀ hk'.ne', mul_one]
    rw [heq] at hmemξ
    exact mem_closedBall_iff_norm.1 hmemξ
  have hdq : (k : ℝ) * (ψ (w + (k : ℝ)⁻¹ • e) i - ψ w i) = fderiv ℝ ψ (w + τ • e) e i := by
    rw [hτeq]
    simp only [zero_smul, add_zero, sub_zero]
    field_simp
  rw [hdq]
  have hdist : dist (fderiv ℝ ψ (w + τ • e)) (fderiv ℝ ψ x) < ε :=
    hδε (by rw [dist_eq_norm]; linarith)
  calc |fderiv ℝ ψ (w + τ • e) e i - fderiv ℝ ψ x e i|
      = ‖((fderiv ℝ ψ (w + τ • e) - fderiv ℝ ψ x) e) i‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖(fderiv ℝ ψ (w + τ • e) - fderiv ℝ ψ x) e‖ := norm_le_pi_norm _ i
    _ ≤ ‖fderiv ℝ ψ (w + τ • e) - fderiv ℝ ψ x‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ε * 1 := by
        gcongr
        · rw [← dist_eq_norm]
          exact hdist.le
        · simp [e, Pi.norm_single]
    _ = ε := mul_one ε

end CalculusOfVariations
