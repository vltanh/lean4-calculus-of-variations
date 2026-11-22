/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Distribution.SecondDerivative
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.LHopital

/-!
# Convexity through the second distributional derivative

On `ℝ`:

* a convex `f` has `(ofFun f)'' ≥ 0`: `∫ f ψ'' ≥ 0` for `ψ ≥ 0`
  (`ConvexOn.integral_deriv_deriv_mul_nonneg`,
  `ConvexOn.distribNonneg_lineDerivOp_lineDerivOp_ofFun`), since
  `∫ f ψ'' = lim_{δ → 0} ∫ ψ (x) (f (x + δ) − 2 f (x) + f (x − δ)) / δ² dx` and the second
  differences of `f` are nonnegative. For `δ ≠ 0`, translation invariance of the Lebesgue measure
  moves the second difference from `ψ` to `f`; the second difference quotients of `ψ` converge
  pointwise to `ψ''` (`distrib_tendsto_secondDiff`, by l'Hôpital's rule) and are bounded by twice
  the Lipschitz constant of `ψ'` (`distrib_abs_secondDiff_le`, by the mean value inequality), so
  dominated convergence applies, `f` being continuous;
* conversely a continuous `g` with `(ofFun g)'' ≥ 0` is convex
  (`convexOn_of_integral_deriv_deriv_mul_nonneg`, `convexOn_of_distribNonneg`): the mollifications
  `ρ_ε ⋆ g` are smooth with `(ρ_ε ⋆ g)'' (t) = (ρ_ε'' ⋆ g) (t) = ⟨(ofFun g)'', ρ_ε (t − ·)⟩ ≥ 0`
  (differentiating under the convolution), hence convex (`convexOn_univ_of_deriv2_nonneg`), and
  they converge to `g` pointwise; a pointwise limit of convex functions is convex
  (`distrib_convexOn_of_tendsto`).
-/

@[expose] public section

open MeasureTheory TopologicalSpace
open scoped Distributions LineDeriv ContDiff
open Filter Topology
open scoped NNReal

namespace CalculusOfVariations

/-- **Second differences of a function with Lipschitz derivative**: if `φ'` is `L`-Lipschitz,
then `|φ (x + δ) - 2 φ x + φ (x - δ)| ≤ 2 L δ²`, by the mean value inequality for
`t ↦ φ (x + t) + φ (x - t)` on `[-|δ|, |δ|]`. -/
theorem distrib_abs_secondDiff_le {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) {L : ℝ≥0}
    (hL : LipschitzWith L (deriv φ)) (x δ : ℝ) :
    |φ (x + δ) - 2 * φ x + φ (x - δ)| ≤ 2 * L * δ ^ 2 := by
  have hgd : ∀ t, HasDerivAt (fun t => φ (x + t) + φ (x - t))
      (deriv φ (x + t) - deriv φ (x - t)) t := by
    intro t
    have h1 := ((hφ (x + t)).hasDerivAt).comp_const_add x t
    have h2 := ((hφ (x - t)).hasDerivAt).comp_const_sub x t
    convert h1.add h2 using 1
  have hb : ∀ t ∈ Metric.closedBall (0 : ℝ) |δ|,
      ‖deriv φ (x + t) - deriv φ (x - t)‖ ≤ 2 * L * |δ| := by
    intro t ht
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at ht
    have := hL.dist_le_mul (x + t) (x - t)
    rw [Real.dist_eq, Real.dist_eq, show x + t - (x - t) = 2 * t by ring, abs_mul, abs_two]
      at this
    rw [Real.norm_eq_abs]
    calc |deriv φ (x + t) - deriv φ (x - t)| ≤ L * (2 * |t|) := this
      _ ≤ 2 * L * |δ| := by nlinarith [L.coe_nonneg]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hgd t).hasDerivWithinAt) hb (convex_closedBall 0 |δ|)
    (Metric.mem_closedBall_self (abs_nonneg δ)) (show δ ∈ Metric.closedBall (0 : ℝ) |δ| by simp)
  simp only [add_zero, sub_zero, Real.norm_eq_abs] at this
  calc |φ (x + δ) - 2 * φ x + φ (x - δ)| = |φ (x + δ) + φ (x - δ) - (φ x + φ x)| := by
        ring_nf
    _ ≤ 2 * L * |δ| * |δ| := this
    _ = 2 * L * δ ^ 2 := by rw [mul_assoc _ |δ|, ← sq, sq_abs]

/-- **Symmetric second difference quotients** converge to the second derivative: if `φ` is
differentiable and `φ'` has derivative `c` at `x`, then
`(φ (x + δ) - 2 φ x + φ (x - δ)) / δ² → c` as `δ → 0`, `δ ≠ 0` (by l'Hôpital's rule, the quotient
of the derivatives being the mean of the two one-sided difference quotients of `φ'` at `x`). -/
theorem distrib_tendsto_secondDiff {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) {x c : ℝ}
    (hc : HasDerivAt (deriv φ) c x) :
    Tendsto (fun δ => (φ (x + δ) - 2 * φ x + φ (x - δ)) / δ ^ 2) (𝓝[≠] 0) (𝓝 c) := by
  have hN : ∀ δ, HasDerivAt (fun δ => φ (x + δ) - 2 * φ x + φ (x - δ))
      (deriv φ (x + δ) - deriv φ (x - δ)) δ := by
    intro δ
    have h1 := ((hφ (x + δ)).hasDerivAt).comp_const_add x δ
    have h2 := ((hφ (x - δ)).hasDerivAt).comp_const_sub x δ
    convert (h1.sub_const (2 * φ x)).add h2 using 1
  have hD : ∀ δ : ℝ, HasDerivAt (fun δ : ℝ => δ ^ 2) (2 * δ) δ := by
    intro δ; simpa using hasDerivAt_pow 2 δ
  refine HasDerivAt.lhopital_zero_nhdsNE (Eventually.of_forall hN) (Eventually.of_forall hD)
    (eventually_nhdsWithin_of_forall fun δ hδ => mul_ne_zero two_ne_zero hδ) ?_ ?_ ?_
  · apply tendsto_nhdsWithin_of_tendsto_nhds
    have : Continuous (fun δ => φ (x + δ) - 2 * φ x + φ (x - δ)) := by
      have := hφ.continuous; fun_prop
    convert this.tendsto 0 using 2
    simp only [add_zero, sub_zero]; ring
  · apply tendsto_nhdsWithin_of_tendsto_nhds
    simpa using (continuous_pow 2).tendsto (0 : ℝ)
  · have A1 := hc.tendsto_slope_zero
    have hc' : HasDerivAt (fun t => deriv φ (x - t)) (-c) 0 :=
      HasDerivAt.comp_const_sub x 0 (by simpa using hc)
    have A2 := hc'.tendsto_slope_zero
    have A := (A1.sub A2).div_const 2
    rw [show (c - -c) / 2 = c by ring] at A
    refine A.congr' (eventually_nhdsWithin_of_forall fun δ hδ => ?_)
    simp only [smul_eq_mul, zero_add, sub_zero]
    field_simp
    ring

/-- A pointwise limit of convex functions is convex. -/
theorem distrib_convexOn_of_tendsto {E ι : Type*} [AddCommGroup E] [Module ℝ E] {l : Filter ι}
    [l.NeBot] {s : Set E} {F : ι → E → ℝ} {g : E → ℝ} (hF : ∀ᶠ i in l, ConvexOn ℝ s (F i))
    (hlim : ∀ x ∈ s, Tendsto (fun i => F i x) l (𝓝 (g x))) : ConvexOn ℝ s g := by
  obtain ⟨i, hi⟩ := hF.exists
  refine ⟨hi.1, fun x hx y hy a b ha hb hab => ?_⟩
  refine le_of_tendsto_of_tendsto (hlim _ (hi.1 hx hy ha hb hab))
    (((hlim x hx).const_smul a).add ((hlim y hy).const_smul b)) ?_
  filter_upwards [hF] with j hj
  exact hj.2 hx hy ha hb hab

/-- **A convex function has a nonnegative second distributional derivative**, in concrete form:
`∫ f ψ'' ≥ 0` for every compactly supported, nonnegative `C²` function `ψ`. -/
theorem ConvexOn.integral_deriv_deriv_mul_nonneg {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x) :
    0 ≤ ∫ x, deriv (deriv ψ) x * f x := by
  have hfc : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  have hψd : Differentiable ℝ ψ := hψ.differentiable two_ne_zero
  have hψ1 : ContDiff ℝ 1 (deriv ψ) := hψ.deriv'
  have hψcont : Continuous ψ := hψ.continuous
  obtain ⟨L, hL⟩ := hψ1.lipschitzWith_of_hasCompactSupport hψc.deriv one_ne_zero
  obtain ⟨R, hR⟩ := hψc.isCompact.isBounded.subset_closedBall 0
  have hvan : ∀ y, R < |y| → ψ y = 0 := by
    intro y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hys
    have := hR hys
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith
  -- Step 1: for `δ ≠ 0`, `∫ f (ψ (· + δ) - 2 ψ + ψ (· - δ)) / δ² ≥ 0`, by translation invariance
  -- and the nonnegativity of the second differences of the convex `f`
  have step1 : ∀ δ ≠ 0, 0 ≤ ∫ x, (ψ (x + δ) - 2 * ψ x + ψ (x - δ)) / δ ^ 2 * f x := by
    intro δ hδ
    have hcp : HasCompactSupport (fun x => ψ (x + δ)) :=
      hψc.comp_homeomorph (Homeomorph.addRight δ)
    have hcm : HasCompactSupport (fun x => ψ (x - δ)) :=
      hψc.comp_homeomorph (Homeomorph.subRight δ)
    have hI1 : Integrable (fun x => ψ (x + δ) * f x) :=
      distrib_integrable_mul_of_hasCompactSupport (u := fun x => ψ (x + δ)) (by fun_prop) hcp hfc
    have hI2 : Integrable (fun x => 2 * (ψ x * f x)) :=
      (distrib_integrable_mul_of_hasCompactSupport hψcont hψc hfc).const_mul 2
    have hI3 : Integrable (fun x => ψ (x - δ) * f x) :=
      distrib_integrable_mul_of_hasCompactSupport (u := fun x => ψ (x - δ)) (by fun_prop) hcm hfc
    have hJ1 : Integrable (fun x => ψ x * f (x - δ)) :=
      distrib_integrable_mul_of_hasCompactSupport hψcont hψc (by fun_prop)
    have hJ3 : Integrable (fun x => ψ x * f (x + δ)) :=
      distrib_integrable_mul_of_hasCompactSupport hψcont hψc (by fun_prop)
    have hI12 : Integrable (fun x => ψ (x + δ) * f x - 2 * (ψ x * f x)) := hI1.sub hI2
    have hJ12 : Integrable (fun x => ψ x * f (x - δ) - 2 * (ψ x * f x)) := hJ1.sub hI2
    -- translation invariance
    have t1 : ∫ x, ψ (x + δ) * f x = ∫ x, ψ x * f (x - δ) := by
      have := integral_add_right_eq_self (μ := volume) (fun y => ψ y * f (y - δ)) δ
      simpa using this
    have t3 : ∫ x, ψ (x - δ) * f x = ∫ x, ψ x * f (x + δ) := by
      have := integral_sub_right_eq_self (μ := volume) (fun y => ψ y * f (y + δ)) δ
      simpa using this
    have l : ∫ x, (ψ (x + δ) - 2 * ψ x + ψ (x - δ)) / δ ^ 2 * f x =
        ((∫ x, ψ (x + δ) * f x) - 2 * (∫ x, ψ x * f x) + ∫ x, ψ (x - δ) * f x) / δ ^ 2 := by
      rw [← integral_const_mul, ← integral_sub hI1 hI2, ← integral_add hI12 hI3, ← integral_div]
      congr 1 with x; ring
    have r : ∫ x, ψ x * (f (x - δ) - 2 * f x + f (x + δ)) =
        (∫ x, ψ x * f (x - δ)) - 2 * (∫ x, ψ x * f x) + ∫ x, ψ x * f (x + δ) := by
      rw [← integral_const_mul, ← integral_sub hJ1 hI2, ← integral_add hJ12 hJ3]
      congr 1 with x; ring
    rw [l, t1, t3, ← r]
    refine div_nonneg (integral_nonneg fun x => mul_nonneg (hψ0 x) ?_) (sq_nonneg δ)
    have := hf.2 (Set.mem_univ (x - δ)) (Set.mem_univ (x + δ)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have hx : (1 / 2 : ℝ) • (x - δ) + (1 / 2 : ℝ) • (x + δ) = x := by
      simp only [smul_eq_mul]; ring
    rw [hx, smul_eq_mul, smul_eq_mul] at this
    linarith
  -- Step 2: dominated convergence as `δ → 0`
  have step2 : Tendsto (fun δ => ∫ x, (ψ (x + δ) - 2 * ψ x + ψ (x - δ)) / δ ^ 2 * f x)
      (𝓝[≠] 0) (𝓝 (∫ x, deriv (deriv ψ) x * f x)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      ((Metric.closedBall (0 : ℝ) (R + 1)).indicator (fun x => 2 * L * |f x|)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun δ => (by fun_prop : Continuous fun x =>
        (ψ (x + δ) - 2 * ψ x + ψ (x - δ)) / δ ^ 2 * f x).aestronglyMeasurable
    · have hδ1 : ∀ᶠ δ in 𝓝[≠] (0 : ℝ), |δ| ≤ 1 := by
        apply nhdsWithin_le_nhds
        filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with δ hδ
        simpa [Metric.mem_closedBall, dist_zero_right] using hδ
      filter_upwards [hδ1] with δ hδ
      refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ Metric.closedBall (0 : ℝ) (R + 1)
      · rw [Set.indicator_of_mem hx, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        rcases eq_or_ne δ 0 with rfl | hδ0
        · simp
        · rw [abs_div, abs_of_pos (by positivity : 0 < δ ^ 2), div_le_iff₀ (by positivity)]
          exact distrib_abs_secondDiff_le hψd hL x δ
      · rw [Set.indicator_of_notMem hx]
        rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
        have h1 : ψ (x + δ) = 0 := by
          apply hvan
          have := abs_sub_abs_le_abs_sub x (-δ)
          rw [abs_neg, sub_neg_eq_add] at this
          linarith
        have h2 : ψ x = 0 := hvan _ (by linarith)
        have h3 : ψ (x - δ) = 0 := by
          apply hvan
          have := abs_sub_abs_le_abs_sub x δ
          linarith
        simp [h1, h2, h3]
    · exact ((Continuous.continuousOn (by fun_prop)).integrableOn_compact
        (isCompact_closedBall _ _)).integrable_indicator Metric.isClosed_closedBall.measurableSet
    · exact ae_of_all _ fun x => (distrib_tendsto_secondDiff hψd
        ((hψ1.differentiable one_ne_zero x).hasDerivAt)).mul_const (f x)
  exact ge_of_tendsto step2 (eventually_nhdsWithin_of_forall step1)

/-- **A convex function has a nonnegative second distributional derivative.** -/
theorem ConvexOn.distribNonneg_lineDerivOp_lineDerivOp_ofFun {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) :
    DistribNonneg (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (Distribution.ofFun ⊤ f volume ⊤))) := by
  have hfc : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  intro ψ hψ0
  rw [lineDerivOp_lineDerivOp_ofFun_apply hfc.locallyIntegrable]
  exact ConvexOn.integral_deriv_deriv_mul_nonneg hf (ψ.contDiff.of_le (by simp))
    ψ.hasCompactSupport hψ0

/-- **A continuous function with a nonnegative second distributional derivative is convex**, in
concrete form: if `∫ g ψ'' ≥ 0` for every smooth, compactly supported, nonnegative `ψ`, then `g` is
convex. -/
theorem convexOn_of_integral_deriv_deriv_mul_nonneg {g : ℝ → ℝ} (hg : Continuous g)
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, deriv (deriv ψ) x * g x) :
    ConvexOn ℝ Set.univ g := by
  have hgi : LocallyIntegrable g := hg.locallyIntegrable
  -- the bumps `ρ_n`, of radius `1 / (n + 1)`
  let φ : ℕ → ContDiffBump (0 : ℝ) := fun n =>
    ⟨1 / ((n : ℝ) + 1) / 2, 1 / ((n : ℝ) + 1), by positivity, half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  refine distrib_convexOn_of_tendsto (l := atTop)
    (F := fun n => convolution ((φ n).normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume)
    (Eventually.of_forall fun n => ?_)
    (fun x _ => ContDiffBump.convolution_tendsto_right_of_continuous hφ hg x)
  -- the mollification `ρ_n ⋆ g` is convex
  set ρ := (φ n).normed volume
  have hρs : ContDiff ℝ ∞ ρ := (φ n).contDiff_normed
  have hρc : HasCompactSupport ρ := (φ n).hasCompactSupport_normed
  have hρ1 : ContDiff ℝ ∞ (deriv ρ) := hρs.iterate_deriv 1
  have hd1 : ∀ t, HasDerivAt (convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume)
      (convolution (deriv ρ) g (ContinuousLinearMap.lsmul ℝ ℝ) volume t) t := fun t =>
    hρc.hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρs.of_le (by simp)) hgi t
  have hd2 : ∀ t, HasDerivAt (convolution (deriv ρ) g (ContinuousLinearMap.lsmul ℝ ℝ) volume)
      (convolution (deriv (deriv ρ)) g (ContinuousLinearMap.lsmul ℝ ℝ) volume t) t := fun t =>
    hρc.deriv.hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρ1.of_le (by simp))
      hgi t
  have e1 : deriv (convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) =
      convolution (deriv ρ) g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    funext fun t => (hd1 t).deriv
  refine convexOn_univ_of_deriv2_nonneg (fun t => (hd1 t).differentiableAt)
    (by rw [e1]; exact fun t => (hd2 t).differentiableAt) fun t => ?_
  rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply, e1, (hd2 t).deriv,
    convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  -- `(ρ'' ⋆ g) (t) = ∫ ψ_t'' g` for the test function `ψ_t = ρ (t - ·)`
  have e2 : ∫ s, deriv (deriv ρ) s * g (t - s) = ∫ s, deriv (deriv ρ) (t - s) * g s := by
    rw [← integral_sub_left_eq_self (fun s => deriv (deriv ρ) s * g (t - s)) volume t]
    congr 1 with s
    simp only [sub_sub_cancel]
  have dd : deriv (deriv fun s => ρ (t - s)) = fun s => deriv (deriv ρ) (t - s) := by
    have : deriv (fun s => ρ (t - s)) = fun s => -deriv ρ (t - s) :=
      funext fun s => deriv_comp_const_sub ρ t s
    rw [this]; funext s
    rw [deriv.fun_neg, deriv_comp_const_sub, neg_neg]
  have := h (fun s => ρ (t - s)) (hρs.comp (contDiff_const.sub contDiff_id))
    (hρc.comp_homeomorph (Homeomorph.subLeft t)) (fun s => (φ n).nonneg_normed _)
  rw [dd] at this
  rw [e2]
  exact this

/-- **A continuous function with a nonnegative second distributional derivative is convex.** -/
theorem convexOn_of_distribNonneg {g : ℝ → ℝ} (hg : Continuous g)
    (h : DistribNonneg (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (Distribution.ofFun ⊤ g volume ⊤)))) :
    ConvexOn ℝ Set.univ g :=
  convexOn_of_integral_deriv_deriv_mul_nonneg hg
    ((distribNonneg_lineDerivOp_lineDerivOp_ofFun_iff hg.locallyIntegrable).mp h)

end CalculusOfVariations
