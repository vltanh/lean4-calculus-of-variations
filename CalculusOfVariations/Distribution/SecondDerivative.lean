/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Second distributional derivatives on the real line

On `ℝ`, with `Ω = ⊤` and Mathlib's distributions `𝓓'(Ω, ℝ)` (`Distribution.ofFun`, the derivative
`∂_{1}` of `Distribution.lineDerivCLM`):

* `DistribNonneg T`: `T ψ ≥ 0` for every nonnegative test function `ψ`;
* the pairing `⟨(ofFun g)'', ψ⟩ = ∫ g ψ''` (`lineDerivOp_lineDerivOp_ofFun_apply`), by unfolding
  `∂ T ψ = - T (∂ ψ)` twice and `∂_{1} ψ = ψ'` for a test function on `ℝ`
  (`TestFunction.lineDerivOp_one_apply`), and the nonnegativity of `(ofFun g)''` read through it
  (`distribNonneg_lineDerivOp_lineDerivOp_ofFun_iff`), since the test functions on `⊤` are exactly
  the smooth compactly supported functions;
* for a locally Lipschitz `f`, `(ofFun f)' = ofFun f'` (`lineDerivOp_ofFun_eq_ofFun_deriv`); in
  concrete form, `∫ f ψ' = −∫ f' ψ` (`integral_deriv_mul_eq_neg`), by integration by parts for
  absolutely continuous functions on an interval containing the support of `ψ`, on which `f` is
  Lipschitz; `f'` is locally integrable, being measurable and locally bounded by the local
  Lipschitz constants (`LocallyLipschitz.locallyIntegrable_deriv`);
* the Leibniz rule for a smooth `h`: `(h f)'' = h f'' + 2 h' f' + h'' f`, in the paired form
  `∫ h f ψ'' = ∫ f (h ψ)'' + ∫ (2 h' f' + h'' f) ψ` (`integral_deriv_deriv_mul_mul`,
  `lineDerivOp_lineDerivOp_ofFun_mul_apply`), by expanding `(h ψ)'' = h'' ψ + 2 h' ψ' + h ψ''` and
  integrating by parts against the compactly supported `C¹` function `h' ψ`.
-/

@[expose] public section

open MeasureTheory TopologicalSpace
open scoped Distributions LineDeriv ContDiff

namespace CalculusOfVariations

/-- A real distribution `T` is nonnegative if `T ψ ≥ 0` for every nonnegative test function
`ψ`. -/
def DistribNonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
    (T : 𝓓'(Ω, ℝ)) : Prop :=
  ∀ ψ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ ψ x) → 0 ≤ T ψ

/-- On `ℝ`, the derivative `∂_{1}` of a test function is its derivative `deriv`. -/
theorem TestFunction.lineDerivOp_one_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Opens ℝ} (ψ : 𝓓(Ω, F)) (x : ℝ) : (∂_{(1 : ℝ)} ψ) x = deriv ψ x := by
  rw [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, TestFunction.lineDerivCLM_apply_of_le le_top,
    (ψ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv,
    fderiv_apply_one_eq_deriv]

/-- On `ℝ`, the derivative `∂_{1}` of a test function is its derivative `deriv`. -/
theorem TestFunction.coe_lineDerivOp_one {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Opens ℝ} (ψ : 𝓓(Ω, F)) : ⇑(∂_{(1 : ℝ)} ψ : 𝓓(Ω, F)) = deriv ψ :=
  funext (TestFunction.lineDerivOp_one_apply ψ)

/-- The second derivative of the distribution of a locally integrable `g` on `ℝ`, paired with a
test function: `⟨(ofFun g)'', ψ⟩ = ∫ g ψ''`. -/
theorem lineDerivOp_lineDerivOp_ofFun_apply {g : ℝ → ℝ} (hg : LocallyIntegrable g)
    (ψ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (Distribution.ofFun ⊤ g volume ⊤)) ψ =
      ∫ x, deriv (deriv ψ) x * g x := by
  rw [Distribution.lineDerivOp_apply_apply, Distribution.lineDerivOp_apply_apply,
    LineDeriv.lineDerivOp_neg, neg_neg, Distribution.ofFun_apply (hg.locallyIntegrableOn _)]
  simp only [smul_eq_mul, TestFunction.coe_lineDerivOp_one]

/-- `(ofFun g)'' ≥ 0` if and only if `∫ g ψ'' ≥ 0` for every smooth, compactly supported,
nonnegative `ψ`. -/
theorem distribNonneg_lineDerivOp_lineDerivOp_ofFun_iff {g : ℝ → ℝ} (hg : LocallyIntegrable g) :
    DistribNonneg (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (Distribution.ofFun ⊤ g volume ⊤))) ↔
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
        0 ≤ ∫ x, deriv (deriv ψ) x * g x := by
  constructor
  · intro hT ψ hψ hψc hψ0
    have := hT ⟨ψ, hψ, hψc, by simp⟩ hψ0
    rwa [lineDerivOp_lineDerivOp_ofFun_apply hg] at this
  · intro h ψ hψ0
    rw [lineDerivOp_lineDerivOp_ofFun_apply hg]
    exact h ψ ψ.contDiff ψ.hasCompactSupport hψ0

/-- The derivative of a locally Lipschitz function on `ℝ` is locally integrable: it is measurable
and bounded near each point by a local Lipschitz constant. -/
theorem LocallyLipschitz.locallyIntegrable_deriv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : ℝ → F} (hf : LocallyLipschitz f) :
    LocallyIntegrable (deriv f) := by
  intro x
  obtain ⟨K, t, ht, hK⟩ := hf x
  refine ⟨interior t ∩ Metric.ball x 1,
    Filter.inter_mem (interior_mem_nhds.2 ht) (Metric.ball_mem_nhds x one_pos), ?_⟩
  refine Measure.integrableOn_of_bounded (M := K)
    ((measure_mono Set.inter_subset_right).trans_lt measure_ball_lt_top).ne
    (stronglyMeasurable_deriv f).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem (isOpen_interior.inter Metric.isOpen_ball).measurableSet
    fun y hy => ?_
  exact norm_deriv_le_of_lipschitzOn (mem_interior_iff_mem_nhds.1 hy.1) hK

/-- The product of a continuous compactly supported function and a continuous function on `ℝ` is
integrable. -/
theorem distrib_integrable_mul_of_hasCompactSupport {u v : ℝ → ℝ} (hu : Continuous u)
    (hcu : HasCompactSupport u) (hv : Continuous v) : Integrable (fun x => u x * v x) :=
  (hu.mul hv).integrable_of_hasCompactSupport hcu.mul_right

/-- Integration by parts for a locally Lipschitz `f` against a compactly supported `C¹` function
`ψ`, the proof of `integral_deriv_mul_eq_neg`: on an interval `[-r, r]` containing the support of
`ψ`, both `f` and `ψ` are Lipschitz, hence absolutely continuous; integrate by parts there, the
boundary terms and the integrands outside `[-r, r]` vanishing. -/
private theorem integral_deriv_mul_eq_neg_aux {f ψ : ℝ → ℝ} (hf : LocallyLipschitz f)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, deriv ψ x * f x = -∫ x, ψ x * deriv f x := by
  obtain ⟨R, hR⟩ := hψc.isCompact.isBounded.subset_closedBall 0
  set r := max R 0 + 1
  have hR0 : R ≤ max R 0 := le_max_left _ _
  have hab : -r ≤ r := by
    have : 0 ≤ max R 0 := le_max_right _ _
    linarith
  -- the support of `ψ` lies in `(-r, r)`
  have hout : ∀ x ∉ Set.Ioc (-r) r, x ∉ tsupport ψ := by
    intro x hx hxs
    have h1 := hR hxs
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with hx | hx
    · have := neg_abs_le x; linarith
    · have := le_abs_self x; linarith
  have hψa : ψ (-r) = 0 := image_eq_zero_of_notMem_tsupport (hout _ (by simp))
  have hψb : ψ r = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hxs
    have h1 := hR hxs
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
    have h3 : |r| = r := abs_of_nonneg (by linarith)
    linarith
  -- on `[-r, r]`, `f` and `ψ` are Lipschitz, hence absolutely continuous
  obtain ⟨K, hK⟩ :=
    (hf.locallyLipschitzOn (s := Set.uIcc (-r) r)).exists_lipschitzOnWith_of_compact isCompact_uIcc
  obtain ⟨L, hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hψc one_ne_zero
  have key := (hL.lipschitzOnWith (s := Set.uIcc (-r) r)).absolutelyContinuousOnInterval
    |>.integral_mul_deriv_eq_deriv_mul hK.absolutelyContinuousOnInterval
  -- the boundary terms vanish, and the integrands vanish off `(-r, r]`
  rw [hψa, hψb, zero_mul, zero_mul, sub_zero, zero_sub, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab, setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero] at key
  · rw [key, neg_neg]
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hout x hx (tsupport_deriv_subset h)), zero_mul]
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (hout x hx), zero_mul]

/-- **The distributional derivative of a locally Lipschitz function** on `ℝ` is the distribution
of its derivative (which exists almost everywhere and is locally bounded): the fundamental theorem
of calculus for absolutely continuous functions, through integration by parts against the test
function. -/
theorem lineDerivOp_ofFun_eq_ofFun_deriv {f : ℝ → ℝ} (hf : LocallyLipschitz f) :
    ∂_{(1 : ℝ)} (Distribution.ofFun ⊤ f volume ⊤) = Distribution.ofFun ⊤ (deriv f) volume ⊤ := by
  ext ψ
  rw [Distribution.lineDerivOp_apply_apply, map_neg,
    Distribution.ofFun_apply (hf.continuous.locallyIntegrable.locallyIntegrableOn _),
    Distribution.ofFun_apply ((LocallyLipschitz.locallyIntegrable_deriv hf).locallyIntegrableOn _)]
  simp only [smul_eq_mul, TestFunction.coe_lineDerivOp_one]
  rw [integral_deriv_mul_eq_neg_aux hf (ψ.contDiff.of_le (by simp)) ψ.hasCompactSupport, neg_neg]

/-- Integration by parts for a locally Lipschitz `f` against a compactly supported `C¹` function
`ψ`: `∫ ψ' f = −∫ ψ f'`. -/
theorem integral_deriv_mul_eq_neg {f ψ : ℝ → ℝ} (hf : LocallyLipschitz f) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x, deriv ψ x * f x = -∫ x, ψ x * deriv f x :=
  integral_deriv_mul_eq_neg_aux hf hψ hψc

/-- **The Leibniz rule for the second derivative**, in paired form: for a locally Lipschitz `f`, a
`C²` function `h` and a compactly supported `C²` function `ψ`,
`∫ ψ'' (h f) = (∫ (h ψ)'' f) + ∫ ψ (2 h' f' + h'' f)`, that is,
`(h f)'' = h f'' + 2 h' f' + h'' f` with `⟨h f'', ψ⟩ = ⟨f'', h ψ⟩`. -/
theorem integral_deriv_deriv_mul_mul {f h ψ : ℝ → ℝ} (hf : LocallyLipschitz f)
    (hh : ContDiff ℝ 2 h) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, deriv (deriv ψ) x * (h x * f x) =
      (∫ x, deriv (deriv fun y => h y * ψ y) x * f x) +
        ∫ x, ψ x * (2 * deriv h x * deriv f x + deriv (deriv h) x * f x) := by
  have hfc : Continuous f := hf.continuous
  have hdf : LocallyIntegrable (deriv f) := LocallyLipschitz.locallyIntegrable_deriv hf
  have hh1 : ContDiff ℝ 1 (deriv h) := hh.deriv'
  have hψ1 : ContDiff ℝ 1 (deriv ψ) := hψ.deriv'
  have hdh : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hdψ : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hddh : Differentiable ℝ (deriv h) := hh1.differentiable one_ne_zero
  have hddψ : Differentiable ℝ (deriv ψ) := hψ1.differentiable one_ne_zero
  -- `(h ψ)'' = h'' ψ + 2 h' ψ' + h ψ''`
  have e1 : deriv (fun y => h y * ψ y) = fun y => deriv h y * ψ y + h y * deriv ψ y := by
    funext y; exact deriv_mul (hdh y) (hdψ y)
  have e2 : deriv (deriv fun y => h y * ψ y) = fun y => deriv (deriv h) y * ψ y +
      deriv h y * deriv ψ y + (deriv h y * deriv ψ y + h y * deriv (deriv ψ) y) := by
    rw [e1]; funext y
    refine ((((hddh y).hasDerivAt.mul (hdψ y).hasDerivAt).add
      ((hdh y).hasDerivAt.mul (hddψ y).hasDerivAt)).deriv).trans ?_
    ring
  -- integration by parts against the compactly supported `C¹` function `h' ψ`
  have hφc : HasCompactSupport (fun y => deriv h y * ψ y) := hψc.mul_left
  have ibp := integral_deriv_mul_eq_neg hf (hh1.mul (hψ.of_le (by norm_num))) hφc
  have e3 : deriv (fun y => deriv h y * ψ y) =
      fun y => deriv (deriv h) y * ψ y + deriv h y * deriv ψ y := by
    funext y; exact deriv_mul (hddh y) (hdψ y)
  simp only [e3] at ibp
  simp only [e2]
  -- the four integrals involved
  have hA : Integrable (fun x => deriv (deriv ψ) x * h x * f x) :=
    distrib_integrable_mul_of_hasCompactSupport (u := fun x => deriv (deriv ψ) x * h x)
      ((hψ1.continuous_deriv le_rfl).mul hh.continuous) hψc.deriv.deriv.mul_right hfc
  have hB : Integrable (fun x => deriv (deriv h) x * ψ x * f x) :=
    distrib_integrable_mul_of_hasCompactSupport (u := fun x => deriv (deriv h) x * ψ x)
      ((hh1.continuous_deriv le_rfl).mul hψ.continuous) hψc.mul_left hfc
  have hC : Integrable (fun x => deriv h x * deriv ψ x * f x) :=
    distrib_integrable_mul_of_hasCompactSupport (u := fun x => deriv h x * deriv ψ x)
      (hh1.continuous.mul hψ1.continuous) hψc.deriv.mul_left hfc
  have hD : Integrable (fun x => deriv h x * ψ x * deriv f x) := by
    simpa only [smul_eq_mul] using hdf.integrable_smul_left_of_hasCompactSupport
      (g := fun x => deriv h x * ψ x) (hh1.continuous.mul hψ.continuous) hφc
  have i0 : ∫ x, deriv (deriv ψ) x * (h x * f x) = ∫ x, deriv (deriv ψ) x * h x * f x := by
    congr 1 with x; ring
  have i1 : ∫ x, (deriv (deriv h) x * ψ x + deriv h x * deriv ψ x +
      (deriv h x * deriv ψ x + h x * deriv (deriv ψ) x)) * f x =
      (∫ x, deriv (deriv h) x * ψ x * f x) + 2 * (∫ x, deriv h x * deriv ψ x * f x) +
        ∫ x, deriv (deriv ψ) x * h x * f x := by
    have hBC : Integrable (fun x => deriv (deriv h) x * ψ x * f x +
        2 * (deriv h x * deriv ψ x * f x)) := hB.add (hC.const_mul 2)
    rw [← integral_const_mul, ← integral_add hB (hC.const_mul 2), ← integral_add hBC hA]
    congr 1 with x; ring
  have i2 : ∫ x, ψ x * (2 * deriv h x * deriv f x + deriv (deriv h) x * f x) =
      2 * (∫ x, deriv h x * ψ x * deriv f x) + ∫ x, deriv (deriv h) x * ψ x * f x := by
    rw [← integral_const_mul, ← integral_add (hD.const_mul 2) hB]
    congr 1 with x; ring
  have i3 : ∫ x, (deriv (deriv h) x * ψ x + deriv h x * deriv ψ x) * f x =
      (∫ x, deriv (deriv h) x * ψ x * f x) + ∫ x, deriv h x * deriv ψ x * f x := by
    rw [← integral_add hB hC]
    congr 1 with x; ring
  rw [i3] at ibp
  rw [i0, i1, i2]
  linarith

/-- The Leibniz rule for the second distributional derivative of `h f`, `h` smooth and `f`
locally Lipschitz: `⟨(h f)'', ψ⟩ = ⟨f'', h ψ⟩ + ∫ (2 h' f' + h'' f) ψ`. -/
theorem lineDerivOp_lineDerivOp_ofFun_mul_apply {f h : ℝ → ℝ} (hf : LocallyLipschitz f)
    (hh : ContDiff ℝ ∞ h) (ψ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (Distribution.ofFun ⊤ (fun x => h x * f x) volume ⊤)) ψ =
      ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (Distribution.ofFun ⊤ f volume ⊤))
          (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) hh ψ) +
        ∫ x, ψ x * (2 * deriv h x * deriv f x + deriv (deriv h) x * f x) := by
  rw [lineDerivOp_lineDerivOp_ofFun_apply (g := fun x => h x * f x)
      (hh.continuous.mul hf.continuous).locallyIntegrable,
    lineDerivOp_lineDerivOp_ofFun_apply hf.continuous.locallyIntegrable,
    TestFunction.bilinLeftCLM_apply]
  have e : (fun x => ContinuousLinearMap.mul ℝ ℝ (ψ x) (h x)) = fun y => h y * ψ y := by
    funext y; simp [mul_comm]
  rw [e]
  exact integral_deriv_deriv_mul_mul hf (hh.of_le (by simp)) (ψ.contDiff.of_le (by simp))
    ψ.hasCompactSupport

end CalculusOfVariations
