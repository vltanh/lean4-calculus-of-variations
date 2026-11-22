/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Lipschitz.Mollify

/-!
# The Fourier inequality for a quadratic form under the Legendre–Hadamard condition

If the coefficients `c` satisfy the Legendre–Hadamard condition
`∑ c_{ikjl} (a_i ξ_k) (a_j ξ_l) ≥ 0`, then `∑ c_{ikjl} ∫ ∂_k φ_i ∂_l φ_j ≥ 0`:

* `plancherel_smooth_nonneg`: for smooth compactly supported maps on a real inner product space,
  from Plancherel's theorem for Schwartz functions (`SchwartzMap.integral_inner_fourier_fourier`)
  and `𝓕 (∂_v ψ) = 2πi ⟨ξ, v⟩ 𝓕 ψ` (`SchwartzMap.fourier_lineDerivOp_eq`): the integral is
  `4π² ∫ ∑ c_{ikjl} ⟨ξ, v_k⟩ ⟨ξ, v_l⟩ Re (conj (ψ̂_i) ψ̂_j)`, a sum of the Legendre–Hadamard forms
  at `Re ψ̂` and at `Im ψ̂`;
* `plancherel_smooth_pi_nonneg`: the same on `ℝ^m = Fin m → ℝ`, through the measure-preserving
  identification with `EuclideanSpace ℝ (Fin m)`;
* `plancherel_lipschitz_nonneg`: the same for compactly supported Lipschitz maps, by mollification
  (`Lipschitz.Mollify`).
-/

@[expose] public section

open MeasureTheory SchwartzMap Filter Topology ContinuousLinearMap
open scoped FourierTransform ComplexConjugate ComplexInnerProductSpace LineDeriv ContDiff Pointwise

namespace CalculusOfVariations

section Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier transform of a line derivative, paired with another one. -/
theorem plancherel_fourier_lineDeriv_mul (Ψ Φ : 𝓢(V, ℂ)) (v w : V) (ξ : V) :
    conj (𝓕 (∂_{v} Ψ) ξ) * 𝓕 (∂_{w} Φ) ξ =
      ((4 * Real.pi ^ 2 * (inner ℝ ξ v * inner ℝ ξ w) : ℝ) : ℂ) * (conj (𝓕 Ψ ξ) * 𝓕 Φ ξ) := by
  have hv : (inner ℝ · v).HasTemperateGrowth := ((innerSL ℝ).flip v).hasTemperateGrowth
  have hw : (inner ℝ · w).HasTemperateGrowth := ((innerSL ℝ).flip w).hasTemperateGrowth
  rw [fourier_lineDerivOp_eq, fourier_lineDerivOp_eq]
  simp only [FunLike.coe_smul, Pi.smul_apply, smulLeftCLM_apply_apply hv,
    smulLeftCLM_apply_apply hw, smul_eq_mul, Complex.real_smul, map_mul, Complex.conj_ofReal]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat, map_ofNat,
    Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The product `conj f * g` of two Schwartz functions is integrable. -/
theorem plancherel_integrable_conj_mul (f g : 𝓢(V, ℂ)) :
    Integrable (fun ξ => conj (f ξ) * g ξ) := by
  refine g.integrable.bdd_mul (c := SchwartzMap.seminorm ℝ 0 0 f)
    (Complex.continuous_conj.comp f.continuous).aestronglyMeasurable ?_
  filter_upwards with ξ
  simpa [Complex.norm_conj] using norm_le_seminorm ℝ f ξ

/-- Plancherel for two line derivatives of Schwartz functions. -/
theorem plancherel_lineDeriv (Ψ Φ : 𝓢(V, ℂ)) (v w : V) :
    ∫ x, conj (∂_{v} Ψ x) * ∂_{w} Φ x =
      ∫ ξ, ((4 * Real.pi ^ 2 * (inner ℝ ξ v * inner ℝ ξ w) : ℝ) : ℂ) *
        (conj (𝓕 Ψ ξ) * 𝓕 Φ ξ) := by
  have h := integral_inner_fourier_fourier (∂_{v} Ψ) (∂_{w} Φ)
  simp only [RCLike.inner_apply'] at h
  rw [← h]
  congr 1
  ext ξ
  exact plancherel_fourier_lineDeriv_mul Ψ Φ v w ξ

/-- A smooth compactly supported real function, as a complex Schwartz function. -/
noncomputable def plancherelSchwartz (ψ : V → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) : 𝓢(V, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun x => (ψ x : ℂ))
    (hψc.comp_left Complex.ofReal_zero) (Complex.ofRealCLM.contDiff.comp hψ)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem plancherelSchwartz_lineDeriv (ψ : V → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (v x : V) :
    ∂_{v} (plancherelSchwartz ψ hψ hψc) x = (fderiv ℝ ψ x v : ℂ) := by
  rw [lineDerivOp_apply_eq_fderiv]
  have hd : HasFDerivAt (fun y => (ψ y : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ ψ x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x
      ((hψ.differentiable (by simp)).differentiableAt.hasFDerivAt)
  change fderiv ℝ (fun y => (ψ y : ℂ)) x v = _
  rw [hd.fderiv]
  rfl

/-- **The Fourier inequality** for smooth compactly supported maps on a real inner product
space: if the coefficients `c` satisfy the Legendre–Hadamard condition
`∑ c_{ikjl} (a_i ⟨ξ, v_k⟩) (a_j ⟨ξ, v_l⟩) ≥ 0`, then
`∑ c_{ikjl} ∫ ∂_{v_k} ψ_i ∂_{v_l} ψ_j ≥ 0`. By Plancherel and `𝓕 (∂_v ψ) = 2πi ⟨ξ, v⟩ 𝓕 ψ`,
the integral is `4π² ∫ ∑ c_{ikjl} ⟨ξ, v_k⟩ ⟨ξ, v_l⟩ Re (conj (ψ̂_i) ψ̂_j)`, and the integrand is the
sum of the Legendre–Hadamard forms at `Re ψ̂` and at `Im ψ̂`. -/
theorem plancherel_smooth_nonneg {d m : ℕ} (ψ : Fin d → V → ℝ) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    (hψc : ∀ i, HasCompactSupport (ψ i)) (v : Fin m → V)
    (c : Fin d → Fin m → Fin d → Fin m → ℝ)
    (hc : ∀ (a : Fin d → ℝ) (ξ : V),
      0 ≤ ∑ i, ∑ k, ∑ j, ∑ l, c i k j l * (a i * inner ℝ ξ (v k)) * (a j * inner ℝ ξ (v l))) :
    0 ≤ ∑ i, ∑ k, ∑ j, ∑ l, c i k j l *
      ∫ x, fderiv ℝ (ψ i) x (v k) * fderiv ℝ (ψ j) x (v l) := by
  set Ψ : Fin d → 𝓢(V, ℂ) := fun i => plancherelSchwartz (ψ i) (hψ i) (hψc i) with hΨ
  -- each real integral is the real part of the complex one
  have h1 : ∀ i k j l, ∫ x, fderiv ℝ (ψ i) x (v k) * fderiv ℝ (ψ j) x (v l) =
      (∫ ξ, ((4 * Real.pi ^ 2 * (inner ℝ ξ (v k) * inner ℝ ξ (v l)) : ℝ) : ℂ) *
        (conj (𝓕 (Ψ i) ξ) * 𝓕 (Ψ j) ξ)).re := by
    intro i k j l
    rw [← plancherel_lineDeriv]
    simp only [hΨ, plancherelSchwartz_lineDeriv, Complex.conj_ofReal, ← Complex.ofReal_mul,
      integral_complex_ofReal, Complex.ofReal_re]
  have hint : ∀ i k j l, Integrable (fun ξ =>
      ((4 * Real.pi ^ 2 * (inner ℝ ξ (v k) * inner ℝ ξ (v l)) : ℝ) : ℂ) *
        (conj (𝓕 (Ψ i) ξ) * 𝓕 (Ψ j) ξ)) := by
    intro i k j l
    have := plancherel_integrable_conj_mul (𝓕 (∂_{v k} (Ψ i))) (𝓕 (∂_{v l} (Ψ j)))
    refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
    exact plancherel_fourier_lineDeriv_mul (Ψ i) (Ψ j) (v k) (v l) ξ
  have h2 : ∀ i k j l, c i k j l * ∫ x, fderiv ℝ (ψ i) x (v k) * fderiv ℝ (ψ j) x (v l) =
      ∫ ξ, c i k j l * (4 * Real.pi ^ 2 * (inner ℝ ξ (v k) * inner ℝ ξ (v l)) *
        ((𝓕 (Ψ i) ξ).re * (𝓕 (Ψ j) ξ).re + (𝓕 (Ψ i) ξ).im * (𝓕 (Ψ j) ξ).im)) := by
    intro i k j l
    have := integral_re (hint i k j l)
    simp only [RCLike.re_to_complex] at this
    rw [h1, ← this, ← integral_const_mul]
    congr 1
    ext ξ
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im, zero_mul, sub_zero]
    ring
  have hint2 : ∀ i k j l, Integrable (fun ξ => c i k j l *
      (4 * Real.pi ^ 2 * (inner ℝ ξ (v k) * inner ℝ ξ (v l)) *
        ((𝓕 (Ψ i) ξ).re * (𝓕 (Ψ j) ξ).re + (𝓕 (Ψ i) ξ).im * (𝓕 (Ψ j) ξ).im))) := by
    intro i k j l
    refine ((hint i k j l).re.const_mul (c i k j l)).congr
      (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, zero_mul, sub_zero]
    ring
  simp only [h2]
  have hsum : ∀ (s : Finset (Fin d)) (t : Finset (Fin m)) (u : Finset (Fin d))
      (w : Finset (Fin m)) (F : Fin d → Fin m → Fin d → Fin m → V → ℝ),
      (∀ i k j l, Integrable (F i k j l)) →
      ∑ i ∈ s, ∑ k ∈ t, ∑ j ∈ u, ∑ l ∈ w, ∫ ξ, F i k j l ξ =
        ∫ ξ, ∑ i ∈ s, ∑ k ∈ t, ∑ j ∈ u, ∑ l ∈ w, F i k j l ξ := by
    intro s t u w F hF
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => hF i k j l]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => hF i k j l]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => hF i k j l]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun l _ => hF i k j l]
  rw [hsum _ _ _ _ _ hint2]
  refine integral_nonneg fun ξ => ?_
  have e : ∑ i, ∑ k, ∑ j, ∑ l, c i k j l *
      (4 * Real.pi ^ 2 * (inner ℝ ξ (v k) * inner ℝ ξ (v l)) *
        ((𝓕 (Ψ i) ξ).re * (𝓕 (Ψ j) ξ).re + (𝓕 (Ψ i) ξ).im * (𝓕 (Ψ j) ξ).im)) =
      4 * Real.pi ^ 2 * (∑ i, ∑ k, ∑ j, ∑ l, c i k j l *
        ((𝓕 (Ψ i) ξ).re * inner ℝ ξ (v k)) * ((𝓕 (Ψ j) ξ).re * inner ℝ ξ (v l))) +
      4 * Real.pi ^ 2 * (∑ i, ∑ k, ∑ j, ∑ l, c i k j l *
        ((𝓕 (Ψ i) ξ).im * inner ℝ ξ (v k)) * ((𝓕 (Ψ j) ξ).im * inner ℝ ξ (v l))) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  simp only at e ⊢
  rw [e]
  have hpi : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  exact add_nonneg (mul_nonneg hpi (hc _ ξ)) (mul_nonneg hpi (hc _ ξ))

end Fourier

/-- The Fourier inequality for smooth compactly supported maps on `ℝ^m = Fin m → ℝ` (through the
measure-preserving identification with `EuclideanSpace ℝ (Fin m)`): if
`∑ c_{ikjl} (a_i ξ_k) (a_j ξ_l) ≥ 0` for all `a, ξ`, then `∑ c_{ikjl} ∫ ∂_k ψ_i ∂_l ψ_j ≥ 0`. -/
theorem plancherel_smooth_pi_nonneg {d m : ℕ} (ψ : Fin d → (Fin m → ℝ) → ℝ)
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (hψc : ∀ i, HasCompactSupport (ψ i))
    (c : Fin d → Fin m → Fin d → Fin m → ℝ)
    (hc : ∀ (a : Fin d → ℝ) (ξ : Fin m → ℝ),
      0 ≤ ∑ i, ∑ k, ∑ j, ∑ l, c i k j l * (a i * ξ k) * (a j * ξ l)) :
    0 ≤ ∑ i, ∑ k, ∑ j, ∑ l, c i k j l *
      ∫ x, fderiv ℝ (ψ i) x (Pi.single k 1) * fderiv ℝ (ψ j) x (Pi.single l 1) := by
  set e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ) with he
  have h := plancherel_smooth_nonneg (V := EuclideanSpace ℝ (Fin m)) (fun i => ψ i ∘ e)
    (fun i => (hψ i).comp e.contDiff) (fun i => (hψc i).comp_homeomorph e.toHomeomorph)
    (fun k => EuclideanSpace.single k 1) c (fun a ξ => by
      simpa [EuclideanSpace.inner_single_right] using hc a (fun k => ξ k))
  have hd : ∀ i k (y : EuclideanSpace ℝ (Fin m)),
      fderiv ℝ (ψ i ∘ e) y (EuclideanSpace.single k 1) = fderiv ℝ (ψ i) (e y) (Pi.single k 1) := by
    intro i k y
    rw [e.comp_right_fderiv]
    rfl
  simp only [hd] at h
  have hint : ∀ F : (Fin m → ℝ) → ℝ, ∫ y : EuclideanSpace ℝ (Fin m), F (e y) = ∫ x, F x := by
    intro F
    exact (PiLp.volume_preserving_ofLp (Fin m)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm.measurableEmbedding F
  have hint' : ∀ i k j l, ∫ y : EuclideanSpace ℝ (Fin m),
      fderiv ℝ (ψ i) (e y) (Pi.single k 1) * fderiv ℝ (ψ j) (e y) (Pi.single l 1) =
      ∫ x, fderiv ℝ (ψ i) x (Pi.single k 1) * fderiv ℝ (ψ j) x (Pi.single l 1) :=
    fun i k j l => hint (fun x => fderiv ℝ (ψ i) x (Pi.single k 1) *
      fderiv ℝ (ψ j) x (Pi.single l 1))
  simpa only [hint'] using h

/-- **The Fourier inequality for Lipschitz maps.** For compactly
supported Lipschitz `φ_i : ℝ^m → ℝ`, `∑ c_{ikjl} ∫ ∂_k φ_i ∂_l φ_j ≥ 0` when `c` satisfies the
Legendre–Hadamard condition. The smooth case is `plancherel_smooth_pi_nonneg`; the mollifications
`ρ_n ⋆ φ_i` are smooth with compact support, and their derivatives `ρ_n ⋆ ∂_k φ_i` are bounded,
supported in a fixed compact set, and converge to `∂_k φ_i` almost everywhere. -/
theorem plancherel_lipschitz_nonneg {d m : ℕ} (φ : Fin d → (Fin m → ℝ) → ℝ) (K : Fin d → NNReal)
    (hφ : ∀ i, LipschitzWith (K i) (φ i)) (hφc : ∀ i, HasCompactSupport (φ i))
    (c : Fin d → Fin m → Fin d → Fin m → ℝ)
    (hc : ∀ (a : Fin d → ℝ) (ξ : Fin m → ℝ),
      0 ≤ ∑ i, ∑ k, ∑ j, ∑ l, c i k j l * (a i * ξ k) * (a j * ξ l)) :
    0 ≤ ∑ i, ∑ k, ∑ j, ∑ l, c i k j l *
      ∫ x, fderiv ℝ (φ i) x (Pi.single k 1) * fderiv ℝ (φ j) x (Pi.single l 1) := by
  set ψ : ℕ → Fin d → (Fin m → ℝ) → ℝ :=
    fun n i => plancherelMollify volume (plancherelBump m n) (φ i) with hψ
  have hψs : ∀ n i, ContDiff ℝ ∞ (ψ n i) := fun n i =>
    plancherelMollify_contDiff _ (hφ i).continuous
  have hψn : ∀ n, 0 ≤ ∑ i, ∑ k, ∑ j, ∑ l, c i k j l *
      ∫ x, fderiv ℝ (ψ n i) x (Pi.single k 1) * fderiv ℝ (ψ n j) x (Pi.single l 1) :=
    fun n => plancherel_smooth_pi_nonneg (ψ n) (hψs n)
      (fun i => plancherelMollify_hasCompactSupport _ (hφc i)) c hc
  -- the bound on the derivatives and their support
  have hbd : ∀ n i (v : Fin m → ℝ) x, |fderiv ℝ (ψ n i) x v| ≤ K i * ‖v‖ := by
    intro n i v x
    rw [plancherelMollify_fderiv _ (hφ i)]
    exact plancherelMollify_abs_le _ (fun y => by
      simpa [Real.norm_eq_abs] using norm_lineDeriv_le_of_lipschitz ℝ (hφ i) (x₀ := y) (v := v)) x
  have hsupp : ∀ n i (v : Fin m → ℝ) x,
      x ∉ Metric.closedBall (0 : Fin m → ℝ) 1 + tsupport (φ i) → fderiv ℝ (ψ n i) x v = 0 := by
    intro n i v x hx
    rw [plancherelMollify_fderiv _ (hφ i)]
    exact plancherelMollify_eq_zero _ (plancherelBump_rOut_le m n)
      (fun y hy => plancherel_lineDeriv_eq_zero_of_notMem hy v) hx
  have hlim : ∀ i k j l, Tendsto (fun n =>
      ∫ x, fderiv ℝ (ψ n i) x (Pi.single k 1) * fderiv ℝ (ψ n j) x (Pi.single l 1)) atTop
      (𝓝 (∫ x, fderiv ℝ (φ i) x (Pi.single k 1) * fderiv ℝ (φ j) x (Pi.single l 1))) := by
    intro i k j l
    set S := Metric.closedBall (0 : Fin m → ℝ) 1 + tsupport (φ i)
    have hS : IsCompact S := (isCompact_closedBall _ _).add (hφc i)
    refine tendsto_integral_of_dominated_convergence
      (S.indicator fun _ => (K i * ‖(Pi.single k 1 : Fin m → ℝ)‖) *
        (K j * ‖(Pi.single l 1 : Fin m → ℝ)‖)) (fun n => ?_) ?_ (fun n => ?_) ?_
    · exact (((hψs n i).continuous_fderiv (by simp)).clm_apply continuous_const).mul
        (((hψs n j).continuous_fderiv (by simp)).clm_apply continuous_const)
        |>.aestronglyMeasurable
    · exact (integrable_indicator_iff hS.measurableSet).2
        (integrableOn_const hS.measure_lt_top.ne)
    · filter_upwards with x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hbd n i _ x) (hbd n j _ x) (abs_nonneg _) (by positivity)
      · rw [Set.indicator_of_notMem hx, hsupp n i _ x hx]
        simp
    · filter_upwards [plancherel_ae_tendsto (hφ i) (Pi.single k 1),
        plancherel_ae_tendsto (hφ j) (Pi.single l 1)] with x hx1 hx2
      exact hx1.mul hx2
  have hlimsum := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun k _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun j _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun l _ =>
      (hlim i k j l).const_mul (c i k j l)
  exact ge_of_tendsto' hlimsum hψn

end CalculusOfVariations
