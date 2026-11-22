/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Lipschitz.Periodic
public import CalculusOfVariations.Lipschitz.Cutoff
public import CalculusOfVariations.Lipschitz.Rescale

/-!
# Quasiconvexity with periodic test maps

For a lower semicontinuous, locally bounded `f`, quasiconvexity at `A` on the unit cube is
equivalent to the inequality `f (A) ≤ ∫_{(0,1)^m} f (A + ∇φ)` for `ℤ^m`-periodic Lipschitz `φ`
(`quasiconvexAtOn_iff_periodic`).

"⇒": for a periodic `φ`, the maps `ψ_j = η_{1/j} · j⁻² φ (j² ·)` vanish off the cube, where
`η_δ = ∏ h_δ (x_i)` is a Lipschitz cut-off equal to `1` on `[δ, 1 − δ]^m`; their Lipschitz
constants are bounded in `j`, they agree with `j⁻² φ (j² ·)` on `(δ, 1 − δ)^m`, where
`∫ f (A + ∇φ (j² x)) dx = ∫ f (A + ∇φ)` by periodicity, and the boundary layer has measure
`1 − (1 − 2/j)^m → 0`, on which the integrands are bounded; so
`f (A) ≤ ∫ f (A + ∇ψ_j) → ∫ f (A + ∇φ)`. "⇐": a test map on the cube extends periodically
(`rd_perExt`), Lipschitz because it vanishes on the boundary of the cube, with the same gradient
on the open cube.
-/

@[expose] public section

open Metric Set MeasureTheory Filter Topology
open scoped Pointwise

namespace CalculusOfVariations

variable {d m : ℕ}

/-- The test map `ψ = η_δ · k⁻¹ φ (k ·)` and its Lipschitz constant. -/
private lemma rd_testMap_lipschitz {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) {δ k : ℝ} (hδ : 0 < δ) (hk : 0 < k) :
    LipschitzWith (K + m * M / (δ * k)).toNNReal
      (fun x => rd_eta δ x • (k⁻¹ • φ (k • x))) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
  have e : rd_eta δ x • (k⁻¹ • φ (k • x)) - rd_eta δ y • (k⁻¹ • φ (k • y)) =
      rd_eta δ x • (k⁻¹ • φ (k • x) - k⁻¹ • φ (k • y)) +
        (rd_eta δ x - rd_eta δ y) • (k⁻¹ • φ (k • y)) := by
    rw [smul_sub, sub_smul]; abel
  rw [e]
  have h1 : ‖k⁻¹ • φ (k • x) - k⁻¹ • φ (k • y)‖ ≤ K * ‖x - y‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hk)]
    have := hφ.dist_le_mul (k • x) (k • y)
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hk]
      at this
    calc k⁻¹ * ‖φ (k • x) - φ (k • y)‖ ≤ k⁻¹ * (K * (k * ‖x - y‖)) := by gcongr
      _ = K * ‖x - y‖ := by field_simp
  have h2 : ‖k⁻¹ • φ (k • y)‖ ≤ M / k := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hk), inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (hM _) hk.le
  have h3 := rd_eta_lip hδ x y
  rw [dist_eq_norm] at h3
  have h4 := rd_eta_mem δ x
  calc ‖rd_eta δ x • (k⁻¹ • φ (k • x) - k⁻¹ • φ (k • y)) +
        (rd_eta δ x - rd_eta δ y) • (k⁻¹ • φ (k • y))‖
      ≤ |rd_eta δ x| * ‖k⁻¹ • φ (k • x) - k⁻¹ • φ (k • y)‖ +
        |rd_eta δ x - rd_eta δ y| * ‖k⁻¹ • φ (k • y)‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * (K * ‖x - y‖) + (m * ‖x - y‖ / δ) * (M / k) := by
        gcongr
        · rw [abs_of_nonneg h4.1]; exact h4.2
    _ = (K + m * M / (δ * k)) * ‖x - y‖ := by field_simp

/-- Quasiconvexity on the cube gives the inequality for periodic test maps. The maps
`ψ_j = η_{1/j} · j⁻² φ (j² ·)` are admissible on the cube, with a Lipschitz constant bounded in `j`;
they agree with `j⁻² φ (j² ·)` on the inner cube `(1/j, 1 − 1/j)^m`, where
`∫ f (A + ∇φ (j² x)) = ∫ f (A + ∇φ)` by periodicity, and the boundary layer has measure
`1 − (1 − 2/j)^m → 0`. -/
lemma rd_periodic_of_cube {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ)
    (hq : QuasiconvexAtOn (unitCube m) f A) : QuasiconvexAtPeriodic f A := by
  intro φ K hφ hper _
  obtain ⟨M, hM0, hM⟩ := rd_periodic_bounded hφ hper
  obtain ⟨C, hC0, hC⟩ := rd_bound_near hbdd A (K + m * M)
  have hvolQ : volume (unitCube m) < ⊤ := by rw [rd_volume_unitCube]; exact ENNReal.one_lt_top
  set I := ∫ x in unitCube m, f (A + grad φ x)
  have hFm : Measurable fun x => f (A + grad φ x) :=
    hlsc.measurable.comp (rd_measurable_add_grad A φ)
  have key : ∀ j : ℕ, 3 ≤ j → f A ≤ I + 2 * C * (1 - (1 - 2 / (j : ℝ)) ^ m) := by
    intro j hj
    have hj' : (3 : ℝ) ≤ j := by exact_mod_cast hj
    have hjpos : (0 : ℝ) < j := by linarith
    set δ : ℝ := 1 / j with hδdef
    have hδ : 0 < δ := by positivity
    set k : ℝ := (j : ℝ) ^ 2 with hkdef
    have hk : 0 < k := by positivity
    set ψ : (Fin m → ℝ) → Fin d → ℝ := fun x => rd_eta δ x • (k⁻¹ • φ (k • x)) with hψdef
    have hψ := rd_testMap_lipschitz hφ hM hδ hk
    have hδk : m * M / (δ * k) ≤ m * M := by
      rw [show δ * k = j by rw [hδdef, hkdef]; field_simp]
      exact div_le_self (by positivity) (by linarith)
    have hψK : ((K + m * M / (δ * k)).toNNReal : ℝ) ≤ K + m * M := by
      rw [Real.coe_toNNReal _ (by positivity)]; linarith
    have h0 : ∀ x ∉ unitCube m, ψ x = 0 := fun x hx => by
      simp only [hψdef, rd_eta_zero hδ hx, zero_smul]
    have hq' := hq ψ _ hψ h0 (rd_integrableOn hlsc hbdd A hψ hvolQ)
    rw [rd_volume_unitCube, ENNReal.toReal_one, one_mul] at hq'
    -- the two integrands agree on the inner cube
    set F₁ : (Fin m → ℝ) → ℝ := fun x => f (A + grad ψ x)
    set F₂ : (Fin m → ℝ) → ℝ := fun x => f (A + grad φ (k • x))
    have hagree : ∀ x ∈ unitCube m ∩ rd_inner δ, F₁ x = F₂ x := by
      intro x hx
      have heq : ψ =ᶠ[𝓝 x] fun y => k⁻¹ • φ (k • y) := by
        filter_upwards [(rd_inner_isOpen δ).mem_nhds hx.2] with y hy
        simp only [hψdef, rd_eta_one hδ hy, one_smul]
      have hg : grad ψ x = grad (fun y => k⁻¹ • φ (k • y)) x := by
        ext i l
        simp only [grad, Matrix.of_apply]
        have hi : (fun y => ψ y i) =ᶠ[𝓝 x] fun y => (k⁻¹ • φ (k • y)) i :=
          heq.mono fun y hy => by show ψ y i = (k⁻¹ • φ (k • y)) i; rw [hy]
        rw [Filter.EventuallyEq.fderiv_eq hi]
      simp only [F₁, F₂, hg, rd_grad_rescale φ hk.ne']
    have hF₁b : ∀ x, |F₁ x| ≤ C := fun x => hC _ fun i l =>
      (rd_grad_abs_le hψ x i l).trans hψK
    have hF₂b : ∀ x, |F₂ x| ≤ C := fun x => hC _ fun i l =>
      (rd_grad_abs_le hφ _ i l).trans (by linarith [mul_nonneg (Nat.cast_nonneg m) hM0])
    have hint₁ : IntegrableOn F₁ (unitCube m) := rd_integrableOn hlsc hbdd A hψ hvolQ
    have hint₂ : IntegrableOn F₂ (unitCube m) := by
      refine IntegrableOn.of_bound hvolQ ?_ C (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hF₂b x)
      exact (hFm.comp (measurable_const_smul k)).aestronglyMeasurable
    have hmeas : MeasurableSet (rd_inner (m := m) δ) :=
      MeasurableSet.univ_pi fun _ => measurableSet_Ioo
    have hsplit₁ := integral_inter_add_sdiff hmeas hint₁
    have hsplit₂ := integral_inter_add_sdiff hmeas hint₂
    have hin : ∫ x in unitCube m ∩ rd_inner δ, F₁ x = ∫ x in unitCube m ∩ rd_inner δ, F₂ x :=
      setIntegral_congr_fun ((MeasurableSet.univ_pi fun _ => measurableSet_Ioo).inter hmeas)
        hagree
    -- the boundary layer
    have hinner_sub : rd_inner (m := m) δ ⊆ unitCube m := by
      intro x hx i _
      have := hx i (Set.mem_univ _)
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    have hδ2 : 2 * δ ≤ 1 := by rw [hδdef, mul_one_div, div_le_one hjpos]; linarith
    have hvol_layer : volume.real (unitCube m \ rd_inner (m := m) δ) =
        1 - (1 - 2 / (j : ℝ)) ^ m := by
      rw [Measure.real, measure_sdiff hinner_sub hmeas.nullMeasurableSet (by
          simp only [rd_inner, Real.volume_pi_Ioo]
          exact (ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top).ne),
        rd_volume_unitCube]
      simp only [rd_inner, Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      have hle : ENNReal.ofReal (1 - δ - δ) ^ m ≤ 1 := by
        apply pow_le_one₀ (by simp)
        rw [ENNReal.ofReal_le_one]; linarith
      rw [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top, ENNReal.toReal_one,
        ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith)]
      congr 2
      rw [hδdef]; ring
    have hvol_lt : volume (unitCube m \ rd_inner (m := m) δ) < ⊤ :=
      (measure_mono Set.sdiff_subset).trans_lt hvolQ
    have hb₁ := norm_setIntegral_le_of_norm_le_const hvol_lt (f := F₁) (C := C)
      fun x _ => by rw [Real.norm_eq_abs]; exact hF₁b x
    have hb₂ := norm_setIntegral_le_of_norm_le_const hvol_lt (f := F₂) (C := C)
      fun x _ => by rw [Real.norm_eq_abs]; exact hF₂b x
    rw [hvol_layer, Real.norm_eq_abs] at hb₁ hb₂
    -- the periodic average
    have havg : ∫ x in unitCube m, F₂ x = I := by
      have hGb : ∀ y, |f (A + grad φ y)| ≤ C := fun y => hC _ fun i l =>
        (rd_grad_abs_le hφ y i l).trans (by linarith [mul_nonneg (Nat.cast_nonneg m) hM0])
      have := rd_setIntegral_comp_nsmul hFm hGb ?_ (N := j ^ 2) (by positivity)
      · simpa [F₂, hkdef] using this
      · intro x z
        rw [rd_grad_periodic hper]
    have hF₂avg : ∫ x in unitCube m, F₂ x = I := havg
    have e₁ := abs_le.1 hb₁
    have e₂ := abs_le.1 hb₂
    have hfin : ∫ x in unitCube m, F₁ x ≤ I + 2 * C * (1 - (1 - 2 / (j : ℝ)) ^ m) := by
      rw [← hsplit₁, hin, ← hF₂avg, ← hsplit₂]
      linarith
    exact hq'.trans hfin
  -- the limit `j → ∞`
  have ht : Tendsto (fun j : ℕ => I + 2 * C * (1 - (1 - 2 / (j : ℝ)) ^ m)) atTop
      (𝓝 (I + 2 * C * (1 - (1 - 0) ^ m))) := by
    refine tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_const_nhds.sub
      ((tendsto_const_nhds.sub ?_).pow m)))
    exact tendsto_const_div_atTop_nhds_zero_nat 2
  simp only [sub_zero, one_pow, sub_self, mul_zero, add_zero] at ht
  exact ge_of_tendsto ht (eventually_atTop.2 ⟨3, key⟩)

/-- The inequality for periodic test maps gives quasiconvexity on the cube: a test map on the
cube extends periodically (`rd_perExt`,
Lipschitz since it vanishes on the boundary of the cube), with the same gradient on the open
cube. -/
private lemma rd_cube_of_periodic {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (A : Matrix (Fin d) (Fin m) ℝ) (hp : QuasiconvexAtPeriodic f A) :
    QuasiconvexAtOn (unitCube m) f A := by
  intro φ K hφ h0 hint
  have hopen : IsOpen (unitCube m) := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  have heq : ∀ x ∈ unitCube m, f (A + grad (rd_perExt φ) x) = f (A + grad φ x) :=
    fun x hx => by rw [rd_grad_perExt hx]
  have hmeas : MeasurableSet (unitCube m) := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hint' : IntegrableOn (fun x => f (A + grad (rd_perExt φ) x)) (unitCube m) :=
    hint.congr_fun (fun x hx => (heq x hx).symm) hmeas
  have := hp (rd_perExt φ) _ (rd_perExt_lipschitz hφ h0) (rd_perExt_periodic φ) hint'
  rw [setIntegral_congr_fun hmeas heq] at this
  rw [rd_volume_unitCube, ENNReal.toReal_one, one_mul]
  exact this

/-- **Quasiconvexity with periodic test maps**: for a lower semicontinuous, locally bounded `f`,
quasiconvexity at `A` on the unit cube is equivalent to the inequality for `ℤ^m`-periodic
Lipschitz test maps, that is, on the torus `𝕋^m = ℝ^m / ℤ^m`.

Proof: the argument of S. Müller, *Variational models for microstructure and phase transitions*,
lecture notes, MPI MiS Leipzig, 1998, Proposition 4.19 (a cut-off near the boundary and a rescaled
periodic map), here on the unit cube. "⇒": for a periodic `φ`, the maps
`ψ_j = η_{1/j} · j⁻² φ (j² ·)` vanish off the cube, where `η_δ = ∏ h_δ (x_i)` is a Lipschitz cutoff
equal to `1` on `[δ, 1 − δ]^m`; their Lipschitz constants are bounded in `j`, they agree with
`j⁻² φ (j² ·)` on `(δ, 1 − δ)^m`, where `∫ f (A + ∇φ (j² x)) dx = ∫ f (A + ∇φ)` by periodicity
(`rd_setIntegral_comp_nsmul`), and the boundary layer has measure `1 − (1 − 2/j)^m → 0`, on which
the integrands are bounded (`f` is locally bounded); so `f (A) ≤ ∫ f (A + ∇ψ_j) → ∫ f (A + ∇φ)`.
"⇐": a test map on the cube extends periodically (`rd_perExt`, `x ↦ φ (fract x)`), Lipschitz because
it vanishes on the boundary of the cube, with the same gradient on the open cube.-/
theorem quasiconvexAtOn_iff_periodic {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ) :
    QuasiconvexAtOn (unitCube m) f A ↔ QuasiconvexAtPeriodic f A :=
  ⟨rd_periodic_of_cube hlsc hbdd A, rd_cube_of_periodic A⟩

end CalculusOfVariations
