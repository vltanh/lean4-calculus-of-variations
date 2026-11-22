/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Quasiconvex.Laminate
public import CalculusOfVariations.Quasiconvex.Periodic
public import CalculusOfVariations.Convex.SeparatelyConvex

/-!
# A quasiconvex integrand is rank-one convex

`rankOneConvex_of_quasiconvex`: a lower semicontinuous, locally bounded `f` that is quasiconvex
on the unit cube at every matrix is rank-one convex.

The proof uses periodic laminates in integer directions: with the periodic form of
quasiconvexity (`Quasiconvex.Periodic`), the periodic laminate `u (x) = h_λ (n · x) a`
(`h_λ` the sawtooth of `Quasiconvex.Laminate`, `n ∈ ℤ^m ∖ {0}`) gives the two-point inequality
`f (A) ≤ λ f (A + (1 − λ) a ⊗ n) + (1 − λ) f (A − λ a ⊗ n)`, because
`∫_{(0,1)^m} F (n · x) dx = ∫_0^1 F` for `1`-periodic `F` (`rd_integral_dir`). In the coordinate
directions this makes `f` convex in each entry, hence continuous; the inequality extends to
rational directions by scaling and to real ones by continuity.

The argument of S. Müller (lecture notes, 1998, Lemma 4.3), a laminate on a cube with faces
orthogonal to the rank-one direction, is stated in `Quasiconvex.Laminate`.
-/

@[expose] public section

open Metric Set MeasureTheory Filter Topology
open scoped Pointwise

namespace CalculusOfVariations

variable {d m : ℕ}

/-- The one-dimensional substitution for a `1`-periodic `F` and an integer `N ≠ 0`:
`∫_0^1 F (N t + b) dt = ∫_0^1 F`. -/
private lemma rd_integral_comp_mul_add_periodic {F : ℝ → ℝ} (hF : Function.Periodic F 1)
    (hFi : ∀ a b, IntervalIntegrable F volume a b) {N : ℤ} (hN : N ≠ 0) (b : ℝ) :
    ∫ t in (0 : ℝ)..1, F (N * t + b) = ∫ t in (0 : ℝ)..1, F t := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [intervalIntegral.integral_comp_mul_add F hN' b]
  simp only [mul_zero, zero_add, mul_one]
  have h1 := hF.intervalIntegral_add_zsmul_eq N b hFi
  rw [show (N : ℝ) + b = b + N • (1 : ℝ) by rw [zsmul_eq_mul, mul_one, add_comm], h1,
    hF.intervalIntegral_add_eq b 0, zero_add, zsmul_eq_mul, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hN', one_mul]

/-- The average along an integer direction: for a bounded measurable `1`-periodic `F` and
`n ∈ ℤ^m ∖ {0}`, `∫_{(0,1)^m} F (n · x) dx = ∫_0^1 F` (Fubini in a coordinate `c` with
`n_c ≠ 0`, and the one-dimensional substitution). -/
private lemma rd_integral_dir {F : ℝ → ℝ} (hFm : Measurable F) {C : ℝ} (hFb : ∀ t, |F t| ≤ C)
    (hF : Function.Periodic F 1) {n : Fin m → ℤ} (hn : n ≠ 0) :
    ∫ x in unitCube m, F (∑ j, (n j : ℝ) * x j) = ∫ t in (0 : ℝ)..1, F t := by
  obtain ⟨c, hc⟩ := Function.ne_iff.1 hn
  cases m with
  | zero => exact c.elim0
  | succ m' =>
  have hFi : ∀ a b, IntervalIntegrable F volume a b := fun a b =>
    (IntegrableOn.of_bound (by rw [Set.uIcc]; exact measure_Icc_lt_top) hFm.aestronglyMeasurable C
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hFb t)).intervalIntegrable
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m' + 1) => ℝ) c
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m' + 1) => ℝ) c
  set G : (Fin (m' + 1) → ℝ) → ℝ := fun x => F (∑ j, (n j : ℝ) * x j)
  have hpre : e ⁻¹' (Ioo (0 : ℝ) 1 ×ˢ unitCube m') = unitCube (m' + 1) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, unitCube, Set.mem_pi, Set.mem_univ, true_implies,
      e, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.coe_mk, Fin.insertNthEquiv,
      Equiv.coe_fn_symm_mk]
    constructor
    · rintro ⟨h1, h2⟩ i
      rcases Fin.eq_self_or_eq_succAbove c i with rfl | ⟨j, rfl⟩
      · exact h1
      · exact h2 j
    · intro h
      exact ⟨h c, fun j => h _⟩
  have h1 := hmp.setIntegral_preimage_emb e.measurableEmbedding (G ∘ e.symm)
    (Ioo (0 : ℝ) 1 ×ˢ unitCube m')
  simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply, hpre] at h1
  rw [h1, show (volume : Measure (ℝ × (Fin m' → ℝ))) = volume.prod volume from rfl,
    ← setIntegral_prod_swap (Ioo (0 : ℝ) 1) (unitCube m') (fun y => G (e.symm y))]
  have hint : IntegrableOn (fun z : (Fin m' → ℝ) × ℝ => G (e.symm z.swap))
      (unitCube m' ×ˢ Ioo (0 : ℝ) 1) (volume.prod volume) := by
    refine IntegrableOn.of_bound ?_ ?_ C (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hFb _)
    · rw [Measure.prod_prod]
      simp only [unitCube, Real.volume_pi_Ioo, Real.volume_Ioo]
      exact ENNReal.mul_lt_top (ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top)
        ENNReal.ofReal_lt_top
    · refine Measurable.aestronglyMeasurable ?_
      exact hFm.comp ((Finset.measurable_sum _ fun j _ => (measurable_const.mul
        (measurable_pi_apply j))).comp (e.symm.measurable.comp measurable_swap))
  rw [setIntegral_prod _ hint]
  -- the inner integral, over the coordinate `c`
  have hinner : ∀ y : Fin m' → ℝ, ∫ t in Ioo (0 : ℝ) 1, G (e.symm (y, t).swap) =
      ∫ t in (0 : ℝ)..1, F t := by
    intro y
    have hsum : ∀ t : ℝ, ∑ j, (n j : ℝ) * (e.symm (t, y)) j =
        (n c : ℝ) * t + ∑ j, (n (c.succAbove j) : ℝ) * y j := by
      intro t
      rw [Fin.sum_univ_succAbove _ c]
      simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
    simp only [Prod.swap_prod_mk, G, hsum]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    exact rd_integral_comp_mul_add_periodic hF hFi hc _
  simp only [hinner]
  rw [setIntegral_const]
  simp [unitCube, Real.volume_pi_Ioo, Measure.real]


/-- The linear form `x ↦ n · x`. -/
private noncomputable def rd_lin (n : Fin m → ℤ) : (Fin m → ℝ) →L[ℝ] ℝ :=
  ∑ j, (n j : ℝ) • ContinuousLinearMap.proj j

private lemma rd_lin_apply (n : Fin m → ℤ) (x : Fin m → ℝ) :
    rd_lin n x = ∑ j, (n j : ℝ) * x j := by
  simp [rd_lin]

/-- The chain rule for `h ∘ (n · )`, also where `h` is not differentiable (then neither is the
composite, since `n ≠ 0`). -/
private lemma rd_fderiv_comp_lin {h : ℝ → ℝ} {n : Fin m → ℤ} (hn : n ≠ 0) (x : Fin m → ℝ) :
    fderiv ℝ (fun y => h (rd_lin n y)) x = deriv h (rd_lin n x) • rd_lin n := by
  by_cases hd : DifferentiableAt ℝ h (rd_lin n x)
  · exact (HasDerivAt.comp_hasFDerivAt x hd.hasDerivAt (rd_lin n).hasFDerivAt).fderiv
  · obtain ⟨c, hc⟩ := Function.ne_iff.1 hn
    have hc' : (n c : ℝ) ≠ 0 := by exact_mod_cast hc
    set γ : ℝ → Fin m → ℝ := fun t => x + ((t - rd_lin n x) / n c) • Pi.single c 1
    have hγ : ∀ t, rd_lin n (γ t) = t := by
      intro t
      simp only [γ, map_add, map_smul, smul_eq_mul]
      rw [rd_lin_apply n (Pi.single c 1)]
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      field_simp
      ring
    have hnd : ¬ DifferentiableAt ℝ (fun y => h (rd_lin n y)) x := by
      intro hdiff
      apply hd
      have hγx : γ (rd_lin n x) = x := by simp [γ]
      have heq : h = (fun y => h (rd_lin n y)) ∘ γ := funext fun t => by simp [hγ]
      rw [heq]
      refine DifferentiableAt.comp _ (by rw [hγx]; exact hdiff) ?_
      exact (((differentiableAt_id.sub_const _).div_const _).smul_const _).const_add x
    rw [fderiv_zero_of_not_differentiableAt hnd, deriv_zero_of_not_differentiableAt hd, zero_smul]

/-- The laminate test map `u (x) = h_λ (n · x) a`, with gradient `h_λ' (n · x) a ⊗ n`. -/
private lemma rd_grad_laminate {l : ℝ} (a : Fin d → ℝ) {n : Fin m → ℤ} (hn : n ≠ 0)
    (x : Fin m → ℝ) :
    grad (fun y => rd_saw l (rd_lin n y) • a) x =
      deriv (rd_saw l) (rd_lin n x) • Matrix.vecMulVec a (fun k => (n k : ℝ)) := by
  ext i k
  simp only [grad, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  have : (fun y => rd_saw l (rd_lin n y) * a i) = a i • fun y => rd_saw l (rd_lin n y) := by
    funext y; simp [mul_comm]
  rw [this, fderiv_const_smul_field, Pi.smul_apply, rd_fderiv_comp_lin hn]
  have hk : rd_lin n (Pi.single k 1) = n k := by
    rw [rd_lin_apply]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  simp only [smul_apply, smul_eq_mul, hk, Matrix.smul_apply, Matrix.vecMulVec_apply]
  ring

/-- The two-point inequality along an integer rank-one direction, from the periodic laminate
`u (x) = h_λ (n · x) a`: `f (A) ≤ λ f (A + (1 − λ) a ⊗ n) + (1 − λ) f (A − λ a ⊗ n)`
(see `rankOneConvex_of_quasiconvex`). -/
private lemma rd_two_point {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hlsc : LowerSemicontinuous f)
    (hbdd : IsLocallyBounded f) {A : Matrix (Fin d) (Fin m) ℝ} (hper : QuasiconvexAtPeriodic f A)
    (a : Fin d → ℝ) {n : Fin m → ℤ} (hn : n ≠ 0) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) :
    f A ≤ l * f (A + (1 - l) • Matrix.vecMulVec a (fun k => (n k : ℝ))) +
      (1 - l) * f (A - l • Matrix.vecMulVec a (fun k => (n k : ℝ))) := by
  set R := Matrix.vecMulVec a (fun k => (n k : ℝ))
  set u : (Fin m → ℝ) → Fin d → ℝ := fun y => rd_saw l (rd_lin n y) • a
  set F : ℝ → ℝ := fun t => f (A + deriv (rd_saw l) t • R)
  have hsaw := rd_saw_lipschitz hl0.le hl1.le
  -- `u` is a periodic Lipschitz test map
  have hu : LipschitzWith (‖a‖₊ * (1 * ‖rd_lin n‖₊)) u := by
    have h3 : LipschitzWith ‖a‖₊ (fun t : ℝ => t • a) := LipschitzWith.of_dist_le_mul fun s t => by
      rw [dist_eq_norm, dist_eq_norm, ← sub_smul, norm_smul, mul_comm]; rfl
    exact h3.comp (hsaw.comp (rd_lin n).lipschitzWith)
  have huper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), u (x + fun i => (z i : ℝ)) = u x := by
    intro x z
    simp only [u, map_add]
    rw [rd_lin_apply n (fun i => (z i : ℝ)),
      show ∑ j, (n j : ℝ) * (z j : ℝ) = ((∑ j, n j * z j : ℤ) : ℝ) by push_cast; rfl,
      rd_saw_add_int]
  -- the integrand is `F (n · x)`
  have hgrad : ∀ x, f (A + grad u x) = F (∑ j, (n j : ℝ) * x j) := fun x => by
    show f (A + grad (fun y => rd_saw l (rd_lin n y) • a) x) = _
    rw [rd_grad_laminate a hn x, rd_lin_apply]
  have hderiv : ∀ t, |deriv (rd_saw l) t| ≤ 1 := fun t => by
    have := norm_deriv_le_of_lipschitz (x₀ := t) hsaw
    simpa using this
  obtain ⟨C, -, hC⟩ := rd_bound_near hbdd A (∑ i, ∑ k, |R i k|)
  have hFb : ∀ t, |F t| ≤ C := fun t => hC _ fun i k => by
    simp only [Matrix.smul_apply, smul_eq_mul, abs_mul]
    calc |deriv (rd_saw l) t| * |R i k| ≤ 1 * |R i k| := by gcongr; exact hderiv t
      _ ≤ ∑ i, ∑ k, |R i k| := by
        rw [one_mul]
        exact (Finset.single_le_sum (f := fun k' => |R i k'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ k)).trans (Finset.single_le_sum (f := fun i' => ∑ k', |R i' k'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  have hFm : Measurable F := by
    refine hlsc.measurable.comp (Measurable.of_eval_matrix _ fun i k => ?_)
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact measurable_const.add ((measurable_deriv (rd_saw l)).mul measurable_const)
  have hFper : Function.Periodic F 1 := fun t => by
    have : deriv (rd_saw l) (t + 1) = deriv (rd_saw l) t := by
      rw [← deriv_comp_add_const]
      congr 1
      funext s
      have := rd_saw_add_int l s 1
      simpa using this
    simp only [F, this]
  have hFi : ∀ a b, IntervalIntegrable F volume a b := fun a b =>
    (IntegrableOn.of_bound (by rw [Set.uIcc]; exact measure_Icc_lt_top) hFm.aestronglyMeasurable C
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hFb t)).intervalIntegrable
  have hvolQ : volume (unitCube m) < ⊤ := by rw [rd_volume_unitCube]; exact ENNReal.one_lt_top
  have key := hper u _ hu huper (rd_integrableOn hlsc hbdd A hu hvolQ)
  simp only [hgrad] at key
  rw [rd_integral_dir hFm hFb hFper hn,
    ← intervalIntegral.integral_add_adjacent_intervals (hFi 0 l) (hFi l 1)] at key
  have hne : ∀ b : ℝ, ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({b} : Set ℝ) := fun b =>
    measure_eq_zero_iff_ae_notMem.1 (Real.volume_singleton)
  have hI1 : ∫ t in (0 : ℝ)..l, F t = l * f (A + (1 - l) • R) := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => f (A + (1 - l) • R)) ?_,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    filter_upwards [hne l] with t ht htmem
    rw [Set.uIoc_of_le hl0.le] at htmem
    have htl : t < l := lt_of_le_of_ne htmem.2 (by simpa using ht)
    have hft : Int.fract t = t := Int.fract_eq_self.2 ⟨htmem.1.le, by linarith⟩
    simp only [F]
    rw [(rd_saw_hasDerivAt_up hl1 (by rw [hft]; exact htmem.1) (by rw [hft]; exact htl)).deriv]
  have hI2 : ∫ t in l..1, F t = (1 - l) * f (A - l • R) := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => f (A - l • R)) ?_,
      intervalIntegral.integral_const, smul_eq_mul]
    filter_upwards [hne 1] with t ht htmem
    rw [Set.uIoc_of_le hl1.le] at htmem
    have ht1 : t < 1 := lt_of_le_of_ne htmem.2 (by simpa using ht)
    have hft : Int.fract t = t := Int.fract_eq_self.2 ⟨by linarith [htmem.1], ht1⟩
    simp only [F]
    rw [(rd_saw_hasDerivAt_down hl0 (by rw [hft]; exact htmem.1)).deriv, neg_smul,
      ← sub_eq_add_neg]
  rw [hI1, hI2] at key
  exact key


/-- A function satisfying the two-point convexity inequality is convex. -/
private lemma rd_convex_of_two_point {g : ℝ → ℝ}
    (h : ∀ x y l : ℝ, 0 < l → l < 1 → g (l * x + (1 - l) * y) ≤ l * g x + (1 - l) * g y) :
    ConvexOn ℝ univ g := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  simp only [smul_eq_mul]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp
  rcases eq_or_lt_of_le hb with hb0 | hb'
  · have : a = 1 := by linarith
    subst this; simp
  · exact h x y a ha' (by linarith)

/-- Convexity along the line `t ↦ A₀ + t B` from the two-point inequality in the directions
`c B`. -/
private lemma rd_convex_line {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (A₀ B : Matrix (Fin d) (Fin m) ℝ)
    (h2 : ∀ (P : Matrix (Fin d) (Fin m) ℝ) (c l : ℝ), 0 < l → l < 1 →
      f P ≤ l * f (P + (1 - l) • (c • B)) + (1 - l) * f (P - l • (c • B))) :
    ConvexOn ℝ univ (fun t : ℝ => f (A₀ + t • B)) := by
  apply rd_convex_of_two_point
  intro x y l hl0 hl1
  have := h2 (A₀ + (l * x + (1 - l) * y) • B) (x - y) l hl0 hl1
  rwa [show A₀ + (l * x + (1 - l) * y) • B + (1 - l) • ((x - y) • B) = A₀ + x • B by module,
    show A₀ + (l * x + (1 - l) * y) • B - l • ((x - y) • B) = A₀ + y • B by module] at this

/-- A matrix of rank one is `a ⊗ q`. -/
private lemma rd_rank_one_eq {B : Matrix (Fin d) (Fin m) ℝ} (hB : B.rank = 1) :
    ∃ (a : Fin d → ℝ) (q : Fin m → ℝ), B = Matrix.vecMulVec a q := by
  rw [Matrix.rank_eq_finrank_span_cols] at hB
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.1 hB
  choose c hc using fun k : Fin m => hv ⟨B.col k, Submodule.subset_span ⟨k, rfl⟩⟩
  refine ⟨(v : Fin d → ℝ), c, ?_⟩
  ext i k
  have h1 : ((c k • v : Submodule.span ℝ (Set.range B.col)) : Fin d → ℝ) i = B i k :=
    congrArg (fun w : Submodule.span ℝ (Set.range B.col) => (w : Fin d → ℝ) i) (hc k)
  rw [Matrix.vecMulVec_apply, ← h1, mul_comm]
  rfl

/-- The approximants `⌊(N + 1) x⌋ / (N + 1) → x`. -/
private lemma rd_tendsto_floor_div (x : ℝ) :
    Tendsto (fun N : ℕ => (⌊((N : ℝ) + 1) * x⌋ : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 x) := by
  have hlow : Tendsto (fun N : ℕ => x - 1 / ((N : ℝ) + 1)) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun N => ?_)
    (fun N => ?_)
  · have hN : (0 : ℝ) < N + 1 := by positivity
    rw [le_div_iff₀ hN, sub_mul, one_div_mul_cancel hN.ne']
    linarith [Int.lt_floor_add_one (((N : ℝ) + 1) * x), mul_comm x ((N : ℝ) + 1)]
  · have hN : (0 : ℝ) < N + 1 := by positivity
    rw [div_le_iff₀ hN]
    linarith [Int.floor_le (((N : ℝ) + 1) * x), mul_comm x ((N : ℝ) + 1)]

/-- **A quasiconvex integrand is rank-one convex**: a lower semicontinuous, locally bounded `f`
that is quasiconvex on the unit cube at every matrix is rank-one convex.

Proof, with periodic laminates: by the periodic form of quasiconvexity (`rd_periodic_of_cube`),
`f` is quasiconvex at every `A` with periodic test maps. For an integer direction `n ≠ 0`, a vector
`a` and `λ ∈ (0, 1)`, the periodic laminate `u (x) = h_λ (n · x) a` (`h_λ` the sawtooth with slopes
`1 − λ` and `−λ`) has `∇u = h_λ' (n · x) a ⊗ n`, and `∫_{(0,1)^m} F (n · x) dx = ∫_0^1 F` for
`1`-periodic `F` (Fubini in a coordinate with `n_c ≠ 0`, `rd_integral_dir`), which gives
`f (A) ≤ λ f (A + (1 − λ) a ⊗ n) + (1 − λ) f (A − λ a ⊗ n)` (`rd_two_point`). In the coordinate
directions this makes `f` convex in each entry, hence continuous (as in
`RankOneConvex.locallyLipschitz`); the inequality extends to rational directions by scaling and to
real ones by continuity, and a rank-one matrix is `a ⊗ q` (`rd_rank_one_eq`).

The argument of S. Müller, *Variational models for microstructure and phase transitions*, lecture
notes, MPI MiS Leipzig, 1998, Lemma 4.3, lays the laminate in the direction `n ∈ ℝ^m` on a cube with
faces orthogonal to `n`, which gives every real direction at once; its steps are stated in
`Quasiconvex.Laminate`. -/
theorem rankOneConvex_of_quasiconvex {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) (hf : Quasiconvex f) :
    RankOneConvex f := by
  have hper : ∀ A, QuasiconvexAtPeriodic f A := fun A => rd_periodic_of_cube hlsc hbdd A (hf A)
  -- the two-point inequality along integer directions (periodic laminates)
  have h2int : ∀ (P : Matrix (Fin d) (Fin m) ℝ) (a : Fin d → ℝ) (n : Fin m → ℤ) (l : ℝ),
      0 < l → l < 1 → f P ≤ l * f (P + (1 - l) • Matrix.vecMulVec a (fun k => (n k : ℝ))) +
        (1 - l) * f (P - l • Matrix.vecMulVec a (fun k => (n k : ℝ))) := by
    intro P a n l hl0 hl1
    by_cases hn : n = 0
    · subst hn
      have : Matrix.vecMulVec a (fun k => ((0 : Fin m → ℤ) k : ℝ)) = 0 := by
        ext i k; simp [Matrix.vecMulVec_apply]
      rw [this, smul_zero, smul_zero, add_zero, sub_zero]
      linarith
    · exact rd_two_point hlsc hbdd (hper P) a hn hl0 hl1
  -- convexity in each entry, hence continuity (as in `RankOneConvex.locallyLipschitz`)
  have hsep : ∀ (A : Matrix (Fin d) (Fin m) ℝ) (i : Fin d) (j : Fin m),
      ConvexOn ℝ univ (fun t : ℝ => f (A + t • Matrix.single i j 1)) := by
    intro A i j
    refine rd_convex_line _ _ fun P c l hl0 hl1 => ?_
    have e : c • Matrix.single i j (1 : ℝ) = Matrix.vecMulVec (c • Pi.single i 1)
        (fun k => ((Pi.single j (1 : ℤ) : Fin m → ℤ) k : ℝ)) := by
      ext a b
      simp only [Matrix.smul_apply, Matrix.single_apply, Matrix.vecMulVec_apply, Pi.smul_apply,
        Pi.single_apply, smul_eq_mul]
      split_ifs <;> simp_all
    rw [e]
    exact h2int P _ _ l hl0 hl1
  have hcont : Continuous f := (Matrix.locallyLipschitz_of_convexOn_single hsep).continuous
  -- the two-point inequality along every rank-one direction `a ⊗ q`, by rational approximation
  have h2real : ∀ (P : Matrix (Fin d) (Fin m) ℝ) (a : Fin d → ℝ) (q : Fin m → ℝ) (l : ℝ),
      0 < l → l < 1 → f P ≤ l * f (P + (1 - l) • Matrix.vecMulVec a q) +
        (1 - l) * f (P - l • Matrix.vecMulVec a q) := by
    intro P a q l hl0 hl1
    set qs : ℕ → Fin m → ℝ := fun N k => (⌊((N : ℝ) + 1) * q k⌋ : ℝ) / ((N : ℝ) + 1)
    have hq : Tendsto qs atTop (𝓝 q) := tendsto_pi_nhds.2 fun k => rd_tendsto_floor_div (q k)
    have hineq : ∀ N, f P ≤ l * f (P + (1 - l) • Matrix.vecMulVec a (qs N)) +
        (1 - l) * f (P - l • Matrix.vecMulVec a (qs N)) := by
      intro N
      have e : Matrix.vecMulVec a (qs N) = Matrix.vecMulVec (((N : ℝ) + 1)⁻¹ • a)
          (fun k => ((⌊((N : ℝ) + 1) * q k⌋ : ℤ) : ℝ)) := by
        ext i k
        simp only [qs, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      exact h2int P _ _ l hl0 hl1
    have hc : Continuous fun q' : Fin m → ℝ => l * f (P + (1 - l) • Matrix.vecMulVec a q') +
        (1 - l) * f (P - l • Matrix.vecMulVec a q') := by
      have hv : Continuous fun q' : Fin m → ℝ => Matrix.vecMulVec a q' :=
        continuous_const.matrix_vecMulVec continuous_id
      exact (continuous_const.mul (hcont.comp (continuous_const.add (hv.const_smul (1 - l))))).add
        (continuous_const.mul (hcont.comp (continuous_const.sub (hv.const_smul l))))
    exact ge_of_tendsto ((hc.tendsto q).comp hq) (Eventually.of_forall hineq)
  -- a rank-one matrix is `a ⊗ q`
  intro A B hB
  obtain ⟨a, q, rfl⟩ := rd_rank_one_eq hB
  refine rd_convex_line _ _ fun P c l hl0 hl1 => ?_
  rw [show c • Matrix.vecMulVec a q = Matrix.vecMulVec (c • a) q by
    ext i k; simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    ring]
  exact h2real P _ q l hl0 hl1

end CalculusOfVariations
