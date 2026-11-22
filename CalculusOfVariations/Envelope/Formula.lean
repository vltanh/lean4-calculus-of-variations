/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Envelope.Convexity

/-!
# Dacorogna's formula for the quasiconvex envelope

For a continuous `f : ℝ^{d×m} → ℝ`, `f^{qc} (A) = inf_φ ⨍_{B} f (A + ∇φ)` over the Lipschitz `φ`
vanishing outside the Euclidean unit ball `B` (`qcEnvelope_eq_iInf_unitBall`), with values in
`EReal`; and over any nonempty bounded open set in place of `B` (`qcEnvelope_eq_iInf`). B.
Dacorogna, *Quasiconvexity and relaxation of nonconvex problems in the calculus of variations*, J.
Funct. Anal. 46 (1982), 102–118; for integrands with values in `[−∞, ∞)`, S. Müller, *Variational
models for microstructure and phase transitions*, lecture notes, MPI MiS Leipzig, 1998, Theorem 4.5
(iii).

For the ball:

* `cv_le_ball_average`: a quasiconvex minorant of `f` is below every average over the ball, so
  the envelope is below the infimum formula over the ball;
* `cv_ballQ_le`: the infimum formula over the ball is below the infimum formula over the cube
  `cubeInf f`, by gluing rescaled copies of the cube test maps into finitely many disjoint small
  cubes filling the ball up to `ε` (Besicovitch);
* `cubeInf_le_qcEnvelope`: `cubeInf f` is below the envelope, being `≡ −∞` or a continuous
  quasiconvex minorant of `f`. -/

@[expose] public section

open MeasureTheory

namespace CalculusOfVariations

/-! ### The Euclidean unit ball -/

section Ball

variable {d m : ℕ}

open Metric Set Filter Topology

theorem cv_unitBall_isOpen : IsOpen (unitBall m) :=
  isOpen_lt (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2) continuous_const

theorem cv_sq_le_of_mem_unitBall {x : Fin m → ℝ} (hx : x ∈ closure (unitBall m)) (i : Fin m) :
    x i ^ 2 ≤ 1 := by
  have hc : IsClosed {x : Fin m → ℝ | ∑ i, x i ^ 2 ≤ 1} :=
    isClosed_le (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2) continuous_const
  have hsub : closure (unitBall m) ⊆ {x : Fin m → ℝ | ∑ i, x i ^ 2 ≤ 1} :=
    closure_minimal (fun y (hy : ∑ i, y i ^ 2 < 1) => (le_of_lt hy : ∑ i, y i ^ 2 ≤ 1)) hc
  exact (Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg _)
    (Finset.mem_univ i)).trans (hsub hx)

theorem cv_unitBall_subset : unitBall m ⊆ closedBall (0 : Fin m → ℝ) 1 := by
  intro x hx
  rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have := cv_sq_le_of_mem_unitBall (subset_closure hx) i
  rw [Real.norm_eq_abs]
  nlinarith [abs_nonneg (x i), sq_abs (x i)]

theorem cv_unitBall_convex : Convex ℝ (unitBall m) := by
  intro x hx y hy a b ha hb hab
  change ∑ i, (a • x + b • y) i ^ 2 < 1
  have hx' : ∑ i, x i ^ 2 < 1 := hx
  have hy' : ∑ i, y i ^ 2 < 1 := hy
  have h : ∀ i, (a • x + b • y) i ^ 2 ≤ a * x i ^ 2 + b * y i ^ 2 := by
    intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : a * x i ^ 2 + b * y i ^ 2 - (a * x i + b * y i) ^ 2 = a * b * (x i - y i) ^ 2 := by
      have hb' : b = 1 - a := by linarith
      subst hb'; ring
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x i - y i))]
  calc ∑ i, (a • x + b • y) i ^ 2 ≤ ∑ i, (a * x i ^ 2 + b * y i ^ 2) :=
        Finset.sum_le_sum fun i _ => h i
    _ = a * ∑ i, x i ^ 2 + b * ∑ i, y i ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ < 1 := by
        rcases ha.lt_or_eq with ha' | ha'
        · nlinarith
        · subst ha'; simp at hab; subst hab; simpa using hy'

theorem cv_unitBall_pos : 0 < volume (unitBall m) :=
  cv_unitBall_isOpen.measure_pos volume ⟨0, by simp [unitBall]⟩

theorem cv_unitBall_ne_top : volume (unitBall m) ≠ ⊤ :=
  ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono cv_unitBall_subset)

theorem cv_frontier_unitBall : volume (frontier (unitBall m)) = 0 :=
  Convex.addHaar_frontier volume cv_unitBall_convex

/-- The ball of radius `1/2` around the centre of the cube lies in the cube (and its closure in
the closure of the cube). -/
theorem cv_half_ball_subset {x : Fin m → ℝ}
    (hx : (2 : ℝ) • (x - fun _ => (1 / 2 : ℝ)) ∈ closure (unitBall m)) :
    x ∈ closedBall (fun _ => (1 / 2 : ℝ)) (1 / 2) := by
  rw [mem_closedBall, dist_pi_le_iff (by norm_num)]
  intro i
  have := cv_sq_le_of_mem_unitBall hx i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this
  rw [Real.dist_eq, abs_le]
  constructor <;> nlinarith

theorem cv_half_ball_subset' {x : Fin m → ℝ}
    (hx : (2 : ℝ) • (x - fun _ => (1 / 2 : ℝ)) ∈ unitBall m) : x ∈ unitCube m := by
  rw [cv_unitCube_eq_ball, mem_ball, dist_pi_lt_iff (by norm_num)]
  intro i
  set y : Fin m → ℝ := (2 : ℝ) • (x - fun _ => (1 / 2 : ℝ)) with hy
  have hx' : ∑ i, y i ^ 2 < 1 := hx
  have := (Finset.single_le_sum (f := fun i => y i ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ i)).trans_lt hx'
  simp only [hy, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith

/-- A locally bounded function is bounded near `A`. -/
theorem cv_bdd_of_locallyBounded {g : Matrix (Fin d) (Fin m) ℝ → ℝ} (hg : IsLocallyBounded g)
    (A : Matrix (Fin d) (Fin m) ℝ) (R : ℝ) :
    ∃ M, ∀ X : Matrix (Fin d) (Fin m) ℝ, (∀ i k, |X i k| ≤ R) → |g (A + X)| ≤ M := by
  classical
  set S : Set (Matrix (Fin d) (Fin m) ℝ) :=
    (fun X : Fin d → Fin m → ℝ => A + Matrix.of X) '' closedBall 0 (max R 0)
  have hS : IsCompact S := (isCompact_closedBall _ _).image
    (continuous_const.add (continuous_matrixOf.2 continuous_id))
  choose U hU C hC using hg
  obtain ⟨t, -, ht⟩ := hS.elim_nhds_subcover U fun B _ => hU B
  refine ⟨∑ B ∈ t, |C B|, fun X hX => ?_⟩
  have hmem : A + X ∈ S := by
    refine ⟨fun i k => X i k, ?_, rfl⟩
    rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (le_max_right _ _)]
    intro i
    rw [pi_norm_le_iff_of_nonneg (le_max_right _ _)]
    intro k
    rw [Real.norm_eq_abs]
    exact (hX i k).trans (le_max_left _ _)
  obtain ⟨B, hB, hAB⟩ := mem_iUnion₂.1 (ht hmem)
  exact (hC B _ hAB).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun B => |C B|) (fun _ _ => abs_nonneg _) hB))

/-- **A quasiconvex minorant is below the averages over the ball.** For an admissible `g`
(lower semicontinuous, locally bounded, quasiconvex on the unit cube, `g ≤ f`) and a test map `ψ`
on the ball: `g (A) ≤ ⨍_B f (A + ∇ψ)`. The rescaled copy `x ↦ ψ (2 (x - c)) / 2` of `ψ` lives in
the ball of radius `1/2` around the centre `c` of the cube; quasiconvexity on the cube with this
test map gives `g (A) ≤ g (A) + 2^{-m} (∫_B g (A + ∇ψ) - |B| g (A))`, since the gradient vanishes
outside the small ball. -/
theorem cv_le_ball_average {f g : Matrix (Fin d) (Fin m) ℝ → ℝ} (hlsc : LowerSemicontinuous g)
    (hbdd : IsLocallyBounded g) (hqc : Quasiconvex g) (hgf : ∀ B, g B ≤ f B)
    (hf : Continuous f) (A : Matrix (Fin d) (Fin m) ℝ) {ψ : (Fin m → ℝ) → Fin d → ℝ}
    (hψ : (∃ K, LipschitzWith K ψ) ∧ ∀ x ∉ unitBall m, ψ x = 0) :
    g A ≤ (volume (unitBall m)).toReal⁻¹ * ∫ x in unitBall m, f (A + grad ψ x) := by
  obtain ⟨⟨K, hK⟩, hψB⟩ := hψ
  set c : Fin m → ℝ := fun _ => 1 / 2 with hc
  set Ψ := rescaleMap ψ c (1 / 2) with hΨ
  have hΨL : LipschitzWith K Ψ := rescaleMap_lipschitz hK c (by norm_num)
  have hgrad : ∀ x, grad Ψ x = grad ψ ((2 : ℝ) • (x - c)) := by
    intro x; rw [hΨ, rescaleMap_grad _ _ (by norm_num)]; norm_num
  have hΨQ : ∀ x ∉ unitCube m, Ψ x = 0 := by
    intro x hx
    refine rescaleMap_eq_zero hψB c (1 / 2) ?_
    rw [show (1 / 2 : ℝ)⁻¹ = 2 by norm_num]
    exact fun h => hx (cv_half_ball_subset' h)
  obtain ⟨Mg, hMg⟩ := cv_bdd_of_locallyBounded hbdd A K
  have hgm : Measurable fun X : Fin d → Fin m → ℝ => g (Matrix.of X) := by
    have : LowerSemicontinuous fun X : Fin d → Fin m → ℝ => g (Matrix.of X) := hlsc
    exact this.measurable
  -- `F y = g (A + ∇ψ y) - g (A)`
  set F : (Fin m → ℝ) → ℝ := fun y => g (A + grad ψ y) - g A with hF
  have hFm : Measurable F := (cv_measurable_comp_grad hgm A ψ).sub measurable_const
  have hFb : ∀ y, |F y| ≤ Mg + |g A| := fun y =>
    (abs_sub _ _).trans (add_le_add (hMg _ (cv_grad_abs_le hK y)) le_rfl)
  have hF0 : ∀ y, y ∉ closure (unitBall m) → F y = 0 := by
    intro y hy
    have : ψ =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy] with z hz
      exact hψB z fun h => hz (subset_closure h)
    simp [hF, cv_grad_eq_zero this]
  have hFint : ∀ s : Set (Fin m → ℝ), volume s ≠ ⊤ → IntegrableOn F s := fun s hs =>
    Measure.integrableOn_of_bounded (M := Mg + |g A|) hs hFm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hFb y)
  have hQfin : volume (unitCube m) ≠ ⊤ := by rw [cv_volume_unitCube]; exact ENNReal.one_ne_top
  -- quasiconvexity on the cube
  have hint : IntegrableOn (fun x => g (A + grad Ψ x)) (unitCube m) := by
    refine Measure.integrableOn_of_bounded (M := Mg) hQfin
      (cv_measurable_comp_grad hgm A Ψ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]; exact hMg _ (cv_grad_abs_le hΨL x)
  have hq := hqc A Ψ K hΨL hΨQ hint
  rw [cv_volume_unitCube, ENNReal.toReal_one, one_mul] at hq
  -- the integral over the cube
  have e1 : ∫ x in unitCube m, g (A + grad Ψ x) =
      g A + ∫ x in unitCube m, F ((2 : ℝ) • (x - c)) := by
    have : ∀ x, g (A + grad Ψ x) = g A + F ((2 : ℝ) • (x - c)) := fun x => by
      simp [hF, hgrad]
    simp only [this]
    rw [integral_add (integrableOn_const hQfin), setIntegral_const, smul_eq_mul, Measure.real,
      cv_volume_unitCube, ENNReal.toReal_one, one_mul]
    have : (fun x => F ((2 : ℝ) • (x - c))) =
        (fun x => g (A + grad Ψ x) - g A) := by ext x; simp [hF, hgrad]
    rw [this]
    exact hint.sub (integrableOn_const hQfin)
  have e2 : ∫ x in unitCube m, F ((2 : ℝ) • (x - c)) = ∫ x, F ((2 : ℝ) • (x - c)) := by
    refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (Convex.addHaar_frontier volume (convex_ball c (1 / 2) : Convex ℝ (ball c (1 / 2))))]
      with x hxf hxQ
    refine hF0 _ fun h => ?_
    have h1 := cv_half_ball_subset h
    rw [← closure_ball c (by norm_num : (1 / 2 : ℝ) ≠ 0), closure_eq_self_union_frontier] at h1
    rcases h1 with h1 | h1
    · exact hxQ (by rw [cv_unitCube_eq_ball]; exact h1)
    · exact hxf h1
  have e3 : ∫ x, F ((2 : ℝ) • (x - c)) = (1 / 2) ^ m * ∫ y, F y := by
    have := cv_integral_comp_affine F c (by norm_num : (0 : ℝ) < 1 / 2)
    rwa [show (1 / 2 : ℝ)⁻¹ = 2 by norm_num] at this
  have e4 : ∫ y, F y = ∫ y in unitBall m, F y := by
    refine (setIntegral_eq_integral_of_ae_compl_eq_zero ?_).symm
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 cv_frontier_unitBall] with y hyf hyB
    refine hF0 y fun h => ?_
    rw [closure_eq_self_union_frontier] at h
    rcases h with h | h
    · exact hyB h
    · exact hyf h
  have e5 : ∫ y in unitBall m, F y =
      (∫ y in unitBall m, g (A + grad ψ y)) - (volume (unitBall m)).toReal * g A := by
    rw [hF, integral_sub _ (integrableOn_const cv_unitBall_ne_top), setIntegral_const,
      smul_eq_mul, Measure.real]
    have : (fun y => g (A + grad ψ y)) = fun y => F y + g A := by ext y; simp [hF]
    rw [this]
    exact (hFint _ cv_unitBall_ne_top).add (integrableOn_const cv_unitBall_ne_top)
  rw [e1, e2, e3, e4, e5] at hq
  have hpos : 0 < (1 / 2 : ℝ) ^ m := by positivity
  have hB : 0 <
      (volume (unitBall m)).toReal := ENNReal.toReal_pos cv_unitBall_pos.ne' cv_unitBall_ne_top
  have h1 : (volume (unitBall m)).toReal * g A ≤ ∫ y in unitBall m, g (A + grad ψ y) := by
    nlinarith
  have h2 : ∫ y in unitBall m, g (A + grad ψ y) ≤ ∫ y in unitBall m, f (A + grad ψ y) := by
    refine setIntegral_mono_on ?_ (cv_integrableOn hf A hK cv_unitBall_ne_top)
      cv_unitBall_isOpen.measurableSet fun y _ => hgf _
    have : (fun y => g (A + grad ψ y)) = fun y => F y + g A := by ext y; simp [hF]
    rw [this]
    exact (hFint _ cv_unitBall_ne_top).add (integrableOn_const cv_unitBall_ne_top)
  rw [le_inv_mul_iff₀ hB]
  linarith

/-- The arithmetic of the gluing into the ball. -/
theorem cv_ball_estimate {m : ℕ} {ε b T I M G : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hb : 0 < b)
    (hM0 : 0 ≤ M) (hT0 : 0 ≤ T) (hT1 : b - ε ≤ T) (hT2 : T ≤ b)
    (hG : G ≤ (1 - ε) ^ m * T * I + M * (b - (1 - ε) ^ m * T)) :
    b⁻¹ * G ≤ I + b⁻¹ * (m * b + 1) * (M + |I|) * ε := by
  have hpow0 : 0 ≤ (1 - ε) ^ m := pow_nonneg (by linarith) m
  have hpow1 : (1 - ε) ^ m ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hbern : 1 + (m : ℝ) * (-ε) ≤ (1 + -ε) ^ m :=
    one_add_le_pow_of_two_add_nonneg (by linarith) m
  rw [← sub_eq_add_neg] at hbern
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hbern' : 1 - m * ε ≤ (1 - ε) ^ m := by linarith
  set a := (1 - ε) ^ m * T with ha
  have ha1 : a ≤ b := by nlinarith
  have ha2 : b - a ≤ (m * b + 1) * ε := by
    have h1 : (1 - ε) ^ m * (b - ε) ≤ a := mul_le_mul_of_nonneg_left hT1 hpow0
    have h2 : (1 - m * ε) * (b - ε) ≤ (1 - ε) ^ m * (b - ε) ∨ b - ε < 0 := by
      rcases le_or_gt 0 (b - ε) with h | h
      · exact Or.inl (mul_le_mul_of_nonneg_right hbern' h)
      · exact Or.inr h
    rcases h2 with h2 | h2
    · have : 0 ≤ (m : ℝ) * ε * ε := by positivity
      nlinarith
    · nlinarith
  have hkey : G ≤ b * I + (b - a) * (M + |I|) := by
    have e : a * I + M * (b - a) = b * I + (b - a) * (M - I) := by ring
    have h3 : (b - a) * (M - I) ≤ (b - a) * (M + |I|) :=
      mul_le_mul_of_nonneg_left (by linarith [neg_abs_le I]) (by linarith)
    linarith
  rw [inv_mul_le_iff₀ hb]
  have h4 : (b - a) * (M + |I|) ≤ (m * b + 1) * ε * (M + |I|) :=
    mul_le_mul_of_nonneg_right ha2 (by positivity)
  have e : b * (I + b⁻¹ * (m * b + 1) * (M + |I|) * ε) = b * I + (m * b + 1) * ε * (M + |I|) := by
    field_simp
  rw [e]
  linarith

/-- **Gluing into the ball.** Copies of a test map on the cube, glued into finitely many disjoint
small cubes filling the ball up to `ε` (Besicovitch), give `⨍_B f (A + ∇Φ) ≤ ∫_Q f (A + ∇φ) + O(ε)`;
hence the infimum formula over the ball is at most `cubeInf f`. -/
theorem cv_ballQ_le {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) :
    (⨅ (φ : (Fin m → ℝ) → Fin d → ℝ) (_ : (∃ K, LipschitzWith K φ) ∧ ∀ x ∉ unitBall m, φ x = 0),
      (((volume (unitBall m)).toReal⁻¹ * ∫ x in unitBall m, f (A + grad φ x) : ℝ) : EReal)) ≤
      cubeInf f A := by
  refine le_iInf₂ fun φ hφ => ?_
  obtain ⟨⟨K, hK⟩, hφQ⟩ := hφ
  set I := ∫ y in unitCube m, f (A + grad φ y) with hI
  set b := (volume (unitBall m)).toReal with hbdef
  have hb : 0 < b := ENNReal.toReal_pos cv_unitBall_pos.ne' cv_unitBall_ne_top
  obtain ⟨M, hM0, hM⟩ := cv_bdd hf A (3 * (0 : NNReal) + 1)
  refine cv_ereal_le_of_eps (C := b⁻¹ * (m * b + 1) * (M + |I|)) (by positivity)
    fun ε hε0 hε1 => ?_
  -- the cover of the ball by small cubes
  obtain ⟨t, htP, htdisj, htvol⟩ := cv_exists_finite_cover (s := unitBall m) cv_unitBall_ne_top
    cv_unitBall_isOpen.measurableSet (fun x r => closedBall x r ⊆ unitBall m)
    (Filter.Eventually.of_forall fun x hx δ hδ => by
      obtain ⟨ε', hε', hball⟩ := Metric.isOpen_iff.1 cv_unitBall_isOpen x hx
      refine ⟨min (δ / 2) (ε' / 2), ⟨lt_min (by linarith) (by linarith),
        (min_le_left _ _).trans_lt (by linarith)⟩, ?_⟩
      exact (closedBall_subset_ball ((min_le_right _ _).trans_lt (by linarith))).trans hball)
    (ENNReal.ofReal_pos.2 hε0)
  have hzero : ∀ x, tangentMap (fun _ : Fin m → ℝ => (0 : Fin d → ℝ)) x = fun _ => 0 := by
    intro x; ext z; simp [tangentMap]
  obtain ⟨Φ, ⟨hΦL, hΦB⟩, hΦle⟩ := cv_glue_on hf A (φ := fun _ => 0) (K := 0)
    (LipschitzWith.const _) cv_unitBall_ne_top (fun _ _ => rfl) hε0 (by linarith) t
    (fun p hp => ⟨(htP p hp).1, (htP p hp).2, differentiableAt_const _, fun z _ => by
      rw [hzero]; simp only [sub_self, norm_zero]
      exact mul_nonneg hε0.le (htP p hp).1.le⟩) htdisj (fun _ => φ)
    (fun _ _ => ⟨⟨K, hK⟩, hφQ⟩) hM
  have hg0 : ∀ x, grad (fun _ : Fin m → ℝ => (0 : Fin d → ℝ)) x = 0 := fun x =>
    cv_grad_eq_zero (Filter.Eventually.of_forall fun _ => rfl)
  simp only [hg0, add_zero] at hΦle
  refine (iInf₂_le Φ ⟨hΦL, hΦB⟩).trans (EReal.coe_le_coe_iff.2 ?_)
  -- the measures
  have hV : ∀ p ∈ t, volume.real (closedBall p.1 p.2) = (2 * p.2) ^ m := fun p hp =>
    cv_measureReal_closedBall _ (htP p hp).1.le
  set T := ∑ p ∈ t, volume.real (closedBall p.1 p.2) with hTdef
  have hUC : (⋃ p ∈ t, closedBall p.1 p.2) ⊆ unitBall m := by
    intro z hz
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hz
    exact (htP p hp).2 hzp
  have hUCm : MeasurableSet (⋃ p ∈ t, closedBall p.1 p.2) :=
    Finset.measurableSet_biUnion _ fun _ _ => measurableSet_closedBall
  have hT : T = volume.real (⋃ p ∈ t, closedBall p.1 p.2) :=
    (measureReal_biUnion_finset htdisj (fun _ _ => measurableSet_closedBall)
      (fun _ _ => measure_closedBall_lt_top.ne)).symm
  have hrest : volume.real (unitBall m \ ⋃ p ∈ t, closedBall p.1 p.2) ≤ ε :=
    (ENNReal.toReal_lt_of_lt_ofReal htvol).le
  have hbB : volume.real (unitBall m) = b := by rw [hbdef, measureReal_def]
  have hTeq : T = b - volume.real (unitBall m \ ⋃ p ∈ t, closedBall p.1 p.2) := by
    rw [measureReal_sdiff hUC hUCm cv_unitBall_ne_top, hbB, hT]; ring
  have hrest0 : 0 ≤ volume.real (unitBall m \ ⋃ p ∈ t, closedBall p.1 p.2) := measureReal_nonneg
  set U := ⋃ p ∈ t, ball p.1 ((1 - ε) * p.2) with hUdef
  have hUB : U ⊆ unitBall m := by
    intro z hz
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hz
    have h1 : (1 - ε) * p.2 ≤ p.2 := by nlinarith [(htP p hp).1]
    exact (htP p hp).2 (ball_subset_closedBall (ball_subset_ball h1 hzp))
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion _ fun _ _ => measurableSet_ball
  have hUvol : volume.real U = (1 - ε) ^ m * T := by
    rw [hUdef, measureReal_biUnion_finset (fun p hp q hq hpq => by
      have h1 : (1 - ε) * p.2 ≤ p.2 := by nlinarith [(htP p hp).1]
      have h2 : (1 - ε) * q.2 ≤ q.2 := by nlinarith [(htP q hq).1]
      exact (htdisj hp hq hpq).mono (ball_subset_closedBall.trans (closedBall_subset_closedBall h1))
        (ball_subset_closedBall.trans (closedBall_subset_closedBall h2)))
      (fun _ _ => measurableSet_ball) (fun _ _ => measure_ball_lt_top.ne), hTdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hr := (htP p hp).1
    rw [cv_measureReal_ball _ (mul_pos (by linarith) hr), hV p hp, ← mul_pow]
    ring_nf
  have hBU : volume.real (unitBall m \ U) = b - (1 - ε) ^ m * T := by
    rw [measureReal_sdiff hUB hUm cv_unitBall_ne_top, hUvol, hbB]
  have hsum : ∑ p ∈ t, (2 * ((1 - ε) * p.2)) ^ m * I = (1 - ε) ^ m * T * I := by
    rw [hTdef, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hV p hp, mul_pow, mul_pow, mul_pow]
    ring
  rw [hsum, hBU] at hΦle
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => measureReal_nonneg
  have := cv_ball_estimate (m := m) hε0 hε1 hb hM0 hT0 (by linarith) (by linarith) hΦle
  linarith

/-- **Dacorogna's formula on the unit ball**: for a continuous `f : ℝ^{d×m} → ℝ` and every `A`,
`f^{qc} (A) = inf_φ ⨍_{B} f (A + ∇φ)` over the Lipschitz `φ` vanishing outside the Euclidean unit
ball `B` (that is, `φ ∈ W^{1,∞}_0 (B, ℝ^d)` extended by `0`), with values in `EReal`.

`qcEnvelope f ≤ inf_B` because a quasiconvex minorant is below every average over the ball
(`cv_le_ball_average`); `inf_B ≤ cubeInf f`, the infimum formula on the cube, by gluing copies of
the cube test maps into the ball (`cv_ballQ_le`); and `cubeInf f ≤ qcEnvelope f` because `cubeInf f`
is either `≡ −∞` or a continuous quasiconvex minorant of `f` (`cubeInf_le_qcEnvelope`). -/
theorem qcEnvelope_eq_iInf_unitBall {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) :
    qcEnvelope f A =
      ⨅ (φ : (Fin m → ℝ) → Fin d → ℝ) (_ : (∃ K, LipschitzWith K φ) ∧ ∀ x ∉ unitBall m, φ x = 0),
        (((volume (unitBall m)).toReal⁻¹ * ∫ x in unitBall m, f (A + grad φ x) : ℝ) : EReal) := by
  refine le_antisymm ?_ ((cv_ballQ_le hf A).trans (cubeInf_le_qcEnvelope hf A))
  refine iSup₂_le fun g hg => le_iInf₂ fun φ hφ => ?_
  obtain ⟨hlsc, hbdd, hqc, hgf⟩ := hg
  exact EReal.coe_le_coe_iff.2 (cv_le_ball_average hlsc hbdd hqc hgf hf A hφ)

/-- **Dacorogna's formula** (B. Dacorogna, J. Funct. Anal. 46 (1982); for integrands unbounded
below, Müller 1998, Theorem 4.5 (iii)): for a continuous `f : ℝ^{d×m} → ℝ`, every nonempty bounded
open `Ω ⊆ ℝ^m` and every `A`, `f^{qc} (A) = inf_φ ⨍_Ω f (A + ∇φ)` over the Lipschitz `φ` vanishing
outside `Ω` (that is, `φ ∈ W^{1,∞}_0 (Ω, ℝ^d)` extended by `0`), with values in `EReal`.
Müller states it for domains with `|∂Ω| = 0`; for any bounded open domain the boundary is handled
by the vanishing of the gradient of a Lipschitz map almost everywhere on its zero set
(`Lipschitz.ZeroSet`), as in `quasiconvexAtOn_iff`.

PLACEHOLDER: the route of the proof is pending its source. The proof of S. Müller (lecture notes,
1998, Theorem 4.5 (iii) and §4.8) runs as follows: the infimum formula `Qf` does not depend on the
domain; `Qf ≥ f^{qc}`; `⨍ Qf (F + ∇ψ) ≥ Qf (F)` for piecewise affine `ψ ∈ W^{1,∞}_0`
(`cubeInf_le_sum_of_piecewiseAffine`), by gluing almost minimisers on the pieces; with the laminates
of `Quasiconvex.Laminate` this makes `Qf` rank-one convex, hence locally Lipschitz; and (4.28) with
"density arguments" makes it quasiconvex (here: piecewise affine approximation by Kuhn–Freudenthal
interpolation, `Lipschitz.PiecewiseAffine`). -/
theorem qcEnvelope_eq_iInf {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    {Ω : Set (Fin m → ℝ)} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (A : Matrix (Fin d) (Fin m) ℝ) :
    qcEnvelope f A =
      ⨅ (φ : (Fin m → ℝ) → Fin d → ℝ) (_ : (∃ K, LipschitzWith K φ) ∧ ∀ x ∉ Ω, φ x = 0),
        (((volume Ω).toReal⁻¹ * ∫ x in Ω, f (A + grad φ x) : ℝ) : EReal) := by
  sorry

end Ball

end CalculusOfVariations
