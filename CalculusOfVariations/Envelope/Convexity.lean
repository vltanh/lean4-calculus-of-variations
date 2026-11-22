/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Envelope.Glue
public import CalculusOfVariations.Convex.SeparatelyConvex

/-!
# Convexity, continuity and quasiconvexity of the infimum formula

For a continuous `f` and the infimum formula `cubeInf f` on the unit cube `Q` (the function `Qf`
of S. Müller, *Variational models for microstructure and phase transitions*, lecture notes, MPI
MiS Leipzig, 1998, §4.8, proof of Theorem 4.5 (iii)), the steps of Müller's proof that `Qf` is
quasiconvex:

* the dichotomy (`cubeInf_bot_line`, `cubeInf_bot_all`): by the two-point inequality
  `cubeInf_le_two_point` along `(s e_i) ⊗ e_j = s E_{ij}` (`env_two_point_single`), the value `−∞`
  at one end of a segment forces `−∞` at its midpoint, hence along every line `B + t E_{ij}`, and
  then, one entry at a time, everywhere ("the rank-1 directions span the space of all matrices");
* in the finite case, `cubeInfReal f`, the real-valued `cubeInf f`, is convex along every line
  `A + t E_{ij}` (`cubeInfReal_convexOn`, from `cubeInf_le_two_point`), hence locally Lipschitz
  (Müller's Remark 3 after Definition 4.2, `Matrix.locallyLipschitz_of_convexOn_single`) and
  continuous (`cubeInfReal_continuous`);
* `cubeInfReal_quasiconvex`: for a test map `φ` on `Q`, the Kuhn–Freudenthal interpolants `I_k φ`
  are piecewise affine test maps; (4.28) (`cubeInf_le_sum_of_piecewiseAffine`) for them reads
  `cubeInf f (A) ≤ ∑ i |P i| cubeInf f (A + ∇ (L i)) = ∫_Q cubeInf f (A + ∇ I_k φ)`
  (`env_integral_piecewiseAffine`); dominated convergence, with `cubeInfReal f` continuous,
  `|∇ I_k φ| ≤ m K` and `∇ I_k φ → ∇φ` almost everywhere, gives
  `cubeInf f (A) ≤ ∫_Q cubeInf f (A + ∇φ)` (Müller's "density arguments");
* `cubeInf_le_qcEnvelope`: `cubeInf f ≤ qcEnvelope f`, since `cubeInf f` is either `≡ −∞` or a
  continuous quasiconvex minorant of `f`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

namespace CalculusOfVariations

variable {d m : ℕ}

/-! ### The two-point inequality along matrix units -/

theorem cv_single_shift (A : Matrix (Fin d) (Fin m) ℝ) (i : Fin d) (j : Fin m) {t₁ t₂ t : ℝ}
    (h : t₁ + t₂ = t) :
    A + Matrix.single i j t₁ + Matrix.single i j t₂ = A + Matrix.single i j t := by
  rw [add_assoc, ← Matrix.single_add, h]

theorem cv_smul_single (i : Fin d) (j : Fin m) (t : ℝ) :
    t • Matrix.single i j (1 : ℝ) = Matrix.single i j t := by
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

/-- The rank-one matrix `(s e_i) ⊗ e_j` is the matrix unit `s E_{ij}`. -/
theorem env_vecMulVec_single (s : ℝ) (i : Fin d) (j : Fin m) :
    Matrix.vecMulVec (Pi.single i s) (Pi.single j 1) = Matrix.single i j s := by
  ext a b
  simp only [Matrix.vecMulVec_apply, Pi.single_apply, Matrix.single_apply]
  split_ifs <;> simp_all

/-- The two-point inequality `cubeInf_le_two_point` with `a = s e_i`:
`cubeInf f (F) ≤ λ cubeInf f (F + (1 − λ) s E_{ij}) + (1 − λ) cubeInf f (F − λ s E_{ij})`. -/
theorem env_two_point_single {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (F : Matrix (Fin d) (Fin m) ℝ) (i : Fin d) (j : Fin m) (s : ℝ) {l : ℝ} (hl0 : 0 < l)
    (hl1 : l < 1) :
    cubeInf f F ≤ (l : EReal) * cubeInf f (F + Matrix.single i j ((1 - l) * s)) +
      ((1 - l : ℝ) : EReal) * cubeInf f (F + Matrix.single i j (-l * s)) := by
  have h := cubeInf_le_two_point hf F (Pi.single i s) j hl0 hl1
  have e : F - Matrix.single i j (l * s) = F + Matrix.single i j (-l * s) := by
    ext a b
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> ring
  rwa [env_vecMulVec_single, Matrix.smul_single, Matrix.smul_single, smul_eq_mul, smul_eq_mul,
    e] at h

/-! ### The dichotomy -/

/-- `-∞` propagates along the lines `B + t E_{ij}`: `B + t E_{ij}` is the midpoint of `B` and
`B + 2 t E_{ij}`, and the two-point inequality there has the term `(1/2) cubeInf f (B) = −∞`. -/
theorem cubeInf_bot_line {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    {B : Matrix (Fin d) (Fin m) ℝ} (hB : cubeInf f B = ⊥) (i : Fin d) (j : Fin m) (t : ℝ) :
    cubeInf f (B + Matrix.single i j t) = ⊥ := by
  have h := env_two_point_single hf (B + Matrix.single i j t) i j (2 * t) (l := 1 / 2)
    (by norm_num) (by norm_num)
  rw [cv_single_shift _ _ _ (show t + -(1 / 2) * (2 * t) = 0 by ring), Matrix.single_zero,
    add_zero, hB, EReal.mul_bot_of_pos (EReal.coe_pos.2 (by norm_num)), EReal.add_bot] at h
  exact le_bot_iff.1 h

/-- **The dichotomy**: if `cubeInf f` takes the value `-∞`, it is `-∞` everywhere (changing one
entry at a time along rank-one lines). -/
theorem cubeInf_bot_all {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    {B : Matrix (Fin d) (Fin m) ℝ} (hB : cubeInf f B = ⊥) (A : Matrix (Fin d) (Fin m) ℝ) :
    cubeInf f A = ⊥ := by
  classical
  have key : ∀ S : Finset (Fin d × Fin m),
      cubeInf f (B + ∑ p ∈ S, Matrix.single p.1 p.2 ((A - B) p.1 p.2)) = ⊥ := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using hB
    | insert p S hp ih =>
      rw [Finset.sum_insert hp, add_comm (Matrix.single p.1 p.2 _), ← add_assoc]
      exact cubeInf_bot_line hf ih _ _ _
  have e : B + ∑ p : Fin d × Fin m, Matrix.single p.1 p.2 ((A - B) p.1 p.2) = A := by
    rw [Fintype.sum_prod_type, ← Matrix.matrix_eq_sum_single (A - B)]
    abel
  have := key Finset.univ
  rwa [e] at this

/-! ### Convexity along the matrix units and continuity in the finite case -/

/-- The real-valued infimum formula, when it is finite. -/
noncomputable def cubeInfReal (f : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  (cubeInf f A).toReal

theorem cubeInf_eq_cubeInfReal {f : Matrix (Fin d) (Fin m) ℝ → ℝ} {A : Matrix (Fin d) (Fin m) ℝ}
    (h : cubeInf f A ≠ ⊥) : cubeInf f A = (cubeInfReal f A : EReal) :=
  (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) (cubeInf_le A)) h).symm

/-- The key inequality of convexity along a line `A₀ + t E_{ij}`, in the finite case: the
two-point inequality at `A₀ + (a x + b y) E_{ij}` with `λ = b` and `s = y − x`. -/
theorem cubeInfReal_convex_ineq {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hfin : ∀ A, cubeInf f A ≠ ⊥) (A₀ : Matrix (Fin d) (Fin m) ℝ) (i : Fin d) (j : Fin m)
    {x y a b : ℝ} (hxy : x < y) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    cubeInfReal f (A₀ + (a * x + b * y) • Matrix.single i j 1) ≤
      a * cubeInfReal f (A₀ + x • Matrix.single i j 1) + b * cubeInfReal f
          (A₀ + y • Matrix.single i j 1) := by
  -- the order `x < y` is not needed: the two-point inequality holds for every `s = y - x`
  have _ := hxy
  have hX : ∀ X, cubeInf f X = (cubeInfReal f X : EReal) := fun X =>
    cubeInf_eq_cubeInfReal (hfin X)
  have h := env_two_point_single hf (A₀ + (a * x + b * y) • Matrix.single i j 1) i j (y - x) hb
    (by linarith)
  rw [cv_smul_single, cv_single_shift _ _ _
      (show a * x + b * y + (1 - b) * (y - x) = y by linear_combination x * hab),
    cv_single_shift _ _ _ (show a * x + b * y + -b * (y - x) = x by linear_combination x * hab),
    ← cv_smul_single i j y, ← cv_smul_single i j x, ← cv_smul_single i j (a * x + b * y)] at h
  simp only [hX] at h
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff,
    show 1 - b = a by linarith] at h
  linarith

theorem cubeInfReal_convexOn {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hfin : ∀ A, cubeInf f A ≠ ⊥) (A₀ : Matrix (Fin d) (Fin m) ℝ) (i : Fin d) (j : Fin m) :
    ConvexOn ℝ univ fun t : ℝ => cubeInfReal f (A₀ + t • Matrix.single i j 1) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · rcases lt_trichotomy x y with hxy | rfl | hxy
      · exact cubeInfReal_convex_ineq hf hfin A₀ i j hxy ha' hb' hab
      · rw [← add_mul, hab, one_mul, ← add_mul, hab, one_mul]
      · have := cubeInfReal_convex_ineq hf hfin A₀ i j hxy hb' ha' (by linarith)
        rw [add_comm (a * x), add_comm (a * cubeInfReal f _)]
        exact this
    · subst hb'
      have : a = 1 := by linarith
      subst this
      simp
  · subst ha'
    have : b = 1 := by linarith
    subst this
    simp

/-- In the finite case, `cubeInf f` is continuous: a function convex in each coordinate direction
is locally Lipschitz (Müller 1998, Remark 3 after Definition 4.2). -/
theorem cubeInfReal_continuous {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hfin : ∀ A, cubeInf f A ≠ ⊥) : Continuous (cubeInfReal f) := by
  exact (Matrix.locallyLipschitz_of_convexOn_single fun A i j =>
    cubeInfReal_convexOn hf hfin A i j).continuous

/-! ### Quasiconvexity in the finite case -/

private lemma env_coe_sum {n : ℕ} (r : Fin n → ℝ) :
    ((∑ i, r i : ℝ) : EReal) = ∑ i, (r i : EReal) :=
  map_sum Real.toERealAddHom r Finset.univ

/-- The integral over the unit cube of `g (A + ∇ψ)` for a map `ψ` agreeing with the affine map
`L i` on the open set `P i`, where the `P i ⊆ Q` are pairwise disjoint and cover `Q` up to a null
set: `∫_Q g (A + ∇ψ) = ∑ i |P i| g (A + ∇ (L i))`. -/
theorem env_integral_piecewiseAffine (g : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin d) (Fin m) ℝ) {n : ℕ} (P : Fin n → Set (Fin m → ℝ))
    (L : Fin n → (Fin m → ℝ) →ᵃ[ℝ] (Fin d → ℝ)) (hPo : ∀ i, IsOpen (P i))
    (hPd : Pairwise (Function.onFun Disjoint P)) (hPQ : ∀ i, P i ⊆ unitCube m)
    (hcov : volume (unitCube m \ ⋃ i, P i) = 0) {ψ : (Fin m → ℝ) → Fin d → ℝ}
    (hψL : ∀ i, ∀ x ∈ P i, ψ x = L i x) :
    ∫ x in unitCube m, g (A + grad ψ x) =
      ∑ i, (volume (P i)).toReal * g (A + LinearMap.toMatrix' (L i).linear) := by
  have hQfin : volume (unitCube m) ≠ ⊤ := by rw [cv_volume_unitCube]; exact ENNReal.one_ne_top
  have hae : unitCube m =ᵐ[volume] ⋃ i, P i := by
    refine ae_eq_set.2 ⟨hcov, ?_⟩
    rw [sdiff_eq_empty.2 (iUnion_subset hPQ), measure_empty]
  have hgrad : ∀ i, ∀ x ∈ P i, grad ψ x = LinearMap.toMatrix' (L i).linear := fun i x hx =>
    glue_grad_eq (hPo i) (hψL i) hx
  have hint : ∀ i, IntegrableOn (fun x => g (A + grad ψ x)) (P i) := fun i =>
    (integrableOn_const (C := g (A + LinearMap.toMatrix' (L i).linear))
      (ne_top_of_le_ne_top hQfin (measure_mono (hPQ i)))).congr_fun
      (fun x hx => by rw [hgrad i x hx]) (hPo i).measurableSet
  rw [setIntegral_congr_set hae, integral_iUnion_fintype (fun i => (hPo i).measurableSet) hPd hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [setIntegral_congr_fun (hPo i).measurableSet (fun x hx => by rw [hgrad i x hx]),
    setIntegral_const, smul_eq_mul, Measure.real]

/-- In the finite case, `cubeInf f` is quasiconvex. For a test map `φ`, (4.28)
(`cubeInf_le_sum_of_piecewiseAffine`) for the piecewise affine Kuhn–Freudenthal interpolants
`I_k φ` gives `cubeInf f (A) ≤ ∫_Q cubeInf f (A + ∇ I_k φ)` (`env_integral_piecewiseAffine`);
the integrands are continuous functions of `∇ I_k φ`, bounded since `|∇ I_k φ| ≤ m K`, and converge
almost everywhere since `∇ I_k φ → ∇φ`, so dominated convergence gives
`cubeInf f (A) ≤ ∫_Q cubeInf f (A + ∇φ)`. -/
theorem cubeInfReal_quasiconvex {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hfin : ∀ A, cubeInf f A ≠ ⊥) : Quasiconvex (cubeInfReal f) := by
  intro A φ K hφ hφQ _
  have hc := cubeInfReal_continuous hf hfin
  have hX : ∀ X, cubeInf f X = (cubeInfReal f X : EReal) := fun X =>
    cubeInf_eq_cubeInfReal (hfin X)
  rw [cv_volume_unitCube, ENNReal.toReal_one, one_mul]
  -- (4.28) for the Kuhn–Freudenthal interpolants
  have hstep : ∀ k, 0 < k →
      cubeInfReal f A ≤ ∫ x in unitCube m, cubeInfReal f (A + grad (kuhnInterpolation k φ) x) := by
    intro k hk
    obtain ⟨n, P, L, hPo, hPd, hPQ, hcov, hPL⟩ := kuhnInterpolation_piecewiseAffineOn φ hk
    have h := cubeInf_le_sum_of_piecewiseAffine hf A P L hPo hPd hPQ hcov
      ⟨_, kuhnInterpolation_lipschitz hφ k⟩ (kuhnInterpolation_eq_zero hφQ k) hPL
    simp only [hX, ← EReal.coe_mul, ← env_coe_sum, EReal.coe_le_coe_iff] at h
    rw [env_integral_piecewiseAffine _ A P L hPo hPd hPQ hcov hPL]
    exact h
  -- dominated convergence
  obtain ⟨M, -, hM⟩ := cv_bdd hc A ((m * K : NNReal) : ℝ)
  have hlim : Tendsto (fun k => ∫ x in unitCube m,
      cubeInfReal f (A + grad (kuhnInterpolation k φ) x)) atTop
      (𝓝 (∫ x in unitCube m, cubeInfReal f (A + grad φ x))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun k => ?_)
      (integrableOn_const (by rw [cv_volume_unitCube]; exact ENNReal.one_ne_top)) (fun k => ?_) ?_
    · exact (cv_measurable_comp_grad (cv_continuous_of hc).measurable A
        (kuhnInterpolation k φ)).aestronglyMeasurable
    · exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact hM _ (cv_grad_abs_le (kuhnInterpolation_lipschitz hφ k) x)
    · filter_upwards [ae_restrict_of_ae (ae_tendsto_grad_kuhnInterpolation hφ)] with x hx
      exact (hc.tendsto _).comp (tendsto_const_nhds.add hx)
  exact ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun k hk => hstep k hk⟩)

/-! ### The infimum formula is below the envelope -/

/-- **`cubeInf f` is below the quasiconvex envelope**: either `cubeInf f ≡ -∞`, or it is a
continuous quasiconvex minorant of `f`. -/
theorem cubeInf_le_qcEnvelope {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) : cubeInf f A ≤ qcEnvelope f A := by
  by_cases hA : cubeInf f A = ⊥
  · rw [hA]; exact bot_le
  have hfin : ∀ B, cubeInf f B ≠ ⊥ := fun B hB => hA (cubeInf_bot_all hf hB A)
  have hc := cubeInfReal_continuous hf hfin
  have hadm : LowerSemicontinuous (cubeInfReal f) ∧ IsLocallyBounded (cubeInfReal f) ∧ Quasiconvex
      (cubeInfReal f) ∧
      ∀ B, cubeInfReal f B ≤ f B := by
    refine ⟨hc.lowerSemicontinuous, fun B => ?_, cubeInfReal_quasiconvex hf hfin, fun B => ?_⟩
    · refine ⟨cubeInfReal f ⁻¹' Metric.ball (cubeInfReal f B) 1, hc.continuousAt.preimage_mem_nhds
        (Metric.ball_mem_nhds _ one_pos), |cubeInfReal f B| + 1, fun C hC => ?_⟩
      rw [mem_preimage, Metric.mem_ball, Real.dist_eq] at hC
      have := abs_sub_abs_le_abs_sub (cubeInfReal f C) (cubeInfReal f B)
      linarith
    · have := cubeInf_le (f := f) B
      rw [cubeInf_eq_cubeInfReal (hfin B), EReal.coe_le_coe_iff] at this
      exact this
  rw [cubeInf_eq_cubeInfReal hA]
  exact le_iSup₂ (f := fun g (_ : LowerSemicontinuous g ∧ IsLocallyBounded g ∧ Quasiconvex g ∧
    ∀ B, g B ≤ f B) => (g A : EReal)) (cubeInfReal f) hadm

end CalculusOfVariations
