/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Envelope.Glue
public import CalculusOfVariations.Envelope.RankOneConvex
public import CalculusOfVariations.Lipschitz.Mollify
public import CalculusOfVariations.Lipschitz.PiecewiseAffine
public import CalculusOfVariations.Quasiconvex.RankOneConvex
public import CalculusOfVariations.RankOneConvex.LocallyLipschitz

/-!
# Continuity and quasiconvexity of the infimum formula

For a continuous `f` and the infimum formula `cubeInf f` on the unit cube `Q`, (iii) and (iv) of
Proposition 8.1 of D. Kinderlehrer and P. Pedregal, *Characterizations of Young measures generated
by gradients*, Arch. Rational Mech. Anal. 115 (1991), 329–365 ([KP], p. 361–362), where the
integrand is `ψ` and the infimum formula `ψ^#`:

* (iii), "If `ψ^# (A₀) > −∞` for some `A₀ ∈ 𝕄`, then `ψ^# ∈ C (𝕄)`". By the two-point inequality
  (ii), the value `−∞` at one end of a segment in a rank-one direction forces `−∞` at its midpoint,
  hence along the whole rank-one line ([KP]: a convex function on a line that is finite at some
  point is finite), and any two matrices are connected by a path of rank-one segments, here along
  the matrix units (`env_two_point_single`, `cubeInf_bot_line`, `cubeInf_bot_all`). In the finite
  case `cubeInfReal f`, the real-valued `cubeInf f`, is rank-one convex
  (`cubeInfReal_rankOneConvex`), hence locally Lipschitz (`RankOneConvex.locallyLipschitz`) and
  continuous (`cubeInfReal_continuous`). [KP] leave this to the reader ("it is easy to check that
  `ψ^#` is finite everywhere and continuous").
* (iv), "If `ψ^# ∈ C (𝕄)`, then it is quasiconvex" (`cubeInfReal_quasiconvex`): [KP] refer to
  B. Dacorogna's book (1989 edition) or to the technique of Step 6 of the proof of their Proposition
  7.2. The latter is followed here: a test map is approximated by piecewise affine ones, `ζ_ε`, with
  `∫ |ψ^# (A + ∇ζ) − ψ^# (A + ∇ζ_ε)| < ε` ((7.14)), and for piecewise affine maps the inequality is
  the gluing inequality `cubeInf_le_sum_of_piecewiseAffine`. [KP] do not prove the approximation;
  here: a test map `φ` on `Q` is first shrunk to a test map `φ'` supported in `(¼, ¾)^m`, which
  changes `∫_Q Qf (A + ∇φ) − Qf (A)` by the factor `2^{−m}` (scaling, `env_integral_rescale_sub`);
  `φ'` is approximated by its mollifications `ψ_n` (smooth, vanishing off `Q`), and `ψ_n` by its
  Kuhn–Freudenthal interpolant `v_n` on a grid fine enough that `|∇v_n − ∇ψ_n| ≤ 1/(n+1)`
  (`kuhnInterpolation_grad_uniform`, a diagonal choice of the triangulation). The `v_n` are
  piecewise affine test maps with `|∇v_n| ≤ m K` and `∇v_n → ∇φ'` almost everywhere; the gluing
  inequality reads `Qf (A) ≤ ∑ i |P i| Qf (A + ∇ (L i)) = ∫_Q Qf (A + ∇v_n)` (`Qf = cubeInf f`,
  `env_integral_piecewiseAffine`), and dominated convergence gives `Qf (A) ≤ ∫_Q Qf (A + ∇φ')`.
  (This is the density argument of the proof of Theorem 4.4 (i) in S. Müller, *Variational models
  for microstructure and phase transitions*, lecture notes, MPI MiS Leipzig, 1998.)
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

/-! ### Rank-one convexity and continuity in the finite case -/

/-- The real-valued infimum formula, when it is finite. -/
noncomputable def cubeInfReal (f : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  (cubeInf f A).toReal

theorem cubeInf_eq_cubeInfReal {f : Matrix (Fin d) (Fin m) ℝ → ℝ} {A : Matrix (Fin d) (Fin m) ℝ}
    (h : cubeInf f A ≠ ⊥) : cubeInf f A = (cubeInfReal f A : EReal) :=
  (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) (cubeInf_le A)) h).symm

/-- The two-point inequality as convexity along a line `A₀ + t B`, `B = a ⊗ n`, in the finite case:
the two-point inequality at `A₀ + (α x + β y) B` with `λ = β` and the direction `(y − x) a ⊗ n`. -/
theorem cubeInfReal_rankOneConvex {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hfin : ∀ A, cubeInf f A ≠ ⊥) : RankOneConvex (cubeInfReal f) := by
  have hX : ∀ X, cubeInf f X = (cubeInfReal f X : EReal) := fun X =>
    cubeInf_eq_cubeInfReal (hfin X)
  intro A₀ B hB
  obtain ⟨a, n, rfl⟩ := exists_eq_vecMulVec_of_rank_eq_one hB
  refine ⟨convex_univ, fun x _ y _ α β hα hβ hαβ => ?_⟩
  simp only [smul_eq_mul]
  rcases hα.lt_or_eq with hα' | hα'
  · rcases hβ.lt_or_eq with hβ' | hβ'
    · have h := cubeInf_le_two_point_vecMulVec hf (A₀ + (α * x + β * y) • Matrix.vecMulVec a n)
        ((y - x) • a) n hβ' (by linarith)
      obtain rfl : α = 1 - β := by linarith
      rw [Matrix.smul_vecMulVec, show A₀ + ((1 - β) * x + β * y) • Matrix.vecMulVec a n +
          (1 - β) • ((y - x) • Matrix.vecMulVec a n) = A₀ + y • Matrix.vecMulVec a n by module,
        show A₀ + ((1 - β) * x + β * y) • Matrix.vecMulVec a n -
          β • ((y - x) • Matrix.vecMulVec a n) = A₀ + x • Matrix.vecMulVec a n by module] at h
      simp only [hX] at h
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
      linarith
    · subst hβ'
      have : α = 1 := by linarith
      subst this
      simp
  · subst hα'
    have : β = 1 := by linarith
    subst this
    simp

/-- In the finite case, `cubeInf f` is continuous ([KP], Proposition 8.1 (iii), "it is easy to
check"): a rank-one convex function is locally Lipschitz (`RankOneConvex.locallyLipschitz`). -/
theorem cubeInfReal_continuous {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hfin : ∀ A, cubeInf f A ≠ ⊥) : Continuous (cubeInfReal f) :=
  (cubeInfReal_rankOneConvex hf hfin).locallyLipschitz.continuous

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

/-- A point `x` with `2 (x − ¼ 𝟙) ∈ Q`, moved by less than `1/4` (sup norm), stays in `Q`. -/
private lemma env_add_mem_unitCube {x b : Fin m → ℝ}
    (hx : (1 / 2 : ℝ)⁻¹ • (x - fun _ => (1 / 4 : ℝ)) ∈ unitCube m) (hb : ‖b‖ < 1 / 4) :
    b + x ∈ unitCube m := by
  intro i _
  have h := hx i (mem_univ i)
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mem_Ioo] at h
  norm_num at h
  have hbi : |b i| < 1 / 4 := by
    rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm b i).trans_lt hb
  rw [abs_lt] at hbi
  simp only [Pi.add_apply, mem_Ioo]
  constructor <;> linarith [h.1, h.2, hbi.1, hbi.2]

/-- **Scaling.** For a continuous `g` and a test map `φ` on the unit cube, the copy
`φ' (x) = ½ φ (2 (x − ¼ 𝟙))` (`rescaleMap φ (¼ 𝟙) ½`), a test map supported in `(¼, ¾)^m`,
satisfies `∫_Q g (A + ∇φ') − g (A) = 2^{−m} (∫_Q g (A + ∇φ) − g (A))`: the gradients of both
vanish almost everywhere off the cube (`rd_ae_grad_eq_zero`), so both sides are integrals over
`ℝ^m` of `g (A + ∇ ·) − g (A)`, and `∇φ' (x) = ∇φ (2 (x − ¼ 𝟙))`. -/
theorem env_integral_rescale_sub {g : Matrix (Fin d) (Fin m) ℝ → ℝ} (hg : Continuous g)
    (A : Matrix (Fin d) (Fin m) ℝ) {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) (hφQ : ∀ x ∉ unitCube m, φ x = 0) :
    (∫ x in unitCube m, g (A + grad (rescaleMap φ (fun _ => 1 / 4) (1 / 2)) x)) - g A =
      (1 / 2) ^ m * ((∫ x in unitCube m, g (A + grad φ x)) - g A) := by
  have hQfin : volume (unitCube m) ≠ ⊤ := by rw [cv_volume_unitCube]; exact ENNReal.one_ne_top
  have hQ1 : volume.real (unitCube m) = 1 := by
    rw [measureReal_def, cv_volume_unitCube, ENNReal.toReal_one]
  -- `∫_Q g (A + ∇ψ) − g (A) = ∫ (g (A + ∇ψ) − g (A))` for a test map `ψ` on the cube
  have hext : ∀ {ψ : (Fin m → ℝ) → Fin d → ℝ} {L : NNReal}, LipschitzWith L ψ →
      (∀ x ∉ unitCube m, ψ x = 0) →
      (∫ x in unitCube m, g (A + grad ψ x)) - g A = ∫ x, (g (A + grad ψ x) - g A) := by
    intro ψ L hψ hψQ
    have h1 : ∫ x in unitCube m, (g (A + grad ψ x) - g A) = ∫ x, (g (A + grad ψ x) - g A) := by
      refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
      filter_upwards [rd_ae_grad_eq_zero hψ] with x hx hxQ
      rw [hx (hψQ x hxQ), add_zero, sub_self]
    rw [← h1, integral_sub (cv_integrableOn hg A hψ hQfin) (integrableOn_const hQfin),
      setIntegral_const, smul_eq_mul, hQ1, one_mul]
  have hφ'Q : ∀ x ∉ unitCube m, rescaleMap φ (fun _ => 1 / 4) (1 / 2) x = 0 := fun x hx =>
    rescaleMap_eq_zero hφQ _ (1 / 2) fun h => hx (by
      simpa using env_add_mem_unitCube (b := 0) h (by simp))
  rw [hext (rescaleMap_lipschitz hφ _ (by norm_num)) hφ'Q, hext hφ hφQ]
  have e : ∀ x, g (A + grad (rescaleMap φ (fun _ => 1 / 4) (1 / 2)) x) - g A =
      (fun y => g (A + grad φ y) - g A) ((1 / 2 : ℝ)⁻¹ • (x - fun _ => 1 / 4)) := fun x => by
    rw [rescaleMap_grad φ _ (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  exact (integral_congr_ae (ae_of_all _ e)).trans (cv_integral_comp_affine
    (fun y => g (A + grad φ y) - g A) (fun _ => 1 / 4) (by norm_num : (0 : ℝ) < 1 / 2))

/-- In the finite case, `cubeInf f` is quasiconvex ([KP], Proposition 8.1 (iv), by the technique of
Step 6 of the proof of Proposition 7.2: piecewise affine approximation (7.14), and gluing). For a
test map `φ` on `Q`:

* (scaling) `φ' = rescaleMap φ (¼ 𝟙) ½` is supported in `(¼, ¾)^m`, and
  `∫_Q Qf (A + ∇φ') − Qf (A) = 2^{−m} (∫_Q Qf (A + ∇φ) − Qf (A))` (`env_integral_rescale_sub`),
  so it suffices to show `Qf (A) ≤ ∫_Q Qf (A + ∇φ')`;
* (smooth approximation) the mollifications `ψ_n = mollifyPi (n + 7) φ'` are smooth, `K`-Lipschitz,
  vanish off `Q` (the mollifier has radius `2 / (n + 9) < 1/4`), and `∇ψ_n → ∇φ'` almost
  everywhere (`ae_tendsto_grad_mollifyPi`);
* (piecewise affine approximation, diagonal choice of the triangulation) by
  `kuhnInterpolation_grad_uniform`, there is `k_n ≥ 1` with `|∇ I_{k_n} ψ_n − ∇ψ_n| ≤ 1/(n+1)`
  almost everywhere; `v_n = I_{k_n} ψ_n` is a piecewise affine test map on `Q` with
  `|∇v_n| ≤ m K`, and `∇v_n → ∇φ'` almost everywhere, hence in measure;
* (the gluing inequality and the limit) `Qf (A) ≤ ∑ i |P i| Qf (A + ∇ (L i)) = ∫_Q Qf (A + ∇v_n)`
  (`cubeInf_le_sum_of_piecewiseAffine`, `env_integral_piecewiseAffine`), and dominated convergence
  (`Qf` continuous, the gradients bounded) gives `Qf (A) ≤ ∫_Q Qf (A + ∇φ')`. -/
theorem cubeInfReal_quasiconvex {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hfin : ∀ A, cubeInf f A ≠ ⊥) : Quasiconvex (cubeInfReal f) := by
  intro A φ K hφ hφQ _
  have hc := cubeInfReal_continuous hf hfin
  have hX : ∀ X, cubeInf f X = (cubeInfReal f X : EReal) := fun X =>
    cubeInf_eq_cubeInfReal (hfin X)
  rw [cv_volume_unitCube, ENNReal.toReal_one, one_mul]
  -- scaling: it suffices to treat the copy `φ'` supported in `(1/4, 3/4)^m`
  have hs := env_integral_rescale_sub hc A hφ hφQ
  set φ' := rescaleMap φ (fun _ => (1 / 4 : ℝ)) (1 / 2) with hφ'
  have hφ'L : LipschitzWith K φ' := rescaleMap_lipschitz hφ _ (by norm_num)
  have hφ'S : ∀ x ∉ {y : Fin m → ℝ | (1 / 2 : ℝ)⁻¹ • (y - fun _ => (1 / 4 : ℝ)) ∈ unitCube m},
      φ' x = 0 := fun x hx => rescaleMap_eq_zero hφQ _ (1 / 2) hx
  suffices h : cubeInfReal f A ≤ ∫ x in unitCube m, cubeInfReal f (A + grad φ' x) by
    have hpos : (0 : ℝ) < (1 / 2) ^ m := by positivity
    nlinarith
  -- smooth approximation: the mollifications of `φ'`, vanishing off the cube
  set ψ : ℕ → (Fin m → ℝ) → Fin d → ℝ := fun n => mollifyPi (n + 7) φ' with hψdef
  have hψL : ∀ n, LipschitzWith K (ψ n) := fun n => mollifyPi_lipschitzWith hφ'L (n + 7)
  have hψQ : ∀ n, ∀ x ∉ unitCube m, ψ n x = 0 := by
    intro n x hx
    refine mollifyPi_eq_zero hφ'S (n + 7) fun h => hx ?_
    obtain ⟨b, hb, y, hy, rfl⟩ := Set.mem_add.1 h
    refine env_add_mem_unitCube hy ((mem_closedBall_zero_iff.1 hb).trans_lt ?_)
    rw [div_lt_iff₀ (by positivity)]
    push_cast
    linarith
  have hψd : ∀ n, ContDiff ℝ 1 (ψ n) := fun n =>
    (mollifyPi_contDiff hφ'L.continuous (n + 7)).of_le (by exact_mod_cast le_top)
  have hψc : ∀ n, HasCompactSupport (ψ n) := fun n =>
    HasCompactSupport.intro (isCompact_closedBall (fun _ => (1 / 2 : ℝ)) (1 / 2)) fun x hx =>
      hψQ n x fun h => hx (cv_unitCube_subset_closedBall h)
  -- piecewise affine approximation on a Kuhn–Freudenthal triangulation chosen diagonally
  choose k₀ hk₀ using fun n : ℕ =>
    kuhnInterpolation_grad_uniform (hψd n) (hψc n) (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  set k : ℕ → ℕ := fun n => max (k₀ n) 1 with hkdef
  set v : ℕ → (Fin m → ℝ) → Fin d → ℝ := fun n => kuhnInterpolation (k n) (ψ n) with hvdef
  have hvL : ∀ n, LipschitzWith (m * K) (v n) := fun n =>
    kuhnInterpolation_lipschitz (hψL n) (k n)
  have hvQ : ∀ n, ∀ x ∉ unitCube m, v n x = 0 := fun n =>
    kuhnInterpolation_eq_zero (hψQ n) (k n)
  have hv : ∀ᵐ x, Tendsto (fun n => grad (v n) x) atTop (𝓝 (grad φ' x)) := by
    have h1 : ∀ᵐ x, ∀ n : ℕ, ∀ i j, |grad (v n) x i j - grad (ψ n) x i j| ≤ 1 / ((n : ℝ) + 1) :=
      ae_all_iff.2 fun n => hk₀ n (k n) (le_max_left _ _)
    filter_upwards [h1, ae_tendsto_grad_mollifyPi hφ'L] with x hx hx'
    have hx'' : Tendsto (fun n => grad (ψ n) x) atTop (𝓝 (grad φ' x)) :=
      hx'.comp (tendsto_add_atTop_nat 7)
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have e1 : Tendsto (fun n => grad (ψ n) x i j) atTop (𝓝 (grad φ' x i j)) :=
      tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hx'' i) j
    have e2 : Tendsto (fun n => grad (v n) x i j - grad (ψ n) x i j) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hx n i j)
        tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using e2.add e1
  -- the gluing inequality for the `v n`
  have hstep : ∀ n, cubeInfReal f A ≤ ∫ x in unitCube m, cubeInfReal f (A + grad (v n) x) := by
    intro n
    obtain ⟨N, P, L, hPo, hPd, hPQ, hcov, hPL⟩ :=
      kuhnInterpolation_piecewiseAffineOn (ψ n) (lt_of_lt_of_le one_pos (le_max_right _ _) :
        0 < k n)
    have h := cubeInf_le_sum_of_piecewiseAffine hf A P L hPo hPd hPQ hcov ⟨_, hvL n⟩ (hvQ n) hPL
    simp only [hX, ← EReal.coe_mul, ← env_coe_sum, EReal.coe_le_coe_iff] at h
    rw [env_integral_piecewiseAffine _ A P L hPo hPd hPQ hcov hPL]
    exact h
  -- dominated convergence
  obtain ⟨M, -, hM⟩ := cv_bdd hc A ((m * K : NNReal) : ℝ)
  have hlim : Tendsto (fun n => ∫ x in unitCube m, cubeInfReal f (A + grad (v n) x)) atTop
      (𝓝 (∫ x in unitCube m, cubeInfReal f (A + grad φ' x))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun n => ?_)
      (integrableOn_const (by rw [cv_volume_unitCube]; exact ENNReal.one_ne_top)) (fun n => ?_) ?_
    · exact (cv_measurable_comp_grad (cv_continuous_of hc).measurable A (v n)).aestronglyMeasurable
    · exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact hM _ (cv_grad_abs_le (hvL n) x)
    · filter_upwards [ae_restrict_of_ae hv] with x hx
      exact (hc.tendsto _).comp (tendsto_const_nhds.add hx)
  exact ge_of_tendsto' hlim hstep

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
