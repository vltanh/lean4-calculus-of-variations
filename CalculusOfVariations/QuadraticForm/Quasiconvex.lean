/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.QuadraticForm.Plancherel
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# A rank-one convex quadratic form is quasiconvex

`quadraticForm_quasiconvex`: if `Q` is a bilinear form on `ℝ^{d×m}` and `A ↦ Q (A, A)` is rank-one
convex, then `A ↦ Q (A, A)` is quasiconvex. This is Theorem 5.25 (i) of B. Dacorogna, *Direct
Methods in the Calculus of Variations*, 2nd ed., Springer, 2008 ([D08], p. 191–194; there for a
symmetric matrix `M` and `f (ξ) = ⟨M ξ; ξ⟩`), with its proof by Plancherel's formula. [D08] (Remark
5.26) attributes the result to Van Hove; see also C. B. Morrey, *Quasi-convexity and the lower
semicontinuity of multiple integrals*, Pacific J. Math. 2 (1952), 25–53, Theorem 5.2.
-/

@[expose] public section

open MeasureTheory

namespace CalculusOfVariations

variable {d m : ℕ}

private lemma minors_rank_eq_zero_imp {A : Matrix (Fin d) (Fin m) ℝ} (h : A.rank = 0) :
    A = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  ext i j
  have := congrArg (fun F => F (Pi.single j 1) i) h
  simpa [Matrix.mulVecLin_apply] using this

/-- A bilinear form on matrices in coordinates: `Q (X, Y) = ∑ Q (E_{ik}, E_{jl}) X_{ik} Y_{jl}`. -/
private lemma minors_bilin_expand (Q : LinearMap.BilinForm ℝ (Matrix (Fin d) (Fin m) ℝ))
    (X Y : Matrix (Fin d) (Fin m) ℝ) :
    Q X Y = ∑ i, ∑ k, ∑ j, ∑ l,
      Q (Matrix.single i k 1) (Matrix.single j l 1) * (X i k * Y j l) := by
  have hX : X = ∑ i, ∑ k, X i k • Matrix.single i k (1 : ℝ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp
  have hY : Y = ∑ j, ∑ l, Y j l • Matrix.single j l (1 : ℝ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    simp
  have h1 : ∀ Z, Q Z Y = ∑ j, ∑ l, Y j l * Q Z (Matrix.single j l 1) := by
    intro Z
    conv_lhs => rw [hY]
    simp only [map_sum, map_smul, smul_eq_mul]
  have h2 : Q X Y = ∑ i, ∑ k, X i k * Q (Matrix.single i k 1) Y := by
    conv_lhs => rw [hX]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [h2]
  simp only [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- The Legendre–Hadamard condition `Q (a ⊗ ξ, a ⊗ ξ) ≥ 0` of a rank-one convex quadratic form. -/
private lemma minors_legendreHadamard (Q : LinearMap.BilinForm ℝ (Matrix (Fin d) (Fin m) ℝ))
    (hQ : RankOneConvex fun A => Q A A) (a : Fin d → ℝ) (ξ : Fin m → ℝ) :
    0 ≤ Q (Matrix.vecMulVec a ξ) (Matrix.vecMulVec a ξ) := by
  set B := Matrix.vecMulVec a ξ
  by_cases hB : B = 0
  · simp [hB]
  have hrank : B.rank = 1 := by
    refine le_antisymm (Matrix.rank_vecMulVec_le _ _) ?_
    rw [Nat.one_le_iff_ne_zero]
    exact fun h => hB (minors_rank_eq_zero_imp h)
  have hc := (hQ 0 B hrank).2 (Set.mem_univ (-1 : ℝ)) (Set.mem_univ (1 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [zero_add, smul_eq_mul, map_smul, LinearMap.smul_apply] at hc
  norm_num at hc
  linarith

/-- **A rank-one convex quadratic form is quasiconvex** ([D08], Theorem 5.25 (i)).

Proof ([D08], p. 192–194). Since `Q` is quadratic,
`Q (A + ∇φ) = Q (A) + [Q (A, ∇φ) + Q (∇φ, A)] + Q (∇φ)`; the linear term integrates to `0`
(`plancherel_integral_fderiv_eq_zero`), so quasiconvexity is `∫ Q (∇φ) ≥ 0` (Lemma 5.27 (iii)), and
rank-one convexity is the Legendre–Hadamard condition `Q (a ⊗ ξ) ≥ 0` (Lemma 5.27 (iv),
`minors_legendreHadamard`). The test map, extended by `0` outside the cube, is a compactly supported
Lipschitz map on `ℝ^m`, and its gradient vanishes off the closed cube, whose boundary is null. By
Lemma 5.28 the Fourier transform of `∇φ` is `2πi φ̂ ⊗ ξ`, whose real and imaginary parts have rank
at most one, and by Plancherel's formula (5.58) `∫ Q (∇φ)` is the integral of the sum of `Q` at
these parts, so it is nonnegative. Here Plancherel's formula is applied to smooth maps
(`plancherel_smooth_nonneg`), and the inequality passes to Lipschitz maps by mollification
(`plancherel_lipschitz_nonneg`); [D08] applies it to the Lipschitz map itself. -/
theorem quadraticForm_quasiconvex
    (Q : LinearMap.BilinForm ℝ (Matrix (Fin d) (Fin m) ℝ))
    (hQ : RankOneConvex fun A => Q A A) : Quasiconvex fun A => Q A A := by
  intro A φ K hφ hφ0 hint
  set c : Fin d → Fin m → Fin d → Fin m → ℝ :=
    fun i k j l => Q (Matrix.single i k 1) (Matrix.single j l 1) with hcdef
  have hc : ∀ (a : Fin d → ℝ) (ξ : Fin m → ℝ),
      0 ≤ ∑ i, ∑ k, ∑ j, ∑ l, c i k j l * (a i * ξ k) * (a j * ξ l) := by
    intro a ξ
    have h := minors_legendreHadamard Q hQ a ξ
    rw [minors_bilin_expand] at h
    simpa [Matrix.vecMulVec_apply, mul_assoc, hcdef] using h
  -- the components of `φ` and the closed cube
  set φc : Fin d → (Fin m → ℝ) → ℝ := fun i y => φ y i with hφcdef
  set S : Set (Fin m → ℝ) := Set.Icc 0 1 with hS
  have hScpt : IsCompact S := isCompact_Icc
  have hcubeS : unitCube m ⊆ S := fun x hx => ⟨fun k => (hx k (Set.mem_univ _)).1.le,
    fun k => (hx k (Set.mem_univ _)).2.le⟩
  have hφi : ∀ i, LipschitzWith K (φc i) := fun i => by
    have := (LipschitzWith.eval (α := fun _ : Fin d => ℝ) i).comp hφ
    rw [one_mul] at this
    exact this
  have hφS : ∀ i, ∀ x ∉ S, φc i x = 0 := fun i x hx => by
    simp [hφcdef, hφ0 x (fun h => hx (hcubeS h))]
  have hφc : ∀ i, HasCompactSupport (φc i) := fun i =>
    HasCompactSupport.intro hScpt (hφS i)
  have hG : ∀ x i k, grad φ x i k = fderiv ℝ (φc i) x (Pi.single k 1) := fun _ _ _ => rfl
  have hG0 : ∀ i k, ∀ x ∉ S, grad φ x i k = 0 := by
    intro i k x hx
    rw [hG, fderiv_of_notMem_tsupport]
    · rfl
    · exact fun h => hx ((closure_minimal (fun y hy => by
        by_contra h'; exact hy (hφS i y h')) hScpt.isClosed) h)
  have hGb : ∀ x i k, |grad φ x i k| ≤ K := by
    intro x i k
    rw [hG]
    calc |fderiv ℝ (φc i) x (Pi.single k 1)|
        ≤ ‖fderiv ℝ (φc i) x‖ * ‖(Pi.single k 1 : Fin m → ℝ)‖ :=
          (fderiv ℝ (φc i) x).le_opNorm _
      _ ≤ K * 1 := by
          gcongr
          · exact norm_fderiv_le_of_lipschitz ℝ (hφi i)
          · simp [Pi.norm_single]
      _ = K := mul_one _
  have hGm : ∀ i k, Measurable fun x => grad φ x i k := fun i k =>
    measurable_fderiv_apply_const ℝ (φc i) (Pi.single k 1)
  -- integrability on `ℝ^m`
  have hbint : ∀ C : ℝ, Integrable (S.indicator fun _ => C) :=
    fun C => (integrable_indicator_iff hScpt.measurableSet).2
      (integrableOn_const hScpt.measure_lt_top.ne)
  have hi1 : ∀ i k, Integrable fun x => grad φ x i k := by
    intro i k
    refine (hbint K).mono' (hGm i k).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs]; exact hGb x i k
    · rw [Set.indicator_of_notMem hx, hG0 i k x hx, norm_zero]
  have hi2 : ∀ i k j l, Integrable fun x => grad φ x i k * grad φ x j l := by
    intro i k j l
    refine (hbint (K * K)).mono' ((hGm i k).mul (hGm j l)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hGb x i k) (hGb x j l) (abs_nonneg _) K.2
    · rw [Set.indicator_of_notMem hx, hG0 i k x hx, zero_mul, norm_zero]
  -- the decomposition
  set L : Fin d → Fin m → ℝ := fun i k => Q A (Matrix.single i k 1) + Q (Matrix.single i k 1) A
  set h : (Fin m → ℝ) → ℝ := fun x => (∑ i, ∑ k, L i k * grad φ x i k) +
    ∑ i, ∑ k, ∑ j, ∑ l, c i k j l * (grad φ x i k * grad φ x j l) with hh
  have hpt : ∀ x, Q (A + grad φ x) (A + grad φ x) = Q A A + h x := by
    intro x
    have e1 : Q A (grad φ x) + Q (grad φ x) A = ∑ i, ∑ k, L i k * grad φ x i k := by
      have hX : grad φ x = ∑ i, ∑ k, grad φ x i k • Matrix.single i k (1 : ℝ) := by
        conv_lhs => rw [Matrix.matrix_eq_sum_single (grad φ x)]
        simp
      conv_lhs => rw [hX]
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have e2 := minors_bilin_expand Q (grad φ x) (grad φ x)
    simp only [map_add, LinearMap.add_apply, hh]
    rw [← e1, e2]
    ring
  have hhint : Integrable h := by
    refine (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
      (hi1 i k).const_mul (L i k)).add
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
        integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
          (hi2 i k j l).const_mul (c i k j l))
  have hh0 : ∀ x ∉ S, h x = 0 := by
    intro x hx
    simp [hh, hG0 _ _ x hx]
  have hvol : volume (unitCube m) ≠ ⊤ := (measure_mono hcubeS).trans_lt hScpt.measure_lt_top |>.ne
  -- the integral over the cube
  have hcube : ∫ x in unitCube m, Q (A + grad φ x) (A + grad φ x) =
      (volume (unitCube m)).toReal * Q A A + ∫ x, h x := by
    simp only [hpt]
    rw [integral_add (integrableOn_const hvol) hhint.integrableOn, setIntegral_const,
      smul_eq_mul, Measure.real]
    congr 1
    have hae : unitCube m =ᵐ[volume] S := by
      rw [hS, ← Set.pi_univ_Icc]
      exact Measure.pi_Ioo_ae_eq_pi_Icc
    rw [setIntegral_congr_set hae, setIntegral_eq_integral_of_forall_compl_eq_zero hh0]
  have hlin : ∫ x, h x = (∑ i, ∑ k, L i k * ∫ x, grad φ x i k) +
      ∑ i, ∑ k, ∑ j, ∑ l, c i k j l * ∫ x, grad φ x i k * grad φ x j l := by
    rw [hh, integral_add (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
      (hi1 i k).const_mul (L i k))
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
        integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
          (hi2 i k j l).const_mul (c i k j l))]
    congr 1
    · rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
        (hi1 i k).const_mul (L i k)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun k _ => (hi1 i k).const_mul (L i k)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul]
    · rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
        integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
          (hi2 i k j l).const_mul (c i k j l)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ =>
        integrable_finsetSum _ fun l _ => (hi2 i k j l).const_mul (c i k j l)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
        (hi2 i k j l).const_mul (c i k j l)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_finsetSum _ fun l _ => (hi2 i k j l).const_mul (c i k j l)]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [integral_const_mul]
  have hzero : ∀ i k, ∫ x, grad φ x i k = 0 := fun i k => by
    simp only [hG]
    exact plancherel_integral_fderiv_eq_zero (hφi i) (hφc i) _
  have hpos : 0 ≤ ∑ i, ∑ k, ∑ j, ∑ l, c i k j l * ∫ x, grad φ x i k * grad φ x j l := by
    simp only [hG]
    exact plancherel_lipschitz_nonneg φc (fun _ => K) hφi hφc c hc
  simp only at hcube ⊢
  rw [hcube, hlin]
  simp only [hzero, mul_zero, Finset.sum_const_zero, zero_add]
  linarith

end CalculusOfVariations
