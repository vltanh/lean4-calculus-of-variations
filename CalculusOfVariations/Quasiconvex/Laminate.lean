/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Lipschitz.Periodic
public import CalculusOfVariations.Quasiconvex.Cutoff
public import CalculusOfVariations.Quasiconvex.Domain
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Laminates, and the two-point inequality along rank-one segments

A lower semicontinuous, locally bounded `f` that is quasiconvex at `F` satisfies
`f (F) ≤ λ f (F + (1 − λ) a ⊗ n) + (1 − λ) f (F − λ a ⊗ n)` for all `a`, `n` and `λ ∈ (0, 1)`
(`le_of_quasiconvexAtOn_vecMulVec`). This is the proof of Proposition 5.6 of F. Rindler, *Calculus
of Variations*, 2nd ed., Graduate Texts in Mathematics 310, Springer, 2026 ([R2]), p. 111–113, where
`A = F + (1 − λ) a ⊗ n` and `B = F − λ a ⊗ n` (so `F = λ A + (1 − λ) B`; `a` here is `−a` there):

* (Step 1, p. 111) The laminate `u_k (x) = F x + k⁻¹ h (k x · n) a` with the sawtooth `h = rd_saw λ`
  (`1`-periodic, `0` at the integers, slope `1 − λ` on `(k, k + λ)` and `−λ` on `(k + λ, k + 1)`)
  has the gradients `A` and `B`, almost everywhere, on a cube `Q_n` with two faces orthogonal to
  `n`, and `⨍_{Q_n} f (∇u_k) → λ f (A) + (1 − λ) f (B)`. Here first for `n = e_j` and the unit cube
  `Q = (0, 1)^m`: `sawLaminate` is `x ↦ k⁻¹ h (k x_j) a`, its gradient is `(1 − λ) a ⊗ e_j` or
  `−λ a ⊗ e_j` (`lam_ae_hasFDerivAt_sawPart`), and
  `∫_Q f (F + ∇ (sawLaminate)) = λ f (A) + (1 − λ) f (B)` for every `k ≥ 1`
  (`setIntegral_sawLaminate`).
* (Step 2, p. 112) The `u_k` are cut off near `∂Q_n`, with a diagonal choice of the cut-offs and of
  `k` (`le_of_quasiconvexAtOn_of_tendsto`, `Quasiconvex.Cutoff`), so quasiconvexity on `Q_n` gives
  `f (F) ≤ λ f (A) + (1 − λ) f (B)` (`le_of_quasiconvexAtOn_unitCube_of_lsc`).
* The cube `Q_n` is `R Q` for an orthogonal matrix `R` with `R e_j = n`
  (`exists_orthogonal_mulVec_single_eq`, a Householder reflection): quasiconvexity at `F` on `R Q`
  is quasiconvexity of `X ↦ f (X Rᵀ)` at `F R` on `Q`, by the orthogonal change of variables
  `x = R y` (`quasiconvexAtOn_unitCube_comp_orthogonal`), and `a ⊗ n = (a ⊗ e_j) Rᵀ`. Quasiconvexity
  on `Q_n` is quasiconvexity on `Q` by the independence of the domain (`quasiconvexAtOn_iff`; [R2],
  Lemma 5.2).
-/
@[expose] public section

open Metric Set MeasureTheory Filter Topology
open scoped Pointwise Matrix

namespace CalculusOfVariations

variable {d m : ℕ}

/-! ### The sawtooth -/

/-- The profile of the sawtooth, vanishing off `(0, 1)`. -/
noncomputable def rd_tooth (l : ℝ) (s : Fin 1 → ℝ) : Fin 1 → ℝ :=
  fun _ => max 0 (min ((1 - l) * s 0) (l * (1 - s 0)))

private lemma rd_tooth_lipschitz {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    LipschitzWith 1 (rd_tooth l) := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
  intro _
  simp only [rd_tooth, Real.dist_eq]
  have h0 : |s 0 - t 0| ≤ dist s t := by rw [← Real.dist_eq]; exact dist_le_pi_dist s t 0
  refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
  simp only [sub_self, abs_zero]
  refine max_le dist_nonneg ((abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_))
  · rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith)]
    nlinarith [abs_nonneg (s 0 - t 0)]
  · rw [show l * (1 - s 0) - l * (1 - t 0) = l * (t 0 - s 0) by ring, abs_mul,
      abs_of_nonneg hl0, abs_sub_comm]
    nlinarith [abs_nonneg (s 0 - t 0)]

private lemma rd_tooth_zero {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    ∀ s ∉ unitCube 1, rd_tooth l s = 0 := by
  intro s hs
  have hs' : s 0 ≤ 0 ∨ 1 ≤ s 0 := by
    by_contra h
    push Not at h
    exact hs fun i _ => by rw [Subsingleton.elim i 0]; exact ⟨h.1, h.2⟩
  funext _
  simp only [rd_tooth, Pi.zero_apply]
  apply max_eq_left
  rcases hs' with h | h
  · exact (min_le_left _ _).trans (mul_nonpos_of_nonneg_of_nonpos (by linarith) h)
  · exact (min_le_right _ _).trans (mul_nonpos_of_nonneg_of_nonpos hl0 (by linarith))

/-- The sawtooth `h_λ (t) = max 0 (min ((1 − λ) fract t) (λ (1 − fract t)))`: slope `1 − λ` on
`(k, k + λ)`, slope `−λ` on `(k + λ, k + 1)`, `1`-periodic and `1`-Lipschitz. -/
noncomputable def rd_saw (l t : ℝ) : ℝ := rd_perExt (rd_tooth l) (fun _ => t) 0

private lemma rd_saw_eq (l t : ℝ) :
    rd_saw l t = max 0 (min ((1 - l) * Int.fract t) (l * (1 - Int.fract t))) := rfl

lemma rd_saw_lipschitz {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    LipschitzWith 1 (rd_saw l) := by
  have h := rd_perExt_lipschitz (rd_tooth_lipschitz hl0 hl1) (rd_tooth_zero hl0 hl1)
  have hc : LipschitzWith 1 (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    LipschitzWith.of_dist_le_mul fun s t => by
      rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]; intro _; exact le_rfl
  have := (LipschitzWith.eval (α := fun _ : Fin 1 => ℝ) 0).comp (h.comp hc)
  exact this.weaken (by simp)

lemma rd_saw_add_int (l t : ℝ) (k : ℤ) : rd_saw l (t + k) = rd_saw l t := by
  simp only [rd_saw_eq, Int.fract_add_intCast]

lemma rd_saw_hasDerivAt_up {l t : ℝ} (hl1 : l < 1) (h0 : 0 < Int.fract t)
    (h1 : Int.fract t < l) : HasDerivAt (rd_saw l) (1 - l) t := by
  set k : ℤ := ⌊t⌋
  have hkt : t = Int.fract t + k := by rw [← Int.self_sub_floor]; ring
  have hev : rd_saw l =ᶠ[𝓝 t] fun s => (1 - l) * (s - k) := by
    filter_upwards [Ioo_mem_nhds (show (k : ℝ) < t by linarith)
      (show t < k + l by linarith)] with s hs
    have hfs : Int.fract s = s - k := by
      rw [← Int.self_sub_floor, Int.floor_eq_iff.2 ⟨hs.1.le, by linarith [hs.2]⟩]
    rw [rd_saw_eq, hfs]
    have a : 0 ≤ (1 - l) * (s - k) := mul_nonneg (by linarith) (by linarith [hs.1])
    have b : (1 - l) * (s - k) ≤ l * (1 - (s - k)) := by nlinarith [hs.2]
    rw [min_eq_left b, max_eq_right a]
  have hd : HasDerivAt (fun s => (1 - l) * (s - k)) (1 - l) t := by
    simpa using HasDerivAt.const_mul (1 - l) (HasDerivAt.sub_const (k : ℝ) (hasDerivAt_id t))
  exact hd.congr_of_eventuallyEq hev

lemma rd_saw_hasDerivAt_down {l t : ℝ} (hl0 : 0 < l) (h0 : l < Int.fract t) :
    HasDerivAt (rd_saw l) (-l) t := by
  set k : ℤ := ⌊t⌋
  have hkt : t = Int.fract t + k := by rw [← Int.self_sub_floor]; ring
  have h1 := Int.fract_lt_one t
  have hev : rd_saw l =ᶠ[𝓝 t] fun s => l * (1 - (s - k)) := by
    filter_upwards [Ioo_mem_nhds (show (k : ℝ) + l < t by linarith)
      (show t < k + 1 by linarith)] with s hs
    have hfs : Int.fract s = s - k := by
      rw [← Int.self_sub_floor, Int.floor_eq_iff.2 ⟨by linarith [hs.1], hs.2⟩]
    rw [rd_saw_eq, hfs]
    have a : 0 ≤ l * (1 - (s - k)) := mul_nonneg hl0.le (by linarith [hs.2])
    have b : l * (1 - (s - k)) ≤ (1 - l) * (s - k) := by nlinarith [hs.1]
    rw [min_eq_right b, max_eq_right a]
  have hd : HasDerivAt (fun s => l * (1 - (s - k))) (-l) t := by
    simpa using HasDerivAt.const_mul l
      (HasDerivAt.const_sub 1 (HasDerivAt.sub_const (k : ℝ) (hasDerivAt_id t)))
  exact hd.congr_of_eventuallyEq hev

lemma lam_saw_nonneg (l t : ℝ) : 0 ≤ rd_saw l t := le_max_left _ _

lemma lam_saw_le_one {l : ℝ} (hl0 : 0 ≤ l) (t : ℝ) : rd_saw l t ≤ 1 := by
  rw [rd_saw_eq]
  refine max_le zero_le_one ((min_le_left _ _).trans ?_)
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  nlinarith

/-! ### The laminate -/

/-- The laminate `u_k (x) = k⁻¹ h_λ (k x_j) a`, `h_λ = rd_saw λ`: its gradient is
`(1 − λ) a ⊗ e_j` where `fract (k x_j) ∈ (0, λ)` and `−λ a ⊗ e_j` where `fract (k x_j) ∈ (λ, 1)`. -/
noncomputable def sawLaminate (a : Fin d → ℝ) (j : Fin m) (l : ℝ) (k : ℕ) (x : Fin m → ℝ) :
    Fin d → ℝ :=
  ((k : ℝ)⁻¹ * rd_saw l (k * x j)) • a

/-- The sawtooth part `x ↦ k⁻¹ h_λ (k x_j)` is `1`-Lipschitz (for `k = 0` it is `0`). -/
lemma lam_sawPart_lipschitz (j : Fin m) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (k : ℕ) :
    LipschitzWith 1 (fun x : Fin m → ℝ => (k : ℝ)⁻¹ * rd_saw l (k * x j)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, Real.dist_eq, ← mul_sub, abs_mul,
    abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg k))]
  have h := (rd_saw_lipschitz hl0 hl1).dist_le_mul (k * x j) (k * y j)
  rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul,
    Nat.abs_cast] at h
  have hxy : |x j - y j| ≤ dist x y := by rw [← Real.dist_eq]; exact dist_le_pi_dist x y j
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
    calc (k : ℝ)⁻¹ * |rd_saw l (k * x j) - rd_saw l (k * y j)|
        ≤ (k : ℝ)⁻¹ * (k * |x j - y j|) := by gcongr
      _ = |x j - y j| := by field_simp
      _ ≤ dist x y := hxy

/-- `u_k` is `‖a‖`-Lipschitz (sup norms). -/
lemma sawLaminate_lipschitz (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (k : ℕ) : LipschitzWith ‖a‖₊ (sawLaminate a j l k) := by
  have hs : LipschitzWith ‖a‖₊ (fun t : ℝ => t • a) := LipschitzWith.of_dist_le_mul fun s t => by
    rw [dist_eq_norm, dist_eq_norm, ← sub_smul, norm_smul, mul_comm]; rfl
  have := hs.comp (lam_sawPart_lipschitz j hl0 hl1 k)
  rw [mul_one] at this
  exact this

/-- `|u_k| ≤ k⁻¹ |a|`. -/
lemma sawLaminate_norm_le (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (hl0 : 0 ≤ l) (k : ℕ)
    (x : Fin m → ℝ) : ‖sawLaminate a j l k x‖ ≤ (k : ℝ)⁻¹ * ‖a‖ := by
  rw [sawLaminate, norm_smul, Real.norm_of_nonneg (mul_nonneg (by positivity)
    (lam_saw_nonneg l _))]
  have := lam_saw_le_one hl0 (k * x j)
  gcongr
  exact mul_le_of_le_one_right (by positivity) this

/-- A coordinate preimage of a null set is null. -/
lemma lam_volume_eval_preimage_null (j : Fin m) {N : Set ℝ} (hN : volume N = 0) :
    volume {x : Fin m → ℝ | x j ∈ N} = 0 := by
  have : {x : Fin m → ℝ | x j ∈ N} = univ.pi (Function.update (fun _ => univ) j N) := by
    ext x
    simp only [mem_ofPred_eq, Set.mem_pi, mem_univ, true_implies]
    constructor
    · intro h i
      rcases eq_or_ne i j with rfl | hij
      · simpa using h
      · simp [Function.update_of_ne hij]
    · intro h
      simpa using h j
  rw [this, volume_pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simpa using hN)

/-- Almost everywhere, `fract (k x_j) ≠ c`: the exceptional set is a countable union of
hyperplanes `{x_j = (z + c) / k}`. -/
lemma lam_ae_fract_ne (j : Fin m) {k : ℕ} (hk : 0 < k) (c : ℝ) :
    ∀ᵐ x : Fin m → ℝ, Int.fract (k * x j) ≠ c := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hc : {t : ℝ | Int.fract (k * t) = c}.Countable := by
    refine (Set.countable_range fun z : ℤ => ((z : ℝ) + c) / k).mono fun t ht => ?_
    refine ⟨⌊(k : ℝ) * t⌋, ?_⟩
    have ht' : Int.fract ((k : ℝ) * t) = c := ht
    have : (k : ℝ) * t = ⌊(k : ℝ) * t⌋ + c := by
      have := Int.floor_add_fract ((k : ℝ) * t)
      linarith
    field_simp
    linarith
  have := lam_volume_eval_preimage_null j (hc.measure_zero volume)
  rw [ae_iff]
  simpa using this

/-- The gradient of `y ↦ ψ (y) a` is `a ⊗ ∇ψ`. -/
lemma lam_grad_smul (ψ : (Fin m → ℝ) → ℝ) (a : Fin d → ℝ) (x : Fin m → ℝ) :
    grad (fun y => ψ y • a) x = Matrix.vecMulVec a (fun i => fderiv ℝ ψ x (Pi.single i 1)) := by
  ext i k
  simp only [grad, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
  have : (fun y => ψ y * a i) = a i • ψ := by funext y; simp [mul_comm]
  rw [this, fderiv_const_smul_field]
  simp

lemma lam_proj_single (i : Fin m) :
    (fun i' => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i)
      (Pi.single i' 1)) = Pi.single i 1 := by
  funext i'
  simp [Pi.single_apply, eq_comm]

lemma lam_smul_proj_single (c : ℝ) (i : Fin m) :
    (fun i' => (c • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i)
      (Pi.single i' 1)) = c • Pi.single i 1 := by
  funext i'
  simp [Pi.single_apply, eq_comm]

/-- The gradient of `y ↦ ψ (y) a` where `ψ` has derivative `c e_j`. -/
lemma lam_grad_smul_of_hasFDerivAt {ψ : (Fin m → ℝ) → ℝ} (a : Fin d → ℝ) {j : Fin m}
    {c : ℝ} {x : Fin m → ℝ}
    (h : HasFDerivAt ψ (c • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j) x) :
    grad (fun y => ψ y • a) x = c • Matrix.vecMulVec a (Pi.single j 1) := by
  rw [lam_grad_smul, h.fderiv, lam_smul_proj_single, Matrix.vecMulVec_smul]

/-- The derivative of the sawtooth part `y ↦ k⁻¹ h_λ (k y_j)`, where `h_λ` has derivative `c`. -/
lemma lam_hasFDerivAt_sawPart (j : Fin m) {k : ℕ} (hk : 0 < k) {l c : ℝ}
    {x : Fin m → ℝ} (h : HasDerivAt (rd_saw l) c (k * x j)) :
    HasFDerivAt (fun y : Fin m → ℝ => (k : ℝ)⁻¹ * rd_saw l (k * y j))
      (c • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j) x := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hin : HasFDerivAt (fun y : Fin m → ℝ => (k : ℝ) * y j)
      ((k : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j) x :=
    (hasFDerivAt_apply j x).const_mul (k : ℝ)
  have := (h.comp_hasFDerivAt x hin).const_mul (k : ℝ)⁻¹
  refine this.congr_fderiv ?_
  rw [smul_smul, smul_smul, mul_comm _ c, mul_assoc, inv_mul_cancel₀ hk', mul_one]

/-- Almost everywhere (off `{fract (k x_j) ∈ {0, λ}}`), the sawtooth part has derivative
`(1 − λ) e_j` where `fract (k x_j) < λ` and `−λ e_j` elsewhere. -/
lemma lam_ae_hasFDerivAt_sawPart (j : Fin m) {k : ℕ} (hk : 0 < k) {l : ℝ} (hl0 : 0 < l)
    (hl1 : l < 1) :
    ∀ᵐ x : Fin m → ℝ, HasFDerivAt (fun y : Fin m → ℝ => (k : ℝ)⁻¹ * rd_saw l (k * y j))
      ((if Int.fract ((k : ℝ) * x j) < l then 1 - l else -l) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j) x := by
  filter_upwards [lam_ae_fract_ne j hk 0, lam_ae_fract_ne j hk l] with x h0 hl
  split_ifs with h
  · exact lam_hasFDerivAt_sawPart j hk
      (rd_saw_hasDerivAt_up hl1 (lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm h0)) h)
  · exact lam_hasFDerivAt_sawPart j hk
      (rd_saw_hasDerivAt_down hl0 (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hl)))

/-- `∫_Q G (k x) dx = λ c₁ + (1 − λ) c₂` for `k ≥ 1` and `G (y) = c₁` where `fract (y_j) < λ`,
`G (y) = c₂` elsewhere: `G` is a bounded measurable `ℤ^m`-periodic function, so
`∫_Q G (k x) dx = ∫_Q G` (`rd_setIntegral_comp_nsmul`), and `|{y ∈ Q : y_j < λ}| = λ`. -/
lemma lam_setIntegral_fract (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {k : ℕ} (hk : 0 < k)
    (c₁ c₂ : ℝ) : ∫ x in unitCube m, (if Int.fract ((k : ℝ) * x j) < l then c₁ else c₂) =
      l * c₁ + (1 - l) * c₂ := by
  set G : (Fin m → ℝ) → ℝ := fun y => if Int.fract (y j) < l then c₁ else c₂
  have hGm : Measurable G :=
    Measurable.ite (measurableSet_lt (measurable_fract.comp (measurable_pi_apply j))
      measurable_const) measurable_const measurable_const
  have hGb : ∀ y, |G y| ≤ |c₁| + |c₂| := fun y => by
    simp only [G]
    split_ifs <;> linarith [abs_nonneg c₁, abs_nonneg c₂]
  have hGper : ∀ (y : Fin m → ℝ) (z : Fin m → ℤ), G (y + fun i => (z i : ℝ)) = G y := by
    intro y z
    simp only [G, Pi.add_apply, Int.fract_add_intCast]
  have hGk : ∀ x : Fin m → ℝ, (if Int.fract ((k : ℝ) * x j) < l then c₁ else c₂) =
      G ((k : ℝ) • x) := fun _ => rfl
  simp only [hGk]
  rw [rd_setIntegral_comp_nsmul hGm hGb hGper hk]
  -- the integral of `G` over the cube
  set S : Set (Fin m → ℝ) := {y | y j < l}
  have hS : MeasurableSet S := measurableSet_lt (measurable_pi_apply j) measurable_const
  have hQm : MeasurableSet (unitCube m) := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hGS : ∀ y ∈ unitCube m, G y = S.piecewise (fun _ => c₁) (fun _ => c₂) y := by
    intro y hy
    have hy' := hy j (mem_univ j)
    simp only [G, S, Set.piecewise, mem_ofPred_eq, Int.fract_eq_self.2 ⟨hy'.1.le, hy'.2⟩]
  have hfin : IsFiniteMeasure (volume.restrict (unitCube m)) :=
    isFiniteMeasure_restrict.2 (by rw [rd_volume_unitCube]; exact ENNReal.one_ne_top)
  rw [setIntegral_congr_fun hQm hGS, integral_piecewise hS (integrableOn_const (measure_ne_top _ _))
    (integrableOn_const (measure_ne_top _ _)), setIntegral_const, setIntegral_const]
  have hSQ : S ∩ unitCube m =
      univ.pi fun i => Ioo (0 : ℝ) (Function.update (fun _ => (1 : ℝ)) j l i) := by
    ext y
    simp only [S, mem_inter_iff, mem_ofPred_eq, unitCube, Set.mem_pi, mem_univ, true_implies,
      mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩ i
      rcases eq_or_ne i j with rfl | hij
      · simpa using ⟨(h2 i).1, h1⟩
      · simpa [Function.update_of_ne hij] using h2 i
    · intro h
      refine ⟨by simpa using (h j).2, fun i => ?_⟩
      rcases eq_or_ne i j with rfl | hij
      · exact ⟨(h i).1, by have := (h i).2; simp at this; linarith⟩
      · simpa [Function.update_of_ne hij] using h i
  have hvS : (volume.restrict (unitCube m)).real S = l := by
    rw [measureReal_restrict_apply hS, hSQ, measureReal_def, Real.volume_pi_Ioo,
      Finset.prod_eq_single j (fun i _ hij => by simp [Function.update_of_ne hij])
        (fun h => (h (Finset.mem_univ j)).elim)]
    simp [hl0.le]
  have hvQ : (volume.restrict (unitCube m)).real univ = 1 := by
    rw [measureReal_restrict_apply MeasurableSet.univ, univ_inter, measureReal_def,
      rd_volume_unitCube, ENNReal.toReal_one]
  rw [measureReal_compl hS, hvS, hvQ, smul_eq_mul, smul_eq_mul]

/-- The energy of `u_k`: for every `f` and `k ≥ 1`,
`∫_Q f (F + ∇u_k) = λ f (F + (1 − λ) a ⊗ e_j) + (1 − λ) f (F − λ a ⊗ e_j)`. Almost everywhere
`∇u_k (x)` is `(1 − λ) a ⊗ e_j` where `fract (k x_j) < λ` and `−λ a ⊗ e_j` elsewhere
(`lam_setIntegral_fract`). -/
theorem setIntegral_sawLaminate (f : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (F : Matrix (Fin d) (Fin m) ℝ) (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1)
    {k : ℕ} (hk : 0 < k) :
    ∫ x in unitCube m, f (F + grad (sawLaminate a j l k) x) =
      l * f (F + (1 - l) • Matrix.vecMulVec a (Pi.single j 1)) +
        (1 - l) * f (F - l • Matrix.vecMulVec a (Pi.single j 1)) := by
  rw [← lam_setIntegral_fract j hl0 hl1 hk]
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [lam_ae_hasFDerivAt_sawPart j hk hl0 hl1] with x hx
  have e : grad (sawLaminate a j l k) x = _ := lam_grad_smul_of_hasFDerivAt a hx
  rw [e]
  split_ifs
  · rfl
  · rw [sub_eq_add_neg, neg_smul]

/-! ### The two-point inequality on the unit cube -/

/-- **The two-point inequality on the unit cube** ([R2], proof of Proposition 5.6): if `f` is lower
semicontinuous, locally bounded and quasiconvex at `F` on the unit cube, then
`f (F) ≤ λ f (F + (1 − λ) a ⊗ e_j) + (1 − λ) f (F − λ a ⊗ e_j)`. The laminates `u_k`
(`sawLaminate`) are Lipschitz with the same constant, converge to `0` uniformly, and
`∫_Q f (F + ∇u_k)` is the right-hand side (Step 1), so the cut-off argument
`le_of_quasiconvexAtOn_of_tendsto` applies (Step 2). -/
theorem le_of_quasiconvexAtOn_unitCube_of_lsc {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) {F : Matrix (Fin d) (Fin m) ℝ}
    (hf : QuasiconvexAtOn (unitCube m) f F) (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (hl0 : 0 < l)
    (hl1 : l < 1) :
    f F ≤ l * f (F + (1 - l) • Matrix.vecMulVec a (Pi.single j 1)) +
      (1 - l) * f (F - l • Matrix.vecMulVec a (Pi.single j 1)) := by
  refine le_of_quasiconvexAtOn_of_tendsto hlsc hbdd hf
    (fun k => sawLaminate_lipschitz a j hl0.le hl1.le k) ?_ ?_
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hlim : Tendsto (fun k : ℕ => (k : ℝ)⁻¹ * ‖a‖) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ).mul_const ‖a‖
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with k hk x
    rw [Pi.zero_apply, dist_zero_left]
    exact (sawLaminate_norm_le a j hl0.le k x).trans_lt hk
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact (setIntegral_sawLaminate f F a j hl0 hl1 hk).symm

/-! ### The cube with faces orthogonal to a given direction -/

/-- For `Rᵀ R = 1`, the image of a set under `x ↦ R x` is its preimage under `y ↦ Rᵀ y`. -/
lemma lam_image_mulVec_eq_preimage {R : Matrix (Fin m) (Fin m) ℝ} (hR : Rᵀ * R = 1)
    (s : Set (Fin m → ℝ)) :
    (fun x => R.mulVec x) '' s = (fun y => Rᵀ.mulVec y) ⁻¹' s := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.1 hR
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [Matrix.mulVec_mulVec, hR] using hx
  · intro hy
    exact ⟨Rᵀ.mulVec y, hy, by simp [Matrix.mulVec_mulVec, hR']⟩

/-- An orthogonal `R` preserves the volume: `|det R| = 1`. -/
lemma lam_measurePreserving_mulVec {R : Matrix (Fin m) (Fin m) ℝ} (hR : Rᵀ * R = 1) :
    MeasurePreserving (fun x => R.mulVec x) volume volume := by
  have hdet : R.det * R.det = 1 := by
    calc R.det * R.det = Rᵀ.det * R.det := by rw [Matrix.det_transpose]
      _ = 1 := by rw [← Matrix.det_mul, hR, Matrix.det_one]
  have habs : |R.det| = 1 := by
    have h := congrArg abs hdet
    rw [abs_mul, abs_one] at h
    exact (mul_self_eq_one_iff.1 h).resolve_right (by linarith [abs_nonneg R.det])
  have hne : LinearMap.det (Matrix.toLin' R) ≠ 0 := by
    rw [LinearMap.det_toLin']
    intro h
    rw [h, mul_zero] at hdet
    exact zero_ne_one hdet
  have hcont : Continuous (fun x : Fin m → ℝ => R.mulVec x) :=
    continuous_const.matrix_mulVec continuous_id
  refine ⟨hcont.measurable, ?_⟩
  have e : (fun x : Fin m → ℝ => R.mulVec x) = Matrix.toLin' R := by
    funext x; rw [Matrix.toLin'_apply]
  rw [e, Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne, LinearMap.det_toLin', abs_inv,
    habs, inv_one, ENNReal.ofReal_one, one_smul]

/-- `x ↦ R x` is a measurable embedding for an orthogonal `R`. -/
lemma lam_measurableEmbedding_mulVec {R : Matrix (Fin m) (Fin m) ℝ} (hR : Rᵀ * R = 1) :
    MeasurableEmbedding (fun x : Fin m → ℝ => R.mulVec x) := by
  have hcont : Continuous (fun x : Fin m → ℝ => R.mulVec x) :=
    continuous_const.matrix_mulVec continuous_id
  refine hcont.measurableEmbedding fun x y hxy => ?_
  have := congrArg (fun z => Rᵀ.mulVec z) hxy
  simpa [Matrix.mulVec_mulVec, hR] using this

/-- The change of variables `y = R x` for an orthogonal `R`. -/
lemma lam_setIntegral_image_mulVec {R : Matrix (Fin m) (Fin m) ℝ} (hR : Rᵀ * R = 1)
    (g : (Fin m → ℝ) → ℝ) (s : Set (Fin m → ℝ)) :
    ∫ y in (fun x => R.mulVec x) '' s, g y = ∫ x in s, g (R.mulVec x) :=
  (lam_measurePreserving_mulVec hR).setIntegral_image_emb (lam_measurableEmbedding_mulVec hR) g s

/-- The image of the unit cube under an orthogonal matrix has volume `1`. -/
lemma lam_volume_image_mulVec {R : Matrix (Fin m) (Fin m) ℝ} (hR : Rᵀ * R = 1) :
    volume ((fun x => R.mulVec x) '' unitCube m) = 1 := by
  have hme := lam_measurableEmbedding_mulVec hR
  have := hme.map_apply volume ((fun x => R.mulVec x) '' unitCube m)
  rw [(lam_measurePreserving_mulVec hR).map_eq, hme.injective.preimage_image,
    rd_volume_unitCube] at this
  exact this

/-- The image of the unit cube under an orthogonal matrix is open. -/
lemma lam_isOpen_image_mulVec {R : Matrix (Fin m) (Fin m) ℝ} (hR : Rᵀ * R = 1) :
    IsOpen ((fun x => R.mulVec x) '' unitCube m) := by
  rw [lam_image_mulVec_eq_preimage hR]
  exact (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo).preimage
    (continuous_const.matrix_mulVec continuous_id)

/-- The image of the unit cube under a linear map is bounded. -/
lemma lam_isBounded_image_mulVec (R : Matrix (Fin m) (Fin m) ℝ) :
    Bornology.IsBounded ((fun x => R.mulVec x) '' unitCube m) := by
  have hsub : unitCube m ⊆ Icc (0 : Fin m → ℝ) 1 := fun x hx =>
    ⟨fun i => (hx i (mem_univ i)).1.le, fun i => (hx i (mem_univ i)).2.le⟩
  have hcont : Continuous (fun x : Fin m → ℝ => R.mulVec x) :=
    continuous_const.matrix_mulVec continuous_id
  exact (isCompact_Icc.image hcont).isBounded.subset (image_mono hsub)

lemma lam_nonempty_image_mulVec (R : Matrix (Fin m) (Fin m) ℝ) :
    ((fun x => R.mulVec x) '' unitCube m).Nonempty :=
  ⟨_, mem_image_of_mem _ (show (fun _ => (1 / 2 : ℝ)) ∈ unitCube m from
    fun _ _ => ⟨by norm_num, by norm_num⟩)⟩

/-- The image of the unit cube under a linear map is convex. -/
lemma lam_convex_image_mulVec (R : Matrix (Fin m) (Fin m) ℝ) :
    Convex ℝ ((fun x => R.mulVec x) '' unitCube m) :=
  (convex_pi fun _ _ => convex_Ioo 0 1).is_linear_image ⟨Matrix.mulVec_add R,
    fun c x => Matrix.mulVec_smul R c x⟩

/-- **Rotated test maps.** For an orthogonal `R` and a test map `φ` on the unit cube `Q`,
`ψ (y) = φ (Rᵀ y)` is a test map on `R Q`, with `∇ψ (R x) = ∇φ (x) Rᵀ`. -/
lemma lam_exists_rotate {R : Matrix (Fin m) (Fin m) ℝ} (hR : Rᵀ * R = 1)
    {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    (hφ0 : ∀ x ∉ unitCube m, φ x = 0) :
    ∃ (ψ : (Fin m → ℝ) → Fin d → ℝ) (K' : NNReal), LipschitzWith K' ψ ∧
      (∀ y ∉ (fun x => R.mulVec x) '' unitCube m, ψ y = 0) ∧
      ∀ x, grad ψ (R.mulVec x) = grad φ x * Rᵀ := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.1 hR
  -- the rotation `y ↦ Rᵀ y`, a continuous linear equivalence with inverse `x ↦ R x`
  let Lₗ : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun y => Rᵀ.mulVec y
      invFun := fun x => R.mulVec x
      map_add' := Matrix.mulVec_add Rᵀ
      map_smul' := fun c y => Matrix.mulVec_smul Rᵀ c y
      left_inv := fun y => by simp [Matrix.mulVec_mulVec, hR']
      right_inv := fun x => by simp [Matrix.mulVec_mulVec, hR] }
  let L : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) := Lₗ.toContinuousLinearEquiv
  have hL : ∀ y, L y = Rᵀ.mulVec y := fun _ => rfl
  refine ⟨φ ∘ L, K * ‖(L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ))‖₊,
    hφ.comp (L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)).lipschitzWith, fun y hy => ?_, fun x => ?_⟩
  · rw [lam_image_mulVec_eq_preimage hR] at hy
    exact hφ0 _ hy
  · have hx : L (R.mulVec x) = x := by rw [hL, Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
    ext i k
    simp only [grad, Matrix.of_apply, Matrix.mul_apply]
    have e : (fun z => (φ ∘ L) z i) = (fun w => φ w i) ∘ L := rfl
    rw [e, L.comp_right_fderiv, hx]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hL]
    rw [Matrix.mulVec_single_one]
    conv_lhs => rw [← Finset.univ_sum_single (Rᵀ.col k)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [show Pi.single k' (Rᵀ.col k k') = Rᵀ.col k k' • (Pi.single k' 1 : Fin m → ℝ) by
      rw [← Pi.single_smul', smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]
    rfl

/-- **Quasiconvexity on a rotated cube.** For an orthogonal `R`, quasiconvexity of `f` at `F` on the
cube `R Q`, whose faces are orthogonal to the columns of `R`, is quasiconvexity of `X ↦ f (X Rᵀ)` at
`F R` on `Q`: the change of variables `y = R x`, with the test maps `y ↦ φ (Rᵀ y)`. -/
theorem quasiconvexAtOn_unitCube_comp_orthogonal {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    {F : Matrix (Fin d) (Fin m) ℝ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : Rᵀ * R = 1)
    (hf : QuasiconvexAtOn ((fun x => R.mulVec x) '' unitCube m) f F) :
    QuasiconvexAtOn (unitCube m) (fun X => f (X * Rᵀ)) (F * R) := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.1 hR
  intro φ K hφ hφ0 hint
  obtain ⟨ψ, K', hψ, hψ0, hgrad⟩ := lam_exists_rotate hR hφ hφ0
  have hcomp : ∀ x, f (F + grad ψ (R.mulVec x)) = f ((F * R + grad φ x) * Rᵀ) := by
    intro x
    rw [hgrad, Matrix.add_mul, Matrix.mul_assoc, hR', Matrix.mul_one]
  have hint' :
      IntegrableOn (fun y => f (F + grad ψ y)) ((fun x => R.mulVec x) '' unitCube m) := by
    rw [(lam_measurePreserving_mulVec hR).integrableOn_image (lam_measurableEmbedding_mulVec hR)]
    simpa only [Function.comp_def, hcomp] using hint
  have key := hf ψ _ hψ hψ0 hint'
  rw [lam_setIntegral_image_mulVec hR, lam_volume_image_mulVec hR] at key
  rw [rd_volume_unitCube]
  simpa only [hcomp, Matrix.mul_assoc, hR', Matrix.mul_one] using key

/-- Every unit vector `n` (`n ⬝ᵥ n = 1`) is the `j`-th column of an orthogonal matrix: a
Householder reflection `I − 2 w wᵀ / |w|²`, `w = e_j − n` (the identity if `n = e_j`). -/
theorem exists_orthogonal_mulVec_single_eq (j : Fin m) {n : Fin m → ℝ} (hn : n ⬝ᵥ n = 1) :
    ∃ R : Matrix (Fin m) (Fin m) ℝ, Rᵀ * R = 1 ∧ R.mulVec (Pi.single j 1) = n := by
  set w : Fin m → ℝ := Pi.single j 1 - n
  set s := w ⬝ᵥ w
  set P := Matrix.vecMulVec w w
  -- for `w = 0`, `2 / s = 0` and the matrix is the identity
  refine ⟨1 - (2 / s) • P, ?_, ?_⟩
  · have hT : (1 - (2 / s) • P)ᵀ = 1 - (2 / s) • P := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
        Matrix.transpose_vecMulVec]
    rw [hT]
    rcases eq_or_ne s 0 with hs | hs
    · simp [hs]
    · have hPP : P * P = s • P := by
        rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
      calc (1 - (2 / s) • P) * (1 - (2 / s) • P)
          = 1 - (2 * (2 / s)) • P + ((2 / s) * (2 / s)) • (P * P) := by
            simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
              Matrix.mul_smul, smul_smul]
            module
        _ = 1 := by
            rw [hPP, smul_smul]
            have : 2 / s * (2 / s) * s = 2 * (2 / s) := by field_simp
            rw [this, sub_add_cancel]
  · have hw : w ⬝ᵥ Pi.single j 1 = 1 - n j := by
      rw [dotProduct_single, mul_one]
      simp [w]
    have hs : s = 2 * (1 - n j) := by
      simp only [s, w, sub_dotProduct, dotProduct_sub, single_dotProduct, dotProduct_single, hn]
      simp
      ring
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
      op_smul_eq_smul, hw, smul_smul]
    rcases eq_or_ne (1 - n j) 0 with h | h
    · have hw0 : w = 0 := dotProduct_self_eq_zero.1 (by change s = 0; rw [hs, h, mul_zero])
      have : n = Pi.single j 1 := (sub_eq_zero.1 hw0).symm
      rw [h, mul_zero, zero_smul, sub_zero, this]
    · rw [hs, show 2 / (2 * (1 - n j)) * (1 - n j) = 1 by field_simp, one_smul]
      simp [w]

/-- **The two-point inequality in every rank-one direction** ([R2], proof of Proposition 5.6): for a
lower semicontinuous, locally bounded `f` quasiconvex at `F` on the unit cube, and all `a ∈ ℝ^d`,
`n ∈ ℝ^m` and `λ ∈ (0, 1)`, `f (F) ≤ λ f (F + (1 − λ) a ⊗ n) + (1 − λ) f (F − λ a ⊗ n)`. Write
`a ⊗ n = (|n| a) ⊗ (n / |n|)`, take an orthogonal `R` with `R e_j = n / |n|`
(`exists_orthogonal_mulVec_single_eq`), pass from the unit cube to `Q_n = R Q` by the independence
of the domain (`quasiconvexAtOn_iff`), and apply `le_of_quasiconvexAtOn_unitCube_of_lsc` to
`X ↦ f (X Rᵀ)` at `F R` (`quasiconvexAtOn_unitCube_comp_orthogonal`). -/
theorem le_of_quasiconvexAtOn_vecMulVec {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) {F : Matrix (Fin d) (Fin m) ℝ}
    (hf : QuasiconvexAtOn (unitCube m) f F) (a : Fin d → ℝ) (n : Fin m → ℝ) {l : ℝ} (hl0 : 0 < l)
    (hl1 : l < 1) :
    f F ≤ l * f (F + (1 - l) • Matrix.vecMulVec a n) +
      (1 - l) * f (F - l • Matrix.vecMulVec a n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have h0 : Matrix.vecMulVec a (0 : Fin m → ℝ) = 0 := by
      ext; simp [Matrix.vecMulVec_apply]
    rw [h0, smul_zero, smul_zero, add_zero, sub_zero]
    linarith
  obtain ⟨j, -⟩ := Function.ne_iff.1 hn
  -- the unit vector `n / |n|`
  have hnn : 0 < n ⬝ᵥ n := by
    refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (n i)) ?_
    exact fun h => hn (dotProduct_self_eq_zero.1 h.symm)
  set r := Real.sqrt (n ⬝ᵥ n)
  have hr : 0 < r := Real.sqrt_pos.2 hnn
  have hrr : r * r = n ⬝ᵥ n := Real.mul_self_sqrt hnn.le
  have hn' : (r⁻¹ • n) ⬝ᵥ (r⁻¹ • n) = 1 := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hrr]
    field_simp
  obtain ⟨R, hR, hRj⟩ := exists_orthogonal_mulVec_single_eq j hn'
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.1 hR
  -- quasiconvexity on `Q_n = R Q`, and the change of variables
  have hU := quasiconvexAtOn_unitCube_comp_orthogonal hR ((quasiconvexAtOn_iff hlsc hbdd F
    (lam_isOpen_image_mulVec hR) (lam_isBounded_image_mulVec R)
    (lam_nonempty_image_mulVec R)).1 hf)
  have hcont : Continuous fun X : Matrix (Fin d) (Fin m) ℝ => X * Rᵀ :=
    continuous_id.matrix_mul continuous_const
  have hbdd' : IsLocallyBounded fun X : Matrix (Fin d) (Fin m) ℝ => f (X * Rᵀ) := fun X => by
    obtain ⟨U, hU, C, hC⟩ := hbdd (X * Rᵀ)
    exact ⟨_, hcont.continuousAt.preimage_mem_nhds hU, C, fun B hB => hC _ hB⟩
  have := le_of_quasiconvexAtOn_unitCube_of_lsc (f := fun X => f (X * Rᵀ)) (hlsc.comp hcont) hbdd'
    hU (r • a) j hl0 hl1
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, hR',
    Matrix.mul_one, Matrix.smul_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose] at this
  rwa [hRj, Matrix.smul_vecMulVec, ← Matrix.vecMulVec_smul, smul_smul, mul_inv_cancel₀ hr.ne',
    one_smul] at this

end CalculusOfVariations
