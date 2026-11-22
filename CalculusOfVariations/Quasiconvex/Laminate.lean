/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Lipschitz.Periodic
public import CalculusOfVariations.Quasiconvex.Domain

/-!
# Laminates on the unit cube

* the sawtooth `rd_saw λ`: `1`-periodic, `0` at the integers, slope `1 − λ` on `(k, k + λ)` and
  `−λ` on `(k + λ, k + 1)`, `1`-Lipschitz;
* the laminate of S. Müller, *Variational models for microstructure and phase transitions*, lecture
  notes, MPI MiS Leipzig, 1998, proof of Lemma 4.3: on the unit
  cube `Q = (0, 1)^m`, with `h = rd_saw λ`, `u_k (x) = k⁻¹ h (k x_j) a` (`sawLaminate`) and
  `v_k (x) = min (k⁻¹ h (k x_j), dist_∞ (x, ∂Q)) a` (`cubeLaminate`). Then `v_k` is Lipschitz and
  vanishes off `Q`, `∇v_k ∈ {(1 − λ) a ⊗ e_j, −λ a ⊗ e_j} ∪ {± a ⊗ e_i}` almost everywhere, and
  `|{∇v_k ≠ ∇u_k}| → 0`, while
  `∫_Q f (F + ∇u_k) = λ f (F + (1 − λ) a ⊗ e_j) + (1 − λ) f (F − λ a ⊗ e_j)`. Quasiconvexity at `F`
  on the cube, tested with `v_k`, gives the two-point inequality
  `f (F) ≤ λ f (F + (1 − λ) a ⊗ e_j) + (1 − λ) f (F − λ a ⊗ e_j)`
  (`le_of_quasiconvexAtOn_unitCube`); no regularity of `f` is used, since `f (F + ∇v_k)` takes
  finitely many values;
* an orthogonal change of variables `x ↦ R x` turns `e_j` into the column `R e_j`, so
  quasiconvexity on the cube `R Q`, whose faces are orthogonal to `R e_j`, gives the inequality in
  the direction `a ⊗ R e_j` (`le_of_quasiconvexAtOn_orthogonal`); every unit vector is a column of
  an orthogonal matrix (`exists_orthogonal_mulVec_single_eq`, a Householder reflection), and with
  the independence of the domain (`quasiconvexAtOn_iff`) this gives the inequality in every
  rank-one direction (`le_of_quasiconvexAtOn_vecMulVec`).

`coordLaminate` (`Envelope.Convexity`) is the same construction in the coordinate directions,
with `a = s e_i` and `n` layers, and `cv_layer_measure` bounds its boundary layer.

The statements of the laminate argument are stated here with `sorry` proofs, to be proved.
-/

@[expose] public section

open Metric Set MeasureTheory Filter Topology
open scoped Pointwise Matrix

namespace CalculusOfVariations

variable {d m : ℕ}

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

/-! ### Müller's laminate on the unit cube -/

/-- The laminate `u_k (x) = k⁻¹ h_λ (k x_j) a`, `h_λ = rd_saw λ`: its gradient is
`(1 − λ) a ⊗ e_j` where `fract (k x_j) ∈ (0, λ)` and `−λ a ⊗ e_j` where `fract (k x_j) ∈ (λ, 1)`. -/
noncomputable def sawLaminate (a : Fin d → ℝ) (j : Fin m) (l : ℝ) (k : ℕ) (x : Fin m → ℝ) :
    Fin d → ℝ :=
  ((k : ℝ)⁻¹ * rd_saw l (k * x j)) • a

/-- Müller's laminate `v_k (x) = min (k⁻¹ h_λ (k x_j), dist_∞ (x, ∂Q)) a` on the unit cube `Q`:
the distance is the sup-norm distance to the complement of `Q`, so `v_k` vanishes off `Q`. -/
noncomputable def cubeLaminate (a : Fin d → ℝ) (j : Fin m) (l : ℝ) (k : ℕ) (x : Fin m → ℝ) :
    Fin d → ℝ :=
  min ((k : ℝ)⁻¹ * rd_saw l (k * x j)) (infDist x (unitCube m)ᶜ) • a

/-- `v_k` is `‖a‖`-Lipschitz (sup norms). -/
theorem cubeLaminate_lipschitz (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (k : ℕ) : LipschitzWith ‖a‖₊ (cubeLaminate a j l k) := by
  sorry

/-- `v_k` vanishes off the unit cube. -/
theorem cubeLaminate_eq_zero (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (k : ℕ) : ∀ x ∉ unitCube m, cubeLaminate a j l k x = 0 := by
  sorry

/-- Almost everywhere on the unit cube, `∇v_k ∈ {(1 − λ) a ⊗ e_j, −λ a ⊗ e_j} ∪ {± a ⊗ e_i}`. -/
theorem ae_grad_cubeLaminate_mem (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1)
    {k : ℕ} (hk : 0 < k) :
    ∀ᵐ x, x ∈ unitCube m → grad (cubeLaminate a j l k) x ∈
      ({(1 - l) • Matrix.vecMulVec a (Pi.single j 1), (-l) • Matrix.vecMulVec a (Pi.single j 1)} ∪
        Set.range (fun i => Matrix.vecMulVec a (Pi.single i 1)) ∪
        Set.range (fun i => -Matrix.vecMulVec a (Pi.single i 1)) :
        Set (Matrix (Fin d) (Fin m) ℝ)) := by
  sorry

/-- `|{x ∈ Q : ∇v_k (x) ≠ ∇u_k (x)}| → 0` as `k → ∞`. -/
theorem tendsto_volume_grad_cubeLaminate_ne (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) :
    Tendsto (fun k : ℕ => volume {x ∈ unitCube m |
      grad (cubeLaminate a j l k) x ≠ grad (sawLaminate a j l k) x}) atTop (𝓝 0) := by
  sorry

/-- The energy of `u_k`: for every `f` and `k ≥ 1`,
`∫_Q f (F + ∇u_k) = λ f (F + (1 − λ) a ⊗ e_j) + (1 − λ) f (F − λ a ⊗ e_j)`. -/
theorem setIntegral_sawLaminate (f : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (F : Matrix (Fin d) (Fin m) ℝ) (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1)
    {k : ℕ} (hk : 0 < k) :
    ∫ x in unitCube m, f (F + grad (sawLaminate a j l k) x) =
      l * f (F + (1 - l) • Matrix.vecMulVec a (Pi.single j 1)) +
        (1 - l) * f (F - l • Matrix.vecMulVec a (Pi.single j 1)) := by
  sorry

/-- **The two-point inequality on the unit cube** (Müller 1998, proof of Lemma 4.3): if `f` is
quasiconvex at `F` on the unit cube, then
`f (F) ≤ λ f (F + (1 − λ) a ⊗ e_j) + (1 − λ) f (F − λ a ⊗ e_j)`. The test maps are the laminates
`v_k` (`cubeLaminate`): `f (F) ≤ ∫_Q f (F + ∇v_k)`, which differs from
`∫_Q f (F + ∇u_k) = λ f (F + (1 − λ) a ⊗ e_j) + (1 − λ) f (F − λ a ⊗ e_j)` by at most
`2 max |f| · |{∇v_k ≠ ∇u_k}| → 0`, the maximum over the finitely many values of `F + ∇v_k` and
`F + ∇u_k`. No regularity of `f` is needed. -/
theorem le_of_quasiconvexAtOn_unitCube {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    {F : Matrix (Fin d) (Fin m) ℝ} (hf : QuasiconvexAtOn (unitCube m) f F) (a : Fin d → ℝ)
    (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) :
    f F ≤ l * f (F + (1 - l) • Matrix.vecMulVec a (Pi.single j 1)) +
      (1 - l) * f (F - l • Matrix.vecMulVec a (Pi.single j 1)) := by
  sorry

/-! ### The cube with faces orthogonal to a given direction -/

/-- **The two-point inequality on a rotated cube.** For an orthogonal matrix `R` (`Rᵀ R = 1`), if
`f` is quasiconvex at `F` on the cube `R Q`, whose faces are orthogonal to the columns of `R`,
then the two-point inequality holds in the direction `a ⊗ R e_j`. The test maps are
`x ↦ v_k (Rᵀ x)`, with gradients `∇v_k (Rᵀ x) Rᵀ`, and `x ↦ R x` preserves the volume. -/
theorem le_of_quasiconvexAtOn_orthogonal {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    {F : Matrix (Fin d) (Fin m) ℝ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : Rᵀ * R = 1)
    (hf : QuasiconvexAtOn ((fun x => R.mulVec x) '' unitCube m) f F) (a : Fin d → ℝ)
    (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) :
    f F ≤ l * f (F + (1 - l) • Matrix.vecMulVec a (R.mulVec (Pi.single j 1))) +
      (1 - l) * f (F - l • Matrix.vecMulVec a (R.mulVec (Pi.single j 1))) := by
  sorry

/-- Every unit vector `n` (`n ⬝ᵥ n = 1`) is the `j`-th column of an orthogonal matrix: a
Householder reflection `I − 2 w wᵀ / |w|²`, `w = e_j − n` (the identity if `n = e_j`). -/
theorem exists_orthogonal_mulVec_single_eq (j : Fin m) {n : Fin m → ℝ} (hn : n ⬝ᵥ n = 1) :
    ∃ R : Matrix (Fin m) (Fin m) ℝ, Rᵀ * R = 1 ∧ R.mulVec (Pi.single j 1) = n := by
  sorry

/-- **The two-point inequality in every rank-one direction** (Müller 1998, Lemma 4.3): for a lower
semicontinuous, locally bounded `f` quasiconvex at `F` on the unit cube, and all `a ∈ ℝ^d`,
`n ∈ ℝ^m` and `λ ∈ (0, 1)`, `f (F) ≤ λ f (F + (1 − λ) a ⊗ n) + (1 − λ) f (F − λ a ⊗ n)`. Write
`a ⊗ n = (|n| a) ⊗ (n / |n|)`, take an orthogonal `R` with `R e_j = n / |n|`
(`exists_orthogonal_mulVec_single_eq`), pass from the unit cube to `R Q` by the independence of
the domain (`quasiconvexAtOn_iff`, whose statement here assumes `f` lower semicontinuous and
locally bounded; Müller's Lemma 4.3 needs no regularity, and `le_of_quasiconvexAtOn_orthogonal`
needs none), and apply `le_of_quasiconvexAtOn_orthogonal`. -/
theorem le_of_quasiconvexAtOn_vecMulVec {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) {F : Matrix (Fin d) (Fin m) ℝ}
    (hf : QuasiconvexAtOn (unitCube m) f F) (a : Fin d → ℝ) (n : Fin m → ℝ) {l : ℝ} (hl0 : 0 < l)
    (hl1 : l < 1) :
    f F ≤ l * f (F + (1 - l) • Matrix.vecMulVec a n) +
      (1 - l) * f (F - l • Matrix.vecMulVec a n) := by
  sorry

end CalculusOfVariations
