/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Lipschitz.Periodic
public import CalculusOfVariations.Quasiconvex.Domain
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Laminates on the unit cube

The proof of S. Müller, *Variational models for microstructure and phase transitions*, lecture
notes, MPI MiS Leipzig, 1998, Lemma 4.3 (a quasiconvex integrand satisfies the two-point
inequality along every rank-one segment):

* the sawtooth `rd_saw λ`: `1`-periodic, `0` at the integers, slope `1 − λ` on `(k, k + λ)` and
  `−λ` on `(k + λ, k + 1)`, `1`-Lipschitz;
* Müller's laminates on the unit cube `Q = (0, 1)^m`, with `h = rd_saw λ`:
  `u_k (x) = k⁻¹ h (k x_j) a` (`sawLaminate`) and
  `v_k (x) = min (k⁻¹ h (k x_j), dist_∞ (x, ∂Q)) a` (`cubeLaminate`). Then `v_k` is Lipschitz and
  vanishes off `Q` (`cubeLaminate_lipschitz`, `cubeLaminate_eq_zero`);
  `∇v_k ∈ {(1 − λ) a ⊗ e_j, −λ a ⊗ e_j} ∪ {± a ⊗ e_i}` almost everywhere on `Q`
  (`ae_grad_cubeLaminate_mem`: on `Q` the distance is `min_i min (x_i, 1 − x_i)`, and at almost
  every point the derivative of a minimum of Lipschitz functions is the derivative of a function
  attaining it, by the vanishing of the gradient of a Lipschitz map almost everywhere on its zero
  set, `rd_ae_fderiv_eq_zero`); `|{∇v_k ≠ ∇u_k}| → 0`, since the bad set lies in the boundary layer
  `{x ∈ Q : dist_∞ (x, Qᶜ) ≤ 1/k}`, of measure at most `2m/k` (`lam_layer_measure`,
  `tendsto_volume_grad_cubeLaminate_ne`); and for every `f`,
  `∫_Q f (F + ∇u_k) = λ f (F + (1 − λ) a ⊗ e_j) + (1 − λ) f (F − λ a ⊗ e_j)`
  (`setIntegral_sawLaminate`). Quasiconvexity at `F` on the cube, tested with `v_k`, gives the
  two-point inequality `f (F) ≤ λ f (F + (1 − λ) a ⊗ e_j) + (1 − λ) f (F − λ a ⊗ e_j)`
  (`le_of_quasiconvexAtOn_unitCube`); no regularity of `f` is used, since almost everywhere
  `f (F + ∇v_k)` and `f (F + ∇u_k)` take finitely many values;
* an orthogonal change of variables `x ↦ R x` turns `e_j` into the column `R e_j`, so
  quasiconvexity on the cube `R Q`, whose faces are orthogonal to `R e_j`, gives the inequality in
  the direction `a ⊗ R e_j` (`le_of_quasiconvexAtOn_orthogonal`); every unit vector is a column of
  an orthogonal matrix (`exists_orthogonal_mulVec_single_eq`, a Householder reflection), and with
  the independence of the domain (`quasiconvexAtOn_iff`) this gives the inequality in every
  rank-one direction (`le_of_quasiconvexAtOn_vecMulVec`).
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

private lemma lam_saw_nonneg (l t : ℝ) : 0 ≤ rd_saw l t := le_max_left _ _

private lemma lam_saw_le_one {l : ℝ} (hl0 : 0 ≤ l) (t : ℝ) : rd_saw l t ≤ 1 := by
  rw [rd_saw_eq]
  refine max_le zero_le_one ((min_le_left _ _).trans ?_)
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  nlinarith

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

/-! ### Lipschitz bound and support -/

/-- The sawtooth part `x ↦ k⁻¹ h_λ (k x_j)` is `1`-Lipschitz (for `k = 0` it is `0`). -/
private lemma lam_sawPart_lipschitz (j : Fin m) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (k : ℕ) :
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

/-- `v_k` is `‖a‖`-Lipschitz (sup norms): the sawtooth part and the distance are `1`-Lipschitz,
hence so is their minimum, and `s ↦ s a` is `‖a‖`-Lipschitz. -/
theorem cubeLaminate_lipschitz (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (k : ℕ) : LipschitzWith ‖a‖₊ (cubeLaminate a j l k) := by
  have h3 := (lam_sawPart_lipschitz j hl0 hl1 k).min (lipschitz_infDist_pt (unitCube m)ᶜ)
  have hs : LipschitzWith ‖a‖₊ (fun t : ℝ => t • a) := LipschitzWith.of_dist_le_mul fun s t => by
    rw [dist_eq_norm, dist_eq_norm, ← sub_smul, norm_smul, mul_comm]; rfl
  have := hs.comp h3
  rw [max_self, mul_one] at this
  exact this

/-- `v_k` vanishes off the unit cube: there the distance is `0` and the sawtooth is `≥ 0`. -/
theorem cubeLaminate_eq_zero (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (k : ℕ) : ∀ x ∉ unitCube m, cubeLaminate a j l k x = 0 := by
  -- the bounds on `λ` are not needed: the sawtooth is nonnegative for every `λ`
  have _ := hl0
  have _ := hl1
  intro x hx
  simp only [cubeLaminate]
  rw [infDist_zero_of_mem (mem_compl hx),
    min_eq_right (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg k)) (lam_saw_nonneg l _)), zero_smul]

/-! ### The gradient of `v_k` -/

/-- A coordinate preimage of a null set is null. -/
private lemma lam_volume_eval_preimage_null (j : Fin m) {N : Set ℝ} (hN : volume N = 0) :
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
private lemma lam_ae_fract_ne (j : Fin m) {k : ℕ} (hk : 0 < k) (c : ℝ) :
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

/-- At almost every point where two Lipschitz functions agree, their derivatives agree: the
derivative of their difference vanishes almost everywhere on its zero set
(`rd_ae_fderiv_eq_zero`). -/
private lemma lam_ae_fderiv_eq_of_eq {φ₁ φ₂ : (Fin m → ℝ) → ℝ} {K₁ K₂ : NNReal}
    (h₁ : LipschitzWith K₁ φ₁) (h₂ : LipschitzWith K₂ φ₂) :
    ∀ᵐ x, φ₁ x = φ₂ x → fderiv ℝ φ₁ x = fderiv ℝ φ₂ x := by
  set Φ : (Fin m → ℝ) → Fin 1 → ℝ := fun y _ => φ₁ y - φ₂ y
  have hΦ : LipschitzWith (K₁ + K₂) Φ := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_pi_le_iff (by positivity)]
    intro _
    exact (h₁.sub h₂).dist_le_mul x y
  filter_upwards [rd_ae_fderiv_eq_zero hΦ, h₁.ae_differentiableAt, h₂.ae_differentiableAt]
    with x hx hd₁ hd₂ heq
  have h0 : fderiv ℝ Φ x = 0 := hx (funext fun _ => sub_eq_zero.2 heq)
  have hd : HasFDerivAt Φ (ContinuousLinearMap.pi fun _ => fderiv ℝ φ₁ x - fderiv ℝ φ₂ x) x :=
    hasFDerivAt_pi.2 fun _ => hd₁.hasFDerivAt.sub hd₂.hasFDerivAt
  rw [hd.fderiv] at h0
  ext v
  have := congrFun (congrArg (fun L => L v) h0) 0
  simpa [sub_eq_zero] using this

/-- The gradient of `y ↦ ψ (y) a` is `a ⊗ ∇ψ`. -/
private lemma lam_grad_smul (ψ : (Fin m → ℝ) → ℝ) (a : Fin d → ℝ) (x : Fin m → ℝ) :
    grad (fun y => ψ y • a) x = Matrix.vecMulVec a (fun i => fderiv ℝ ψ x (Pi.single i 1)) := by
  ext i k
  simp only [grad, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
  have : (fun y => ψ y * a i) = a i • ψ := by funext y; simp [mul_comm]
  rw [this, fderiv_const_smul_field]
  simp

private lemma lam_proj_single (i : Fin m) :
    (fun i' => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i)
      (Pi.single i' 1)) = Pi.single i 1 := by
  funext i'
  simp [Pi.single_apply, eq_comm]

private lemma lam_smul_proj_single (c : ℝ) (i : Fin m) :
    (fun i' => (c • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i)
      (Pi.single i' 1)) = c • Pi.single i 1 := by
  funext i'
  simp [Pi.single_apply, eq_comm]

/-- The gradient of `y ↦ ψ (y) a` where `ψ` has derivative `c e_j`. -/
private lemma lam_grad_smul_of_hasFDerivAt {ψ : (Fin m → ℝ) → ℝ} (a : Fin d → ℝ) {j : Fin m}
    {c : ℝ} {x : Fin m → ℝ}
    (h : HasFDerivAt ψ (c • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j) x) :
    grad (fun y => ψ y • a) x = c • Matrix.vecMulVec a (Pi.single j 1) := by
  rw [lam_grad_smul, h.fderiv, lam_smul_proj_single, Matrix.vecMulVec_smul]

/-- On the unit cube the sup-norm distance to the complement is `x_i` or `1 − x_i` for some `i`
(it is `min_i min (x_i, 1 − x_i)`). -/
lemma exists_infDist_compl_unitCube_eq {x : Fin m → ℝ} (hx : x ∈ unitCube m) (i₀ : Fin m) :
    ∃ i, infDist x (unitCube m)ᶜ = x i ∨ infDist x (unitCube m)ᶜ = 1 - x i := by
  have hx' : ∀ i, 0 < x i ∧ x i < 1 := fun i => hx i (mem_univ i)
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => min (x i) (1 - x i))
    ⟨i₀, Finset.mem_univ _⟩
  have hout : ∀ v : ℝ, v ∉ Ioo (0 : ℝ) 1 → Function.update x i v ∈ (unitCube m)ᶜ :=
    fun v hv hmem => hv (by simpa using hmem i (mem_univ i))
  have hle : ∀ v : ℝ, v ∉ Ioo (0 : ℝ) 1 → infDist x (unitCube m)ᶜ ≤ |x i - v| := by
    intro v hv
    refine (infDist_le_dist_of_mem (hout v hv)).trans ?_
    rw [dist_pi_le_iff (abs_nonneg _)]
    intro b
    rcases eq_or_ne b i with rfl | hb
    · simp [Real.dist_eq]
    · simp [Function.update_of_ne hb]
  have hge : min (x i) (1 - x i) ≤ infDist x (unitCube m)ᶜ := by
    refine (le_infDist ⟨_, hout 0 (by simp)⟩).2 fun y hy => ?_
    have : ∃ b, y b ∉ Ioo (0 : ℝ) 1 := by
      by_contra h
      push Not at h
      exact hy fun b _ => h b
    obtain ⟨b, hb⟩ := this
    refine (hi b (Finset.mem_univ _)).trans ?_
    refine le_trans ?_ (dist_le_pi_dist x y b)
    rw [Real.dist_eq]
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hb
    rcases hb with hb | hb
    · exact (min_le_left _ _).trans (by rw [abs_of_pos (by linarith [hx' b])]; linarith)
    · exact (min_le_right _ _).trans
        (by rw [abs_sub_comm, abs_of_pos (by linarith [hx' b])]; linarith)
  refine ⟨i, ?_⟩
  rcases min_choice (x i) (1 - x i) with h | h
  · left
    refine le_antisymm ?_ (h ▸ hge)
    have := hle 0 (by simp)
    rwa [sub_zero, abs_of_pos (hx' i).1] at this
  · right
    refine le_antisymm ?_ (h ▸ hge)
    have := hle 1 (by simp)
    rwa [abs_sub_comm, abs_of_pos (by linarith [(hx' i).2])] at this

/-- The derivative of the sawtooth part `y ↦ k⁻¹ h_λ (k y_j)`, where `h_λ` has derivative `c`. -/
private lemma lam_hasFDerivAt_sawPart (j : Fin m) {k : ℕ} (hk : 0 < k) {l c : ℝ}
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
private lemma lam_ae_hasFDerivAt_sawPart (j : Fin m) {k : ℕ} (hk : 0 < k) {l : ℝ} (hl0 : 0 < l)
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

/-- Almost everywhere on the unit cube, `∇v_k ∈ {(1 − λ) a ⊗ e_j, −λ a ⊗ e_j} ∪ {± a ⊗ e_i}`.
Write `v_k = ψ a` with `ψ = min (g, D)`, `g (x) = k⁻¹ h_λ (k x_j)`, `D (x) = dist_∞ (x, Qᶜ)`. Almost
everywhere `∇g ∈ {(1 − λ) e_j, −λ e_j}`; on `Q`, `D` equals one of the affine maps `x_i`, `1 − x_i`;
and at almost every point where two Lipschitz functions agree their derivatives agree
(`rd_ae_fderiv_eq_zero`), so `∇ψ` is `∇g` or `∇D`, and `∇D` is `± e_i`. -/
theorem ae_grad_cubeLaminate_mem (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1)
    {k : ℕ} (hk : 0 < k) :
    ∀ᵐ x, x ∈ unitCube m → grad (cubeLaminate a j l k) x ∈
      ({(1 - l) • Matrix.vecMulVec a (Pi.single j 1), (-l) • Matrix.vecMulVec a (Pi.single j 1)} ∪
        Set.range (fun i => Matrix.vecMulVec a (Pi.single i 1)) ∪
        Set.range (fun i => -Matrix.vecMulVec a (Pi.single i 1)) :
        Set (Matrix (Fin d) (Fin m) ℝ)) := by
  set g : (Fin m → ℝ) → ℝ := fun y => (k : ℝ)⁻¹ * rd_saw l (k * y j)
  set D : (Fin m → ℝ) → ℝ := fun y => infDist y (unitCube m)ᶜ
  set ψ : (Fin m → ℝ) → ℝ := fun y => min (g y) (D y)
  have hg : LipschitzWith 1 g := lam_sawPart_lipschitz j hl0.le hl1.le k
  have hD : LipschitzWith 1 D := lipschitz_infDist_pt _
  have hψ := hg.min hD
  have hc : ∀ i : Fin m, LipschitzWith 1 (fun y : Fin m → ℝ => y i) := fun i =>
    LipschitzWith.eval i
  have hc' : ∀ i : Fin m, LipschitzWith (0 + 1) (fun y : Fin m → ℝ => 1 - y i) := fun i =>
    (LipschitzWith.const (1 : ℝ)).sub (LipschitzWith.eval i)
  filter_upwards [lam_ae_fderiv_eq_of_eq hψ hg, lam_ae_fderiv_eq_of_eq hψ hD,
    ae_all_iff.2 fun i => lam_ae_fderiv_eq_of_eq hD (hc i),
    ae_all_iff.2 fun i => lam_ae_fderiv_eq_of_eq hD (hc' i),
    lam_ae_hasFDerivAt_sawPart j hk hl0 hl1] with x h1 h2 h3 h4 h5 hxQ
  have hv : grad (cubeLaminate a j l k) x =
      Matrix.vecMulVec a (fun i => fderiv ℝ ψ x (Pi.single i 1)) := lam_grad_smul ψ a x
  rcases min_choice (g x) (D x) with hm | hm
  · -- `ψ = g` at `x`: the sawtooth part
    have e := (h1 hm).trans h5.fderiv
    rw [hv, e, lam_smul_proj_single, Matrix.vecMulVec_smul]
    left; left
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · -- `ψ = D` at `x`: the distance part
    obtain ⟨i, hi | hi⟩ := exists_infDist_compl_unitCube_eq hxQ j
    · have e := ((h2 hm).trans (h3 i hi)).trans (hasFDerivAt_apply i x).fderiv
      left; right
      refine ⟨i, ?_⟩
      rw [hv, e, lam_proj_single]
    · have e := ((h2 hm).trans (h4 i hi)).trans ((hasFDerivAt_apply i x).const_sub 1).fderiv
      right
      refine ⟨i, ?_⟩
      rw [hv, e]
      simp only [neg_apply]
      rw [show (fun i' => -(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i)
          (Pi.single i' 1)) =
        -(fun i' => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i)
          (Pi.single i' 1)) from rfl,
        lam_proj_single, Matrix.vecMulVec_neg]

/-! ### The boundary layer -/

/-- The boundary layer `{x ∈ Q : dist_∞ (x, Qᶜ) ≤ η}` of the unit cube has measure at most
`2 m η`: for `η < 1/2` it misses the cube `(η, 1 − η)^m`, of measure `(1 − 2η)^m ≥ 1 − 2 m η`. -/
theorem lam_layer_measure (hm : 0 < m) {η : ℝ} (hη : 0 ≤ η) :
    volume.real {x | x ∈ unitCube m ∧ infDist x (unitCube m)ᶜ ≤ η} ≤ 2 * m * η := by
  have hQfin : volume (unitCube m) ≠ ⊤ := by rw [rd_volume_unitCube]; exact ENNReal.one_ne_top
  have hQ1 : volume.real (unitCube m) = 1 := by
    rw [measureReal_def, rd_volume_unitCube, ENNReal.toReal_one]
  have hsub : {x | x ∈ unitCube m ∧ infDist x (unitCube m)ᶜ ≤ η} ⊆ unitCube m := fun x hx => hx.1
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rcases le_or_gt (1 / 2) η with hη2 | hη2
  · calc volume.real {x | x ∈ unitCube m ∧ infDist x (unitCube m)ᶜ ≤ η}
        ≤ volume.real (unitCube m) := measureReal_mono hsub hQfin
      _ = 1 := hQ1
      _ ≤ 2 * m * η := by nlinarith
  · set P : Set (Fin m → ℝ) := univ.pi fun _ => Ioo η (1 - η)
    have hPQ : P ⊆ unitCube m := fun x hx i hi =>
      ⟨by linarith [(hx i hi).1], by linarith [(hx i hi).2]⟩
    have hsub2 : {x | x ∈ unitCube m ∧ infDist x (unitCube m)ᶜ ≤ η} ⊆ unitCube m \ P := by
      intro x hx
      refine ⟨hx.1, fun hxP => ?_⟩
      obtain ⟨i, hi | hi⟩ := exists_infDist_compl_unitCube_eq hx.1 ⟨0, hm⟩
      · have := (hxP i (mem_univ i)).1
        linarith [hx.2]
      · have := (hxP i (mem_univ i)).2
        linarith [hx.2]
    have hPvol : volume.real P = (1 - 2 * η) ^ m := by
      simp only [P, measureReal_def, Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith)]
      ring_nf
    calc volume.real {x | x ∈ unitCube m ∧ infDist x (unitCube m)ᶜ ≤ η}
        ≤ volume.real (unitCube m \ P) :=
          measureReal_mono hsub2 (ne_top_of_le_ne_top hQfin (measure_mono sdiff_subset))
      _ = 1 - (1 - 2 * η) ^ m := by
          rw [measureReal_sdiff hPQ (MeasurableSet.univ_pi fun _ => measurableSet_Ioo) hQfin, hQ1,
            hPvol]
      _ ≤ 2 * m * η := by
          have := one_add_mul_le_pow (a := -2 * η) (by linarith) m
          have e : (1 : ℝ) + -2 * η = 1 - 2 * η := by ring
          rw [e] at this
          nlinarith

/-- `|{x ∈ Q : ∇v_k (x) ≠ ∇u_k (x)}| → 0` as `k → ∞`. Where `dist_∞ (x, Qᶜ) > k⁻¹ h_λ (k x_j)`,
an open condition, `v_k = u_k` near `x`; since `h_λ ≤ 1`, the bad set lies in the boundary layer
`{x ∈ Q : dist_∞ (x, Qᶜ) ≤ 1/k}`, of measure at most `2m/k` (`lam_layer_measure`). -/
theorem tendsto_volume_grad_cubeLaminate_ne (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) :
    Tendsto (fun k : ℕ => volume {x ∈ unitCube m |
      grad (cubeLaminate a j l k) x ≠ grad (sawLaminate a j l k) x}) atTop (𝓝 0) := by
  have hm : 0 < m := j.pos
  have hsub : ∀ k : ℕ, {x ∈ unitCube m |
      grad (cubeLaminate a j l k) x ≠ grad (sawLaminate a j l k) x} ⊆
      {x | x ∈ unitCube m ∧ infDist x (unitCube m)ᶜ ≤ (k : ℝ)⁻¹} := by
    intro k x ⟨hxQ, hne⟩
    refine ⟨hxQ, ?_⟩
    by_contra hlt
    push Not at hlt
    apply hne
    have hgx : (k : ℝ)⁻¹ * rd_saw l (k * x j) ≤ (k : ℝ)⁻¹ := by
      have := lam_saw_le_one hl0 (k * x j)
      calc (k : ℝ)⁻¹ * rd_saw l (k * x j) ≤ (k : ℝ)⁻¹ * 1 := by gcongr
        _ = (k : ℝ)⁻¹ := mul_one _
    have hopen : IsOpen
        {y : Fin m → ℝ | (k : ℝ)⁻¹ * rd_saw l (k * y j) < infDist y (unitCube m)ᶜ} :=
      isOpen_lt (lam_sawPart_lipschitz j hl0 hl1 k).continuous (continuous_infDist_pt _)
    apply cv_grad_congr
    filter_upwards [hopen.mem_nhds (show x ∈ _ from hgx.trans_lt hlt)] with y hy
    simp only [cubeLaminate, sawLaminate]
    rw [min_eq_left hy.le]
  have hbound : ∀ k : ℕ, volume {x ∈ unitCube m |
      grad (cubeLaminate a j l k) x ≠ grad (sawLaminate a j l k) x} ≤
      ENNReal.ofReal (2 * m * (k : ℝ)⁻¹) := by
    intro k
    refine (measure_mono (hsub k)).trans ?_
    have hfin : volume {x | x ∈ unitCube m ∧ infDist x (unitCube m)ᶜ ≤ (k : ℝ)⁻¹} ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [rd_volume_unitCube]; exact ENNReal.one_ne_top)
        (measure_mono fun x hx => hx.1)
    rw [← ofReal_measureReal hfin]
    exact ENNReal.ofReal_le_ofReal (lam_layer_measure hm (inv_nonneg.2 (Nat.cast_nonneg k)))
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (2 * m * (k : ℝ)⁻¹)) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul
      (2 * (m : ℝ))
    simpa using ENNReal.tendsto_ofReal this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
    hbound

/-! ### The energies of `u_k` and `v_k` -/

/-- The energy of `u_k`: for every `f` and `k ≥ 1`,
`∫_Q f (F + ∇u_k) = λ f (F + (1 − λ) a ⊗ e_j) + (1 − λ) f (F − λ a ⊗ e_j)`. Almost everywhere
`f (F + ∇u_k (x)) = G (k x)` with `G (y) = f (F + (1 − λ) a ⊗ e_j)` where `fract (y_j) < λ` and
`f (F − λ a ⊗ e_j)` elsewhere, a bounded measurable `ℤ^m`-periodic function, so
`∫_Q G (k x) dx = ∫_Q G` (`rd_setIntegral_comp_nsmul`), and `|{y ∈ Q : y_j < λ}| = λ`. -/
theorem setIntegral_sawLaminate (f : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (F : Matrix (Fin d) (Fin m) ℝ) (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1)
    {k : ℕ} (hk : 0 < k) :
    ∫ x in unitCube m, f (F + grad (sawLaminate a j l k) x) =
      l * f (F + (1 - l) • Matrix.vecMulVec a (Pi.single j 1)) +
        (1 - l) * f (F - l • Matrix.vecMulVec a (Pi.single j 1)) := by
  set c₁ := f (F + (1 - l) • Matrix.vecMulVec a (Pi.single j 1))
  set c₂ := f (F - l • Matrix.vecMulVec a (Pi.single j 1))
  set G : (Fin m → ℝ) → ℝ := fun y => if Int.fract (y j) < l then c₁ else c₂
  have hae : ∀ᵐ x : Fin m → ℝ, f (F + grad (sawLaminate a j l k) x) = G ((k : ℝ) • x) := by
    filter_upwards [lam_ae_hasFDerivAt_sawPart j hk hl0 hl1] with x hx
    have e : grad (sawLaminate a j l k) x = _ := lam_grad_smul_of_hasFDerivAt a hx
    rw [e]
    simp only [G, Pi.smul_apply, smul_eq_mul]
    split_ifs
    · rfl
    · simp only [c₂, sub_eq_add_neg, neg_smul]
  have hGm : Measurable G :=
    Measurable.ite (measurableSet_lt (measurable_fract.comp (measurable_pi_apply j))
      measurable_const) measurable_const measurable_const
  have hGb : ∀ y, |G y| ≤ |c₁| + |c₂| := fun y => by
    simp only [G]
    split_ifs <;> linarith [abs_nonneg c₁, abs_nonneg c₂]
  have hGper : ∀ (y : Fin m → ℝ) (z : Fin m → ℤ), G (y + fun i => (z i : ℝ)) = G y := by
    intro y z
    simp only [G, Pi.add_apply, Int.fract_add_intCast]
  rw [integral_congr_ae (ae_restrict_of_ae hae), rd_setIntegral_comp_nsmul hGm hGb hGper hk]
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

/-- The restriction of any function to a finite set of matrices is measurable. -/
private lemma lam_measurable_indicator_of_finite {T : Set (Matrix (Fin d) (Fin m) ℝ)}
    (hT : T.Finite) (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Measurable (T.indicator f) := by
  intro B hB
  rw [Set.indicator_preimage]
  exact (hT.subset inter_subset_right).measurableSet.union
    ((measurable_zero hB).diff hT.measurableSet)

/-- **The two-point inequality on the unit cube** (Müller 1998, proof of Lemma 4.3): if `f` is
quasiconvex at `F` on the unit cube, then
`f (F) ≤ λ f (F + (1 − λ) a ⊗ e_j) + (1 − λ) f (F − λ a ⊗ e_j)`. The test maps are the laminates
`v_k` (`cubeLaminate`): `f (F) ≤ ∫_Q f (F + ∇v_k)`, which differs from
`∫_Q f (F + ∇u_k) = λ f (F + (1 − λ) a ⊗ e_j) + (1 − λ) f (F − λ a ⊗ e_j)` by at most
`2 max |f| · |{∇v_k ≠ ∇u_k}| → 0`, the maximum over the finitely many values of `F + ∇v_k` and
`F + ∇u_k`. No regularity of `f` is needed: almost everywhere on `Q` the integrands agree with
those of the measurable, bounded restriction of `f` to these finitely many values (which also
gives the integrability required by `QuasiconvexAtOn`). -/
theorem le_of_quasiconvexAtOn_unitCube {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    {F : Matrix (Fin d) (Fin m) ℝ} (hf : QuasiconvexAtOn (unitCube m) f F) (a : Fin d → ℝ)
    (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) :
    f F ≤ l * f (F + (1 - l) • Matrix.vecMulVec a (Pi.single j 1)) +
      (1 - l) * f (F - l • Matrix.vecMulVec a (Pi.single j 1)) := by
  set A₀ := Matrix.vecMulVec a (Pi.single j (1 : ℝ))
  -- the finitely many values of `F + ∇v_k`, and the restriction `f'` of `f` to them
  set S : Set (Matrix (Fin d) (Fin m) ℝ) := {(1 - l) • A₀, (-l) • A₀} ∪
    Set.range (fun i => Matrix.vecMulVec a (Pi.single i 1)) ∪
    Set.range (fun i => -Matrix.vecMulVec a (Pi.single i 1))
  have hS : S.Finite := ((Set.toFinite _).union (Set.finite_range _)).union (Set.finite_range _)
  set T := (fun X => F + X) '' S
  have hT : T.Finite := hS.image _
  set f' := T.indicator f
  have hf'm : Measurable f' := lam_measurable_indicator_of_finite hT f
  set C := ∑ X ∈ hT.toFinset, |f X|
  have hC : ∀ X, |f' X| ≤ C := by
    intro X
    by_cases hX : X ∈ T
    · rw [show f' X = f X from Set.indicator_of_mem hX f]
      exact Finset.single_le_sum (f := fun X => |f X|) (fun _ _ => abs_nonneg _)
        ((Set.Finite.mem_toFinset hT).2 hX)
    · rw [show f' X = 0 from Set.indicator_of_notMem hX f, abs_zero]
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hQm : MeasurableSet (unitCube m) := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hQfin : volume (unitCube m) < ⊤ := by rw [rd_volume_unitCube]; exact ENNReal.one_lt_top
  have hint : ∀ φ : (Fin m → ℝ) → Fin d → ℝ,
      IntegrableOn (fun x => f' (F + grad φ x)) (unitCube m) := fun φ =>
    IntegrableOn.of_bound hQfin (hf'm.comp (rd_measurable_add_grad F φ)).aestronglyMeasurable C
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC _)
  have hT1 : F + (1 - l) • A₀ ∈ T := mem_image_of_mem _ (Or.inl (Or.inl (Or.inl rfl)))
  have hT2 : F - l • A₀ ∈ T := by
    rw [sub_eq_add_neg, ← neg_smul]
    exact mem_image_of_mem _ (Or.inl (Or.inl (Or.inr rfl)))
  set E := l * f (F + (1 - l) • A₀) + (1 - l) * f (F - l • A₀)
  -- quasiconvexity tested with `v_k`
  have hv : ∀ k : ℕ, 0 < k →
      f F ≤ ∫ x in unitCube m, f' (F + grad (cubeLaminate a j l k) x) := by
    intro k hk
    have hae : ∀ᵐ x ∂(volume.restrict (unitCube m)),
        f (F + grad (cubeLaminate a j l k) x) = f' (F + grad (cubeLaminate a j l k) x) := by
      rw [ae_restrict_iff' hQm]
      filter_upwards [ae_grad_cubeLaminate_mem a j hl0 hl1 hk] with x hx hxQ
      exact (Set.indicator_of_mem (mem_image_of_mem _ (hx hxQ)) f).symm
    have := hf _ ‖a‖₊ (cubeLaminate_lipschitz a j hl0.le hl1.le k)
      (cubeLaminate_eq_zero a j hl0.le hl1.le k)
      ((hint (cubeLaminate a j l k)).congr (hae.mono fun x hx => hx.symm))
    rwa [rd_volume_unitCube, ENNReal.toReal_one, one_mul, integral_congr_ae hae] at this
  -- the energy of `u_k`
  have hu : ∀ k : ℕ, 0 < k → ∫ x in unitCube m, f' (F + grad (sawLaminate a j l k) x) = E := by
    intro k hk
    have h1 : f' (F + (1 - l) • A₀) = f (F + (1 - l) • A₀) := Set.indicator_of_mem hT1 f
    have h2 : f' (F - l • A₀) = f (F - l • A₀) := Set.indicator_of_mem hT2 f
    rw [setIntegral_sawLaminate f' F a j hl0 hl1 hk]
    change l * f' (F + (1 - l) • A₀) + (1 - l) * f' (F - l • A₀) = E
    rw [h1, h2]
  -- the two energies differ by at most `2 C |{∇v_k ≠ ∇u_k}|`
  have hdiff : ∀ k : ℕ, 0 < k → f F ≤ E + 2 * C * volume.real {x ∈ unitCube m |
      grad (cubeLaminate a j l k) x ≠ grad (sawLaminate a j l k) x} := by
    intro k hk
    set B := {x ∈ unitCube m | grad (cubeLaminate a j l k) x ≠ grad (sawLaminate a j l k) x}
    have hBQ : B ⊆ unitCube m := fun x hx => hx.1
    have hB : volume B < ⊤ := (measure_mono hBQ).trans_lt hQfin
    have e1 : ∫ x in unitCube m, (f' (F + grad (cubeLaminate a j l k) x) -
        f' (F + grad (sawLaminate a j l k) x)) =
        ∫ x in B, (f' (F + grad (cubeLaminate a j l k) x) -
          f' (F + grad (sawLaminate a j l k) x)) := by
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQm hBQ ?_
      intro x ⟨hxQ, hxB⟩
      have : grad (cubeLaminate a j l k) x = grad (sawLaminate a j l k) x := by
        by_contra h
        exact hxB ⟨hxQ, h⟩
      rw [this, sub_self]
    have hbd : ∀ x ∈ B, ‖f' (F + grad (cubeLaminate a j l k) x) -
        f' (F + grad (sawLaminate a j l k) x)‖ ≤ 2 * C := by
      intro x _
      rw [Real.norm_eq_abs]
      refine (abs_sub _ _).trans ?_
      linarith [hC (F + grad (cubeLaminate a j l k) x), hC (F + grad (sawLaminate a j l k) x)]
    have e2 := norm_setIntegral_le_of_norm_le_const hB hbd
    rw [← e1, integral_sub (hint _) (hint _), hu k hk, Real.norm_eq_abs] at e2
    have h3 := (abs_le.1 e2).2
    have h4 := hv k hk
    linarith
  -- pass to the limit
  have hlim : Tendsto (fun k : ℕ => E + 2 * C * volume.real {x ∈ unitCube m |
      grad (cubeLaminate a j l k) x ≠ grad (sawLaminate a j l k) x}) atTop
      (𝓝 (E + 2 * C * 0)) := by
    refine tendsto_const_nhds.add (tendsto_const_nhds.mul ?_)
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_volume_grad_cubeLaminate_ne a j hl0.le hl1.le)
    rw [ENNReal.toReal_zero] at this
    exact this
  rw [mul_zero, add_zero] at hlim
  exact ge_of_tendsto hlim ((eventually_gt_atTop 0).mono hdiff)

/-! ### The cube with faces orthogonal to a given direction -/

/-- For `Rᵀ R = 1`, the image of a set under `x ↦ R x` is its preimage under `y ↦ Rᵀ y`. -/
private lemma lam_image_mulVec_eq_preimage {R : Matrix (Fin m) (Fin m) ℝ} (hR : Rᵀ * R = 1)
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
private lemma lam_measurePreserving_mulVec {R : Matrix (Fin m) (Fin m) ℝ} (hR : Rᵀ * R = 1) :
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

/-- **The two-point inequality on a rotated cube.** For an orthogonal matrix `R` (`Rᵀ R = 1`), if
`f` is quasiconvex at `F` on the cube `R Q`, whose faces are orthogonal to the columns of `R`,
then the two-point inequality holds in the direction `a ⊗ R e_j`. The test maps are
`x ↦ v_k (Rᵀ x)`, with gradients `∇v_k (Rᵀ x) Rᵀ`, and `x ↦ R x` preserves the volume: `g (X) =
f (X Rᵀ)` is quasiconvex at `F R` on `Q`, and `le_of_quasiconvexAtOn_unitCube` applies to it, with
`(a ⊗ e_j) Rᵀ = a ⊗ R e_j`. -/
theorem le_of_quasiconvexAtOn_orthogonal {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    {F : Matrix (Fin d) (Fin m) ℝ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : Rᵀ * R = 1)
    (hf : QuasiconvexAtOn ((fun x => R.mulVec x) '' unitCube m) f F) (a : Fin d → ℝ)
    (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) :
    f F ≤ l * f (F + (1 - l) • Matrix.vecMulVec a (R.mulVec (Pi.single j 1))) +
      (1 - l) * f (F - l • Matrix.vecMulVec a (R.mulVec (Pi.single j 1))) := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.1 hR
  set g : Matrix (Fin d) (Fin m) ℝ → ℝ := fun X => f (X * Rᵀ)
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
  have hmp := lam_measurePreserving_mulVec hR
  have hme : MeasurableEmbedding (fun x : Fin m → ℝ => R.mulVec x) :=
    L.symm.toHomeomorph.measurableEmbedding
  have hvol : volume ((fun x => R.mulVec x) '' unitCube m) = volume (unitCube m) := by
    have := hme.map_apply volume ((fun x => R.mulVec x) '' unitCube m)
    rwa [hmp.map_eq, hme.injective.preimage_image] at this
  -- `g` is quasiconvex at `F R` on the unit cube
  have hg : QuasiconvexAtOn (unitCube m) g (F * R) := by
    intro φ K hφ hφ0 hint
    set ψ : (Fin m → ℝ) → Fin d → ℝ := φ ∘ L
    have hψ : LipschitzWith (K * ‖(L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ))‖₊) ψ :=
      hφ.comp (L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)).lipschitzWith
    have hψ0 : ∀ y ∉ (fun x => R.mulVec x) '' unitCube m, ψ y = 0 := by
      intro y hy
      rw [lam_image_mulVec_eq_preimage hR] at hy
      exact hφ0 _ hy
    have hgrad : ∀ y, grad ψ y = grad φ (Rᵀ.mulVec y) * Rᵀ := by
      intro y
      ext i k
      simp only [grad, Matrix.of_apply, Matrix.mul_apply]
      have e : (fun z => ψ z i) = (fun w => φ w i) ∘ L := rfl
      rw [e, L.comp_right_fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hL]
      rw [Matrix.mulVec_single_one]
      conv_lhs => rw [← Finset.univ_sum_single (Rᵀ.col k)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [show Pi.single k' (Rᵀ.col k k') = Rᵀ.col k k' • (Pi.single k' 1 : Fin m → ℝ) by
        rw [← Pi.single_smul', smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]
      rfl
    have hcomp : ∀ x, f (F + grad ψ (R.mulVec x)) = g (F * R + grad φ x) := by
      intro x
      rw [hgrad, Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
      simp only [g, Matrix.add_mul, Matrix.mul_assoc, hR', Matrix.mul_one]
    have hint' :
        IntegrableOn (fun y => f (F + grad ψ y)) ((fun x => R.mulVec x) '' unitCube m) := by
      rw [hmp.integrableOn_image hme]
      simpa only [Function.comp_def, hcomp] using hint
    have key := hf ψ _ hψ hψ0 hint'
    rw [hmp.setIntegral_image_emb hme, hvol] at key
    simpa only [hcomp, g, Matrix.mul_assoc, hR', Matrix.mul_one] using key
  have := le_of_quasiconvexAtOn_unitCube hg a j hl0 hl1
  simp only [g, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, hR', Matrix.mul_one,
    Matrix.smul_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose] at this
  exact this

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
  -- the rotated cube is a bounded open nonempty set
  have hQo : IsOpen (unitCube m) := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
  have hcont : Continuous (fun x : Fin m → ℝ => R.mulVec x) :=
    continuous_const.matrix_mulVec continuous_id
  have hopen : IsOpen ((fun x => R.mulVec x) '' unitCube m) := by
    rw [lam_image_mulVec_eq_preimage hR]
    exact hQo.preimage (continuous_const.matrix_mulVec continuous_id)
  have hbd : Bornology.IsBounded ((fun x => R.mulVec x) '' unitCube m) :=
    ((isCompact_Icc (a := (0 : Fin m → ℝ)) (b := 1)).image hcont).isBounded.subset
      (image_mono fun x hx => ⟨fun i => (hx i (mem_univ i)).1.le,
        fun i => (hx i (mem_univ i)).2.le⟩)
  have hne : ((fun x => R.mulVec x) '' unitCube m).Nonempty :=
    ⟨_, mem_image_of_mem _ (show (fun _ => (1 / 2 : ℝ)) ∈ unitCube m from
      fun _ _ => ⟨by norm_num, by norm_num⟩)⟩
  have hU := (quasiconvexAtOn_iff hlsc hbdd F hopen hbd hne).1 hf
  have := le_of_quasiconvexAtOn_orthogonal hR hU (r • a) j hl0 hl1
  rwa [hRj, Matrix.smul_vecMulVec, ← Matrix.vecMulVec_smul, smul_smul, mul_inv_cancel₀ hr.ne',
    one_smul] at this

end CalculusOfVariations
