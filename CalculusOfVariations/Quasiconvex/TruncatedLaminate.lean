/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Quasiconvex.Laminate

/-!
# Truncated laminates: the two-point inequality without regularity

On the unit cube the two-point inequality
`f (F) ≤ λ f (F + (1 − λ) a ⊗ e_j) + (1 − λ) f (F − λ a ⊗ e_j)` holds for every `f` that is
quasiconvex at `F`, without any regularity of `f` (`le_of_quasiconvexAtOn_unitCube`), and likewise
on a rotated cube `R Q`, in the direction `a ⊗ R e_j` (`le_of_quasiconvexAtOn_orthogonal`).
(`le_of_quasiconvexAtOn_vecMulVec` of `Quasiconvex.Laminate`, which cuts the laminates off by
multiplication, needs `f` Borel and locally bounded: its test maps have infinitely
many gradients.)

The argument is the proof of S. Müller, *Variational models for microstructure and phase
transitions*, lecture notes, MPI MiS Leipzig, 1998, Lemma 4.3: the laminate is truncated instead of
cut off, so that its gradients take finitely many values. On the unit cube `Q = (0, 1)^m`, with
`h = rd_saw λ`, let `u_k (x) = k⁻¹ h (k x_j) a` (`sawLaminate`) and
`v_k (x) = min (k⁻¹ h (k x_j), dist_∞ (x, ∂Q)) a` (`cubeLaminate`). Then `v_k` is Lipschitz and
vanishes off `Q` (`cubeLaminate_lipschitz`, `cubeLaminate_eq_zero`);
`∇v_k ∈ {(1 − λ) a ⊗ e_j, −λ a ⊗ e_j} ∪ {± a ⊗ e_i}` almost everywhere on `Q`
(`ae_grad_cubeLaminate_mem`: on `Q` the distance is `min_i min (x_i, 1 − x_i)`, and at almost every
point the derivative of a minimum of Lipschitz functions is the derivative of a function attaining
it, by the vanishing of the gradient of a Lipschitz map almost everywhere on its zero set,
`rd_ae_fderiv_eq_zero`); `|{∇v_k ≠ ∇u_k}| → 0`, since the bad set lies in the boundary layer
`{x ∈ Q : dist_∞ (x, Qᶜ) ≤ 1/k}`, of measure at most `2m/k` (`lam_layer_measure`,
`tendsto_volume_grad_cubeLaminate_ne`); and the energy of `u_k` is the right-hand side
(`setIntegral_sawLaminate`). Quasiconvexity at `F`, tested with `v_k`, gives the inequality; no
regularity of `f` is used, since almost everywhere `f (F + ∇v_k)` and `f (F + ∇u_k)` take finitely
many values.
-/
@[expose] public section

open Metric Set MeasureTheory Filter Topology
open scoped Pointwise Matrix

namespace CalculusOfVariations

variable {d m : ℕ}

/-! ### The truncated laminate on the unit cube -/

/-- Müller's laminate `v_k (x) = min (k⁻¹ h_λ (k x_j), dist_∞ (x, ∂Q)) a` on the unit cube `Q`:
the distance is the sup-norm distance to the complement of `Q`, so `v_k` vanishes off `Q`. -/
noncomputable def cubeLaminate (a : Fin d → ℝ) (j : Fin m) (l : ℝ) (k : ℕ) (x : Fin m → ℝ) :
    Fin d → ℝ :=
  min ((k : ℝ)⁻¹ * rd_saw l (k * x j)) (infDist x (unitCube m)ᶜ) • a

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
theorem cubeLaminate_eq_zero (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (k : ℕ) :
    ∀ x ∉ unitCube m, cubeLaminate a j l k x = 0 := by
  intro x hx
  simp only [cubeLaminate]
  rw [infDist_zero_of_mem (mem_compl hx),
    min_eq_right (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg k)) (lam_saw_nonneg l _)), zero_smul]

/-! ### The gradient of `v_k` -/

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

/-! ### The two-point inequality -/

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
      (cubeLaminate_eq_zero a j k)
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

/-- **The two-point inequality on a rotated cube.** For an orthogonal matrix `R` (`Rᵀ R = 1`), if
`f` is quasiconvex at `F` on the cube `R Q`, whose faces are orthogonal to the columns of `R`,
then the two-point inequality holds in the direction `a ⊗ R e_j`: `X ↦ f (X Rᵀ)` is quasiconvex at
`F R` on `Q` (`quasiconvexAtOn_unitCube_comp_orthogonal`), and `le_of_quasiconvexAtOn_unitCube`
applies to it, with `(a ⊗ e_j) Rᵀ = a ⊗ R e_j`. -/
theorem le_of_quasiconvexAtOn_orthogonal {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    {F : Matrix (Fin d) (Fin m) ℝ} {R : Matrix (Fin m) (Fin m) ℝ} (hR : Rᵀ * R = 1)
    (hf : QuasiconvexAtOn ((fun x => R.mulVec x) '' unitCube m) f F) (a : Fin d → ℝ)
    (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) :
    f F ≤ l * f (F + (1 - l) • Matrix.vecMulVec a (R.mulVec (Pi.single j 1))) +
      (1 - l) * f (F - l • Matrix.vecMulVec a (R.mulVec (Pi.single j 1))) := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.1 hR
  have := le_of_quasiconvexAtOn_unitCube (quasiconvexAtOn_unitCube_comp_orthogonal hR hf) a j
    hl0 hl1
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, hR', Matrix.mul_one,
    Matrix.smul_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose] at this
  exact this

end CalculusOfVariations
