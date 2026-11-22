/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Envelope.Cube
public import CalculusOfVariations.Lipschitz.Cutoff
public import CalculusOfVariations.Lipschitz.Rescale
public import CalculusOfVariations.Covering.Cubes

/-!
# Gluing rescaled test maps into small cubes

`cv_glue_on`: take finitely many disjoint closed cubes `closedBall x_p r_p` (sup norm) in a set
`Ω` of finite measure, a Lipschitz `φ` vanishing off `Ω` and `δ r_p`-close to its tangent map on
each cube, and test maps `ψ_p` on the unit cube. Replacing `φ` in each cube by its tangent map,
glued to `φ` by a cut-off, plus the rescaled copy of `ψ_p` in the inner cube
`ball x_p ((1 - δ) r_p)`, gives a Lipschitz map vanishing off `Ω` whose energy is at most the sum
of the energies of the copies plus `M` times the measure of the rest (`cv_glue` on the unit cube).

Where `φ` is affine on each cube, as in all uses in this package, `φ` is its own tangent map
there, the cut-off changes nothing, and the glued map is `φ` plus the rescaled copies: with
`φ = 0` for the covering step of the independence of the domain (`env_iInf_le_cubeInf`,
`Envelope.Formula`), and with a piecewise affine `φ` for the inequality (4.28) of S. Müller's
lecture notes (`cubeInf_le_sum_of_piecewiseAffine`, `Envelope.Glue`).

Also: `cv_ereal_le_of_eps` (an `EReal` below `b + C ε` for all small `ε` is below `b`), and the
volumes of sup-norm balls.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

namespace CalculusOfVariations

variable {d m : ℕ}

/-! ### The local modification near a point of differentiability -/

/-- The tangent map of `φ` at `x`. -/
noncomputable def tangentMap (φ : (Fin m → ℝ) → Fin d → ℝ) (x : Fin m → ℝ) :
    (Fin m → ℝ) → Fin d → ℝ :=
  fun z => φ x + fderiv ℝ φ x (z - x)

/-- The corner of the cube `ball x ρ` (sup norm): `ball x ρ = c + 2ρ (0,1)^m`. -/
def ballCorner (x : Fin m → ℝ) (ρ : ℝ) : Fin m → ℝ := x - fun _ => ρ

/-- The modification of `φ` in `ball x r`: the tangent map glued to `φ` by the cut-off, plus a
rescaled copy of `ψ` in `ball x ((1 - δ) r)`. -/
noncomputable def gluedPiece (φ ψ : (Fin m → ℝ) → Fin d → ℝ) (x : Fin m → ℝ) (r δ : ℝ) :
    (Fin m → ℝ) → Fin d → ℝ :=
  fun z => ballCutoff x r δ z • (tangentMap φ x z - φ z) +
    rescaleMap ψ (ballCorner x ((1 - δ) * r)) (2 * ((1 - δ) * r)) z

theorem cv_ball_eq_preimage (x : Fin m → ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ball x ρ = {y | (2 * ρ)⁻¹ • (y - ballCorner x ρ) ∈ unitCube m} := by
  ext y
  simp only [mem_ball, dist_pi_lt_iff hρ, Real.dist_eq, abs_sub_lt_iff, mem_ofPred_eq, unitCube,
    Set.mem_pi, mem_univ, true_implies, mem_Ioo, ballCorner, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul]
  refine forall_congr' fun i => ?_
  have h2 : 0 < 2 * ρ := by positivity
  constructor
  · rintro ⟨h1, h1'⟩
    constructor
    · exact mul_pos (inv_pos.2 h2) (by linarith)
    · rw [inv_mul_lt_iff₀ h2]; linarith
  · rintro ⟨h1, h1'⟩
    have h1 := (mul_pos_iff_of_pos_left (inv_pos.2 h2)).1 h1
    rw [inv_mul_lt_iff₀ h2] at h1'
    constructor <;> linarith

theorem tangentMap_lipschitz {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    (x : Fin m → ℝ) : LipschitzWith K (tangentMap φ x) := by
  have hD : ‖fderiv ℝ φ x‖ ≤ K := norm_fderiv_le_of_lipschitz ℝ hφ (x₀ := x)
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [dist_eq_norm, dist_eq_norm, tangentMap, tangentMap, add_sub_add_left_eq_sub, ← map_sub,
    sub_sub_sub_cancel_right]
  exact ((fderiv ℝ φ x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))

theorem tangentMap_grad {φ : (Fin m → ℝ) → Fin d → ℝ} {x : Fin m → ℝ} (hφ : DifferentiableAt ℝ φ x)
    (y : Fin m → ℝ) : grad (tangentMap φ x) y = grad φ x := by
  ext i k
  change fderiv ℝ (fun z => (φ x + fderiv ℝ φ x (z - x)) i) y (Pi.single k 1) =
    fderiv ℝ (fun z => φ z i) x (Pi.single k 1)
  have h1 : HasFDerivAt (fun z => (φ x + fderiv ℝ φ x (z - x)) i)
      ((ContinuousLinearMap.proj i).comp (fderiv ℝ φ x)) y := by
    have : HasFDerivAt (fun z => φ x + fderiv ℝ φ x (z - x)) (fderiv ℝ φ x) y := by
      have := ((fderiv ℝ φ x).hasFDerivAt (x := y - x)).comp y ((hasFDerivAt_id y).sub_const x)
      simpa using this.const_add (φ x)
    exact (hasFDerivAt_apply i _).comp y this
  have h2 : HasFDerivAt (fun z => φ z i) ((ContinuousLinearMap.proj i).comp (fderiv ℝ φ x)) x :=
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin d => ℝ) i (φ x)).comp x hφ.hasFDerivAt
  rw [h1.fderiv, h2.fderiv]

section Piece

variable {φ ψ : (Fin m → ℝ) → Fin d → ℝ} {x : Fin m → ℝ} {r δ : ℝ}

theorem rescaleMap_eq_zero_of_notMem_ball (hψ : ∀ y ∉ unitCube m, ψ y = 0) {ρ : ℝ} (hρ : 0 < ρ)
    {z : Fin m → ℝ} (hz : z ∉ ball x ρ) : rescaleMap ψ (ballCorner x ρ) (2 * ρ) z = 0 := by
  refine rescaleMap_eq_zero hψ _ _ ?_
  rw [cv_ball_eq_preimage x hρ] at hz
  exact hz

theorem gluedPiece_eq_zero (hr : 0 < r) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hψ : ∀ y ∉ unitCube m, ψ y = 0) {z : Fin m → ℝ} (hz : z ∉ ball x r) :
    gluedPiece φ ψ x r δ z = 0 := by
  have hz' : r ≤ ‖z - x‖ := by rw [mem_ball, dist_eq_norm, not_lt] at hz; exact hz
  have hρ : 0 < (1 - δ) * r := mul_pos (by linarith) hr
  have hzρ : z ∉ ball x ((1 - δ) * r) := fun h =>
    hz (ball_subset_ball (by nlinarith) h)
  simp only [gluedPiece, ballCutoff_eq_zero hr hδ0 hz', zero_smul, zero_add,
    rescaleMap_eq_zero_of_notMem_ball hψ hρ hzρ]

/-- The glued map near `x`, without the inserted copy of `ψ`, is `(3K+1)`-Lipschitz. -/
theorem cv_cut_lipschitz {K : NNReal} (hφ : LipschitzWith K φ) (hr : 0 < r) (hδ0 : 0 < δ)
    (happrox : ∀ z ∈ closedBall x r, ‖φ z - tangentMap φ x z‖ ≤ δ * r) :
    LipschitzWith (K + (K + K + (1 / (δ * r)).toNNReal * (δ * r).toNNReal))
      fun z => φ z + ballCutoff x r δ z • (tangentMap φ x z - φ z) := by
  refine hφ.add (cv_lipschitz_smul (S := closedBall x r) (ballCutoff_lipschitz x hr hδ0)
    (ballCutoff_nonneg x r δ) (ballCutoff_le_one x r δ) (fun y hy => ?_)
        ((tangentMap_lipschitz hφ x).sub hφ)
    (fun y hy => ?_) (by positivity))
  · refine ballCutoff_eq_zero hr hδ0 ?_
    rw [mem_closedBall, dist_eq_norm, not_le] at hy
    exact hy.le
  · rw [norm_sub_rev]; exact happrox y hy

theorem cv_cut_lipschitz_const {K : NNReal} (hr : 0 < r) (hδ0 : 0 < δ) :
    ((K + (K + K + (1 / (δ * r)).toNNReal * (δ * r).toNNReal) : NNReal) : ℝ) = 3 * K + 1 := by
  push_cast
  rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
  field_simp
  ring

theorem gluedPiece_lipschitz {K K' : NNReal} (hφ : LipschitzWith K φ) (hψ : LipschitzWith K' ψ)
    (hr : 0 < r) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (happrox : ∀ z ∈ closedBall x r, ‖φ z - tangentMap φ x z‖ ≤ δ * r) :
    ∃ C, LipschitzWith C (gluedPiece φ ψ x r δ) := by
  have hρ : 0 < 2 * ((1 - δ) * r) := by have := mul_pos (by linarith : (0 : ℝ) < 1 - δ) hr; linarith
  refine ⟨_, (cv_lipschitz_smul (S := closedBall x r) (B := δ * r) (ballCutoff_lipschitz x hr hδ0)
    (ballCutoff_nonneg x r δ) (ballCutoff_le_one x r δ) (fun y hy => ?_)
        ((tangentMap_lipschitz hφ x).sub hφ)
    (fun y hy => ?_) (by positivity)).add (rescaleMap_lipschitz hψ _ hρ)⟩
  · refine ballCutoff_eq_zero hr hδ0 ?_
    rw [mem_closedBall, dist_eq_norm, not_le] at hy
    exact hy.le
  · rw [norm_sub_rev]; exact happrox y hy

/-- In the inner cube, the glued map is the tangent map plus the copy of `ψ`. -/
theorem gluedPiece_eventually_inner (hr : 0 < r) (hδ0 : 0 < δ) {z : Fin m → ℝ}
    (hz : z ∈ ball x ((1 - δ) * r)) :
    (fun y => φ y + gluedPiece φ ψ x r δ y) =ᶠ[𝓝 z]
      fun y => tangentMap φ x y + rescaleMap ψ (ballCorner x ((1 - δ) * r))
          (2 * ((1 - δ) * r)) y := by
  filter_upwards [isOpen_ball.mem_nhds hz] with y hy
  have : ballCutoff x r δ y = 1 := by
    refine ballCutoff_eq_one hr hδ0 ?_
    rw [mem_ball, dist_eq_norm] at hy
    exact hy.le
  simp only [gluedPiece, this, one_smul]
  abel

/-- Outside the inner cube, the glued map does not see the copy of `ψ`. -/
theorem gluedPiece_eventually_outer (hψ : ∀ y ∉ unitCube m, ψ y = 0) (hr : 0 < r) (hδ1 : δ < 1)
    {z : Fin m → ℝ} (hz : z ∉ closedBall x ((1 - δ) * r)) :
    (fun y => φ y + gluedPiece φ ψ x r δ y) =ᶠ[𝓝 z]
      fun y => φ y + ballCutoff x r δ y • (tangentMap φ x y - φ y) := by
  have hρ : 0 < (1 - δ) * r := mul_pos (by linarith) hr
  filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hz] with y hy
  have : y ∉ ball x ((1 - δ) * r) := fun h => hy (ball_subset_closedBall h)
  simp only [gluedPiece, rescaleMap_eq_zero_of_notMem_ball hψ hρ this, add_zero]

end Piece

theorem cv_finsum_lipschitz {ι : Type*} (t : Finset ι) (g : ι → (Fin m → ℝ) → Fin d → ℝ)
    (hg : ∀ p ∈ t, ∃ C, LipschitzWith C (g p)) :
    ∃ C, LipschitzWith C fun z => ∑ p ∈ t, g p z := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a t ha ih =>
    obtain ⟨C1, h1⟩ := hg a (Finset.mem_insert_self _ _)
    obtain ⟨C2, h2⟩ := ih fun p hp => hg p (Finset.mem_insert_of_mem hp)
    refine ⟨C1 + C2, ?_⟩
    simpa [Finset.sum_insert ha] using h1.add h2

theorem cv_volume_sphere (x : Fin m → ℝ) {ρ : ℝ} (hρ : 0 < ρ) : volume (sphere x ρ) = 0 := by
  rw [← frontier_ball x hρ.ne']
  exact Convex.addHaar_frontier volume (convex_ball x ρ)

/-- **Gluing.** Finitely many disjoint cubes `closedBall x_p r_p` in the unit cube, around points
where `φ` is differentiable and `δ r_p`-close to its tangent map: replacing `φ` in each cube by the
tangent map glued to `φ` by a cut-off, plus a rescaled copy of a test map `ψ_p` in the inner cube
`ball x_p ((1 - δ) r_p)`, gives a test map whose energy is at most the sum of the energies of the
copies plus `M` times the measure of the rest. -/
theorem cv_glue_on {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) {Ω : Set (Fin m → ℝ)} (hΩ : volume Ω ≠ ⊤)
    (hφQ : ∀ x ∉ Ω, φ x = 0) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (t : Finset ((Fin m → ℝ) × ℝ))
    (ht : ∀ p ∈ t, 0 < p.2 ∧ closedBall p.1 p.2 ⊆ Ω ∧ DifferentiableAt ℝ φ p.1 ∧
      ∀ z ∈ closedBall p.1 p.2, ‖φ z - tangentMap φ p.1 z‖ ≤ δ * p.2)
    (hdisj : (t : Set ((Fin m → ℝ) × ℝ)).PairwiseDisjoint fun p => closedBall p.1 p.2)
    (ψ : (Fin m → ℝ) × ℝ → (Fin m → ℝ) → Fin d → ℝ) (hψ : ∀ p ∈ t, IsCubeTestMap (ψ p)) {M : ℝ}
    (hM : ∀ X : Matrix (Fin d) (Fin m) ℝ, (∀ i k, |X i k| ≤ 3 * K + 1) → |f (A + X)| ≤ M) :
    ∃ Φ, ((∃ C, LipschitzWith C Φ) ∧ ∀ x ∉ Ω, Φ x = 0) ∧ ∫ x in Ω, f (A + grad Φ x) ≤
      (∑ p ∈ t, (2 * ((1 - δ) * p.2)) ^ m *
        ∫ y in unitCube m, f (A + grad φ p.1 + grad (ψ p) y)) +
      M * volume.real (Ω \ ⋃ p ∈ t, ball p.1 ((1 - δ) * p.2)) := by
  classical
  set Φ : (Fin m → ℝ) → Fin d → ℝ := fun z => φ z + ∑ p ∈ t, gluedPiece φ (ψ p) p.1 p.2 δ z
    with hΦ
  have hpiece0 : ∀ q ∈ t, ∀ z, z ∉ closedBall q.1 q.2 →
      ∀ᶠ y in 𝓝 z, gluedPiece φ (ψ q) q.1 q.2 δ y = 0 := by
    intro q hq z hz
    filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hz] with y hy
    exact gluedPiece_eq_zero (ht q hq).1 hδ0 hδ1 (hψ q hq).2
        (fun h => hy (ball_subset_closedBall h))
  have hloc : ∀ p ∈ t, ∀ z ∈ closedBall p.1 p.2,
      Φ =ᶠ[𝓝 z] fun y => φ y + gluedPiece φ (ψ p) p.1 p.2 δ y := by
    intro p hp z hz
    have h : ∀ q ∈ t.erase p, ∀ᶠ y in 𝓝 z, gluedPiece φ (ψ q) q.1 q.2 δ y = 0 := by
      intro q hq
      have hq' := Finset.mem_of_mem_erase hq
      refine hpiece0 q hq' z fun h => ?_
      exact Set.disjoint_left.1 (hdisj hq' hp (Finset.ne_of_mem_erase hq)) h hz
    filter_upwards [(Filter.eventually_all_finset _).2 h] with y hy
    simp only [hΦ]
    rw [← Finset.add_sum_erase t _ hp, Finset.sum_eq_zero hy, add_zero]
  have hout : ∀ z, (∀ p ∈ t, z ∉ closedBall p.1 p.2) → Φ =ᶠ[𝓝 z] φ := by
    intro z hz
    filter_upwards [(Filter.eventually_all_finset t).2 fun q hq => hpiece0 q hq z (hz q hq)]
      with y hy
    simp only [hΦ, Finset.sum_eq_zero hy, add_zero]
  -- `Φ` is a test map
  have hΦlip : ∃ C, LipschitzWith C Φ := by
    obtain ⟨C, hC⟩ := cv_finsum_lipschitz t (fun p => gluedPiece φ (ψ p) p.1 p.2 δ) fun p hp => by
      obtain ⟨⟨K', hK'⟩, -⟩ := hψ p hp
      exact gluedPiece_lipschitz hφ hK' (ht p hp).1 hδ0 hδ1 (ht p hp).2.2.2
    exact ⟨K + C, hφ.add hC⟩
  have hΦQ : ∀ x ∉ Ω, Φ x = 0 := by
    intro x hx
    simp only [hΦ, hφQ x hx, zero_add]
    refine Finset.sum_eq_zero fun p hp => ?_
    exact gluedPiece_eq_zero (ht p hp).1 hδ0 hδ1 (hψ p hp).2
      (fun h => hx ((ht p hp).2.1 (ball_subset_closedBall h)))
  refine ⟨Φ, ⟨hΦlip, hΦQ⟩, ?_⟩
  obtain ⟨CΦ, hCΦ⟩ := hΦlip
  set U := ⋃ p ∈ t, ball p.1 ((1 - δ) * p.2) with hU
  have hUQ : U ⊆ Ω := by
    intro z hz
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hz
    have h1 : (1 - δ) * p.2 ≤ p.2 := by nlinarith [(ht p hp).1]
    exact (ht p hp).2.1 (ball_subset_closedBall (ball_subset_ball h1 hzp))
  have hint : IntegrableOn (fun x => f (A + grad Φ x)) Ω := cv_integrableOn hf A hCΦ hΩ
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion _ fun _ _ => measurableSet_ball
  rw [← integral_inter_add_sdiff hUm hint, inter_eq_right.2 hUQ,
    integral_biUnion_finset t (fun p _ => measurableSet_ball) (fun p hp q hq hpq => by
      have h1 : (1 - δ) * p.2 ≤ p.2 := by nlinarith [(ht p hp).1]
      have h2 : (1 - δ) * q.2 ≤ q.2 := by nlinarith [(ht q hq).1]
      exact (hdisj hp hq hpq).mono (ball_subset_closedBall.trans (closedBall_subset_closedBall h1))
        (ball_subset_closedBall.trans (closedBall_subset_closedBall h2)))
    (fun p hp => hint.mono_set (hUQ.trans' (subset_biUnion_of_mem (u := fun p =>
      ball p.1 ((1 - δ) * p.2)) hp)))]
  apply add_le_add
  · -- the inner cubes
    refine le_of_eq (Finset.sum_congr rfl fun p hp => ?_)
    obtain ⟨hr, -, hdiff, happrox⟩ := ht p hp
    obtain ⟨⟨Kψ, hKψ⟩, hψQ⟩ := hψ p hp
    have hρ : 0 < (1 - δ) * p.2 := mul_pos (by linarith) hr
    have h2ρ : 0 < 2 * ((1 - δ) * p.2) := by linarith
    set c := ballCorner p.1 ((1 - δ) * p.2)
    set Ψ := rescaleMap (ψ p) c (2 * ((1 - δ) * p.2))
    have hΨlip : LipschitzWith Kψ Ψ := rescaleMap_lipschitz hKψ c h2ρ
    have hae : ∀ᵐ z, z ∈ ball p.1 ((1 - δ) * p.2) → f (A + grad Φ z) =
        (fun y => f (A + grad φ p.1 + grad (ψ p) y)) ((2 * ((1 - δ) * p.2))⁻¹ • (z - c)) := by
      filter_upwards [hΨlip.ae_differentiableAt (μ := volume)] with z hzd hz
      have e1 := (hloc p hp z (ball_subset_closedBall (ball_subset_ball (by nlinarith) hz))).trans
        (gluedPiece_eventually_inner (ψ := ψ p) hr hδ0 hz)
      rw [cv_grad_congr e1]
      have hTd : DifferentiableAt ℝ (tangentMap φ p.1) z := by
        have : DifferentiableAt ℝ (fun y => φ p.1 + fderiv ℝ φ p.1 (y - p.1)) z :=
          ((fderiv ℝ φ p.1).differentiableAt.comp z (differentiableAt_id.sub_const _)).const_add _
        exact this
      rw [show (fun y => tangentMap φ p.1 y + Ψ y) = tangentMap φ p.1 + Ψ from rfl,
        cv_grad_add hTd hzd, tangentMap_grad hdiff, rescaleMap_grad _ _ h2ρ.ne', add_assoc]
    rw [setIntegral_congr_ae measurableSet_ball hae, ← integral_indicator measurableSet_ball,
      ← integral_indicator cv_measurableSet_unitCube]
    have hind : (ball p.1 ((1 - δ) * p.2)).indicator (fun z =>
        (fun y => f (A + grad φ p.1 + grad (ψ p) y)) ((2 * ((1 - δ) * p.2))⁻¹ • (z - c))) =
        fun z => (unitCube m).indicator (fun y => f (A + grad φ p.1 + grad (ψ p) y))
          ((2 * ((1 - δ) * p.2))⁻¹ • (z - c)) := by
      ext z
      simp only [Set.indicator, cv_ball_eq_preimage p.1 hρ, mem_ofPred_eq]
      rfl
    rw [hind, cv_integral_comp_affine _ c h2ρ]
  · -- the rest: the gradient is bounded there
    have hfin : volume (Ω \ U) < ⊤ := (measure_mono sdiff_subset).trans_lt hΩ.lt_top
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const_ae' hfin ?_
    have hnull : ∀ᵐ z : Fin m → ℝ, ∀ p ∈ t,
        z ∉ sphere p.1 ((1 - δ) * p.2) ∧ z ∉ sphere p.1 p.2 := by
      refine (Filter.eventually_all_finset t).2 fun p hp => ?_
      have hr := (ht p hp).1
      have hρ : 0 < (1 - δ) * p.2 := mul_pos (by linarith) hr
      exact (measure_eq_zero_iff_ae_notMem.1 (cv_volume_sphere p.1 hρ)).and
        (measure_eq_zero_iff_ae_notMem.1 (cv_volume_sphere p.1 hr))
    filter_upwards [hnull] with z hz hzQU
    rw [Real.norm_eq_abs]
    refine hM _ fun i k => ?_
    have hzU : z ∉ U := hzQU.2
    by_cases hzin : ∃ p ∈ t, z ∈ ball p.1 p.2
    · obtain ⟨p, hp, hzp⟩ := hzin
      obtain ⟨hr, -, -, happrox⟩ := ht p hp
      have hzρ : z ∉ closedBall p.1 ((1 - δ) * p.2) := by
        rw [← ball_union_sphere]
        rintro (h | h)
        · exact hzU (mem_iUnion₂.2 ⟨p, hp, h⟩)
        · exact (hz p hp).1 h
      have e := (hloc p hp z (ball_subset_closedBall hzp)).trans
        (gluedPiece_eventually_outer (hψ p hp).2 hr hδ1 hzρ)
      rw [cv_grad_congr e]
      have := cv_grad_abs_le (cv_cut_lipschitz hφ hr hδ0 happrox) z i k
      rwa [cv_cut_lipschitz_const hr hδ0] at this
    · push Not at hzin
      have hcl : ∀ p ∈ t, z ∉ closedBall p.1 p.2 := by
        intro p hp h
        rw [← ball_union_sphere] at h
        rcases h with h | h
        · exact hzin p hp h
        · exact (hz p hp).2 h
      rw [cv_grad_congr (hout z hcl)]
      have := cv_grad_abs_le hφ z i k
      have hK : (0 : ℝ) ≤ K := K.2
      linarith

/-- `cv_glue_on` in the unit cube. -/
theorem cv_glue {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) (hφQ : ∀ x ∉ unitCube m, φ x = 0) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (t : Finset ((Fin m → ℝ) × ℝ))
    (ht : ∀ p ∈ t, 0 < p.2 ∧ closedBall p.1 p.2 ⊆ unitCube m ∧ DifferentiableAt ℝ φ p.1 ∧
      ∀ z ∈ closedBall p.1 p.2, ‖φ z - tangentMap φ p.1 z‖ ≤ δ * p.2)
    (hdisj : (t : Set ((Fin m → ℝ) × ℝ)).PairwiseDisjoint fun p => closedBall p.1 p.2)
    (ψ : (Fin m → ℝ) × ℝ → (Fin m → ℝ) → Fin d → ℝ) (hψ : ∀ p ∈ t, IsCubeTestMap (ψ p)) {M : ℝ}
    (hM : ∀ X : Matrix (Fin d) (Fin m) ℝ, (∀ i k, |X i k| ≤ 3 * K + 1) → |f (A + X)| ≤ M) :
    ∃ Φ, IsCubeTestMap Φ ∧ ∫ x in unitCube m, f (A + grad Φ x) ≤
      (∑ p ∈ t, (2 * ((1 - δ) * p.2)) ^ m *
        ∫ y in unitCube m, f (A + grad φ p.1 + grad (ψ p) y)) +
      M * volume.real (unitCube m \ ⋃ p ∈ t, ball p.1 ((1 - δ) * p.2)) :=
  cv_glue_on hf A hφ (by rw [cv_volume_unitCube]; exact ENNReal.one_ne_top) hφQ hδ0 hδ1 t ht
    hdisj ψ hψ hM

/-! ### Auxiliary estimates -/

/-- An `EReal` bounded by `b + C ε` for all small `ε > 0` is bounded by `b`. -/
theorem cv_ereal_le_of_eps {a : EReal} {b C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → a ≤ ((b + C * ε : ℝ) : EReal)) : a ≤ (b : EReal) := by
  induction a using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd (h (1 / 4) (by norm_num) (by norm_num)) (not_le.2 (EReal.coe_lt_top _))
  | coe a =>
    rw [EReal.coe_le_coe_iff]
    by_contra hab
    push Not at hab
    set ε := min (1 / 4) ((a - b) / (2 * (C + 1))) with hε
    have hε0 : 0 < ε := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
    have hε1 : ε < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
    have h1 := h ε hε0 hε1
    rw [EReal.coe_le_coe_iff] at h1
    have h2 : ε ≤ (a - b) / (2 * (C + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h2
    nlinarith

theorem cv_measureReal_closedBall (x : Fin m → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (closedBall x r) = (2 * r) ^ m := by
  rw [measureReal_def, Real.volume_pi_closedBall x hr, Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]

theorem cv_measureReal_ball (x : Fin m → ℝ) {r : ℝ} (hr : 0 < r) :
    volume.real (ball x r) = (2 * r) ^ m := by
  rw [measureReal_def, Real.volume_pi_ball x hr, Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]

end CalculusOfVariations
