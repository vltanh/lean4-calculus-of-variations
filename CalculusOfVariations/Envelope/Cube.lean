/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Lipschitz.Gradient
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Covering.Differentiation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Data.EReal.Operations

/-!
# The infimum formula on the unit cube

For `f : ℝ^{d×m} → ℝ`, `cubeInf f A = inf_φ ∫_{(0,1)^m} f (A + ∇φ)` over the Lipschitz `φ` vanishing
outside the unit cube (`IsCubeTestMap`), with values in `EReal`. For continuous `f`: `cubeInf f ≤ f`
(`cubeInf_le`), and `cubeInf f` is upper semicontinuous (`cubeInf_usc`).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

namespace CalculusOfVariations

variable {d m : ℕ}

/-- The test maps on the unit cube: Lipschitz, vanishing outside `(0, 1)^m`. -/
def IsCubeTestMap (φ : (Fin m → ℝ) → Fin d → ℝ) : Prop :=
  (∃ K, LipschitzWith K φ) ∧ ∀ x ∉ unitCube m, φ x = 0

/-- The infimum formula on the unit cube. -/
noncomputable def cubeInf (f : Matrix (Fin d) (Fin m) ℝ → ℝ) (A : Matrix (Fin d) (Fin m) ℝ) :
    EReal :=
  ⨅ (φ : (Fin m → ℝ) → Fin d → ℝ) (_ : IsCubeTestMap φ),
    ((∫ x in unitCube m, f (A + grad φ x) : ℝ) : EReal)

/-! ### The unit cube -/

theorem cv_unitCube_eq_ball : unitCube m = ball (fun _ => (1 / 2 : ℝ)) (1 / 2) := by
  ext x
  simp only [unitCube, Set.mem_pi, mem_univ, true_implies, mem_Ioo, mem_ball, dist_pi_lt_iff
    (by norm_num : (0 : ℝ) < 1 / 2), Real.dist_eq, abs_sub_lt_iff]
  refine forall_congr' fun i => ?_
  constructor
  · intro h; constructor <;> linarith [h.1, h.2]
  · intro h; constructor <;> linarith [h.1, h.2]

theorem cv_isOpen_unitCube : IsOpen (unitCube m) := by
  rw [cv_unitCube_eq_ball]; exact isOpen_ball

theorem cv_measurableSet_unitCube : MeasurableSet (unitCube m) :=
  cv_isOpen_unitCube.measurableSet

theorem cv_volume_unitCube : volume (unitCube m) = 1 := by
  rw [unitCube, Real.volume_pi_Ioo]
  simp

theorem cv_unitCube_subset_closedBall :
    unitCube m ⊆ closedBall (fun _ => (1 / 2 : ℝ)) (1 / 2) := by
  rw [cv_unitCube_eq_ball]; exact ball_subset_closedBall

/-! ### Bounds and integrability -/

/-- A continuous `f` is bounded near `A`. -/
theorem cv_bdd {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) (R : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ X : Matrix (Fin d) (Fin m) ℝ, (∀ i k, |X i k| ≤ R) → |f (A + X)| ≤ M := by
  have hc : Continuous fun X : Fin d → Fin m → ℝ => f (A + Matrix.of X) :=
    hf.comp (continuous_const.add continuous_id)
  obtain ⟨C, hC⟩ :=
      (isCompact_closedBall (0 : Fin d → Fin m → ℝ) (max R 0)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun X hX => ?_⟩
  have hmem : (fun i k => X i k : Fin d → Fin m → ℝ) ∈ closedBall (0 : Fin d → Fin m → ℝ)
      (max R 0) := by
    rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (le_max_right _ _)]
    intro i
    rw [pi_norm_le_iff_of_nonneg (le_max_right _ _)]
    intro k
    rw [Real.norm_eq_abs]
    exact (hX i k).trans (le_max_left _ _)
  have := hC _ hmem
  rw [Real.norm_eq_abs] at this
  exact (le_of_eq (by rfl)).trans (this.trans (le_max_left _ _))

/-- `f (A + ∇φ)` is integrable on sets of finite measure for a Lipschitz `φ`. -/
theorem cv_integrableOn {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) {s : Set (Fin m → ℝ)} (hs : volume s ≠ ⊤) :
    IntegrableOn (fun x => f (A + grad φ x)) s := by
  obtain ⟨M, -, hM⟩ := cv_bdd hf A K
  refine Measure.integrableOn_of_bounded (M := M) hs ?_ ?_
  · exact (cv_measurable_comp_grad (cv_continuous_of hf).measurable A φ).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hM _ (cv_grad_abs_le hφ x)

/-- `cubeInf f ≤ f`, with the test map `0`. -/
theorem cubeInf_le {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (A : Matrix (Fin d) (Fin m) ℝ) :
    cubeInf f A ≤ f A := by
  have h0 : IsCubeTestMap (fun _ : Fin m → ℝ => (0 : Fin d → ℝ)) :=
    ⟨⟨0, LipschitzWith.const _⟩, fun _ _ => rfl⟩
  refine (iInf₂_le _ h0).trans ?_
  have hg : ∀ x, grad (fun _ : Fin m → ℝ => (0 : Fin d → ℝ)) x = 0 := fun x =>
    cv_grad_eq_zero (Filter.Eventually.of_forall fun _ => rfl)
  simp only [hg, add_zero, setIntegral_const, smul_eq_mul, Measure.real, cv_volume_unitCube,
    ENNReal.toReal_one, one_mul, le_refl]

/-- For a fixed test map, `A ↦ ∫_Q f (A + ∇φ)` is continuous. -/
theorem cv_continuous_integral {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ) :
    Continuous fun A : Matrix (Fin d) (Fin m) ℝ => ∫ x in unitCube m, f (A + grad φ x) := by
  -- continuity on `Fin d → Fin m → ℝ`, a first-countable space
  have hg : Continuous fun X : Fin d → Fin m → ℝ =>
      ∫ x in unitCube m, f (Matrix.of X + grad φ x) := by
    rw [continuous_iff_continuousAt]
    intro X₀
    obtain ⟨M, -, hM⟩ := cv_bdd hf (Matrix.of X₀) (K + 1)
    have hnhds : ∀ᶠ X in 𝓝 X₀, ∀ i k, |X i k - X₀ i k| ≤ 1 := by
      filter_upwards [closedBall_mem_nhds X₀ one_pos] with X hX i k
      rw [← Real.dist_eq]
      exact (dist_le_pi_dist (X i) (X₀ i) k).trans ((dist_le_pi_dist X X₀ i).trans hX)
    refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun X =>
        (cv_measurable_comp_grad (cv_continuous_of hf).measurable
            (Matrix.of X) φ).aestronglyMeasurable
    · filter_upwards [hnhds] with X hX
      filter_upwards with x
      rw [Real.norm_eq_abs]
      have : Matrix.of X + grad φ x = Matrix.of X₀ + (Matrix.of X - Matrix.of X₀ + grad φ x) := by
        abel
      rw [this]
      refine hM _ fun i k => ?_
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply]
      calc |X i k - X₀ i k + grad φ x i k| ≤ |X i k - X₀ i k| + |grad φ x i k| := abs_add_le _ _
        _ ≤ 1 + K := add_le_add (hX i k) (cv_grad_abs_le hφ x i k)
        _ = K + 1 := add_comm _ _
    · exact integrableOn_const (by rw [cv_volume_unitCube]; exact ENNReal.one_ne_top)
    · exact Filter.Eventually.of_forall fun x =>
        (hf.comp ((continuous_matrixOf.2 continuous_id).add continuous_const)).continuousAt
  have hc : Continuous fun A : Matrix (Fin d) (Fin m) ℝ => (fun i k => A i k : Fin d → Fin m → ℝ) :=
    continuous_pi fun i => continuous_pi fun k => continuous_id.matrix_elem i k
  exact hg.comp hc

/-- `cubeInf f` is upper semicontinuous, as an infimum of continuous functions. -/
theorem cubeInf_usc {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f) :
    UpperSemicontinuous (cubeInf f) := by
  refine upperSemicontinuous_iInf fun φ => upperSemicontinuous_iInf fun hφ => ?_
  obtain ⟨⟨K, hK⟩, -⟩ := hφ
  exact (continuous_coe_real_ereal.comp (cv_continuous_integral hf hK)).upperSemicontinuous

end CalculusOfVariations
