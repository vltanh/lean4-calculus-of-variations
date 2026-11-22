module

public import CalculusOfVariations.QuadraticForm.Quasiconvex
public import CalculusOfVariations.Quasiconvex.Domain
public import CalculusOfVariations.Quasiconvex.Periodic
public import CalculusOfVariations.Quasiconvex.RankOneConvex
public import CalculusOfVariations.RankOneConvex.LocallyLipschitz

/-!
# Solution: quasiconvexity and rank-one convexity

The statements of `palomar/Quasiconvexity/Challenge.lean`, word for word, proved from the library.
-/

@[expose] public section

open MeasureTheory

namespace QuasiconvexityChallenge

open CalculusOfVariations

variable {d m : ℕ}

open scoped Matrix.Norms.Frobenius in
theorem rankOneConvex_locallyLipschitz {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : RankOneConvex f) :
    LocallyLipschitz f := by
  -- the product metric is at most the Frobenius distance
  have hL : LipschitzWith 1 (Matrix.of.symm : Matrix (Fin d) (Fin m) ℝ → Fin d → Fin m → ℝ) := by
    refine LipschitzWith.of_dist_le_mul fun A B => ?_
    rw [NNReal.coe_one, one_mul, dist_eq_norm A B]
    refine (dist_pi_le_iff (norm_nonneg _)).2 fun i =>
      (dist_pi_le_iff (norm_nonneg _)).2 fun j => ?_
    rw [dist_eq_norm]
    exact Matrix.norm_apply_le_frobenius_norm (A - B) i j
  intro A
  obtain ⟨K, t, ht, hK⟩ := hf.locallyLipschitz (Matrix.of.symm A)
  exact ⟨K * 1, _, hL.continuous.continuousAt.preimage_mem_nhds ht,
    hK.comp (hL.lipschitzOnWith (s := _)) fun _ hx => hx⟩

open scoped Matrix.Norms.Frobenius in
theorem rankOneConvex_abs_sub_le_of_osc {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : RankOneConvex f)
    {F : Matrix (Fin d) (Fin m) ℝ} {r ω : ℝ} (hr : 0 < r)
    (hω : ∀ A ∈ Metric.closedBall F (6 * r), ∀ B ∈ Metric.closedBall F (6 * r), |f A - f B| ≤ ω)
    {A B : Matrix (Fin d) (Fin m) ℝ} (hA : A ∈ Metric.ball F r) (hB : B ∈ Metric.ball F r) :
    |f A - f B| ≤ √(min d m : ℕ) * (ω / (3 * r)) * ‖A - B‖ :=
  hf.abs_sub_le_of_osc hr hω hA hB

theorem rankOneConvex_of_quasiconvex {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hm : Measurable f)
    (hb : IsLocallyBounded f) (hf : Quasiconvex f) : RankOneConvex f :=
  rankOneConvex_of_quasiconvex_of_measurable hm hb hf

theorem quasiconvexAtOn_iff {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hm : Measurable f)
    (hb : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ) {Ω Ω' : Set (Fin m → ℝ)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hΩne : Ω.Nonempty)
    (hΩ' : IsOpen Ω') (hΩ'b : Bornology.IsBounded Ω') (hΩ'ne : Ω'.Nonempty) :
    QuasiconvexAtOn Ω f A ↔ QuasiconvexAtOn Ω' f A :=
  (quasiconvexAtOn_iff_of_measurable hm hb A hΩ hΩb hΩne).symm.trans
    (quasiconvexAtOn_iff_of_measurable hm hb A hΩ' hΩ'b hΩ'ne)

theorem quasiconvexAtOn_unitCube_iff_periodic {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hm : Measurable f) (hb : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ) :
    QuasiconvexAtOn (unitCube m) f A ↔ QuasiconvexAtPeriodic f A :=
  quasiconvexAtOn_iff_periodic_of_measurable hm hb A

theorem quadraticForm_quasiconvex_iff (Q : LinearMap.BilinForm ℝ (Matrix (Fin d) (Fin m) ℝ)) :
    (Quasiconvex fun A => Q A A) ↔ RankOneConvex fun A => Q A A :=
  CalculusOfVariations.quadraticForm_quasiconvex_iff Q

theorem integrableOn_add_grad {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hm : Measurable f)
    (hb : IsLocallyBounded f) {Ω : Set (Fin m → ℝ)} (hΩ : Bornology.IsBounded Ω)
    (A : Matrix (Fin d) (Fin m) ℝ) {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) : IntegrableOn (fun x => f (A + grad φ x)) Ω :=
  rd_integrableOn hm hb A hφ hΩ.measure_lt_top

end QuasiconvexityChallenge
