module

public import CalculusOfVariations.Minors.Characterization

/-!
# Solution: null Lagrangians and quasiaffine functions

The statements of `palomar/NullLagrangians/Challenge.lean`, word for word, proved from the library.
-/

@[expose] public section

open MeasureTheory

namespace NullLagrangiansChallenge

open CalculusOfVariations

variable {d m : ℕ}

theorem setIntegral_minor_add_grad {Ω : Set (Fin m → ℝ)} (hΩ : Bornology.IsBounded Ω)
    {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ) (h0 : ∀ x ∉ Ω, φ x = 0)
    (A : Matrix (Fin d) (Fin m) ℝ) {k : ℕ} (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m) :
    ∫ x in Ω, minor (A + grad φ x) r c = (volume Ω).toReal * minor A r c :=
  CalculusOfVariations.setIntegral_minor_add_grad hΩ hφ h0 A r c

theorem rankOneAffine_tfae (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : List.TFAE
    [RankOneAffine f,
      Measurable f ∧ IsLocallyBounded f ∧ Quasiconvex f ∧ Quasiconvex (-f),
      Measurable f ∧ IsLocallyBounded f ∧ ∀ Ω : Set (Fin m → ℝ), IsOpen Ω →
        Bornology.IsBounded Ω → ∀ (A : Matrix (Fin d) (Fin m) ℝ) (φ : (Fin m → ℝ) → Fin d → ℝ)
          (K : NNReal), LipschitzWith K φ → (∀ x ∉ Ω, φ x = 0) →
            ∫ x in Ω, f (A + grad φ x) = (volume Ω).toReal * f A,
      ∃ a : (k : ℕ) → (Fin k ↪o Fin d) → (Fin k ↪o Fin m) → ℝ,
        ∀ A, f A = ∑ k ∈ Finset.range (min d m + 1), ∑ r, ∑ c, a k r c * minor A r c] :=
  CalculusOfVariations.rankOneAffine_tfae f

end NullLagrangiansChallenge
