module

public import CalculusOfVariations.Envelope.Formula

/-!
# Solution: the quasiconvex envelope (Dacorogna's formula)

The statements of `palomar/QuasiconvexEnvelope/Challenge.lean`, word for word, proved from the
library.
-/

@[expose] public section

open MeasureTheory

namespace QuasiconvexEnvelopeChallenge

open CalculusOfVariations

variable {d m : ℕ} {f : Matrix (Fin d) (Fin m) ℝ → ℝ} {Ω : Set (Fin m → ℝ)}

theorem quasiconvexEnvelope_eq_domainInf (hf : Continuous f) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) (A : Matrix (Fin d) (Fin m) ℝ) :
    quasiconvexEnvelope f A = domainInf Ω f A :=
  CalculusOfVariations.quasiconvexEnvelope_eq_domainInf hf hΩ hb hne A

theorem domainInf_eq (hf : Continuous f) (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) {Ω' : Set (Fin m → ℝ)} (hΩ' : IsOpen Ω') (hb' : Bornology.IsBounded Ω')
    (hne' : Ω'.Nonempty) (A : Matrix (Fin d) (Fin m) ℝ) :
    domainInf Ω f A = domainInf Ω' f A :=
  domainInf_eq_of_isBounded hf hΩ hb hne hΩ' hb' hne' A

theorem domainInf_le_of_rank_le_one (hf : Continuous f) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) {A B : Matrix (Fin d) (Fin m) ℝ}
    (hAB : (A - B).rank ≤ 1) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) :
    domainInf Ω f (l • A + (1 - l) • B) ≤
      (l : EReal) * domainInf Ω f A + ((1 - l : ℝ) : EReal) * domainInf Ω f B :=
  CalculusOfVariations.domainInf_le_of_rank_le_one hf hΩ hb hne hAB hl0 hl1

theorem exists_domainInf_eq_coe (hf : Continuous f) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) {A₀ : Matrix (Fin d) (Fin m) ℝ}
    (h : domainInf Ω f A₀ ≠ ⊥) :
    ∃ g : Matrix (Fin d) (Fin m) ℝ → ℝ, Continuous g ∧ RankOneConvex g ∧ Quasiconvex g ∧
      ∀ A, domainInf Ω f A = (g A : EReal) := by
  obtain ⟨g, hg, hq, h⟩ := CalculusOfVariations.exists_domainInf_eq_coe hf hΩ hb hne h
  exact ⟨g, hg, rankOneConvex_of_quasiconvex_of_measurable hg.measurable
    (isLocallyBounded_of_continuous hg) hq, hq, h⟩

end QuasiconvexEnvelopeChallenge
