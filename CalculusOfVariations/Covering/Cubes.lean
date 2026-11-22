/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Finite disjoint coverings by cubes

`cv_exists_finite_cover`: the Besicovitch covering theorem in finite form, on `ℝ^m` with the sup
norm (so that `Metric.closedBall x r` is the cube `x + [−r, r]^m`). If almost every point of a set
`s` of finite measure has arbitrarily small admissible radii, then finitely many disjoint
admissible closed cubes cover `s` up to measure `ε`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

namespace CalculusOfVariations

variable {m : ℕ}

/-- The Besicovitch covering theorem, finite form: if every point of `s` (up to a null set) has
arbitrarily small admissible radii, then finitely many disjoint admissible closed cubes cover `s`
up to measure `ε`. -/
theorem cv_exists_finite_cover {s : Set (Fin m → ℝ)} (hs : volume s ≠ ⊤)
    (hsm : MeasurableSet s) (P : (Fin m → ℝ) → ℝ → Prop)
    (hP : ∀ᵐ x, x ∈ s → ∀ δ > 0, ∃ r ∈ Ioo 0 δ, P x r) {ε : ENNReal} (hε : 0 < ε) :
    ∃ t : Finset ((Fin m → ℝ) × ℝ), (∀ p ∈ t, 0 < p.2 ∧ P p.1 p.2) ∧
      (t : Set ((Fin m → ℝ) × ℝ)).PairwiseDisjoint (fun p => closedBall p.1 p.2) ∧
      volume (s \ ⋃ p ∈ t, closedBall p.1 p.2) < ε := by
  classical
  -- the good points
  set s' := {x ∈ s | ∀ δ > 0, ∃ r ∈ Ioo 0 δ, P x r} with hs'
  have hss' : volume (s \ s') = 0 := by
    rw [ae_iff] at hP
    refine measure_mono_null (fun x hx => ?_) hP
    intro h
    exact hx.2 ⟨hx.1, h hx.1⟩
  obtain ⟨t, r, htc, hts, htr, htμ, htd⟩ := Besicovitch.exists_disjoint_closedBall_covering_ae
    volume (fun x => {r | P x r}) s' (fun x hx δ hδ => by
      obtain ⟨r, hr, hPr⟩ := hx.2 δ hδ
      exact ⟨r, hPr, hr⟩) (fun _ => 1) (fun _ _ => one_pos)
  -- the whole countable family covers `s` up to a null set
  have hnull : volume (s \ ⋃ x ∈ t, closedBall x (r x)) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (measure_union_null hss' htμ)
    by_cases h : x ∈ s'
    · exact Or.inr ⟨h, hx.2⟩
    · exact Or.inl ⟨hx.1, h⟩
  -- exhaust the countable family by finite subfamilies
  rcases t.eq_empty_or_nonempty with rfl | hne
  · refine ⟨∅, by simp, by simp, ?_⟩
    simpa using (show volume s = 0 by simpa using hnull) ▸ hε
  obtain ⟨e, he⟩ := htc.exists_eq_range hne
  let S : ℕ → Set (Fin m → ℝ) := fun n => s \ ⋃ k ∈ Finset.range n, closedBall (e k) (r (e k))
  have hanti : Antitone S := by
    intro a b hab x hx
    refine ⟨hx.1, fun h => hx.2 ?_⟩
    simp only [mem_iUnion, Finset.mem_range] at h ⊢
    obtain ⟨k, hk, hxk⟩ := h
    exact ⟨k, lt_of_lt_of_le hk hab, hxk⟩
  have hmeas : ∀ n, NullMeasurableSet (S n) volume := fun n =>
    (hsm.diff (Finset.measurableSet_biUnion _ fun k _ => isClosed_closedBall.measurableSet))
      |>.nullMeasurableSet
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, by
    exact ne_top_of_le_ne_top hs (measure_mono sdiff_subset)⟩
  have hinter : (⋂ n, S n) = s \ ⋃ x ∈ t, closedBall x (r x) := by
    ext x
    simp only [S, mem_iInter]
    constructor
    · intro h
      refine ⟨(h 0).1, fun hx => ?_⟩
      simp only [mem_iUnion] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      rw [he] at hy
      obtain ⟨k, rfl⟩ := hy
      exact (h (k + 1)).2 (mem_iUnion₂.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_self k), hxy⟩)
    · rintro ⟨hxs, h⟩ n
      refine ⟨hxs, fun hx => h ?_⟩
      obtain ⟨k, -, hxk⟩ := mem_iUnion₂.1 hx
      exact mem_iUnion₂.2 ⟨e k, he ▸ mem_range_self k, hxk⟩
  rw [hinter, hnull] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  refine ⟨(Finset.range n).image fun k => (e k, r (e k)), ?_, ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_image, Finset.mem_range] at hp
    obtain ⟨k, -, rfl⟩ := hp
    have hk : e k ∈ t := he ▸ mem_range_self k
    exact ⟨(htr _ hk).2.1, (htr _ hk).1⟩
  · intro p hp q hq hpq
    simp only [Finset.coe_image, Finset.coe_range, mem_image, mem_Iio] at hp hq
    obtain ⟨k, -, rfl⟩ := hp
    obtain ⟨l, -, rfl⟩ := hq
    have hk : e k ∈ t := he ▸ mem_range_self k
    have hl : e l ∈ t := he ▸ mem_range_self l
    have hne : e k ≠ e l := fun h => hpq (by simp [h])
    exact htd hk hl hne
  · have e : s \ ⋃ p ∈ (Finset.range n).image (fun k => (e k, r (e k))), closedBall p.1 p.2 =
        S n := by
      ext x
      simp [S]
    rw [e]
    exact hn

end CalculusOfVariations
