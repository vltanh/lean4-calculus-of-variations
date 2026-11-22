/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Minors.AllOrders
public import CalculusOfVariations.Quasiconvex.RankOneConvex

/-!
# Quasiaffine functions are the affine combinations of minors

`rankOneAffine_tfae`: for `f : ℝ^{d×m} → ℝ`, the following are equivalent: `f` is rank-one affine;
`f` is quasiaffine (`f` and `−f` are quasiconvex); `f` is a null Lagrangian
(`∫_Ω f (A + ∇φ) = |Ω| f (A)` for every bounded open `Ω` and every test map `φ` on `Ω`); `f` is an
affine combination of minors. This is the equivalence of (i), (ii), (iii') in Theorem 5.20 of
B. Dacorogna, *Direct Methods in the Calculus of Variations*, 2nd ed., Springer, 2008 ([D08],
p. 179), which is due to J. M. Ball, *Convexity conditions and existence theorems in nonlinear
elasticity*, Arch. Ration. Mech. Anal. 63 (1977), 337–403, with the null Lagrangians of
Proposition 4 of B. Dacorogna, *Quasiconvexity and relaxation of nonconvex problems in the calculus
of variations*, J. Funct. Anal. 46 (1982), 102–118 ([D82]; on every bounded domain). The proof is
that of [D08]:

* (ii) ⇒ (iii'), rank-one affine ⇒ affine combination of minors, in [D08] through (ii'):
  `RankOneAffine.exists_eq_sum_minor`, by the proof of [D08] (see there), where (ii') ⇒ (iii') is
  "the only non trivial implication".
* (iii') ⇒ (i), affine combination of minors ⇒ quasiaffine. [D08] gives two arguments: through (iii)
  and Theorem 5.3 (polyconvex ⇒ quasiconvex, by (8.44) and Jensen's inequality), and by Theorem 8.35
  (p. 181). The second one is used: (8.44) (`setIntegral_minor_add_grad`) makes an affine
  combination of minors a null Lagrangian, which is also the argument of [D08] for Corollary 5.22,
  and a null Lagrangian is quasiaffine, by the case of the unit cube. [D82] states Proposition 4
  without proof.
* (i) ⇒ (ii), quasiaffine ⇒ rank-one affine: "immediately from Theorem 5.3", quasiconvex ⇒ rank-one
  convex, for `f` and `−f` (`rankOneConvex_of_quasiconvex`). The library proves this theorem once,
  by the proof of F. Rindler, *Calculus of Variations*, 2nd ed., 2026, Proposition 5.6; the proof of
  Theorem 5.3 in [D08] compares the same energies, with test maps from its Lemma 3.11.

Conditions (ii') and (iii) of [D08], Theorem 5.20 (`f` of class `C¹` with
`f (ξ + a ⊗ b) = f (ξ) + ⟨∇f (ξ); a ⊗ b⟩`; `f` and `−f` polyconvex) are not treated.
-/

@[expose] public section

open MeasureTheory

namespace CalculusOfVariations

variable {d m : ℕ}

/-- A minor is a continuous function of the matrix. -/
theorem continuous_minor {k : ℕ} (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m) :
    Continuous fun A : Matrix (Fin d) (Fin m) ℝ => minor A r c :=
  (continuous_id.matrix_submatrix r c).matrix_det

/-- Affine combinations of minors are null Lagrangians: `setIntegral_minor_add_grad`, summed. -/
theorem setIntegral_sum_minor_add_grad
    (a : (k : ℕ) → (Fin k ↪o Fin d) → (Fin k ↪o Fin m) → ℝ) (s : Finset ℕ) {Ω : Set (Fin m → ℝ)}
    (hb : Bornology.IsBounded Ω) {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) (h0 : ∀ x ∉ Ω, φ x = 0) (A : Matrix (Fin d) (Fin m) ℝ) :
    ∫ x in Ω, ∑ k ∈ s, ∑ r, ∑ c, a k r c * minor (A + grad φ x) r c =
      (volume Ω).toReal * ∑ k ∈ s, ∑ r, ∑ c, a k r c * minor A r c := by
  have hfin : volume Ω ≠ ⊤ := hb.measure_lt_top.ne
  have hI : ∀ (k : ℕ) (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m),
      IntegrableOn (fun x => a k r c * minor (A + grad φ x) r c) Ω := fun k r c =>
    (nl_integrableOn_cube hφ (continuous_minor r c) A Ω hfin).const_mul _
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun r _ =>
    integrable_finsetSum _ fun c _ => hI k r c, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun r _ => integrable_finsetSum _ fun c _ => hI k r c, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_finsetSum _ fun c _ => hI k r c, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_const_mul, setIntegral_minor_add_grad hb hφ h0]
  ring

/-- **Quasiaffine functions are the affine combinations of minors** ([D08], Theorem 5.20, (i), (ii),
(iii'); [D82], Proposition 4). For `f : ℝ^{d×m} → ℝ` the following are equivalent:

1. `f` is rank-one affine (`f` and `−f` are rank-one convex);
2. `f` is quasiaffine: Borel, locally bounded, and `f` and `−f` are quasiconvex;
3. `f` is a null Lagrangian: Borel, locally bounded, and `∫_Ω f (A + ∇φ) = |Ω| f (A)` for every
   bounded open `Ω`, every `A` and every Lipschitz `φ` vanishing outside `Ω`;
4. `f` is an affine combination of minors, `f (A) = ∑_{k ≤ min d m} ∑_{r, c} a k r c · minor A r c`
   (the `0 × 0` minor is the constant `1`). -/
theorem rankOneAffine_tfae (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : List.TFAE
    [RankOneAffine f,
      Measurable f ∧ IsLocallyBounded f ∧ Quasiconvex f ∧ Quasiconvex (-f),
      Measurable f ∧ IsLocallyBounded f ∧ ∀ Ω : Set (Fin m → ℝ), IsOpen Ω →
        Bornology.IsBounded Ω → ∀ (A : Matrix (Fin d) (Fin m) ℝ) (φ : (Fin m → ℝ) → Fin d → ℝ)
          (K : NNReal), LipschitzWith K φ → (∀ x ∉ Ω, φ x = 0) →
            ∫ x in Ω, f (A + grad φ x) = (volume Ω).toReal * f A,
      ∃ a : (k : ℕ) → (Fin k ↪o Fin d) → (Fin k ↪o Fin m) → ℝ,
        ∀ A, f A = ∑ k ∈ Finset.range (min d m + 1), ∑ r, ∑ c, a k r c * minor A r c] := by
  tfae_have 1 → 4 := fun h => h.exists_eq_sum_minor
  tfae_have 4 → 3 := by
    rintro ⟨a, ha⟩
    have hc : Continuous f := by
      rw [show f = fun A => ∑ k ∈ Finset.range (min d m + 1), ∑ r, ∑ c, a k r c * minor A r c from
        funext ha]
      exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun r _ =>
        continuous_finsetSum _ fun c _ => continuous_const.mul (continuous_minor r c)
    refine ⟨hc.measurable, isLocallyBounded_of_continuous hc, fun Ω _ hb A φ K hφ h0 => ?_⟩
    simp only [ha]
    exact setIntegral_sum_minor_add_grad a _ hb hφ h0 A
  tfae_have 3 → 2 := by
    rintro ⟨hm, hb, h⟩
    have hQ : ∀ (A : Matrix (Fin d) (Fin m) ℝ) (φ : (Fin m → ℝ) → Fin d → ℝ) (K : NNReal),
        LipschitzWith K φ → (∀ x ∉ unitCube m, φ x = 0) →
          ∫ x in unitCube m, f (A + grad φ x) = (volume (unitCube m)).toReal * f A :=
      h (unitCube m) (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo)
        ((nl_isCompact_Icc m).isBounded.subset (nl_unitCube_subset m))
    refine ⟨hm, hb, fun A φ K hφ h0 _ => (hQ A φ K hφ h0).ge, fun A φ K hφ h0 _ => ?_⟩
    simp only [Pi.neg_apply, integral_neg, mul_neg]
    exact (neg_le_neg_iff.2 (hQ A φ K hφ h0).le)
  tfae_have 2 → 1 := by
    rintro ⟨hm, hb, hq, hq'⟩
    refine ⟨rankOneConvex_of_quasiconvex hm hb hq,
      rankOneConvex_of_quasiconvex hm.neg (fun A => ?_) hq'⟩
    obtain ⟨U, hU, C, hC⟩ := hb A
    exact ⟨U, hU, C, fun B hB => by rw [Pi.neg_apply, abs_neg]; exact hC B hB⟩
  tfae_finish

end CalculusOfVariations
