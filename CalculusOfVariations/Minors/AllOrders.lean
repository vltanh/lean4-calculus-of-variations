/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Minors.Quasiaffine
public import CalculusOfVariations.Lipschitz.ZeroSet

/-!
# Minors of every order are null Lagrangians and quasiaffine

For a Lipschitz `φ : ℝ^m → ℝ^d` vanishing outside a bounded set `Ω`, every `A` and every minor (of
any order `k`), `∫_Ω minor (A + ∇φ) = |Ω| minor A` (`setIntegral_minor_add_grad`). This is (8.44) of
Theorem 8.35 of B. Dacorogna, *Direct Methods in the Calculus of Variations*, 2nd ed., Springer,
2008 ([D08], p. 409–411; `Ω` open there), by the proof of its part (ii), with `v` affine and
`w = φ`:

* (Theorem 8.33, p. 407–408; there for maps of class `C²`) For smooth `v_1, …, v_k` and the partial
  derivatives in the directions `c_1, …, c_k`, a Jacobian is a divergence, (8.43):
  `det [∂_{c_j} v_i] = ∑_t ± ∂_{c_t} (v_{i₀} M_t)`, `M_t` the minor without the row `i₀` and the
  column `t`, because `∑_t ± ∂_{c_t} M_t = 0`, (8.42). Here both are written with Leibniz' formula,
  as sums over the permutations `σ` of the columns (`nl_det_eq_sum_D`, `nl_sum_perm_eq_zero`), and
  (8.42) is a sign-reversing involution, `σ ↦ σ ∘ (i₀ i)`: it exchanges the two mixed second
  derivatives `∂_{c_{σ(i₀)}} ∂_{c_{σ(i)}} v_i`. [D08] proves (8.42) by induction on `k`, inserting
  (8.43) for the minors of order `k − 1`. The cancellation is the same (mixed second derivatives are
  symmetric and the sign changes), but not the terms: in [D08] they are second derivatives of
  products of `v_2` with minors of order `k − 2`.
* (p. 410–411) `det (X + Y)` is the sum over the sets `s` of rows of the determinants with the rows
  `s` of `X` and the other rows of `Y` (Proposition 5.67 of [D08]; `nl_det_add_eq_sum`). For `X` a
  submatrix of `A` and `Y` the one of `∇ψ`, `ψ` smooth with compact support, each of these
  determinants is a Jacobian, of linear functions and components of `ψ`, and its integral vanishes
  if at least one component of `ψ` occurs (`nl_integral_det_smooth`); the remaining term is `det X`.
  So `∫ (minor (A + ∇ψ) − minor A) = 0` (`nl_integral_det_add_smooth`).
* (Step 2, "elementary density argument") The identity passes to compactly supported Lipschitz maps
  by mollification (`nl_lipschitz_limit`; `nl_integral_minor_sub`), and the gradient of `φ` vanishes
  almost everywhere outside `Ω` (`rd_ae_grad_eq_zero`).

The minors of orders `2` and `3` are treated with explicit formulas in `Minors.NullLagrangian` and
`Minors.Quasiaffine`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace CalculusOfVariations

variable {d m k : ℕ}

/-! ### Products of smooth functions -/

/-- A finite product of smooth functions is smooth. -/
theorem nl_contDiff_prod {ι : Type*} (s : Finset ι) {g : ι → (Fin m → ℝ) → ℝ}
    (hg : ∀ i ∈ s, ContDiff ℝ ∞ (g i)) : ContDiff ℝ ∞ fun x => ∏ i ∈ s, g i x :=
  contDiff_prod hg

/-- `∂_a ∏ g_i = ∑_i ∂_a g_i ∏_{j ≠ i} g_j`. -/
theorem nl_D_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {g : ι → (Fin m → ℝ) → ℝ}
    (hg : ∀ i ∈ s, ContDiff ℝ ∞ (g i)) (a : Fin m) (x : Fin m → ℝ) :
    nlD a (fun y => ∏ i ∈ s, g i y) x =
      ∑ i ∈ s, (∏ j ∈ s.erase i, g j x) * nlD a (g i) x := by
  have h := HasFDerivAt.finsetProd (u := s) (x := x) (g := g) fun i hi =>
    (((hg i hi).differentiable (by simp)) x).hasFDerivAt
  simp only [nlD]
  rw [h.fderiv]
  simp [smul_eq_mul]

/-! ### The divergence identity -/

/-- **The divergence of the cofactors vanishes**, (8.42) of [D08], in Leibniz form:
`∑_σ sgn σ ∂_{c_{σ(i₀)}} ∏_{i ≠ i₀} ∂_{c_{σ(i)}} v_i = 0`. By the product rule the sum is over `σ`
and `i ≠ i₀`, with the second derivatives `∂_{c_{σ(i₀)}} ∂_{c_{σ(i)}} v_i`; for fixed `i`, the
involution `σ ↦ σ ∘ (i₀ i)` changes the sign and, by the symmetry of the second derivatives, nothing
else. -/
theorem nl_sum_perm_eq_zero {v : Fin k → (Fin m → ℝ) → ℝ} (i₀ : Fin k)
    (hv : ∀ i, i ≠ i₀ → ContDiff ℝ ∞ (v i)) (c : Fin k → Fin m) (x : Fin m → ℝ) :
    ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) *
      nlD (c (σ i₀)) (fun y => ∏ i ∈ Finset.univ.erase i₀, nlD (c (σ i)) (v i) y) x = 0 := by
  have h1 : ∀ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) *
      nlD (c (σ i₀)) (fun y => ∏ i ∈ Finset.univ.erase i₀, nlD (c (σ i)) (v i) y) x =
      ∑ i ∈ Finset.univ.erase i₀, (Equiv.Perm.sign σ : ℝ) *
        ((∏ j ∈ (Finset.univ.erase i₀).erase i, nlD (c (σ j)) (v j) x) *
          nlD (c (σ i₀)) (nlD (c (σ i)) (v i)) x) := by
    intro σ
    rw [nl_D_prod _ (fun i hi => nl_D_contDiff (hv i (Finset.ne_of_mem_erase hi)) _),
      Finset.mul_sum]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hne : i ≠ i₀ := Finset.ne_of_mem_erase hi
  refine Finset.sum_involution (fun σ _ => σ * Equiv.swap i₀ i) (fun σ _ => ?_) (fun σ _ _ => ?_)
    (fun _ _ => Finset.mem_univ _) (fun σ _ => ?_)
  · have hprod : ∏ j ∈ (Finset.univ.erase i₀).erase i,
        nlD (c ((σ * Equiv.swap i₀ i) j)) (v j) x =
        ∏ j ∈ (Finset.univ.erase i₀).erase i, nlD (c (σ j)) (v j) x := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne
        (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)) (Finset.ne_of_mem_erase hj)]
    rw [hprod, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, nl_D_comm (hv i hne) (c (σ i)) (c (σ i₀)), Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap hne.symm]
    push_cast
    ring
  · intro h
    have := congrArg (fun τ : Equiv.Perm (Fin k) => τ i₀) h
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at this
    exact hne (σ.injective this)
  · rw [mul_assoc, Equiv.swap_mul_self, mul_one]

/-- **A Jacobian is a divergence**, (8.43) of [D08], in Leibniz form, for any row `i₀`:
`det [∂_{c_j} v_i] = ∑_σ sgn σ ∂_{c_{σ(i₀)}} (v_{i₀} ∏_{i ≠ i₀} ∂_{c_{σ(i)}} v_i)`, by the product
rule and `nl_sum_perm_eq_zero`. -/
theorem nl_det_eq_sum_D {v : Fin k → (Fin m → ℝ) → ℝ} (i₀ : Fin k)
    (hv : ∀ i, ContDiff ℝ ∞ (v i)) (c : Fin k → Fin m) (x : Fin m → ℝ) :
    (Matrix.of fun i j => nlD (c j) (v i) x).det =
      ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) * nlD (c (σ i₀)) (fun y => v i₀ y *
        ∏ i ∈ Finset.univ.erase i₀, nlD (c (σ i)) (v i) y) x := by
  have hP : ∀ σ : Equiv.Perm (Fin k), ContDiff ℝ ∞
      fun y => ∏ i ∈ Finset.univ.erase i₀, nlD (c (σ i)) (v i) y := fun σ =>
    nl_contDiff_prod _ fun i _ => nl_D_contDiff (hv i) _
  have h0 := nl_sum_perm_eq_zero i₀ (fun i _ => hv i) c x
  calc (Matrix.of fun i j => nlD (c j) (v i) x).det
      = ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) * ∏ i, nlD (c (σ i)) (v i) x := by
        rw [← Matrix.det_transpose, Matrix.det_apply']
        rfl
    _ = ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) * ∏ i, nlD (c (σ i)) (v i) x +
        v i₀ x * ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) *
          nlD (c (σ i₀)) (fun y => ∏ i ∈ Finset.univ.erase i₀, nlD (c (σ i)) (v i) y) x := by
        rw [h0, mul_zero, add_zero]
    _ = _ := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [nl_D_mul (hv i₀) (hP σ), ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
        ring

/-- A Jacobian with one compactly supported component integrates to zero (smooth case): it is a sum
of derivatives of smooth, compactly supported functions. -/
theorem nl_integral_det_smooth {v : Fin k → (Fin m → ℝ) → ℝ} (i₀ : Fin k)
    (hv : ∀ i, ContDiff ℝ ∞ (v i)) (hc : HasCompactSupport (v i₀)) (c : Fin k → Fin m) :
    ∫ x, (Matrix.of fun i j => nlD (c j) (v i) x).det = 0 := by
  have hw : ∀ σ : Equiv.Perm (Fin k), ContDiff ℝ ∞ fun y => v i₀ y *
      ∏ i ∈ Finset.univ.erase i₀, nlD (c (σ i)) (v i) y := fun σ =>
    (hv i₀).mul (nl_contDiff_prod _ fun i _ => nl_D_contDiff (hv i) _)
  have hwc : ∀ σ : Equiv.Perm (Fin k), HasCompactSupport fun y => v i₀ y *
      ∏ i ∈ Finset.univ.erase i₀, nlD (c (σ i)) (v i) y := fun σ => hc.mul_right
  simp_rw [nl_det_eq_sum_D i₀ hv c]
  rw [integral_finsetSum _ fun σ _ => (nl_integrable_of_smooth (nl_D_contDiff (hw σ) _)
    (nl_hasCompactSupport_D (hwc σ) _)).const_mul _]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [integral_const_mul, nl_integral_D_eq_zero (hw σ) (hwc σ), mul_zero]

/-! ### The minors of `A + ∇φ` -/

/-- A Jacobian whose component `i₀` is compactly supported is integrable (smooth case). -/
theorem nl_integrable_det_smooth {v : Fin k → (Fin m → ℝ) → ℝ} (i₀ : Fin k)
    (hv : ∀ i, ContDiff ℝ ∞ (v i)) (hc : HasCompactSupport (v i₀)) (c : Fin k → Fin m) :
    Integrable fun x => (Matrix.of fun i j => nlD (c j) (v i) x).det := by
  have hw : ∀ σ : Equiv.Perm (Fin k), ContDiff ℝ ∞ fun y => v i₀ y *
      ∏ i ∈ Finset.univ.erase i₀, nlD (c (σ i)) (v i) y := fun σ =>
    (hv i₀).mul (nl_contDiff_prod _ fun i _ => nl_D_contDiff (hv i) _)
  simp_rw [nl_det_eq_sum_D i₀ hv c]
  exact integrable_finsetSum _ fun σ _ => (nl_integrable_of_smooth (nl_D_contDiff (hw σ) _)
    (nl_hasCompactSupport_D hc.mul_right _)).const_mul _

/-- The linear function `y ↦ ∑_l a_l y_l` has the partial derivatives `a_b`. -/
theorem nl_D_linear (a : Fin m → ℝ) (b : Fin m) (x : Fin m → ℝ) :
    nlD b (fun y => ∑ l, a l * y l) x = a b := by
  have h : HasFDerivAt (fun y : Fin m → ℝ => ∑ l, a l * y l)
      (∑ l, a l • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) l) x :=
    HasFDerivAt.fun_sum fun l _ => (hasFDerivAt_apply l x).const_mul (a l)
  rw [nlD, h.fderiv]
  simp [Pi.single_apply]

/-- Proposition 5.67 of [D08]: `det (X + Y)` is the sum over `s` of the determinants with the rows
`i ∈ s` of `X` and the rows `i ∉ s` of `Y`. -/
theorem nl_det_add_eq_sum (X Y : Matrix (Fin k) (Fin k) ℝ) :
    (X + Y).det =
      ∑ s : Finset (Fin k), (Matrix.of fun i j => if i ∈ s then X i j else Y i j).det := by
  have h := (Matrix.detRowAlternating (n := Fin k) (R := ℝ)).toMultilinearMap.map_add_univ
    (Matrix.of.symm X) (Matrix.of.symm Y)
  refine h.trans (Finset.sum_congr rfl fun s _ => ?_)
  change (Matrix.of (s.piecewise (Matrix.of.symm X) (Matrix.of.symm Y))).det = _
  congr 1
  ext i j
  by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]

/-- **The smooth case**: for smooth compactly supported `ψ_i` and a constant matrix `X`,
`∫ (det (X + [∂_{c_j} ψ_i]) − det X) = 0`. By `nl_det_add_eq_sum` the integrand is the sum over the
sets `s` of rows, `s` not the set of all rows, of the Jacobians of the functions `v s i`, where
`v s i` is linear with the gradient `X_i` for `i ∈ s`, and `ψ_i` for `i ∉ s`. -/
theorem nl_integral_det_add_smooth (X : Matrix (Fin k) (Fin k) ℝ) {ψ : Fin k → (Fin m → ℝ) → ℝ}
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (hc : ∀ i, HasCompactSupport (ψ i)) (c : Fin k ↪o Fin m) :
    ∫ x, ((X + Matrix.of fun i j => nlD (c j) (ψ i) x).det - X.det) = 0 := by
  classical
  -- `v s i = X_i · x` for `i ∈ s`, and `v s i = ψ_i` for `i ∉ s`
  set v : Finset (Fin k) → Fin k → (Fin m → ℝ) → ℝ := fun s i =>
    if i ∈ s then fun y => ∑ l, (∑ j, if c j = l then X i j else 0) * y l else ψ i with hv
  have hvs : ∀ s i, ContDiff ℝ ∞ (v s i) := by
    intro s i
    simp only [hv]
    split_ifs
    · exact ContDiff.sum fun l _ => contDiff_const.mul (by fun_prop)
    · exact hψ i
  have hvD : ∀ (s : Finset (Fin k)) x,
      (Matrix.of fun i j => if i ∈ s then X i j else Matrix.of (fun i j => nlD (c j) (ψ i) x) i j) =
        Matrix.of fun i j => nlD (c j) (v s i) x := by
    intro s x
    ext i j
    by_cases hi : i ∈ s
    · simp only [Matrix.of_apply, hv, hi, ite_true, nl_D_linear, c.injective.eq_iff]
      simp
    · simp only [Matrix.of_apply, hv, hi, ite_false]
  have hexp : ∀ x, (X + Matrix.of fun i j => nlD (c j) (ψ i) x).det - X.det =
      ∑ s ∈ Finset.univ.erase Finset.univ, (Matrix.of fun i j => nlD (c j) (v s i) x).det := by
    intro x
    have hX : (Matrix.of fun i j => if i ∈ (Finset.univ : Finset (Fin k)) then X i j else
        Matrix.of (fun i j => nlD (c j) (ψ i) x) i j) = X := by
      ext i j; simp
    rw [nl_det_add_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ Finset.univ), hX,
      add_sub_cancel_left]
    simp_rw [hvD]
  have key : ∀ s ∈ Finset.univ.erase (Finset.univ : Finset (Fin k)),
      ∃ i₀, HasCompactSupport (v s i₀) := by
    intro s hs
    have hne : s ≠ Finset.univ := Finset.ne_of_mem_erase hs
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ ∉ s := by
      by_contra h
      push Not at h
      exact hne (Finset.eq_univ_iff_forall.2 h)
    exact ⟨i₀, by simpa only [hv, hi₀, ite_false] using hc i₀⟩
  simp_rw [hexp]
  rw [integral_finsetSum _ fun s hs => ?_]
  · refine Finset.sum_eq_zero fun s hs => ?_
    obtain ⟨i₀, hi₀⟩ := key s hs
    exact nl_integral_det_smooth i₀ (hvs s) hi₀ c
  · obtain ⟨i₀, hi₀⟩ := key s hs
    exact nl_integrable_det_smooth i₀ (hvs s) hi₀ c

/-- For a Lipschitz `φ` with compact support, `∫ (minor (A + ∇φ) − minor A) = 0`. -/
theorem nl_integral_minor_sub {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    (hc : HasCompactSupport φ) (A : Matrix (Fin d) (Fin m) ℝ) (r : Fin k ↪o Fin d)
    (c : Fin k ↪o Fin m) : ∫ x, (minor (A + grad φ x) r c - minor A r c) = 0 := by
  have hcomp : ∀ i, HasCompactSupport fun y => φ y i := fun i =>
    hc.comp_left (g := fun z : Fin d → ℝ => z i) rfl
  have hF : Continuous fun G : Fin d → Fin m → ℝ =>
      minor (A + Matrix.of G) r c - minor A r c := by
    have : Continuous fun G : Fin d → Fin m → ℝ => (A + Matrix.of G).submatrix r c :=
      (continuous_const.add continuous_id).matrix_submatrix r c
    exact this.matrix_det.sub continuous_const
  refine nl_lipschitz_limit (fun i y => φ y i) (fun _ => K) (nl_lip_comp hφ) hcomp
    (fun G => minor (A + Matrix.of G) r c - minor A r c) hF (by simp) fun ψ hψ hψc => ?_
  exact nl_integral_det_add_smooth (A.submatrix r c) (fun i => hψ (r i)) (fun i => hψc (r i)) c

/-- **Minors of every order are quasiaffine** ([D08], Theorem 8.35, (8.44)): for a bounded `Ω` and a
Lipschitz `φ` vanishing outside `Ω`, `∫_Ω minor (A + ∇φ) = |Ω| minor A`. -/
theorem setIntegral_minor_add_grad {Ω : Set (Fin m → ℝ)} (hb : Bornology.IsBounded Ω)
    {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ) (h0 : ∀ x ∉ Ω, φ x = 0)
    (A : Matrix (Fin d) (Fin m) ℝ) (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m) :
    ∫ x in Ω, minor (A + grad φ x) r c = (volume Ω).toReal * minor A r c := by
  have hfin : volume Ω ≠ ⊤ := hb.measure_lt_top.ne
  have hcs : HasCompactSupport φ := by
    obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    exact HasCompactSupport.intro (isCompact_closedBall _ R) fun x hx => h0 x fun h => hx (hR h)
  have hcont : Continuous fun J : Matrix (Fin d) (Fin m) ℝ => minor J r c :=
    (continuous_id.matrix_submatrix r c).matrix_det
  have hI : IntegrableOn (fun x => minor (A + grad φ x) r c) Ω :=
    nl_integrableOn_cube hφ hcont A Ω hfin
  have h1 : ∫ x in Ω, (minor (A + grad φ x) r c - minor A r c) = 0 := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero, nl_integral_minor_sub hφ hcs A r c]
    filter_upwards [rd_ae_grad_eq_zero hφ] with x hx hxΩ
    rw [hx (h0 x hxΩ), add_zero, sub_self]
  rw [integral_sub hI (integrableOn_const hfin enorm_ne_top), setIntegral_const, smul_eq_mul,
    Measure.real] at h1
  linarith

end CalculusOfVariations
