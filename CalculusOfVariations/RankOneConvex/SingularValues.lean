/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.Matrix.Normed

/-!
# The singular value decomposition of a real matrix

Every real `d × m` matrix is `∑_{i < min d m} σ_i p_i ⊗ q_i` with `σ_0 ≥ σ_1 ≥ … ≥ 0` and
orthonormal families `p_i` in `ℝ^d` and `q_i` in `ℝ^m`
(`Matrix.exists_singularValueDecomposition`), and the rank-one matrices of such a sum are orthogonal
for the Frobenius inner product: `|∑_{i ∈ s} σ_i p_i ⊗ q_i|² = ∑_{i ∈ s} σ_i²`
(`Matrix.frobenius_norm_sq_sum_smul_vecMulVec`).

Mathlib has the singular values of a linear map (`LinearMap.singularValues`), not the decomposition.
The proof here is the standard one. For the linear map `T : ℝ^m → ℝ^d` of the matrix let `q` be an
orthonormal basis of eigenvectors of `T* T`, for the eigenvalues `σ_0² ≥ σ_1² ≥ …`. The vectors
`T q_i` are pairwise orthogonal with `|T q_i| = σ_i` (`lip_inner_apply`), so the `σ_i⁻¹ T q_i` with
`σ_i > 0` are orthonormal and extend to an orthonormal basis `p` of `ℝ^d`
(`lip_exists_orthonormalBasis`). The place of the decomposition in Mathlib would be after
`Mathlib/Analysis/InnerProductSpace/SingularValues.lean`.
-/

@[expose] public section

namespace Matrix

open Finset
open scoped Matrix.Norms.Frobenius RealInnerProductSpace

variable {d m : ℕ}

/-- The images under `T` of the eigenvectors of `T* T` are pairwise orthogonal, and their norms are
the singular values. -/
private lemma lip_inner_apply (T : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (i j : Fin m) :
    let q := T.isSymmetric_adjoint_comp_self.eigenvectorBasis finrank_euclideanSpace_fin
    ⟪T (q i), T (q j)⟫ = if i = j then T.singularValues j ^ 2 else 0 := by
  intro q
  have h := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis finrank_euclideanSpace_fin j
  rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply, h, ← T.sq_singularValues_fin,
    real_inner_smul_right, orthonormal_iff_ite.1 q.orthonormal]
  split_ifs <;> simp

/-- Orthonormal bases `q` of `ℝ^m` and `p` of `ℝ^d` with `T q_i = σ_i p_i` for `i < min d m` and
`T q_i = 0` for `i ≥ d`. -/
private lemma lip_exists_orthonormalBasis
    (T : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∃ (q : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)))
      (p : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))),
      (∀ (i : Fin m) (h : (i : ℕ) < d), T (q i) = T.singularValues i • p ⟨i, h⟩) ∧
        ∀ i : Fin m, d ≤ i → T (q i) = 0 := by
  set q := T.isSymmetric_adjoint_comp_self.eigenvectorBasis finrank_euclideanSpace_fin
  have hT : ∀ i j, ⟪T (q i), T (q j)⟫ = if i = j then T.singularValues j ^ 2 else 0 :=
    lip_inner_apply T
  have hT0 : ∀ i : Fin m, T.singularValues i = 0 → T (q i) = 0 := fun i hi => by
    have := hT i i
    rwa [ite_eq_left rfl, hi, zero_pow two_ne_zero, inner_self_eq_zero] at this
  -- the normalized images of the `q i` with `σ i > 0`
  let v : Fin d → EuclideanSpace ℝ (Fin d) := fun i =>
    if h : (i : ℕ) < m then (T.singularValues i)⁻¹ • T (q ⟨i, h⟩) else 0
  let s : Set (Fin d) := {i | 0 < T.singularValues i}
  have hsm : ∀ i ∈ s, (i : ℕ) < m := fun i hi => by
    by_contra h
    exact (hi : 0 < T.singularValues i).ne'
      (T.singularValues_of_finrank_le (by simpa using h))
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : 0 < T.singularValues i := hi
    simp only [Set.domRestrict_apply, v, dite_eq_left (hsm i hi), dite_eq_left (hsm j hj),
      real_inner_smul_left, real_inner_smul_right, hT, Subtype.mk.injEq, Fin.ext_iff]
    split_ifs with h
    · rw [← h]; field_simp
    · simp
  obtain ⟨p, hp⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨q, p, fun i h => ?_, fun i h => ?_⟩
  · rcases (T.singularValues_nonneg i).eq_or_lt with h0 | h0
    · rw [hT0 i h0.symm, ← h0, zero_smul]
    · rw [hp ⟨i, h⟩ h0]
      simp [v, smul_smul, h0.ne']
  · refine hT0 i (T.singularValues_eq_zero_iff_le_finrank_range.2 ?_)
    exact (Submodule.finrank_le _).trans (by simpa using h)

/-- **Singular value decomposition** of a real `d × m` matrix, in reduced form:
`M = ∑_{i < min d m} σ_i p_i ⊗ q_i` with `σ_0 ≥ σ_1 ≥ … ≥ 0` and orthonormal families `p_i` in `ℝ^d`
and `q_i` in `ℝ^m`. (In the form `M = P Σ Qᵀ`, the `p_i` and `q_i` are the first `min d m` columns
of the orthogonal matrices `P` and `Q`, and `p_i ⊗ q_i = P (e_i ⊗ e_i) Qᵀ`.) -/
theorem exists_singularValueDecomposition (M : Matrix (Fin d) (Fin m) ℝ) :
    ∃ (σ : Fin (min d m) → ℝ) (p : Fin (min d m) → Fin d → ℝ) (q : Fin (min d m) → Fin m → ℝ),
      Antitone σ ∧ (∀ i, 0 ≤ σ i) ∧ (∀ i j, p i ⬝ᵥ p j = if i = j then 1 else 0) ∧
        (∀ i j, q i ⬝ᵥ q j = if i = j then 1 else 0) ∧
        M = ∑ i, σ i • vecMulVec (p i) (q i) := by
  set T := toEuclideanLin M with hTM
  obtain ⟨q, p, h1, h2⟩ := lip_exists_orthonormalBasis T
  let a : Fin (min d m) → Fin d := Fin.castLE (min_le_left d m)
  let b : Fin (min d m) → Fin m := Fin.castLE (min_le_right d m)
  have hp := orthonormal_iff_ite.1 p.orthonormal
  have hq := orthonormal_iff_ite.1 q.orthonormal
  refine ⟨fun i => T.singularValues i, fun i => (p (a i)).ofLp, fun i => (q (b i)).ofLp,
    fun i j hij => T.singularValues_antitone hij, fun i => T.singularValues_nonneg i,
    fun i j => ?_, fun i j => ?_, ?_⟩
  · have := hp (a j) (a i)
    rw [PiLp.inner_apply] at this
    simpa [dotProduct, a, eq_comm] using this
  · have := hq (b j) (b i)
    rw [PiLp.inner_apply] at this
    simpa [dotProduct, b, eq_comm] using this
  · refine toEuclideanLin.injective (q.toBasis.ext fun j => ?_)
    rw [← hTM, OrthonormalBasis.coe_toBasis, map_sum, LinearMap.sum_apply]
    have hterm : ∀ i : Fin (min d m),
        toEuclideanLin (T.singularValues i • vecMulVec (p (a i)).ofLp (q (b i)).ofLp) (q j) =
          if b i = j then T.singularValues i • p (a i) else 0 := fun i => by
      have hij := hq (b i) j
      rw [PiLp.inner_apply] at hij
      have hij' : (q (b i)).ofLp ⬝ᵥ (q j).ofLp = if b i = j then 1 else 0 := by
        rw [← hij]; simp [dotProduct, mul_comm]
      ext c
      rw [map_smul, LinearMap.smul_apply, toLpLin_apply, vecMulVec_mulVec, hij']
      split_ifs <;> simp
    simp only [hterm]
    by_cases h : (j : ℕ) < d
    · rw [h1 j h, Finset.sum_eq_single ⟨j, lt_min h j.2⟩]
      · simp [a, b]
      · intro i _ hi
        refine ite_eq_right fun hbi => absurd (Fin.ext ?_) hi
        simpa [b, Fin.ext_iff] using hbi
      · simp
    · rw [h2 j (not_lt.1 h)]
      refine (Finset.sum_eq_zero fun i _ => ite_eq_right fun hbi => h ?_).symm
      rw [← hbi]
      exact i.2.trans_le (min_le_left d m)

/-- The square of the Frobenius norm is the sum of the squares of the entries. -/
theorem frobenius_norm_sq_eq_sum_sq (M : Matrix (Fin d) (Fin m) ℝ) :
    ‖M‖ ^ 2 = ∑ i, ∑ j, M i j ^ 2 := by
  rw [frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp

/-- For orthonormal families `p_i` and `q_i`, the matrices `σ_i p_i ⊗ q_i` are orthogonal for the
Frobenius inner product and have norm `|σ_i|`: `|∑_{i ∈ s} σ_i p_i ⊗ q_i|² = ∑_{i ∈ s} σ_i²`. -/
theorem frobenius_norm_sq_sum_smul_vecMulVec {ι : Type*} [DecidableEq ι] (σ : ι → ℝ)
    {p : ι → Fin d → ℝ} {q : ι → Fin m → ℝ}
    (hp : ∀ i j, p i ⬝ᵥ p j = if i = j then 1 else 0)
    (hq : ∀ i j, q i ⬝ᵥ q j = if i = j then 1 else 0) (s : Finset ι) :
    ‖∑ i ∈ s, σ i • vecMulVec (p i) (q i)‖ ^ 2 = ∑ i ∈ s, σ i ^ 2 := by
  have h : ∀ i j, ∑ a, ∑ b, σ i * (p i a * q i b) * (σ j * (p j a * q j b)) =
      if i = j then σ i ^ 2 else 0 := fun i j => by
    have e : ∑ a, ∑ b, σ i * (p i a * q i b) * (σ j * (p j a * q j b)) =
        σ i * σ j * ((p i ⬝ᵥ p j) * (q i ⬝ᵥ q j)) := by
      rw [dotProduct, dotProduct, sum_mul_sum, mul_sum]
      refine sum_congr rfl fun a _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun b _ => by ring
    rw [e, hp, hq]
    split_ifs with hij
    · rw [hij]; ring
    · ring
  rw [frobenius_norm_sq_eq_sum_sq]
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, sq, sum_mul_sum]
  rw [sum_congr rfl fun a _ => sum_comm, sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [sum_congr rfl fun a _ => sum_comm, sum_comm, sum_congr rfl fun j _ => h i j]
  rw [sum_ite_eq, ite_eq_left hi, sq]

end Matrix
