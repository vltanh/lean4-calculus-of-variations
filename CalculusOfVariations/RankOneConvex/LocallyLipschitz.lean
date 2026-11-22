/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Basic
public import CalculusOfVariations.Convex.SeparatelyConvex
public import CalculusOfVariations.RankOneConvex.SingularValues

/-!
# Rank-one convex functions are locally Lipschitz

A real-valued rank-one convex `f : ℝ^{d×m} → ℝ` is locally Lipschitz
(`RankOneConvex.locallyLipschitz`), with the quantitative bound

  `|f (A) − f (B)| ≤ √(min d m) · osc (f; B̄_{6r} (F)) / (3r) · |A − B|`  for `A, B ∈ B_r (F)`

in the Frobenius norm `|·|` (`RankOneConvex.abs_sub_le_of_osc`). This is Lemma 5.9 of F. Rindler,
*Calculus of Variations*, 2nd ed., Graduate Texts in Mathematics 310, Springer, 2026 ([R2]),
pp. 114–115, the bound being its (5.9), with the proof given there. [R2] (Notes to Chapter 5,
p. 124) attributes the result to Morrey and the proof to J. M. Ball, B. Kirchheim, J. Kristensen,
*Regularity of quasiconvex envelopes*, Calc. Var. Partial Differential Equations 11 (2000), 333–359,
Lemma 2.2. Lemma 5.6 of the first edition (2018) is, by content, Lemma 5.9 of the second edition;
the first edition was not consulted.

The proof (in [R2] the matrices are `m × d`):

* *Local boundedness* (`lip_exists_abs_le`). In [R2] it is part of the definition of rank-one
  convexity (p. 110), which also asks for Borel measurability; p. 111 remarks that local boundedness
  is automatic and refers to the proof of Lemma 2.3 of B. Kirchheim, J. Kristensen, *On rank-one
  convex functions that are homogeneous of degree one*, Arch. Ration. Mech. Anal. 221 (2016),
  527–558. `RankOneConvex` has neither clause, so this step fills a gap: `f` is convex in each entry
  (the matrix units have rank one), hence bounded above on a cube by its values at the vertices and
  below by reflection in one entry at a time, similar to the averaging over the sign flips of the
  entries in the proof of [R2], Lemma 5.8 (`Matrix.exists_abs_le_of_convexOn_single`).
* *Rank-one lines*, (5.10) (`lip_sub_le_of_rank_le_one`, `lip_abs_sub_le_of_rank_le_one`). Let
  `A, B ∈ B_r (F)` with `rank (A − B) ≤ 1`, `A ≠ B`, and let `X` be a point where the ray from `B`
  through `A` meets `∂B_{2r} (F)`; `X` lies beyond `A`, and `|X − B| ≥ r`. Convexity along the ray
  gives `(f (A) − f (B)) / |A − B| ≤ (f (X) − f (B)) / |X − B| ≤ osc (f; B̄_{2r} (F)) / r`, and the
  exchange of `A` and `B` the bound for `|f (A) − f (B)|`. In [R2] the chain (5.10) has the absolute
  values `|f (A) − f (B)|` and `|f (X) − f (B)|`. Then its first inequality holds when
  `f (B) ≤ f (A)`, but not in general, as convexity bounds the slope only from above: for
  `f (t) = max (1 − t, 0)` (`d = m = 1`), `B = 0`, `A = 1`, `X > 1` it reads `1 ≤ 1 / X`. When
  `f (A) < f (B)`, `A` and `B` have to be exchanged.
* *General `A, B`*, (5.9) (`RankOneConvex.abs_sub_le_of_osc`). By the singular value decomposition
  (`Matrix.exists_singularValueDecomposition`; [R2], Appendix A.1), `B − A = ∑ σ_i p_i ⊗ q_i`
  (`p_i = P e_i`, `q_i = Q e_i`). Put `A_k = A + ∑_{i < k} σ_i p_i ⊗ q_i`, from `A_0 = A` to
  `A_{min d m} = B`. The summands are Frobenius orthogonal
  (`Matrix.frobenius_norm_sq_sum_smul_vecMulVec`; (A.1) of [R2]), so
  `|A_k − F| ≤ |A − F| + (∑_{i < k} σ_i²)^{1/2} ≤ |A − F| + |B − A| < 3r` and
  `∑ |A_k − A_{k+1}|² = |A − B|²`. Apply (5.10) to `A_k, A_{k+1} ∈ B_{3r} (F)`, sum over `k` and use
  the Cauchy–Schwarz inequality.
* *Conclusion* (`RankOneConvex.locallyLipschitz`). By the local boundedness the oscillation is
  finite, and `|·|_∞ ≤ |·| ≤ √(d m) |·|_∞` (`lip_dist_le_frobenius`, `lip_frobenius_le_dist`)
  gives the statement for the product metric.

The estimate (5.8) of [R2] for functions of `p`-growth, the second part of its Lemma 5.9, is not
included, nor is the better constant `√(min d m) · osc (f; B̄_{2r} (F)) / r` of its Remark 5.10.
-/

@[expose] public section

open Metric Set Matrix
open scoped Matrix.Norms.Frobenius

namespace CalculusOfVariations

variable {d m : ℕ}

private lemma rank_eq_zero_imp {A : Matrix (Fin d) (Fin m) ℝ} (h : A.rank = 0) : A = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  ext i j
  have := congrArg (fun F => F (Pi.single j 1) i) h
  simpa [Matrix.mulVecLin_apply] using this

private lemma rank_single_one (i : Fin d) (j : Fin m) : (Matrix.single i j (1 : ℝ)).rank = 1 := by
  apply le_antisymm
  · rw [Matrix.single_eq_single_vecMulVec_single]; exact Matrix.rank_vecMulVec_le _ _
  · rw [Nat.one_le_iff_ne_zero]; intro h
    have := congrArg (fun M => M i j) (rank_eq_zero_imp h)
    simp at this

/-- [R2], Lemma 5.9, (5.10), without absolute values: if `osc (f; B̄_{2r} (F)) ≤ ω`, then
`f (A) − f (B) ≤ (ω / r) |A − B|` for `A, B ∈ B_r (F)` with `rank (A − B) ≤ 1`, by convexity along
the ray from `B` through `A`, up to a point `X` of the sphere `∂B_{2r} (F)`. -/
private lemma lip_sub_le_of_rank_le_one {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : RankOneConvex f)
    {F : Matrix (Fin d) (Fin m) ℝ} {r ω : ℝ} (hr : 0 < r)
    (hω : ∀ A ∈ closedBall F (2 * r), ∀ B ∈ closedBall F (2 * r), |f A - f B| ≤ ω)
    {A B : Matrix (Fin d) (Fin m) ℝ} (hA : A ∈ ball F r) (hB : B ∈ ball F r)
    (hAB : (A - B).rank ≤ 1) : f A - f B ≤ ω / r * ‖A - B‖ := by
  by_cases hne : A = B
  · simp [hne]
  have hrank : (A - B).rank = 1 := le_antisymm hAB
    (Nat.one_le_iff_ne_zero.2 fun h => hne (sub_eq_zero.1 (rank_eq_zero_imp h)))
  have hn : 0 < ‖A - B‖ := norm_sub_pos_iff.2 hne
  rw [mem_ball, dist_eq_norm] at hA hB
  have hn2 : ‖A - B‖ < 2 * r := by
    have := norm_sub_le_norm_sub_add_norm_sub A F B
    rw [norm_sub_rev F B] at this
    linarith
  -- the point `X = B + τ (A - B)` with `|X - F| = 2 r`
  obtain ⟨τ, hτ, hX⟩ : ∃ τ ∈ Icc 1 (3 * r / ‖A - B‖), ‖B + τ • (A - B) - F‖ = 2 * r := by
    have hcont : Continuous fun t : ℝ => ‖B + t • (A - B) - F‖ := by fun_prop
    refine intermediate_value_Icc ((one_le_div hn).2 (by linarith)) hcont.continuousOn ⟨?_, ?_⟩
    · rw [one_smul, add_sub_cancel]
      linarith
    · have h1 : ‖(3 * r / ‖A - B‖) • (A - B)‖ = 3 * r := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hn.ne']
      have h2 := norm_sub_norm_le ((3 * r / ‖A - B‖) • (A - B)) (F - B)
      rw [h1, norm_sub_rev F B] at h2
      rw [show B + (3 * r / ‖A - B‖) • (A - B) - F = (3 * r / ‖A - B‖) • (A - B) - (F - B) by abel]
      linarith
  have hτ0 : 0 < τ := one_pos.trans_le hτ.1
  -- the distance from `B` to `X`
  have hXB : r ≤ τ * ‖A - B‖ := by
    have h1 := norm_sub_le_norm_sub_add_norm_sub (B + τ • (A - B)) B F
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ0.le, hX] at h1
    linarith
  -- convexity along the ray
  have hconv := (hf B (A - B) hrank).secant_mono (mem_univ 0) (mem_univ 1) (mem_univ τ) one_ne_zero
    hτ0.ne' hτ.1
  simp only [one_smul, zero_smul, add_zero, sub_zero, div_one, add_sub_cancel] at hconv
  have hosc : f (B + τ • (A - B)) - f B ≤ ω :=
    (le_abs_self _).trans (hω _ (by rw [mem_closedBall, dist_eq_norm, hX]) _
      (by rw [mem_closedBall, dist_eq_norm]; linarith))
  have hω0 : 0 ≤ ω := (abs_nonneg _).trans
    (hω F (mem_closedBall_self (by linarith)) F (mem_closedBall_self (by linarith)))
  calc f A - f B ≤ (f (B + τ • (A - B)) - f B) / τ := hconv
    _ ≤ ω / τ := by gcongr
    _ ≤ ω / r * ‖A - B‖ := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hτ0 hr]
      calc ω * r ≤ ω * (τ * ‖A - B‖) := by gcongr
        _ = ω * ‖A - B‖ * τ := by ring

/-- [R2], Lemma 5.9, (5.10): if `osc (f; B̄_{2r} (F)) ≤ ω`, then
`|f (A) − f (B)| ≤ (ω / r) |A − B|` for `A, B ∈ B_r (F)` with `rank (A − B) ≤ 1`, from
`lip_sub_le_of_rank_le_one` by exchanging `A` and `B`. -/
private lemma lip_abs_sub_le_of_rank_le_one {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : RankOneConvex f) {F : Matrix (Fin d) (Fin m) ℝ} {r ω : ℝ} (hr : 0 < r)
    (hω : ∀ A ∈ closedBall F (2 * r), ∀ B ∈ closedBall F (2 * r), |f A - f B| ≤ ω)
    {A B : Matrix (Fin d) (Fin m) ℝ} (hA : A ∈ ball F r) (hB : B ∈ ball F r)
    (hAB : (A - B).rank ≤ 1) : |f A - f B| ≤ ω / r * ‖A - B‖ := by
  refine abs_sub_le_iff.2 ⟨lip_sub_le_of_rank_le_one hf hr hω hA hB hAB, ?_⟩
  rw [norm_sub_rev]
  refine lip_sub_le_of_rank_le_one hf hr hω hB hA ?_
  rw [← neg_sub, ← Matrix.one_mul (A - B), ← Matrix.neg_mul]
  exact (Matrix.rank_mul_le_right _ _).trans hAB

/-- **The Lipschitz bound of a rank-one convex function by its oscillation** ([R2], Lemma 5.9,
(5.9); see the module docstring for the proof): in the Frobenius norm, if `|f (A) − f (B)| ≤ ω` for
all `A, B` in the closed ball `B̄_{6r} (F)`, that is `osc (f; B̄_{6r} (F)) ≤ ω`, then `f` is
Lipschitz on the ball `B_r (F)` with the constant `√(min d m) ω / (3r)`. -/
theorem RankOneConvex.abs_sub_le_of_osc {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : RankOneConvex f)
    {F : Matrix (Fin d) (Fin m) ℝ} {r ω : ℝ} (hr : 0 < r)
    (hω : ∀ A ∈ closedBall F (6 * r), ∀ B ∈ closedBall F (6 * r), |f A - f B| ≤ ω)
    {A B : Matrix (Fin d) (Fin m) ℝ} (hA : A ∈ ball F r) (hB : B ∈ ball F r) :
    |f A - f B| ≤ √(min d m : ℕ) * (ω / (3 * r)) * ‖A - B‖ := by
  obtain ⟨σ, p, q, -, -, hp, hq, hM⟩ := exists_singularValueDecomposition (B - A)
  let R : Fin (min d m) → Matrix (Fin d) (Fin m) ℝ := fun i => σ i • vecMulVec (p i) (q i)
  have hR : ∀ s : Finset (Fin (min d m)), ‖∑ i ∈ s, R i‖ ^ 2 = ∑ i ∈ s, σ i ^ 2 :=
    frobenius_norm_sq_sum_smul_vecMulVec σ hp hq
  have hR1 : ∀ i, ‖R i‖ ^ 2 = σ i ^ 2 := fun i => by simpa using hR {i}
  have hBA : ‖A - B‖ ^ 2 = ∑ i, σ i ^ 2 := by rw [norm_sub_rev, hM]; exact hR Finset.univ
  rw [mem_ball, dist_eq_norm] at hA hB
  have hAB : ‖A - B‖ < 2 * r := by
    have := norm_sub_le_norm_sub_add_norm_sub A F B
    rw [norm_sub_rev F B] at this
    linarith
  have hω0 : 0 ≤ ω := (abs_nonneg _).trans
    (hω F (mem_closedBall_self (by linarith)) F (mem_closedBall_self (by linarith)))
  -- the path `A_k = A + ∑_{i < k} σ_i p_i ⊗ q_i` from `A` to `B`
  let s : ℕ → Finset (Fin (min d m)) := fun k => Finset.univ.filter fun i => (i : ℕ) < k
  let S : ℕ → Matrix (Fin d) (Fin m) ℝ := fun k => A + ∑ i ∈ s k, R i
  have hS0 : S 0 = A := by simp [S, s]
  have hSn : S (min d m) = B := by
    have : s (min d m) = Finset.univ := Finset.filter_true_of_mem fun i _ => i.2
    simp only [S, this]
    rw [← hM, add_sub_cancel]
  have hSs : ∀ i : Fin (min d m), S (i + 1) - S i = R i := fun i => by
    have h : s (i + 1) = insert i (s i) := by
      ext j
      simp only [s, Finset.mem_filter_univ, Finset.mem_insert, Fin.ext_iff]
      omega
    simp only [S]
    rw [h, Finset.sum_insert (by simp [s])]
    abel
  have hSmem : ∀ k, S k ∈ ball F (3 * r) := fun k => by
    have h1 : ‖∑ i ∈ s k, R i‖ ≤ ‖A - B‖ := by
      refine le_of_sq_le_sq ?_ (norm_nonneg _)
      rw [hR, hBA]
      exact Finset.sum_le_univ_sum_of_nonneg fun i => sq_nonneg _
    have h2 := norm_add_le (A - F) (∑ i ∈ s k, R i)
    rw [mem_ball, dist_eq_norm, show S k - F = A - F + ∑ i ∈ s k, R i by
      simp only [S]; abel]
    linarith
  have hstep : ∀ i : Fin (min d m), |f (S (i + 1)) - f (S i)| ≤ ω / (3 * r) * ‖R i‖ := fun i => by
    rw [← hSs i]
    refine lip_abs_sub_le_of_rank_le_one hf (by linarith) ?_ (hSmem _) (hSmem _) ?_
    · rwa [show 2 * (3 * r) = 6 * r by ring]
    · rw [hSs i]
      simp only [R]
      rw [← smul_vecMulVec]
      exact rank_vecMulVec_le _ _
  have hCS : ∑ i, ‖R i‖ ≤ √(min d m : ℕ) * ‖A - B‖ := by
    have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin (min d m) => 1) fun i => ‖R i‖
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, hR1, ← hBA, Real.sqrt_sq (norm_nonneg _)] using this
  calc |f A - f B| = |f (S (min d m)) - f (S 0)| := by rw [hS0, hSn, abs_sub_comm]
    _ = |∑ i : Fin (min d m), (f (S (i + 1)) - f (S i))| := by
      rw [← Finset.sum_range_sub (fun k => f (S k)), Finset.sum_range]
    _ ≤ ∑ i : Fin (min d m), |f (S (i + 1)) - f (S i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ω / (3 * r) * ‖R i‖ := Finset.sum_le_sum fun i _ => hstep i
    _ = ω / (3 * r) * ∑ i, ‖R i‖ := by rw [Finset.mul_sum]
    _ ≤ ω / (3 * r) * (√(min d m : ℕ) * ‖A - B‖) := by gcongr
    _ = √(min d m : ℕ) * (ω / (3 * r)) * ‖A - B‖ := by ring

/-- `|·|_∞ ≤ |·|`: the product metric is at most the Frobenius distance. -/
private lemma lip_dist_le_frobenius (y z : Fin d → Fin m → ℝ) :
    dist y z ≤ ‖Matrix.of y - Matrix.of z‖ := by
  refine (dist_pi_le_iff (norm_nonneg _)).2 fun i => (dist_pi_le_iff (norm_nonneg _)).2 fun j => ?_
  rw [dist_eq_norm]
  exact norm_apply_le_frobenius_norm (Matrix.of y - Matrix.of z) i j

/-- `|·| ≤ √(d m) |·|_∞`: the Frobenius distance is at most `√(d m)` times the product metric. -/
private lemma lip_frobenius_le_dist (y z : Fin d → Fin m → ℝ) :
    ‖Matrix.of y - Matrix.of z‖ ≤ √(d * m) * dist y z := by
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [frobenius_norm_sq_eq_sum_sq, mul_pow, Real.sq_sqrt (by positivity)]
  calc ∑ i, ∑ j, (Matrix.of y - Matrix.of z) i j ^ 2
      ≤ ∑ _i : Fin d, ∑ _j : Fin m, dist y z ^ 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => sq_le_sq.2 ?_
        rw [abs_of_nonneg dist_nonneg, Matrix.sub_apply, Matrix.of_apply, Matrix.of_apply,
          ← Real.dist_eq]
        exact (dist_le_pi_dist (y i) (z i) j).trans (dist_le_pi_dist y z i)
    _ = d * m * dist y z ^ 2 := by simp [mul_assoc]

/-- A rank-one convex function is bounded on every closed ball of the Frobenius norm: it is convex
in each entry, so `Matrix.exists_abs_le_of_convexOn_single` applies. -/
private lemma lip_exists_abs_le {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : RankOneConvex f)
    (F : Matrix (Fin d) (Fin m) ℝ) (R : ℝ) : ∃ K, ∀ A ∈ closedBall F R, |f A| ≤ K := by
  obtain ⟨K, hK⟩ := exists_abs_le_of_convexOn_single (fun A i j => hf A _ (rank_single_one i j))
    (Matrix.of.symm F) R
  refine ⟨K, fun A hA => hK (Matrix.of.symm A) ?_⟩
  rw [mem_closedBall, dist_eq_norm] at hA
  exact (lip_dist_le_frobenius _ _).trans hA

/-- **A rank-one convex function is locally Lipschitz** ([R2], Lemma 5.9): every real-valued
rank-one convex `f : ℝ^{d×m} → ℝ` is locally Lipschitz (`Matrix.of` identifies `ℝ^{d×m}` with
`Fin d → Fin m → ℝ`, with its product metric). No regularity of `f` is assumed.

Proof: `f` is bounded on Frobenius balls (`lip_exists_abs_le`), so its oscillation is finite there,
and `RankOneConvex.abs_sub_le_of_osc` with `r = 1` gives a Lipschitz bound on the unit ball at every
matrix, in the Frobenius norm, which is equivalent to the norm of the product metric; see the module
docstring. -/
theorem RankOneConvex.locallyLipschitz {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : RankOneConvex f) :
    LocallyLipschitz fun X : Fin d → Fin m → ℝ => f (Matrix.of X) := by
  intro x
  obtain ⟨K, hK⟩ := lip_exists_abs_le hf (Matrix.of x) (6 * 1)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK _ (mem_closedBall_self (by norm_num)))
  have hω : ∀ A ∈ closedBall (Matrix.of x) (6 * 1), ∀ B ∈ closedBall (Matrix.of x) (6 * 1),
      |f A - f B| ≤ 2 * K := fun A hA B hB => by
    linarith [abs_sub (f A) (f B), hK A hA, hK B hB]
  have hball : ∀ y ∈ ball x (1 / (√(d * m) + 1)), Matrix.of y ∈ ball (Matrix.of x) 1 := by
    intro y hy
    rw [mem_ball, dist_eq_norm]
    refine (lip_frobenius_le_dist y x).trans_lt ?_
    rw [mem_ball, lt_div_iff₀ (by positivity)] at hy
    nlinarith [dist_nonneg (x := y) (y := x)]
  refine ⟨(√(min d m : ℕ) * (2 * K / (3 * 1)) * √(d * m)).toNNReal, ball x (1 / (√(d * m) + 1)),
    ball_mem_nhds x (by positivity), LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_⟩
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity), mul_assoc]
  exact (hf.abs_sub_le_of_osc one_pos hω (hball y hy) (hball z hz)).trans
    (mul_le_mul_of_nonneg_left (lip_frobenius_le_dist y z) (by positivity))

end CalculusOfVariations
