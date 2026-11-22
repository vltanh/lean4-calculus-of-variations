/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Quasiconvex.Laminate

/-!
# A quasiconvex integrand is rank-one convex

`rankOneConvex_of_quasiconvex`: a lower semicontinuous, locally bounded `f` that is quasiconvex
on the unit cube at every matrix is rank-one convex.

The proof is the one of S. Müller, *Variational models for microstructure and phase transitions*,
lecture notes, MPI MiS Leipzig, 1998, Lemma 4.3: laminates on a cube with faces orthogonal to the
rank-one direction (`Quasiconvex.Laminate`) give the two-point inequality
`f (A) ≤ λ f (A + (1 − λ) a ⊗ n) + (1 − λ) f (A − λ a ⊗ n)` in every rank-one direction `a ⊗ n`
(`le_of_quasiconvexAtOn_vecMulVec`; the passage from the unit cube to the rotated cube is the
independence of the domain, `quasiconvexAtOn_iff`), and this inequality at every matrix is the
convexity of `f` along every rank-one line.
-/

@[expose] public section

open Set

namespace CalculusOfVariations

variable {d m : ℕ}

/-- A function satisfying the two-point convexity inequality is convex. -/
private lemma rd_convex_of_two_point {g : ℝ → ℝ}
    (h : ∀ x y l : ℝ, 0 < l → l < 1 → g (l * x + (1 - l) * y) ≤ l * g x + (1 - l) * g y) :
    ConvexOn ℝ univ g := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  simp only [smul_eq_mul]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp
  rcases eq_or_lt_of_le hb with hb0 | hb'
  · have : a = 1 := by linarith
    subst this; simp
  · exact h x y a ha' (by linarith)

/-- Convexity along the line `t ↦ A₀ + t B` from the two-point inequality in the directions
`c B`. -/
private lemma rd_convex_line {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (A₀ B : Matrix (Fin d) (Fin m) ℝ)
    (h2 : ∀ (P : Matrix (Fin d) (Fin m) ℝ) (c l : ℝ), 0 < l → l < 1 →
      f P ≤ l * f (P + (1 - l) • (c • B)) + (1 - l) * f (P - l • (c • B))) :
    ConvexOn ℝ univ (fun t : ℝ => f (A₀ + t • B)) := by
  apply rd_convex_of_two_point
  intro x y l hl0 hl1
  have := h2 (A₀ + (l * x + (1 - l) * y) • B) (x - y) l hl0 hl1
  rwa [show A₀ + (l * x + (1 - l) * y) • B + (1 - l) • ((x - y) • B) = A₀ + x • B by module,
    show A₀ + (l * x + (1 - l) * y) • B - l • ((x - y) • B) = A₀ + y • B by module] at this

/-- A matrix of rank one is `a ⊗ q`. -/
private lemma rd_rank_one_eq {B : Matrix (Fin d) (Fin m) ℝ} (hB : B.rank = 1) :
    ∃ (a : Fin d → ℝ) (q : Fin m → ℝ), B = Matrix.vecMulVec a q := by
  rw [Matrix.rank_eq_finrank_span_cols] at hB
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.1 hB
  choose c hc using fun k : Fin m => hv ⟨B.col k, Submodule.subset_span ⟨k, rfl⟩⟩
  refine ⟨(v : Fin d → ℝ), c, ?_⟩
  ext i k
  have h1 : ((c k • v : Submodule.span ℝ (Set.range B.col)) : Fin d → ℝ) i = B i k :=
    congrArg (fun w : Submodule.span ℝ (Set.range B.col) => (w : Fin d → ℝ) i) (hc k)
  rw [Matrix.vecMulVec_apply, ← h1, mul_comm]
  rfl

/-- **A quasiconvex integrand is rank-one convex** (S. Müller, *Variational models for
microstructure and phase transitions*, lecture notes, MPI MiS Leipzig, 1998, Lemma 4.3): a lower
semicontinuous, locally bounded `f` that is quasiconvex on the unit cube at every matrix is
rank-one convex.

Proof: a rank-one matrix is `a ⊗ q` (`rd_rank_one_eq`). At every matrix `P`, Müller's laminates on
a cube with faces orthogonal to `q` give
`f (P) ≤ λ f (P + (1 − λ) (c a) ⊗ q) + (1 − λ) f (P − λ (c a) ⊗ q)` for every `c ∈ ℝ` and
`λ ∈ (0, 1)` (`le_of_quasiconvexAtOn_vecMulVec`, from quasiconvexity at `P` on the unit cube and
the independence of the domain for the rotated cube); this two-point inequality along the line
`t ↦ A + t a ⊗ q` is its convexity (`rd_convex_line`). -/
theorem rankOneConvex_of_quasiconvex {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) (hf : Quasiconvex f) :
    RankOneConvex f := by
  intro A B hB
  obtain ⟨a, q, rfl⟩ := rd_rank_one_eq hB
  refine rd_convex_line _ _ fun P c l hl0 hl1 => ?_
  rw [show c • Matrix.vecMulVec a q = Matrix.vecMulVec (c • a) q by
    ext i k; simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    ring]
  exact le_of_quasiconvexAtOn_vecMulVec hlsc hbdd (hf P) (c • a) q hl0 hl1

end CalculusOfVariations
