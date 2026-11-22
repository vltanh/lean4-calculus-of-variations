/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Basic
public import CalculusOfVariations.Convex.SeparatelyConvex

/-!
# Rank-one convex functions are locally Lipschitz

A real-valued rank-one convex `f : ℝ^{d×m} → ℝ` is locally Lipschitz
(`RankOneConvex.locallyLipschitz`): it is convex along every matrix unit `E_{ij}`, a matrix of rank
one, and a separately convex function is locally Lipschitz
(`Matrix.locallyLipschitz_of_convexOn_single`).
-/

@[expose] public section

open Metric Set MeasureTheory Filter Topology
open scoped Pointwise

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

/-- **A rank-one convex function is locally Lipschitz**: every real-valued rank-one convex
`f : ℝ^{d×m} → ℝ` is locally Lipschitz (`Matrix.of` identifies `ℝ^{d×m}` with
`Fin d → Fin m → ℝ`, with its product metric). No regularity of `f` is assumed.

Proof: `f` is convex along every coordinate direction `E_{ij}`, a matrix of rank one, and a function
convex in each entry is locally Lipschitz (`Matrix.locallyLipschitz_of_convexOn_single`: bounds
above at the vertices of a cube and below by reflection, a Lipschitz bound along each coordinate
line, and a path that changes one entry at a time); see S. Müller, *Variational models for
microstructure and phase transitions*, lecture notes, MPI MiS Leipzig, 1998, Definition 4.2, Remark
3. -/
theorem RankOneConvex.locallyLipschitz {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : RankOneConvex f) :
    LocallyLipschitz fun X : Fin d → Fin m → ℝ => f (Matrix.of X) :=
  Matrix.locallyLipschitz_of_convexOn_single fun A i j => hf A _ (rank_single_one i j)

end CalculusOfVariations
