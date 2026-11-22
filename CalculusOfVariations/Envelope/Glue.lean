/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Envelope.Cube
public import CalculusOfVariations.Lipschitz.PiecewiseAffine
public import CalculusOfVariations.Quasiconvex.Laminate

/-!
# The infimum formula and piecewise affine test maps

For a continuous `f`, with `cubeInf f` the infimum formula on the unit cube:

* `cubeInf_le_sum_of_piecewiseAffine`: for a Lipschitz `ψ` vanishing off the unit cube `Q` and
  affine on the pieces `P i` of a finite partition of `Q` up to a null set,
  `cubeInf f (F) ≤ ∑ i |P i| cubeInf f (F + ∇ (L i))`, that is,
  `⨍_Q cubeInf f (F + ∇ψ) ≥ cubeInf f (F)`. This is (4.28) of S. Müller, *Variational models for
  microstructure and phase transitions*, lecture notes, MPI MiS Leipzig, 1998, §4.8. Müller inserts
  in each piece an almost minimiser of the infimum formula on that piece, which does not depend on
  the domain; here the same step is done with the covering inline: finitely many disjoint small
  cubes fill the piece up to `ε` (`cv_exists_finite_cover`), and rescaled almost minimisers for
  `cubeInf f (F + ∇ (L i))` are inserted in them (`rescaleMap`). The value `−∞` is allowed;
* `cubeLaminate_piecewiseAffineOn`: the laminates of `Quasiconvex.Laminate` are piecewise affine on
  the cube;
* `cubeInf_le_two_point`: hence, with the laminates and `|{∇v_k ≠ ∇u_k}| → 0`, the two-point
  inequality of `cubeInf f` along `a ⊗ e_j` (Müller 1998, §4.8, with Lemma 4.3).

The results are stated with `sorry` proofs, to be proved.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

namespace CalculusOfVariations

variable {d m : ℕ}

/-- **The quasiconvexity inequality of the infimum formula for piecewise affine test maps**
(Müller 1998, (4.28)): for a Lipschitz `ψ` vanishing off the unit cube and agreeing with the affine
map `L i` on the open set `P i`, where the `P i ⊆ Q` are pairwise disjoint and cover `Q` up to a
null set, `cubeInf f (F) ≤ ∑ i |P i| cubeInf f (F + ∇ (L i))` (in `EReal`). -/
theorem cubeInf_le_sum_of_piecewiseAffine {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (F : Matrix (Fin d) (Fin m) ℝ) {n : ℕ} (P : Fin n → Set (Fin m → ℝ))
    (L : Fin n → (Fin m → ℝ) →ᵃ[ℝ] (Fin d → ℝ)) (hPo : ∀ i, IsOpen (P i))
    (hPd : Pairwise (Function.onFun Disjoint P)) (hPQ : ∀ i, P i ⊆ unitCube m)
    (hcov : volume (unitCube m \ ⋃ i, P i) = 0) {ψ : (Fin m → ℝ) → Fin d → ℝ}
    (hψ : ∃ K, LipschitzWith K ψ) (hψ0 : ∀ x ∉ unitCube m, ψ x = 0)
    (hψL : ∀ i, ∀ x ∈ P i, ψ x = L i x) :
    cubeInf f F ≤
      ∑ i, ((volume (P i)).toReal : EReal) * cubeInf f (F + LinearMap.toMatrix' (L i).linear) := by
  sorry

/-- The laminate `v_k` of `Quasiconvex.Laminate` is piecewise affine on the unit cube: the
sawtooth is affine between the points of `k⁻¹ (ℤ ∪ (ℤ + λ))`, the distance to the boundary is
affine on each of the `2 m` pyramids over the faces, and the minimum of two affine maps is affine
on each side of a hyperplane. -/
theorem cubeLaminate_piecewiseAffineOn (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (hl0 : 0 < l)
    (hl1 : l < 1) {k : ℕ} (hk : 0 < k) :
    PiecewiseAffineOn (unitCube m) (cubeLaminate a j l k) := by
  sorry

/-- **The two-point inequality of the infimum formula** (Müller 1998, §4.8, with Lemma 4.3): for
continuous `f`,
`cubeInf f (F) ≤ λ cubeInf f (F + (1 − λ) a ⊗ e_j) + (1 − λ) cubeInf f (F − λ a ⊗ e_j)` (in
`EReal`), from `cubeInf_le_sum_of_piecewiseAffine` applied to the laminates `v_k`. -/
theorem cubeInf_le_two_point {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (F : Matrix (Fin d) (Fin m) ℝ) (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (hl0 : 0 < l)
    (hl1 : l < 1) :
    cubeInf f F ≤ (l : EReal) * cubeInf f (F + (1 - l) • Matrix.vecMulVec a (Pi.single j 1)) +
      ((1 - l : ℝ) : EReal) * cubeInf f (F - l • Matrix.vecMulVec a (Pi.single j 1)) := by
  sorry

end CalculusOfVariations
