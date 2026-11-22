/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Piecewise affine maps and Kuhn–Freudenthal interpolation

* `PiecewiseAffineOn U φ`: `φ` agrees with an affine map on each of finitely many pairwise
  disjoint open subsets of `U` that cover `U` up to a null set;
* `kuhnInterpolation k ψ`: the piecewise affine interpolation of `ψ` on the Kuhn–Freudenthal
  triangulation of the grid `k⁻¹ ℤ^m` (H. Freudenthal, Ann. of Math. 43 (1942); H. W. Kuhn,
  1960), in the closed form `I_k ψ (x) = ∫_0^1 ψ (k⁻¹ ⌈k x − t 𝟙⌉) dt` (ceiling coordinatewise).
  For `x` in the open simplex `{⌊k x⌋ = a, fractional parts of k x ordered by σ}` the nodes
  `k⁻¹ ⌈k x − t 𝟙⌉` run through the vertices of that simplex, with weights the barycentric
  coordinates of `x`, so `I_k ψ` is the affine interpolant of the values of `ψ` at the vertices.

Properties: `I_k ψ` is `m K`-Lipschitz for `K`-Lipschitz `ψ` (since
`∫_0^1 |⌈u − t⌉ − ⌈u' − t⌉| dt = |u − u'|`), vanishes off the unit cube when `ψ` does,
is piecewise affine on the unit cube (`k ≥ 1`), and `∇ I_k ψ → ∇ψ` almost everywhere: at a point
of differentiability of `ψ` on no grid hyperplane, the gradient of `I_k ψ` is a vector of
difference quotients of `ψ` along edges of length `k⁻¹` of a simplex containing the point.

The results are stated with `sorry` proofs, to be proved.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace CalculusOfVariations

variable {d m : ℕ}

/-- `φ` is piecewise affine on `U`: there are finitely many pairwise disjoint open sets `P i ⊆ U`,
covering `U` up to a null set, on each of which `φ` agrees with an affine map `L i`. -/
def PiecewiseAffineOn (U : Set (Fin m → ℝ)) (φ : (Fin m → ℝ) → Fin d → ℝ) : Prop :=
  ∃ (n : ℕ) (P : Fin n → Set (Fin m → ℝ)) (L : Fin n → (Fin m → ℝ) →ᵃ[ℝ] (Fin d → ℝ)),
    (∀ i, IsOpen (P i)) ∧ Pairwise (Function.onFun Disjoint P) ∧ (∀ i, P i ⊆ U) ∧
      volume (U \ ⋃ i, P i) = 0 ∧ ∀ i, ∀ x ∈ P i, φ x = L i x

/-- The Kuhn–Freudenthal interpolation of `ψ` on the grid `k⁻¹ ℤ^m`:
`I_k ψ (x) = ∫_0^1 ψ (k⁻¹ ⌈k x − t 𝟙⌉) dt`, the ceiling taken coordinatewise. -/
noncomputable def kuhnInterpolation (k : ℕ) (ψ : (Fin m → ℝ) → Fin d → ℝ) (x : Fin m → ℝ) :
    Fin d → ℝ :=
  ∫ t in (0 : ℝ)..1, ψ (fun i => (k : ℝ)⁻¹ * ⌈(k : ℝ) * x i - t⌉)

/-- The interpolation of a `K`-Lipschitz map is `m K`-Lipschitz (sup norms). -/
theorem kuhnInterpolation_lipschitz {ψ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hψ : LipschitzWith K ψ) (k : ℕ) : LipschitzWith (m * K) (kuhnInterpolation k ψ) := by
  sorry

/-- The interpolation of a map vanishing off the unit cube vanishes off the unit cube. -/
theorem kuhnInterpolation_eq_zero {ψ : (Fin m → ℝ) → Fin d → ℝ}
    (hψ : ∀ x ∉ unitCube m, ψ x = 0) (k : ℕ) :
    ∀ x ∉ unitCube m, kuhnInterpolation k ψ x = 0 := by
  sorry

/-- The interpolation is piecewise affine on the unit cube: affine on each of the finitely many
open Kuhn simplices of the grid `k⁻¹ ℤ^m` in the cube, whose boundaries lie in finitely many
hyperplanes. -/
theorem kuhnInterpolation_piecewiseAffineOn (ψ : (Fin m → ℝ) → Fin d → ℝ) {k : ℕ} (hk : 0 < k) :
    PiecewiseAffineOn (unitCube m) (kuhnInterpolation k ψ) := by
  sorry

/-- For a Lipschitz `ψ`, `∇ I_k ψ → ∇ψ` almost everywhere as `k → ∞`. -/
theorem ae_tendsto_grad_kuhnInterpolation {ψ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hψ : LipschitzWith K ψ) :
    ∀ᵐ x, Tendsto (fun k => grad (kuhnInterpolation k ψ) x) atTop (𝓝 (grad ψ x)) := by
  sorry

end CalculusOfVariations
