/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Distribution.SecondDerivative
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Convexity through the second distributional derivative

On `ℝ`:

* a convex `f` has `(ofFun f)'' ≥ 0`: `∫ f ψ'' ≥ 0` for `ψ ≥ 0`
  (`ConvexOn.integral_deriv_deriv_mul_nonneg`,
  `ConvexOn.distribNonneg_lineDerivOp_lineDerivOp_ofFun`), since
  `∫ f ψ'' = lim_{δ → 0} ∫ ψ (x) (f (x + δ) − 2 f (x) + f (x − δ)) / δ² dx` and the second
  differences of `f` are nonnegative;
* conversely a continuous `g` with `(ofFun g)'' ≥ 0` is convex
  (`convexOn_of_integral_deriv_deriv_mul_nonneg`, `convexOn_of_distribNonneg`): the mollifications
  `ρ_ε ⋆ g` are smooth with `(ρ_ε ⋆ g)'' (t) = ⟨(ofFun g)'', ρ_ε (t − ·)⟩ ≥ 0`, hence convex
  (`convexOn_of_deriv2_nonneg`), and they converge to `g` pointwise; a pointwise limit of convex
  functions is convex.

The results are stated with `sorry` proofs, to be proved.
-/

@[expose] public section

open MeasureTheory TopologicalSpace
open scoped Distributions LineDeriv ContDiff

namespace CalculusOfVariations

/-- **A convex function has a nonnegative second distributional derivative**, in concrete form:
`∫ f ψ'' ≥ 0` for every compactly supported, nonnegative `C²` function `ψ`. -/
theorem ConvexOn.integral_deriv_deriv_mul_nonneg {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x) :
    0 ≤ ∫ x, deriv (deriv ψ) x * f x := by
  sorry

/-- **A convex function has a nonnegative second distributional derivative.** -/
theorem ConvexOn.distribNonneg_lineDerivOp_lineDerivOp_ofFun {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) :
    DistribNonneg (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (Distribution.ofFun ⊤ f volume ⊤))) := by
  sorry

/-- **A continuous function with a nonnegative second distributional derivative is convex**, in
concrete form: if `∫ g ψ'' ≥ 0` for every smooth, compactly supported, nonnegative `ψ`, then `g` is
convex. -/
theorem convexOn_of_integral_deriv_deriv_mul_nonneg {g : ℝ → ℝ} (hg : Continuous g)
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, deriv (deriv ψ) x * g x) :
    ConvexOn ℝ Set.univ g := by
  sorry

/-- **A continuous function with a nonnegative second distributional derivative is convex.** -/
theorem convexOn_of_distribNonneg {g : ℝ → ℝ} (hg : Continuous g)
    (h : DistribNonneg (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (Distribution.ofFun ⊤ g volume ⊤)))) :
    ConvexOn ℝ Set.univ g := by
  sorry

end CalculusOfVariations
