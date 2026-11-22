/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Second distributional derivatives on the real line

On `ℝ`, with `Ω = ⊤` and Mathlib's distributions `𝓓'(Ω, ℝ)` (`Distribution.ofFun`, the derivative
`∂_{1}` of `Distribution.lineDerivCLM`):

* `DistribNonneg T`: `T ψ ≥ 0` for every nonnegative test function `ψ`;
* the pairing `⟨(ofFun g)'', ψ⟩ = ∫ g ψ''` (`lineDerivOp_lineDerivOp_ofFun_apply`), and the
  nonnegativity of `(ofFun g)''` read through it
  (`distribNonneg_lineDerivOp_lineDerivOp_ofFun_iff`);
* for a locally Lipschitz `f`, `(ofFun f)' = ofFun f'`, by the fundamental theorem of calculus for
  absolutely continuous functions (`lineDerivOp_ofFun_eq_ofFun_deriv`); in concrete form,
  `∫ f ψ' = −∫ f' ψ` (`integral_deriv_mul_eq_neg`);
* the Leibniz rule for a smooth `h`: `(h f)'' = h f'' + 2 h' f' + h'' f`, in the paired form
  `∫ h f ψ'' = ∫ f (h ψ)'' + ∫ (2 h' f' + h'' f) ψ` (`integral_deriv_deriv_mul_mul`,
  `lineDerivOp_lineDerivOp_ofFun_mul_apply`).

The results are stated with `sorry` proofs, to be proved.
-/

@[expose] public section

open MeasureTheory TopologicalSpace
open scoped Distributions LineDeriv ContDiff

namespace CalculusOfVariations

/-- A real distribution `T` is nonnegative if `T ψ ≥ 0` for every nonnegative test function
`ψ`. -/
def DistribNonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
    (T : 𝓓'(Ω, ℝ)) : Prop :=
  ∀ ψ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ ψ x) → 0 ≤ T ψ

/-- The second derivative of the distribution of a locally integrable `g` on `ℝ`, paired with a
test function: `⟨(ofFun g)'', ψ⟩ = ∫ g ψ''`. -/
theorem lineDerivOp_lineDerivOp_ofFun_apply {g : ℝ → ℝ} (hg : LocallyIntegrable g)
    (ψ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (Distribution.ofFun ⊤ g volume ⊤)) ψ =
      ∫ x, deriv (deriv ψ) x * g x := by
  sorry

/-- `(ofFun g)'' ≥ 0` if and only if `∫ g ψ'' ≥ 0` for every smooth, compactly supported,
nonnegative `ψ`. -/
theorem distribNonneg_lineDerivOp_lineDerivOp_ofFun_iff {g : ℝ → ℝ} (hg : LocallyIntegrable g) :
    DistribNonneg (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (Distribution.ofFun ⊤ g volume ⊤))) ↔
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
        0 ≤ ∫ x, deriv (deriv ψ) x * g x := by
  sorry

/-- **The distributional derivative of a locally Lipschitz function** on `ℝ` is the distribution
of its derivative (which exists almost everywhere and is locally bounded): the fundamental theorem
of calculus for absolutely continuous functions, through integration by parts against the test
function. -/
theorem lineDerivOp_ofFun_eq_ofFun_deriv {f : ℝ → ℝ} (hf : LocallyLipschitz f) :
    ∂_{(1 : ℝ)} (Distribution.ofFun ⊤ f volume ⊤) = Distribution.ofFun ⊤ (deriv f) volume ⊤ := by
  sorry

/-- Integration by parts for a locally Lipschitz `f` against a compactly supported `C¹` function
`ψ`: `∫ ψ' f = −∫ ψ f'`. -/
theorem integral_deriv_mul_eq_neg {f ψ : ℝ → ℝ} (hf : LocallyLipschitz f) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x, deriv ψ x * f x = -∫ x, ψ x * deriv f x := by
  sorry

/-- **The Leibniz rule for the second derivative**, in paired form: for a locally Lipschitz `f`, a
`C²` function `h` and a compactly supported `C²` function `ψ`,
`∫ ψ'' (h f) = ∫ (h ψ)'' f + ∫ ψ (2 h' f' + h'' f)`, that is,
`(h f)'' = h f'' + 2 h' f' + h'' f` with `⟨h f'', ψ⟩ = ⟨f'', h ψ⟩`. -/
theorem integral_deriv_deriv_mul_mul {f h ψ : ℝ → ℝ} (hf : LocallyLipschitz f)
    (hh : ContDiff ℝ 2 h) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, deriv (deriv ψ) x * (h x * f x) =
      ∫ x, deriv (deriv fun y => h y * ψ y) x * f x +
        ∫ x, ψ x * (2 * deriv h x * deriv f x + deriv (deriv h) x * f x) := by
  sorry

/-- The Leibniz rule for the second distributional derivative of `h f`, `h` smooth and `f`
locally Lipschitz: `⟨(h f)'', ψ⟩ = ⟨f'', h ψ⟩ + ∫ (2 h' f' + h'' f) ψ`. -/
theorem lineDerivOp_lineDerivOp_ofFun_mul_apply {f h : ℝ → ℝ} (hf : LocallyLipschitz f)
    (hh : ContDiff ℝ ∞ h) (ψ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (Distribution.ofFun ⊤ (fun x => h x * f x) volume ⊤)) ψ =
      ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (Distribution.ofFun ⊤ f volume ⊤))
          (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) hh ψ) +
        ∫ x, ψ x * (2 * deriv h x * deriv f x + deriv (deriv h) x * f x) := by
  sorry

end CalculusOfVariations
