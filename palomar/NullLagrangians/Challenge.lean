module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Data.List.TFAE
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Semicontinuity.Defs

/-!
# Challenge: null Lagrangians and quasiaffine functions

A function `f : ℝ^{d×m} → ℝ` is quasiaffine if `f` and `−f` are quasiconvex, and rank-one affine if
`f` and `−f` are rank-one convex. The quasiaffine functions are the rank-one affine ones, and they
are the affine combinations of the minors (subdeterminants) of the matrix, of all orders; they are
also the null Lagrangians, the `f` with `∫_Ω f (A + ∇φ) = |Ω| f (A)` for all test maps `φ`.

## The theorems

1. `setIntegral_minor_add_grad`: minors of every order are null Lagrangians,
   `∫_Ω minor (A + ∇φ) = |Ω| minor A`.
2. `rankOneAffine_tfae`: for an arbitrary `f : ℝ^{d×m} → ℝ`, the equivalence of the four notions.

The sources are [D] B. Dacorogna, *Direct Methods in the Calculus of Variations*, 2nd ed., Springer,
2008, Theorems 5.20 and 8.35, whose proofs are followed, and [D82] B. Dacorogna, *Quasiconvexity and
relaxation of nonconvex problems in the calculus of variations*, J. Funct. Anal. 46 (1982), 102–118,
Proposition 4. The characterization is due to J. M. Ball, *Convexity conditions and existence
theorems in nonlinear elasticity*, Arch. Ration. Mech. Anal. 63 (1977), 337–403, after Edelen and
Ericksen.

## Conventions

* `d × m` matrices are `Matrix (Fin d) (Fin m) ℝ`, `ℝ^m` is `Fin m → ℝ`, and the gradient of
  `φ : ℝ^m → ℝ^d` at `x` is `grad φ x` (rows are the components).
* `minor A r c` is the determinant of the submatrix with the rows `r` and the columns `c`, two
  strictly increasing maps `Fin k ↪o Fin d`, `Fin k ↪o Fin m`. The `0 × 0` minor is the constant
  `1`; the `1 × 1` minors are the entries.
* A test map on `Ω` is a Lipschitz `φ : ℝ^m → ℝ^d` with `φ = 0` outside `Ω`. For a bounded Lipschitz
  domain these are the maps of `W^{1,∞}_0 (Ω, ℝ^d)`, extended by `0`. For an arbitrary bounded open
  `Ω` they are among those of [D], where `W^{1,∞}_0 (Ω) = W^{1,∞} (Ω) ∩ W^{1,1}_0 (Ω)`, possibly not
  all of them (for `Ω = B ∖ {0}`, `B` a ball, `m ≥ 2`, the maps of [D] need not vanish at `0`).
* `Quasiconvex f` is tested on the unit cube; for Borel, locally bounded `f` it does not depend on
  the domain ([D], Proposition 5.11). The quasiconvex functions of [D] are Borel and locally bounded
  by definition; here `Measurable f` and `IsLocallyBounded f` are stated separately.

The definitions are copied word for word from `CalculusOfVariations/Basic.lean` (kept in sync by
`scripts/sync_challenge_defs.py`); the theorems are proved in
`palomar/NullLagrangians/Solution.lean`.
-/

@[expose] public section

open MeasureTheory

namespace CalculusOfVariations

-- BEGIN SHARED DEFINITIONS: core

variable {d m : ℕ}

/-- The derivative matrix of `φ : ℝ^m → ℝ^d` at `x`: the `d × m` matrix with the entries
`∂_k φ_i (x)` (rows are the components). For a Lipschitz `φ` it is the gradient almost everywhere
(Rademacher's theorem); an entry is `0` where `φ_i` is not differentiable. -/
noncomputable def grad (φ : (Fin m → ℝ) → Fin d → ℝ) (x : Fin m → ℝ) :
    Matrix (Fin d) (Fin m) ℝ :=
  Matrix.of fun i k => fderiv ℝ (fun y => φ y i) x (Pi.single k 1)

/-- The open unit cube `(0, 1)^m`. -/
def unitCube (m : ℕ) : Set (Fin m → ℝ) :=
  Set.pi Set.univ fun _ => Set.Ioo 0 1

/-- `f` is bounded on a neighbourhood of every matrix. -/
def IsLocallyBounded (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ A, ∃ U ∈ nhds A, ∃ C : ℝ, ∀ B ∈ U, |f B| ≤ C

/-- Rank-one convexity: `t ↦ f (A + t B)` is convex on `ℝ` for every `A` and every `B` of rank
one. -/
def RankOneConvex (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ A B : Matrix (Fin d) (Fin m) ℝ, B.rank = 1 → ConvexOn ℝ Set.univ fun t : ℝ => f (A + t • B)

/-- Quasiconvexity at `A` on the domain `Ω`: `|Ω| f (A) ≤ ∫_Ω f (A + ∇φ)` for every Lipschitz `φ`
vanishing outside `Ω` for which the integral exists (for a Borel, locally bounded `f` and a bounded
`Ω`, it always does). -/
def QuasiconvexAtOn (Ω : Set (Fin m → ℝ)) (f : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin d) (Fin m) ℝ) : Prop :=
  ∀ (φ : (Fin m → ℝ) → Fin d → ℝ) (K : NNReal), LipschitzWith K φ → (∀ x ∉ Ω, φ x = 0) →
    IntegrableOn (fun x => f (A + grad φ x)) Ω →
      (volume Ω).toReal * f A ≤ ∫ x in Ω, f (A + grad φ x)

/-- Quasiconvexity: quasiconvexity on the unit cube at every matrix. -/
def Quasiconvex (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ A, QuasiconvexAtOn (unitCube m) f A

-- END SHARED DEFINITIONS: core

-- BEGIN SHARED DEFINITIONS: minors

/-- Rank-one affinity: `f` and `−f` are rank-one convex. -/
def RankOneAffine (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  RankOneConvex f ∧ RankOneConvex (-f)

/-- The `k × k` minor of `A` with the rows `r` and the columns `c` (strictly increasing). -/
noncomputable def minor (A : Matrix (Fin d) (Fin m) ℝ) {k : ℕ} (r : Fin k ↪o Fin d)
    (c : Fin k ↪o Fin m) : ℝ :=
  (A.submatrix r c).det

-- END SHARED DEFINITIONS: minors

end CalculusOfVariations

namespace NullLagrangiansChallenge

open CalculusOfVariations

variable {d m : ℕ}

/-- **Minors are null Lagrangians** ([D], Theorem 8.35, (8.44)): for a bounded `Ω ⊆ ℝ^m`, a
Lipschitz `φ : ℝ^m → ℝ^d` vanishing outside `Ω`, every matrix `A` and every minor, of any order `k`,
`∫_Ω minor (A + ∇φ) = |Ω| minor A`. ([D]: `Ω` open.) -/
theorem setIntegral_minor_add_grad {Ω : Set (Fin m → ℝ)} (hΩ : Bornology.IsBounded Ω)
    {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ) (h0 : ∀ x ∉ Ω, φ x = 0)
    (A : Matrix (Fin d) (Fin m) ℝ) {k : ℕ} (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m) :
    ∫ x in Ω, minor (A + grad φ x) r c = (volume Ω).toReal * minor A r c := by
  sorry

/-- **Quasiaffine functions are the affine combinations of minors** ([D], Theorem 5.20, (i), (ii),
(iii'); [D82], Proposition 4; due to Ball, 1977). For `f : ℝ^{d×m} → ℝ` the following are
equivalent:

1. `f` is rank-one affine: `f` and `−f` are rank-one convex;
2. `f` is quasiaffine: Borel, locally bounded, and `f` and `−f` are quasiconvex;
3. `f` is a null Lagrangian: Borel, locally bounded, and `∫_Ω f (A + ∇φ) = |Ω| f (A)` for every
   bounded open `Ω`, every `A` and every Lipschitz `φ` vanishing outside `Ω`;
4. `f` is an affine combination of minors, `f (A) = ∑_{k ≤ min d m} ∑_{r, c} a k r c · minor A r c`.

No regularity of `f` is assumed in 1 and 4. The conditions (ii') and (iii) of [D], Theorem 5.20
(`f ∈ C¹` with `f (ξ + a ⊗ b) = f (ξ) + ⟨∇f (ξ); a ⊗ b⟩`; `f` and `−f` polyconvex) are not
stated. -/
theorem rankOneAffine_tfae (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : List.TFAE
    [RankOneAffine f,
      Measurable f ∧ IsLocallyBounded f ∧ Quasiconvex f ∧ Quasiconvex (-f),
      Measurable f ∧ IsLocallyBounded f ∧ ∀ Ω : Set (Fin m → ℝ), IsOpen Ω →
        Bornology.IsBounded Ω → ∀ (A : Matrix (Fin d) (Fin m) ℝ) (φ : (Fin m → ℝ) → Fin d → ℝ)
          (K : NNReal), LipschitzWith K φ → (∀ x ∉ Ω, φ x = 0) →
            ∫ x in Ω, f (A + grad φ x) = (volume Ω).toReal * f A,
      ∃ a : (k : ℕ) → (Fin k ↪o Fin d) → (Fin k ↪o Fin m) → ℝ,
        ∀ A, f A = ∑ k ∈ Finset.range (min d m + 1), ∑ r, ∑ c, a k r c * minor A r c] := by
  sorry

end NullLagrangiansChallenge
