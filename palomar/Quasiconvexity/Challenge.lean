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
# Challenge: quasiconvexity and rank-one convexity

The basic theory of Morrey's quasiconvexity, for integrands `f : ℝ^{d×m} → ℝ` and test maps
`φ : ℝ^m → ℝ^d`. `f` is quasiconvex if `|Ω| f (A) ≤ ∫_Ω f (A + ∇φ)` for every matrix `A` and every
test map `φ` on the domain `Ω`; it is rank-one convex if it is convex along the lines
`t ↦ A + t B`, `rank B = 1`.

## The theorems

1. `rankOneConvex_locallyLipschitz`, `rankOneConvex_abs_sub_le_of_osc`: a rank-one convex function
   is locally Lipschitz, with a bound by its oscillation.
2. `rankOneConvex_of_quasiconvex`: a quasiconvex function is rank-one convex.
3. `quasiconvexAtOn_iff_of_isBounded`: quasiconvexity does not depend on the domain, among the
   nonempty bounded open sets.
4. `quasiconvexAtOn_unitCube_iff_periodic`: it may be tested with periodic maps.
5. `quadraticForm_quasiconvex_iff`: a quadratic form is quasiconvex if and only if it is rank-one
   convex.
6. `integrableOn_add_grad`: a check of the definitions, which shows that the integrability clause of
   `QuasiconvexAtOn` is void under the hypotheses of 2–4.

The sources are [R] F. Rindler, *Calculus of Variations*, 2nd ed., Graduate Texts in Mathematics
310, Springer, 2026, and [D] B. Dacorogna, *Direct Methods in the Calculus of Variations*, 2nd ed.,
Springer, 2008; the notions and most of the results go back to C. B. Morrey, *Quasi-convexity and
the lower semicontinuity of multiple integrals*, Pacific J. Math. 2 (1952), 25–53.

## Conventions

* `d × m` matrices are `Matrix (Fin d) (Fin m) ℝ`, `ℝ^m` is `Fin m → ℝ`, and the gradient of
  `φ : ℝ^m → ℝ^d` at `x` is `grad φ x` (rows are the components; [R] has `m × d` matrices, [D] has
  `N × n` matrices). The dimensions `d`, `m` are arbitrary (`0` allowed).
* A test map on `Ω` is a Lipschitz `φ : ℝ^m → ℝ^d` with `φ = 0` outside `Ω`. For a bounded Lipschitz
  domain these are the maps of `W^{1,∞}_0 (Ω, ℝ^d)`, extended by `0`. For an arbitrary bounded open
  `Ω` they are among those of [D], where `W^{1,∞}_0 (Ω) = W^{1,∞} (Ω) ∩ W^{1,1}_0 (Ω)`
  (Definition 12.9 (iv)), possibly not all of them (for `Ω = B ∖ {0}`, `B` a ball, `m ≥ 2`, the maps
  of [D] need not vanish at `0`). Quasiconvexity on `Ω` is the same for both classes, by theorem 3
  and [D], Proposition 5.11, since they agree on the cube.
* `Quasiconvex f` (quasiconvexity at every matrix) is tested on the unit cube `(0, 1)^m`; [R] uses
  the unit ball, [D] every bounded open set. By theorem 3 this is the same.
* In [R] and [D] a quasiconvex function is by definition Borel measurable and locally bounded. Here
  these are hypotheses, `Measurable f` (for the Borel `σ`-algebra) and `IsLocallyBounded f`.
* The norms of `ℝ^m`, `ℝ^d` are sup norms (they matter only for the meaning of "Lipschitz"). In
  theorem 1 the norm of matrices is the Frobenius norm, as in [R].

The definitions are copied word for word from `CalculusOfVariations/Basic.lean` (kept in sync by
`scripts/sync_challenge_defs.py`); the theorems are proved in
`palomar/Quasiconvexity/Solution.lean`.
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
`Ω`, it always does). It is used for bounded `Ω` only: if `|Ω| = ∞`, `(volume Ω).toReal` is `0`. -/
def QuasiconvexAtOn (Ω : Set (Fin m → ℝ)) (f : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin d) (Fin m) ℝ) : Prop :=
  ∀ (φ : (Fin m → ℝ) → Fin d → ℝ) (K : NNReal), LipschitzWith K φ → (∀ x ∉ Ω, φ x = 0) →
    IntegrableOn (fun x => f (A + grad φ x)) Ω →
      (volume Ω).toReal * f A ≤ ∫ x in Ω, f (A + grad φ x)

/-- Quasiconvexity: quasiconvexity on the unit cube at every matrix. -/
def Quasiconvex (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ A, QuasiconvexAtOn (unitCube m) f A

-- END SHARED DEFINITIONS: core

-- BEGIN SHARED DEFINITIONS: periodic

/-- Quasiconvexity at `A` with periodic test maps: `f (A) ≤ ∫_{(0,1)^m} f (A + ∇φ)` for every
`ℤ^m`-periodic Lipschitz `φ` for which the integral exists. -/
def QuasiconvexAtPeriodic (f : Matrix (Fin d) (Fin m) ℝ → ℝ) (A : Matrix (Fin d) (Fin m) ℝ) :
    Prop :=
  ∀ (φ : (Fin m → ℝ) → Fin d → ℝ) (K : NNReal), LipschitzWith K φ →
    (∀ (x : Fin m → ℝ) (z : Fin m → ℤ), φ (x + fun i => (z i : ℝ)) = φ x) →
    IntegrableOn (fun x => f (A + grad φ x)) (unitCube m) →
      f A ≤ ∫ x in unitCube m, f (A + grad φ x)

-- END SHARED DEFINITIONS: periodic

end CalculusOfVariations

namespace QuasiconvexityChallenge

open CalculusOfVariations

variable {d m : ℕ}

open scoped Matrix.Norms.Frobenius in
/-- **A rank-one convex function is locally Lipschitz** ([D], Theorem 5.3 (iv); [R], Lemma 5.9,
first assertion), for the Frobenius norm. In [R] rank-one convex functions are Borel and locally
bounded by definition (with a remark that the local boundedness is automatic); in [D], and here,
nothing is assumed beyond `f : ℝ^{d×m} → ℝ` and the convexity along rank-one lines. -/
theorem rankOneConvex_locallyLipschitz {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : RankOneConvex f) :
    LocallyLipschitz f := by
  sorry

open scoped Matrix.Norms.Frobenius in
/-- **The Lipschitz bound by the oscillation** ([R], (5.9), in the proof of Lemma 5.9): in the
Frobenius norm, if a rank-one convex `f` has oscillation at most `ω` on the closed ball
`B̄_{6r} (F)`, then it is Lipschitz on the open ball `B_r (F)` with the constant
`√(min d m) · ω / (3r)`. -/
theorem rankOneConvex_abs_sub_le_of_osc {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : RankOneConvex f)
    {F : Matrix (Fin d) (Fin m) ℝ} {r ω : ℝ} (hr : 0 < r)
    (hω : ∀ A ∈ Metric.closedBall F (6 * r), ∀ B ∈ Metric.closedBall F (6 * r), |f A - f B| ≤ ω)
    {A B : Matrix (Fin d) (Fin m) ℝ} (hA : A ∈ Metric.ball F r) (hB : B ∈ Metric.ball F r) :
    |f A - f B| ≤ √(min d m : ℕ) * (ω / (3 * r)) * ‖A - B‖ := by
  sorry

/-- **A quasiconvex function is rank-one convex** ([R], Proposition 5.6; [D], Theorem 5.3 (i)): a
Borel, locally bounded `f` that is quasiconvex (on the unit cube) at every matrix is convex along
every rank-one line. -/
theorem rankOneConvex_of_quasiconvex {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hm : Measurable f)
    (hb : IsLocallyBounded f) (hf : Quasiconvex f) : RankOneConvex f := by
  sorry

/-- **Quasiconvexity does not depend on the domain** ([D], Proposition 5.11; [R], Lemma 5.2 (i), for
Lipschitz domains): for a Borel, locally bounded `f`, quasiconvexity at `A` is the same on all
nonempty bounded open sets. ([D] does not say that its first domain is nonempty; the statement is
false for the empty one, on which every `f` is quasiconvex. [D] and [R] quantify over `A`; their
proof, for a fixed `A`, gives the equivalence at each `A`.) -/
theorem quasiconvexAtOn_iff_of_isBounded {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hm : Measurable f)
    (hb : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ) {Ω Ω' : Set (Fin m → ℝ)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hΩne : Ω.Nonempty)
    (hΩ' : IsOpen Ω') (hΩ'b : Bornology.IsBounded Ω') (hΩ'ne : Ω'.Nonempty) :
    QuasiconvexAtOn Ω f A ↔ QuasiconvexAtOn Ω' f A := by
  sorry

/-- **Quasiconvexity with periodic test maps** ([D], Proposition 5.13): for a Borel, locally bounded
`f`, quasiconvexity at `A` on the unit cube is equivalent to `f (A) ≤ ∫_{(0,1)^m} f (A + ∇φ)` for
all `ℤ^m`-periodic Lipschitz `φ`. ([D] quantifies over `A`; its proof gives the equivalence at each
`A`.) -/
theorem quasiconvexAtOn_unitCube_iff_periodic {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hm : Measurable f) (hb : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ) :
    QuasiconvexAtOn (unitCube m) f A ↔ QuasiconvexAtPeriodic f A := by
  sorry

/-- **Quadratic forms** ([D], Theorem 5.25 (i), due to Van Hove): the quadratic form `A ↦ Q (A, A)`
of a bilinear form `Q` on `ℝ^{d×m}` is quasiconvex if and only if it is rank-one convex. ([D]: for
`f (ξ) = ⟨M ξ; ξ⟩`, `M` symmetric; these are the same functions.) -/
theorem quadraticForm_quasiconvex_iff (Q : LinearMap.BilinForm ℝ (Matrix (Fin d) (Fin m) ℝ)) :
    (Quasiconvex fun A => Q A A) ↔ RankOneConvex fun A => Q A A := by
  sorry

/-- A check of the definitions: for a Borel, locally bounded `f`, a bounded `Ω` and a Lipschitz `φ`,
the function `x ↦ f (A + ∇φ (x))` is integrable on `Ω`, so that the integrability clauses of
`QuasiconvexAtOn` and `QuasiconvexAtPeriodic` exclude no test map. -/
theorem integrableOn_add_grad {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hm : Measurable f)
    (hb : IsLocallyBounded f) {Ω : Set (Fin m → ℝ)} (hΩ : Bornology.IsBounded Ω)
    (A : Matrix (Fin d) (Fin m) ℝ) {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) : IntegrableOn (fun x => f (A + grad φ x)) Ω := by
  sorry

end QuasiconvexityChallenge
