# Calculus of variations in Lean: quasiconvexity, rank-one convexity, the quasiconvex envelope

[![Lean Action CI](https://github.com/vltanh/lean4-calculus-of-variations/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-calculus-of-variations/actions/workflows/lean_action_ci.yml)

Lean 4 with Mathlib `v4.36.0-rc2`, for integrands `f : ℝ^{d×m} → ℝ` and Lipschitz maps
`φ : ℝ^m → ℝ^d` (sup norms):

- **Rank-one convexity and quasiconvexity.** A rank-one convex function is locally Lipschitz, with
  a bound by its oscillation (and so is a separately convex function); a quasiconvex integrand is
  rank-one convex, by laminates, cut off near the boundary of a cube with faces orthogonal to the
  rank-one direction; quasiconvexity does not
  depend on the bounded open domain, and may be tested with periodic maps.
- **Quadratic forms and minors.** A quadratic form is quasiconvex if and only if it is rank-one
  convex. Rank-one affine functions, quasiaffine functions, null Lagrangians and affine
  combinations of minors (of every order) are the same.
- **The quasiconvex envelope.** Dacorogna's formula `f^{qc} (A) = inf_φ ⨍_Ω f (A + ∇φ)` on every
  nonempty bounded open `Ω`, for continuous `f`, with values in `EReal`; behind it, the independence
  of the domain and the rank-one convexity of the infimum formula `Qf`, and the inequality
  `⨍ Qf (F + ∇ψ) ≥ Qf (F)` for piecewise affine test maps `ψ`.
- **Smoothing.** A smooth rank-one convex integrand that is not quasiconvex at `0` gives a smooth
  one with the same properties, uniformly Legendre–Hadamard and of quadratic growth.
- **Distributions on `ℝ`.** Second distributional derivatives, the Leibniz rule, and convexity: a
  continuous function is convex if and only if its second distributional derivative is
  nonnegative.
- **Tools.** Gradients of Lipschitz maps, rescaling, periodic extension, cut-offs, mollification
  (also of periodic maps), the vanishing of the gradient on the zero set, finite coverings by
  cubes, piecewise affine maps and Kuhn–Freudenthal interpolation.

**Status: proved.** Every statement is proved; the [audit](scripts/Audit.lean) checks that every
declaration of the library, and of the Solutions in [`palomar/`](palomar), depends only on
[`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound) (no `sorry`, no `axiom`, no `native_decide`).

## Main statements

[`unitCube`](CalculusOfVariations/Basic.lean#L75) is `(0, 1)^m`; [`grad`](CalculusOfVariations/Basic.lean#L70) is the gradient: `grad φ x` is the `d × m` matrix of partial
derivatives; a test map on `Ω` is a Lipschitz `φ` vanishing outside `Ω`. The definitions are in
[`CalculusOfVariations/Basic.lean`](CalculusOfVariations/Basic.lean) ([M, Def. 4.2], with the
conventions of the package): [`RankOneConvex`](CalculusOfVariations/Basic.lean#L84), [`RankOneAffine`](CalculusOfVariations/Basic.lean#L138), [`QuasiconvexAtOn`](CalculusOfVariations/Basic.lean#L90)
(`QuasiconvexAtOn Ω f A`: `|Ω| f (A) ≤ ∫_Ω f (A + ∇φ)` for every test map on `Ω` for which the
integral exists), [`QuasiconvexAtPeriodic`](CalculusOfVariations/Basic.lean#L106), [`Quasiconvex`](CalculusOfVariations/Basic.lean#L97) (on the unit cube, at every matrix),
[`IsLocallyBounded`](CalculusOfVariations/Basic.lean#L79), [`quasiconvexEnvelope`](CalculusOfVariations/Basic.lean#L120) (the supremum of the Borel, locally bounded, quasiconvex
minorants, in `EReal`; equal to [`qcEnvelope`](CalculusOfVariations/Basic.lean#L155), over the lower semicontinuous ones,
[`quasiconvexEnvelope_eq_qcEnvelope`](CalculusOfVariations/Envelope/Formula.lean#L193)), [`domainInf`](CalculusOfVariations/Basic.lean#L128) (`domainInf Ω f A` is the infimum formula
`inf_φ ⨍_Ω f (A + ∇φ)`) and [`minor`](CalculusOfVariations/Basic.lean#L142).

| Statement | Lean | Source |
| --- | --- | --- |
| separately convex ⇒ bounded on cubes, locally Lipschitz | [`Matrix.exists_abs_le_of_convexOn_single`](CalculusOfVariations/Convex/SeparatelyConvex.lean#L217), [`Matrix.locallyLipschitz_of_convexOn_single`](CalculusOfVariations/Convex/SeparatelyConvex.lean#L334) | [M, Def. 4.2, Remark 3] |
| rank-one convex ⇒ locally Lipschitz; in the Frobenius norm, `lip (f; B_r (F)) ≤ √(min d m) osc (f; B̄_{6r} (F)) / (3r)` | [`RankOneConvex.locallyLipschitz`](CalculusOfVariations/RankOneConvex/LocallyLipschitz.lean#L257), [`RankOneConvex.abs_sub_le_of_osc`](CalculusOfVariations/RankOneConvex/LocallyLipschitz.lean#L155) | [R, Lemma 5.9] (without (5.8)), [Da08, Thm 5.3 (iv)] |
| `M = ∑_{i < min d m} σ_i p_i ⊗ q_i`, `σ_0 ≥ σ_1 ≥ … ≥ 0`, `p_i`, `q_i` orthonormal (singular value decomposition) | [`Matrix.exists_singularValueDecomposition`](CalculusOfVariations/RankOneConvex/SingularValues.lean#L94) | [R, Appendix A.1] |
| `f` Borel, locally bounded, quasiconvex at `F` on the unit cube ⇒ `f (F) ≤ λ f (F + (1−λ) a ⊗ n) + (1−λ) f (F − λ a ⊗ n)`, by laminates with cut-offs | [`le_of_quasiconvexAtOn_vecMulVec`](CalculusOfVariations/Quasiconvex/Laminate.lean#L582), with [`sawLaminate`](CalculusOfVariations/Quasiconvex/Laminate.lean#L153), [`setIntegral_sawLaminate`](CalculusOfVariations/Quasiconvex/Laminate.lean#L343), [`le_of_quasiconvexAtOn_of_tendsto`](CalculusOfVariations/Quasiconvex/Cutoff.lean#L91) (the cut-off), [`le_of_quasiconvexAtOn_unitCube_of_measurable`](CalculusOfVariations/Quasiconvex/Laminate.lean#L366) (`n = e_j`) | [R, Prop. 5.6] |
| `f` Borel, locally bounded, quasiconvex ⇒ rank-one convex | [`rankOneConvex_of_quasiconvex`](CalculusOfVariations/Quasiconvex/RankOneConvex.lean#L80) | [R, Prop. 5.6] |
| without regularity of `f`: quasiconvex at `F` on the unit cube ⇒ the two-point inequality along `a ⊗ e_j`, by truncated laminates; on a rotated cube, along `a ⊗ R e_j` | [`le_of_quasiconvexAtOn_unitCube`](CalculusOfVariations/Quasiconvex/TruncatedLaminate.lean#L301), [`le_of_quasiconvexAtOn_orthogonal`](CalculusOfVariations/Quasiconvex/TruncatedLaminate.lean#L402), with [`cubeLaminate`](CalculusOfVariations/Quasiconvex/TruncatedLaminate.lean#L51) | [M, Lemma 4.3] |
| `f` Borel, locally bounded: quasiconvexity on the cube ⇔ on any nonempty bounded open `Ω` | [`quasiconvexAtOn_iff`](CalculusOfVariations/Quasiconvex/Domain.lean#L268), [`quasiconvexAtOn_of_unitCube`](CalculusOfVariations/Quasiconvex/Domain.lean#L49) | [Da08, Prop. 5.11], [R, Lemma 5.2 (i)] |
| `f` Borel, locally bounded: quasiconvexity on the cube ⇔ with periodic test maps | [`quasiconvexAtOn_iff_periodic`](CalculusOfVariations/Quasiconvex/Periodic.lean#L108) | [Da08, Prop. 5.13] |
| `Q` bilinear: `A ↦ Q (A, A)` quasiconvex ⇔ rank-one convex | [`quadraticForm_quasiconvex_iff`](CalculusOfVariations/QuadraticForm/Quasiconvex.lean#L240), [`quadraticForm_quasiconvex`](CalculusOfVariations/QuadraticForm/Quasiconvex.lean#L96) | [Da08, Thm 5.25 (i)] |
| `f` rank-one affine ⇔ quasiaffine ⇔ null Lagrangian ⇔ affine combination of minors | [`rankOneAffine_tfae`](CalculusOfVariations/Minors/Characterization.lean#L87) | [Da08, Thm 5.20, (i), (ii), (iii′)], [Da82, Prop. 4] |
| rank-one affine ⇒ affine combination of minors (continuity not assumed) | [`RankOneAffine.exists_eq_sum_minor`](CalculusOfVariations/Minors/RankOneAffine.lean#L899) | [Da08, Thm 5.20, (ii) ⇒ (iii′)] |
| `∫_Ω minor (A + ∇φ) = \|Ω\| minor A`, minors of every order, `φ` Lipschitz, `φ = 0` off the bounded set `Ω` | [`setIntegral_minor_add_grad`](CalculusOfVariations/Minors/AllOrders.lean#L352); [`nl_jac_eq_sum_D`](CalculusOfVariations/Minors/AllOrders.lean#L167) (a Jacobian of smooth maps is a divergence), [`nl_sum_D_jac_eq_zero`](CalculusOfVariations/Minors/AllOrders.lean#L123) | [Da08, Thm 8.35, (8.44); Thm 8.33] |
| with explicit formulas: `∫ minor (∇φ) = 0` for `2 × 2`, `3 × 3` minors, `φ` Lipschitz with compact support; `∫_Q minor (A + ∇φ) = minor A` for `3 × 3` minors | [`nl_null2`](CalculusOfVariations/Minors/NullLagrangian.lean#L240), [`nl_null3`](CalculusOfVariations/Minors/NullLagrangian.lean#L252), [`nl_minor3_quasiaffine`](CalculusOfVariations/Minors/Quasiaffine.lean#L181) | [Da08, Thm 8.35], [Mo, Lemma 5.1] |
| `f^{qc} (A) = inf_φ ⨍_Ω f (A + ∇φ)`, `Ω` nonempty, bounded, open, `f` continuous; `Ω` the unit ball | [`quasiconvexEnvelope_eq_domainInf`](CalculusOfVariations/Envelope/Formula.lean#L203), [`qcEnvelope_eq_iInf`](CalculusOfVariations/Envelope/Formula.lean#L161), [`qcEnvelope_eq_iInf_unitBall`](CalculusOfVariations/Envelope/Formula.lean#L182) | from [KP, Prop. 8.1]; [Da82, Thm 5], [Da08, Thm 6.9] |
| the infimum formula, `Ω` nonempty, bounded, open: independent of `Ω`; rank-one convex; finite at one matrix ⇒ real-valued, continuous, quasiconvex | [`domainInf_eq_of_isBounded`](CalculusOfVariations/Envelope/Formula.lean#L212), [`domainInf_le_of_rank_le_one`](CalculusOfVariations/Envelope/Formula.lean#L236), [`exists_domainInf_eq_coe`](CalculusOfVariations/Envelope/Formula.lean#L254) | [KP, Prop. 8.1] |
| the infimum formula does not depend on the domain (null boundaries): copies of a test map by Vitali's theorem | [`domainInf_eq`](CalculusOfVariations/Envelope/Domain.lean#L266), [`domainInf_le_domainInf`](CalculusOfVariations/Envelope/Domain.lean#L250), [`exists_testMap_setIntegral_eq`](CalculusOfVariations/Envelope/Domain.lean#L125) | [KP, Prop. 8.1 (i)] |
| `Qf (F) ≤ λ Qf (F + (1−λ) a ⊗ n) + (1−λ) Qf (F − λ a ⊗ n)`, in `EReal`; `Qf` finite ⇒ rank-one convex, continuous | [`cubeInf_le_two_point_vecMulVec`](CalculusOfVariations/Envelope/RankOneConvex.lean#L403), [`cubeInf_le_two_point`](CalculusOfVariations/Envelope/RankOneConvex.lean#L311) (`n = e_j`), [`cubeInfReal_rankOneConvex`](CalculusOfVariations/Envelope/Convexity.lean#L138), [`cubeInfReal_continuous`](CalculusOfVariations/Envelope/Convexity.lean#L169) | [KP, Prop. 8.1 (ii), (iii)] |
| `⨍_Q Qf (F + ∇ψ) ≥ Qf (F)` for piecewise affine test maps `ψ`; `Qf` finite ⇒ quasiconvex | [`cubeInf_le_sum_of_piecewiseAffine`](CalculusOfVariations/Envelope/Glue.lean#L146), [`cubeInfReal_quasiconvex`](CalculusOfVariations/Envelope/Convexity.lean#L270) | [KP, Prop. 8.1 (iv), Prop. 7.2, Step 6] |
| Kuhn–Freudenthal interpolation: Lipschitz, piecewise affine; for `C¹` maps with compact support, `∇ I_k ψ → ∇ψ` uniformly | [`kuhnInterpolation_lipschitz`](CalculusOfVariations/Lipschitz/PiecewiseAffine.lean#L206), [`kuhnInterpolation_piecewiseAffineOn`](CalculusOfVariations/Lipschitz/PiecewiseAffine.lean#L591), [`kuhnInterpolation_grad_uniform`](CalculusOfVariations/Lipschitz/PiecewiseAffine.lean#L652) | [F], [Ku] (the triangulation) |
| `⟨(ofFun g)'', ψ⟩ = ∫ g ψ''`; `(ofFun f)' = ofFun f'` for locally Lipschitz `f`; Leibniz for `(h f)''` | [`lineDerivOp_lineDerivOp_ofFun_apply`](CalculusOfVariations/Distribution/SecondDerivative.lean#L65), [`lineDerivOp_ofFun_eq_ofFun_deriv`](CalculusOfVariations/Distribution/SecondDerivative.lean#L159), [`integral_deriv_deriv_mul_mul`](CalculusOfVariations/Distribution/SecondDerivative.lean#L179), [`lineDerivOp_lineDerivOp_ofFun_mul_apply`](CalculusOfVariations/Distribution/SecondDerivative.lean#L246) | |
| on `ℝ`: `f` convex ⇒ `(ofFun f)'' ≥ 0`; `g` continuous with `(ofFun g)'' ≥ 0` ⇒ `g` convex | [`ConvexOn.distribNonneg_lineDerivOp_lineDerivOp_ofFun`](CalculusOfVariations/Distribution/Convex.lean#L223), [`convexOn_of_distribNonneg`](CalculusOfVariations/Distribution/Convex.lean#L285) | |
| mollification: Lipschitz with the same constant; of `ℤ^m`-periodic maps, periodic | [`plancherelMollify_lipschitzWith`](CalculusOfVariations/Lipschitz/Mollify.lean#L230), [`plancherelMollify_periodic`](CalculusOfVariations/Lipschitz/Mollify.lean#L254) | |
| componentwise mollification of Lipschitz maps: smooth, periodic for periodic maps, Lipschitz, supported near the support, `∇ → ∇φ` a.e. | [`mollifyPi_contDiff`](CalculusOfVariations/Lipschitz/Mollify.lean#L286), [`mollifyPi_periodic`](CalculusOfVariations/Lipschitz/Mollify.lean#L291), [`mollifyPi_lipschitzWith`](CalculusOfVariations/Lipschitz/Mollify.lean#L300), [`mollifyPi_eq_zero`](CalculusOfVariations/Lipschitz/Mollify.lean#L271), [`ae_tendsto_grad_mollifyPi`](CalculusOfVariations/Lipschitz/Mollify.lean#L307) | |
| smoothing of a rank-one convex `p` not quasiconvex at `0` | [`Smoothing.exists_smoothing`](CalculusOfVariations/Smoothing/RankOneConvex.lean#L232) | [K, proof of Prop. 2] |

`Qf = cubeInf f` is the infimum formula on the unit cube ([`cubeInf`](CalculusOfVariations/Envelope/Cube.lean#L35)).

All names are in the namespace [`CalculusOfVariations`](CalculusOfVariations) except those that begin with `Matrix`. Two of
them in Lean:

```lean
theorem CalculusOfVariations.quasiconvexAtOn_iff {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : Measurable f) (hbdd : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ)
    {Ω : Set (Fin m → ℝ)} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    QuasiconvexAtOn (unitCube m) f A ↔ QuasiconvexAtOn Ω f A

theorem CalculusOfVariations.quasiconvexEnvelope_eq_domainInf {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : Continuous f) {Ω : Set (Fin m → ℝ)} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (A : Matrix (Fin d) (Fin m) ℝ) :
    quasiconvexEnvelope f A = domainInf Ω f A
```

## Method

- **Rank-one convex functions** are locally Lipschitz by the proof of [R, Lemma 5.9]: convexity along
  the rank-one ray from `B` through `A` up to the sphere `∂B_{2r} (F)`, then a path from `A` to `B`
  along the terms of the singular value decomposition of `B − A`, which are orthogonal for the
  Frobenius inner product. Two gaps are filled or repaired: local boundedness (part of the definition
  in [R]) is proved by convexity in each entry, and the slope bound [R, (5.10)] is one-sided (exchange
  `A` and `B`).
- **Domain independence** follows [Da08, Prop. 5.11] and [R, Lemma 5.2 (i)]: extend the test map by
  zero and translate and scale the domain (one large cube, one small cube). For the test maps used here (Lipschitz, zero off the domain) on arbitrary bounded open sets, this
  uses that the gradient of a Lipschitz map vanishes almost everywhere on its zero set (Lebesgue
  density). The first domain must be nonempty.
- **Periodic test maps** follow [Da08, Prop. 5.13]: rescaled copies `ν⁻¹ φ (ν x)` and cut-offs.
- **Quadratic forms** follow [Da08, Thm 5.25 (i)]: the linear term integrates to zero, and the
  quadratic term is nonnegative under the Legendre–Hadamard condition, by Plancherel's formula,
  applied to smooth maps and then, by mollification, to Lipschitz maps.
- **Null Lagrangians** follow [Da08, Thm 8.35 (i)]: for smooth maps, (8.46) by induction on the
  order, with the expansion along the first row (Prop. 5.65), integration by parts and the identity
  (8.42) of [Da08, Thm 8.33], which is proved by induction on the order as well; then mollification
  (the smooth case on a ball, and `∇φ = 0` almost everywhere off `Ω`, since mollified maps need not
  have support in `Ω`). The induction is for minors of maps of `m` variables; [Da08] reduces to
  square matrices, but its induction step uses minors of order `s − 1` of maps of `s` variables.
  [Da08, Thm 8.33] is stated there for `C²` maps, here for smooth ones (for `C²` maps and order
  `s ≥ 3`, the second derivatives in its proof are those of functions that are only `C¹`). The orders
  `2` and `3` are also done with explicit formulas, by [Da08, Thm 8.35 (ii)] and [Mo, Lemma 5.1].
- **Quasiaffine functions** follow [Da08, Thm 5.20]: rank-one affine ⇒ affine combination of minors
  (next item) ⇒ null Lagrangian, by [Da08, Thm 8.35], the second of its two arguments (p. 181; the
  first goes through polyconvexity; [Da08, Cor. 5.22] is the same argument with part (ii)) ⇒
  quasiaffine ⇒ rank-one affine, by the theorem that quasiconvex functions are rank-one convex, which
  is proved here once, as in [R, Prop. 5.6] ([Da08] uses its Theorem 5.3, proved with its Lemma 3.11).
- **Rank-one affine functions** follow the proof of [Da08, Thm 5.20, (ii) ⇒ (iii′)]: induction on
  the number of rows (after a transposition, `N ≤ n`). The function is affine in its first row
  (5.42), the coefficients are combinations of minors of the other rows (5.43), the parts with a
  given set of other rows are rank-one affine, and Lemma 5.24 makes each part a combination of
  minors that contain the first row, by the vanishing of the `t²` coefficients along
  `(e_1 + e_2) ⊗ b`. Lemma 5.24, Part 2, is repaired: for `n > s + 1` the functions `X_β` of (5.47)
  are not rank-one affine and their sum is not `g`, so the columns are restricted to `β` first; the
  matrices `ξ` are chosen with zero columns, since the displayed coefficients omit terms, and then
  the vectors `b` are arbitrary. That rank-one affine functions are `C¹` is neither justified in the
  source nor needed (module docstring of [`CalculusOfVariations/Minors/RankOneAffine.lean`](CalculusOfVariations/Minors/RankOneAffine.lean)).
- **Quasiconvex ⇒ rank-one convex** follows [R, Prop. 5.6]: the sawtooth laminates
  `u_k = k⁻¹ h (k x_j) a` have two gradients, with the volume fractions `λ`, `1 − λ`; multiplied by
  cut-offs, with a diagonal choice of `k`, they are test maps with bounded gradients, whose energies
  differ from those of the `u_k` by at most a constant times the measure of the boundary layer. An
  orthogonal change of variables (a Householder reflection) and the independence of the domain give
  every rank-one direction. The truncated laminates
  `v_k = min (k⁻¹ h (k x_j), dist_∞ (x, ∂Q)) a` of [M, Lemma 4.3], which have finitely many
  gradients, give the inequality on a cube without any regularity of `f`.
- **Dacorogna's formula** follows [KP, Prop. 8.1]. (i) The infimum formula over `Ω` is at most the one
  over `D`, if `|∂D| = 0`: `Ω` is, up to a null set, a disjoint union of countably many copies of `D̄`
  (Vitali), and the rescaled copies of a test map glue to one with the same average. (ii) The formula
  `Qf` over the cube is rank-one convex: cut-off laminates on a cube with a face orthogonal to the
  direction, with test maps chosen independently on the slabs where the gradient is constant. (iii)
  `Qf` is `≡ −∞` or finite everywhere, along paths of rank-one segments, and then continuous, as a
  rank-one convex function. (iv) `Qf` is then quasiconvex: the inequality for piecewise affine test
  maps, by gluing almost minimisers into the pieces, and an approximation of the test maps by
  piecewise affine ones (mollification and Kuhn–Freudenthal interpolation), which [KP] leave to the
  reader. [KP] do not state the formula itself: a quasiconvex minorant is quasiconvex on `Ω`, so it
  is below every average over `Ω`; and `Qf` is `≡ −∞` or a quasiconvex minorant of `f`.
- **Distributions on `ℝ`.** Integration by parts for locally Lipschitz functions (absolute
  continuity); a convex function has a nonnegative second distributional derivative, by second
  differences and dominated convergence; conversely, the mollifications of a continuous `g` with
  `(ofFun g)'' ≥ 0` are smooth and convex, and converge to `g` pointwise.
- **Kuhn–Freudenthal interpolation** is the closed form
  `I_k ψ (x) = ∫_0^1 ψ (k⁻¹ ⌈k x − t 𝟙⌉) dt`: on each open simplex of the triangulation of
  `k⁻¹ ℤ^m` it is the affine interpolant of the values at the vertices, and its gradient there is a
  vector of difference quotients of `ψ` along edges of length `k⁻¹`; for a `C¹` map these
  converge uniformly (mean value theorem, uniform continuity of the derivative).
- **Smoothing** follows the first step of [K, proof of Prop. 2], with cut-offs that are functions
  of `|X|²` (module docstring of [`CalculusOfVariations/Smoothing/RankOneConvex.lean`](CalculusOfVariations/Smoothing/RankOneConvex.lean)).

## Shorter proofs

Arguments shorter or simpler than those of the sources, which the library follows ("checked in Lean":
the argument compiles against the library at `e474abf`, in a file that is not part of it):

- Rank-one convex ⇒ locally Lipschitz: a rank-one convex function is separately convex, and
  [`Matrix.locallyLipschitz_of_convexOn_single`](CalculusOfVariations/Convex/SeparatelyConvex.lean#L334) applies; no singular values, no explicit constant.
  Checked in Lean.
- The bound `√(min d m) osc (f; B̄_{6r} (F)) / (3r)` of [R, (5.9)]: the rows of `B − A` (or its
  columns) are Frobenius-orthogonal matrices of rank at most one and replace the singular value
  decomposition. On paper (the orthogonality of the rows checked in Lean).
- Quasiconvex ⇒ the two-point inequality along `a ⊗ e_j` ([R, Prop. 5.6] on the cube):
  [`quasiconvexAtOn_iff_periodic`](CalculusOfVariations/Quasiconvex/Periodic.lean#L108), tested with the periodic sawtooth `sawLaminate a j l 1`; no further
  cut-off. Checked in Lean.
- Rank-one affine ⇒ minors ([Da08, Thm 5.20]): `f` is multi-affine in the rows; the part `G_I` of `f`
  that is multilinear in the rows `I` (an alternating sum of `f` with rows set to zero) vanishes when
  two of these rows are equal, by the `t²` coefficient along `(e_i + e_j) ⊗ b`, so it is an
  alternating form, a combination of minors with the rows `I`; no induction, no transposition, no
  Lemma 5.24. On paper.
- Lemma 5.24 of [Da08]: the same argument shows that the part `g^i` with the other rows `I` is alternating in
  the rows `{1} ∪ I`. On paper.
- (8.42) and (8.43) of [Da08, Thm 8.33]: expand the Jacobian by Leibniz' formula, with the row `i₀`
  of the component left undifferentiated in (8.43); in (8.42) the involution `σ ↦ σ ∘ (i₀ i)` of the
  permutations exchanges two mixed second derivatives of `u^i` and changes the sign; no induction.
  68 lines instead of 89 (without docstrings). In the library's history, commit `cbc1d7b`.
- (8.44) of [Da08, Thm 8.35] from (8.43), by the proof of part (ii) with `v` affine: the minors of
  `A + ∇φ` are expanded into mixed minors [Da08, Prop. 5.67], and those with a row of `∇φ` are
  divergences; no induction. With the previous item, 186 lines instead of 264. In the library's
  history, commit `cbc1d7b`.
- Dacorogna's formula: (ii) of [KP, Prop. 8.1] is needed only along the `e_i ⊗ e_j`
  ([`cubeInf_le_two_point`](CalculusOfVariations/Envelope/RankOneConvex.lean#L311)), with [`Matrix.locallyLipschitz_of_convexOn_single`](CalculusOfVariations/Convex/SeparatelyConvex.lean#L334) for the continuity; no
  rotated cubes. Checked in Lean.

## Literature

Keys in brackets are in the [References](#references).

**The theorems.** Morrey [Mo] introduced quasiconvexity, proved that it is equivalent to the lower
semicontinuity of `∫ f (∇u)` under uniform convergence with bounded Lipschitz constants, and that
it implies rank-one convexity. The converse fails for `d ≥ 3`, `m ≥ 2` [Š]; for `d = 2`, preprints
of 2026 claim that it fails for `m ≥ 3` ([arXiv:2608.03488](https://arxiv.org/abs/2608.03488); also [arXiv:2608.12298](https://arxiv.org/abs/2608.12298), `m = 4`); it is open
for `2 × 2` matrices ([R], Chapter 8). Laminate proofs of the implication: [Fo], [M], [R]; the independence of
the domain by Vitali coverings: [BM]. Rank-one convex functions are locally Lipschitz by
[Mo, Thm 4.3] (continuous `f`) and [KK, Lemma 2.3] (any `f`). Rank-one convex quadratic forms:
[VH], [Mo, Thm 5.2]; they are polyconvex when `d = 2` or `m = 2`, not in general ([T],
[Da08, Thm 5.25]). Null Lagrangians are the affine combinations of minors: [La], [Er], [Ed],
[Ba77] (after Edelen, Ericksen and Rund, according to [Da08, p. 179]), and [BCO] for higher
derivatives; a short proof is in [CDKM]. The formula for the
quasiconvex envelope is due to Dacorogna [Da82], for cubes and growth conditions, and was extended
in [Fo], [Hü], [KP], [Da08]. Kristensen [K] deduced from [Š] that quasiconvexity is not a local
condition for `d ≥ 3`, `m ≥ 2`. On `ℝ`, convexity through the second distributional derivative is
due to Schwartz, and on `ℝ^n` to Reshetnyak and Dudley [Du].

**Formalizations** (searched on 22 November 2026: Mathlib, GitHub, the Palomar registry, arXiv,
the Lean Zulip archive, the Archive of Formal Proofs, MathComp-Analysis).

- Mathlib has the tools (convex functions, Rademacher's theorem, coverings, mollification,
  Plancherel's formula, alternating forms, distributions), not these notions: its `QuasiconvexOn`
  means convex sublevel sets.
- Lean developments with Morrey's quasiconvexity include
  [so3-r1c-and-not-qc](https://github.com/sergioconti/so3-r1c-and-not-qc) (Conti, Dolzmann,
  Dondl, [arXiv:2610.31886](https://arxiv.org/abs/2610.31886): a frame-indifferent counterexample on `ℝ^{3×3}`),
  [hierarchical_laminates_lean](https://github.com/lcao11/hierarchical_laminates_lean) (Cao: two
  envelopes that differ, for `d = 32`, `m = 2`; in that size, periodic quasiconvex functions below
  a continuous one are rank-one convex; functions convex in each coordinate and locally bounded
  are locally Lipschitz; a test with `C¹` periodic maps, whose envelope does not depend on the size of
  the cube) and [atlas-lean](https://github.com/facebookresearch/atlas-lean)
  (definitions for `2 × 2` matrices).
- [PDEAtlas](https://github.com/Robertboy18/PDEAtlas), after Evans, has null Lagrangians, the
  divergence form (for `C²` maps) and the weak continuity of minors of every order, and minimizers of
  polyconvex energies;
  [Tau Ceti](https://github.com/TauCetiProject/TauCeti) has Sobolev spaces on domains and the
  direct method.
- HOL Light has the Euler–Lagrange equations [GZWLSL]; nothing
  on Morrey's quasiconvexity was found in Isabelle or Rocq.

Beyond these, no earlier formalization was found of the independence of the domain, the
equivalence with periodic test maps, quasiconvex ⇒ rank-one convex in every size, rank-one convex
⇒ locally Lipschitz, Dacorogna's formula, the theorems on rank-one affine and quasiaffine functions
and on quadratic forms, Kristensen's smoothing, or convexity through Mathlib's distributions. The lower
semicontinuity and relaxation theorems, Young measures and `W^{1,p}` are not treated here.

## Planned extensions

- Dacorogna's formula for Borel, locally bounded integrands with a quasiconvex minorant [Da08,
  Thm 6.9].
- Mathlib-style names for the helper lemmas (prefixes `rd_`, `cv_`, `env_`, `glue_`, `lam_`,
  `distrib_`, `nl_`, and `plancherel` for the mollification lemmas), and one family of lemmas on
  gradients of Lipschitz maps in [`CalculusOfVariations/Lipschitz/Gradient.lean`](CalculusOfVariations/Lipschitz/Gradient.lean) instead of two.

## Using it from another Lake project

```toml
[[require]]
name = "CalculusOfVariations"
git = "https://github.com/vltanh/lean4-calculus-of-variations"
rev = "<commit>"
```

Then import the modules you need, for instance
`public import CalculusOfVariations.Quasiconvex.Domain`, or `import CalculusOfVariations` for
everything. The package requires Lean and Mathlib `v4.36.0-rc2`.

## Building

```sh
lake exe cache get                 # Mathlib's compiled files
lake build                         # the library and palomar/
lake env lean scripts/Audit.lean   # axioms; fails on any `sorry` of the library or a Solution
python3 scripts/sync_challenge_defs.py --check   # the Challenges' copies of the definitions
python3 scripts/linkify_docs.py --check          # the links of this file to the code
lake env lake comparator --config=palomar/Quasiconvexity/comparator.json   # and the other entries
```

## Palomar

The headline theorems are packaged for the [Palomar registry](https://palomar-registry.org) as three
entries, not submitted yet. An entry is a directory `palomar/<Entry>/`: `Challenge.lean` states the
theorems, with `sorry` proofs and the definitions they need, importing only Mathlib; `Solution.lean`
proves the same statements from the library; `comparator.json` configures Comparator, which checks
that the Solution proves the Challenge; `formalization.yaml` is the metadata (sources, scope,
differences from the sources).

| Entry | Theorems | Sources | Files |
| --- | --- | --- | --- |
| [`Quasiconvexity`](palomar/Quasiconvexity) | rank-one convex ⇒ locally Lipschitz, with the oscillation bound; quasiconvex ⇒ rank-one convex; independence of the domain; periodic test maps; quadratic forms | [R], [Da08] | [`Challenge.lean`](palomar/Quasiconvexity/Challenge.lean), [`Solution.lean`](palomar/Quasiconvexity/Solution.lean), [`comparator.json`](palomar/Quasiconvexity/comparator.json), [`formalization.yaml`](palomar/Quasiconvexity/formalization.yaml) |
| [`QuasiconvexEnvelope`](palomar/QuasiconvexEnvelope) | Dacorogna's formula; independence of the domain, rank-one convexity, continuity and quasiconvexity of the infimum formula | [KP], [Da82], [Da08] | [`Challenge.lean`](palomar/QuasiconvexEnvelope/Challenge.lean), [`Solution.lean`](palomar/QuasiconvexEnvelope/Solution.lean), [`comparator.json`](palomar/QuasiconvexEnvelope/comparator.json), [`formalization.yaml`](palomar/QuasiconvexEnvelope/formalization.yaml) |
| [`NullLagrangians`](palomar/NullLagrangians) | minors are null Lagrangians; rank-one affine ⇔ quasiaffine ⇔ null Lagrangian ⇔ affine combination of minors | [Da08], [Da82] | [`Challenge.lean`](palomar/NullLagrangians/Challenge.lean), [`Solution.lean`](palomar/NullLagrangians/Solution.lean), [`comparator.json`](palomar/NullLagrangians/comparator.json), [`formalization.yaml`](palomar/NullLagrangians/formalization.yaml) |

The definitions in the Challenges are copies of marked blocks of [`CalculusOfVariations/Basic.lean`](CalculusOfVariations/Basic.lean),
made by [`scripts/sync_challenge_defs.py`](scripts/sync_challenge_defs.py).

## Layout

| Path | Content |
| --- | --- |
| [`CalculusOfVariations/Basic.lean`](CalculusOfVariations/Basic.lean) | the definitions |
| [`CalculusOfVariations/Convex/`](CalculusOfVariations/Convex) | [`SeparatelyConvex`](CalculusOfVariations/Convex/SeparatelyConvex.lean) |
| [`CalculusOfVariations/RankOneConvex/`](CalculusOfVariations/RankOneConvex) | [`SingularValues`](CalculusOfVariations/RankOneConvex/SingularValues.lean), [`LocallyLipschitz`](CalculusOfVariations/RankOneConvex/LocallyLipschitz.lean) |
| [`CalculusOfVariations/Lipschitz/`](CalculusOfVariations/Lipschitz) | [`Gradient`](CalculusOfVariations/Lipschitz/Gradient.lean), [`Rescale`](CalculusOfVariations/Lipschitz/Rescale.lean), [`Periodic`](CalculusOfVariations/Lipschitz/Periodic.lean), [`Cutoff`](CalculusOfVariations/Lipschitz/Cutoff.lean), [`ZeroSet`](CalculusOfVariations/Lipschitz/ZeroSet.lean), [`Mollify`](CalculusOfVariations/Lipschitz/Mollify.lean), [`PiecewiseAffine`](CalculusOfVariations/Lipschitz/PiecewiseAffine.lean) |
| [`CalculusOfVariations/Covering/`](CalculusOfVariations/Covering) | [`Cubes`](CalculusOfVariations/Covering/Cubes.lean) (finite Besicovitch coverings) |
| [`CalculusOfVariations/Quasiconvex/`](CalculusOfVariations/Quasiconvex) | [`Domain`](CalculusOfVariations/Quasiconvex/Domain.lean), [`Cutoff`](CalculusOfVariations/Quasiconvex/Cutoff.lean), [`Periodic`](CalculusOfVariations/Quasiconvex/Periodic.lean), [`Laminate`](CalculusOfVariations/Quasiconvex/Laminate.lean), [`RankOneConvex`](CalculusOfVariations/Quasiconvex/RankOneConvex.lean), [`TruncatedLaminate`](CalculusOfVariations/Quasiconvex/TruncatedLaminate.lean) |
| [`CalculusOfVariations/QuadraticForm/`](CalculusOfVariations/QuadraticForm) | [`Plancherel`](CalculusOfVariations/QuadraticForm/Plancherel.lean), [`Quasiconvex`](CalculusOfVariations/QuadraticForm/Quasiconvex.lean) |
| [`CalculusOfVariations/Minors/`](CalculusOfVariations/Minors) | [`RankOneAffine`](CalculusOfVariations/Minors/RankOneAffine.lean), [`NullLagrangian`](CalculusOfVariations/Minors/NullLagrangian.lean) (orders `2`, `3`), [`Quasiaffine`](CalculusOfVariations/Minors/Quasiaffine.lean) (order `3`), [`AllOrders`](CalculusOfVariations/Minors/AllOrders.lean), [`Characterization`](CalculusOfVariations/Minors/Characterization.lean) |
| [`CalculusOfVariations/Envelope/`](CalculusOfVariations/Envelope) | [`Cube`](CalculusOfVariations/Envelope/Cube.lean) (the infimum formula on the cube), [`Domain`](CalculusOfVariations/Envelope/Domain.lean) (independence of the domain), [`RankOneConvex`](CalculusOfVariations/Envelope/RankOneConvex.lean), [`Glue`](CalculusOfVariations/Envelope/Glue.lean) (piecewise affine test maps), [`Convexity`](CalculusOfVariations/Envelope/Convexity.lean) (continuity, quasiconvexity), [`Formula`](CalculusOfVariations/Envelope/Formula.lean) |
| [`CalculusOfVariations/Smoothing/`](CalculusOfVariations/Smoothing) | [`RankOneConvex`](CalculusOfVariations/Smoothing/RankOneConvex.lean) |
| [`CalculusOfVariations/Distribution/`](CalculusOfVariations/Distribution) | [`SecondDerivative`](CalculusOfVariations/Distribution/SecondDerivative.lean), [`Convex`](CalculusOfVariations/Distribution/Convex.lean) |
| [`palomar/`](palomar) | the Palomar entries |
| [`scripts/`](scripts) | [`Audit.lean`](scripts/Audit.lean) (the axiom audit), [`sync_challenge_defs.py`](scripts/sync_challenge_defs.py), [`linkify_docs.py`](scripts/linkify_docs.py), [`check_md_tables.py`](scripts/check_md_tables.py) |
| [`.github/workflows/`](.github/workflows) | CI: build, audit, import list of the audit, copies of the definitions, links, tables, line lengths; Palomar's preflight, one per entry, on demand |

## References

- [M] S. Müller, *Variational models for microstructure and phase transitions*, Max-Planck-Institut
  für Mathematik in den Naturwissenschaften, Leipzig,
  [Lecture notes no. 2, 1998](https://www.mis.mpg.de/publications/preprint-repository/lecture_note/1998/issue-2)
  (C.I.M.E. summer school, Cetraro, 1996; also in Lecture Notes in Math. 1713, Springer, 1999,
  85–210, [doi:10.1007/BFb0092670](https://doi.org/10.1007/BFb0092670)): Definition 4.2 and Remark 3; Lemma 4.3; the density argument of Theorem 4.4
  (i); Theorem 4.5 (iii) (statement).
- [R] F. Rindler, *Calculus of Variations*, 2nd ed., Graduate Texts in Mathematics 310, Springer,
  2026, [doi:10.1007/978-3-032-24483-3](https://doi.org/10.1007/978-3-032-24483-3): Lemma 5.2 (i), Proposition 5.6, Lemma 5.9, Appendix A.1; Chapter 8.
- [Mo] C. B. Morrey, *Quasi-convexity and the lower semicontinuity of multiple integrals*, Pacific
  J. Math. 2 (1952), 25–53, [doi:10.2140/pjm.1952.2.25](https://doi.org/10.2140/pjm.1952.2.25): Lemmas 4.1 (statement), 5.1; Theorems 2.1, 2.2, 4.1–4.3, 5.2.
- [Da82] B. Dacorogna, *Quasiconvexity and relaxation of nonconvex problems in the calculus of
  variations*, J. Funct. Anal. 46 (1982), 102–118,
  [doi:10.1016/0022-1236(82)90046-5](<https://doi.org/10.1016/0022-1236(82)90046-5>): Proposition 4, Theorem 5 (statements).
- [KP] D. Kinderlehrer, P. Pedregal, *Characterizations of Young measures generated by gradients*,
  Arch. Rational Mech. Anal. 115 (1991), 329–365,
  [doi:10.1007/BF00375279](https://doi.org/10.1007/BF00375279): Proposition 8.1, with Step 6 of the proof of
  Proposition 7.2.
- [Da08] B. Dacorogna, *Direct methods in the calculus of variations*, 2nd ed., Springer, 2008,
  [doi:10.1007/978-0-387-55249-1](https://doi.org/10.1007/978-0-387-55249-1): Theorem 5.3 (i), (iv) (statements), Propositions 5.11, 5.13, Theorem 5.20 with Lemma 5.24,
  Corollary 5.22 (statement), Theorem 5.25 (i), Propositions 5.65, 5.67, Theorem 6.9 (statement),
  Theorems 8.33, 8.35.
- [K] J. Kristensen, *On the non-locality of quasiconvexity*, Ann. Inst. H. Poincaré Anal. Non
  Linéaire 16 (1999), 1–13, [doi:10.1016/S0294-1449(99)80006-7](<https://doi.org/10.1016/S0294-1449(99)80006-7>),
  [Numdam](https://www.numdam.org/item/AIHPC_1999__16_1_1_0/): proof of Proposition 2.
- [F] H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*, Ann. of Math. 43 (1942),
  580–582, [doi:10.2307/1968813](https://doi.org/10.2307/1968813).
- [Ku] H. W. Kuhn, *Some combinatorial lemmas in topology*, IBM J. Res. Develop. 4 (1960),
  518–524, [doi:10.1147/rd.45.0518](https://doi.org/10.1147/rd.45.0518).

Cited in the section on the literature only:

- [Š] V. Šverák, *Rank-one convexity does not imply quasiconvexity*, Proc. Roy. Soc. Edinburgh Sect.
  A 120 (1992), 185–189, [doi:10.1017/S0308210500015080](https://doi.org/10.1017/S0308210500015080).
- [Fo] I. Fonseca, *The lower quasiconvex envelope of the stored energy function for an elastic
  crystal*, J. Math. Pures Appl. (9) 67 (1988), 175–195,
  [zbMATH 4185175](https://zbmath.org/4185175).
- [BM] J. M. Ball, F. Murat, *`W^{1,p}`-quasiconvexity and variational problems for multiple
  integrals*, J. Funct. Anal. 58 (1984), 225–253,
  [doi:10.1016/0022-1236(84)90041-7](<https://doi.org/10.1016/0022-1236(84)90041-7>).
- [KK] B. Kirchheim, J. Kristensen, *On rank-one convex functions that are homogeneous of degree
  one*, Arch. Ration. Mech. Anal. 221 (2016), 527–558,
  [doi:10.1007/s00205-016-0967-1](https://doi.org/10.1007/s00205-016-0967-1).
- [VH] L. Van Hove, *Sur l'extension de la condition de Legendre du calcul des variations aux
  intégrales multiples à plusieurs fonctions inconnues*, Proc. Akad. Wet. Amsterdam 50 (1947),
  18–23, [zbMATH 3046021](https://zbmath.org/3046021).
- [T] F. J. Terpstra, *Die Darstellung biquadratischer Formen als Summen von Quadraten mit Anwendung
  auf die Variationsrechnung*, Math. Ann. 116 (1938/39), 166–180,
  [doi:10.1007/BF01597353](https://doi.org/10.1007/BF01597353).
- [La] A. W. Landers, *Invariant multiple integrals in the calculus of variations*, Contributions to
  the Calculus of Variations 1938–1941, Univ. of Chicago Press, 1942, 175–207,
  [zbMATH 3105419](https://zbmath.org/3105419).
- [Er] J. L. Ericksen, *Nilpotent energies in liquid crystal theory*, Arch. Ration. Mech. Anal. 10
  (1962), 189–196, [doi:10.1007/BF00281186](https://doi.org/10.1007/BF00281186).
- [Ed] D. G. B. Edelen, *The null set of the Euler–Lagrange operator*, Arch. Ration. Mech. Anal. 11
  (1962), 117–121, [doi:10.1007/BF00253934](https://doi.org/10.1007/BF00253934).
- [Ba77] J. M. Ball, *Convexity conditions and existence theorems in nonlinear elasticity*, Arch.
  Ration. Mech. Anal. 63 (1976/77), 337–403, [doi:10.1007/BF00279992](https://doi.org/10.1007/BF00279992).
- [BCO] J. M. Ball, J. C. Currie, P. J. Olver, *Null Lagrangians, weak continuity, and variational
  problems of arbitrary order*, J. Funct. Anal. 41 (1981), 135–174,
  [doi:10.1016/0022-1236(81)90085-9](<https://doi.org/10.1016/0022-1236(81)90085-9>).
- [CDKM] S. Conti, G. Dolzmann, B. Kirchheim, S. Müller, *Sufficient conditions for the validity of
  the Cauchy–Born rule close to SO(n)*, J. Eur. Math. Soc. 8 (2006), 515–530,
  [doi:10.4171/jems/65](https://doi.org/10.4171/jems/65): Theorem 6.1.
- [Hü] F. V. Gusejnov (Hüsseinov), *Continuity of quasiconvex functions and a theorem on
  quasiconvexity* (Russian), Izv. Akad. Nauk Az. SSR, Ser. Fiz.-Tekh. Mat. Nauk 1988, no. 1, 20–25,
  [zbMATH 4082371](https://zbmath.org/4082371).
- [Du] R. M. Dudley, *On second derivatives of convex functions*, Math. Scand. 41 (1977), 159–174,
  [doi:10.7146/math.scand.a-11710](https://doi.org/10.7146/math.scand.a-11710); *Acknowledgment of
  priority: Second derivatives of convex functions*, Math. Scand. 46 (1980), 61,
  [doi:10.7146/math.scand.a-11851](https://doi.org/10.7146/math.scand.a-11851).
- [GZWLSL] Y. Guan, J. Zhang, G. Wang, X. Li, Z. Shi, Y. Li, *Formalization of Euler–Lagrange
  equation set based on variational calculus in HOL Light*, J. Automat. Reason. 65 (2021), 1–29,
  [doi:10.1007/s10817-020-09549-w](https://doi.org/10.1007/s10817-020-09549-w).

## Credits

- Maintained by The-Anh Vu-Le.
- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code.
- No person has reviewed the statements or the proofs.

## License

Apache-2.0; see [LICENSE](LICENSE).
