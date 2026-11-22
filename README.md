# Calculus of variations in Lean: quasiconvexity, rank-one convexity, the quasiconvex envelope

[![Lean Action CI](https://github.com/vltanh/lean4-calculus-of-variations/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-calculus-of-variations/actions/workflows/lean_action_ci.yml)

Lean 4 with Mathlib `v4.36.0-rc2`, for integrands `f : ℝ^{d×m} → ℝ` and Lipschitz maps
`φ : ℝ^m → ℝ^d` (sup norms):

- **Rank-one convexity and quasiconvexity.** A rank-one convex function is locally Lipschitz, with
  a bound by its oscillation (and so is a separately convex function); a quasiconvex integrand is
  rank-one convex, by laminates, cut off near the boundary of a cube with faces orthogonal to the
  rank-one direction; quasiconvexity does not
  depend on the bounded open domain, and may be tested with periodic maps.
- **Quadratic forms and minors.** A rank-one convex quadratic form is quasiconvex; a rank-one
  affine function is an affine combination of minors; the minors of order `2` and `3` are null
  Lagrangians, and the `3 × 3` minors are quasiaffine.
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
declaration of the library depends only on `propext`, `Classical.choice` and `Quot.sound` (no
`sorry`, no `axiom`, no `native_decide`).

## Main statements

`unitCube m = (0, 1)^m`; `grad φ x` is the `d × m` matrix of partial derivatives; a test map on `Ω`
is a Lipschitz `φ` vanishing outside `Ω`. The definitions are in
[`CalculusOfVariations/Basic.lean`](CalculusOfVariations/Basic.lean) ([M, Def. 4.2], with the
conventions of the package): `RankOneConvex`,
`RankOneAffine`, `QuasiconvexAtOn Ω f A` (`|Ω| f (A) ≤ ∫_Ω f (A + ∇φ)` for every test map on `Ω`
for which the integral exists), `QuasiconvexAtPeriodic`, `Quasiconvex` (on the unit cube, at every
matrix), `IsLocallyBounded`, and `qcEnvelope` (the supremum of the quasiconvex, lower
semicontinuous, locally bounded minorants, in `EReal`).

| Statement | Lean | Source |
| --- | --- | --- |
| separately convex ⇒ bounded on cubes, locally Lipschitz | `Matrix.exists_abs_le_of_convexOn_single`, `Matrix.locallyLipschitz_of_convexOn_single` | [M, Def. 4.2, Remark 3] |
| rank-one convex ⇒ locally Lipschitz; in the Frobenius norm, `lip (f; B_r (F)) ≤ √(min d m) osc (f; B̄_{6r} (F)) / (3r)` | `RankOneConvex.locallyLipschitz`, `RankOneConvex.abs_sub_le_of_osc` | [R, Lemma 5.9] (without (5.8)) |
| `M = ∑_{i < min d m} σ_i p_i ⊗ q_i`, `σ_0 ≥ σ_1 ≥ … ≥ 0`, `p_i`, `q_i` orthonormal (singular value decomposition) | `Matrix.exists_singularValueDecomposition` | [R, Appendix A.1] |
| `f` lsc, locally bounded, quasiconvex at `F` on the unit cube ⇒ `f (F) ≤ λ f (F + (1−λ) a ⊗ n) + (1−λ) f (F − λ a ⊗ n)`, by laminates with cut-offs | `le_of_quasiconvexAtOn_vecMulVec`, with `sawLaminate`, `setIntegral_sawLaminate`, `le_of_quasiconvexAtOn_of_tendsto` (the cut-off), `le_of_quasiconvexAtOn_unitCube_of_lsc` (`n = e_j`) | [R, Prop. 5.6] |
| `f` lsc, locally bounded, quasiconvex ⇒ rank-one convex | `rankOneConvex_of_quasiconvex` | [R, Prop. 5.6] |
| without regularity of `f`: quasiconvex at `F` on the unit cube ⇒ the two-point inequality along `a ⊗ e_j`, by truncated laminates; on a rotated cube, along `a ⊗ R e_j` | `le_of_quasiconvexAtOn_unitCube`, `le_of_quasiconvexAtOn_orthogonal`, with `cubeLaminate` | [M, Lemma 4.3] |
| quasiconvexity on the cube ⇔ on any nonempty bounded open `Ω` | `quasiconvexAtOn_iff`, `quasiconvexAtOn_of_unitCube` | [Da08, Prop. 5.11], [R, Lemma 5.2 (i)] |
| quasiconvexity on the cube ⇔ with periodic test maps | `quasiconvexAtOn_iff_periodic` | [Da08, Prop. 5.13] |
| `Q` bilinear, `A ↦ Q (A, A)` rank-one convex ⇒ quasiconvex | `quadraticForm_quasiconvex` | [Da08, Thm 5.25 (i)] |
| rank-one affine ⇒ affine combination of minors (continuity not assumed) | `RankOneAffine.exists_eq_sum_minor`; for continuous functions, `RankOneAffine.exists_eq_sum_minor_of_continuous` | [Da08, Thm 5.20, (ii) ⇒ (iii′)] |
| `∫ minor (∇φ) = 0` for `2 × 2`, `3 × 3` minors, `φ` Lipschitz with compact support | `nl_null2`, `nl_null3` | [Da08, Thm 8.35], [Mo, Lemma 5.1] |
| `∫_Q minor (A + ∇φ) = minor A` for `3 × 3` minors, `φ` a test map on `Q` | `nl_minor3_quasiaffine` | [Da08, Thm 8.35] |
| `f^{qc} (A) = inf_φ ⨍_Ω f (A + ∇φ)`, `Ω` nonempty, bounded, open, `f` continuous; `Ω` the unit ball | `qcEnvelope_eq_iInf`, `qcEnvelope_eq_iInf_unitBall` | from [KP, Prop. 8.1]; [Da82, Thm 5], [Da08, Thm 6.9] |
| the infimum formula does not depend on the domain (null boundaries): copies of a test map by Vitali's theorem | `domainInf_eq`, `domainInf_le_domainInf`, `exists_testMap_setIntegral_eq` | [KP, Prop. 8.1 (i)] |
| `Qf (F) ≤ λ Qf (F + (1−λ) a ⊗ n) + (1−λ) Qf (F − λ a ⊗ n)`, in `EReal`; `Qf` finite ⇒ rank-one convex, continuous | `cubeInf_le_two_point_vecMulVec`, `cubeInf_le_two_point` (`n = e_j`), `cubeInfReal_rankOneConvex`, `cubeInfReal_continuous` | [KP, Prop. 8.1 (ii), (iii)] |
| `⨍_Q Qf (F + ∇ψ) ≥ Qf (F)` for piecewise affine test maps `ψ`; `Qf` finite ⇒ quasiconvex | `cubeInf_le_sum_of_piecewiseAffine`, `cubeInfReal_quasiconvex` | [KP, Prop. 8.1 (iv), Prop. 7.2, Step 6] |
| Kuhn–Freudenthal interpolation: Lipschitz, piecewise affine; for `C¹` maps with compact support, `∇ I_k ψ → ∇ψ` uniformly | `kuhnInterpolation_lipschitz`, `kuhnInterpolation_piecewiseAffineOn`, `kuhnInterpolation_grad_uniform` | [F], [Ku] (the triangulation) |
| `⟨(ofFun g)'', ψ⟩ = ∫ g ψ''`; `(ofFun f)' = ofFun f'` for locally Lipschitz `f`; Leibniz for `(h f)''` | `lineDerivOp_lineDerivOp_ofFun_apply`, `lineDerivOp_ofFun_eq_ofFun_deriv`, `integral_deriv_deriv_mul_mul`, `lineDerivOp_lineDerivOp_ofFun_mul_apply` | |
| on `ℝ`: `f` convex ⇒ `(ofFun f)'' ≥ 0`; `g` continuous with `(ofFun g)'' ≥ 0` ⇒ `g` convex | `ConvexOn.distribNonneg_lineDerivOp_lineDerivOp_ofFun`, `convexOn_of_distribNonneg` | |
| mollification: Lipschitz with the same constant; of `ℤ^m`-periodic maps, periodic | `plancherelMollify_lipschitzWith`, `plancherelMollify_periodic` | |
| componentwise mollification of Lipschitz maps: smooth, periodic for periodic maps, Lipschitz, supported near the support, `∇ → ∇φ` a.e. | `mollifyPi_contDiff`, `mollifyPi_periodic`, `mollifyPi_lipschitzWith`, `mollifyPi_eq_zero`, `ae_tendsto_grad_mollifyPi` | |
| smoothing of a rank-one convex `p` not quasiconvex at `0` | `Smoothing.exists_smoothing` | [K, proof of Prop. 2] |

`Qf = cubeInf f` is the infimum formula on the unit cube.

All names are in the namespace `CalculusOfVariations` except those that begin with `Matrix`. Two of
them in Lean:

```lean
theorem CalculusOfVariations.quasiconvexAtOn_iff {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ)
    {Ω : Set (Fin m → ℝ)} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    QuasiconvexAtOn (unitCube m) f A ↔ QuasiconvexAtOn Ω f A

theorem CalculusOfVariations.qcEnvelope_eq_iInf {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : Continuous f) {Ω : Set (Fin m → ℝ)} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (A : Matrix (Fin d) (Fin m) ℝ) :
    qcEnvelope f A =
      ⨅ (φ : (Fin m → ℝ) → Fin d → ℝ) (_ : (∃ K, LipschitzWith K φ) ∧ ∀ x ∉ Ω, φ x = 0),
        (((volume Ω).toReal⁻¹ * ∫ x in Ω, f (A + grad φ x) : ℝ) : EReal)
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
- **Null Lagrangians** follow [Da08, Thm 8.35 (ii)] and [Mo, Lemma 5.1]: divergence identities for
  smooth maps, then mollification.
- **Rank-one affine functions** follow the proof of [Da08, Thm 5.20, (ii) ⇒ (iii′)]: induction on
  the number of rows (after a transposition, `N ≤ n`). The function is affine in its first row
  (5.42), the coefficients are combinations of minors of the other rows (5.43), the parts with a
  given set of other rows are rank-one affine, and Lemma 5.24 makes each part a combination of
  minors that contain the first row, by the vanishing of the `t²` coefficients along
  `(e_1 + e_2) ⊗ b`. Lemma 5.24, Part 2, is repaired: for `n > s + 1` the functions `X_β` of (5.47)
  are not rank-one affine and their sum is not `g`, so the columns are restricted to `β` first; the
  matrices `ξ` are chosen with zero columns, since the displayed coefficients omit terms, and then
  the vectors `b` are arbitrary. That rank-one affine functions are `C¹` is neither justified in the
  source nor needed (module docstring of `Minors/RankOneAffine.lean`).
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
  of `|X|²` (module docstring of `Smoothing/RankOneConvex.lean`).

## Simpler proofs

Arguments shorter or simpler than those of the sources, which the library follows:

- Rank-one convex ⇒ locally Lipschitz: a rank-one convex function is separately convex, and
  `Matrix.locallyLipschitz_of_convexOn_single` applies; no singular values, no explicit constant.
  Checked in Lean.
- The bound `√(min d m) osc (f; B̄_{6r} (F)) / (3r)` of [R, (5.9)]: the rows of `B − A` (or its
  columns) are Frobenius-orthogonal matrices of rank at most one and replace the singular value
  decomposition. On paper (the orthogonality of the rows checked in Lean).
- Quasiconvex ⇒ the two-point inequality along `a ⊗ e_j` ([R, Prop. 5.6] on the cube):
  `quasiconvexAtOn_iff_periodic`, tested with the periodic sawtooth `sawLaminate a j l 1`; no further
  cut-off. Checked in Lean.
- Rank-one affine ⇒ minors ([Da08, Thm 5.20]): `f` is multi-affine in the rows; the part `G_I` of `f`
  that is multilinear in the rows `I` (an alternating sum of `f` with rows set to zero) vanishes when
  two of these rows are equal, by the `t²` coefficient along `(e_i + e_j) ⊗ b`, so it is an
  alternating form, a combination of minors with the rows `I`; no induction, no transposition, no
  Lemma 5.24. On paper.
- Lemma 5.24 of [Da08]: the same argument shows that `g` is alternating in the rows `{1} ∪ I`. On
  paper.
- Dacorogna's formula: (ii) of [KP, Prop. 8.1] is needed only along the `e_i ⊗ e_j`
  (`cubeInf_le_two_point`), with `Matrix.locallyLipschitz_of_convexOn_single` for the continuity; no
  rotated cubes. Checked in Lean.

## Planned extensions

- Minors of every order are null Lagrangians and quasiaffine.
- Mathlib-style names for the helper lemmas (prefixes `rd_`, `cv_`, `env_`, `glue_`, `lam_`,
  `distrib_`, `nl_`, and `plancherel` for the mollification lemmas), and one family of lemmas on
  gradients of Lipschitz maps in `Lipschitz/Gradient.lean` instead of two.

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
lake build
lake env lean scripts/Audit.lean   # axioms; fails on any `sorry`
```

## Layout

| Path | Content |
| --- | --- |
| [`CalculusOfVariations/Basic.lean`](CalculusOfVariations/Basic.lean) | the definitions |
| [`CalculusOfVariations/Convex/`](CalculusOfVariations/Convex) | `SeparatelyConvex` |
| [`CalculusOfVariations/RankOneConvex/`](CalculusOfVariations/RankOneConvex) | `SingularValues`, `LocallyLipschitz` |
| [`CalculusOfVariations/Lipschitz/`](CalculusOfVariations/Lipschitz) | `Gradient`, `Rescale`, `Periodic`, `Cutoff`, `ZeroSet`, `Mollify`, `PiecewiseAffine` |
| [`CalculusOfVariations/Covering/`](CalculusOfVariations/Covering) | `Cubes` (finite Besicovitch coverings) |
| [`CalculusOfVariations/Quasiconvex/`](CalculusOfVariations/Quasiconvex) | `Domain`, `Cutoff`, `Periodic`, `Laminate`, `RankOneConvex`, `TruncatedLaminate` |
| [`CalculusOfVariations/QuadraticForm/`](CalculusOfVariations/QuadraticForm) | `Plancherel`, `Quasiconvex` |
| [`CalculusOfVariations/Minors/`](CalculusOfVariations/Minors) | `RankOneAffine`, `RankOneAffineContinuous`, `NullLagrangian`, `Quasiaffine` |
| [`CalculusOfVariations/Envelope/`](CalculusOfVariations/Envelope) | `Cube` (the infimum formula on the cube), `Domain` (independence of the domain), `RankOneConvex`, `Glue` (piecewise affine test maps), `Convexity` (continuity, quasiconvexity), `Formula` |
| [`CalculusOfVariations/Smoothing/`](CalculusOfVariations/Smoothing) | `RankOneConvex` |
| [`CalculusOfVariations/Distribution/`](CalculusOfVariations/Distribution) | `SecondDerivative`, `Convex` |
| [`scripts/Audit.lean`](scripts/Audit.lean) | the axiom audit |
| [`.github/workflows/`](.github/workflows) | CI: build, audit, import list of the audit, line lengths |

## References

- [M] S. Müller, *Variational models for microstructure and phase transitions*, Max-Planck-Institut
  für Mathematik in den Naturwissenschaften, Leipzig, Lecture notes no. 2, 1998 (C.I.M.E. summer
  school, Cetraro, 1996): Definition 4.2 and Remark 3; Lemma 4.3; the density argument of Theorem 4.4
  (i).
- [R] F. Rindler, *Calculus of Variations*, 2nd ed., Graduate Texts in Mathematics 310, Springer,
  2026: Lemma 5.2 (i), Proposition 5.6, Lemma 5.9 (cited in the literature as Lemma 5.6 of the first edition, 2018), Appendix A.1.
- [Mo] C. B. Morrey, *Quasi-convexity and the lower semicontinuity of multiple integrals*, Pacific
  J. Math. 2 (1952), 25–53: Lemma 5.1.
- [Da82] B. Dacorogna, *Quasiconvexity and relaxation of nonconvex problems in the calculus of
  variations*, J. Funct. Anal. 46 (1982), 102–118.
- [KP] D. Kinderlehrer, P. Pedregal, *Characterizations of Young measures generated by gradients*,
  Arch. Rational Mech. Anal. 115 (1991), 329–365: Proposition 8.1, with Step 6 of the proof of
  Proposition 7.2.
- [Da08] B. Dacorogna, *Direct methods in the calculus of variations*, 2nd ed., Springer, 2008:
  Propositions 5.11, 5.13, Theorem 5.20 with Lemma 5.24, Theorem 5.25 (i), Theorem 6.9 (statement), Theorem 8.35.
- [K] J. Kristensen, *On the non-locality of quasiconvexity*, Ann. Inst. H. Poincaré Anal. Non
  Linéaire 16 (1999), 1–13: proof of Proposition 2.
- [F] H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*, Ann. of Math. 43 (1942),
  580–582.
- [Ku] H. W. Kuhn, *Some combinatorial lemmas in topology*, IBM J. Res. Develop. 4 (1960),
  518–524.

## Credits

- Maintained by The-Anh Vu-Le.
- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code.
- No person has reviewed the statements or the proofs.

## License

Apache-2.0; see [LICENSE](LICENSE).
