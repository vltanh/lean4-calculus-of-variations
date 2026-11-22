# Calculus of variations in Lean: quasiconvexity, rank-one convexity, the quasiconvex envelope

[![Lean Action CI](https://github.com/vltanh/lean4-calculus-of-variations/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-calculus-of-variations/actions/workflows/lean_action_ci.yml)

Lean 4 with Mathlib `v4.36.0-rc2`, for integrands `f : ℝ^{d×m} → ℝ` and Lipschitz maps
`φ : ℝ^m → ℝ^d` (sup norms):

- **Rank-one convexity and quasiconvexity.** A separately convex function is locally Lipschitz, so
  a rank-one convex function is locally Lipschitz; a quasiconvex integrand is rank-one convex, by
  laminates on a cube with faces orthogonal to the rank-one direction; quasiconvexity does not
  depend on the bounded open domain, and may be tested with periodic maps.
- **Quadratic forms and minors.** A rank-one convex quadratic form is quasiconvex; a rank-one
  affine function is an affine combination of minors; the minors of order `2` and `3` are null
  Lagrangians, and the `3 × 3` minors are quasiaffine.
- **The quasiconvex envelope.** Dacorogna's formula `f^{qc} (A) = inf_φ ⨍_Ω f (A + ∇φ)` on every
  nonempty bounded open `Ω`, for continuous `f`, with values in `EReal`; the inequality
  `⨍ Qf (F + ∇ψ) ≥ Qf (F)` for piecewise affine test maps `ψ` behind it.
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
| separately convex ⇒ locally Lipschitz | `Matrix.locallyLipschitz_of_convexOn_single` | [M, Def. 4.2, Remark 3] |
| rank-one convex ⇒ locally Lipschitz | `RankOneConvex.locallyLipschitz` | [M, Def. 4.2, Remark 3] |
| quasiconvex at `F` on the unit cube ⇒ `f (F) ≤ λ f (F + (1−λ) a ⊗ e_j) + (1−λ) f (F − λ a ⊗ e_j)`, by laminates; on a rotated cube, in the direction `a ⊗ R e_j`; for `f` lsc and locally bounded, in every direction `a ⊗ n` | `le_of_quasiconvexAtOn_unitCube`, `le_of_quasiconvexAtOn_orthogonal`, `le_of_quasiconvexAtOn_vecMulVec`, with `cubeLaminate` | [M, Lemma 4.3] |
| `f` lsc, locally bounded, quasiconvex ⇒ rank-one convex | `rankOneConvex_of_quasiconvex` | [M, Lemma 4.3] |
| quasiconvexity on the cube ⇔ on any nonempty bounded open `Ω` | `quasiconvexAtOn_iff`, `quasiconvexAtOn_of_unitCube` | [M, Def. 4.2, Remark 2] |
| quasiconvexity on the cube ⇔ with periodic test maps | `quasiconvexAtOn_iff_periodic` | [M, Prop. 4.19] |
| `Q` bilinear, `A ↦ Q (A, A)` rank-one convex ⇒ quasiconvex | `quadraticForm_quasiconvex` | [Da08, Thm 5.25 (i)]; [Mo, Thm 5.2] |
| continuous, rank-one affine ⇒ affine combination of minors | `RankOneAffine.exists_eq_sum_minor_of_continuous` | [Da08, Thm 5.20, (iii) ⇒ (iv)]; proof of [CDKM, Thm 6.1] |
| rank-one affine ⇒ affine combination of minors (no continuity) | `RankOneAffine.exists_eq_sum_minor` | generalizes [Da08, Thm 5.20, (iii) ⇒ (iv)]; second half of the proof of [CDKM, Thm 6.1] |
| a homogeneous polynomial of degree `k` vanishing on the matrices of rank `< k` is a combination of `k × k` minors | `exists_eq_sum_minor_of_rank_lt` | proof of [CDKM, Thm 6.1] |
| `D^k h` of a smooth `h` is symmetric; a symmetric multilinear form vanishing on the diagonal vanishes; Taylor's formula when `D^{n+1} h = 0` | `iteratedFDeriv_comp_perm_of_contDiff`, `eq_zero_of_symmetric_of_apply_diag_eq_zero`, `eq_sum_iteratedFDeriv_of_iteratedFDeriv_eq_zero` | [CDKM, Prop. 6.2] (the second) |
| `∫ minor (∇φ) = 0` for `2 × 2`, `3 × 3` minors, `φ` Lipschitz with compact support | `nl_null2`, `nl_null3` | [Mo, Lemma 5.1] |
| `∫_Q minor (A + ∇φ) = minor A` for `3 × 3` minors, `φ` a test map on `Q` | `nl_minor3_quasiaffine` | |
| `f^{qc} (A) = inf_φ ⨍_Ω f (A + ∇φ)`, `Ω` nonempty, bounded, open, `f` continuous; `Ω` the unit ball | `qcEnvelope_eq_iInf`, `qcEnvelope_eq_iInf_unitBall` | [KP, Prop. 8.1], [Da82]; proof of [M, Thm 4.5 (iii)] |
| `⨍_Q Qf (F + ∇ψ) ≥ Qf (F)` for piecewise affine test maps `ψ`; the two-point inequality of `Qf` | `cubeInf_le_sum_of_piecewiseAffine`, `cubeInf_le_two_point` | [M, (4.28)] |
| Kuhn–Freudenthal interpolation: Lipschitz, piecewise affine; for `C¹` maps with compact support, `∇ I_k ψ → ∇ψ` uniformly | `kuhnInterpolation_lipschitz`, `kuhnInterpolation_piecewiseAffineOn`, `kuhnInterpolation_grad_uniform` | [F], [Ku] (the triangulation) |
| `⟨(ofFun g)'', ψ⟩ = ∫ g ψ''`; `(ofFun f)' = ofFun f'` for locally Lipschitz `f`; Leibniz for `(h f)''` | `lineDerivOp_lineDerivOp_ofFun_apply`, `lineDerivOp_ofFun_eq_ofFun_deriv`, `integral_deriv_deriv_mul_mul`, `lineDerivOp_lineDerivOp_ofFun_mul_apply` | |
| on `ℝ`: `f` convex ⇒ `(ofFun f)'' ≥ 0`; `g` continuous with `(ofFun g)'' ≥ 0` ⇒ `g` convex | `ConvexOn.distribNonneg_lineDerivOp_lineDerivOp_ofFun`, `convexOn_of_distribNonneg` | |
| mollification: Lipschitz with the same constant; of `ℤ^m`-periodic maps, periodic | `plancherelMollify_lipschitzWith`, `plancherelMollify_periodic` | |
| componentwise mollification of Lipschitz maps: smooth, periodic for periodic maps, Lipschitz, supported near the support, `∇ → ∇φ` a.e. | `mollifyPi_contDiff`, `mollifyPi_periodic`, `mollifyPi_lipschitzWith`, `mollifyPi_eq_zero`, `ae_tendsto_grad_mollifyPi` | |
| smoothing of a rank-one convex `p` not quasiconvex at `0` | `Smoothing.exists_smoothing` | [K, proof of Prop. 2] |

`Qf = cubeInf f` is the infimum formula on the unit cube.

All names are in the namespace `CalculusOfVariations` except
`Matrix.locallyLipschitz_of_convexOn_single`. Two of them in Lean:

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

- **Domain independence** follows [M, Def. 4.2, Remark 2]: extend the test map by zero and
  translate and scale the domain (one large cube, one small cube). Instead of `|∂Ω| = 0`, the
  gradient of a Lipschitz map vanishes almost everywhere on its zero set (Lebesgue density).
- **Quadratic forms** follow [Mo, Thm 5.2]: the linear term integrates to zero, and the quadratic
  term is nonnegative under the Legendre–Hadamard condition, for smooth maps (Morrey cites Van Hove;
  here by Plancherel's formula for Schwartz functions) and then for Lipschitz maps (here by
  mollification).
- **Null Lagrangians** follow [Mo, Lemma 5.1]: divergence identities for smooth maps, then
  mollification.
- **Rank-one affine functions.** The continuous case follows the proof of [CDKM, Thm 6.1]: the
  proof of [Da08, Thm 5.20] was not accessible. The function is affine along the rank-one lines,
  so its second derivative in a rank-one direction vanishes, and its `k`-th derivative vanishes on
  `(F, …, F)` when `rank F < k`; with [CDKM, Prop. 6.2], `D^{min (d, m) + 1}` vanishes, so the
  function is a polynomial of degree at most `min (d, m)`, `∑_k P_k` by Taylor's formula, with
  `P_k = 0` on the matrices of rank `< k`. [CDKM] take these derivatives in the sense of
  distributions; here they are classical derivatives of the mollifications, which are polynomials
  of degree at most `min (d, m)`, and so is their pointwise limit (a finite-dimensional space is
  closed). Then, as in [CDKM]: the terms of `P_k` whose rows `I` or columns `J` number fewer than
  `k` cancel (induction on `|I| + |J|`), the others are regrouped by permutations, and each group
  is an alternating multilinear form in the columns, a multiple of a minor. Without continuity,
  `RankOneAffine.exists_eq_sum_minor` uses a simpler argument of our own in place of the first
  half of [CDKM]: the function is affine in each entry, hence a sum of products of distinct
  entries, and `t ↦ f (t F)` has degree `< k` when `F` is a sum of fewer than `k` rank-one
  matrices (module docstrings of `Minors/RankOneAffine.lean` and
  `Minors/RankOneAffineContinuous.lean`).
- **Quasiconvex ⇒ rank-one convex** follows [M, Lemma 4.3]: quasiconvexity on the unit cube,
  tested with the laminates `v_k = min (k⁻¹ h (k x_j), dist_∞ (x, ∂Q)) a`, gives the two-point
  inequality along `a ⊗ e_j`, since `∇v_k` differs from the gradient of the sawtooth laminate only
  on a set of measure `→ 0`; an orthogonal change of variables (a Householder reflection) and the
  independence of the domain give every rank-one direction. No regularity of `f` enters the
  laminate argument.
- **Dacorogna's formula** follows the proof of [M, Thm 4.5 (iii), §4.8]: the proofs of [KP,
  Prop. 8.1] and [Da82] were not accessible. A quasiconvex minorant is quasiconvex on `Ω`, so it
  is below every average over `Ω`; the infimum formula over `Ω` is below the infimum formula `Qf`
  over the cube, by gluing rescaled copies of the cube test maps into finitely many disjoint small
  cubes filling `Ω` (Besicovitch); and `Qf` is `≡ −∞` or a continuous quasiconvex minorant of `f`:
  the inequality [M, (4.28)] for piecewise affine test maps, by gluing almost minimisers on the
  pieces, gives with the laminates of [M, Lemma 4.3] the two-point inequality of `Qf`, hence the
  dichotomy, convexity in each entry and continuity ([M, Def. 4.2, Remark 3]); and (4.28) with
  the "density arguments" of [M] gives quasiconvexity. The density argument is the one of the
  proof of [M, Thm 4.4 (i)]: a test map, shrunk into a smaller cube by scaling, is approximated
  by smooth maps (mollification), each of them by piecewise affine maps on a fine
  Kuhn–Freudenthal triangulation (whose gradients converge uniformly), with the triangulation
  chosen diagonally; the gradients stay bounded and converge almost everywhere, and dominated
  convergence passes (4.28) to the limit. Müller assumes `|∂Ω| = 0`; the independence of the
  domain used here does not need it.
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

## Planned extensions

- Minors of every order are null Lagrangians and quasiaffine.
- Mathlib-style names for the helper lemmas (prefixes `rd_`, `cv_`, `env_`, `glue_`, `lam_`,
  `distrib_`, `nl_`, and `plancherel` for the mollification lemmas), and one family of lemmas on
  gradients of Lipschitz maps in `Lipschitz/Gradient.lean` instead of two.
- The gluing lemma `cv_glue_on` for maps that are affine on the cubes, without the tangent maps
  and cut-offs it allows for (every use in the package is of that kind).

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
| [`CalculusOfVariations/RankOneConvex/`](CalculusOfVariations/RankOneConvex) | `LocallyLipschitz` |
| [`CalculusOfVariations/Lipschitz/`](CalculusOfVariations/Lipschitz) | `Gradient`, `Rescale`, `Periodic`, `Cutoff`, `ZeroSet`, `Mollify`, `PiecewiseAffine` |
| [`CalculusOfVariations/Covering/`](CalculusOfVariations/Covering) | `Cubes` (finite Besicovitch coverings) |
| [`CalculusOfVariations/Quasiconvex/`](CalculusOfVariations/Quasiconvex) | `Domain`, `Periodic`, `Laminate`, `RankOneConvex` |
| [`CalculusOfVariations/QuadraticForm/`](CalculusOfVariations/QuadraticForm) | `Plancherel`, `Quasiconvex` |
| [`CalculusOfVariations/Calculus/`](CalculusOfVariations/Calculus) | `IteratedFDeriv` (symmetry of the derivatives of smooth functions, polarization, Taylor) |
| [`CalculusOfVariations/Minors/`](CalculusOfVariations/Minors) | `RankOneAffine`, `RankOneAffineContinuous`, `NullLagrangian`, `Quasiaffine` |
| [`CalculusOfVariations/Envelope/`](CalculusOfVariations/Envelope) | `Cube` (the infimum formula on the cube), `Tangent` (gluing rescaled copies into cubes), `Glue` ((4.28)), `Convexity`, `Formula` |
| [`CalculusOfVariations/Smoothing/`](CalculusOfVariations/Smoothing) | `RankOneConvex` |
| [`CalculusOfVariations/Distribution/`](CalculusOfVariations/Distribution) | `SecondDerivative`, `Convex` |
| [`scripts/Audit.lean`](scripts/Audit.lean) | the axiom audit |
| [`.github/workflows/`](.github/workflows) | CI: build, audit, import list of the audit, line lengths |

## References

- [M] S. Müller, *Variational models for microstructure and phase transitions*, Max-Planck-Institut
  für Mathematik in den Naturwissenschaften, Leipzig, Lecture notes no. 2, 1998 (C.I.M.E. summer
  school, Cetraro, 1996): Definition 4.2 and Remarks 2, 3; Lemma 4.3; Theorem 4.5 (ii), (iii) and
  its proof in §4.8, with (4.28); Proposition 4.19.
- [Mo] C. B. Morrey, *Quasi-convexity and the lower semicontinuity of multiple integrals*, Pacific
  J. Math. 2 (1952), 25–53: Lemma 5.1, Theorem 5.2.
- [Da82] B. Dacorogna, *Quasiconvexity and relaxation of nonconvex problems in the calculus of
  variations*, J. Funct. Anal. 46 (1982), 102–118.
- [KP] D. Kinderlehrer, P. Pedregal, *Characterizations of Young measures generated by gradients*,
  Arch. Rational Mech. Anal. 115 (1991), 329–365: Proposition 8.1 (statement).
- [Da08] B. Dacorogna, *Direct methods in the calculus of variations*, 2nd ed., Springer, 2008:
  Theorems 5.20 and 5.25 (statements).
- [CDKM] S. Conti, G. Dolzmann, B. Kirchheim, S. Müller, *Sufficient conditions for the validity
  of the Cauchy–Born rule close to SO(n)*, J. Eur. Math. Soc. 8 (2006), 515–530: Appendix,
  Theorem 6.1 and its proof, Proposition 6.2.
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
