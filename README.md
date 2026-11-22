# Calculus of variations in Lean: quasiconvexity, rank-one convexity, the quasiconvex envelope

<!-- PLACEHOLDER: CI badge, once the repository has a public URL. -->

Lean 4 with Mathlib `v4.36.0-rc2`, for integrands `f : ℝ^{d×m} → ℝ` and Lipschitz maps
`φ : ℝ^m → ℝ^d` (sup norms):

- **Rank-one convexity and quasiconvexity.** A separately convex function is locally Lipschitz, so
  a rank-one convex function is locally Lipschitz; a quasiconvex integrand is rank-one convex;
  quasiconvexity does not depend on the bounded open domain, and may be tested with periodic maps.
- **Quadratic forms and minors.** A rank-one convex quadratic form is quasiconvex; a rank-one
  affine function is an affine combination of minors; the minors of order `2` and `3` are null
  Lagrangians, and the `3 × 3` minors are quasiaffine.
- **The quasiconvex envelope.** Dacorogna's formula `f^{qc} (A) = inf_φ ⨍_B f (A + ∇φ)` on the
  unit ball `B`, for continuous `f`, with values in `EReal`.
- **Smoothing.** A smooth rank-one convex integrand that is not quasiconvex at `0` gives a smooth
  one with the same properties, uniformly Legendre–Hadamard and of quadratic growth.
- **Tools.** Gradients of Lipschitz maps, rescaling, periodic extension, cut-offs, mollification,
  the vanishing of the gradient on the zero set, finite coverings by cubes.
- **Stated so far.** The laminate on a cube with faces orthogonal to a rank-one direction;
  Dacorogna's formula on any bounded open domain and the inequality for piecewise affine test maps
  behind it; Kuhn–Freudenthal interpolation; mollification of periodic Lipschitz maps; second
  distributional derivatives on `ℝ` and convexity.

**Status: partly proved.** The results of the first five items are proved. The statements listed under "Stated" below have `sorry` proofs, which the
[audit](scripts/Audit.lean) lists (33 declarations). No `axiom`, no `native_decide`.

## Main statements

`unitCube m = (0, 1)^m`; `grad φ x` is the `d × m` matrix of partial derivatives; a test map on `Ω`
is a Lipschitz `φ` vanishing outside `Ω`. The definitions are in
[`CalculusOfVariations/Basic.lean`](CalculusOfVariations/Basic.lean) ([M, Def. 4.2], with the
conventions of the package): `RankOneConvex`,
`RankOneAffine`, `QuasiconvexAtOn Ω f A` (`|Ω| f (A) ≤ ∫_Ω f (A + ∇φ)` for every test map on `Ω`
for which the integral exists), `QuasiconvexAtPeriodic`, `Quasiconvex` (on the unit cube, at every
matrix), `IsLocallyBounded`, and `qcEnvelope` (the supremum of the quasiconvex, lower
semicontinuous, locally bounded minorants, in `EReal`).

Proved:

| Statement | Lean | Source |
| --- | --- | --- |
| separately convex ⇒ locally Lipschitz | `Matrix.locallyLipschitz_of_convexOn_single` | [M, Def. 4.2, Remark 3] |
| rank-one convex ⇒ locally Lipschitz | `RankOneConvex.locallyLipschitz` | [M, Def. 4.2, Remark 3] |
| `f` lsc, locally bounded, quasiconvex ⇒ rank-one convex | `rankOneConvex_of_quasiconvex` | periodic laminates (see Method) |
| quasiconvexity on the cube ⇔ on any nonempty bounded open `Ω` | `quasiconvexAtOn_iff`, `quasiconvexAtOn_of_unitCube` | [M, Def. 4.2, Remark 2] |
| quasiconvexity on the cube ⇔ with periodic test maps | `quasiconvexAtOn_iff_periodic` | [M, Prop. 4.19] |
| `Q` bilinear, `A ↦ Q (A, A)` rank-one convex ⇒ quasiconvex | `quadraticForm_quasiconvex` | [Da08, Thm 5.25 (i)]; [Mo, Thm 5.2] |
| rank-one affine ⇒ affine combination of minors | `RankOneAffine.exists_eq_sum_minor` | [Da08, Thm 5.20, (iii) ⇒ (iv)] |
| `∫ minor (∇φ) = 0` for `2 × 2`, `3 × 3` minors, `φ` Lipschitz with compact support | `nl_null2`, `nl_null3` | [Mo, Lemma 5.1] |
| `∫_Q minor (A + ∇φ) = minor A` for `3 × 3` minors, `φ` a test map on `Q` | `nl_minor3_quasiaffine` | |
| `f^{qc} (A) = inf_φ ⨍_B f (A + ∇φ)`, `B` the unit ball, `f` continuous | `qcEnvelope_eq_iInf_unitBall` | [Da82]; [M, Thm 4.5 (iii)] |
| smoothing of a rank-one convex `p` not quasiconvex at `0` | `Smoothing.exists_smoothing` | [K, proof of Prop. 2] |

Stated, with `sorry` proofs:

| Statement | Lean | Source |
| --- | --- | --- |
| the two-point inequality `f (F) ≤ λ f (F + (1−λ) a ⊗ n) + (1−λ) f (F − λ a ⊗ n)` from quasiconvexity, by laminates on a cube with faces orthogonal to `n` | `le_of_quasiconvexAtOn_unitCube`, `le_of_quasiconvexAtOn_orthogonal`, `le_of_quasiconvexAtOn_vecMulVec`, with `cubeLaminate` | [M, Lemma 4.3] |
| `f^{qc} (A) = inf_φ ⨍_Ω f (A + ∇φ)`, `Ω` nonempty, bounded, open | `qcEnvelope_eq_iInf` | [Da82]; [M, Thm 4.5 (iii)] |
| `⨍_Q Qf (F + ∇ψ) ≥ Qf (F)` for piecewise affine test maps `ψ` | `cubeInf_le_sum_of_piecewiseAffine`, `cubeInf_le_two_point` | [M, (4.28)] |
| Kuhn–Freudenthal interpolation: Lipschitz, piecewise affine, `∇ I_k ψ → ∇ψ` a.e. | `kuhnInterpolation_lipschitz`, `kuhnInterpolation_piecewiseAffineOn`, `ae_tendsto_grad_kuhnInterpolation` | [F], [Ku] (the triangulation) |
| `⟨(ofFun g)'', ψ⟩ = ∫ g ψ''`; `(ofFun f)' = ofFun f'` for locally Lipschitz `f`; Leibniz for `(h f)''` | `lineDerivOp_lineDerivOp_ofFun_apply`, `lineDerivOp_ofFun_eq_ofFun_deriv`, `integral_deriv_deriv_mul_mul` | |
| on `ℝ`: `f` convex ⇒ `(ofFun f)'' ≥ 0`; `g` continuous with `(ofFun g)'' ≥ 0` ⇒ `g` convex | `ConvexOn.distribNonneg_lineDerivOp_lineDerivOp_ofFun`, `convexOn_of_distribNonneg` | |
| mollification: Lipschitz with the same constant; of `ℤ^m`-periodic maps, periodic | `plancherelMollify_lipschitzWith`, `plancherelMollify_periodic` | |
| mollification of Lipschitz `ℤ^m`-periodic maps: smooth, periodic, Lipschitz, `∇ → ∇φ` a.e. | `mollifyPi_*`, `ae_tendsto_grad_mollifyPi` | |

All names are in the namespace `CalculusOfVariations` except
`Matrix.locallyLipschitz_of_convexOn_single`. Two of them in Lean:

```lean
theorem CalculusOfVariations.quasiconvexAtOn_iff {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ)
    {Ω : Set (Fin m → ℝ)} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    QuasiconvexAtOn (unitCube m) f A ↔ QuasiconvexAtOn Ω f A

theorem CalculusOfVariations.qcEnvelope_eq_iInf_unitBall {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : Continuous f) (A : Matrix (Fin d) (Fin m) ℝ) :
    qcEnvelope f A =
      ⨅ (φ : (Fin m → ℝ) → Fin d → ℝ) (_ : (∃ K, LipschitzWith K φ) ∧ ∀ x ∉ unitBall m, φ x = 0),
        (((volume (unitBall m)).toReal⁻¹ * ∫ x in unitBall m, f (A + grad φ x) : ℝ) : EReal)
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
- **Quasiconvex ⇒ rank-one convex** is proved by periodic laminates in integer directions, through
  the periodic form, with separate convexity and continuity for the other directions. The laminate
  of [M, Lemma 4.3] on a cube with faces orthogonal to the direction is stated.
- **Dacorogna's formula** on the ball: a quasiconvex minorant is below every average; the formula
  on the ball is below the one on the cube by gluing copies of test maps into small cubes
  (Besicovitch); the formula on the cube is `≡ −∞` or a continuous quasiconvex minorant, by gluing
  at points of differentiability, laminates and separate convexity. The route of the proof of the
  formula on any domain is pending its source <!-- PLACEHOLDER -->; the steps of [M, §4.8] are
  stated: the inequality for piecewise affine test maps, and, for the "density arguments" there,
  piecewise affine approximation by Kuhn–Freudenthal interpolation.
- **Smoothing** follows the first step of [K, proof of Prop. 2], with cut-offs that are functions
  of `|X|²` (module docstring of `Smoothing/RankOneConvex.lean`).

## Planned extensions

<!-- PLACEHOLDER: the final list. -->

- Minors of every order are null Lagrangians and quasiaffine.
- Mathlib-style names for the helper lemmas (prefixes `rd_`, `cv_`, `nl_`, and `plancherel` for
  the mollification lemmas), and one family of lemmas on gradients of Lipschitz maps in
  `Lipschitz/Gradient.lean` instead of two.

## Using it from another Lake project

<!-- PLACEHOLDER: the repository URL and a published commit. -->

```toml
[[require]]
name = "CalculusOfVariations"
git = "<repository URL>"
rev = "<commit>"
```

Then import the modules you need, for instance
`public import CalculusOfVariations.Quasiconvex.Domain`, or `import CalculusOfVariations` for
everything. The package requires Lean and Mathlib `v4.36.0-rc2`, and the package
`HarmonicAnalysis` (`lean4-harmonic-analysis`), at a path while both are developed
<!-- PLACEHOLDER: its published commit -->; no module imports `HarmonicAnalysis` yet.

## Building

```sh
lake exe cache get                 # Mathlib's compiled files
lake build
lake env lean scripts/Audit.lean   # axioms; lists the `sorry`s while proofs are open
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
| [`CalculusOfVariations/Minors/`](CalculusOfVariations/Minors) | `RankOneAffine`, `NullLagrangian`, `Quasiaffine` |
| [`CalculusOfVariations/Envelope/`](CalculusOfVariations/Envelope) | `Cube` (the infimum formula on the cube), `Tangent`, `Convexity`, `Glue`, `Formula` |
| [`CalculusOfVariations/Smoothing/`](CalculusOfVariations/Smoothing) | `RankOneConvex` |
| [`CalculusOfVariations/Distribution/`](CalculusOfVariations/Distribution) | `SecondDerivative`, `Convex` |
| [`scripts/Audit.lean`](scripts/Audit.lean) | the axiom audit |
| [`.github/workflows/`](.github/workflows) | CI: build, audit, import list of the audit, line lengths |

## References

- [M] S. Müller, *Variational models for microstructure and phase transitions*, Max-Planck-Institut
  für Mathematik in den Naturwissenschaften, Leipzig, Lecture notes no. 2, 1998 (C.I.M.E. summer
  school, Cetraro, 1996): Definition 4.2 and Remarks 2, 3; Lemma 4.3; Theorem 4.5 (ii), (iii) and
  §4.8; Proposition 4.19.
- [Mo] C. B. Morrey, *Quasi-convexity and the lower semicontinuity of multiple integrals*, Pacific
  J. Math. 2 (1952), 25–53: Lemma 5.1, Theorem 5.2.
- [Da82] B. Dacorogna, *Quasiconvexity and relaxation of nonconvex problems in the calculus of
  variations*, J. Funct. Anal. 46 (1982), 102–118.
- [Da08] B. Dacorogna, *Direct methods in the calculus of variations*, 2nd ed., Springer, 2008:
  Theorems 5.20 and 5.25 (statements).
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
