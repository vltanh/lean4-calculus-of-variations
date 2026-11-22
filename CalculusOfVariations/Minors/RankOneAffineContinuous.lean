/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Calculus.IteratedFDeriv
public import CalculusOfVariations.Lipschitz.Mollify
public import CalculusOfVariations.Minors.RankOneAffine

/-!
# Continuous rank-one affine functions are affine combinations of minors

`RankOneAffine.exists_eq_sum_minor_of_continuous`: a continuous rank-one affine
`f : ℝ^{d×m} → ℝ` is an affine combination of the minors of its argument, of orders
`k ≤ min (d, m)`. This is the implication (iii) ⇒ (iv) of B. Dacorogna, *Direct methods in the
calculus of variations*, 2nd ed., Springer, 2008, Theorem 5.20, with its hypothesis of continuity
(the result cited; the book is not openly accessible, and its proof was not consulted). It is
proved by the argument of S. Conti, G. Dolzmann, B. Kirchheim, S. Müller, *Sufficient conditions
for the validity of the Cauchy–Born rule close to SO(n)*, J. Eur. Math. Soc. 8 (2006), 515–530,
Appendix, Theorem 6.1, pp. 526–528 ([CDKM]), for a continuous null Lagrangian `N` on the `m × n`
matrices. Below, `d × m` and `min (d, m)` stand for [CDKM]'s `m × n` and `d = min (m, n)`, and `f`
is viewed as a function `g` on `ℝ^{d × m}` (`minorsVec`, `minorsMat`).

## [CDKM]'s proof, step by step

1. `N` is affine along every rank-one line `t ↦ F + t A` ([CDKM] derive this from the null
   Lagrangian property). Here `f` is convex and concave along them
   (`RankOneAffine.add_smul_vecMulVec`).
2. The second derivative of `N` in a rank-one direction `A` vanishes, since `t ↦ N (F + t A)` is
   affine; taking further derivatives gives (6.1) `D^k N (·) (A, A, H₃, …, H_k) = 0` for
   `rank A ≤ 1`. Here: `D² h (·) (A, A) = 0` for a smooth `h` affine along `A`
   (`iterDirDeriv_pair_eq_zero`), and its further derivatives `∂_{H₃} ⋯ ∂_{H_k}` vanish; with the
   symmetry of the derivative, a derivative in which `A` occurs twice vanishes
   (`iterDirDeriv_eq_zero_of_count`).
3. (6.2) `D^k N (·) (F, …, F) = 0` if `rank F < k`: `F` is a sum of at most `k − 1` rank-one
   matrices, the multilinear expansion has two equal indices in every term, and (6.1) and the
   symmetry of the derivative apply (`iteratedFDeriv_sum_eq_zero`,
   `minors_iteratedFDeriv_rank_lt`, with `exists_sum_vecMulVec_of_rank`).
4. With `k = min (d, m) + 1`, `D^k N (·) (F, …, F) = 0` for every `F`, so `D^k N = 0` by
   Proposition 6.2 (`eq_zero_of_symmetric_of_apply_diag_eq_zero`,
   `minors_iteratedFDeriv_eq_zero`). Hence `N` is a polynomial of degree at most `min (d, m)`, the
   previous identities hold pointwise, and Taylor's formula (6.3) gives
   `N = ∑_{k ≤ min (d, m)} P_k`, `P_k (F) = D^k N (0) (F, …, F) / k!`, where `P_k` is a linear
   combination of products of `k` entries (`minors_expand`) and `P_k (F) = 0` when `rank F < k`.
5. The rest of the proof shows that such a `P_k` is a linear combination of the `k × k` minors:
   `exists_eq_sum_minor_of_rank_lt` (module `Minors.RankOneAffine`), proved as in [CDKM].

**Departure from [CDKM] (steps 2 to 4): mollification instead of distributions.** [CDKM] take the
derivatives of `N` in the sense of distributions. Here steps 2 to 4 are carried out with classical
derivatives for the smooth mollifications `g_n = ρ_n ⋆ g` (`plancherelMollify`, with bumps `ρ_n`
of radii `→ 0`). Each `g_n` is affine along the rank-one lines (`minors_mollify_affineAlong`), so
by steps 2 to 4 and Taylor's formula it is a polynomial of degree at most `min (d, m)`
(`minors_mem_polySpace`). These polynomials form a finite-dimensional, hence closed, space of
functions, and `g_n → g` pointwise, so `g` is a polynomial of degree at most `min (d, m)`
(`minors_mem_of_tendsto`), in particular smooth (`minors_contDiff_of_mem`). That "the previous
identities hold also pointwise" is then obtained by running steps 2 to 4 for `g` itself.
-/

@[expose] public section

open MeasureTheory Filter Topology Matrix
open scoped ContDiff Nat Convolution

namespace CalculusOfVariations

variable {d m : ℕ}

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `h` is affine along the lines `t ↦ x + t a`. -/
private def AffineAlong (h : E → ℝ) (a : E) : Prop :=
  ∀ x (t : ℝ), h (x + t • a) = h x + t * (h (x + a) - h x)

private lemma hasDerivAt_line (x a : E) : HasDerivAt (fun s : ℝ => x + s • a) a 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add x

/-- The second derivative of a smooth `h` in a direction `a` along which it is affine vanishes:
`D² h (·) (a, a) = 0` ([CDKM]: as a distribution). -/
private lemma iterDirDeriv_pair_eq_zero {h : E → ℝ} (hh : ContDiff ℝ ∞ h) {a : E}
    (ha : AffineAlong h a) : iterDirDeriv h [a, a] = 0 := by
  have hD : ∀ y, fderiv ℝ h y a = h (y + a) - h y := by
    intro y
    have h1 : HasDerivAt (fun s : ℝ => h (y + s • a)) (fderiv ℝ h y a) 0 := by
      have := (hh.differentiable (by simp) (y + (0 : ℝ) • a)).hasFDerivAt.comp_hasDerivAt
        (0 : ℝ) (hasDerivAt_line y a)
      rw [zero_smul, add_zero] at this
      exact this
    have h2 : HasDerivAt (fun s : ℝ => h (y + s • a)) (h (y + a) - h y) 0 := by
      have e : (fun s : ℝ => h (y + s • a)) = fun s => h y + s * (h (y + a) - h y) :=
        funext (ha y)
      rw [e]
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (h (y + a) - h y)).const_add (h y)
    exact h1.unique h2
  funext x
  have hconst : (fun s : ℝ => fderiv ℝ h (x + s • a) a) = fun _ => fderiv ℝ h x a := by
    funext s
    have e : x + s • a + a = x + (s + 1) • a := by rw [add_smul, one_smul, add_assoc]
    rw [hD, hD, e, ha x (s + 1), ha x s]
    ring
  have hg : Differentiable ℝ (fun y => fderiv ℝ h y a) :=
    (contDiff_iterDirDeriv hh [a]).differentiable (by simp)
  have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ h (x + s • a) a)
      (fderiv ℝ (fun y => fderiv ℝ h y a) x a) 0 := by
    have := (hg (x + (0 : ℝ) • a)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_line x a)
    rw [zero_smul, add_zero] at this
    exact this
  rw [hconst] at h1
  exact h1.unique (hasDerivAt_const _ _)

/-- **(6.1)** of [CDKM]: a derivative of `h` in which a direction `a` along which `h` is affine
occurs twice vanishes. -/
private lemma iterDirDeriv_eq_zero_of_count [DecidableEq E] {h : E → ℝ} (hh : ContDiff ℝ ∞ h)
    {a : E}
    (ha : AffineAlong h a) {l : List E} (hl : 2 ≤ l.count a) : iterDirDeriv h l = 0 := by
  have hmem : a ∈ l := List.count_pos_iff.1 (by omega)
  have hmem' : a ∈ l.erase a := List.count_pos_iff.1 (by rw [List.count_erase_self]; omega)
  have p : l.Perm ((l.erase a).erase a ++ [a, a]) :=
    (List.perm_cons_erase hmem).trans ((List.Perm.cons a (List.perm_cons_erase hmem')).trans
      (List.perm_append_comm (l₁ := [a, a]) (l₂ := (l.erase a).erase a)))
  rw [iterDirDeriv_perm hh p, iterDirDeriv_append, iterDirDeriv_pair_eq_zero hh ha,
    iterDirDeriv_zero]

/-- **(6.2)** of [CDKM]: `D^k h (x) (F, …, F) = 0` if `F` is a sum of fewer than `k` directions
along which `h` is affine: by multilinearity, a sum of terms in which, by pigeonhole, one of
these directions occurs twice. -/
private lemma iteratedFDeriv_sum_eq_zero {h : E → ℝ} (hh : ContDiff ℝ ∞ h) {r k : ℕ}
    (a : Fin r → E) (ha : ∀ j, AffineAlong h (a j)) (hrk : r < k) (x : E) :
    iteratedFDeriv ℝ k h x (fun _ => ∑ j, a j) = 0 := by
  classical
  rw [ContinuousMultilinearMap.map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  have hs : ¬ Function.Injective s := fun hinj => by
    have := Fintype.card_le_of_injective s hinj
    simp only [Fintype.card_fin] at this
    omega
  have hn : ¬ (List.ofFn fun i => a (s i)).Nodup := by
    rw [List.nodup_ofFn]
    exact fun h' => hs h'.of_comp
  rw [List.nodup_iff_count_le_one] at hn
  push Not at hn
  obtain ⟨b, hb⟩ := hn
  have hbmem : b ∈ List.ofFn fun i => a (s i) := List.count_pos_iff.1 (by omega)
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hbmem
  rw [iteratedFDeriv_eq_iterDirDeriv hh, iterDirDeriv_eq_zero_of_count hh (ha (s i)) (by omega)]
  rfl

end Smooth

/-! ### Matrices as vectors -/

/-- A matrix as a vector of `ℝ^{d × m}`. -/
private def minorsVec (F : Matrix (Fin d) (Fin m) ℝ) : Fin d × Fin m → ℝ := fun p => F p.1 p.2

/-- A vector of `ℝ^{d × m}` as a matrix. -/
private def minorsMat (x : Fin d × Fin m → ℝ) : Matrix (Fin d) (Fin m) ℝ :=
  Matrix.of fun i j => x (i, j)

/-- (6.2) for matrices: `D^k h (x) (F, …, F) = 0` if `rank F < k`, since `F` is then a sum of at
most `k − 1` rank-one matrices. -/
private lemma minors_iteratedFDeriv_rank_lt {h : (Fin d × Fin m → ℝ) → ℝ}
    (hh : ContDiff ℝ ∞ h) (ha : ∀ u v, AffineAlong h (minorsVec (vecMulVec u v))) {k : ℕ}
    {F : Matrix (Fin d) (Fin m) ℝ} (hF : F.rank < k) (x : Fin d × Fin m → ℝ) :
    iteratedFDeriv ℝ k h x (fun _ => minorsVec F) = 0 := by
  obtain ⟨r, a, b, hr, hFe⟩ := exists_sum_vecMulVec_of_rank F
  have e : minorsVec F = ∑ l, minorsVec (vecMulVec (a l) (b l)) := by
    rw [hFe]
    ext p
    simp [minorsVec, Matrix.sum_apply, Finset.sum_apply]
  rw [e]
  exact iteratedFDeriv_sum_eq_zero hh _ (fun l => ha _ _) (by omega) x

/-- [CDKM]: (6.2) with `k = min (d, m) + 1`, and Proposition 6.2: `D^{min (d, m) + 1} h = 0`. -/
private lemma minors_iteratedFDeriv_eq_zero {h : (Fin d × Fin m → ℝ) → ℝ}
    (hh : ContDiff ℝ ∞ h) (ha : ∀ u v, AffineAlong h (minorsVec (vecMulVec u v)))
    (y : Fin d × Fin m → ℝ) : iteratedFDeriv ℝ (min d m + 1) h y = 0 :=
  eq_zero_of_symmetric_of_apply_diag_eq_zero _
    (fun σ v => iteratedFDeriv_comp_perm_of_contDiff hh y v σ) (fun x => by
      have hx : x = minorsVec (minorsMat x) := rfl
      rw [hx]
      refine minors_iteratedFDeriv_rank_lt hh ha ?_ y
      have := le_min (rank_le_height (minorsMat x)) (rank_le_width (minorsMat x))
      omega)

/-! ### Polynomials of bounded degree -/

/-- The multilinear expansion `M (x, …, x) = ∑_t M (e_{t₁}, …, e_{t_k}) x_{t₁} ⋯ x_{t_k}`. -/
private lemma minors_expand {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => ι → ℝ) ℝ) (x : ι → ℝ) :
    M (fun _ => x) = ∑ t : Fin k → ι, M (fun i => Pi.single (t i) 1) * ∏ i, x (t i) := by
  have hx : x = ∑ j, x j • Pi.single j (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  refine (M.map_sum (fun _ j => x j • Pi.single j (1 : ℝ))).trans
    (Finset.sum_congr rfl fun t _ => ?_)
  rw [M.map_smul_univ, smul_eq_mul, mul_comm]

/-- The polynomials of degree at most `n` on `ℝ^ι`: the span of the monomials
`x_{t₁} ⋯ x_{t_k}`, `k ≤ n`, a finite-dimensional space of functions. -/
private def minorsPolySpace (ι : Type*) [Fintype ι] (n : ℕ) : Submodule ℝ ((ι → ℝ) → ℝ) :=
  Submodule.span ℝ
    (Set.range fun kt : (Σ k : Fin (n + 1), Fin k → ι) => fun x : ι → ℝ => ∏ i, x (kt.2 i))

/-- Taylor's formula: a smooth function with `D^{n+1} h = 0` is a polynomial of degree at most
`n`. -/
private lemma minors_mem_polySpace {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    {h : (ι → ℝ) → ℝ} (hh : ContDiff ℝ ∞ h) (hn : ∀ y, iteratedFDeriv ℝ (n + 1) h y = 0) :
    h ∈ minorsPolySpace ι n := by
  have e : h = ∑ k : Fin (n + 1), ∑ t : Fin k → ι,
      (iteratedFDeriv ℝ k h 0 (fun i => Pi.single (t i) 1) / (k : ℕ)!) •
        fun x : ι → ℝ => ∏ i, x (t i) := by
    funext x
    rw [eq_sum_iteratedFDeriv_of_iteratedFDeriv_eq_zero hh hn x, ← Fin.sum_univ_eq_sum_range]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [minors_expand, Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [e]
  exact Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun t _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨k, t⟩, rfl⟩)

private lemma minors_contDiff_of_mem {ι : Type*} [Fintype ι] {n : ℕ} {g : (ι → ℝ) → ℝ}
    (hg : g ∈ minorsPolySpace ι n) : ContDiff ℝ ∞ g := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨kt, rfl⟩ := hx
    exact contDiff_prod fun i _ => contDiff_pi.1 contDiff_id (kt.2 i)
  | zero => exact contDiff_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact contDiff_const.smul hx

/-- A pointwise limit of polynomials of degree at most `n` is one: they form a finite-dimensional,
hence closed, subspace. -/
private lemma minors_mem_of_tendsto {ι : Type*} [Fintype ι] {n : ℕ} {g : (ι → ℝ) → ℝ}
    {gn : ℕ → (ι → ℝ) → ℝ} (hmem : ∀ k, gn k ∈ minorsPolySpace ι n)
    (hlim : ∀ x, Tendsto (fun k => gn k x) atTop (𝓝 (g x))) : g ∈ minorsPolySpace ι n := by
  have : FiniteDimensional ℝ (minorsPolySpace ι n) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  exact (minorsPolySpace ι n).closed_of_finiteDimensional.mem_of_tendsto
    (tendsto_pi_nhds.2 hlim) (Eventually.of_forall hmem)

/-! ### Mollification -/

section Mollify

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The bumps with radii `1 / (n + 2) < 2 / (n + 2)`. -/
private noncomputable def minorsBump (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] (n : ℕ) : ContDiffBump (0 : E) where
  rIn := 1 / (n + 2)
  rOut := 2 / (n + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := by gcongr; norm_num

omit [MeasurableSpace E] [BorelSpace E] in
private lemma minorsBump_tendsto :
    Tendsto (fun n => (minorsBump E n).rOut) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0)
  have : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  simpa using this.const_div_atTop 2

/-- The mollification of a continuous function affine along a direction is affine along it. -/
private lemma minors_mollify_affineAlong {g : E → ℝ} (hg : Continuous g) {a : E}
    (ha : AffineAlong g a) (ρ : ContDiffBump (0 : E)) :
    AffineAlong (plancherelMollify μ ρ g) a := by
  intro x t
  simp only [plancherelMollify, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hint : ∀ z, Integrable (fun y => ρ.normed μ y * g (z - y)) μ := fun z =>
    ((ρ.contDiff_normed (μ := μ) (n := 0)).continuous.mul
      (hg.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      ρ.hasCompactSupport_normed.mul_right
  have e : ∀ y, ρ.normed μ y * g (x + t • a - y) = ρ.normed μ y * g (x - y) +
      t * (ρ.normed μ y * g (x + a - y) - ρ.normed μ y * g (x - y)) := by
    intro y
    have h1 : x + t • a - y = (x - y) + t • a := by abel
    have h2 : x + a - y = (x - y) + a := by abel
    rw [h1, h2, ha]
    ring
  have hI : Integrable
      (fun y => t * (ρ.normed μ y * g (x + a - y) - ρ.normed μ y * g (x - y))) μ :=
    ((hint (x + a)).sub (hint x)).const_mul t
  simp_rw [e]
  rw [integral_add (hint x) hI, integral_const_mul, integral_sub (hint (x + a)) (hint x)]

end Mollify

/-! ### The theorem -/

/-- **A continuous rank-one affine function is an affine combination of minors** (the implication
(iii) ⇒ (iv) of Dacorogna 2008, Theorem 5.20, the statement cited): for a continuous rank-one
affine `f : ℝ^{d×m} → ℝ` there are coefficients `a k r c` with
`f (A) = ∑_{k ≤ min d m} ∑_{r, c} a k r c · minor A r c` for every `A` (the `0 × 0` minor is the
constant `1`). The proof is that of Conti–Dolzmann–Kirchheim–Müller 2006, Theorem 6.1, with
mollification in place of distributions (module docstring). -/
theorem RankOneAffine.exists_eq_sum_minor_of_continuous {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hc : Continuous f) (hf : RankOneAffine f) :
    ∃ a : (k : ℕ) → (Fin k ↪o Fin d) → (Fin k ↪o Fin m) → ℝ,
      ∀ A, f A = ∑ k ∈ Finset.range (min d m + 1), ∑ r, ∑ c, a k r c * minor A r c := by
  let g : (Fin d × Fin m → ℝ) → ℝ := fun x => f (minorsMat x)
  have hgc : Continuous g := hc.comp (continuous_pi fun i => continuous_pi fun j =>
    continuous_apply (i, j))
  -- step 1: `g` is affine along the rank-one lines
  have hga : ∀ u v, AffineAlong g (minorsVec (vecMulVec u v)) := by
    intro u v x t
    have e : ∀ s : ℝ, minorsMat (x + s • minorsVec (vecMulVec u v)) =
        minorsMat x + s • vecMulVec u v := by
      intro s
      ext i j
      simp [minorsMat, minorsVec]
    have e1 := e 1
    rw [one_smul, one_smul] at e1
    simp only [g, e, e1]
    exact hf.add_smul_vecMulVec _ u v t
  -- the mollifications are smooth, affine along the rank-one lines, hence polynomials of degree
  -- at most `min d m`, and converge to `g`
  let gn : ℕ → (Fin d × Fin m → ℝ) → ℝ := fun n =>
    plancherelMollify volume (minorsBump (Fin d × Fin m → ℝ) n) g
  have hgn : ∀ n, ContDiff ℝ ∞ (gn n) := fun n => plancherelMollify_contDiff _ hgc
  have hgn_mem : ∀ n, gn n ∈ minorsPolySpace (Fin d × Fin m) (min d m) := fun n =>
    minors_mem_polySpace (hgn n) (minors_iteratedFDeriv_eq_zero (hgn n)
      fun u v => minors_mollify_affineAlong hgc (hga u v) _)
  have hg_mem : g ∈ minorsPolySpace (Fin d × Fin m) (min d m) :=
    minors_mem_of_tendsto hgn_mem fun x =>
      ContDiffBump.convolution_tendsto_right_of_continuous minorsBump_tendsto hgc x
  have hgs : ContDiff ℝ ∞ g := minors_contDiff_of_mem hg_mem
  -- (6.3): Taylor's formula for `g`, with `D^{min d m + 1} g = 0`
  have hT := eq_sum_iteratedFDeriv_of_iteratedFDeriv_eq_zero hgs
    (minors_iteratedFDeriv_eq_zero hgs hga)
  -- `P_k (F) = D^k g (0) (F, …, F) / k!` as a sum of products of entries
  have hP : ∀ (k : ℕ) (F : Matrix (Fin d) (Fin m) ℝ),
      iteratedFDeriv ℝ k g 0 (fun _ => minorsVec F) / k ! =
        ∑ t : Fin k → Fin d × Fin m,
          iteratedFDeriv ℝ k g 0 (fun i => Pi.single (t i) 1) / k ! * ∏ i, F (t i).1 (t i).2 := by
    intro k F
    rw [minors_expand, Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [minorsVec]
    ring
  choose a ha using fun k => exists_eq_sum_minor_of_rank_lt
    (fun t : Fin k → Fin d × Fin m => iteratedFDeriv ℝ k g 0 (fun i => Pi.single (t i) 1) / k !)
    (fun F hF => by rw [← hP, minors_iteratedFDeriv_rank_lt hgs hga hF 0, zero_div])
  refine ⟨a, fun A => ?_⟩
  change g (minorsVec A) = _
  rw [hT]
  exact Finset.sum_congr rfl fun k _ => by rw [hP, ha]

end CalculusOfVariations
