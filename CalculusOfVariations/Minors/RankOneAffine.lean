/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Order.Hom.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.RowCol

/-!
# Rank-one affine functions are affine combinations of minors

`minor A r c`: the `k × k` minor of `A` with the rows `r` and the columns `c`.
`RankOneAffine.exists_eq_sum_minor`: a rank-one affine `f : ℝ^{d×m} → ℝ` is an affine combination
of the minors of its argument. Continuity is not needed.

This is the implication (iii) ⇒ (iv) of B. Dacorogna, *Direct methods in the calculus of
variations*, 2nd ed., Springer, 2008, Theorem 5.20, which is the statement cited; the proof of the
book was not accessible. The proof here is the one of S. Conti, G. Dolzmann, B. Kirchheim,
S. Müller, *Sufficient conditions for the validity of the Cauchy–Born rule close to SO(n)*,
J. Eur. Math. Soc. 8 (2006), 515–530, Appendix, Theorem 6.1, pp. 526–528 ([CDKM]): a continuous
null Lagrangian `N` on `m × n` matrices is a constant plus a linear combination of minors. After
its first sentence, which shows that `N` is affine along every rank-one line `t ↦ F + t a ⊗ b`,
that proof uses only this property and the continuity of `N`.

## The steps of [CDKM], and where they are here

1. `N` is affine along the rank-one lines. Here `f` is convex and concave along them, hence affine
   (`minors_RA_of_rankOneAffine`).
2. `N` is a polynomial of degree at most `min (m, n)`, `N = ∑_k P_k` with `P_k` homogeneous of
   degree `k` ((6.3)), and (6.2) gives `P_k (F) = 0` whenever `rank F < k`. Replaced here by
   Steps 2a and 2b below.
3. `P_k` has only the products of entries that occur in the `k × k` minors. With `F_{I,J}` the
   matrix `F` with the entries outside the rows `I` and the columns `J` set to `0`, and `S_{I,J}`
   the terms of `P_k` whose rows are exactly `I` and whose columns are exactly `J`,
   `P_k (F_{I,J}) = ∑_{I' ⊆ I, J' ⊆ J} S_{I',J'} (F)` (`minors_hom_restr`); if `|I| < k` or
   `|J| < k`, then `rank F_{I,J} < k`, so `P_k (F_{I,J}) = 0`, and by induction `S_{I,J} = 0`
   (`minors_block_eq_zero`; the induction is on `|I| + |J|`).
4. For `|I| = |J| = k`, `I = {α₁ < ⋯ < α_k}`, `J = {β₁ < ⋯ < β_k}`, the form
   `Q (v¹, …, v^k) = S_{I,J} (F_v) = P_k (F_v)`, `F_v = ∑_{i,j} v^j_i e_{α_i} ⊗ e_{β_j}`, is
   multilinear in the columns `v^j`, and vanishes when `dim span {v^j} < k`, since then
   `rank F_v < k`; so it is alternating, hence a multiple `ĉ_{I,J} det` of the determinant, and
   `S_{I,J} (F) = ĉ_{I,J} det_k F_{I,J}` (`minors_block_eq_minor`).
5. `N = ∑_k ∑_{|I| = |J| = k} ĉ_{I,J} det_k F_{I,J}` (`RankOneAffine.exists_eq_sum_minor`).

**Departure from [CDKM] (its step 2).** [CDKM] obtain step 2 from the continuity of `N`: the
second distributional derivative of `N` in a rank-one direction vanishes, hence (6.1)
`D^k N (A, A, H₃, …, H_k) = 0` for `rank A ≤ 1`, hence (6.2) `D^k N (F, …, F) = 0` for
`rank F < k`, so `D^{d+1} N = 0` (their Proposition 6.2) and `N` is a polynomial of degree at most
`d = min (m, n)`. The statement here does not assume `f` continuous, so step 2 is replaced by two
algebraic steps, which give what steps 3 and 4 use:

* **Step 2a.** `f` is affine in each entry, since `e_i ⊗ e_j` has rank one, and a function on
  `ℝ^N` that is affine in each coordinate is `∑_S c_S ∏_{s ∈ S} x_s` (`minors_multiaffine`); so
  `f (F) = ∑_S c_S F^S` over the sets `S` of entries, `F^S = ∏_{(i,j) ∈ S} F_{ij}`
  (`minors_exists_mono`), and `P_k = ∑_{|S| = k} c_S F^S` (`minorsHom`).
* **Step 2b** (for (6.2)). If `F` is a sum of fewer than `k` rank-one matrices `A_l`, then
  `P_k (F) = 0` (`minors_hom_eq_zero`): `s ↦ f (∑_l s_l A_l)` is affine in each `s_l`, so by
  Step 2a the function `t ↦ f (t F)` is a polynomial of degree less than `k`, while
  `f (t F) = ∑_j t^j P_j (F)`. It is used where [CDKM] use (6.2), with explicit decompositions in
  place of the rank: `F_{I,J}` is the sum of the `|I|` matrices `e_i ⊗ (row i of F_{I,J})`, and
  of the `|J|` matrices `(column j of F_{I,J}) ⊗ e_j` (`minors_restr_eq_sum_rows`,
  `minors_restr_eq_sum_cols`); and in step 4 only the case of two equal columns `v^p = v^q` is
  needed, where `F_v` is a sum of `k − 1` rank-one matrices (`minors_Fv_eq_sum_erase`).

Steps 3 to 5 are those of [CDKM], with the monomials of Step 2a. These have no repeated entry and
are indexed by their sets of entries `S`, of rows `I` and columns `J`; the degree bound
`k ≤ min (m, n)` holds because there is no `k × k` minor otherwise. In step 4, [CDKM] write the
terms of `S_{I,J}` as a sum over the permutations of `{1, …, k}` to see that `Q` is multilinear;
here a monomial of `S_{I,J}` has `k` entries in the `k` columns of `J`, hence exactly one in each
column, and is linear in it (`minors_mono_updateCol`, `minorsQ`). "Every alternating multilinear
form is a multiple of the determinant" is Mathlib's `AlternatingMap.eq_smul_basis_det`.
-/

@[expose] public section

namespace CalculusOfVariations

variable {d m : ℕ}

/-- The `k × k` minor of `A` with the rows `r` and the columns `c` (strictly increasing). -/
noncomputable def minor (A : Matrix (Fin d) (Fin m) ℝ) {k : ℕ} (r : Fin k ↪o Fin d)
    (c : Fin k ↪o Fin m) : ℝ :=
  (A.submatrix r c).det

private lemma minors_rank_eq_zero_imp {A : Matrix (Fin d) (Fin m) ℝ} (h : A.rank = 0) :
    A = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  ext i j
  have := congrArg (fun F => F (Pi.single j 1) i) h
  simpa [Matrix.mulVecLin_apply] using this

/-! ### Rank-one affine functions are affine combinations of minors -/

section RankOneAffine

open Matrix

/-! #### Step 1: affinity along the rank-one lines -/

/-- Affinity along the rank-one lines `t ↦ A + t (u ⊗ v)`. -/
private def MinorsRA {d m : ℕ} (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ A (u : Fin d → ℝ) (v : Fin m → ℝ) (t : ℝ),
    f (A + t • vecMulVec u v) = f A + t * (f (A + vecMulVec u v) - f A)

/-- A function on `ℝ` that is convex and concave is affine. -/
private lemma minors_affine_of_convex_concave {g : ℝ → ℝ} (h1 : ConvexOn ℝ Set.univ g)
    (h2 : ConvexOn ℝ Set.univ (-g)) (t : ℝ) : g t = g 0 + t * (g 1 - g 0) := by
  have key : ∀ x y a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → g (a * x + b * y) = a * g x + b * g y := by
    intro x y a b ha hb hab
    have e1 := h1.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    have e2 := h2.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    simp only [smul_eq_mul, Pi.neg_apply] at e1 e2
    linarith
  rcases le_or_gt t 1 with ht1 | ht1
  · rcases le_or_gt 0 t with ht0 | ht0
    · have := key 0 1 (1 - t) t (by linarith) ht0 (by ring)
      simp only [mul_zero, zero_add, mul_one] at this
      rw [this]; ring
    · -- `0` is a convex combination of `t` and `1`
      have hpos : 0 < 1 - t := by linarith
      have := key t 1 (1 / (1 - t)) (-t / (1 - t)) (by positivity)
        (div_nonneg (by linarith) hpos.le) (by field_simp; ring)
      have e : 1 / (1 - t) * t + -t / (1 - t) * 1 = 0 := by field_simp; ring
      rw [e] at this
      field_simp at this
      linarith
  · have hpos : 0 < t := by linarith
    have := key 0 t (1 - 1 / t) (1 / t) (by rw [sub_nonneg, div_le_one hpos]; linarith)
      (by positivity) (by ring)
    have e : (1 - 1 / t) * 0 + 1 / t * t = 1 := by
      rw [mul_zero, zero_add, one_div, inv_mul_cancel₀ hpos.ne']
    rw [e] at this
    field_simp at this
    linarith

private lemma minors_rank_vecMulVec {u : Fin d → ℝ} {v : Fin m → ℝ} (h : vecMulVec u v ≠ 0) :
    (vecMulVec u v).rank = 1 :=
  le_antisymm (rank_vecMulVec_le _ _) (Nat.one_le_iff_ne_zero.2 fun h' =>
    h (minors_rank_eq_zero_imp h'))

/-- **Step 1.** A rank-one affine function is affine along the rank-one lines ([CDKM] reach this
from the null Lagrangian property; here it is the definition, convex and concave along them). -/
private lemma minors_RA_of_rankOneAffine {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : RankOneAffine f) : MinorsRA f := by
  intro A u v t
  by_cases h : vecMulVec u v = 0
  · simp [h]
  have hr := minors_rank_vecMulVec h
  have := minors_affine_of_convex_concave (hf.1 A _ hr) (hf.2 A _ hr) t
  simpa using this

/-! #### Step 2a (in place of [CDKM]'s step 2): `f` is a polynomial with no repeated entry -/

/-- **Step 2a.** A function on `ℝ^ι` that is affine in each coordinate separately is
`g (x) = ∑_S c_S ∏_{i ∈ S} x_i`. Induction on the coordinates:
`g (x', x_a) = g (x', 0) + x_a (g (x', 1) − g (x', 0))`, both coefficients being affine in each
coordinate. -/
private lemma minors_multiaffine {ι : Type*} [Fintype ι] [DecidableEq ι] {g : (ι → ℝ) → ℝ}
    (hg : ∀ x (i : ι) (t : ℝ),
      g (x + t • Pi.single i 1) = g x + t * (g (x + Pi.single i 1) - g x)) :
    ∃ c : Finset ι → ℝ, ∀ x, g x = ∑ S, c S * ∏ i ∈ S, x i := by
  have key : ∀ s : Finset ι, ∀ g : (ι → ℝ) → ℝ, (∀ x (i : ι) (t : ℝ),
      g (x + t • Pi.single i 1) = g x + t * (g (x + Pi.single i 1) - g x)) →
      ∃ c : Finset ι → ℝ, ∀ x : ι → ℝ, g (fun i => if i ∈ s then x i else 0) =
        ∑ S ∈ s.powerset, c S * ∏ i ∈ S, x i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g _
      refine ⟨fun _ => g 0, fun x => ?_⟩
      simp only [Finset.notMem_empty, ite_false, Finset.powerset_empty, Finset.sum_singleton,
        Finset.prod_empty, mul_one]
      rfl
    | insert a s ha ih =>
      intro g hg
      obtain ⟨c0, h0⟩ := ih g hg
      obtain ⟨c1, h1⟩ := ih (fun y => g (y + Pi.single a 1) - g y) (fun x i t => by
        have e1 := hg (x + Pi.single a 1) i t
        have e2 := hg x i t
        have e3 : x + t • Pi.single i 1 + Pi.single a 1 =
            x + Pi.single a 1 + t • Pi.single i 1 := by abel
        have e4 : x + Pi.single i 1 + Pi.single a 1 = x + Pi.single a 1 + Pi.single i 1 := by
          abel
        simp only [e3, e4, e1, e2]
        ring)
      refine ⟨fun S => if a ∈ S then c1 (S.erase a) else c0 S, fun x => ?_⟩
      set y : ι → ℝ := fun i => if i ∈ s then x i else 0 with hy
      have hxy : (fun i => if i ∈ insert a s then x i else 0) = y + x a • Pi.single a 1 := by
        ext i
        by_cases hia : i = a
        · subst hia; simp [hy, ha]
        · simp [hy, Finset.mem_insert, hia]
      have hS : ∀ S ∈ s.powerset, a ∉ S := fun S hS h => ha (Finset.mem_powerset.1 hS h)
      have h1x : g (y + Pi.single a 1) - g y = ∑ S ∈ s.powerset, c1 S * ∏ i ∈ S, x i := h1 x
      rw [hxy, hg y a (x a), Finset.sum_powerset_insert ha, h1x, h0, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun S hS' => by beta_reduce; rw [ite_eq_right (hS S hS')]
      · refine Finset.sum_congr rfl fun S hS' => ?_
        beta_reduce
        rw [ite_eq_left (Finset.mem_insert_self a S), Finset.erase_insert (hS S hS'),
          Finset.prod_insert (hS S hS')]
        ring
  obtain ⟨c, hc⟩ := key Finset.univ g hg
  refine ⟨c, fun x => ?_⟩
  have := hc x
  simp only [Finset.mem_univ, ite_true, Finset.powerset_univ] at this
  exact this

/-- The monomial `F^S = ∏_{(i, j) ∈ S} F_{ij}` of a set `S` of entries. -/
private def minorsMono (S : Finset (Fin d × Fin m)) (F : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  ∏ s ∈ S, F s.1 s.2

/-- Step 2a for `f`: `f` is affine in each entry (`e_i ⊗ e_j` has rank one), so
`f (F) = ∑_S c_S F^S`. -/
private lemma minors_exists_mono {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : MinorsRA f) :
    ∃ c : Finset (Fin d × Fin m) → ℝ, ∀ F, f F = ∑ S, c S * minorsMono S F := by
  obtain ⟨c, hc⟩ := minors_multiaffine
    (g := fun x : Fin d × Fin m → ℝ => f (Matrix.of fun i j => x (i, j))) (fun x p t => by
      have e : ∀ s : ℝ, (Matrix.of fun i j => (x + s • Pi.single p 1 : Fin d × Fin m → ℝ) (i, j)) =
          Matrix.of (fun i j => x (i, j)) + s • vecMulVec (Pi.single p.1 1) (Pi.single p.2 1) := by
        intro s
        obtain ⟨p1, p2⟩ := p
        ext i j
        by_cases h1 : i = p1 <;> by_cases h2 : j = p2 <;>
          simp [vecMulVec_apply, Pi.single_apply, h1, h2]
      have e1 := e 1
      simp only [one_smul] at e1
      simp only [e, e1]
      exact hf _ _ _ t)
  exact ⟨c, fun F => hc (fun p => F p.1 p.2)⟩

/-- The homogeneous part of degree `k`: `P_k (F) = ∑_{|S| = k} c_S F^S`. -/
private def minorsHom (c : Finset (Fin d × Fin m) → ℝ) (k : ℕ) (F : Matrix (Fin d) (Fin m) ℝ) :
    ℝ :=
  ∑ S with S.card = k, c S * minorsMono S F

private lemma minors_mono_smul (S : Finset (Fin d × Fin m)) (t : ℝ)
    (F : Matrix (Fin d) (Fin m) ℝ) : minorsMono S (t • F) = t ^ S.card * minorsMono S F := by
  simp only [minorsMono, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const]

/-! #### Step 2b (for [CDKM]'s (6.2)): `P_k` vanishes on sums of fewer than `k` rank-one matrices -/

/-- **Step 2b.** If `F = ∑_{l ∈ L} a_l ⊗ b_l` with `|L| < k`, then `P_k (F) = 0`:
`s ↦ f (∑_l s_l a_l ⊗ b_l)` is affine in each `s_l` (rank-one lines), hence by Step 2a a
polynomial with no repeated variable, so `t ↦ f (t F)` is a polynomial of degree at most `|L|`;
comparing its coefficients with those of `f (t F) = ∑_j t^j P_j (F)` gives `P_k (F) = 0`. -/
private lemma minors_hom_eq_zero {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : MinorsRA f)
    {c : Finset (Fin d × Fin m) → ℝ} (hc : ∀ F, f F = ∑ S, c S * minorsMono S F)
    {ι : Type*} [DecidableEq ι] (L : Finset ι) (a : ι → Fin d → ℝ) (b : ι → Fin m → ℝ) {k : ℕ}
    (hk : L.card < k) : minorsHom c k (∑ l ∈ L, vecMulVec (a l) (b l)) = 0 := by
  set F := ∑ l ∈ L, vecMulVec (a l) (b l) with hF
  obtain ⟨c', hc'⟩ := minors_multiaffine (ι := L)
    (g := fun s : L → ℝ => f (∑ l : L, s l • vecMulVec (a l) (b l))) (fun s l t => by
      have e : ∀ u : ℝ, ∑ l' : L, (s + u • Pi.single l 1 : L → ℝ) l' • vecMulVec (a l') (b l') =
          ∑ l' : L, s l' • vecMulVec (a l') (b l') + u • vecMulVec (a l) (b l) := by
        intro u
        simp only [Pi.add_apply, Pi.smul_apply, add_smul, Finset.sum_add_distrib, smul_eq_mul,
          Pi.single_apply, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
      have e1 := e 1
      simp only [one_smul] at e1
      simp only [e, e1]
      exact hf _ _ _ t)
  -- `f (t F)` two ways
  have h1 : ∀ t : ℝ, f (t • F) = ∑ S, c S * minorsMono S F * t ^ S.card := by
    intro t
    rw [hc]
    exact Finset.sum_congr rfl fun S _ => by rw [minors_mono_smul]; ring
  have h2 : ∀ t : ℝ, f (t • F) = ∑ T, c' T * t ^ T.card := by
    intro t
    have := hc' (fun _ => t)
    simp only [Finset.prod_const] at this
    rw [← this, hF, Finset.smul_sum]
    congr 1
    exact (Finset.sum_coe_sort L fun l => t • vecMulVec (a l) (b l)).symm
  -- compare the coefficients of `t^k`
  set p : Polynomial ℝ := ∑ S, Polynomial.C (c S * minorsMono S F) * Polynomial.X ^ S.card -
    ∑ T, Polynomial.C (c' T) * Polynomial.X ^ T.card with hp
  have hp0 : p = 0 := by
    refine Polynomial.funext fun t => ?_
    simp only [hp, Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    rw [← h1, ← h2, sub_self]
  have hk' := congrArg (fun q => Polynomial.coeff q k) hp0
  simp only [hp, Polynomial.coeff_sub, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hk'
  have hT : ∑ T : Finset L, (if k = T.card then c' T else 0) = 0 := by
    refine Finset.sum_eq_zero fun T _ => ite_eq_right fun h => ?_
    have := Finset.card_le_univ T
    rw [Fintype.card_coe] at this
    omega
  rw [hT, sub_zero] at hk'
  rw [minorsHom, Finset.sum_filter]
  exact Eq.trans (Finset.sum_congr rfl fun S _ => if_congr eq_comm rfl rfl) hk'

/-! #### Step 3: only the monomials with `k` distinct rows and `k` distinct columns survive -/

/-- `F_{I,J}`: the entries of `F` outside the rows `I` and the columns `J` set to `0`. -/
private def minorsRestr (I : Finset (Fin d)) (J : Finset (Fin m)) (F : Matrix (Fin d) (Fin m) ℝ) :
    Matrix (Fin d) (Fin m) ℝ :=
  Matrix.of fun i j => if i ∈ I ∧ j ∈ J then F i j else 0

/-- `S_{I,J}`: the terms of `P_k` whose set of rows is `I` and whose set of columns is `J`. -/
private def minorsBlock (c : Finset (Fin d × Fin m) → ℝ) (k : ℕ) (I : Finset (Fin d))
    (J : Finset (Fin m)) (F : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  ∑ S with S.card = k ∧ S.image Prod.fst = I ∧ S.image Prod.snd = J, c S * minorsMono S F

/-- `(F_{I,J})^S = F^S` if `S ⊆ I × J`, and `0` otherwise. -/
private lemma minors_mono_restr (S : Finset (Fin d × Fin m)) (I : Finset (Fin d))
    (J : Finset (Fin m)) (F : Matrix (Fin d) (Fin m) ℝ) :
    minorsMono S (minorsRestr I J F) =
      if S.image Prod.fst ⊆ I ∧ S.image Prod.snd ⊆ J then minorsMono S F else 0 := by
  unfold minorsMono minorsRestr
  split_ifs with h
  · refine Finset.prod_congr rfl fun s hs => ?_
    have h1 : s.1 ∈ I := h.1 (Finset.mem_image_of_mem _ hs)
    have h2 : s.2 ∈ J := h.2 (Finset.mem_image_of_mem _ hs)
    simp [h1, h2]
  · rw [not_and_or] at h
    rcases h with h | h
    · obtain ⟨i, hi, hiI⟩ := Finset.not_subset.1 h
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hi
      exact Finset.prod_eq_zero hs (by simp [hiI])
    · obtain ⟨j, hj, hjJ⟩ := Finset.not_subset.1 h
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hj
      exact Finset.prod_eq_zero hs (by simp [hjJ])

/-- `P_k (F_{I,J}) = ∑_{I' ⊆ I, J' ⊆ J} S_{I',J'} (F)`. -/
private lemma minors_hom_restr (c : Finset (Fin d × Fin m) → ℝ) (k : ℕ) (I : Finset (Fin d))
    (J : Finset (Fin m)) (F : Matrix (Fin d) (Fin m) ℝ) :
    minorsHom c k (minorsRestr I J F) =
      ∑ I' ∈ I.powerset, ∑ J' ∈ J.powerset, minorsBlock c k I' J' F := by
  have hS : ∀ S : Finset (Fin d × Fin m), (∑ I' ∈ I.powerset, ∑ J' ∈ J.powerset,
      if S.card = k ∧ S.image Prod.fst = I' ∧ S.image Prod.snd = J' then
        c S * minorsMono S F else 0) =
      if S.card = k then c S * minorsMono S (minorsRestr I J F) else 0 := by
    intro S
    rw [minors_mono_restr]
    by_cases hk : S.card = k
    · simp only [hk, true_and, ite_true, ite_and, Finset.sum_ite_eq, Finset.mem_powerset,
        Finset.sum_ite_irrel, Finset.sum_const_zero, mul_ite, mul_zero]
    · simp [hk]
  simp only [minorsHom, minorsBlock, Finset.sum_filter]
  rw [Finset.sum_congr rfl fun I' _ => Finset.sum_comm, Finset.sum_comm]
  exact (Finset.sum_congr rfl fun S _ => hS S).symm

/-- `F_{I,J} = ∑_{i ∈ I} e_i ⊗ (row i of F_{I,J})`, a sum of `|I|` rank-one matrices. -/
private lemma minors_restr_eq_sum_rows (I : Finset (Fin d)) (J : Finset (Fin m))
    (F : Matrix (Fin d) (Fin m) ℝ) :
    minorsRestr I J F = ∑ i ∈ I, vecMulVec (Pi.single i 1) (fun j => minorsRestr I J F i j) := by
  ext a b
  simp only [Matrix.sum_apply, vecMulVec_apply, Pi.single_apply, ite_mul, one_mul, zero_mul,
    minorsRestr, of_apply]
  by_cases ha : a ∈ I <;> simp [ha]

/-- `F_{I,J} = ∑_{j ∈ J} (column j of F_{I,J}) ⊗ e_j`, a sum of `|J|` rank-one matrices. -/
private lemma minors_restr_eq_sum_cols (I : Finset (Fin d)) (J : Finset (Fin m))
    (F : Matrix (Fin d) (Fin m) ℝ) :
    minorsRestr I J F = ∑ j ∈ J, vecMulVec (fun i => minorsRestr I J F i j) (Pi.single j 1) := by
  ext a b
  simp only [Matrix.sum_apply, vecMulVec_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    minorsRestr, of_apply]
  by_cases hb : b ∈ J <;> simp [hb]

/-- **Step 3.** `S_{I,J} = 0` when `|I| < k` or `|J| < k`, by induction on `|I| + |J|`:
`F_{I,J}` is then a sum of fewer than `k` rank-one matrices, so `P_k (F_{I,J}) = 0` (Step 2b, for
[CDKM]'s `rank F_{I,J} < k` and (6.2)), and the other terms of
`P_k (F_{I,J}) = ∑_{I' ⊆ I, J' ⊆ J} S_{I',J'} (F)` vanish by induction. -/
private lemma minors_block_eq_zero {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : MinorsRA f)
    {c : Finset (Fin d × Fin m) → ℝ} (hc : ∀ F, f F = ∑ S, c S * minorsMono S F) (k : ℕ) :
    ∀ n (I : Finset (Fin d)) (J : Finset (Fin m)), I.card + J.card = n →
      (I.card < k ∨ J.card < k) → ∀ F, minorsBlock c k I J F = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro I J hn hIJ F
  have h1 : minorsHom c k (minorsRestr I J F) = 0 := by
    rcases hIJ with h | h
    · rw [minors_restr_eq_sum_rows]; exact minors_hom_eq_zero hf hc I _ _ h
    · rw [minors_restr_eq_sum_cols]; exact minors_hom_eq_zero hf hc J _ _ h
  rw [minors_hom_restr, ← Finset.sum_product' (f := fun I' J' => minorsBlock c k I' J' F),
    ← Finset.add_sum_erase _ _ (Finset.mk_mem_product (Finset.mem_powerset_self I)
      (Finset.mem_powerset_self J))] at h1
  have h2 : ∑ p ∈ (I.powerset ×ˢ J.powerset).erase (I, J), minorsBlock c k p.1 p.2 F = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    obtain ⟨hne, hp⟩ := Finset.mem_erase.1 hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    have hc1 := Finset.card_le_card hp.1
    have hc2 := Finset.card_le_card hp.2
    have hlt : p.1.card + p.2.card < n := by
      by_cases e1 : p.1 = I
      · have e2 : p.2 ≠ J := fun e2 => hne (Prod.ext e1 e2)
        have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hp.2, e2⟩)
        omega
      · have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hp.1, e1⟩)
        omega
    exact ih _ hlt p.1 p.2 rfl (by omega) F
  rw [h2, add_zero] at h1
  exact h1

/-- For `|I| = |J| = k`: `S_{I,J} (F) = P_k (F_{I,J})`, the other terms of
`P_k (F_{I,J}) = ∑_{I' ⊆ I, J' ⊆ J} S_{I',J'} (F)` vanishing by Step 3. -/
private lemma minors_block_eq {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : MinorsRA f)
    {c : Finset (Fin d × Fin m) → ℝ} (hc : ∀ F, f F = ∑ S, c S * minorsMono S F) {k : ℕ}
    {I : Finset (Fin d)} {J : Finset (Fin m)} (hI : I.card = k) (hJ : J.card = k)
    (F : Matrix (Fin d) (Fin m) ℝ) :
    minorsBlock c k I J F = minorsHom c k (minorsRestr I J F) := by
  rw [minors_hom_restr, ← Finset.sum_product' (f := fun I' J' => minorsBlock c k I' J' F),
    ← Finset.add_sum_erase _ _ (Finset.mk_mem_product (Finset.mem_powerset_self I)
      (Finset.mem_powerset_self J))]
  have h2 : ∑ p ∈ (I.powerset ×ˢ J.powerset).erase (I, J), minorsBlock c k p.1 p.2 F = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    obtain ⟨hne, hp⟩ := Finset.mem_erase.1 hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    refine minors_block_eq_zero hf hc k _ p.1 p.2 rfl ?_ F
    by_cases e1 : p.1 = I
    · have e2 : p.2 ≠ J := fun e2 => hne (Prod.ext e1 e2)
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hp.2, e2⟩)
      omega
    · have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hp.1, e1⟩)
      omega
  rw [h2, add_zero]

/-- `S_{I,J} (F_{I,J}) = S_{I,J} (F)`. -/
private lemma minors_block_restr (c : Finset (Fin d × Fin m) → ℝ) (k : ℕ) (I : Finset (Fin d))
    (J : Finset (Fin m)) (F : Matrix (Fin d) (Fin m) ℝ) :
    minorsBlock c k I J (minorsRestr I J F) = minorsBlock c k I J F := by
  refine Finset.sum_congr rfl fun S hS => ?_
  obtain ⟨-, hI, hJ⟩ := (Finset.mem_filter.1 hS).2
  rw [minors_mono_restr, ite_eq_left ⟨hI.le, hJ.le⟩]

/-! #### Step 4: each surviving block `S_{I,J}` is a multiple of a minor -/

/-- The set of values of an order embedding. -/
private def minorsRng {n k : ℕ} (r : Fin k ↪o Fin n) : Finset (Fin n) :=
  Finset.univ.map r.toEmbedding

private lemma minors_mem_rng {n k : ℕ} (r : Fin k ↪o Fin n) (a : Fin n) :
    a ∈ minorsRng r ↔ ∃ i, r i = a := by
  simp [minorsRng]

private lemma minors_card_rng {n k : ℕ} (r : Fin k ↪o Fin n) : (minorsRng r).card = k := by
  simp [minorsRng]

private lemma minors_rng_orderEmbOfFin {n k : ℕ} (s : Finset (Fin n)) (h : s.card = k) :
    minorsRng (s.orderEmbOfFin h) = s := by
  ext x
  rw [minors_mem_rng]
  constructor
  · rintro ⟨i, rfl⟩
    exact Finset.orderEmbOfFin_mem s h i
  · intro hx
    have : x ∈ Set.range (s.orderEmbOfFin h) := by
      rw [Finset.range_orderEmbOfFin]; exact hx
    exact this

/-- The column `x ∈ ℝ^k` placed in the rows `r`: `∑_i x_i e_{r_i}`. -/
private def minorsEmb {k : ℕ} (r : Fin k ↪o Fin d) (x : Fin k → ℝ) : Fin d → ℝ :=
  fun a => ∑ i, if r i = a then x i else 0

private lemma minors_emb_add {k : ℕ} (r : Fin k ↪o Fin d) (x y : Fin k → ℝ) :
    minorsEmb r (x + y) = minorsEmb r x + minorsEmb r y := by
  ext a
  simp only [minorsEmb, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

private lemma minors_emb_smul {k : ℕ} (r : Fin k ↪o Fin d) (t : ℝ) (x : Fin k → ℝ) :
    minorsEmb r (t • x) = t • minorsEmb r x := by
  ext a
  simp only [minorsEmb, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

private lemma minors_emb_apply {k : ℕ} (r : Fin k ↪o Fin d) (x : Fin k → ℝ) (i : Fin k) :
    minorsEmb r x (r i) = x i := by
  simp only [minorsEmb, r.injective.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- `F_v = ∑_{i,j} v^j_i e_{r_i} ⊗ e_{c_j}`: the block `r × c` has the columns `v^j`, and the
other entries are `0`. -/
private def minorsFv {k : ℕ} (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m) (v : Fin k → Fin k → ℝ) :
    Matrix (Fin d) (Fin m) ℝ :=
  ∑ j, vecMulVec (minorsEmb r (v j)) (Pi.single (c j) 1)

private lemma minors_Fv_apply {k : ℕ} (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m)
    (v : Fin k → Fin k → ℝ) (a : Fin d) (j : Fin k) :
    minorsFv r c v a (c j) = minorsEmb r (v j) a := by
  simp only [minorsFv, Matrix.sum_apply, vecMulVec_apply, Pi.single_apply, c.injective.eq_iff,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private lemma minors_Fv_apply_of_notMem {k : ℕ} (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m)
    (v : Fin k → Fin k → ℝ) (a : Fin d) {b : Fin m} (hb : ∀ j, c j ≠ b) :
    minorsFv r c v a b = 0 := by
  simp only [minorsFv, Matrix.sum_apply, vecMulVec_apply, Pi.single_apply]
  exact Finset.sum_eq_zero fun j _ => by rw [ite_eq_right (fun h => hb j h.symm), mul_zero]

/-- Changing the column `v^j` changes the column `c_j` of `F_v`. -/
private lemma minors_Fv_update {k : ℕ} (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m)
    (v : Fin k → Fin k → ℝ) (j : Fin k) (x : Fin k → ℝ) :
    minorsFv r c (Function.update v j x) = (minorsFv r c v).updateCol (c j) (minorsEmb r x) := by
  ext a b
  rw [updateCol_apply]
  split_ifs with hb
  · subst hb
    rw [minors_Fv_apply, Function.update_self]
  · by_cases hb' : ∃ j', c j' = b
    · obtain ⟨j', rfl⟩ := hb'
      have hj : j' ≠ j := fun h => hb (h ▸ rfl)
      rw [minors_Fv_apply, minors_Fv_apply, Function.update_of_ne hj]
    · push Not at hb'
      rw [minors_Fv_apply_of_notMem r c _ a hb', minors_Fv_apply_of_notMem r c _ a hb']

/-- `F_{I,J}`, for `I`, `J` the values of `r`, `c`, is `F_v` with `v` the columns of the block. -/
private lemma minors_restr_eq_Fv {k : ℕ} (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m)
    (F : Matrix (Fin d) (Fin m) ℝ) :
    minorsRestr (minorsRng r) (minorsRng c) F = minorsFv r c (fun j i => F (r i) (c j)) := by
  ext a b
  simp only [minorsRestr, of_apply, minors_mem_rng]
  by_cases hb : ∃ j, c j = b
  · obtain ⟨j, rfl⟩ := hb
    rw [minors_Fv_apply]
    by_cases ha : ∃ i, r i = a
    · obtain ⟨i, rfl⟩ := ha
      rw [minors_emb_apply, ite_eq_left ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩]
    · push Not at ha
      rw [ite_eq_right (fun h => by obtain ⟨i, hi⟩ := h.1; exact ha i hi)]
      exact (Finset.sum_eq_zero fun i _ => ite_eq_right (ha i)).symm
  · rw [ite_eq_right (fun h => hb h.2), minors_Fv_apply_of_notMem r c _ a (fun j h => hb ⟨j, h⟩)]

private lemma minors_restr_Fv {k : ℕ} (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m)
    (v : Fin k → Fin k → ℝ) : minorsRestr (minorsRng r) (minorsRng c) (minorsFv r c v) =
      minorsFv r c v := by
  rw [minors_restr_eq_Fv]
  congr 1
  ext j i
  rw [minors_Fv_apply, minors_emb_apply]

/-- If the columns `v^p` and `v^q` coincide (`p ≠ q`), then `F_v` is a sum of `k − 1` rank-one
matrices: `F_v = ∑_{j ≠ q} ṽ^j ⊗ b_j`, `b_j = e_{c_j}` for `j ≠ p` and `b_p = e_{c_p} + e_{c_q}`. -/
private lemma minors_Fv_eq_sum_erase {k : ℕ} (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m)
    (v : Fin k → Fin k → ℝ) {p q : Fin k} (hpq : v p = v q) (hne : p ≠ q) :
    minorsFv r c v = ∑ j ∈ Finset.univ.erase q, vecMulVec (minorsEmb r (v j))
      (Pi.single (c j) 1 + if j = p then Pi.single (c q) 1 else 0) := by
  have hp : p ∈ Finset.univ.erase q := Finset.mem_erase.2 ⟨hne, Finset.mem_univ p⟩
  simp only [vecMulVec_add, Finset.sum_add_distrib]
  have e : ∑ j ∈ Finset.univ.erase q,
      vecMulVec (minorsEmb r (v j)) (if j = p then Pi.single (c q) 1 else 0) =
      vecMulVec (minorsEmb r (v q)) (Pi.single (c q) 1) := by
    rw [Finset.sum_eq_single_of_mem p hp (fun j _ hj => by
      rw [ite_eq_right hj]; ext; simp [vecMulVec_apply]), ite_eq_left rfl, hpq]
  rw [e, Finset.sum_erase_add _ _ (Finset.mem_univ q)]
  rfl

/-- A monomial with exactly one entry `s₀` in the column `s₀.2` is linear in that column. -/
private lemma minors_mono_updateCol {S : Finset (Fin d × Fin m)}
    (hS : Set.InjOn Prod.snd (S : Set (Fin d × Fin m))) {s₀ : Fin d × Fin m} (hs₀ : s₀ ∈ S)
    (G : Matrix (Fin d) (Fin m) ℝ) (w : Fin d → ℝ) :
    minorsMono S (G.updateCol s₀.2 w) = w s₀.1 * ∏ s ∈ S.erase s₀, G s.1 s.2 := by
  unfold minorsMono
  rw [← Finset.mul_prod_erase S _ hs₀, updateCol_self]
  congr 1
  refine Finset.prod_congr rfl fun s hs => ?_
  obtain ⟨hne, hs⟩ := Finset.mem_erase.1 hs
  exact updateCol_ne fun h => hne (hS hs hs₀ h)

/-- The form `Q (v¹, …, v^k) = S_{I,J} (F_v)` (`I`, `J` the values of `r`, `cc`), multilinear in
the columns `v^j`: a monomial of `S_{I,J}` has `k` entries in the `k` columns `J`, so exactly one
in each column, and is linear in it ([CDKM] see this from the permutation form of `S_{I,J}`). -/
private noncomputable def minorsQ (c : Finset (Fin d × Fin m) → ℝ) {k : ℕ} (r : Fin k ↪o Fin d)
    (cc : Fin k ↪o Fin m) : MultilinearMap ℝ (fun _ : Fin k => Fin k → ℝ) ℝ where
  toFun v := minorsBlock c k (minorsRng r) (minorsRng cc) (minorsFv r cc v)
  map_update_add' := by
    intro inst v j x y
    obtain rfl : inst = instDecidableEqFin k := Subsingleton.elim _ _
    simp only [minorsBlock, minors_Fv_update, minors_emb_add, ← Finset.sum_add_distrib, ← mul_add]
    refine Finset.sum_congr rfl fun S hS => ?_
    obtain ⟨hk, -, hJ⟩ := (Finset.mem_filter.1 hS).2
    have hinj : Set.InjOn Prod.snd (S : Set (Fin d × Fin m)) :=
      Finset.card_image_iff.1 (by rw [hJ, minors_card_rng, hk])
    obtain ⟨s₀, hs₀, hcj⟩ := Finset.mem_image.1 (hJ ▸ (minors_mem_rng cc (cc j)).2 ⟨j, rfl⟩)
    rw [← hcj, minors_mono_updateCol hinj hs₀, minors_mono_updateCol hinj hs₀,
      minors_mono_updateCol hinj hs₀, Pi.add_apply]
    ring
  map_update_smul' := by
    intro inst v j t x
    obtain rfl : inst = instDecidableEqFin k := Subsingleton.elim _ _
    simp only [minorsBlock, minors_Fv_update, minors_emb_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S hS => ?_
    obtain ⟨hk, -, hJ⟩ := (Finset.mem_filter.1 hS).2
    have hinj : Set.InjOn Prod.snd (S : Set (Fin d × Fin m)) :=
      Finset.card_image_iff.1 (by rw [hJ, minors_card_rng, hk])
    obtain ⟨s₀, hs₀, hcj⟩ := Finset.mem_image.1 (hJ ▸ (minors_mem_rng cc (cc j)).2 ⟨j, rfl⟩)
    rw [← hcj, minors_mono_updateCol hinj hs₀, minors_mono_updateCol hinj hs₀, Pi.smul_apply,
      smul_eq_mul]
    ring

/-- **Step 4.** For `I`, `J` the values of `r`, `cc` (so `|I| = |J| = k`), `S_{I,J}` is a
multiple of the minor with the rows `r` and the columns `cc`. The form `Q` is multilinear, and it
is alternating: `Q (v) = P_k (F_v)` (Step 3), and if `v^p = v^q` with `p ≠ q`, then `F_v` is a sum
of `k − 1` rank-one matrices, so `P_k (F_v) = 0` (Step 2b, for [CDKM]'s
`dim span {v^j} < k` and (6.2)). So `Q = Q (e) det`, and
`S_{I,J} (F) = S_{I,J} (F_{I,J}) = Q (columns of the block of F) = Q (e) minor F r cc`. -/
private lemma minors_block_eq_minor {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : MinorsRA f)
    {c : Finset (Fin d × Fin m) → ℝ} (hc : ∀ F, f F = ∑ S, c S * minorsMono S F) {k : ℕ}
    (r : Fin k ↪o Fin d) (cc : Fin k ↪o Fin m) :
    ∃ a : ℝ, ∀ F, minorsBlock c k (minorsRng r) (minorsRng cc) F = a * minor F r cc := by
  let Q : (Fin k → ℝ) [⋀^Fin k]→ₗ[ℝ] ℝ :=
    { minorsQ c r cc with
      map_eq_zero_of_eq' := fun v p q hpq hne => by
        change minorsBlock c k (minorsRng r) (minorsRng cc) (minorsFv r cc v) = 0
        rw [minors_block_eq hf hc (minors_card_rng r) (minors_card_rng cc), minors_restr_Fv,
          minors_Fv_eq_sum_erase r cc v hpq hne]
        have := Fin.pos p
        exact minors_hom_eq_zero hf hc _ _ _ (by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
          omega) }
  refine ⟨Q (Pi.basisFun ℝ (Fin k)), fun F => ?_⟩
  have h := congrArg (fun φ : (Fin k → ℝ) [⋀^Fin k]→ₗ[ℝ] ℝ => φ (fun j i => F (r i) (cc j)))
    (Q.eq_smul_basis_det (Pi.basisFun ℝ (Fin k)))
  simp only [_root_.smul_apply, smul_eq_mul, Module.Basis.det_apply] at h
  have hM : (Pi.basisFun ℝ (Fin k)).toMatrix (fun j i => F (r i) (cc j)) = F.submatrix r cc := by
    ext i j
    simp [Module.Basis.toMatrix_apply]
  rw [hM] at h
  rw [← minors_block_restr, minors_restr_eq_Fv, minor]
  exact h

end RankOneAffine

/-- **A rank-one affine function is an affine combination of minors** (the implication
(iii) ⇒ (iv) of Dacorogna 2008, Theorem 5.20, the statement cited): for a rank-one affine
`f : ℝ^{d×m} → ℝ` there are coefficients `a k r c` with
`f (A) = ∑_{k ≤ min d m} ∑_{r, c} a k r c · minor A r c` for every `A` (the `0 × 0` minor is the
constant `1`). Continuity is not needed. The proof is that of Conti–Dolzmann–Kirchheim–Müller
2006, Theorem 6.1, with Steps 2a and 2b in place of its use of continuity (module docstring):
`f = ∑_S c_S F^S = ∑_k P_k` (Step 2a), `P_k = ∑_{I,J} S_{I,J}` by grouping the monomials by their
rows and columns, `S_{I,J} = 0` unless `|I| = |J| = k` (Step 3), and then `S_{I,J}` is a multiple
of the minor with the rows `I` and the columns `J` (Step 4); there is no `k × k` minor for
`k > min d m`. -/
theorem RankOneAffine.exists_eq_sum_minor {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : RankOneAffine f) :
    ∃ a : (k : ℕ) → (Fin k ↪o Fin d) → (Fin k ↪o Fin m) → ℝ,
      ∀ A, f A = ∑ k ∈ Finset.range (min d m + 1), ∑ r, ∑ c, a k r c * minor A r c := by
  have hRA := minors_RA_of_rankOneAffine hf
  obtain ⟨γ, hγ⟩ := minors_exists_mono hRA
  choose a ha using fun k (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m) =>
    minors_block_eq_minor hRA hγ r c
  refine ⟨a, fun A => ?_⟩
  -- `f = ∑_k P_k`
  have step1 : ∑ S, γ S * minorsMono S A =
      ∑ k ∈ Finset.range (d * m + 1), minorsHom γ k A := by
    refine (Finset.sum_fiberwise_of_maps_to (g := Finset.card) (fun S _ => ?_) _).symm
    have := Finset.card_le_univ S
    simp only [Fintype.card_prod, Fintype.card_fin] at this
    exact Finset.mem_range.2 (Nat.lt_succ_of_le this)
  -- `P_k = ∑_{I,J} S_{I,J}`
  have step2 : ∀ k, minorsHom γ k A = ∑ I, ∑ J, minorsBlock γ k I J A := by
    intro k
    rw [← Fintype.sum_prod_type', minorsHom,
      ← Finset.sum_fiberwise _ (fun S => (S.image Prod.fst, S.image Prod.snd))]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [minorsBlock, Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun S _ => ?_) fun _ _ => rfl
    simp only [Prod.ext_iff]
  -- `∑_{I,J} S_{I,J} = ∑_{r,c} ĉ minor`: only `|I| = |J| = k` contributes (Step 3)
  have step3 : ∀ k, ∑ I, ∑ J, minorsBlock γ k I J A = ∑ r, ∑ c, a k r c * minor A r c := by
    intro k
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    refine (Finset.sum_of_injOn (fun p => (minorsRng p.1, minorsRng p.2)) ?_ ?_ ?_ ?_).symm
    · rintro ⟨r, c⟩ - ⟨r', c'⟩ - h
      simp only [Prod.mk.injEq] at h
      have e1 : r' = (minorsRng r).orderEmbOfFin (minors_card_rng r) :=
        Finset.orderEmbOfFin_unique' _ fun x => h.1 ▸ (minors_mem_rng r' _).2 ⟨x, rfl⟩
      have e2 : r = (minorsRng r).orderEmbOfFin (minors_card_rng r) :=
        Finset.orderEmbOfFin_unique' _ fun x => (minors_mem_rng r _).2 ⟨x, rfl⟩
      have e3 : c' = (minorsRng c).orderEmbOfFin (minors_card_rng c) :=
        Finset.orderEmbOfFin_unique' _ fun x => h.2 ▸ (minors_mem_rng c' _).2 ⟨x, rfl⟩
      have e4 : c = (minorsRng c).orderEmbOfFin (minors_card_rng c) :=
        Finset.orderEmbOfFin_unique' _ fun x => (minors_mem_rng c _).2 ⟨x, rfl⟩
      exact Prod.ext (e2.trans e1.symm) (e4.trans e3.symm)
    · exact fun _ _ => Finset.mem_univ _
    · rintro ⟨I, J⟩ - hIJ
      by_contra hne
      obtain ⟨S, hS, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      obtain ⟨hk, hI, hJ⟩ := (Finset.mem_filter.1 hS).2
      have hI' : I.card ≤ k := by
        rw [← (show S.image Prod.fst = I from hI), ← hk]; exact Finset.card_image_le
      have hJ' : J.card ≤ k := by
        rw [← (show S.image Prod.snd = J from hJ), ← hk]; exact Finset.card_image_le
      by_cases h : I.card = k ∧ J.card = k
      · refine hIJ ⟨(I.orderEmbOfFin h.1, J.orderEmbOfFin h.2),
          Finset.mem_coe.2 (Finset.mem_univ _), ?_⟩
        dsimp only
        rw [minors_rng_orderEmbOfFin, minors_rng_orderEmbOfFin]
      · exact hne (minors_block_eq_zero hRA hγ k _ I J rfl (by omega) A)
    · rintro ⟨r, c⟩ -
      exact (ha k r c A).symm
  -- the degree bound: no `k × k` minor for `k > min d m`
  have step4 : ∑ k ∈ Finset.range (d * m + 1), ∑ r, ∑ c, a k r c * minor A r c =
      ∑ k ∈ Finset.range (min d m + 1), ∑ r, ∑ c, a k r c * minor A r c := by
    refine (Finset.sum_subset (Finset.range_subset_range.2 (Nat.succ_le_succ ?_))
      fun k _ hk => ?_).symm
    · rcases Nat.eq_zero_or_pos m with h | h
      · simp [h]
      · exact (min_le_left d m).trans (Nat.le_mul_of_pos_right d h)
    · rw [Finset.mem_range, not_lt] at hk
      refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun c _ => ?_
      have h1 := Fintype.card_le_of_embedding r.toEmbedding
      have h2 := Fintype.card_le_of_embedding c.toEmbedding
      simp only [Fintype.card_fin] at h1 h2
      omega
  rw [hγ A, step1, ← step4]
  exact Finset.sum_congr rfl fun k _ => by rw [step2, step3]

end CalculusOfVariations
