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

* `exists_eq_sum_minor_of_rank_lt`: a homogeneous polynomial of degree `k` in the entries of the
  `d × m` matrices that vanishes on the matrices of rank `< k` is a linear combination of the
  `k × k` minors. This is the second half of the proof of Theorem 6.1 of S. Conti, G. Dolzmann,
  B. Kirchheim, S. Müller, *Sufficient conditions for the validity of the Cauchy–Born rule close
  to SO(n)*, J. Eur. Math. Soc. 8 (2006), 515–530, Appendix, pp. 527–528 ([CDKM]), and it is
  proved as there (Steps 3 to 5 below).
* `RankOneAffine.exists_eq_sum_minor`: a rank-one affine `f : ℝ^{d×m} → ℝ`, not assumed
  continuous, is an affine combination of the minors of orders `k ≤ min (d, m)`. With the
  hypothesis of continuity this is the implication (iii) ⇒ (iv) of B. Dacorogna, *Direct methods
  in the calculus of variations*, 2nd ed., Springer, 2008, Theorem 5.20 (the result cited; the
  book is not openly accessible, and its proof was not consulted), and
  `RankOneAffine.exists_eq_sum_minor_of_continuous` (module `Minors.RankOneAffineContinuous`)
  proves it by [CDKM]'s argument. **The proof of `RankOneAffine.exists_eq_sum_minor` is not
  [CDKM]'s.** [CDKM]'s first half uses the continuity of the function (distributional
  derivatives, (6.1), (6.2), their Proposition 6.2, and Taylor's formula (6.3)); here it is
  replaced by an elementary multi-affine argument, a simpler argument of our own (Steps 2a and 2b
  below), which needs no continuity. The second half is Steps 3 to 5.

Below, `d × m` and `min (d, m)` stand for [CDKM]'s `m × n` and `min (m, n)`.

## Steps 3 to 5: [CDKM], pp. 527–528

`P (F) = ∑_t γ_t F_{t₁} ⋯ F_{t_k}` over the `k`-tuples `t` of entries ([CDKM]: "`P_k (F)` is a
linear combination of products `F_{α₁,β₁} ⋯ F_{α_k,β_k}`"), and `P (F) = 0` when `rank F < k`
((6.2) and (6.3) in [CDKM]).

3. The terms of `P` are grouped by their sets of rows `I` and of columns `J` into `S_{I,J}`
   (`minors_poly_eq_sum_block`). With `F_{I,J}` the matrix `F` with the entries outside `I × J`
   set to `0`, `P (F_{I,J}) = ∑_{I' ⊆ I, J' ⊆ J} S_{I',J'} (F)` (`minors_poly_restr`). If `|I| < k`
   or `|J| < k`, then `rank F_{I,J} < k` (`minors_rank_restr_lt`), so `P (F_{I,J}) = 0`, and by
   induction `S_{I,J} = 0` (`minors_block_eq_zero`; [CDKM] induct separately on `|I|` and on
   `|J|`, here the induction is on `|I| + |J|`).
4. Regrouping the terms obtained by permutation within fixed index sets, `P = ∑_{α,β} P_{α,β}`
   over the increasing `α₁ < ⋯ < α_k`, `β₁ < ⋯ < β_k`, with
   `P_{α,β} (F) = ∑_{σ ∈ S_k} c^σ_{α,β} F_{α₁ β_{σ 1}} ⋯ F_{α_k β_{σ k}}` and
   `c^σ_{α,β} = ∑_τ c̃_{τ(α), (τ ∘ σ)(β)}` (`minorsCoeff`, `minorsPerm`,
   `minors_poly_eq_sum_perm`).
5. The multilinear form `Q (v¹, …, v^k) = ∑_σ c^σ v^{σ 1}_1 ⋯ v^{σ k}_k` on `(ℝ^k)^k` (`minorsQ`)
   satisfies `Q (v) = P_{α,β} (F_v) = P (F_v)`, `F_v = ∑_{i,j} v^j_i e_{α_i} ⊗ e_{β_j}`, so
   `Q (v) = 0` when `rank F_v < k` (`minors_perm_Fv`, `minors_Q_eq_zero_of_rank_lt`); by
   polarization `Q` is antisymmetric, hence a multiple `ĉ_{α,β} det` of the determinant, and
   `P_{α,β} (F) = ĉ_{α,β} det_k F_{I,J}` (`minors_perm_eq_minor`). Here the polarization is not
   needed: Mathlib's uniqueness theorem, `AlternatingMap.eq_smul_basis_det`, is stated for forms
   that vanish when two arguments are equal, which is the vanishing that [CDKM]'s polarization
   starts from (`F_v` with two equal columns is a sum of `k − 1` rank-one matrices,
   `minors_Fv_eq_sum_erase`).

## Steps 2a and 2b: the multi-affine route, without continuity (not [CDKM]'s)

* **Step 2a.** `f` is affine in each entry, since `e_i ⊗ e_j` has rank one, and a function on
  `ℝ^ι` (`ι` finite) that is affine in each coordinate is `∑_{S ⊆ ι} c_S ∏_{s ∈ S} x_s`
  (`minors_multiaffine`). So `f (F) = ∑_S c_S F^S` over the sets `S` of entries,
  `F^S = ∏_{(i,j) ∈ S} F_{ij}` (`minors_exists_mono`), and `f = ∑_k P_k`,
  `P_k = ∑_{|S| = k} c_S F^S` (`minorsHom`), a polynomial in which no entry occurs twice.
* **Step 2b.** If `F = ∑_{l ≤ r} A_l` with `rank A_l ≤ 1` and `r < k`, then `P_k (F) = 0`
  (`minors_hom_eq_zero`): `s ↦ f (∑_l s_l A_l)` is affine in each `s_l`, so by Step 2a the
  function `t ↦ f (t F)` is a polynomial of degree at most `r`, while `f (t F) = ∑_j t^j P_j (F)`.
  A matrix of rank `< k` is a sum of at most `k − 1` rank-one matrices
  (`exists_sum_vecMulVec_of_rank`), so `P_k (F) = 0` when `rank F < k`
  (`minors_hom_eq_zero_of_rank_lt`), and `P_k = 0` for `k > min (d, m)` (`minors_eq_sum_hom`).

Then Steps 3 to 5 apply to each `P_k`, written with tuples of entries (`minors_hom_eq_tuple`).
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

open Matrix

/-! ### Rank-one lines and rank -/

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

/-- A rank-one affine function is affine along the rank-one lines `t ↦ A + t (u ⊗ v)`: by
definition it is convex and concave along them. -/
theorem RankOneAffine.add_smul_vecMulVec {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : RankOneAffine f) (A : Matrix (Fin d) (Fin m) ℝ) (u : Fin d → ℝ) (v : Fin m → ℝ)
    (t : ℝ) : f (A + t • vecMulVec u v) = f A + t * (f (A + vecMulVec u v) - f A) := by
  by_cases h : vecMulVec u v = 0
  · simp [h]
  have hr := minors_rank_vecMulVec h
  have := minors_affine_of_convex_concave (hf.1 A _ hr) (hf.2 A _ hr) t
  simpa using this

/-- A matrix of rank `r` is a sum of `r` rank-one matrices: with a basis `a_1, …, a_r` of the
column space, `F = ∑_l a_l ⊗ b_l`, `b_l` the coordinates of the columns of `F` along `a_l`. -/
theorem exists_sum_vecMulVec_of_rank (F : Matrix (Fin d) (Fin m) ℝ) :
    ∃ (r : ℕ) (a : Fin r → Fin d → ℝ) (b : Fin r → Fin m → ℝ), r ≤ F.rank ∧
      F = ∑ l, vecMulVec (a l) (b l) := by
  let V := LinearMap.range F.mulVecLin
  let e := Module.finBasis ℝ V
  let col : Fin m → V := fun j => ⟨F.mulVecLin (Pi.single j 1), LinearMap.mem_range_self _ _⟩
  refine ⟨_, fun l => (e l : Fin d → ℝ), fun l j => e.repr (col j) l, le_rfl, ?_⟩
  ext i j
  have h1 : F i j = (col j : Fin d → ℝ) i := by
    simp [col]
  have h2 : (col j : Fin d → ℝ) = ∑ l, e.repr (col j) l • (e l : Fin d → ℝ) := by
    conv_lhs => rw [← e.sum_repr (col j)]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  rw [h1, h2, Matrix.sum_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, vecMulVec_apply, mul_comm]

/-- The rank of a sum of `|L|` rank-one matrices is at most `|L|`. -/
private lemma minors_rank_sum_vecMulVec_le {ι : Type*} [DecidableEq ι] (L : Finset ι)
    (a : ι → Fin d → ℝ) (b : ι → Fin m → ℝ) :
    (∑ l ∈ L, vecMulVec (a l) (b l)).rank ≤ L.card := by
  have hle : LinearMap.range (∑ l ∈ L, vecMulVec (a l) (b l)).mulVecLin ≤
      Submodule.span ℝ ((L.image a : Finset (Fin d → ℝ)) : Set (Fin d → ℝ)) := by
    rintro _ ⟨x, rfl⟩
    rw [Matrix.mulVecLin_apply, sum_mulVec]
    refine Submodule.sum_mem _ fun l hl => ?_
    rw [vecMulVec_mulVec, op_smul_eq_smul]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem a hl)))
  exact (Submodule.finrank_mono hle).trans
    ((finrank_span_finset_le_card _).trans Finset.card_image_le)

/-! ### A homogeneous polynomial vanishing on the matrices of rank `< k` -/

section Homogeneous

variable {k : ℕ}

/-- The monomial `F_{t₁} ⋯ F_{t_k}` of a `k`-tuple `t` of entries. -/
private def minorsMono (t : Fin k → Fin d × Fin m) (F : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  ∏ i, F (t i).1 (t i).2

/-- The homogeneous polynomial `P (F) = ∑_t γ_t F_{t₁} ⋯ F_{t_k}`. -/
private def minorsPoly (γ : (Fin k → Fin d × Fin m) → ℝ) (F : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  ∑ t, γ t * minorsMono t F

/-- The set of rows `{α₁, …, α_k}` of a tuple of entries `t = ((α₁, β₁), …, (α_k, β_k))`. -/
private def minorsRows (t : Fin k → Fin d × Fin m) : Finset (Fin d) :=
  Finset.univ.image fun i => (t i).1

/-- The set of columns `{β₁, …, β_k}` of a tuple of entries. -/
private def minorsCols (t : Fin k → Fin d × Fin m) : Finset (Fin m) :=
  Finset.univ.image fun i => (t i).2

/-- `F_{I,J}`: the entries of `F` outside the rows `I` and the columns `J` set to `0`. -/
private def minorsRestr (I : Finset (Fin d)) (J : Finset (Fin m)) (F : Matrix (Fin d) (Fin m) ℝ) :
    Matrix (Fin d) (Fin m) ℝ :=
  Matrix.of fun i j => if i ∈ I ∧ j ∈ J then F i j else 0

/-- `S_{I,J}`: the terms of `P` whose set of rows is `I` and whose set of columns is `J`. -/
private def minorsBlock (γ : (Fin k → Fin d × Fin m) → ℝ) (I : Finset (Fin d))
    (J : Finset (Fin m)) (F : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  ∑ t with minorsRows t = I ∧ minorsCols t = J, γ t * minorsMono t F

/-- [CDKM]'s grouping: `P = ∑_{I,J} S_{I,J}`. -/
private lemma minors_poly_eq_sum_block (γ : (Fin k → Fin d × Fin m) → ℝ)
    (F : Matrix (Fin d) (Fin m) ℝ) : minorsPoly γ F = ∑ I, ∑ J, minorsBlock γ I J F := by
  rw [← Fintype.sum_prod_type', minorsPoly,
    ← Finset.sum_fiberwise _ (fun t => (minorsRows t, minorsCols t))]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [minorsBlock]
  refine Finset.sum_congr (Finset.filter_congr fun t _ => ?_) fun _ _ => rfl
  simp only [Prod.ext_iff]

/-- `(F_{I,J})_{t₁} ⋯ (F_{I,J})_{t_k} = F_{t₁} ⋯ F_{t_k}` if the entries of `t` are in `I × J`, and
`0` otherwise. -/
private lemma minors_mono_restr (t : Fin k → Fin d × Fin m) (I : Finset (Fin d))
    (J : Finset (Fin m)) (F : Matrix (Fin d) (Fin m) ℝ) :
    minorsMono t (minorsRestr I J F) =
      if minorsRows t ⊆ I ∧ minorsCols t ⊆ J then minorsMono t F else 0 := by
  unfold minorsMono minorsRestr
  split_ifs with h
  · refine Finset.prod_congr rfl fun i _ => ?_
    have h1 : (t i).1 ∈ I := h.1 (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have h2 : (t i).2 ∈ J := h.2 (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    simp [h1, h2]
  · rw [not_and_or] at h
    rcases h with h | h
    · obtain ⟨a, ha, haI⟩ := Finset.not_subset.1 h
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [haI])
    · obtain ⟨b, hb, hbJ⟩ := Finset.not_subset.1 h
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hb
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hbJ])

/-- `P (F_{I,J}) = ∑_{I' ⊆ I, J' ⊆ J} S_{I',J'} (F)`. -/
private lemma minors_poly_restr (γ : (Fin k → Fin d × Fin m) → ℝ) (I : Finset (Fin d))
    (J : Finset (Fin m)) (F : Matrix (Fin d) (Fin m) ℝ) :
    minorsPoly γ (minorsRestr I J F) =
      ∑ I' ∈ I.powerset, ∑ J' ∈ J.powerset, minorsBlock γ I' J' F := by
  have ht : ∀ t : Fin k → Fin d × Fin m, (∑ I' ∈ I.powerset, ∑ J' ∈ J.powerset,
      if minorsRows t = I' ∧ minorsCols t = J' then γ t * minorsMono t F else 0) =
      γ t * minorsMono t (minorsRestr I J F) := by
    intro t
    rw [minors_mono_restr]
    simp only [ite_and, Finset.sum_ite_eq, Finset.mem_powerset, Finset.sum_ite_irrel,
      Finset.sum_const_zero, mul_ite, mul_zero]
  simp only [minorsPoly, minorsBlock, Finset.sum_filter]
  rw [Finset.sum_congr rfl fun I' _ => Finset.sum_comm, Finset.sum_comm]
  exact (Finset.sum_congr rfl fun t _ => ht t).symm

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

/-- `rank F_{I,J} < k` when `|I| < k` or `|J| < k`. -/
private lemma minors_rank_restr_lt {I : Finset (Fin d)} {J : Finset (Fin m)} {k : ℕ}
    (h : I.card < k ∨ J.card < k) (F : Matrix (Fin d) (Fin m) ℝ) :
    (minorsRestr I J F).rank < k := by
  rcases h with h | h
  · rw [minors_restr_eq_sum_rows]
    exact (minors_rank_sum_vecMulVec_le _ _ _).trans_lt h
  · rw [minors_restr_eq_sum_cols]
    exact (minors_rank_sum_vecMulVec_le _ _ _).trans_lt h

/-- **Step 3.** If `P` vanishes on the matrices of rank `< k`, then `S_{I,J} = 0` when `|I| < k`
or `|J| < k`: then `rank F_{I,J} < k`, so `P (F_{I,J}) = 0`, and the other terms of
`P (F_{I,J}) = ∑_{I' ⊆ I, J' ⊆ J} S_{I',J'} (F)` vanish by induction. [CDKM] induct separately on
`|I|` and on `|J|`; here the induction is on `|I| + |J|`. -/
private lemma minors_block_eq_zero {γ : (Fin k → Fin d × Fin m) → ℝ}
    (hγ : ∀ F : Matrix (Fin d) (Fin m) ℝ, F.rank < k → minorsPoly γ F = 0) :
    ∀ n (I : Finset (Fin d)) (J : Finset (Fin m)), I.card + J.card = n →
      (I.card < k ∨ J.card < k) → ∀ F, minorsBlock γ I J F = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro I J hn hIJ F
  have h1 : minorsPoly γ (minorsRestr I J F) = 0 := hγ _ (minors_rank_restr_lt hIJ F)
  rw [minors_poly_restr, ← Finset.sum_product' (f := fun I' J' => minorsBlock γ I' J' F),
    ← Finset.add_sum_erase _ _ (Finset.mk_mem_product (Finset.mem_powerset_self I)
      (Finset.mem_powerset_self J))] at h1
  have h2 : ∑ p ∈ (I.powerset ×ˢ J.powerset).erase (I, J), minorsBlock γ p.1 p.2 F = 0 := by
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

/-- For `|I| = |J| = k`: `S_{I,J} (F) = P (F_{I,J})`, the other terms of
`P (F_{I,J}) = ∑_{I' ⊆ I, J' ⊆ J} S_{I',J'} (F)` vanishing by Step 3. -/
private lemma minors_block_eq {γ : (Fin k → Fin d × Fin m) → ℝ}
    (hγ : ∀ F : Matrix (Fin d) (Fin m) ℝ, F.rank < k → minorsPoly γ F = 0)
    {I : Finset (Fin d)} {J : Finset (Fin m)} (hI : I.card = k) (hJ : J.card = k)
    (F : Matrix (Fin d) (Fin m) ℝ) : minorsBlock γ I J F = minorsPoly γ (minorsRestr I J F) := by
  rw [minors_poly_restr, ← Finset.sum_product' (f := fun I' J' => minorsBlock γ I' J' F),
    ← Finset.add_sum_erase _ _ (Finset.mk_mem_product (Finset.mem_powerset_self I)
      (Finset.mem_powerset_self J))]
  have h2 : ∑ p ∈ (I.powerset ×ˢ J.powerset).erase (I, J), minorsBlock γ p.1 p.2 F = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    obtain ⟨hne, hp⟩ := Finset.mem_erase.1 hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    refine minors_block_eq_zero hγ _ p.1 p.2 rfl ?_ F
    by_cases e1 : p.1 = I
    · have e2 : p.2 ≠ J := fun e2 => hne (Prod.ext e1 e2)
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hp.2, e2⟩)
      omega
    · have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hp.1, e1⟩)
      omega
  rw [h2, add_zero]

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

/-- The tuple of entries `((α_{τ 1}, β_{σ (τ 1)}), …, (α_{τ k}, β_{σ (τ k)}))`. -/
private def minorsTuple (α : Fin k ↪o Fin d) (β : Fin k ↪o Fin m) (τ σ : Equiv.Perm (Fin k)) :
    Fin k → Fin d × Fin m :=
  fun i => (α (τ i), β (σ (τ i)))

/-- [CDKM]'s coefficient `c^σ_{α,β} = ∑_τ c̃_{τ(α), (τ ∘ σ)(β)}`. -/
private def minorsCoeff (γ : (Fin k → Fin d × Fin m) → ℝ) (α : Fin k ↪o Fin d)
    (β : Fin k ↪o Fin m) (σ : Equiv.Perm (Fin k)) : ℝ :=
  ∑ τ : Equiv.Perm (Fin k), γ (minorsTuple α β τ σ)

/-- `P_{α,β} (F) = ∑_{σ ∈ S_k} c^σ_{α,β} F_{α₁ β_{σ 1}} ⋯ F_{α_k β_{σ k}}`. -/
private def minorsPerm (γ : (Fin k → Fin d × Fin m) → ℝ) (α : Fin k ↪o Fin d)
    (β : Fin k ↪o Fin m) (F : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin k), minorsCoeff γ α β σ * ∏ i, F (α i) (β (σ i))

private lemma minors_mono_tuple (α : Fin k ↪o Fin d) (β : Fin k ↪o Fin m)
    (τ σ : Equiv.Perm (Fin k)) (F : Matrix (Fin d) (Fin m) ℝ) :
    minorsMono (minorsTuple α β τ σ) F = ∏ i, F (α i) (β (σ i)) :=
  Equiv.prod_comp τ fun j => F (α j) (β (σ j))

private lemma minors_rows_tuple (α : Fin k ↪o Fin d) (β : Fin k ↪o Fin m)
    (τ σ : Equiv.Perm (Fin k)) : minorsRows (minorsTuple α β τ σ) = minorsRng α := by
  ext a
  simp only [minorsRows, minorsTuple, Finset.mem_image, Finset.mem_univ, true_and,
    minors_mem_rng]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨τ i, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨τ.symm j, by rw [Equiv.apply_symm_apply]⟩

private lemma minors_cols_tuple (α : Fin k ↪o Fin d) (β : Fin k ↪o Fin m)
    (τ σ : Equiv.Perm (Fin k)) : minorsCols (minorsTuple α β τ σ) = minorsRng β := by
  ext b
  simp only [minorsCols, minorsTuple, Finset.mem_image, Finset.mem_univ, true_and,
    minors_mem_rng]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨σ (τ i), rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨τ.symm (σ.symm j), by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]⟩

/-- A `k`-tuple of entries with the rows `α` and the columns `β` is `minorsTuple α β τ σ` for
some permutations `τ`, `σ`. -/
private lemma minors_exists_tuple {α : Fin k ↪o Fin d} {β : Fin k ↪o Fin m}
    {t : Fin k → Fin d × Fin m} (hI : minorsRows t = minorsRng α)
    (hJ : minorsCols t = minorsRng β) :
    ∃ p : Equiv.Perm (Fin k) × Equiv.Perm (Fin k), minorsTuple α β p.2 p.1 = t := by
  have hinj1 : Function.Injective fun i => (t i).1 := by
    have hc : (Finset.univ.image fun i => (t i).1).card = (Finset.univ : Finset (Fin k)).card := by
      change (minorsRows t).card = _
      rw [hI, minors_card_rng, Finset.card_univ, Fintype.card_fin]
    exact fun a b hab => Finset.card_image_iff.1 hc (Finset.mem_coe.2 (Finset.mem_univ a))
      (Finset.mem_coe.2 (Finset.mem_univ b)) hab
  have hinj2 : Function.Injective fun i => (t i).2 := by
    have hc : (Finset.univ.image fun i => (t i).2).card = (Finset.univ : Finset (Fin k)).card := by
      change (minorsCols t).card = _
      rw [hJ, minors_card_rng, Finset.card_univ, Fintype.card_fin]
    exact fun a b hab => Finset.card_image_iff.1 hc (Finset.mem_coe.2 (Finset.mem_univ a))
      (Finset.mem_coe.2 (Finset.mem_univ b)) hab
  have h1 : ∀ i, ∃ j, α j = (t i).1 := fun i =>
    (minors_mem_rng α _).1 (by rw [← hI]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have h2 : ∀ i, ∃ j, β j = (t i).2 := fun i =>
    (minors_mem_rng β _).1 (by rw [← hJ]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i))
  choose τ hτ using h1
  choose π hπ using h2
  have hτi : Function.Injective τ := fun i i' h => hinj1 (by simp only [← hτ, h])
  have hπi : Function.Injective π := fun i i' h => hinj2 (by simp only [← hπ, h])
  let τ' := Equiv.ofBijective τ (Finite.injective_iff_bijective.1 hτi)
  let π' := Equiv.ofBijective π (Finite.injective_iff_bijective.1 hπi)
  refine ⟨(τ'.symm.trans π', τ'), funext fun i => ?_⟩
  simp only [minorsTuple, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact Prod.ext (hτ i) (hπ i)

/-- `S_{I,J} = P_{α,β}` for `I`, `J` the values of `α`, `β` ([CDKM]: "regrouping terms which are
obtained by permutation within a fixed index set"). -/
private lemma minors_block_eq_perm (γ : (Fin k → Fin d × Fin m) → ℝ) (α : Fin k ↪o Fin d)
    (β : Fin k ↪o Fin m) (F : Matrix (Fin d) (Fin m) ℝ) :
    minorsBlock γ (minorsRng α) (minorsRng β) F = minorsPerm γ α β F := by
  have e : minorsPerm γ α β F = ∑ p : Equiv.Perm (Fin k) × Equiv.Perm (Fin k),
      γ (minorsTuple α β p.2 p.1) * minorsMono (minorsTuple α β p.2 p.1) F := by
    rw [Fintype.sum_prod_type]
    simp only [minorsPerm, minorsCoeff, Finset.sum_mul, minors_mono_tuple]
  rw [e]
  symm
  refine Finset.sum_nbij (fun p => minorsTuple α β p.2 p.1) (fun p _ => ?_)
    (fun p _ p' _ h => ?_) (fun t ht => ?_) (fun p _ => rfl)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨minors_rows_tuple α β _ _, minors_cols_tuple α β _ _⟩
  · have hτ : p.2 = p'.2 := Equiv.ext fun i =>
      α.injective (congrArg Prod.fst (congrFun h i))
    have hσ : p.1 = p'.1 := Equiv.ext fun j => by
      have := congrArg Prod.snd (congrFun h (p.2.symm j))
      simp only [minorsTuple, hτ, Equiv.apply_symm_apply] at this
      exact β.injective this
    exact Prod.ext hσ hτ
  · obtain ⟨hI, hJ⟩ := (Finset.mem_filter.1 (Finset.mem_coe.1 ht)).2
    obtain ⟨p, hp⟩ := minors_exists_tuple hI hJ
    exact ⟨p, Finset.mem_coe.2 (Finset.mem_univ p), hp⟩

/-- **Step 4.** `P = ∑_{α,β} P_{α,β}` over the increasing `α : Fin k ↪o Fin d`,
`β : Fin k ↪o Fin m`: the `S_{I,J}` with `|I| < k` or `|J| < k` vanish by Step 3, those with
`|I| > k` or `|J| > k` are empty sums, and `S_{I,J} = P_{α,β}` for the increasing enumerations
`α`, `β` of `I`, `J`. -/
private lemma minors_poly_eq_sum_perm {γ : (Fin k → Fin d × Fin m) → ℝ}
    (hγ : ∀ F : Matrix (Fin d) (Fin m) ℝ, F.rank < k → minorsPoly γ F = 0)
    (F : Matrix (Fin d) (Fin m) ℝ) :
    minorsPoly γ F = ∑ α : Fin k ↪o Fin d, ∑ β : Fin k ↪o Fin m, minorsPerm γ α β F := by
  rw [minors_poly_eq_sum_block, ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  refine (Finset.sum_of_injOn (fun p => (minorsRng p.1, minorsRng p.2)) ?_ ?_ ?_ ?_).symm
  · rintro ⟨α, β⟩ - ⟨α', β'⟩ - h
    simp only [Prod.mk.injEq] at h
    have e1 : α' = (minorsRng α).orderEmbOfFin (minors_card_rng α) :=
      Finset.orderEmbOfFin_unique' _ fun x => h.1 ▸ (minors_mem_rng α' _).2 ⟨x, rfl⟩
    have e2 : α = (minorsRng α).orderEmbOfFin (minors_card_rng α) :=
      Finset.orderEmbOfFin_unique' _ fun x => (minors_mem_rng α _).2 ⟨x, rfl⟩
    have e3 : β' = (minorsRng β).orderEmbOfFin (minors_card_rng β) :=
      Finset.orderEmbOfFin_unique' _ fun x => h.2 ▸ (minors_mem_rng β' _).2 ⟨x, rfl⟩
    have e4 : β = (minorsRng β).orderEmbOfFin (minors_card_rng β) :=
      Finset.orderEmbOfFin_unique' _ fun x => (minors_mem_rng β _).2 ⟨x, rfl⟩
    exact Prod.ext (e2.trans e1.symm) (e4.trans e3.symm)
  · exact fun _ _ => Finset.mem_univ _
  · rintro ⟨I, J⟩ - hIJ
    by_contra hne
    obtain ⟨t, ht, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨hI, hJ⟩ := (Finset.mem_filter.1 ht).2
    have hI' : I.card ≤ k := by
      rw [← (show minorsRows t = I from hI), minorsRows]
      exact Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin])
    have hJ' : J.card ≤ k := by
      rw [← (show minorsCols t = J from hJ), minorsCols]
      exact Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin])
    by_cases h : I.card = k ∧ J.card = k
    · refine hIJ ⟨(I.orderEmbOfFin h.1, J.orderEmbOfFin h.2),
        Finset.mem_coe.2 (Finset.mem_univ _), ?_⟩
      dsimp only
      rw [minors_rng_orderEmbOfFin, minors_rng_orderEmbOfFin]
    · exact hne (minors_block_eq_zero hγ _ I J rfl (by omega) F)
  · rintro ⟨α, β⟩ -
    exact (minors_block_eq_perm γ α β F).symm

/-- The column `x ∈ ℝ^k` placed in the rows `r`: `∑_i x_i e_{r_i}`. -/
private def minorsEmb {k : ℕ} (r : Fin k ↪o Fin d) (x : Fin k → ℝ) : Fin d → ℝ :=
  fun a => ∑ i, if r i = a then x i else 0

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

/-- [CDKM]'s form `Q (v¹, …, v^k) = ∑_σ c^σ v^{σ 1}_1 ⋯ v^{σ k}_k` on `(ℝ^k)^k`, multilinear: a sum
of products of one coordinate of each `v^j`. -/
private noncomputable def minorsQ (γ : (Fin k → Fin d × Fin m) → ℝ) (α : Fin k ↪o Fin d)
    (β : Fin k ↪o Fin m) : MultilinearMap ℝ (fun _ : Fin k => Fin k → ℝ) ℝ :=
  ∑ σ : Equiv.Perm (Fin k), minorsCoeff γ α β σ •
    (MultilinearMap.mkPiAlgebra ℝ (Fin k) ℝ).compLinearMap fun j => LinearMap.proj (σ.symm j)

private lemma minors_Q_apply (γ : (Fin k → Fin d × Fin m) → ℝ) (α : Fin k ↪o Fin d)
    (β : Fin k ↪o Fin m) (v : Fin k → Fin k → ℝ) :
    minorsQ γ α β v = ∑ σ : Equiv.Perm (Fin k), minorsCoeff γ α β σ * ∏ i, v (σ i) i := by
  simp only [minorsQ, FunLike.coe_sum, Finset.sum_apply, _root_.smul_apply, smul_eq_mul,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, LinearMap.proj_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Equiv.prod_comp σ (fun j => v j (σ.symm j))]
  simp only [Equiv.symm_apply_apply]

/-- `Q (v) = P_{α,β} (F_v)`. -/
private lemma minors_perm_Fv (γ : (Fin k → Fin d × Fin m) → ℝ) (α : Fin k ↪o Fin d)
    (β : Fin k ↪o Fin m) (v : Fin k → Fin k → ℝ) :
    minorsPerm γ α β (minorsFv α β v) = minorsQ γ α β v := by
  simp only [minorsPerm, minors_Q_apply, minors_Fv_apply, minors_emb_apply]

/-- [CDKM]: `Q (v) = P_{α,β} (F_v) = P (F_v)` (Steps 3 and 4), so `Q (v) = 0` when
`rank F_v < k`. -/
private lemma minors_Q_eq_zero_of_rank_lt {γ : (Fin k → Fin d × Fin m) → ℝ}
    (hγ : ∀ F : Matrix (Fin d) (Fin m) ℝ, F.rank < k → minorsPoly γ F = 0)
    (α : Fin k ↪o Fin d) (β : Fin k ↪o Fin m) {v : Fin k → Fin k → ℝ}
    (hv : (minorsFv α β v).rank < k) : minorsQ γ α β v = 0 := by
  rw [← minors_perm_Fv, ← minors_block_eq_perm,
    minors_block_eq hγ (minors_card_rng α) (minors_card_rng β), minors_restr_Fv]
  exact hγ _ hv

/-- **Step 5.** `P_{α,β} (F) = ĉ_{α,β} · minor F α β`. `Q` vanishes when two columns `v^p = v^q`
coincide, since `F_v` is then a sum of `k − 1` rank-one matrices, so `rank F_v < k`; so `Q` is
alternating, hence `Q = Q (e) det` (Mathlib's `AlternatingMap.eq_smul_basis_det`; [CDKM] first
deduce by polarization that `Q` is antisymmetric, and use that antisymmetric multilinear forms are
multiples of the determinant). And `P_{α,β} (F) = Q (v)` for the columns `v^j` of the block of `F`
with the rows `α` and the columns `β`. -/
private lemma minors_perm_eq_minor {γ : (Fin k → Fin d × Fin m) → ℝ}
    (hγ : ∀ F : Matrix (Fin d) (Fin m) ℝ, F.rank < k → minorsPoly γ F = 0)
    (α : Fin k ↪o Fin d) (β : Fin k ↪o Fin m) :
    ∃ a : ℝ, ∀ F, minorsPerm γ α β F = a * minor F α β := by
  let Q : (Fin k → ℝ) [⋀^Fin k]→ₗ[ℝ] ℝ :=
    { toMultilinearMap := minorsQ γ α β
      map_eq_zero_of_eq' := fun v p q hpq hne => minors_Q_eq_zero_of_rank_lt hγ α β (by
        rw [minors_Fv_eq_sum_erase α β v hpq hne]
        have := Fin.pos p
        refine (minors_rank_sum_vecMulVec_le _ _ _).trans_lt ?_
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        omega) }
  refine ⟨Q (Pi.basisFun ℝ (Fin k)), fun F => ?_⟩
  have h := congrArg (fun φ : (Fin k → ℝ) [⋀^Fin k]→ₗ[ℝ] ℝ => φ (fun j i => F (α i) (β j)))
    (Q.eq_smul_basis_det (Pi.basisFun ℝ (Fin k)))
  simp only [_root_.smul_apply, smul_eq_mul, Module.Basis.det_apply] at h
  have hM : (Pi.basisFun ℝ (Fin k)).toMatrix (fun j i => F (α i) (β j)) = F.submatrix α β := by
    ext i j
    simp [Module.Basis.toMatrix_apply]
  rw [hM] at h
  have hP : minorsPerm γ α β F = minorsQ γ α β (fun j i => F (α i) (β j)) := by
    rw [minors_Q_apply]
    rfl
  rw [hP, minor]
  exact h

/-- **A homogeneous polynomial of degree `k` in the entries that vanishes on the matrices of
rank `< k` is a linear combination of the `k × k` minors.** This is the second half of the proof of
Theorem 6.1 of [CDKM] (Steps 3 to 5 of the module docstring): the terms `S_{I,J}` of `P` with the
rows `I` and the columns `J` vanish unless `|I| = |J| = k` (Step 3); `P = ∑_{α,β} P_{α,β}`,
regrouping by permutations (Step 4); and each `P_{α,β}` is a multiple of the minor with the rows
`α` and the columns `β`, because `Q (v) = P_{α,β} (F_v)` is alternating (Step 5). -/
theorem exists_eq_sum_minor_of_rank_lt (γ : (Fin k → Fin d × Fin m) → ℝ)
    (hγ : ∀ F : Matrix (Fin d) (Fin m) ℝ, F.rank < k → ∑ t, γ t * ∏ i, F (t i).1 (t i).2 = 0) :
    ∃ a : (Fin k ↪o Fin d) → (Fin k ↪o Fin m) → ℝ, ∀ F : Matrix (Fin d) (Fin m) ℝ,
      ∑ t, γ t * ∏ i, F (t i).1 (t i).2 = ∑ r, ∑ c, a r c * minor F r c := by
  choose a ha using fun (α : Fin k ↪o Fin d) (β : Fin k ↪o Fin m) => minors_perm_eq_minor hγ α β
  refine ⟨a, fun F => ?_⟩
  change minorsPoly γ F = _
  rw [minors_poly_eq_sum_perm hγ F]
  exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ha α β F

end Homogeneous

/-! ### Without continuity: the multi-affine route -/

section MultiAffine

/-- Affinity along the rank-one lines `t ↦ A + t (u ⊗ v)`. -/
private def MinorsRA {d m : ℕ} (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ A (u : Fin d → ℝ) (v : Fin m → ℝ) (t : ℝ),
    f (A + t • vecMulVec u v) = f A + t * (f (A + vecMulVec u v) - f A)

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
private def minorsSetMono (S : Finset (Fin d × Fin m)) (F : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  ∏ s ∈ S, F s.1 s.2

/-- Step 2a for `f`: `f` is affine in each entry (`e_i ⊗ e_j` has rank one), so
`f (F) = ∑_S c_S F^S`. -/
private lemma minors_exists_mono {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : MinorsRA f) :
    ∃ c : Finset (Fin d × Fin m) → ℝ, ∀ F, f F = ∑ S, c S * minorsSetMono S F := by
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
  ∑ S with S.card = k, c S * minorsSetMono S F

private lemma minors_setMono_smul (S : Finset (Fin d × Fin m)) (t : ℝ)
    (F : Matrix (Fin d) (Fin m) ℝ) : minorsSetMono S (t • F) = t ^ S.card * minorsSetMono S F := by
  simp only [minorsSetMono, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const]

/-- **Step 2b.** If `F = ∑_{l ∈ L} a_l ⊗ b_l` with `|L| < k`, then `P_k (F) = 0`:
`s ↦ f (∑_l s_l a_l ⊗ b_l)` is affine in each `s_l` (rank-one lines), hence by Step 2a a
polynomial with no repeated variable, so `t ↦ f (t F)` is a polynomial of degree at most `|L|`;
comparing its coefficients with those of `f (t F) = ∑_j t^j P_j (F)` gives `P_k (F) = 0`. -/
private lemma minors_hom_eq_zero {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : MinorsRA f)
    {c : Finset (Fin d × Fin m) → ℝ} (hc : ∀ F, f F = ∑ S, c S * minorsSetMono S F)
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
  have h1 : ∀ t : ℝ, f (t • F) = ∑ S, c S * minorsSetMono S F * t ^ S.card := by
    intro t
    rw [hc]
    exact Finset.sum_congr rfl fun S _ => by rw [minors_setMono_smul]; ring
  have h2 : ∀ t : ℝ, f (t • F) = ∑ T, c' T * t ^ T.card := by
    intro t
    have := hc' (fun _ => t)
    simp only [Finset.prod_const] at this
    rw [← this, hF, Finset.smul_sum]
    congr 1
    exact (Finset.sum_coe_sort L fun l => t • vecMulVec (a l) (b l)).symm
  -- compare the coefficients of `t^k`
  set p : Polynomial ℝ := ∑ S, Polynomial.C (c S * minorsSetMono S F) * Polynomial.X ^ S.card -
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

/-- **Step 2b**: `P_k (F) = 0` when `rank F < k`, since `F` is then a sum of fewer than `k`
rank-one matrices. -/
private lemma minors_hom_eq_zero_of_rank_lt {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : MinorsRA f)
    {c : Finset (Fin d × Fin m) → ℝ} (hc : ∀ F, f F = ∑ S, c S * minorsSetMono S F) {k : ℕ}
    {F : Matrix (Fin d) (Fin m) ℝ} (hF : F.rank < k) : minorsHom c k F = 0 := by
  obtain ⟨r, a, b, hr, h⟩ := exists_sum_vecMulVec_of_rank F
  rw [h]
  exact minors_hom_eq_zero hf hc Finset.univ a b (by
    rw [Finset.card_univ, Fintype.card_fin]; omega)

/-- **The degree bound.** `f = ∑_{k ≤ min (d, m)} P_k`: `f = ∑_k P_k` (Step 2a), and `P_k = 0`
for every `k > min (d, m)` by Step 2b, since `rank F ≤ min (d, m)`. -/
private lemma minors_eq_sum_hom {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : MinorsRA f)
    {c : Finset (Fin d × Fin m) → ℝ} (hc : ∀ F, f F = ∑ S, c S * minorsSetMono S F)
    (F : Matrix (Fin d) (Fin m) ℝ) :
    f F = ∑ k ∈ Finset.range (min d m + 1), minorsHom c k F := by
  have h1 : ∑ S, c S * minorsSetMono S F = ∑ k ∈ Finset.range (d * m + 1), minorsHom c k F := by
    refine (Finset.sum_fiberwise_of_maps_to (g := Finset.card) (fun S _ => ?_) _).symm
    have := Finset.card_le_univ S
    simp only [Fintype.card_prod, Fintype.card_fin] at this
    exact Finset.mem_range.2 (Nat.lt_succ_of_le this)
  rw [hc, h1]
  refine (Finset.sum_subset (Finset.range_subset_range.2 (Nat.succ_le_succ ?_))
    fun k _ hk => ?_).symm
  · rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · exact (min_le_left d m).trans (Nat.le_mul_of_pos_right d h)
  · rw [Finset.mem_range, not_lt] at hk
    refine minors_hom_eq_zero_of_rank_lt hf hc ?_
    have := le_min (rank_le_height F) (rank_le_width F)
    omega

/-- The part `P_k` of Step 2a, written with tuples of entries: `P_k (F) = ∑_t γ_t F_{t₁} ⋯ F_{t_k}`
(each set of `k` entries, in one order). -/
private lemma minors_hom_eq_tuple (c : Finset (Fin d × Fin m) → ℝ) (k : ℕ) :
    ∃ γ : (Fin k → Fin d × Fin m) → ℝ, ∀ F : Matrix (Fin d) (Fin m) ℝ,
      minorsHom c k F = ∑ t, γ t * ∏ i, F (t i).1 (t i).2 := by
  let e : {S : Finset (Fin d × Fin m) // S.card = k} → Fin k → Fin d × Fin m :=
    fun S i => (S.1.equivFin.symm (finCongr S.2.symm i) : Fin d × Fin m)
  have he : ∀ (S : {S : Finset (Fin d × Fin m) // S.card = k}) (F : Matrix (Fin d) (Fin m) ℝ),
      minorsSetMono S.1 F = ∏ i, F (e S i).1 (e S i).2 := by
    intro S F
    rw [minorsSetMono, ← Finset.prod_coe_sort, ← Equiv.prod_comp S.1.equivFin.symm,
      ← Equiv.prod_comp (finCongr S.2.symm)]
  refine ⟨fun t => ∑ S with e S = t, c S.1, fun F => ?_⟩
  rw [minorsHom, Finset.sum_subtype (p := fun S : Finset (Fin d × Fin m) => S.card = k) _
    (fun S => by simp), ← Finset.sum_fiberwise _ e]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [he, (Finset.mem_filter.1 hS).2]

end MultiAffine

/-- **A rank-one affine function is an affine combination of minors**, without continuity: for a
rank-one affine `f : ℝ^{d×m} → ℝ` there are coefficients `a k r c` with
`f (A) = ∑_{k ≤ min d m} ∑_{r, c} a k r c · minor A r c` for every `A` (the `0 × 0` minor is the
constant `1`). With continuity this is the implication (iii) ⇒ (iv) of Dacorogna 2008,
Theorem 5.20 (the statement cited), proved by the argument of Conti–Dolzmann–Kirchheim–Müller
2006, Theorem 6.1, in `RankOneAffine.exists_eq_sum_minor_of_continuous`. **This proof is not
theirs**: in place of their first half, which uses continuity (distributional derivatives,
Proposition 6.2, Taylor's formula), it uses an elementary multi-affine argument of our own,
which is simpler and needs no continuity: `f` is affine in each entry, hence
`f = ∑_S c_S ∏_{s ∈ S} F_s` over the sets of entries (Step 2a), and the part `P_k` of degree `k`
vanishes on the matrices of rank `< k` because `t ↦ f (t F)` is then a polynomial of degree `< k`
(Step 2b). The second half, `exists_eq_sum_minor_of_rank_lt`, is theirs. -/
theorem RankOneAffine.exists_eq_sum_minor {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : RankOneAffine f) :
    ∃ a : (k : ℕ) → (Fin k ↪o Fin d) → (Fin k ↪o Fin m) → ℝ,
      ∀ A, f A = ∑ k ∈ Finset.range (min d m + 1), ∑ r, ∑ c, a k r c * minor A r c := by
  have hRA : MinorsRA f := hf.add_smul_vecMulVec
  obtain ⟨c, hc⟩ := minors_exists_mono hRA
  choose γ hγ using minors_hom_eq_tuple c
  choose a ha using fun k => exists_eq_sum_minor_of_rank_lt (γ k) (fun F hF => by
    rw [← hγ]; exact minors_hom_eq_zero_of_rank_lt hRA hc hF)
  refine ⟨a, fun A => ?_⟩
  rw [minors_eq_sum_hom hRA hc A]
  exact Finset.sum_congr rfl fun k _ => by rw [hγ, ha]

end CalculusOfVariations
