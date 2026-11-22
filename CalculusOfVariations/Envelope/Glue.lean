/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Envelope.Cube
public import CalculusOfVariations.Envelope.Tangent
public import CalculusOfVariations.Lipschitz.PiecewiseAffine
public import CalculusOfVariations.Quasiconvex.Laminate
public import Mathlib.Data.EReal.Inv

/-!
# The infimum formula and piecewise affine test maps

For a continuous `f`, with `cubeInf f` the infimum formula on the unit cube `Q` (in `EReal`):

* `cubeInf_le_sum_of_piecewiseAffine`: for a Lipschitz `ψ` vanishing off `Q` and agreeing with the
  affine map `L i` on the open piece `P i` of a finite partition of `Q` up to a null set,
  `cubeInf f (F) ≤ ∑ i |P i| cubeInf f (F + ∇ (L i))`, that is,
  `⨍_Q cubeInf f (F + ∇ψ) ≥ cubeInf f (F)`; the value `−∞` is allowed. This is (4.28) of
  S. Müller, *Variational models for microstructure and phase transitions*, lecture notes, MPI MiS
  Leipzig, 1998, §4.8, proved by his argument: an almost minimiser is inserted in each piece and the
  glued map `ψ + ∑ φ_i` is tested. Müller uses that the infimum formula does not depend on the
  domain; here that step is done with the covering inline: finitely many disjoint small closed cubes
  inside `P i` fill it up to `η` (`cv_exists_finite_cover`), and rescaled test maps of energy
  `< b i` for `cubeInf f (F + ∇ (L i))`, for given reals `b i > cubeInf f (F + ∇ (L i))`, are
  inserted in them (`cv_glue`, whose cut-off changes nothing since `ψ` is affine on the cubes, in
  the limit `δ → 0` of its inner cubes). This gives `cubeInf f F ≤ ∑ i |P i| b i + C η`; then
  `η → 0` and `b i ↓ cubeInf f (F + ∇ (L i))`, or, when a piece of positive measure has
  `cubeInf f (F + ∇ (L i)) = −∞`, `b i → −∞` there, which gives `cubeInf f F = −∞` (Müller's
  "obvious modification");
* `cubeLaminate_piecewiseAffineOn`: the laminate `v_k` of `Quasiconvex.Laminate` is piecewise
  affine on `Q`. On the slab `{c < k x_j < c + 1}` of `Q`, `v_k = h a` with `h` the minimum of the
  affine functions `(1 − λ) (x_j − c / k)`, `λ ((c + 1) / k − x_j)` (the sawtooth) and `x_i`,
  `1 − x_i` (the sup-norm distance to the complement of `Q`); the minimum of finitely many affine
  functions is affine on each of the open sets where one of them is strictly smallest, and the rest
  lies in the finitely many hyperplanes where two distinct ones agree, or `k x_j ∈ ℤ`, which are
  null;
* `cubeInf_le_two_point`: the two-point inequality
  `cubeInf f (F) ≤ λ cubeInf f (F + (1 − λ) a ⊗ e_j) + (1 − λ) cubeInf f (F − λ a ⊗ e_j)`
  (Müller 1998, §4.8, with the laminate argument of Lemma 4.3). For real bounds `y_A`, `y_B` of
  the two values on the right, let `g = y_A` at `(1 − λ) a ⊗ e_j`, `g = y_B` at `−λ a ⊗ e_j` and
  `g = M` elsewhere, `M` a bound of `f (F + ·)` on the gradients of `v_k`: (4.28) for `v_k` gives
  `cubeInf f F ≤ ∑ i |P i| g (∇ (L i)) = ∫_Q g (∇v_k)`, which differs from
  `∫_Q g (∇u_k) = λ y_A + (1 − λ) y_B` by at most `2 sup |g| · |{∇v_k ≠ ∇u_k}| → 0`. The values
  `−∞` are reached by `y_A → −∞` or `y_B → −∞`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

namespace CalculusOfVariations

variable {d m : ℕ}

/-! ### Maps agreeing with an affine map on an open set -/

/-- A map agreeing with the affine map `L` on an open set has the derivative `L.linear` there. -/
theorem glue_hasFDerivAt {U : Set (Fin m → ℝ)} (hU : IsOpen U) {ψ : (Fin m → ℝ) → Fin d → ℝ}
    {L : (Fin m → ℝ) →ᵃ[ℝ] (Fin d → ℝ)} (hψ : ∀ y ∈ U, ψ y = L y) {x : Fin m → ℝ} (hx : x ∈ U) :
    HasFDerivAt ψ (LinearMap.toContinuousLinearMap L.linear) x := by
  have hL : HasFDerivAt (fun y => LinearMap.toContinuousLinearMap L.linear y + L 0)
      (LinearMap.toContinuousLinearMap L.linear) x :=
    (LinearMap.toContinuousLinearMap L.linear).hasFDerivAt.add_const (L 0)
  refine hL.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy => ?_)
  rw [hψ y hy, LinearMap.coe_toContinuousLinearMap']
  exact congrFun (AffineMap.decomp L) y

/-- The gradient of a map agreeing with the affine map `L` on an open set is the matrix of
`L.linear` there. -/
theorem glue_grad_eq {U : Set (Fin m → ℝ)} (hU : IsOpen U) {ψ : (Fin m → ℝ) → Fin d → ℝ}
    {L : (Fin m → ℝ) →ᵃ[ℝ] (Fin d → ℝ)} (hψ : ∀ y ∈ U, ψ y = L y) {x : Fin m → ℝ} (hx : x ∈ U) :
    grad ψ x = LinearMap.toMatrix' L.linear := by
  have h := glue_hasFDerivAt hU hψ hx
  ext i k
  rw [LinearMap.toMatrix'_apply]
  change fderiv ℝ (fun y => ψ y i) x (Pi.single k 1) = _
  have h2 : HasFDerivAt (fun y => ψ y i)
      ((ContinuousLinearMap.proj i).comp (LinearMap.toContinuousLinearMap L.linear)) x :=
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin d => ℝ) i (ψ x)).comp x h
  rw [h2.fderiv]
  rfl

/-- A map agreeing with the affine map `L` on an open set coincides there with its tangent maps. -/
theorem glue_tangentMap_eq {U : Set (Fin m → ℝ)} (hU : IsOpen U) {ψ : (Fin m → ℝ) → Fin d → ℝ}
    {L : (Fin m → ℝ) →ᵃ[ℝ] (Fin d → ℝ)} (hψ : ∀ y ∈ U, ψ y = L y) {x : Fin m → ℝ} (hx : x ∈ U)
    (z : Fin m → ℝ) : tangentMap ψ x z = L z := by
  rw [tangentMap, (glue_hasFDerivAt hU hψ hx).fderiv, hψ x hx, LinearMap.coe_toContinuousLinearMap']
  have := L.linear_apply_vsub z x
  rw [vsub_eq_sub, vsub_eq_sub] at this
  rw [this]
  abel

/-! ### Müller's (4.28) -/

/-- The pieces of a partition of the unit cube up to a null set have total measure `1`. -/
private theorem glue_sum_volume {n : ℕ} {P : Fin n → Set (Fin m → ℝ)} (hPo : ∀ i, IsOpen (P i))
    (hPd : Pairwise (Function.onFun Disjoint P)) (hPQ : ∀ i, P i ⊆ unitCube m)
    (hcov : volume (unitCube m \ ⋃ i, P i) = 0) : ∑ i, (volume (P i)).toReal = 1 := by
  have hQfin : volume (unitCube m) ≠ ⊤ := by rw [cv_volume_unitCube]; exact ENNReal.one_ne_top
  have h1 := measureReal_sdiff (iUnion_subset hPQ)
    (MeasurableSet.iUnion fun i => (hPo i).measurableSet) hQfin
  have h2 := measureReal_iUnion_fintype hPd (fun i => (hPo i).measurableSet)
    (fun i => ne_top_of_le_ne_top hQfin (measure_mono (hPQ i)))
  simp only [measureReal_def, hcov, cv_volume_unitCube, ENNReal.toReal_zero,
    ENNReal.toReal_one] at h1 h2
  linarith

/-- **Gluing into cubes on which `ψ` is affine.** For finitely many disjoint closed cubes in the
unit cube, each inside an open set on which `ψ` agrees with an affine map, and test maps `φ p`:
inserting the rescaled `φ p` in the cubes gives
`cubeInf f F ≤ ∑_p |C_p| ∫_Q f (F + ∇ψ (x_p) + ∇φ_p) + M (1 − ∑_p |C_p|)`. This is `cv_glue` (in
which the cut-off changes nothing, as `ψ` equals its tangent maps on the cubes) in the limit
`δ → 0`. -/
private theorem glue_le_cover {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (F : Matrix (Fin d) (Fin m) ℝ) {K : NNReal} {ψ : (Fin m → ℝ) → Fin d → ℝ}
    (hK : LipschitzWith K ψ) (hψ0 : ∀ x ∉ unitCube m, ψ x = 0) {M : ℝ}
    (hM : ∀ X : Matrix (Fin d) (Fin m) ℝ, (∀ i k, |X i k| ≤ 3 * K + 1) → |f (F + X)| ≤ M)
    (t : Finset ((Fin m → ℝ) × ℝ))
    (ht : ∀ p ∈ t, 0 < p.2 ∧ closedBall p.1 p.2 ⊆ unitCube m ∧ ∃ U : Set (Fin m → ℝ), IsOpen U ∧
      closedBall p.1 p.2 ⊆ U ∧ ∃ L : (Fin m → ℝ) →ᵃ[ℝ] (Fin d → ℝ), ∀ y ∈ U, ψ y = L y)
    (hdisj : (t : Set ((Fin m → ℝ) × ℝ)).PairwiseDisjoint fun p => closedBall p.1 p.2)
    (φ : (Fin m → ℝ) × ℝ → (Fin m → ℝ) → Fin d → ℝ) (hφ : ∀ p ∈ t, IsCubeTestMap (φ p)) :
    cubeInf f F ≤ ((∑ p ∈ t, (2 * p.2) ^ m *
      (∫ y in unitCube m, f (F + grad ψ p.1 + grad (φ p) y)) +
        M * (1 - ∑ p ∈ t, (2 * p.2) ^ m) : ℝ) : EReal) := by
  classical
  set E : (Fin m → ℝ) × ℝ → ℝ := fun p => ∫ y in unitCube m, f (F + grad ψ p.1 + grad (φ p) y)
    with hE
  set g : ℝ → ℝ := fun δ => ∑ p ∈ t, (2 * ((1 - δ) * p.2)) ^ m * E p +
    M * (1 - ∑ p ∈ t, (2 * ((1 - δ) * p.2)) ^ m) with hg
  have hg0 : g 0 = ∑ p ∈ t, (2 * p.2) ^ m * E p + M * (1 - ∑ p ∈ t, (2 * p.2) ^ m) := by
    simp only [hg, sub_zero, one_mul]
  rw [← hg0]
  have hgc : Continuous g := by
    simp only [hg]
    fun_prop
  have htend : Tendsto (fun δ => (g δ : EReal)) (𝓝[>] 0) (𝓝 (g 0 : EReal)) :=
    ((continuous_coe_real_ereal.comp hgc).tendsto 0).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
  have ht' : ∀ p ∈ t, 0 < p.2 ∧ closedBall p.1 p.2 ⊆ unitCube m ∧ DifferentiableAt ℝ ψ p.1 ∧
      ∀ z ∈ closedBall p.1 p.2, ‖ψ z - tangentMap ψ p.1 z‖ ≤ δ * p.2 := by
    intro p hp
    obtain ⟨hr, hQ, U, hU, hBU, L, hL⟩ := ht p hp
    have hx : p.1 ∈ U := hBU (mem_closedBall_self hr.le)
    refine ⟨hr, hQ, (glue_hasFDerivAt hU hL hx).differentiableAt, fun z hz => ?_⟩
    rw [glue_tangentMap_eq hU hL hx, hL z (hBU hz), sub_self, norm_zero]
    exact mul_nonneg hδ.1.le hr.le
  obtain ⟨Φ, hΦ, hle⟩ := cv_glue hf F hK hψ0 hδ.1 hδ.2 t ht' hdisj φ hφ hM
  refine (iInf₂_le Φ hΦ : cubeInf f F ≤ _).trans (EReal.coe_le_coe_iff.2 (hle.trans (le_of_eq ?_)))
  -- the measure of the rest
  have hρ : ∀ p ∈ t, (1 - δ) * p.2 ≤ p.2 := fun p hp => by nlinarith [(ht p hp).1, hδ.1]
  have hUQ : (⋃ p ∈ t, ball p.1 ((1 - δ) * p.2)) ⊆ unitCube m := by
    intro z hz
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hz
    exact (ht p hp).2.1 (ball_subset_closedBall (ball_subset_ball (hρ p hp) hzp))
  have hUm : MeasurableSet (⋃ p ∈ t, ball p.1 ((1 - δ) * p.2)) :=
    Finset.measurableSet_biUnion _ fun _ _ => measurableSet_ball
  have hQ1 : volume.real (unitCube m) = 1 := by
    rw [measureReal_def, cv_volume_unitCube, ENNReal.toReal_one]
  rw [measureReal_sdiff hUQ hUm (by rw [cv_volume_unitCube]; exact ENNReal.one_ne_top),
    measureReal_biUnion_finset (fun p hp q hq hpq => (hdisj hp hq hpq).mono
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (hρ p hp)))
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (hρ q hq))))
      (fun _ _ => measurableSet_ball) (fun _ _ => measure_ball_lt_top.ne), hQ1]
  simp only [hg]
  congr 3
  exact Finset.sum_congr rfl fun p hp =>
    cv_measureReal_ball _ (mul_pos (by linarith [hδ.2]) (ht p hp).1)

/-- (4.28) with real upper bounds `b i > cubeInf f (F + ∇ (L i))`: almost minimisers with energy
`< b i` inserted in finitely many disjoint small cubes filling the piece `P i` up to `η` give
`cubeInf f F ≤ ∑ i |P i| b i + C η`. -/
private theorem glue_le_of_lt {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (F : Matrix (Fin d) (Fin m) ℝ) {n : ℕ} (P : Fin n → Set (Fin m → ℝ))
    (L : Fin n → (Fin m → ℝ) →ᵃ[ℝ] (Fin d → ℝ)) (hPo : ∀ i, IsOpen (P i))
    (hPd : Pairwise (Function.onFun Disjoint P)) (hPQ : ∀ i, P i ⊆ unitCube m)
    (hcov : volume (unitCube m \ ⋃ i, P i) = 0) {ψ : (Fin m → ℝ) → Fin d → ℝ}
    {K : NNReal} (hK : LipschitzWith K ψ) (hψ0 : ∀ x ∉ unitCube m, ψ x = 0)
    (hψL : ∀ i, ∀ x ∈ P i, ψ x = L i x) (b : Fin n → ℝ)
    (hb : ∀ i, cubeInf f (F + LinearMap.toMatrix' (L i).linear) < b i) :
    cubeInf f F ≤ ((∑ i, (volume (P i)).toReal * b i : ℝ) : EReal) := by
  classical
  set G : Fin n → Matrix (Fin d) (Fin m) ℝ := fun i => LinearMap.toMatrix' (L i).linear with hG
  -- almost minimisers
  have hchoice : ∀ i, ∃ φ, IsCubeTestMap φ ∧ ∫ y in unitCube m, f (F + G i + grad φ y) < b i := by
    intro i
    have h := hb i
    unfold cubeInf at h
    obtain ⟨φ, hφ⟩ := iInf_lt_iff.1 h
    obtain ⟨hadm, hφ'⟩ := iInf_lt_iff.1 hφ
    exact ⟨φ, hadm, EReal.coe_lt_coe_iff.1 hφ'⟩
  choose φ hφadm hφlt using hchoice
  obtain ⟨M, hM0, hM⟩ := cv_bdd hf F (3 * K + 1)
  have hQfin : volume (unitCube m) ≠ ⊤ := by rw [cv_volume_unitCube]; exact ENNReal.one_ne_top
  have hPfin : ∀ i, volume (P i) ≠ ⊤ := fun i => ne_top_of_le_ne_top hQfin (measure_mono (hPQ i))
  have hw1 := glue_sum_volume hPo hPd hPQ hcov
  refine cv_ereal_le_of_eps (C := n * M + ∑ i, |b i|) (by positivity) fun η hη0 _ => ?_
  -- the covers of the pieces
  have hcover : ∀ i, ∃ t : Finset ((Fin m → ℝ) × ℝ),
      (∀ p ∈ t, 0 < p.2 ∧ closedBall p.1 p.2 ⊆ P i) ∧
      (t : Set ((Fin m → ℝ) × ℝ)).PairwiseDisjoint (fun p => closedBall p.1 p.2) ∧
      volume (P i \ ⋃ p ∈ t, closedBall p.1 p.2) < ENNReal.ofReal η := by
    intro i
    refine cv_exists_finite_cover (hPfin i) (hPo i).measurableSet
      (fun x r => closedBall x r ⊆ P i) (Filter.Eventually.of_forall fun x hx δ hδ => ?_)
      (ENNReal.ofReal_pos.2 hη0)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hPo i) x hx
    refine ⟨min (δ / 2) (ε / 2), ⟨lt_min (by linarith) (by linarith),
      (min_le_left _ _).trans_lt (by linarith)⟩, ?_⟩
    exact (closedBall_subset_ball ((min_le_right _ _).trans_lt (by linarith))).trans hball
  choose t htP htd htv using hcover
  have hidx : ∀ i i' p, p ∈ t i → p ∈ t i' → i = i' := by
    intro i i' p hp hp'
    by_contra hne
    have hx := mem_closedBall_self (x := p.1) (htP i p hp).1.le
    exact Set.disjoint_left.1 (hPd hne) ((htP i p hp).2 hx) ((htP i' p hp').2 hx)
  set T := Finset.univ.biUnion t with hT
  have htdisj : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint t := by
    intro i _ i' _ hne
    exact Finset.disjoint_left.2 fun p hp hp' => hne (hidx i i' p hp hp')
  have hmemT : ∀ p ∈ T, ∃ i, p ∈ t i := fun p hp => by
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hp
    exact ⟨i, hi⟩
  set φ' : (Fin m → ℝ) × ℝ → (Fin m → ℝ) → Fin d → ℝ := fun p =>
    if h : ∃ i, p ∈ t i then φ h.choose else fun _ => 0 with hφ'
  have hφ'eq : ∀ i, ∀ p ∈ t i, φ' p = φ i := by
    intro i p hp
    have h : ∃ i, p ∈ t i := ⟨i, hp⟩
    simp only [hφ', h, dite_true]
    rw [hidx _ _ _ h.choose_spec hp]
  have hTdisj : (T : Set ((Fin m → ℝ) × ℝ)).PairwiseDisjoint fun p => closedBall p.1 p.2 := by
    intro p hp q hq hpq
    obtain ⟨i, hi⟩ := hmemT p hp
    obtain ⟨i', hi'⟩ := hmemT q hq
    by_cases hii : i = i'
    · subst hii
      exact htd i hi hi' hpq
    · exact (hPd hii).mono (htP i p hi).2 (htP i' q hi').2
  have hglue := glue_le_cover hf F hK hψ0 hM T (fun p hp => by
      obtain ⟨i, hi⟩ := hmemT p hp
      exact ⟨(htP i p hi).1, (htP i p hi).2.trans (hPQ i), P i, hPo i, (htP i p hi).2, L i,
        hψL i⟩)
    hTdisj φ' (fun p hp => by
      obtain ⟨i, hi⟩ := hmemT p hp
      rw [hφ'eq i p hi]
      exact hφadm i)
  refine hglue.trans (EReal.coe_le_coe_iff.2 ?_)
  -- the arithmetic
  set e : Fin n → ℝ := fun i => ∫ y in unitCube m, f (F + G i + grad (φ i) y) with he
  set S : Fin n → ℝ := fun i => ∑ p ∈ t i, (2 * p.2) ^ m with hS
  have hE : ∀ i, ∀ p ∈ t i,
      (2 * p.2) ^ m * (∫ y in unitCube m, f (F + grad ψ p.1 + grad (φ' p) y)) =
        (2 * p.2) ^ m * e i := by
    intro i p hp
    rw [hφ'eq i p hp, glue_grad_eq (hPo i) (hψL i)
      ((htP i p hp).2 (mem_closedBall_self (htP i p hp).1.le))]
  rw [Finset.sum_biUnion htdisj, Finset.sum_biUnion htdisj,
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p hp => hE i p hp]
  simp_rw [← Finset.sum_mul]
  change ∑ i, S i * e i + M * (1 - ∑ i, S i) ≤ _
  have hsub : ∀ i, (⋃ p ∈ t i, closedBall p.1 p.2) ⊆ P i := fun i z hz => by
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hz
    exact (htP i p hp).2 hzp
  have hSeq : ∀ i, S i = volume.real (⋃ p ∈ t i, closedBall p.1 p.2) := fun i => by
    rw [measureReal_biUnion_finset (htd i) (fun _ _ => measurableSet_closedBall)
      (fun _ _ => measure_closedBall_lt_top.ne)]
    exact Finset.sum_congr rfl fun p hp => (cv_measureReal_closedBall _ (htP i p hp).1.le).symm
  have hS0 : ∀ i, 0 ≤ S i := fun i =>
    Finset.sum_nonneg fun p hp => pow_nonneg (by linarith [(htP i p hp).1]) m
  have hSle : ∀ i, S i ≤ (volume (P i)).toReal := fun i => by
    rw [hSeq i]
    exact measureReal_mono (hsub i) (hPfin i)
  have hSge : ∀ i, (volume (P i)).toReal - η < S i := fun i => by
    have h1 := measureReal_sdiff (hsub i)
      (Finset.measurableSet_biUnion _ fun _ _ => measurableSet_closedBall) (hPfin i)
    have h2 := ENNReal.toReal_lt_of_lt_ofReal (htv i)
    rw [hSeq i]
    simp only [measureReal_def] at h1 h2 ⊢
    linarith
  have h1 : ∑ i, S i * e i ≤ ∑ i, ((volume (P i)).toReal * b i + η * |b i|) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have ha := mul_le_mul_of_nonneg_left (hφlt i).le (hS0 i)
    have hb1 := mul_nonneg (sub_nonneg.2 (hSle i))
      (by linarith [neg_abs_le (b i)] : 0 ≤ b i + |b i|)
    have hb2 := mul_nonneg (by linarith [hSge i] : 0 ≤ η + (S i - (volume (P i)).toReal))
      (abs_nonneg (b i))
    change S i * e i ≤ _
    nlinarith
  have h2 : M * (1 - ∑ i, S i) ≤ M * (n * η) := by
    refine mul_le_mul_of_nonneg_left ?_ hM0
    rw [← hw1, ← Finset.sum_sub_distrib]
    calc ∑ i, ((volume (P i)).toReal - S i) ≤ ∑ _i : Fin n, η :=
          Finset.sum_le_sum fun i _ => by linarith [hSge i]
      _ = n * η := by simp
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
  nlinarith

/-- **The quasiconvexity inequality of the infimum formula for piecewise affine test maps**
(Müller 1998, (4.28)): for a Lipschitz `ψ` vanishing off the unit cube and agreeing with the affine
map `L i` on the open set `P i`, where the `P i ⊆ Q` are pairwise disjoint and cover `Q` up to a
null set, `cubeInf f (F) ≤ ∑ i |P i| cubeInf f (F + ∇ (L i))` (in `EReal`). -/
theorem cubeInf_le_sum_of_piecewiseAffine {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (F : Matrix (Fin d) (Fin m) ℝ) {n : ℕ} (P : Fin n → Set (Fin m → ℝ))
    (L : Fin n → (Fin m → ℝ) →ᵃ[ℝ] (Fin d → ℝ)) (hPo : ∀ i, IsOpen (P i))
    (hPd : Pairwise (Function.onFun Disjoint P)) (hPQ : ∀ i, P i ⊆ unitCube m)
    (hcov : volume (unitCube m \ ⋃ i, P i) = 0) {ψ : (Fin m → ℝ) → Fin d → ℝ}
    (hψ : ∃ K, LipschitzWith K ψ) (hψ0 : ∀ x ∉ unitCube m, ψ x = 0)
    (hψL : ∀ i, ∀ x ∈ P i, ψ x = L i x) :
    cubeInf f F ≤
      ∑ i, ((volume (P i)).toReal : EReal) * cubeInf f (F + LinearMap.toMatrix' (L i).linear) := by
  classical
  obtain ⟨K, hK⟩ := hψ
  set G : Fin n → Matrix (Fin d) (Fin m) ℝ := fun i => LinearMap.toMatrix' (L i).linear with hG
  set c : Fin n → EReal := fun i => cubeInf f (F + G i) with hc
  set w : Fin n → ℝ := fun i => (volume (P i)).toReal with hw
  have hA := glue_le_of_lt hf F P L hPo hPd hPQ hcov hK hψ0 hψL
  have hcf : ∀ i, c i ≤ (f (F + G i) : EReal) := fun i => cubeInf_le _
  have hw1 : ∑ i, w i = 1 := glue_sum_volume hPo hPd hPQ hcov
  change cubeInf f F ≤ ∑ i, (w i : EReal) * c i
  by_cases hbot : ∃ i0, 0 < w i0 ∧ c i0 = ⊥
  · -- a piece of positive measure with `cubeInf = −∞`: then `cubeInf f F = −∞`
    obtain ⟨i0, hw0, hc0⟩ := hbot
    suffices h : cubeInf f F = ⊥ by rw [h]; exact bot_le
    rw [EReal.eq_bot_iff_forall_lt]
    intro y
    set R := ∑ i ∈ Finset.univ.erase i0, w i * (f (F + G i) + 1) with hR
    set N := (y - 1 - R) / w i0 with hN
    have hlt : ∀ i, c i < ((if i = i0 then N else f (F + G i) + 1 : ℝ) : EReal) := by
      intro i
      by_cases hi : i = i0
      · rw [ite_eq_left hi, hi, hc0]
        exact EReal.bot_lt_coe _
      · rw [ite_eq_right hi]
        exact (hcf i).trans_lt (EReal.coe_lt_coe_iff.2 (by linarith))
    refine (hA _ hlt).trans_lt (EReal.coe_lt_coe_iff.2 ?_)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), ite_eq_left rfl,
      Finset.sum_congr rfl fun i hi => by rw [ite_eq_right (Finset.ne_of_mem_erase hi)]]
    change w i0 * N + R < y
    rw [hN, mul_div_cancel₀ _ hw0.ne']
    linarith
  · -- otherwise all the terms are real
    push Not at hbot
    set b : Fin n → ℝ := fun i => if 0 < w i then (c i).toReal else f (F + G i) with hb
    have hterm : ∀ i, (w i : EReal) * c i = ((w i * b i : ℝ) : EReal) := by
      intro i
      by_cases hi : 0 < w i
      · have hne : c i ≠ ⊥ := hbot i hi
        have hne' : c i ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (hcf i)
        rw [hb]
        simp only [ite_eq_left hi]
        rw [EReal.coe_mul, EReal.coe_toReal hne' hne]
      · have h0 : w i = 0 := le_antisymm (not_lt.1 hi) ENNReal.toReal_nonneg
        rw [h0, zero_mul, EReal.coe_zero, zero_mul]
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    have hsum : ∑ i, ((w i * b i : ℝ) : EReal) = ((∑ i, w i * b i : ℝ) : EReal) := by
      induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, EReal.coe_add]
    rw [hsum]
    refine cv_ereal_le_of_eps zero_le_one fun ε hε0 _ => ?_
    have hlt : ∀ i, c i < ((b i + ε : ℝ) : EReal) := by
      intro i
      by_cases hi : 0 < w i
      · have hne : c i ≠ ⊥ := hbot i hi
        have hne' : c i ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (hcf i)
        rw [hb]
        simp only [ite_eq_left hi]
        calc c i = ((c i).toReal : EReal) := (EReal.coe_toReal hne' hne).symm
          _ < _ := EReal.coe_lt_coe_iff.2 (by linarith)
      · rw [hb]
        simp only [ite_eq_right hi]
        exact (hcf i).trans_lt (EReal.coe_lt_coe_iff.2 (by linarith))
    refine (hA _ hlt).trans (le_of_eq ?_)
    congr 1
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    change _ + (∑ i, w i) * ε = _
    rw [hw1]

/-! ### The laminates are piecewise affine -/

/-- `PiecewiseAffineOn` with the pieces indexed by any finite type. -/
private theorem glue_pa_of_fintype {ι : Type*} [Fintype ι] {U : Set (Fin m → ℝ)}
    {φ : (Fin m → ℝ) → Fin d → ℝ} (P : ι → Set (Fin m → ℝ))
    (L : ι → (Fin m → ℝ) →ᵃ[ℝ] (Fin d → ℝ)) (hPo : ∀ i, IsOpen (P i))
    (hPd : Pairwise (Function.onFun Disjoint P)) (hPU : ∀ i, P i ⊆ U)
    (hcov : volume (U \ ⋃ i, P i) = 0) (hL : ∀ i, ∀ x ∈ P i, φ x = L i x) :
    PiecewiseAffineOn U φ := by
  set e := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, P ∘ e, L ∘ e, fun i => hPo _, fun i i' hne => hPd (e.injective.ne hne),
    fun i => hPU _, ?_, fun i => hL _⟩
  show volume (U \ ⋃ i, P (e i)) = 0
  rw [e.surjective.iUnion_comp P]
  exact hcov

/-- A map piecewise affine on each of finitely many disjoint open subsets of `U` that cover `U` up
to a null set is piecewise affine on `U`. -/
private theorem glue_pa_iUnion {ι : Type*} [Fintype ι] {U : Set (Fin m → ℝ)}
    {φ : (Fin m → ℝ) → Fin d → ℝ} (V : ι → Set (Fin m → ℝ))
    (hVd : Pairwise (Function.onFun Disjoint V)) (hVU : ∀ c, V c ⊆ U)
    (hcov : volume (U \ ⋃ c, V c) = 0) (h : ∀ c, PiecewiseAffineOn (V c) φ) :
    PiecewiseAffineOn U φ := by
  choose n P L hPo hPd hPV hcovV hL using h
  refine glue_pa_of_fintype (ι := Σ c, Fin (n c)) (fun q => P q.1 q.2) (fun q => L q.1 q.2)
    (fun q => hPo q.1 q.2) ?_ (fun q => (hPV q.1 q.2).trans (hVU q.1)) ?_ (fun q => hL q.1 q.2)
  · rintro ⟨c, i⟩ ⟨c', i'⟩ hne
    by_cases hc : c = c'
    · subst hc
      have hi : i ≠ i' := fun h => hne (by rw [h])
      exact hPd c hi
    · exact (hVd hc).mono (hPV c i) (hPV c' i')
  · refine measure_mono_null (t := (U \ ⋃ c, V c) ∪ ⋃ c, (V c \ ⋃ i, P c i)) ?_
      (measure_union_null hcov (measure_iUnion_null fun c => hcovV c))
    rintro x ⟨hxU, hx⟩
    by_cases hxV : ∃ c, x ∈ V c
    · obtain ⟨c, hc⟩ := hxV
      refine Or.inr (mem_iUnion.2 ⟨c, hc, fun h => hx ?_⟩)
      obtain ⟨i, hi⟩ := mem_iUnion.1 h
      exact mem_iUnion.2 ⟨⟨c, i⟩, hi⟩
    · exact Or.inl ⟨hxU, fun h => hxV (mem_iUnion.1 h)⟩

/-- Two distinct affine functions agree only on a null set (a hyperplane, or the empty set). -/
private theorem glue_volume_affine_eq {g g' : (Fin m → ℝ) →ᵃ[ℝ] ℝ} (h : g ≠ g') :
    volume {x | g x = g' x} = 0 := by
  set s : AffineSubspace ℝ (Fin m → ℝ) := (affineSpan ℝ ({0} : Set ℝ)).comap (g - g') with hs
  have hs' : (s : Set (Fin m → ℝ)) = {x | g x = g' x} := by
    ext x
    simp [hs, AffineSubspace.coe_comap, sub_eq_zero]
  rw [← hs']
  refine Measure.addHaar_affineSubspace volume s fun htop => h ?_
  ext x
  have hx : x ∈ (s : Set (Fin m → ℝ)) := by rw [htop]; exact AffineSubspace.mem_top ℝ _ x
  rw [hs'] at hx
  exact hx

/-- The affine function `x ↦ α x_i + β`. -/
private def glue_coordAff (i : Fin m) (α β : ℝ) : (Fin m → ℝ) →ᵃ[ℝ] ℝ where
  toFun x := α * x i + β
  linear := α • LinearMap.proj i
  map_vadd' p v := by simp [vadd_eq_add]; ring

private theorem glue_coordAff_apply (i : Fin m) (α β : ℝ) (x : Fin m → ℝ) :
    glue_coordAff i α β x = α * x i + β := rfl

/-- The affine map `x ↦ g (x) a`. -/
private def glue_smulAff (g : (Fin m → ℝ) →ᵃ[ℝ] ℝ) (a : Fin d → ℝ) :
    (Fin m → ℝ) →ᵃ[ℝ] (Fin d → ℝ) where
  toFun x := g x • a
  linear := g.linear.smulRight a
  map_vadd' p v := by
    change g (v +ᵥ p) • a = g.linear v • a + g p • a
    rw [AffineMap.map_vadd, vadd_eq_add, add_smul]

/-- **The minimum of finitely many affine functions is piecewise affine.** If on the open set `U`,
`φ = h a` with `h` the pointwise minimum of the affine functions `G s`, then `φ` is piecewise
affine on `U`: the pieces are the open sets where one of the distinct values of `G` is strictly
smallest, and the rest of `U` lies in the null set where two distinct ones agree. -/
private theorem glue_pa_min {S : Type*} [Fintype S] {U : Set (Fin m → ℝ)} (hU : IsOpen U)
    (G : S → (Fin m → ℝ) →ᵃ[ℝ] ℝ) (a : Fin d → ℝ) {φ : (Fin m → ℝ) → Fin d → ℝ}
    {h : (Fin m → ℝ) → ℝ} (hφ : ∀ x ∈ U, φ x = h x • a) (hle : ∀ x ∈ U, ∀ s, h x ≤ G s x)
    (hex : ∀ x ∈ U, ∃ s, h x = G s x) : PiecewiseAffineOn U φ := by
  classical
  set T := Finset.univ.image G with hT
  set P : T → Set (Fin m → ℝ) := fun g => U ∩ ⋂ g' ∈ T.erase g.1, {x | g.1 x < g' x} with hP
  have hGT : ∀ s, G s ∈ T := fun s => Finset.mem_image_of_mem G (Finset.mem_univ s)
  refine glue_pa_of_fintype P (fun g => glue_smulAff g.1 a) (fun g => ?_) (fun g g' hne => ?_)
    (fun g => inter_subset_left) ?_ (fun g x hx => ?_)
  · exact hU.inter (isOpen_biInter_finset fun g' _ =>
      isOpen_lt (AffineMap.continuous_of_finiteDimensional _)
        (AffineMap.continuous_of_finiteDimensional _))
  · refine Set.disjoint_left.2 fun x hx hx' => ?_
    have hne' : g.1 ≠ g'.1 := fun h => hne (Subtype.ext h)
    have h1 : g.1 x < g'.1 x := mem_iInter₂.1 hx.2 g'.1 (Finset.mem_erase.2 ⟨hne'.symm, g'.2⟩)
    have h2 : g'.1 x < g.1 x := mem_iInter₂.1 hx'.2 g.1 (Finset.mem_erase.2 ⟨hne', g.2⟩)
    exact lt_asymm h1 h2
  · refine measure_mono_null (t := ⋃ (g : T) (g' : T) (_ : g ≠ g'), {x | g.1 x = g'.1 x}) ?_
      (measure_iUnion_null fun g => measure_iUnion_null fun g' => measure_iUnion_null fun hne =>
        glue_volume_affine_eq fun h => hne (Subtype.ext h))
    rintro x ⟨hxU, hx⟩
    obtain ⟨s, hs⟩ := hex x hxU
    have hxP : x ∉ P ⟨G s, hGT s⟩ := fun h => hx (mem_iUnion.2 ⟨_, h⟩)
    have : ∃ g' ∈ T.erase (G s), ¬ G s x < g' x := by
      by_contra hcon
      push Not at hcon
      exact hxP ⟨hxU, mem_iInter₂.2 fun g' hg' => hcon g' hg'⟩
    obtain ⟨g', hg', hlt⟩ := this
    obtain ⟨s', -, rfl⟩ := Finset.mem_image.1 (Finset.mem_of_mem_erase hg')
    refine mem_iUnion₂.2 ⟨⟨G s, hGT s⟩, ⟨G s', hGT s'⟩, mem_iUnion.2
      ⟨fun h => Finset.ne_of_mem_erase hg' (congrArg Subtype.val h).symm, ?_⟩⟩
    have := hle x hxU s'
    show G s x = G s' x
    linarith [not_lt.1 hlt]
  · obtain ⟨hxU, hx⟩ := hx
    obtain ⟨s, hs⟩ := hex x hxU
    obtain ⟨s0, -, hs0⟩ := Finset.mem_image.1 g.2
    have hgs : G s = g.1 := by
      by_contra hne
      have h1 : g.1 x < G s x := mem_iInter₂.1 hx (G s) (Finset.mem_erase.2 ⟨hne, hGT s⟩)
      have h2 := hle x hxU s0
      rw [hs0] at h2
      linarith
    rw [hφ x hxU, hs, hgs]
    rfl

/-- On the unit cube, the sup-norm distance to the complement is at most `x_i` and `1 − x_i`. -/
private theorem glue_infDist_le {x : Fin m → ℝ} (hx : x ∈ unitCube m) (i : Fin m) :
    infDist x (unitCube m)ᶜ ≤ x i ∧ infDist x (unitCube m)ᶜ ≤ 1 - x i := by
  have hxi : x i ∈ Ioo (0 : ℝ) 1 := hx i (mem_univ i)
  constructor
  · have hy : Function.update x i 0 ∈ (unitCube m)ᶜ := fun h => by
      have := (h i (mem_univ i)).1
      simp at this
    refine (infDist_le_dist_of_mem hy).trans ((dist_pi_le_iff hxi.1.le).2 fun i' => ?_)
    by_cases hi : i' = i
    · subst hi
      simp [abs_of_pos hxi.1]
    · simp [Function.update_of_ne hi, hxi.1.le]
  · have hy : Function.update x i 1 ∈ (unitCube m)ᶜ := fun h => by
      have := (h i (mem_univ i)).2
      simp at this
    refine (infDist_le_dist_of_mem hy).trans ((dist_pi_le_iff (by linarith [hxi.2])).2
      fun i' => ?_)
    by_cases hi : i' = i
    · subst hi
      simp [Real.dist_eq, abs_of_neg (by linarith [hxi.2] : x i' - 1 < 0)]
    · simp [Function.update_of_ne hi, hxi.2.le]

/-- On the slab `{c < k x_j < c + 1}` of the unit cube, the laminate `v_k` is the minimum of the
affine functions `(1 − λ) (x_j − c / k)`, `λ ((c + 1) / k − x_j)`, `x_i`, `1 − x_i`, times `a`,
hence piecewise affine. -/
private theorem glue_pa_slab (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1)
    {k : ℕ} (hk : 0 < k) (c : ℕ) :
    PiecewiseAffineOn (unitCube m ∩ ({x | (c : ℝ) < k * x j} ∩ {x | k * x j < c + 1}))
      (cubeLaminate a j l k) := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  set G : Bool × Bool × Fin m → (Fin m → ℝ) →ᵃ[ℝ] ℝ := fun q =>
    if q.1 then (if q.2.1 then glue_coordAff j (1 - l) (-((1 - l) * c / k))
      else glue_coordAff j (-l) (l * (c + 1) / k))
    else (if q.2.1 then glue_coordAff q.2.2 1 0 else glue_coordAff q.2.2 (-1) 1) with hG
  have hopen : IsOpen (unitCube m ∩ ({x | (c : ℝ) < k * x j} ∩ {x | k * x j < c + 1})) :=
    cv_isOpen_unitCube.inter ((isOpen_lt continuous_const
      (continuous_const.mul (continuous_apply j))).inter
      (isOpen_lt (continuous_const.mul (continuous_apply j)) continuous_const))
  -- the sawtooth on the slab
  have hsaw : ∀ x ∈ unitCube m ∩ ({x | (c : ℝ) < k * x j} ∩ {x | k * x j < c + 1}),
      (k : ℝ)⁻¹ * rd_saw l (k * x j) =
        min ((1 - l) * x j + -((1 - l) * c / k)) (-l * x j + l * (c + 1) / k) := by
    rintro x ⟨-, h1, h2⟩
    simp only [mem_ofPred_eq] at h1 h2
    have hfr : Int.fract ((k : ℝ) * x j) = k * x j - c :=
      Int.fract_eq_iff.2 ⟨by linarith, by linarith, c, by push_cast; ring⟩
    have hr : rd_saw l (k * x j) =
        max 0 (min ((1 - l) * Int.fract ((k : ℝ) * x j)) (l * (1 - Int.fract ((k : ℝ) * x j)))) :=
      rfl
    rw [hr, hfr, max_eq_right (le_min (mul_nonneg (by linarith) (by linarith))
      (mul_nonneg hl0.le (by linarith))), mul_min_of_nonneg _ _ (inv_nonneg.2 hk'.le)]
    congr 1
    · field_simp
      ring
    · field_simp
      ring
  refine glue_pa_min hopen G a (h := fun x => min ((k : ℝ)⁻¹ * rd_saw l (k * x j))
    (infDist x (unitCube m)ᶜ)) (fun x _ => rfl) (fun x hx q => ?_) (fun x hx => ?_)
  · obtain ⟨b1, b2, i⟩ := q
    have hs := hsaw x hx
    have hd := glue_infDist_le hx.1 i
    cases b1 <;> cases b2 <;> simp only [hG, glue_coordAff_apply, Bool.false_eq_true,
      ite_true, ite_false]
    · linarith [min_le_right ((k : ℝ)⁻¹ * rd_saw l (k * x j)) (infDist x (unitCube m)ᶜ)]
    · linarith [min_le_right ((k : ℝ)⁻¹ * rd_saw l (k * x j)) (infDist x (unitCube m)ᶜ)]
    · rw [hs]
      exact (min_le_left _ _).trans (min_le_right _ _)
    · rw [hs]
      exact (min_le_left _ _).trans (min_le_left _ _)
  · show ∃ q, min ((k : ℝ)⁻¹ * rd_saw l (k * x j)) (infDist x (unitCube m)ᶜ) = G q x
    by_cases hle : (k : ℝ)⁻¹ * rd_saw l (k * x j) ≤ infDist x (unitCube m)ᶜ
    · rw [min_eq_left hle, hsaw x hx]
      rcases min_choice ((1 - l) * x j + -((1 - l) * c / k)) (-l * x j + l * (c + 1) / k)
        with h | h
      · exact ⟨(true, true, j), by rw [h]; simp [hG, glue_coordAff_apply]⟩
      · exact ⟨(true, false, j), by rw [h]; simp [hG, glue_coordAff_apply]⟩
    · rw [min_eq_right (le_of_not_ge hle)]
      obtain ⟨i, hi | hi⟩ := exists_infDist_compl_unitCube_eq hx.1 j
      · exact ⟨(false, true, i), by rw [hi]; simp [hG, glue_coordAff_apply]⟩
      · exact ⟨(false, false, i), by rw [hi]; simp [hG, glue_coordAff_apply]; ring⟩

/-- The laminate `v_k` of `Quasiconvex.Laminate` is piecewise affine on the unit cube: the
sawtooth is affine between the points of `k⁻¹ (ℤ ∪ (ℤ + λ))`, the distance to the boundary is
affine on each of the `2 m` pyramids over the faces, and the minimum of two affine maps is affine
on each side of a hyperplane. In the proof, on each slab `{c < k x_j < c + 1}` (whose complement in
the cube lies in the hyperplanes `k x_j = c`), `v_k` is `a` times the minimum of the `2 m + 2`
affine functions `(1 − λ) (x_j − c / k)`, `λ ((c + 1) / k − x_j)`, `x_i`, `1 − x_i`, which is
affine on each open set where one of the distinct ones is strictly smallest (`glue_pa_min`). -/
theorem cubeLaminate_piecewiseAffineOn (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (hl0 : 0 < l)
    (hl1 : l < 1) {k : ℕ} (hk : 0 < k) :
    PiecewiseAffineOn (unitCube m) (cubeLaminate a j l k) := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  refine glue_pa_iUnion (fun c : Fin k => unitCube m ∩ ({x | ((c : ℕ) : ℝ) < k * x j} ∩
      {x | k * x j < (c : ℕ) + 1})) (fun c c' hne => ?_) (fun c => inter_subset_left) ?_
    (fun c => glue_pa_slab a j hl0 hl1 hk c)
  · -- the slabs are disjoint
    refine Set.disjoint_left.2 fun x hx hx' => hne ?_
    have h1 : ((c : ℕ) : ℝ) < (c' : ℕ) + 1 := hx.2.1.trans hx'.2.2
    have h2 : ((c' : ℕ) : ℝ) < (c : ℕ) + 1 := hx'.2.1.trans hx.2.2
    have h1' : (c : ℕ) < (c' : ℕ) + 1 := by exact_mod_cast h1
    have h2' : (c' : ℕ) < (c : ℕ) + 1 := by exact_mod_cast h2
    exact Fin.ext (by omega)
  · -- they cover the cube up to the hyperplanes `k x_j = c`
    refine measure_mono_null (t := ⋃ c : Fin k,
      {x | glue_coordAff j k 0 x = glue_coordAff j 0 ((c : ℕ) : ℝ) x}) ?_
      (measure_iUnion_null fun c => glue_volume_affine_eq fun h => ?_)
    · rintro x ⟨hxQ, hx⟩
      have hxj : x j ∈ Ioo (0 : ℝ) 1 := hxQ j (mem_univ j)
      have hpos : 0 < (k : ℝ) * x j := mul_pos hk' hxj.1
      have hltk : (k : ℝ) * x j < k := by nlinarith [hxj.2]
      have hck : ⌊(k : ℝ) * x j⌋₊ < k := (Nat.floor_lt hpos.le).2 hltk
      have hcle : (⌊(k : ℝ) * x j⌋₊ : ℝ) ≤ k * x j := Nat.floor_le hpos.le
      have hclt : (k : ℝ) * x j < ⌊(k : ℝ) * x j⌋₊ + 1 := Nat.lt_floor_add_one _
      refine mem_iUnion.2 ⟨⟨_, hck⟩, ?_⟩
      simp only [mem_ofPred_eq, glue_coordAff_apply]
      by_contra hne
      exact hx (mem_iUnion.2 ⟨⟨_, hck⟩, hxQ, lt_of_le_of_ne hcle fun h => hne (by
        simp only [zero_mul, add_zero, zero_add]
        exact h.symm), hclt⟩)
    · have := congrArg (fun g : (Fin m → ℝ) →ᵃ[ℝ] ℝ => g fun _ => (((c : ℕ) : ℝ) + 1) / k) h
      simp only [glue_coordAff_apply, zero_mul, add_zero, zero_add] at this
      rw [mul_div_cancel₀ _ hk'.ne'] at this
      linarith

/-! ### The two-point inequality -/

/-- The two-point inequality with real bounds `y_A ≥ cubeInf f (F + (1 − λ) a ⊗ e_j)` and
`y_B ≥ cubeInf f (F − λ a ⊗ e_j)`, for `a ≠ 0`. With `g = y_A` at `A' = (1 − λ) a ⊗ e_j`,
`g = y_B` at `B' = −λ a ⊗ e_j` and `g = M ≥ f (F + ·)` elsewhere: (4.28) for the laminate `v_k`
gives `cubeInf f F ≤ ∫_Q g (∇v_k)`, which differs from
`∫_Q g (∇u_k) = λ y_A + (1 − λ) y_B` by at most `2 sup |g| · |{∇v_k ≠ ∇u_k}| → 0`. -/
private theorem glue_two_point_real {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (F : Matrix (Fin d) (Fin m) ℝ) {a : Fin d → ℝ} (ha : a ≠ 0) (j : Fin m) {l : ℝ} (hl0 : 0 < l)
    (hl1 : l < 1) {yA yB : ℝ}
    (hA : cubeInf f (F + (1 - l) • Matrix.vecMulVec a (Pi.single j 1)) ≤ yA)
    (hB : cubeInf f (F - l • Matrix.vecMulVec a (Pi.single j 1)) ≤ yB) :
    cubeInf f F ≤ ((l * yA + (1 - l) * yB : ℝ) : EReal) := by
  classical
  set E := Matrix.vecMulVec a (Pi.single j 1) with hE
  have hE0 : E ≠ 0 := by
    intro h
    apply ha
    funext i
    have := congrFun (congrFun h i) j
    simpa [hE, Matrix.vecMulVec_apply] using this
  have hAB : (1 - l) • E ≠ (-l) • E := by
    intro h
    apply hE0
    have : ((1 - l) - (-l)) • E = 0 := by rw [sub_smul, h, sub_self]
    simpa using this
  have hFB : F - l • E = F + (-l) • E := by rw [neg_smul, ← sub_eq_add_neg]
  obtain ⟨M, hM0, hM⟩ := cv_bdd hf F ‖a‖
  set g : Matrix (Fin d) (Fin m) ℝ → ℝ := fun G =>
    if G = (1 - l) • E then yA else if G = (-l) • E then yB else M with hg
  set C := |yA| + |yB| + M with hC
  have hgC : ∀ G, |g G| ≤ C := by
    intro G
    simp only [hg]
    split_ifs
    · linarith [abs_nonneg yB]
    · linarith [abs_nonneg yA]
    · rw [abs_of_nonneg hM0]
      linarith [abs_nonneg yA, abs_nonneg yB]
  have hgA : g ((1 - l) • E) = yA := ite_eq_left rfl
  have hgB : g ((-l) • E) = yB := by
    show (if (-l) • E = (1 - l) • E then yA else if (-l) • E = (-l) • E then yB else M) = yB
    rw [ite_eq_right hAB.symm, ite_eq_left rfl]
  have hgm : Measurable g := Measurable.ite (measurableSet_singleton _) measurable_const
    (Measurable.ite (measurableSet_singleton _) measurable_const measurable_const)
  have hQfin : volume (unitCube m) ≠ ⊤ := by rw [cv_volume_unitCube]; exact ENNReal.one_ne_top
  have hmgrad : ∀ φ : (Fin m → ℝ) → Fin d → ℝ, Measurable (grad φ) := fun φ => by
    simpa using rd_measurable_add_grad (0 : Matrix (Fin d) (Fin m) ℝ) φ
  have hint : ∀ φ : (Fin m → ℝ) → Fin d → ℝ,
      IntegrableOn (fun x => g (grad φ x)) (unitCube m) := fun φ =>
    Measure.integrableOn_of_bounded (M := C) hQfin (hgm.comp (hmgrad φ)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hgC _)
  -- (4.28) for the laminate `v_k`
  have hv : ∀ k : ℕ, 0 < k →
      cubeInf f F ≤ ((∫ x in unitCube m, g (grad (cubeLaminate a j l k) x) : ℝ) : EReal) := by
    intro k hk
    have hlip := cubeLaminate_lipschitz a j hl0.le hl1.le k
    obtain ⟨n, P, L, hPo, hPd, hPQ, hcov, hL⟩ := cubeLaminate_piecewiseAffineOn a j hl0 hl1 hk
    refine (cubeInf_le_sum_of_piecewiseAffine hf F P L hPo hPd hPQ hcov ⟨_, hlip⟩
      (cubeLaminate_eq_zero a j hl0.le hl1.le k) hL).trans ?_
    have hterm : ∀ i, ((volume (P i)).toReal : EReal) *
        cubeInf f (F + LinearMap.toMatrix' (L i).linear) ≤
        (((volume (P i)).toReal * g (LinearMap.toMatrix' (L i).linear) : ℝ) : EReal) := by
      intro i
      rcases eq_or_lt_of_le (ENNReal.toReal_nonneg : 0 ≤ (volume (P i)).toReal) with h0 | hpos
      · rw [← h0, EReal.coe_zero, zero_mul, zero_mul, EReal.coe_zero]
      · obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero (μ := volume) (s := P i) fun h => by
          simp [h] at hpos
        have hgrad := glue_grad_eq (hPo i) (hL i) hx
        rw [EReal.coe_mul]
        refine mul_le_mul_of_nonneg_left ?_ (EReal.coe_nonneg.2 hpos.le)
        by_cases hGA : LinearMap.toMatrix' (L i).linear = (1 - l) • E
        · rw [hGA, hgA]
          exact hA
        · by_cases hGB : LinearMap.toMatrix' (L i).linear = (-l) • E
          · rw [hGB, ← hFB, hgB]
            exact hB
          · simp only [hg, hGA, hGB, ite_false]
            refine (cubeInf_le _).trans (EReal.coe_le_coe_iff.2 ((le_abs_self _).trans (hM _ ?_)))
            intro i' k'
            rw [← hgrad]
            have := cv_grad_abs_le hlip x i' k'
            rwa [coe_nnnorm] at this
    refine (Finset.sum_le_sum fun i _ => hterm i).trans (le_of_eq ?_)
    have hsum : ∀ r : Fin n → ℝ, ∑ i, ((r i : ℝ) : EReal) = ((∑ i, r i : ℝ) : EReal) := by
      intro r
      induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
      | empty => simp
      | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, ih, EReal.coe_add]
    rw [hsum]
    congr 1
    -- `∫_Q g (∇v_k) = ∑ i |P i| g (∇ (L i))`
    have hQP : unitCube m =ᵐ[volume] ⋃ i, P i := ae_eq_set.2 ⟨hcov, by
      rw [sdiff_eq_empty.2 (iUnion_subset hPQ), measure_empty]⟩
    rw [setIntegral_congr_set hQP, integral_iUnion_fintype (fun i => (hPo i).measurableSet) hPd
      (fun i => (hint _).mono_set (hPQ i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [setIntegral_congr_fun (g := fun _ => g (LinearMap.toMatrix' (L i).linear))
      (hPo i).measurableSet fun x hx => by simp only [glue_grad_eq (hPo i) (hL i) hx],
      setIntegral_const, smul_eq_mul, measureReal_def]
  -- the energy of `u_k`
  have hu : ∀ k : ℕ, 0 < k →
      ∫ x in unitCube m, g (grad (sawLaminate a j l k) x) = l * yA + (1 - l) * yB := by
    intro k hk
    have h := setIntegral_sawLaminate (fun X => g (X - F)) F a j hl0 hl1 hk
    simp only [add_sub_cancel_left, sub_sub_cancel_left] at h
    rw [← hE, ← neg_smul, hgA, hgB] at h
    exact h
  -- the two energies differ by at most `2 C |{∇v_k ≠ ∇u_k}|`
  have hdiff : ∀ k : ℕ, ‖(∫ x in unitCube m, g (grad (cubeLaminate a j l k) x)) -
      ∫ x in unitCube m, g (grad (sawLaminate a j l k) x)‖ ≤
      2 * C * (volume {x ∈ unitCube m |
        grad (cubeLaminate a j l k) x ≠ grad (sawLaminate a j l k) x}).toReal := by
    intro k
    set v := cubeLaminate a j l k
    set u := sawLaminate a j l k
    set D := {x | grad v x ≠ grad u x} with hD
    have hDm : MeasurableSet D :=
      (measurableSet_eq_fun (cv_measurable_grad v) (cv_measurable_grad u)).compl
    rw [← integral_sub (hint v) (hint u)]
    have hb : ∀ x, ‖g (grad v x) - g (grad u x)‖ ≤ D.indicator (fun _ => 2 * C) x := by
      intro x
      by_cases hx : x ∈ D
      · rw [indicator_of_mem hx, Real.norm_eq_abs]
        calc |g (grad v x) - g (grad u x)| ≤ |g (grad v x)| + |g (grad u x)| := abs_sub _ _
          _ ≤ C + C := add_le_add (hgC _) (hgC _)
          _ = 2 * C := by ring
      · have : grad v x = grad u x := not_not.1 hx
        rw [indicator_of_notMem hx, this, sub_self, norm_zero]
    refine (norm_integral_le_of_norm_le
      ((integrableOn_const hQfin : IntegrableOn (fun _ => 2 * C) (unitCube m)).indicator hDm)
      (Filter.Eventually.of_forall hb)).trans (le_of_eq ?_)
    rw [integral_indicator_const _ hDm, measureReal_restrict_apply hDm, smul_eq_mul, mul_comm,
      measureReal_def, inter_comm]
    rfl
  -- the limit
  have hvol : Tendsto (fun k : ℕ => 2 * C * (volume {x ∈ unitCube m |
      grad (cubeLaminate a j l k) x ≠ grad (sawLaminate a j l k) x}).toReal) atTop (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_volume_grad_cubeLaminate_ne a j hl0.le hl1.le)).const_mul (2 * C)
    simpa using this
  have hlim : Tendsto (fun k : ℕ => ∫ x in unitCube m, g (grad (cubeLaminate a j l k) x)) atTop
      (𝓝 (l * yA + (1 - l) * yB)) := by
    have h0 := squeeze_zero_norm' (Filter.Eventually.of_forall hdiff) hvol
    have h1 := h0.add (tendsto_const_nhds (x := l * yA + (1 - l) * yB))
    rw [zero_add] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    rw [hu k hk, sub_add_cancel]
  exact ge_of_tendsto ((continuous_coe_real_ereal.tendsto _).comp hlim)
    ((eventually_gt_atTop 0).mono hv)

/-- **The two-point inequality of the infimum formula** (Müller 1998, §4.8, with Lemma 4.3): for
continuous `f`,
`cubeInf f (F) ≤ λ cubeInf f (F + (1 − λ) a ⊗ e_j) + (1 − λ) cubeInf f (F − λ a ⊗ e_j)` (in
`EReal`), from `cubeInf_le_sum_of_piecewiseAffine` applied to the laminates `v_k`. -/
theorem cubeInf_le_two_point {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (F : Matrix (Fin d) (Fin m) ℝ) (a : Fin d → ℝ) (j : Fin m) {l : ℝ} (hl0 : 0 < l)
    (hl1 : l < 1) :
    cubeInf f F ≤ (l : EReal) * cubeInf f (F + (1 - l) • Matrix.vecMulVec a (Pi.single j 1)) +
      ((1 - l : ℝ) : EReal) * cubeInf f (F - l • Matrix.vecMulVec a (Pi.single j 1)) := by
  by_cases ha : a = 0
  · -- `a = 0`: both sides are `cubeInf f F`
    subst ha
    simp only [Matrix.zero_vecMulVec, smul_zero, add_zero, sub_zero]
    rw [← EReal.right_distrib_of_nonneg (EReal.coe_nonneg.2 hl0.le)
      (EReal.coe_nonneg.2 (by linarith)), ← EReal.coe_add, add_sub_cancel, EReal.coe_one, one_mul]
  set x := cubeInf f (F + (1 - l) • Matrix.vecMulVec a (Pi.single j 1)) with hx
  set y := cubeInf f (F - l • Matrix.vecMulVec a (Pi.single j 1)) with hy
  have hxt : x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (cubeInf_le _)
  have hyt : y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (cubeInf_le _)
  by_cases hxb : x = ⊥
  · -- `x = −∞`: then `cubeInf f F = −∞`
    suffices h : cubeInf f F = ⊥ by rw [h]; exact bot_le
    rw [EReal.eq_bot_iff_forall_lt]
    intro z
    set yB := f (F - l • Matrix.vecMulVec a (Pi.single j 1))
    have h := glue_two_point_real hf F ha j hl0 hl1 (yA := (z - 1 - (1 - l) * yB) / l)
      (yB := yB) (by rw [← hx, hxb]; exact bot_le) (cubeInf_le _)
    refine h.trans_lt (EReal.coe_lt_coe_iff.2 ?_)
    rw [mul_div_cancel₀ _ hl0.ne']
    linarith
  by_cases hyb : y = ⊥
  · -- `y = −∞`: then `cubeInf f F = −∞`
    suffices h : cubeInf f F = ⊥ by rw [h]; exact bot_le
    rw [EReal.eq_bot_iff_forall_lt]
    intro z
    set yA := f (F + (1 - l) • Matrix.vecMulVec a (Pi.single j 1))
    have h1l : (1 - l) ≠ 0 := by linarith
    have h := glue_two_point_real hf F ha j hl0 hl1 (yA := yA)
      (yB := (z - 1 - l * yA) / (1 - l)) (cubeInf_le _) (by rw [← hy, hyb]; exact bot_le)
    refine h.trans_lt (EReal.coe_lt_coe_iff.2 ?_)
    rw [mul_div_cancel₀ _ h1l]
    linarith
  -- both values are real
  have h := glue_two_point_real hf F ha j hl0 hl1 (yA := x.toReal) (yB := y.toReal)
    (le_of_eq (EReal.coe_toReal hxt hxb).symm) (le_of_eq (EReal.coe_toReal hyt hyb).symm)
  refine h.trans (le_of_eq ?_)
  rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul, EReal.coe_toReal hxt hxb,
    EReal.coe_toReal hyt hyb]

end CalculusOfVariations
