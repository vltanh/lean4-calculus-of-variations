/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Envelope.Tangent
public import CalculusOfVariations.Convex.SeparatelyConvex

/-!
# Convexity, continuity and quasiconvexity of the infimum formula

For continuous `f`:

* laminates (`coordLaminate`): the sawtooth in the direction `e_j` and the entry `i`, cut off near
  the boundary of the cube by the minimum with the distance to the complement, give the convexity
  inequality of `cubeInf f` along the lines `A + t E_{ij}` with truncated values
  (`cubeInf_laminate`);
* the dichotomy: `cubeInf f ≡ −∞`, or `cubeInf f` is real-valued (`cubeInf_bot_all`);
* in the finite case `cubeInfReal f`, the real-valued `cubeInf f`, is separately convex, hence
  continuous (`cubeInfReal_continuous`), and quasiconvex (`cubeInfReal_quasiconvex`);
* `cubeInf_le_qcEnvelope`: `cubeInf f ≤ qcEnvelope f`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

namespace CalculusOfVariations

variable {d m : ℕ}

/-! ### Laminates -/

/-- The asymmetric absolute value `max ((1 - λ) τ, -λ τ)`. -/
noncomputable def asymAbs (l τ : ℝ) : ℝ := max ((1 - l) * τ) (-l * τ)

/-- The sawtooth with `n` teeth on `[0, 1]`: slope `1 - λ` on `(k/n, (k+λ)/n)`, slope `-λ` on
`((k+λ)/n, (k+1)/n)`, vanishing at the nodes `k/n`. -/
noncomputable def sawN (l : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (Finset.range (n + 1)).inf' (by simp) fun k => asymAbs l (t - k / n)

theorem asymAbs_nonneg {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (τ : ℝ) : 0 ≤ asymAbs l τ := by
  rcases le_total 0 τ with h | h
  · exact (mul_nonneg (by linarith) h).trans (le_max_left _ _)
  · exact (mul_nonneg_of_nonpos_of_nonpos (by linarith) h).trans (le_max_right _ _)

theorem asymAbs_lipschitz {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) : LipschitzWith 1 (asymAbs l) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  unfold asymAbs
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rw [← mul_sub, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 - l)]; nlinarith [abs_nonneg
      (a - b)]
  · rw [← mul_sub, abs_mul, abs_neg, abs_of_pos hl0]; nlinarith [abs_nonneg (a - b)]

theorem sawN_nonneg {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (n : ℕ) (t : ℝ) : 0 ≤ sawN l n t :=
  Finset.le_inf' _ _ fun _ _ => asymAbs_nonneg hl0 hl1 _

theorem sawN_lipschitz {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (n : ℕ) :
    LipschitzWith 1 (sawN l n) := by
  refine LipschitzWith.of_le_add_mul 1 fun a b => ?_
  obtain ⟨k, hk, hkb⟩ := Finset.exists_mem_eq_inf' (s := Finset.range (n + 1)) (by simp)
    (fun k' => asymAbs l (b - k' / n))
  calc sawN l n a ≤ asymAbs l (a - k / n) := Finset.inf'_le _ hk
    _ ≤ asymAbs l (b - k / n) + 1 * dist (a - k / n) (b - k / n) := by
        have := (asymAbs_lipschitz hl0 hl1).dist_le_mul (a - k / n) (b - k / n)
        rw [Real.dist_eq (asymAbs l _)] at this
        have h2 := le_abs_self (asymAbs l (a - k / n) - asymAbs l (b - k / n))
        push_cast at this ⊢
        linarith
    _ = sawN l n b + 1 * dist a b := by
        rw [sawN, ← hkb, Real.dist_eq, Real.dist_eq, sub_sub_sub_cancel_right]

theorem sawN_le {l : ℝ} (hl0 : 0 < l) (_hl1 : l < 1) {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : sawN l n t ≤ 1 / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set k := ⌊(n : ℝ) * t⌋₊ with hk
  have hk1 : (k : ℝ) ≤ n * t := Nat.floor_le (by positivity)
  have hk2 : (n : ℝ) * t < k + 1 := Nat.lt_floor_add_one _
  have hkn : k ∈ Finset.range (n + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_of_le (by nlinarith)
  refine (Finset.inf'_le _ hkn).trans ?_
  have h0 : 0 ≤ t - k / n := by rw [sub_nonneg, div_le_iff₀ hn']; linarith
  have h1 : t - k / n < 1 / n := by
    rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hn']; linarith
  unfold asymAbs
  refine max_le ?_ ?_
  · nlinarith
  · nlinarith

/-- On the rising part of a tooth, the sawtooth is `(1 - λ) (t - k/n)`. -/
theorem sawN_eq_rise {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {n k : ℕ} (hn : 0 < n) (hk : k < n)
    {t : ℝ} (ht0 : k / n ≤ t) (ht1 : t ≤ (k + l) / n) :
    sawN l n t = (1 - l) * (t - k / n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hkm : k ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  have hval : asymAbs l (t - k / n) = (1 - l) * (t - k / n) := by
    unfold asymAbs
    have : 0 ≤ t - k / n := by linarith
    exact max_eq_left (by nlinarith)
  refine le_antisymm (hval ▸ Finset.inf'_le _ hkm) (Finset.le_inf' _ _ fun k' hk' => ?_)
  unfold asymAbs
  rcases le_or_gt k' k with h | h
  · have : (k' : ℝ) ≤ k := Nat.cast_le.2 h
    have : (k' : ℝ) / n ≤ k / n := div_le_div_of_nonneg_right this hn'.le
    exact le_max_of_le_left (by nlinarith)
  · have h' : (k : ℝ) + 1 ≤ k' := by exact_mod_cast h
    have e1 : ((k : ℝ) + 1) / n ≤ k' / n := div_le_div_of_nonneg_right h' hn'.le
    have e2 : t ≤ (k + l) / n := ht1
    refine le_max_of_le_right ?_
    have e3 : (1 - l) * (t - k / n) ≤ l * ((k + 1) / n - t) := by
      have : (k + l) / n = (1 - l) * (k / n) + l * ((k + 1) / n) := by field_simp; ring
      nlinarith
    nlinarith

/-- On the falling part of a tooth, the sawtooth is `λ ((k+1)/n - t)`. -/
theorem sawN_eq_fall {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {n k : ℕ} (hn : 0 < n) (hk : k < n)
    {t : ℝ} (ht0 : (k + l) / n ≤ t) (ht1 : t ≤ (k + 1) / n) :
    sawN l n t = l * ((k + 1) / n - t) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hkm : k + 1 ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  have hval : asymAbs l (t - ((k + 1 : ℕ) : ℝ) / n) = l * ((k + 1) / n - t) := by
    unfold asymAbs
    push_cast
    have : t - (k + 1) / n ≤ 0 := by linarith
    rw [max_eq_right (by nlinarith)]; ring
  refine le_antisymm (hval ▸ Finset.inf'_le _ hkm) (Finset.le_inf' _ _ fun k' hk' => ?_)
  unfold asymAbs
  rcases le_or_gt k' k with h | h
  · have : (k' : ℝ) ≤ k := Nat.cast_le.2 h
    have : (k' : ℝ) / n ≤ k / n := div_le_div_of_nonneg_right this hn'.le
    refine le_max_of_le_left ?_
    have e3 : l * ((k + 1) / n - t) ≤ (1 - l) * (t - k / n) := by
      have : (k + l) / n = (1 - l) * (k / n) + l * ((k + 1) / n) := by field_simp; ring
      nlinarith
    nlinarith
  · have h' : (k : ℝ) + 1 ≤ k' := by exact_mod_cast h
    have e1 : ((k : ℝ) + 1) / n ≤ k' / n := div_le_div_of_nonneg_right h' hn'.le
    exact le_max_of_le_right (by nlinarith)

/-- The laminate: the sawtooth in the direction `e_j`, in the entry `i`, cut off near the
boundary of the cube by `min` with the distance to the complement. -/
noncomputable def coordLaminate (i : Fin d) (j : Fin m) (l : ℝ) (n : ℕ) (s : ℝ) :
    (Fin m → ℝ) → Fin d → ℝ :=
  fun x => Pi.single i (min (s * sawN l n (x j)) (infDist x (unitCube m)ᶜ))

theorem coordLaminate_lipschitz (i : Fin d) (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (n : ℕ)
    {s : ℝ} (hs : 0 < s) : LipschitzWith (max s.toNNReal 1) (coordLaminate i j l n s) := by
  have h1 : LipschitzWith s.toNNReal fun x : Fin m → ℝ => s * sawN l n (x j) := by
    have := ((sawN_lipschitz hl0 hl1 n).comp (LipschitzWith.eval (α := fun _ : Fin m => ℝ) j))
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h := this.dist_le_mul x y
    simp only [Function.comp_apply, mul_one, NNReal.coe_one, one_mul] at h
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hs, Real.coe_toNNReal _ hs.le]
    rw [Real.dist_eq] at h
    exact mul_le_mul_of_nonneg_left h hs.le
  have h2 := h1.min (lipschitz_infDist_pt (s := (unitCube m)ᶜ))
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [coordLaminate, dist_eq_norm, ← Pi.single_sub, Pi.norm_single]
  have := h2.dist_le_mul x y
  rw [Real.dist_eq] at this
  rw [← Real.norm_eq_abs] at this
  exact this.trans (le_of_eq (by rw [dist_eq_norm]))

theorem coordLaminate_eq_zero (i : Fin d) (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (n : ℕ)
    {s : ℝ} (hs : 0 < s) {x : Fin m → ℝ} (hx : x ∉ unitCube m) : coordLaminate i j l n s x = 0 := by
  simp only [coordLaminate, infDist_zero_of_mem (show x ∈ (unitCube m)ᶜ from hx),
    min_eq_right (mul_nonneg hs.le (sawN_nonneg hl0 hl1 n _)), Pi.single_zero]

/-- The gradient of the affine map `x ↦ a (x_j - b) e_i`. -/
theorem cv_grad_single (i : Fin d) (j : Fin m) (a b : ℝ) (x : Fin m → ℝ) :
    grad (fun y : Fin m → ℝ => (Pi.single i (a * (y j - b)) : Fin d → ℝ)) x =
      Matrix.single i j a := by
  ext i' k
  change fderiv ℝ (fun y : Fin m → ℝ => (Pi.single i (a * (y j - b)) : Fin d → ℝ) i') x
    (Pi.single k 1) = _
  by_cases hi : i' = i
  · subst hi
    have e : (fun y : Fin m → ℝ => (Pi.single i' (a * (y j - b)) : Fin d → ℝ) i') =
        fun y => a * (y j - b) := by ext y; simp
    rw [e]
    have hd : HasFDerivAt (fun y : Fin m → ℝ => a * (y j - b))
        (a • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j) x := by
      have := ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin m => ℝ) j x).sub_const b).const_mul a
      simpa using this
    rw [hd.fderiv]
    simp [Matrix.single_apply, Pi.single_apply]
  · have e : (fun y : Fin m → ℝ => (Pi.single i (a * (y j - b)) : Fin d → ℝ) i') = fun _ => 0 := by
      ext y; simp [hi]
    rw [e, fderiv_const_apply]
    simp [Ne.symm hi]

/-- The box `{x : a < x_j < b, 0 < x_l < 1 (l ≠ j)}`. -/
def slab (j : Fin m) (a b : ℝ) : Set (Fin m → ℝ) :=
  Set.pi univ fun l => Ioo (if l = j then a else 0) (if l = j then b else 1)

theorem slab_subset {j : Fin m} {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    slab j a b ⊆ unitCube m := by
  intro x hx l _
  have := hx l (mem_univ l)
  simp only at this
  show x l ∈ Ioo 0 1
  split_ifs at this with h
  · exact ⟨ha.trans_lt this.1, this.2.trans_le hb⟩
  · exact this

theorem slab_measureReal (j : Fin m) {a b : ℝ} (hab : a ≤ b) :
    volume.real (slab j a b) = b - a := by
  rw [measureReal_def, slab, Real.volume_pi_Ioo]
  have : (fun l : Fin m => ENNReal.ofReal ((if l = j then b else 1) - (if l = j then a else 0))) =
      fun l => if l = j then ENNReal.ofReal (b - a) else 1 := by
    ext l; split_ifs <;> simp
  rw [this, Finset.prod_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  rw [ENNReal.toReal_ofReal (by linarith)]

theorem slab_disjoint {j : Fin m} {a b a' b' : ℝ} (h : b ≤ a') :
    Disjoint (slab j a b) (slab j a' b') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 := hx j (mem_univ j)
  have h2 := hx' j (mem_univ j)
  simp only [ite_true, mem_Ioo] at h1 h2
  linarith [h1.2, h2.1]

theorem slab_mem {j : Fin m} {a b : ℝ} {x : Fin m → ℝ} (hx : x ∈ slab j a b) :
    a < x j ∧ x j < b := by
  have := hx j (mem_univ j)
  simpa using this

theorem slab_ne_top (j : Fin m) (a b : ℝ) : volume (slab j a b) ≠ ⊤ := by
  rw [slab, Real.volume_pi_Ioo]
  exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top

/-- The rising strips of the laminate, and their total measure. -/
noncomputable def riseStrips (j : Fin m) (l : ℝ) (n : ℕ) : Set (Fin m → ℝ) :=
  ⋃ k ∈ Finset.range n, slab j (k / n) ((k + l) / n)

/-- The falling strips of the laminate. -/
noncomputable def fallStrips (j : Fin m) (l : ℝ) (n : ℕ) : Set (Fin m → ℝ) :=
  ⋃ k ∈ Finset.range n, slab j ((k + l) / n) ((k + 1) / n)

theorem cv_strip_facts (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {n : ℕ} (hn : 0 < n) :
    riseStrips j l n ⊆ unitCube m ∧ fallStrips j l n ⊆ unitCube m ∧
    MeasurableSet (riseStrips j l n) ∧ MeasurableSet (fallStrips j l n) ∧
    Disjoint (riseStrips j l n) (fallStrips j l n) ∧
    volume.real (riseStrips j l n) = l ∧ volume.real (fallStrips j l n) = 1 - l := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hmb : ∀ a b, MeasurableSet (slab j a b) := fun a b =>
    MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hk : ∀ k ∈ Finset.range n, (k : ℝ) + 1 ≤ n := fun k hk => by
    have := Finset.mem_range.1 hk; exact_mod_cast this
  have hdiv : ∀ a b : ℝ, a ≤ b → a / n ≤ b / n := fun a b h => div_le_div_of_nonneg_right h hn'.le
  -- the boxes are ordered along `e_j`
  have hd1 : (Finset.range n : Set ℕ).PairwiseDisjoint fun k => slab j (k / n) ((k + l) / n) := by
    intro k _ k' _ hkk'
    rcases lt_or_gt_of_ne hkk' with h | h
    · have : (k : ℝ) + 1 ≤ k' := by exact_mod_cast h
      exact slab_disjoint (hdiv _ _ (by linarith))
    · have : (k' : ℝ) + 1 ≤ k := by exact_mod_cast h
      exact (slab_disjoint (hdiv _ _ (by linarith))).symm
  have hd2 : (Finset.range n : Set ℕ).PairwiseDisjoint fun k =>
      slab j ((k + l) / n) ((k + 1) / n) := by
    intro k _ k' _ hkk'
    rcases lt_or_gt_of_ne hkk' with h | h
    · have : (k : ℝ) + 1 ≤ k' := by exact_mod_cast h
      exact slab_disjoint (hdiv _ _ (by linarith))
    · have : (k' : ℝ) + 1 ≤ k := by exact_mod_cast h
      exact (slab_disjoint (hdiv _ _ (by linarith))).symm
  refine ⟨?_, ?_, Finset.measurableSet_biUnion _ fun _ _ => hmb _ _,
    Finset.measurableSet_biUnion _ fun _ _ => hmb _ _, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨k, hk', hx⟩ := mem_iUnion₂.1 hx
    exact slab_subset (div_nonneg (Nat.cast_nonneg k) hn'.le)
      (by rw [div_le_one hn']; linarith [hk k hk']) hx
  · intro x hx
    obtain ⟨k, hk', hx⟩ := mem_iUnion₂.1 hx
    exact slab_subset (div_nonneg (by positivity) hn'.le)
      (by rw [div_le_one hn']; linarith [hk k hk']) hx
  · rw [Set.disjoint_left]
    intro x hx hx'
    obtain ⟨k, -, hx⟩ := mem_iUnion₂.1 hx
    obtain ⟨k', -, hx'⟩ := mem_iUnion₂.1 hx'
    have h1 := slab_mem hx
    have h2 := slab_mem hx'
    -- `k/n < x_j < (k+l)/n` and `(k'+l)/n < x_j < (k'+1)/n` are incompatible
    rcases le_or_gt k k' with h | h
    · have : (k : ℝ) ≤ k' := by exact_mod_cast h
      have : ((k : ℝ) + l) / n ≤ (k' + l) / n := hdiv _ _ (by linarith)
      linarith [h1.2, h2.1]
    · have : (k' : ℝ) + 1 ≤ k := by exact_mod_cast h
      have : ((k' : ℝ) + 1) / n ≤ k / n := hdiv _ _ this
      linarith [h1.1, h2.2]
  · rw [riseStrips, measureReal_biUnion_finset hd1 (fun _ _ => hmb _ _)
      (fun _ _ => slab_ne_top _ _ _)]
    rw [Finset.sum_congr rfl fun k _ => slab_measureReal j (hdiv _ _ (by linarith))]
    simp only [add_div, add_sub_cancel_left, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  · rw [fallStrips, measureReal_biUnion_finset hd2 (fun _ _ => hmb _ _)
      (fun _ _ => slab_ne_top _ _ _)]
    rw [Finset.sum_congr rfl fun k _ => slab_measureReal j (hdiv _ _ (by linarith))]
    simp only [add_div, add_sub_add_left_eq_sub, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    field_simp

theorem slab_isOpen (j : Fin m) (a b : ℝ) : IsOpen (slab j a b) :=
  isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

/-- On a rising strip, away from the boundary layer, the laminate is affine. -/
theorem coordLaminate_grad_rise (i : Fin d) (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1)
    {n k : ℕ}
    (hn : 0 < n) (hk : k < n) {s : ℝ} (hs : 0 < s) {x : Fin m → ℝ}
    (hx : x ∈ slab j (k / n) ((k + l) / n)) (hxd : s / n < infDist x (unitCube m)ᶜ) :
    grad (coordLaminate i j l n s) x = Matrix.single i j ((1 - l) * s) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hsub : slab j (k / n) ((k + l) / n) ⊆ unitCube m := slab_subset
    (div_nonneg (Nat.cast_nonneg k) hn'.le)
    (by rw [div_le_one hn']; have : (k : ℝ) + 1 ≤ n := (by exact_mod_cast hk); linarith)
  have hV : slab j (k / n) ((k + l) / n) ∩ {y | s / n < infDist y (unitCube m)ᶜ} ∈ 𝓝 x :=
    ((slab_isOpen j _ _).inter (isOpen_lt continuous_const
      (continuous_infDist_pt (unitCube m)ᶜ))).mem_nhds
      ⟨hx, hxd⟩
  have e : coordLaminate i j l n s =ᶠ[𝓝 x]
      fun y => (Pi.single i (((1 - l) * s) * (y j - k / n)) : Fin d → ℝ) := by
    filter_upwards [hV] with y hy
    have hyQ := hsub hy.1
    have hyj := slab_mem hy.1
    have hy01 : 0 ≤ y j ∧ y j ≤ 1 := ⟨(hyQ j (mem_univ j)).1.le, (hyQ j (mem_univ j)).2.le⟩
    have hsaw := sawN_eq_rise hl0 hl1 hn hk hyj.1.le hyj.2.le
    have hle := sawN_le hl0 hl1 hn hy01.1 hy01.2
    have hmin : min (s * sawN l n (y j)) (infDist y (unitCube m)ᶜ) = s * sawN l n (y j) := by
      refine min_eq_left (le_of_lt (lt_of_le_of_lt ?_ hy.2))
      calc s * sawN l n (y j) ≤ s * (1 / n) := mul_le_mul_of_nonneg_left hle hs.le
        _ = s / n := by ring
    simp only [coordLaminate]
    rw [hmin, hsaw]
    congr 1
    ring
  rw [cv_grad_congr e, cv_grad_single]

/-- On a falling strip, away from the boundary layer, the laminate is affine. -/
theorem coordLaminate_grad_fall (i : Fin d) (j : Fin m) {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1)
    {n k : ℕ}
    (hn : 0 < n) (hk : k < n) {s : ℝ} (hs : 0 < s) {x : Fin m → ℝ}
    (hx : x ∈ slab j ((k + l) / n) ((k + 1) / n)) (hxd : s / n < infDist x (unitCube m)ᶜ) :
    grad (coordLaminate i j l n s) x = Matrix.single i j (-l * s) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hsub : slab j ((k + l) / n) ((k + 1) / n) ⊆ unitCube m := slab_subset
    (div_nonneg (by positivity) hn'.le)
    (by rw [div_le_one hn']; have : (k : ℝ) + 1 ≤ n := (by exact_mod_cast hk); linarith)
  have hV : slab j ((k + l) / n) ((k + 1) / n) ∩ {y | s / n < infDist y (unitCube m)ᶜ} ∈ 𝓝 x :=
    ((slab_isOpen j _ _).inter (isOpen_lt continuous_const
      (continuous_infDist_pt (unitCube m)ᶜ))).mem_nhds
      ⟨hx, hxd⟩
  have e : coordLaminate i j l n s =ᶠ[𝓝 x]
      fun y => (Pi.single i ((-l * s) * (y j - (k + 1) / n)) : Fin d → ℝ) := by
    filter_upwards [hV] with y hy
    have hyQ := hsub hy.1
    have hyj := slab_mem hy.1
    have hy01 : 0 ≤ y j ∧ y j ≤ 1 := ⟨(hyQ j (mem_univ j)).1.le, (hyQ j (mem_univ j)).2.le⟩
    have hsaw := sawN_eq_fall hl0 hl1 hn hk hyj.1.le hyj.2.le
    have hle := sawN_le hl0 hl1 hn hy01.1 hy01.2
    have hmin : min (s * sawN l n (y j)) (infDist y (unitCube m)ᶜ) = s * sawN l n (y j) := by
      refine min_eq_left (le_of_lt (lt_of_le_of_lt ?_ hy.2))
      calc s * sawN l n (y j) ≤ s * (1 / n) := mul_le_mul_of_nonneg_left hle hs.le
        _ = s / n := by ring
    simp only [coordLaminate]
    rw [hmin, hsaw]
    congr 1
    ring
  rw [cv_grad_congr e, cv_grad_single]

/-- The boundary layer `{x ∈ Q : dist (x, Qᶜ) ≤ η}` has measure at most `2 m η`. -/
theorem cv_layer_measure (hm : 0 < m) {η : ℝ} (hη : 0 ≤ η) :
    volume.real {x | x ∈ unitCube m ∧ infDist x (unitCube m)ᶜ ≤ η} ≤ 2 * m * η := by
  have hQ1 : volume.real (unitCube m) = 1 := by
    rw [measureReal_def, cv_volume_unitCube, ENNReal.toReal_one]
  have hsub : {x | x ∈ unitCube m ∧ infDist x (unitCube m)ᶜ ≤ η} ⊆ unitCube m := fun x hx => hx.1
  have hQfin : volume (unitCube m) ≠ ⊤ := by rw [cv_volume_unitCube]; exact ENNReal.one_ne_top
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rcases le_or_gt (1 / 2) η with hη2 | hη2
  · calc volume.real {x | x ∈ unitCube m ∧ infDist x (unitCube m)ᶜ ≤ η}
        ≤ volume.real (unitCube m) := measureReal_mono hsub hQfin
      _ = 1 := hQ1
      _ ≤ 2 * m * η := by nlinarith
  · set c : Fin m → ℝ := fun _ => 1 / 2
    have hne : ((unitCube m)ᶜ).Nonempty := by
      refine ⟨fun _ => 2, fun h => ?_⟩
      have := (h ⟨0, hm⟩ (mem_univ _)).2
      norm_num at this
    have hsub2 : {x | x ∈ unitCube m ∧ infDist x (unitCube m)ᶜ ≤ η} ⊆
        unitCube m \ ball c (1 / 2 - η) := by
      intro x hx
      refine ⟨hx.1, fun hxb => ?_⟩
      have hlt : η < 1 / 2 - dist x c := by rw [mem_ball] at hxb; linarith
      have : infDist x (unitCube m)ᶜ < 1 / 2 - dist x c := lt_of_le_of_lt hx.2 hlt
      obtain ⟨y, hy, hxy⟩ := (infDist_lt_iff hne).1 this
      apply hy
      rw [cv_unitCube_eq_ball, mem_ball]
      calc dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
        _ < 1 / 2 := by rw [dist_comm]; linarith
    have hballQ : ball c (1 / 2 - η) ⊆ unitCube m := by
      rw [cv_unitCube_eq_ball]; exact ball_subset_ball (by linarith)
    calc volume.real {x | x ∈ unitCube m ∧ infDist x (unitCube m)ᶜ ≤ η}
        ≤ volume.real (unitCube m \ ball c (1 / 2 - η)) :=
          measureReal_mono hsub2 (ne_top_of_le_ne_top hQfin (measure_mono sdiff_subset))
      _ = 1 - (1 - 2 * η) ^ m := by
          rw [measureReal_sdiff hballQ measurableSet_ball hQfin, hQ1,
            cv_measureReal_ball c (by linarith)]
          ring_nf
      _ ≤ 2 * m * η := by
          have := one_add_le_pow_of_two_add_nonneg (a := -2 * η) (by linarith) m
          have e : (1 : ℝ) + -2 * η = 1 - 2 * η := by ring
          rw [e] at this
          nlinarith

/-- The integral of a function that equals `c₁` on `S₁` and `c₂` on `S₂` away from a set `B`. -/
theorem cv_laminate_integral {h : (Fin m → ℝ) → ℝ} {H c₁ c₂ l : ℝ}
    (hint : IntegrableOn h (unitCube m)) (hb : ∀ x, |h x| ≤ H)
    {S₁ S₂ B : Set (Fin m → ℝ)} (h1 : S₁ ⊆ unitCube m) (h2 : S₂ ⊆ unitCube m)
    (hm1 : MeasurableSet S₁) (hm2 : MeasurableSet S₂) (hmB : MeasurableSet B)
    (hBQ : B ⊆ unitCube m) (hd : Disjoint S₁ S₂) (hv1 : volume.real S₁ = l)
        (hv2 : volume.real S₂ = 1 - l)
    (he1 : ∀ x ∈ S₁, x ∉ B → h x = c₁) (he2 : ∀ x ∈ S₂, x ∉ B → h x = c₂) :
    ∫ x in unitCube m, h x ≤ l * c₁ + (1 - l) * c₂ + (2 * H + |c₁| + |c₂|) * volume.real B := by
  have hQfin : volume (unitCube m) ≠ ⊤ := by rw [cv_volume_unitCube]; exact ENNReal.one_ne_top
  have hQ1 : volume.real (unitCube m) = 1 := by
    rw [measureReal_def, cv_volume_unitCube, ENNReal.toReal_one]
  have hfin1 : volume S₁ ≠ ⊤ := ne_top_of_le_ne_top hQfin (measure_mono h1)
  have hfin2 : volume S₂ ≠ ⊤ := ne_top_of_le_ne_top hQfin (measure_mono h2)
  have h12 : S₁ ∪ S₂ ⊆ unitCube m := union_subset h1 h2
  have hnull : volume (unitCube m \ (S₁ ∪ S₂)) = 0 := by
    have hr : volume.real (unitCube m \ (S₁ ∪ S₂)) = 0 := by
      rw [measureReal_sdiff h12 (hm1.union hm2) hQfin, measureReal_union hd hm2 hfin1 hfin2, hQ1,
        hv1, hv2]
      ring
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hr
    exact hr.resolve_right (ne_top_of_le_ne_top hQfin (measure_mono sdiff_subset))
  have hH : 0 ≤ H := (abs_nonneg _).trans (hb 0)
  rw [← integral_inter_add_sdiff (hm1.union hm2) hint, inter_eq_right.2 h12,
    setIntegral_measure_zero _ hnull, add_zero,
    setIntegral_union hd hm2 (hint.mono_set h1) (hint.mono_set h2)]
  have hB : ∀ (S : Set (Fin m → ℝ)) (c : ℝ), S ⊆ unitCube m → MeasurableSet S →
      (∀ x ∈ S, x ∉ B → h x = c) →
      ∫ x in S, h x ≤ c * volume.real S + (H + |c|) * volume.real B := by
    intro S c hS hmS he
    have hfinS : volume S ≠ ⊤ := ne_top_of_le_ne_top hQfin (measure_mono hS)
    have hg : IntegrableOn (fun x => c + B.indicator (fun _ => H + |c|) x) S :=
      (integrableOn_const hfinS).add ((integrableOn_const (C := H + |c|) hfinS).indicator hmB)
    calc ∫ x in S, h x ≤ ∫ x in S, (c + B.indicator (fun _ => H + |c|) x) := by
          refine setIntegral_mono_on (hint.mono_set hS) hg hmS fun x hx => ?_
          by_cases hxB : x ∈ B
          · rw [indicator_of_mem hxB]
            have := (le_abs_self (h x)).trans (hb x)
            have := neg_abs_le c
            linarith
          · rw [indicator_of_notMem hxB, he x hx hxB, add_zero]
      _ = c * volume.real S + (H + |c|) * volume.real (S ∩ B) := by
          rw [integral_add (integrableOn_const hfinS)
            ((integrableOn_const (C := H + |c|) hfinS).indicator hmB),
            setIntegral_const, setIntegral_indicator hmB, setIntegral_const, smul_eq_mul,
            smul_eq_mul, mul_comm (volume.real S), mul_comm (volume.real (S ∩ B))]
      _ ≤ c * volume.real S + (H + |c|) * volume.real B := by
          have := measureReal_mono (μ := volume) (inter_subset_right (s := S) (t := B))
            (ne_top_of_le_ne_top hQfin (measure_mono hBQ))
          have h0 : 0 ≤ H + |c| := add_nonneg hH (abs_nonneg _)
          nlinarith
  have b1 := hB S₁ c₁ h1 hm1 he1
  have b2 := hB S₂ c₂ h2 hm2 he2
  rw [hv1] at b1
  rw [hv2] at b2
  linarith

theorem cv_trunc_abs_le {f : Matrix (Fin d) (Fin m) ℝ → ℝ} {A : Matrix (Fin d) (Fin m) ℝ}
    {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ) {ML : ℝ}
    (hML : ∀ X : Matrix (Fin d) (Fin m) ℝ, (∀ i k, |X i k| ≤ K) → |f (A + X)| ≤ ML) (N : ℝ)
    (x : Fin m → ℝ) : |(max (cubeInf f (A + grad φ x)) (N : EReal)).toReal| ≤ max |N| ML := by
  obtain ⟨-, h1, h2⟩ := cv_trunc f (A + grad φ x) N
  have h3 : f (A + grad φ x) ≤ ML := (le_abs_self _).trans (hML _ (cv_grad_abs_le hφ x))
  rw [abs_le]; constructor
  · have := neg_abs_le N; have := le_max_left |N| ML; linarith
  · calc _ ≤ max (f (A + grad φ x)) N := h2
      _ ≤ max ML |N| := max_le_max h3 (le_abs_self N)
      _ = max |N| ML := max_comm _ _

/-- **Laminates.** The convexity inequality of `cubeInf f` along a rank-one line `A + t E_{ij}`,
with truncated values:
`cubeInf f (A) ≤ λ max (cubeInf f (A + (1-λ) s E), N) + (1-λ) max (cubeInf f (A - λ s E), N)`. The
robust quasiconvexity applied to the laminates `coordLaminate` with `n` layers, whose gradient is
`(1-λ) s E` on the rising strips (measure `λ`) and `-λ s E` on the falling strips (measure `1-λ`)
off a boundary layer of measure `O(s/n)`. -/
theorem cubeInf_laminate {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) (i : Fin d) (j : Fin m) {l s : ℝ} (hl0 : 0 < l) (hl1 : l < 1)
    (hs : 0 < s) (N : ℝ) :
    cubeInf f A ≤ ((l * (max (cubeInf f (A + Matrix.single i j ((1 - l) * s))) (N : EReal)).toReal +
      (1 - l) * (max (cubeInf f (A + Matrix.single i j (-l * s)))
          (N : EReal)).toReal : ℝ) : EReal) := by
  have hm : 0 < m := j.pos
  set c₁ := (max (cubeInf f (A + Matrix.single i j ((1 - l) * s))) (N : EReal)).toReal with hc₁
  set c₂ := (max (cubeInf f (A + Matrix.single i j (-l * s))) (N : EReal)).toReal with hc₂
  obtain ⟨ML, -, hML⟩ := cv_bdd hf A (max s.toNNReal 1)
  set H := max |N| ML with hH
  have hH0 : 0 ≤ H := (abs_nonneg N).trans (le_max_left _ _)
  refine cv_ereal_le_of_eps (C := (2 * H + |c₁| + |c₂|) * (2 * m * s)) (by positivity)
    fun ε hε0 hε1 => ?_
  set n := ⌈1 / ε⌉₊ + 1 with hndef
  have hn : 0 < n := Nat.succ_pos _
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hnε : 1 / (n : ℝ) ≤ ε := by
    rw [div_le_iff₀ hn']
    have h1 : 1 / ε ≤ ⌈1 / ε⌉₊ := Nat.le_ceil _
    have h2 : (⌈1 / ε⌉₊ : ℝ) + 1 = n := by rw [hndef]; push_cast; ring
    rw [div_le_iff₀ hε0] at h1
    nlinarith
  set φ := coordLaminate i j l n s with hφdef
  have hφL := coordLaminate_lipschitz i j hl0 hl1 n hs
  have hadm : IsCubeTestMap φ := ⟨⟨_, hφL⟩, fun x hx => coordLaminate_eq_zero i j hl0 hl1 n hs hx⟩
  have hq := cubeInf_quasiconvex_robust hf A hadm N
  refine hq.trans (EReal.coe_le_coe_iff.2 ?_)
  have hb := cv_trunc_abs_le (f := f) (A := A) hφL (by simpa using hML) N
  have hQfin : volume (unitCube m) ≠ ⊤ := by rw [cv_volume_unitCube]; exact ENNReal.one_ne_top
  have hhint : IntegrableOn (fun x => (max (cubeInf f (A + grad φ x)) (N : EReal)).toReal)
      (unitCube m) :=
    Measure.integrableOn_of_bounded (M := H) hQfin
      (cv_measurable_trunc hf A φ N).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
  obtain ⟨hS1Q, hS2Q, hm1, hm2, hd, hv1, hv2⟩ := cv_strip_facts j hl0 hl1 hn
  set B := {x | x ∈ unitCube m ∧ infDist x (unitCube m)ᶜ ≤ s / n} with hBdef
  have hmB : MeasurableSet B := cv_measurableSet_unitCube.inter
    (measurableSet_le (continuous_infDist_pt (unitCube m)ᶜ).measurable measurable_const)
  have hBQ : B ⊆ unitCube m := fun x hx => hx.1
  have he1 : ∀ x ∈ riseStrips j l n, x ∉ B →
      (max (cubeInf f (A + grad φ x)) (N : EReal)).toReal = c₁ := by
    intro x hx hxB
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hx
    have hxd : s / n < infDist x (unitCube m)ᶜ := by
      by_contra h
      exact hxB ⟨hS1Q hx, not_lt.1 h⟩
    rw [hφdef, coordLaminate_grad_rise i j hl0 hl1 hn (Finset.mem_range.1 hk) hs hxk hxd]
  have he2 : ∀ x ∈ fallStrips j l n, x ∉ B →
      (max (cubeInf f (A + grad φ x)) (N : EReal)).toReal = c₂ := by
    intro x hx hxB
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hx
    have hxd : s / n < infDist x (unitCube m)ᶜ := by
      by_contra h
      exact hxB ⟨hS2Q hx, not_lt.1 h⟩
    rw [hφdef, coordLaminate_grad_fall i j hl0 hl1 hn (Finset.mem_range.1 hk) hs hxk hxd]
  have hint := cv_laminate_integral hhint hb hS1Q hS2Q hm1 hm2 hmB hBQ hd hv1 hv2 he1 he2
  have hBm := cv_layer_measure hm (η := s / n) (by positivity)
  have hC : 0 ≤ 2 * H + |c₁| + |c₂| := by positivity
  have h1 : 2 * (m : ℝ) * (s / n) ≤ 2 * m * s * ε := by
    have : s / n = s * (1 / n) := by ring
    rw [this]
    have hm0 : (0 : ℝ) ≤ 2 * m * s := by positivity
    nlinarith
  calc ∫ x in unitCube m, (max (cubeInf f (A + grad φ x)) (N : EReal)).toReal
      ≤ l * c₁ + (1 - l) * c₂ + (2 * H + |c₁| + |c₂|) * volume.real B := hint
    _ ≤ l * c₁ + (1 - l) * c₂ + (2 * H + |c₁| + |c₂|) * (2 * m * s * ε) := by
        gcongr
        exact hBm.trans h1
    _ = l * c₁ + (1 - l) * c₂ + (2 * H + |c₁| + |c₂|) * (2 * m * s) * ε := by ring

/-! ### The dichotomy, convexity along rank-one lines, continuity -/

theorem cv_single_shift (A : Matrix (Fin d) (Fin m) ℝ) (i : Fin d) (j : Fin m) {t₁ t₂ t : ℝ}
    (h : t₁ + t₂ = t) :
    A + Matrix.single i j t₁ + Matrix.single i j t₂ = A + Matrix.single i j t := by
  rw [add_assoc, ← Matrix.single_add, h]

theorem cv_smul_single (i : Fin d) (j : Fin m) (t : ℝ) :
    t • Matrix.single i j (1 : ℝ) = Matrix.single i j t := by
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

/-- If the convexity bound holds with one endpoint at `-∞`, then `cubeInf f (A) = -∞`. -/
theorem cv_bot_of_bound {f : Matrix (Fin d) (Fin m) ℝ → ℝ} {A X Y : Matrix (Fin d) (Fin m) ℝ}
    (hY : cubeInf f Y = ⊥)
    (h : ∀ N : ℝ, cubeInf f A ≤ ((1 / 2 * (max (cubeInf f X) (N : EReal)).toReal +
      (1 - 1 / 2) * (max (cubeInf f Y) (N : EReal)).toReal : ℝ) : EReal)) : cubeInf f A = ⊥ := by
  rw [EReal.eq_bot_iff_forall_lt]
  intro y
  set N := min (f X) (2 * y - f X - 2) with hN
  have hcX := (cv_trunc f X N).2.2
  have hY' : (max (cubeInf f Y) (N : EReal)).toReal = N := by
    rw [hY, max_eq_right bot_le, EReal.toReal_coe]
  have hmax : max (f X) N = f X := max_eq_left (min_le_left _ _)
  have := h N
  rw [hY'] at this
  refine this.trans_lt (EReal.coe_lt_coe_iff.2 ?_)
  have h2 : N ≤ 2 * y - f X - 2 := min_le_right _ _
  rw [hmax] at hcX
  linarith

/-- `-∞` propagates along the lines `B + t E_{ij}`. -/
theorem cubeInf_bot_line {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    {B : Matrix (Fin d) (Fin m) ℝ} (hB : cubeInf f B = ⊥) (i : Fin d) (j : Fin m) (t : ℝ) :
    cubeInf f (B + Matrix.single i j t) = ⊥ := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · refine cv_bot_of_bound (X := B + Matrix.single i j (2 * t)) (Y := B) hB fun N => ?_
    have := cubeInf_laminate hf (B + Matrix.single i j t) i j (l := 1 / 2) (s := -2 * t)
      (by norm_num) (by norm_num) (by linarith) N
    rw [cv_single_shift _ _ _ (show t + (1 - 1 / 2) * (-2 * t) = 0 by ring), Matrix.single_zero,
      add_zero, cv_single_shift _ _ _ (show t + -(1 / 2) * (-2 * t) = 2 * t by ring)] at this
    refine this.trans_eq ?_
    congr 1
    ring
  · simpa using hB
  · refine cv_bot_of_bound (X := B + Matrix.single i j (2 * t)) (Y := B) hB fun N => ?_
    have := cubeInf_laminate hf (B + Matrix.single i j t) i j (l := 1 / 2) (s := 2 * t)
      (by norm_num) (by norm_num) (by linarith) N
    rw [cv_single_shift _ _ _ (show t + (1 - 1 / 2) * (2 * t) = 2 * t by ring),
      cv_single_shift _ _ _ (show t + -(1 / 2) * (2 * t) = 0 by ring), Matrix.single_zero,
      add_zero] at this
    exact this

/-- **The dichotomy**: if `cubeInf f` takes the value `-∞`, it is `-∞` everywhere (changing one
entry at a time along rank-one lines). -/
theorem cubeInf_bot_all {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    {B : Matrix (Fin d) (Fin m) ℝ} (hB : cubeInf f B = ⊥) (A : Matrix (Fin d) (Fin m) ℝ) :
    cubeInf f A = ⊥ := by
  classical
  have key : ∀ S : Finset (Fin d × Fin m),
      cubeInf f (B + ∑ p ∈ S, Matrix.single p.1 p.2 ((A - B) p.1 p.2)) = ⊥ := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using hB
    | insert p S hp ih =>
      rw [Finset.sum_insert hp, add_comm (Matrix.single p.1 p.2 _), ← add_assoc]
      exact cubeInf_bot_line hf ih _ _ _
  have e : B + ∑ p : Fin d × Fin m, Matrix.single p.1 p.2 ((A - B) p.1 p.2) = A := by
    rw [Fintype.sum_prod_type, ← Matrix.matrix_eq_sum_single (A - B)]
    abel
  have := key Finset.univ
  rwa [e] at this

/-- The real-valued infimum formula, when it is finite. -/
noncomputable def cubeInfReal (f : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  (cubeInf f A).toReal

theorem cubeInf_eq_cubeInfReal {f : Matrix (Fin d) (Fin m) ℝ → ℝ} {A : Matrix (Fin d) (Fin m) ℝ}
    (h : cubeInf f A ≠ ⊥) : cubeInf f A = (cubeInfReal f A : EReal) :=
  (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) (cubeInf_le A)) h).symm

theorem cv_trunc_eq {f : Matrix (Fin d) (Fin m) ℝ → ℝ} {A : Matrix (Fin d) (Fin m) ℝ}
    (h : cubeInf f A ≠ ⊥) {N : ℝ} (hN : N ≤ cubeInfReal f A) :
    (max (cubeInf f A) (N : EReal)).toReal = cubeInfReal f A := by
  rw [cubeInf_eq_cubeInfReal h, max_eq_left (EReal.coe_le_coe_iff.2 hN), EReal.toReal_coe]

/-- The key inequality of convexity along a rank-one line, in the finite case. -/
theorem cubeInfReal_convex_ineq {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hfin : ∀ A, cubeInf f A ≠ ⊥) (A₀ : Matrix (Fin d) (Fin m) ℝ) (i : Fin d) (j : Fin m)
    {x y a b : ℝ} (hxy : x < y) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    cubeInfReal f (A₀ + (a * x + b * y) • Matrix.single i j 1) ≤
      a * cubeInfReal f (A₀ + x • Matrix.single i j 1) + b * cubeInfReal f
          (A₀ + y • Matrix.single i j 1) := by
  set N := min (cubeInfReal f (A₀ + x • Matrix.single i j 1))
      (cubeInfReal f (A₀ + y • Matrix.single i j 1))
  have hl := cubeInf_laminate hf (A₀ + (a * x + b * y) • Matrix.single i j 1) i j (l := b)
    (s := y - x) hb (by linarith) (by linarith) N
  rw [cv_smul_single, cv_single_shift _ _ _
      (show a * x + b * y + (1 - b) * (y - x) = y by
        rw [show 1 - b = a by linarith]; linear_combination y * hab),
    cv_single_shift _ _ _ (show a * x + b * y + -b * (y - x) = x by linear_combination x * hab),
    ← cv_smul_single i j y, ← cv_smul_single i j x,
    cv_trunc_eq (hfin _) (min_le_right _ _), cv_trunc_eq (hfin _) (min_le_left _ _)] at hl
  rw [← cv_smul_single i j, cubeInf_eq_cubeInfReal (hfin _), EReal.coe_le_coe_iff,
    show 1 - b = a by linarith] at hl
  linarith

theorem cubeInfReal_convexOn {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hfin : ∀ A, cubeInf f A ≠ ⊥) (A₀ : Matrix (Fin d) (Fin m) ℝ) (i : Fin d) (j : Fin m) :
    ConvexOn ℝ univ fun t : ℝ => cubeInfReal f (A₀ + t • Matrix.single i j 1) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · rcases lt_trichotomy x y with hxy | rfl | hxy
      · exact cubeInfReal_convex_ineq hf hfin A₀ i j hxy ha' hb' hab
      · rw [← add_mul, hab, one_mul, ← add_mul, hab, one_mul]
      · have := cubeInfReal_convex_ineq hf hfin A₀ i j hxy hb' ha' (by linarith)
        rw [add_comm (a * x), add_comm (a * cubeInfReal f _)]
        exact this
    · subst hb'
      have : a = 1 := by linarith
      subst this
      simp
  · subst ha'
    have : b = 1 := by linarith
    subst this
    simp

/-- In the finite case, `cubeInf f` is continuous (a separately convex function is locally
Lipschitz). -/
theorem cubeInfReal_continuous {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hfin : ∀ A, cubeInf f A ≠ ⊥) : Continuous (cubeInfReal f) := by
  exact (Matrix.locallyLipschitz_of_convexOn_single fun A i j =>
    cubeInfReal_convexOn hf hfin A i j).continuous

/-- In the finite case, `cubeInf f` is quasiconvex. -/
theorem cubeInfReal_quasiconvex {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hfin : ∀ A, cubeInf f A ≠ ⊥) : Quasiconvex (cubeInfReal f) := by
  intro A φ K hφ hφQ _
  have hc := cubeInfReal_continuous hf hfin
  obtain ⟨M, -, hM⟩ := cv_bdd hc A K
  have hq := cubeInf_quasiconvex_robust hf A ⟨⟨K, hφ⟩, hφQ⟩ (-M)
  have heq : ∀ x, (max (cubeInf f (A + grad φ x)) ((-M : ℝ) : EReal)).toReal = cubeInfReal f
      (A + grad φ x) :=
    fun x => cv_trunc_eq (hfin _) (by
      have := hM _ (cv_grad_abs_le hφ x); have := neg_abs_le
          (cubeInfReal f (A + grad φ x)); linarith)
  simp only [heq] at hq
  rw [cubeInf_eq_cubeInfReal (hfin A), EReal.coe_le_coe_iff] at hq
  rw [cv_volume_unitCube, ENNReal.toReal_one, one_mul]
  exact hq

/-- **`cubeInf f` is below the quasiconvex envelope**: either `cubeInf f ≡ -∞`, or it is a
continuous quasiconvex minorant of `f`. -/
theorem cubeInf_le_qcEnvelope {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) : cubeInf f A ≤ qcEnvelope f A := by
  by_cases hA : cubeInf f A = ⊥
  · rw [hA]; exact bot_le
  have hfin : ∀ B, cubeInf f B ≠ ⊥ := fun B hB => hA (cubeInf_bot_all hf hB A)
  have hc := cubeInfReal_continuous hf hfin
  have hadm : LowerSemicontinuous (cubeInfReal f) ∧ IsLocallyBounded (cubeInfReal f) ∧ Quasiconvex
      (cubeInfReal f) ∧
      ∀ B, cubeInfReal f B ≤ f B := by
    refine ⟨hc.lowerSemicontinuous, fun B => ?_, cubeInfReal_quasiconvex hf hfin, fun B => ?_⟩
    · refine ⟨cubeInfReal f ⁻¹' Metric.ball (cubeInfReal f B) 1, hc.continuousAt.preimage_mem_nhds
        (Metric.ball_mem_nhds _ one_pos), |cubeInfReal f B| + 1, fun C hC => ?_⟩
      rw [mem_preimage, Metric.mem_ball, Real.dist_eq] at hC
      have := abs_sub_abs_le_abs_sub (cubeInfReal f C) (cubeInfReal f B)
      linarith
    · have := cubeInf_le (f := f) B
      rw [cubeInf_eq_cubeInfReal (hfin B), EReal.coe_le_coe_iff] at this
      exact this
  rw [cubeInf_eq_cubeInfReal hA]
  exact le_iSup₂ (f := fun g (_ : LowerSemicontinuous g ∧ IsLocallyBounded g ∧ Quasiconvex g ∧
    ∀ B, g B ≤ f B) => (g A : EReal)) (cubeInfReal f) hadm

end CalculusOfVariations
