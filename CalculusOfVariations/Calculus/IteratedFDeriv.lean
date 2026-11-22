/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Data.List.FinRange
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Iterated derivatives of smooth functions

For `h : E → ℝ` on a real normed space `E`:

* `iterDirDeriv h [v₁, …, v_k] = ∂_{v₁} ⋯ ∂_{v_k} h`, the iterated directional derivative. For
  smooth `h` it does not depend on the order of the directions (`iterDirDeriv_perm`, from the
  symmetry of second derivatives), and it is the iterated Fréchet derivative
  (`iteratedFDeriv_eq_iterDirDeriv`); hence `D^k h (x)` is a symmetric `k`-linear map
  (`iteratedFDeriv_comp_perm_of_contDiff`; Mathlib states this for analytic functions).
* A symmetric continuous `k`-linear form `M` with `M (x, …, x) = 0` for every `x` vanishes
  (`eq_zero_of_symmetric_of_apply_diag_eq_zero`). This is Proposition 6.2 of S. Conti,
  G. Dolzmann, B. Kirchheim, S. Müller, *Sufficient conditions for the validity of the Cauchy–Born
  rule close to SO(n)*, J. Eur. Math. Soc. 8 (2006), 515–530, proved by their induction on `k`:
  for fixed `G`, `M' (F₁, …, F_k) = M (G, F₁, …, F_k)` satisfies
  `(k + 1) M' (F, …, F) = d/ds|_{s=0} M (F + s G, …, F + s G) = 0`. (They put `G` last, and start
  the induction at `k = 1`; here `G` is first, and the induction starts at `k = 0`.)
* Taylor's formula: a smooth `h` with `D^{n+1} h = 0` is
  `h (x) = ∑_{k ≤ n} D^k h (0) (x, …, x) / k!`
  (`eq_sum_iteratedFDeriv_of_iteratedFDeriv_eq_zero`), by Taylor's theorem with the Lagrange
  remainder for `t ↦ h (t x)`.
-/

@[expose] public section

open scoped ContDiff Nat
open Filter Topology

namespace CalculusOfVariations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The iterated directional derivative `iterDirDeriv h [v₁, …, v_k] = ∂_{v₁} ⋯ ∂_{v_k} h`
(`∂_{v₁}` taken last). -/
noncomputable def iterDirDeriv (h : E → ℝ) : List E → E → ℝ
  | [] => h
  | v :: l => fun x => fderiv ℝ (iterDirDeriv h l) x v

@[simp] lemma iterDirDeriv_nil (h : E → ℝ) : iterDirDeriv h [] = h := rfl

lemma iterDirDeriv_cons (h : E → ℝ) (v : E) (l : List E) :
    iterDirDeriv h (v :: l) = fun x => fderiv ℝ (iterDirDeriv h l) x v := rfl

/-- The iterated directional derivatives of a smooth function are smooth. -/
lemma contDiff_iterDirDeriv {h : E → ℝ} (hh : ContDiff ℝ ∞ h) :
    ∀ l : List E, ContDiff ℝ ∞ (iterDirDeriv h l)
  | [] => hh
  | v :: l => ((contDiff_iterDirDeriv hh l).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const

private lemma fderiv_fderiv_apply_const {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ g y v) x w = fderiv ℝ (fderiv ℝ g) x w v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

/-- The iterated directional derivatives of a smooth function do not depend on the order of the
directions: adjacent directions commute by the symmetry of second derivatives. -/
lemma iterDirDeriv_perm {h : E → ℝ} (hh : ContDiff ℝ ∞ h) {l₁ l₂ : List E}
    (p : l₁.Perm l₂) : iterDirDeriv h l₁ = iterDirDeriv h l₂ := by
  induction p with
  | nil => rfl
  | cons v _ ih => rw [iterDirDeriv_cons, ih, iterDirDeriv_cons]
  | swap v w l =>
    funext x
    simp only [iterDirDeriv_cons]
    have hg := contDiff_iterDirDeriv hh l
    rw [fderiv_fderiv_apply_const hg, fderiv_fderiv_apply_const hg]
    exact ((hg.contDiffAt).isSymmSndFDerivAt (by simp)) w v
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- For smooth `h`, `D^k h (x) (v₁, …, v_k) = ∂_{v₁} ⋯ ∂_{v_k} h (x)`. -/
lemma iteratedFDeriv_eq_iterDirDeriv {h : E → ℝ} (hh : ContDiff ℝ ∞ h) :
    ∀ (k : ℕ) (x : E) (v : Fin k → E), iteratedFDeriv ℝ k h x v = iterDirDeriv h (List.ofFn v) x
  | 0, x, v => by simp
  | k + 1, x, v => by
    rw [iteratedFDeriv_succ_apply_left, List.ofFn_succ, iterDirDeriv_cons]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k h) x :=
      hh.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _) x
    rw [← fderiv_continuousMultilinear_apply_const_apply hd]
    congr 2
    funext y
    exact iteratedFDeriv_eq_iterDirDeriv hh k y _

/-- The `k`-th derivative of a smooth function is symmetric. -/
theorem iteratedFDeriv_comp_perm_of_contDiff {h : E → ℝ} (hh : ContDiff ℝ ∞ h) {k : ℕ} (x : E)
    (v : Fin k → E) (σ : Equiv.Perm (Fin k)) :
    iteratedFDeriv ℝ k h x (v ∘ σ) = iteratedFDeriv ℝ k h x v := by
  rw [iteratedFDeriv_eq_iterDirDeriv hh, iteratedFDeriv_eq_iterDirDeriv hh,
    iterDirDeriv_perm hh (Equiv.Perm.ofFn_comp_perm σ v)]

/-- `∂_{l ++ l'} h = ∂_l (∂_{l'} h)`. -/
lemma iterDirDeriv_append (h : E → ℝ) (l l' : List E) :
    iterDirDeriv h (l ++ l') = iterDirDeriv (iterDirDeriv h l') l := by
  induction l with
  | nil => rfl
  | cons v l ih => rw [List.cons_append, iterDirDeriv_cons, ih, iterDirDeriv_cons]

/-- The iterated directional derivatives of `0` vanish. -/
lemma iterDirDeriv_zero (l : List E) : iterDirDeriv (0 : E → ℝ) l = 0 := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    rw [iterDirDeriv_cons, ih]
    funext x
    simp

/-- **A symmetric multilinear form that vanishes on the diagonal vanishes** (Conti–Dolzmann–
Kirchheim–Müller 2006, Proposition 6.2, by their induction on `k`; module docstring). -/
theorem eq_zero_of_symmetric_of_apply_diag_eq_zero :
    ∀ {k : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ),
      (∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → E), M (v ∘ σ) = M v) →
      (∀ x : E, M (fun _ => x) = 0) → M = 0
  | 0, M, _, hM => by
    ext v
    have : v = fun _ => (0 : E) := funext fun i => i.elim0
    simpa [this] using hM 0
  | k + 1, M, hsym, hM => by
    have key : ∀ G : E, M.curryLeft G = 0 := by
      intro G
      refine eq_zero_of_symmetric_of_apply_diag_eq_zero (M.curryLeft G)
        (fun σ w => ?_) (fun x => ?_)
      · simp only [ContinuousMultilinearMap.curryLeft_apply]
        have e : (Fin.cons G (w ∘ σ) : Fin (k + 1) → E) =
            (Fin.cons G w : Fin (k + 1) → E) ∘ Equiv.Perm.decomposeFin.symm (0, σ) := by
          ext i
          refine Fin.cases ?_ (fun i => ?_) i
          · simp [Equiv.Perm.decomposeFin_symm_apply_zero]
          · simp [Equiv.Perm.decomposeFin_symm_apply_succ]
        rw [e, hsym]
      · -- `(k + 1) M (G, x, …, x) = d/ds|_{s=0} M (x + s G, …, x + s G) = 0`
        simp only [ContinuousMultilinearMap.curryLeft_apply]
        have hd : HasDerivAt (fun s : ℝ => M (fun _ => x + s • G))
            (M.linearDeriv (fun _ => x + (0 : ℝ) • G) (fun _ => G)) 0 := by
          have h1 : HasDerivAt (fun s : ℝ => (fun _ : Fin (k + 1) => x + s • G))
              (fun _ => G) 0 := by
            refine hasDerivAt_pi.2 fun _ => ?_
            simpa using ((hasDerivAt_id (0 : ℝ)).smul_const G).const_add x
          exact (M.hasFDerivAt _).comp_hasDerivAt (0 : ℝ) h1
        have h0 : HasDerivAt (fun s : ℝ => M (fun _ => x + s • G)) 0 0 := by
          have : (fun s : ℝ => M (fun _ => x + s • G)) = fun _ => 0 := funext fun s => hM _
          rw [this]
          exact hasDerivAt_const _ _
        have hsum := hd.unique h0
        rw [ContinuousMultilinearMap.linearDeriv_apply] at hsum
        simp only [zero_smul, add_zero] at hsum
        have hterm : ∀ i : Fin (k + 1),
            M (Function.update (fun _ => x) i G) = M (Fin.cons G fun _ => x) := by
          intro i
          rw [← hsym (Equiv.swap 0 i)]
          congr 1
          ext j
          by_cases hj : j = 0
          · subst hj; simp
          · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj
            by_cases hji : j'.succ = i
            · subst hji
              simp [Equiv.swap_apply_right, Function.update_of_ne (Ne.symm hj)]
            · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hj hji,
                Function.update_of_ne hji]
              simp
        simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          at hsum
        have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
        push_cast at hsum
        exact (mul_eq_zero.1 hsum).resolve_left hk
    ext v
    rw [← Fin.cons_self_tail v, ← ContinuousMultilinearMap.curryLeft_apply, key]
    rfl

/-- Taylor's formula in one variable, for a smooth `g` with `g^{(n+1)} = 0`: Taylor's theorem
with the Lagrange remainder on `[0, 1]`. -/
lemma eq_sum_iteratedDeriv_of_iteratedDeriv_eq_zero {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {n : ℕ}
    (hn : ∀ t, iteratedDeriv (n + 1) g t = 0) :
    g 1 = ∑ k ∈ Finset.range (n + 1), iteratedDeriv k g 0 / k ! := by
  obtain ⟨t, -, ht⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := g) (x₀ := 0) (x := 1)
    (n := n) zero_ne_one (hg.contDiffOn.of_le (by exact_mod_cast le_top))
  rw [hn, zero_mul, zero_div, sub_eq_zero, taylor_within_apply] at ht
  rw [ht]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc zero_ne_one)
    (hg.contDiffAt.of_le (by exact_mod_cast le_top)) (by simp)]
  simp [div_eq_inv_mul]

/-- **Taylor's formula** for a smooth `h` with `D^{n+1} h = 0`:
`h (x) = ∑_{k ≤ n} D^k h (0) (x, …, x) / k!`, by the one-variable formula for `t ↦ h (t x)`. -/
theorem eq_sum_iteratedFDeriv_of_iteratedFDeriv_eq_zero {h : E → ℝ} (hh : ContDiff ℝ ∞ h)
    {n : ℕ} (hn : ∀ y, iteratedFDeriv ℝ (n + 1) h y = 0) (x : E) :
    h x = ∑ k ∈ Finset.range (n + 1), iteratedFDeriv ℝ k h 0 (fun _ => x) / k ! := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight x
  have hL : ∀ t : ℝ, L t = t • x := fun t => rfl
  have hD : ∀ (k : ℕ) (t : ℝ),
      iteratedDeriv k (h ∘ L) t = iteratedFDeriv ℝ k h (t • x) (fun _ => x) := by
    intro k t
    rw [iteratedDeriv_eq_iteratedFDeriv, L.iteratedFDeriv_comp_right hh t
      (by exact_mod_cast le_top)]
    simp [hL]
  have := eq_sum_iteratedDeriv_of_iteratedDeriv_eq_zero (hh.comp L.contDiff) (n := n)
    (fun t => by rw [hD, hn]; rfl)
  simpa [hD, hL] using this

end CalculusOfVariations
