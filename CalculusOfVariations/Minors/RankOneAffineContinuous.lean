/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Minors.RankOneAffine

/-!
# Continuous rank-one affine functions are affine combinations of minors

`RankOneAffine.exists_eq_sum_minor_of_continuous`: the case of a continuous `f` of
`RankOneAffine.exists_eq_sum_minor` (module `Minors.RankOneAffine`), the implication (ii) ⇒ (iii′)
of Theorem 5.20 (p. 179) of B. Dacorogna, *Direct Methods in the Calculus of Variations*, 2nd ed.,
Springer, 2008 ([D08]). [D08] states the theorem without continuity, and the hypothesis is not used.
-/

@[expose] public section

namespace CalculusOfVariations

variable {d m : ℕ}

/-- **A continuous rank-one affine function is an affine combination of minors**: the case of a
continuous `f` of `RankOneAffine.exists_eq_sum_minor` ([D08], Theorem 5.20 (p. 179), (ii) ⇒ (iii′),
which has no hypothesis of continuity). The continuity is not used. -/
theorem RankOneAffine.exists_eq_sum_minor_of_continuous {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (_hc : Continuous f) (hf : RankOneAffine f) :
    ∃ a : (k : ℕ) → (Fin k ↪o Fin d) → (Fin k ↪o Fin m) → ℝ,
      ∀ A, f A = ∑ k ∈ Finset.range (min d m + 1), ∑ r, ∑ c, a k r c * minor A r c :=
  hf.exists_eq_sum_minor

end CalculusOfVariations
