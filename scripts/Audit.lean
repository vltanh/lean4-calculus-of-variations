module

public meta import Lean.Elab.Command
-- One `import all` line per module of the library and per Solution of `palomar/`, so that proofs
-- are visible to the axiom traversal (the module system hides them from a plain `import`). Generate
-- the lines with
--   { find CalculusOfVariations -name '*.lean'; cd palomar && find . -name Solution.lean; } |
--     sed 's#^\./##; s/\.lean$//; s#/#.#g; s/^/import all /' | sort
-- No Challenge is imported: each holds a copy of definitions of the library.
import all CalculusOfVariations.Basic
import all CalculusOfVariations.Convex.SeparatelyConvex
import all CalculusOfVariations.Convex.SupportFunction
import all CalculusOfVariations.Covering.Cubes
import all CalculusOfVariations.Distribution.Convex
import all CalculusOfVariations.Distribution.SecondDerivative
import all CalculusOfVariations.Envelope.Convexity
import all CalculusOfVariations.Envelope.Cube
import all CalculusOfVariations.Envelope.Domain
import all CalculusOfVariations.Envelope.Formula
import all CalculusOfVariations.Envelope.Glue
import all CalculusOfVariations.Envelope.RankOneConvex
import all CalculusOfVariations.Lipschitz.Cutoff
import all CalculusOfVariations.Lipschitz.FDeriv
import all CalculusOfVariations.Lipschitz.FundamentalDomain
import all CalculusOfVariations.Lipschitz.Gradient
import all CalculusOfVariations.Lipschitz.GradientConstraint
import all CalculusOfVariations.Lipschitz.Mollify
import all CalculusOfVariations.Lipschitz.Periodic
import all CalculusOfVariations.Lipschitz.Periodize
import all CalculusOfVariations.Lipschitz.PiecewiseAffine
import all CalculusOfVariations.Lipschitz.Rescale
import all CalculusOfVariations.Lipschitz.ZeroSet
import all CalculusOfVariations.Minors.AllOrders
import all CalculusOfVariations.Minors.Characterization
import all CalculusOfVariations.Minors.NullLagrangian
import all CalculusOfVariations.Minors.Periodic
import all CalculusOfVariations.Minors.Quasiaffine
import all CalculusOfVariations.Minors.RankOneAffine
import all CalculusOfVariations.QuadraticForm.Plancherel
import all CalculusOfVariations.QuadraticForm.Quasiconvex
import all CalculusOfVariations.Quasiconvex.Cutoff
import all CalculusOfVariations.Quasiconvex.Domain
import all CalculusOfVariations.Quasiconvex.Laminate
import all CalculusOfVariations.Quasiconvex.Periodic
import all CalculusOfVariations.Quasiconvex.RankOneConvex
import all CalculusOfVariations.Quasiconvex.TruncatedLaminate
import all CalculusOfVariations.RankOneConvex.LocallyLipschitz
import all CalculusOfVariations.RankOneConvex.SingularValues
import all CalculusOfVariations.Smoothing.RankOneConvex
import all NullLagrangians.Solution
import all QuasiconvexEnvelope.Solution
import all Quasiconvexity.Solution

/-!
# Axiom audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

Prints the axioms on which the main theorems depend, then checks that they and every declaration
of the library and of the Solutions in `palomar/`, including private and auxiliary ones, depend
only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. A `sorry` shows up as
the axiom `sorryAx`. (The Challenges in `palomar/`, whose theorems are stated with `sorry`, are not
imported.)

`allowSorry` is `false`, so that any `sorry` fails the audit. While proofs are open it may be set
to `true`: the audit then lists the declarations whose own proof contains a `sorry`, and fails only
on other axioms.
-/

open Lean Elab Command

namespace Audit

/-- The main theorems of the library. -/
meta def mainResults : List Name :=
  [``Matrix.exists_abs_le_of_convexOn_single,
   ``Matrix.locallyLipschitz_of_convexOn_single,
   ``Matrix.exists_singularValueDecomposition,
   ``CalculusOfVariations.RankOneConvex.abs_sub_le_of_osc,
   ``CalculusOfVariations.RankOneConvex.locallyLipschitz,
   ``CalculusOfVariations.rankOneConvex_of_quasiconvex,
   ``CalculusOfVariations.quasiconvexAtOn_of_unitCube,
   ``CalculusOfVariations.quasiconvexAtOn_iff,
   ``CalculusOfVariations.quasiconvexAtOn_iff_periodic,
   ``CalculusOfVariations.quadraticForm_quasiconvex,
   ``CalculusOfVariations.quadraticForm_quasiconvex_iff,
   ``CalculusOfVariations.RankOneAffine.exists_eq_sum_minor,
   ``CalculusOfVariations.setIntegral_minor_add_grad,
   ``CalculusOfVariations.rankOneAffine_tfae,
   ``CalculusOfVariations.nl_null2,
   ``CalculusOfVariations.nl_null3,
   ``CalculusOfVariations.nl_minor3_quasiaffine,
   ``CalculusOfVariations.qcEnvelope_eq_iInf_unitBall,
   ``CalculusOfVariations.Smoothing.exists_smoothing,
   ``CalculusOfVariations.le_of_quasiconvexAtOn_of_tendsto,
   ``CalculusOfVariations.le_of_quasiconvexAtOn_unitCube_of_measurable,
   ``CalculusOfVariations.le_of_quasiconvexAtOn_unitCube,
   ``CalculusOfVariations.le_of_quasiconvexAtOn_orthogonal,
   ``CalculusOfVariations.le_of_quasiconvexAtOn_vecMulVec,
   ``CalculusOfVariations.lineDerivOp_lineDerivOp_ofFun_apply,
   ``CalculusOfVariations.lineDerivOp_ofFun_eq_ofFun_deriv,
   ``CalculusOfVariations.integral_deriv_deriv_mul_mul,
   ``CalculusOfVariations.lineDerivOp_lineDerivOp_ofFun_mul_apply,
   ``CalculusOfVariations.ConvexOn.distribNonneg_lineDerivOp_lineDerivOp_ofFun,
   ``CalculusOfVariations.convexOn_of_distribNonneg,
   ``CalculusOfVariations.plancherelMollify_lipschitzWith,
   ``CalculusOfVariations.ae_tendsto_grad_mollifyPi,
   ``CalculusOfVariations.kuhnInterpolation_lipschitz,
   ``CalculusOfVariations.kuhnInterpolation_piecewiseAffineOn,
   ``CalculusOfVariations.kuhnInterpolation_grad_uniform,
   ``CalculusOfVariations.exists_testMap_setIntegral_eq,
   ``CalculusOfVariations.domainInf_le_domainInf,
   ``CalculusOfVariations.domainInf_eq,
   ``CalculusOfVariations.cubeInf_le_sum_of_piecewiseAffine,
   ``CalculusOfVariations.cubeInf_le_two_point,
   ``CalculusOfVariations.cubeInf_comp_orthogonal,
   ``CalculusOfVariations.cubeInf_le_two_point_vecMulVec,
   ``CalculusOfVariations.cubeInfReal_rankOneConvex,
   ``CalculusOfVariations.cubeInfReal_quasiconvex,
   ``CalculusOfVariations.cubeInf_le_qcEnvelope,
   ``CalculusOfVariations.qcEnvelope_eq_iInf,
   ``CalculusOfVariations.quasiconvexEnvelope_eq_qcEnvelope,
   ``CalculusOfVariations.quasiconvexEnvelope_eq_domainInf,
   ``CalculusOfVariations.domainInf_eq_of_isBounded,
   ``CalculusOfVariations.domainInf_le_of_rank_le_one,
   ``CalculusOfVariations.exists_domainInf_eq_coe,
   ``CalculusOfVariations.setIntegral_unitCube_fderiv_eq_zero,
   ``CalculusOfVariations.setIntegral_unitCube_grad_eq_zero,
   ``CalculusOfVariations.setIntegral_unitCube_det_add_grad,
   ``CalculusOfVariations.setIntegral_unitCube_comp_add,
   ``CalculusOfVariations.ae_of_ae_restrict_unitCube_of_periodic,
   ``CalculusOfVariations.mem_of_forall_dotProduct_le_supportFun,
   ``CalculusOfVariations.gradient_supportFun_mem,
   ``CalculusOfVariations.sub_add_dotProduct_le_supportFun_of_ae_mem,
   ``CalculusOfVariations.add_fderiv_mem_of_sub_add_dotProduct_le_supportFun,
   ``CalculusOfVariations.exists_lipschitzWith_of_sub_add_dotProduct_le_supportFun,
   ``CalculusOfVariations.exists_tendsto_of_ae_restrict_unitCube_tendsto,
   ``CalculusOfVariations.ae_fderiv_max_eq_or,
   ``CalculusOfVariations.tendsto_setIntegral_slope_mul,
   ``CalculusOfVariations.lipschitzWith_supPeriodize]

/-- The theorems of the Challenges in `palomar/`, as proved in the Solutions. -/
meta def solutionResults : List Name :=
  [``QuasiconvexityChallenge.rankOneConvex_locallyLipschitz,
   ``QuasiconvexityChallenge.rankOneConvex_abs_sub_le_of_osc,
   ``QuasiconvexityChallenge.rankOneConvex_of_quasiconvex,
   ``QuasiconvexityChallenge.quasiconvexAtOn_iff_of_isBounded,
   ``QuasiconvexityChallenge.quasiconvexAtOn_unitCube_iff_periodic,
   ``QuasiconvexityChallenge.quadraticForm_quasiconvex_iff,
   ``QuasiconvexityChallenge.integrableOn_add_grad,
   ``QuasiconvexEnvelopeChallenge.quasiconvexEnvelope_eq_domainInf,
   ``QuasiconvexEnvelopeChallenge.domainInf_eq_of_isBounded,
   ``QuasiconvexEnvelopeChallenge.domainInf_le_of_rank_le_one,
   ``QuasiconvexEnvelopeChallenge.exists_domainInf_eq_coe,
   ``NullLagrangiansChallenge.setIntegral_minor_add_grad,
   ``NullLagrangiansChallenge.rankOneAffine_tfae]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `sorryAx` is listed instead of rejected (only while proofs are open). -/
meta def allowSorry : Bool := false

/-- Whether `m` is a module of the library or a Solution of `palomar/`. -/
meta def isLibraryModule (m : Name) : Bool :=
  [`CalculusOfVariations, `Quasiconvexity, `QuasiconvexEnvelope, `NullLagrangians].any
    (·.isPrefixOf m)

/-- The constants declared in the library and in the Solutions. -/
meta def libraryConstants (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      out := out ++ d.constNames
  return out

/-- Whether the proof or body of `c` itself contains `sorryAx`. -/
meta def hasOwnSorry (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some ci => match ci.value? (allowOpaque := true) with
    | some v => v.getUsedConstants.contains ``sorryAx
    | none => false
  | none => false

/-- Whether the axioms `axs` are acceptable. -/
meta def acceptable (axs : Array Name) : Bool :=
  axs.all fun a => standardAxioms.contains a || (allowSorry && a == ``sorryAx)

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let mut rows : Array String := #[]
  for n in mainResults ++ solutionResults do
    let axs ← liftCoreM <| collectAxioms n
    unless acceptable axs do bad := bad.push n
    rows := rows.push s!"{n}: {axs.toList}"
  let library := libraryConstants env
  let mut sorries : Array Name := #[]
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    unless acceptable axs do bad := bad.push c
    if hasOwnSorry env c then sorries := sorries.push c
  let sorryRows := sorries.qsort (·.toString < ·.toString) |>.toList.map (s!"  {·}")
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library and the Solutions: " ++
    (if bad.isEmpty then "no axioms beyond the standard ones" else "see the error") ++
    (if sorries.isEmpty then "; no `sorry`." else
      s!"; {sorries.size} contain a `sorry`:\n" ++ "\n".intercalate sorryRows))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#audit
