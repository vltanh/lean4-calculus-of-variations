module

public meta import Lean.Elab.Command
-- One `import all` line per module of the library, so that proofs are visible to the axiom
-- traversal (the module system hides them from a plain `import`). Generate the lines with
--   find CalculusOfVariations -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g; s/^/import all /'
import all CalculusOfVariations.Basic
import all CalculusOfVariations.Convex.SeparatelyConvex
import all CalculusOfVariations.Covering.Cubes
import all CalculusOfVariations.Distribution.Convex
import all CalculusOfVariations.Distribution.SecondDerivative
import all CalculusOfVariations.Envelope.Convexity
import all CalculusOfVariations.Envelope.Cube
import all CalculusOfVariations.Envelope.Formula
import all CalculusOfVariations.Envelope.Glue
import all CalculusOfVariations.Envelope.Tangent
import all CalculusOfVariations.Lipschitz.Cutoff
import all CalculusOfVariations.Lipschitz.Gradient
import all CalculusOfVariations.Lipschitz.Mollify
import all CalculusOfVariations.Lipschitz.Periodic
import all CalculusOfVariations.Lipschitz.PiecewiseAffine
import all CalculusOfVariations.Lipschitz.Rescale
import all CalculusOfVariations.Lipschitz.ZeroSet
import all CalculusOfVariations.Minors.NullLagrangian
import all CalculusOfVariations.Minors.Quasiaffine
import all CalculusOfVariations.Minors.RankOneAffine
import all CalculusOfVariations.QuadraticForm.Plancherel
import all CalculusOfVariations.QuadraticForm.Quasiconvex
import all CalculusOfVariations.Quasiconvex.Domain
import all CalculusOfVariations.Quasiconvex.Laminate
import all CalculusOfVariations.Quasiconvex.Periodic
import all CalculusOfVariations.Quasiconvex.RankOneConvex
import all CalculusOfVariations.RankOneConvex.LocallyLipschitz
import all CalculusOfVariations.Smoothing.RankOneConvex

/-!
# Axiom audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

Prints the axioms on which the main theorems depend, then checks that they and every declaration
of the library, including private and auxiliary ones, depend only on Lean's standard axioms
`propext`, `Classical.choice` and `Quot.sound`. A `sorry` shows up as the axiom `sorryAx`.

While proofs are still open, `allowSorry` is `true`: the audit then lists the declarations whose
own proof contains a `sorry`, and fails only on other axioms. Set it to `false` before publishing,
so that any `sorry` fails the audit.
-/

open Lean Elab Command

namespace Audit

/-- The main theorems of the library. -/
meta def mainResults : List Name :=
  [``Matrix.locallyLipschitz_of_convexOn_single,
   ``CalculusOfVariations.RankOneConvex.locallyLipschitz,
   ``CalculusOfVariations.rankOneConvex_of_quasiconvex,
   ``CalculusOfVariations.quasiconvexAtOn_of_unitCube,
   ``CalculusOfVariations.quasiconvexAtOn_iff,
   ``CalculusOfVariations.quasiconvexAtOn_iff_periodic,
   ``CalculusOfVariations.quadraticForm_quasiconvex,
   ``CalculusOfVariations.RankOneAffine.exists_eq_sum_minor,
   ``CalculusOfVariations.nl_null2,
   ``CalculusOfVariations.nl_null3,
   ``CalculusOfVariations.nl_minor3_quasiaffine,
   ``CalculusOfVariations.qcEnvelope_eq_iInf_unitBall,
   ``CalculusOfVariations.Smoothing.exists_smoothing,
   -- stated, with `sorry` proofs for now
   ``CalculusOfVariations.le_of_quasiconvexAtOn_unitCube,
   ``CalculusOfVariations.le_of_quasiconvexAtOn_vecMulVec,
   ``CalculusOfVariations.lineDerivOp_ofFun_eq_ofFun_deriv,
   ``CalculusOfVariations.integral_deriv_deriv_mul_mul,
   ``CalculusOfVariations.ConvexOn.distribNonneg_lineDerivOp_lineDerivOp_ofFun,
   ``CalculusOfVariations.convexOn_of_distribNonneg,
   ``CalculusOfVariations.ae_tendsto_grad_mollifyPi,
   ``CalculusOfVariations.kuhnInterpolation_piecewiseAffineOn,
   ``CalculusOfVariations.ae_tendsto_grad_kuhnInterpolation,
   ``CalculusOfVariations.cubeInf_le_sum_of_piecewiseAffine,
   ``CalculusOfVariations.qcEnvelope_eq_iInf]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- While proofs are open, `sorryAx` is listed instead of rejected. Set to `false` before
publishing. -/
meta def allowSorry : Bool := true

/-- Whether `m` is a module of the library. -/
meta def isLibraryModule (m : Name) : Bool := (`CalculusOfVariations).isPrefixOf m

/-- The constants declared in the library. -/
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
  for n in mainResults do
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
    s!"\n\nChecked {library.size} declarations of the library: " ++
    (if bad.isEmpty then "no axioms beyond the standard ones" else "see the error") ++
    (if sorries.isEmpty then "; no `sorry`." else
      s!"; {sorries.size} contain a `sorry`:\n" ++ "\n".intercalate sorryRows))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#audit
