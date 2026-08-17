import K3Lean.HeckeTwoMomentBoundary
import K3Lean.HeckeEulerNonvanishing
import K3Lean.ExplicitFermatHecke
import K3Lean.CanonicalFermatEuler
import K3Lean.FermatDirichletCriterion
import K3Lean.TwoMomentFinal

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Exact Erdos 979 target from a Hecke L-function boundary theorem

This is the public composition point for the lower Hecke route.  The Hecke
input contains analytic L-function data, not CM Sato--Tate, sector abundance,
or a prime-moment conclusion.
-/

namespace K3Lean.HeckeBoundaryFinal

open Filter
open K3Lean.AuditedWienerIkehara
open K3Lean.CanonicalFermatEuler
open K3Lean.ExplicitFermatHecke
open K3Lean.FermatHasseAngle
open K3Lean.FormalConjecturesTarget
open K3Lean.FermatDirichletCriterion
open K3Lean.HeckeDeuringReduction
open K3Lean.HeckeEulerNonvanishing
open K3Lean.HeckeTwoMomentBoundary
open K3Lean.TwoMomentFinal
open K3Lean.WikipediaFermatHecke

noncomputable section

/-- The exact Formal Conjectures #979 target from two Hecke L-functions. -/
theorem erdos_979_k3_from_hecke_L_boundary
    (hHasse : FermatCubicHasseBound)
    (hWI : PNTPlusWienerIkehara)
    (hHecke : FirstTwoHeckeLBoundaryData fermatTraceAngle)
    (hAP : PrimeNumberTheoremModThreeOne) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  apply erdos_979_k3_from_first_two_hecke_moments hHasse
  · exact firstTwoHeckeMoments_of_boundaryData
      hWI fermatTraceAngle hHecke hAP
  · exact hAP

/--
Public endpoint with boundary nonvanishing removed from `hHecke`.  The Hecke
hypothesis now contains only the Euler-product family, Hecke holomorphy, and
the two elementary local/logarithmic-derivative identifications.
-/
theorem erdos_979_k3_from_holomorphic_hecke
    (hHasse : FermatCubicHasseBound)
    (hWI : PNTPlusWienerIkehara)
    (hHecke : FirstTwoHolomorphicHeckeData fermatTraceAngle)
    (hAP : PrimeNumberTheoremModThreeOne) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  exact erdos_979_k3_from_hecke_L_boundary hHasse hWI
    (firstTwoBoundaryData_of_holomorphicData fermatTraceAngle hHecke) hAP

/--
Public endpoint with the rational-prime coefficients and logarithmic
derivative removed from the Hecke hypothesis.  They are calculated from the
explicit split/inert Euler factors in `ExplicitFermatHecke`.
-/
theorem erdos_979_k3_from_explicit_hecke_euler_product
    (hHasse : FermatCubicHasseBound)
    (hWI : PNTPlusWienerIkehara)
    (hHecke : ExplicitFermatHeckeData fermatTraceAngle)
    (hAP : PrimeNumberTheoremModThreeOne) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  exact erdos_979_k3_from_holomorphic_hecke hHasse hWI
    hHecke.toFirstTwoHolomorphicHeckeData hAP

/--
Lowest current Hecke endpoint.  All local radii, phases, square identities,
prime-power coefficients, coefficient bounds, and logarithmic differentiation
are proved below this theorem; `hHecke` retains only the standard analytic
claims about the displayed Fermat Hecke Euler product.
-/
theorem erdos_979_k3_from_fermat_hecke_source
    (hHasse : FermatCubicHasseBound)
    (hWI : PNTPlusWienerIkehara)
    (hHecke : FermatHeckeSourceData fermatTraceAngle)
    (hAP : PrimeNumberTheoremModThreeOne) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  exact erdos_979_k3_from_explicit_hecke_euler_product hHasse hWI
    hHecke.toExplicitFermatHeckeData hAP

/-
Public endpoint after removing `power_euler_log` and the whole trivial factor
from the Hecke hypothesis.  Its only external analytic assertions are the
displayed Euler product for positive powers of the nontrivial Fermat Hecke
character and holomorphy of those powers.  Mathlib supplies the trivial
Dirichlet factors; Lean proves rational grouping and the logarithmic derivative.
-/
theorem erdos_979_k3_from_hecke_theorem
    (hHasse : FermatCubicHasseBound)
    (hWI : PNTPlusWienerIkehara)
    (hHecke : FermatHeckeTheorem fermatTraceAngle)
    (hAP : PrimeNumberTheoremModThreeOne) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  exact erdos_979_k3_from_holomorphic_hecke hHasse hWI
    hHecke.toFirstTwoHolomorphicHeckeData hAP

/-
Audit endpoint with the two logically different Hecke inputs exposed:
the Fermat-specific Euler-factor identification and the general analytic
continuation theorem for the resulting nontrivial Hecke L-functions.
-/
theorem erdos_979_k3_from_hecke_components
    (hHasse : FermatCubicHasseBound)
    (hWI : PNTPlusWienerIkehara)
    (hEuler : FermatHeckeEulerIdentification fermatTraceAngle)
    (hAnalytic : FermatHeckeAnalyticContinuation hEuler)
    (hAP : PrimeNumberTheoremModThreeOne) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  exact erdos_979_k3_from_hecke_theorem hHasse hWI
    (hEuler.withAnalyticContinuation hAnalytic) hAP

/-
The same endpoint with the artificial `hEuler` package removed.  The remaining
Hecke input says that powers `1`, `2`, and `4` of the explicit Fermat Euler
product extend holomorphically to `re s > 1/2`.
-/
theorem erdos_979_k3_from_fermat_euler_continuation
    (hHasse : FermatCubicHasseBound)
    (hWI : PNTPlusWienerIkehara)
    (hContinuation : FermatPowerEulerContinuation fermatTraceAngle)
    (hAP : PrimeNumberTheoremModThreeOne) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  let hEuler := identificationOfContinuation hContinuation
  exact erdos_979_k3_from_hecke_components hHasse hWI hEuler
    (analyticContinuationOfContinuation hContinuation) hAP

/-
The continuation is now constructed in Lean from concrete Dirichlet-series
models.  In particular, no holomorphic function or analytic continuation is
present in `hModels`; the analytic construction is the proved Mellin adapter.
-/
theorem erdos_979_k3_from_fermat_dirichlet_models
    (hHasse : FermatCubicHasseBound)
    (hWI : PNTPlusWienerIkehara)
    (hModels : FermatRequiredDirichletModels fermatTraceAngle)
    (hAP : PrimeNumberTheoremModThreeOne) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  exact erdos_979_k3_from_fermat_euler_continuation hHasse hWI
    (fermatPowerEulerContinuation_of_dirichletModels hModels) hAP

#check @erdos_979_k3_from_hecke_L_boundary
#print axioms erdos_979_k3_from_hecke_L_boundary
#check @erdos_979_k3_from_holomorphic_hecke
#print axioms erdos_979_k3_from_holomorphic_hecke
#check @erdos_979_k3_from_explicit_hecke_euler_product
#print axioms erdos_979_k3_from_explicit_hecke_euler_product
#check @erdos_979_k3_from_fermat_hecke_source
#print axioms erdos_979_k3_from_fermat_hecke_source
#check @erdos_979_k3_from_hecke_theorem
#print axioms erdos_979_k3_from_hecke_theorem
#check @erdos_979_k3_from_hecke_components
#print axioms erdos_979_k3_from_hecke_components
#check @erdos_979_k3_from_fermat_euler_continuation
#print axioms erdos_979_k3_from_fermat_euler_continuation
#check @erdos_979_k3_from_fermat_dirichlet_models
#print axioms erdos_979_k3_from_fermat_dirichlet_models

end

end K3Lean.HeckeBoundaryFinal
