import K3Lean.FermatBaseEuler

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# A source-facing Fermat Hecke package

The source fields below are only the two analytic assertions in the standard
theorem for the *nontrivial* Fermat Hecke character: its displayed Euler
product and holomorphy of every positive character power.  The trivial factor
is constructed from Mathlib Dirichlet L-functions in `FermatBaseEuler`.  The
equality between the Euler logarithm and the rationally grouped `LSeries` is
proved in `FermatEulerLogGrouping`; neither fact is an external field.
-/

namespace K3Lean.WikipediaFermatHecke

open Asymptotics Complex Filter Set Topology
open K3Lean.ExplicitFermatHecke
open K3Lean.FermatBaseEuler
open K3Lean.HeckeBoundaryToMoment
open K3Lean.HeckeEulerNonvanishing
open scoped Topology

noncomputable section

/--
The arithmetic identification of the nontrivial Fermat-cubic L-functions with
the displayed rational-prime Euler products.  This is distinct from the
general analytic-continuation theorem for Hecke L-functions.
-/
structure FermatHeckeEulerIdentification (theta : Nat -> Real) where
  powerL : Nat -> Complex -> Complex
  power_euler : forall m : Nat, forall t x : Real, 0 < x ->
    powerL m (1 + x + Complex.I * t) =
      Complex.exp
        (∑' q : FermatEulerSlot,
          -Complex.log
            (1 - (fermatEulerRadius x q : Complex) *
              fermatEulerLocalValue theta m t q))

/-- The analytic-continuation consequence needed from the general Hecke theorem. -/
def FermatHeckeAnalyticContinuation
    {theta : Nat -> Real} (D : FermatHeckeEulerIdentification theta) : Prop :=
  forall m : Nat, RequiredHeckePower m ->
    DifferentiableOn Complex (D.powerL m) heckeContinuationDomain

/--
The two remaining Hecke inputs, packaged together for the compatibility route.
There is no trivial-factor, coefficient, logarithmic-derivative,
boundary-nonvanishing, or cancellation field here; Lean and Mathlib derive
those below.
-/
structure FermatHeckeTheorem (theta : Nat -> Real)
    extends FermatHeckeEulerIdentification theta where
  power_holomorphic : forall m : Nat, RequiredHeckePower m ->
    DifferentiableOn Complex (powerL m) heckeContinuationDomain

namespace FermatHeckeEulerIdentification

/-- Combine the arithmetic Euler identification with the general analytic theorem. -/
def withAnalyticContinuation
    {theta : Nat -> Real} (D : FermatHeckeEulerIdentification theta)
    (h : FermatHeckeAnalyticContinuation D) : FermatHeckeTheorem theta :=
  { toFermatHeckeEulerIdentification := D
    power_holomorphic := h }

end FermatHeckeEulerIdentification

namespace FermatHeckeTheorem

/-- The grouped Euler-log identity follows from the displayed Euler product. -/
theorem power_euler_log
    {theta : Nat -> Real} (D : FermatHeckeTheorem theta)
    (m : Nat) (s : Complex) (hs : 1 < s.re) :
    D.powerL m s =
      Complex.exp
        (LSeries (fermatHeckeEulerLogCoefficient theta m) s) := by
  let x : Real := s.re - 1
  let t : Real := s.im
  have hx : 0 < x := sub_pos.mpr hs
  have hsForm : (1 + (x : Complex) + Complex.I * (t : Complex)) = s := by
    apply Complex.ext
    · simp [x]
    · simp [t]
  rw [← hsForm, D.power_euler m t x hx]
  rw [fermatEulerLog_eq_LSeries theta m t x hx]

/-- Add the Mathlib-proved trivial factor to the nontrivial Hecke theorem. -/
def toFermatHeckeSourceData
    {theta : Nat -> Real} (D : FermatHeckeTheorem theta) :
    FermatHeckeSourceData theta :=
    { baseL := fermatBaseL
      powerL := D.powerL
      base_euler := fermatBaseL_euler
      power_euler := D.power_euler
      base_simple_pole := fermatBaseL_simple_pole
      power_holomorphic := D.power_holomorphic
      power_euler_log := D.power_euler_log }

/-- Compatibility adapter to the previously proved generic zero-free route. -/
def toExplicitFermatHeckeData
    {theta : Nat -> Real} (D : FermatHeckeTheorem theta) :
    ExplicitFermatHeckeData theta :=
  D.toFermatHeckeSourceData.toExplicitFermatHeckeData

/-- The standard source theorem supplies the first two Hecke moments package. -/
theorem toFirstTwoHolomorphicHeckeData
    {theta : Nat -> Real} (D : FermatHeckeTheorem theta) :
    FirstTwoHolomorphicHeckeData theta :=
  D.toExplicitFermatHeckeData.toFirstTwoHolomorphicHeckeData

end FermatHeckeTheorem

#check @FermatHeckeTheorem
#check @FermatHeckeEulerIdentification
#check @FermatHeckeAnalyticContinuation
#check @FermatHeckeEulerIdentification.withAnalyticContinuation
#check @FermatHeckeTheorem.power_euler_log
#check @FermatHeckeTheorem.toFermatHeckeSourceData
#check @FermatHeckeTheorem.toFirstTwoHolomorphicHeckeData
#print axioms FermatHeckeTheorem.power_euler_log
#print axioms FermatHeckeTheorem.toFermatHeckeSourceData
#print axioms FermatHeckeTheorem.toFirstTwoHolomorphicHeckeData

end


end K3Lean.WikipediaFermatHecke
