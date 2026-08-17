import K3Lean.WikipediaFermatHecke

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Canonical packaging of the explicit Fermat Euler product

`FermatHeckeEulerIdentification` does not itself assert analytic continuation
or identify a pre-existing arithmetic L-function.  It only asks for a global
function whose values on `re s > 1` equal the already explicit Euler product.
The function below supplies that packaging without any external hypothesis.

All genuinely analytic content therefore belongs in the continuation theorem,
not in a separate `hEuler` assumption.
-/

namespace K3Lean.CanonicalFermatEuler

open Complex
open K3Lean.ExplicitFermatHecke
open K3Lean.FermatHasseAngle
open K3Lean.HeckeBoundaryToMoment
open K3Lean.HeckeEulerNonvanishing
open K3Lean.WikipediaFermatHecke

noncomputable section

/-- The explicit Euler product, given a value at every complex input by `tsum`. -/
def explicitFermatPowerL
    (theta : Nat -> Real) (m : Nat) (s : Complex) : Complex :=
  Complex.exp
    (∑' q : FermatEulerSlot,
      -Complex.log
        (1 - (fermatEulerRadius (s.re - 1) q : Complex) *
          fermatEulerLocalValue theta m s.im q))

/--
The mathematically meaningful remaining input: the explicit Euler products
for powers `1`, `2`, and `4` are holomorphic on `re s > 1 / 2`.  The
continuation is required to agree with the convergent product only on
`re s > 1`; no value is prescribed elsewhere.
-/
def FermatPowerEulerContinuation (theta : Nat -> Real) : Prop :=
  forall m : Nat, RequiredHeckePower m ->
    exists F : Complex -> Complex,
      DifferentiableOn Complex F heckeContinuationDomain /\
        forall s : Complex, 1 < s.re ->
          F s = explicitFermatPowerL theta m s

private noncomputable def continuedPowerL
    {theta : Nat -> Real} (h : FermatPowerEulerContinuation theta)
    (m : Nat) : Complex -> Complex := by
  classical
  exact if hm : RequiredHeckePower m then Classical.choose (h m hm)
    else explicitFermatPowerL theta m

private theorem continuedPowerL_eq_explicit
    {theta : Nat -> Real} (h : FermatPowerEulerContinuation theta)
    (m : Nat) (s : Complex) (hs : 1 < s.re) :
    continuedPowerL h m s = explicitFermatPowerL theta m s := by
  by_cases hm : RequiredHeckePower m
  · rw [continuedPowerL, dif_pos hm]
    exact (Classical.choose_spec (h m hm)).2 s hs
  · rw [continuedPowerL, dif_neg hm]

private theorem continuedPowerL_differentiable
    {theta : Nat -> Real} (h : FermatPowerEulerContinuation theta)
    (m : Nat) (hm : RequiredHeckePower m) :
    DifferentiableOn Complex (continuedPowerL h m) heckeContinuationDomain := by
  rw [continuedPowerL, dif_pos hm]
  exact (Classical.choose_spec (h m hm)).1

/-- A continuation theorem canonically supplies the old Euler package. -/
noncomputable def identificationOfContinuation
    {theta : Nat -> Real} (h : FermatPowerEulerContinuation theta) :
    FermatHeckeEulerIdentification theta where
  powerL := continuedPowerL h
  power_euler := by
    intro m t x hx
    have hs : 1 < (1 + (x : Complex) + Complex.I * (t : Complex)).re := by
      simpa using hx
    rw [continuedPowerL_eq_explicit h m _ hs]
    simp [explicitFermatPowerL]

/-- The same continuation theorem supplies the old analytic package. -/
theorem analyticContinuationOfContinuation
    {theta : Nat -> Real} (h : FermatPowerEulerContinuation theta) :
    FermatHeckeAnalyticContinuation (identificationOfContinuation h) := by
  intro m hm
  exact continuedPowerL_differentiable h m hm

/-- The Euler-identification package is definitional and needs no hypothesis. -/
def canonicalEulerIdentification
    (theta : Nat -> Real) : FermatHeckeEulerIdentification theta where
  powerL := explicitFermatPowerL theta
  power_euler := by
    intro m t x _hx
    simp [explicitFermatPowerL]

/-- In particular, the final theorem's former `hEuler` input is unconditional. -/
def fermatEulerIdentification :
    FermatHeckeEulerIdentification fermatTraceAngle :=
  canonicalEulerIdentification fermatTraceAngle

#check @explicitFermatPowerL
#check @FermatPowerEulerContinuation
#check @canonicalEulerIdentification
#check fermatEulerIdentification
#check @identificationOfContinuation
#check @analyticContinuationOfContinuation
#print axioms canonicalEulerIdentification
#print axioms fermatEulerIdentification
#print axioms identificationOfContinuation
#print axioms analyticContinuationOfContinuation

end

end K3Lean.CanonicalFermatEuler
