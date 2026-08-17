import K3Lean.HeckeBoundaryToMoment
import K3Lean.TwoMomentHecke

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# The exact Hecke boundary needed for the first two moments

The logarithmic derivative of a Hecke Euler product contains prime powers.
Only its first-prime coefficient is visible after the checked prime-power and
log-weight removal.  At a split rational prime that coefficient is the real
part of the unitarized local character value, hence `cos (m * theta p)`; at
an inert prime there is no norm-`p` ideal and the coefficient is zero.
-/

namespace K3Lean.HeckeTwoMomentBoundary

open Filter
open K3Lean.AuditedWienerIkehara
open K3Lean.HeckeBoundaryToMoment
open K3Lean.HeckeCharacterCriterion
open K3Lean.HeckeCosineCancellation
open K3Lean.HeckeDeuringReduction
open K3Lean.LogWeightRemoval
open K3Lean.TwoMomentHecke
open scoped Topology

noncomputable section

/-- The prime coefficients of a rationally grouped Hecke logarithmic derivative. -/
def HasSplitPrimeCoefficients
    (theta : Nat -> Real) (m : Nat) (c : Nat -> Real) : Prop :=
  forall p : Nat, Nat.Prime p ->
    c p = splitCosineCoefficient theta m p

/--
Source-facing data for just the two powers used by the #979 argument.
The values on composite prime powers are left visible rather than silently
discarded: they must be bounded, and `HeckeLogDerivativeData` must identify
their full Dirichlet series with the L-function logarithmic derivative.
-/
def FirstTwoHeckeLBoundaryData (theta : Nat -> Real) : Prop :=
  exists c1 c2 : Nat -> Real,
    (forall n, |c1 n| <= 1) /\
    (forall n, |c2 n| <= 1) /\
    HasSplitPrimeCoefficients theta 1 c1 /\
    HasSplitPrimeCoefficients theta 2 c2 /\
    HeckeLogDerivativeData c1 /\
    HeckeLogDerivativeData c2

theorem unweightedPrimeSum_eq_of_splitPrimeCoefficients
    (theta : Nat -> Real) (m : Nat) (c : Nat -> Real)
    (hPrime : HasSplitPrimeCoefficients theta m c)
    (x : Real) :
    unweightedPrimeSum c x =
      unweightedPrimeSum (splitCosineCoefficient theta m) x := by
  rw [unweightedPrimeSum, unweightedPrimeSum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : Nat.Prime p
  · simp only [h, if_true]
    exact hPrime p h
  · simp [h]

theorem split_prime_unweighted_cancellation
    (hWI : PNTPlusWienerIkehara)
    (theta : Nat -> Real) (m : Nat) (c : Nat -> Real)
    (hc : forall n, |c n| <= 1)
    (hPrime : HasSplitPrimeCoefficients theta m c)
    (hData : HeckeLogDerivativeData c) :
    Tendsto
      (fun x : Real =>
        unweightedPrimeSum (splitCosineCoefficient theta m) x /
          (x / Real.log x))
      atTop (nhds 0) := by
  have h := unweighted_prime_sum_of_heckeLogDerivativeData hWI c hc hData
  simpa only [unweightedPrimeSum_eq_of_splitPrimeCoefficients theta m c hPrime] using h

/--
The general Hecke L-function boundary statement, used only at powers `1` and
`2`, gives exactly the two cosine moments consumed by the finite #979 proof.
-/
theorem firstTwoHeckeMoments_of_boundaryData
    (hWI : PNTPlusWienerIkehara)
    (theta : Nat -> Real)
    (hHecke : FirstTwoHeckeLBoundaryData theta)
    (hAP : PrimeNumberTheoremModThreeOne) :
    FirstTwoHeckeMoments theta := by
  rcases hHecke with
    ⟨c1, c2, hc1, hc2, hPrime1, hPrime2, hData1, hData2⟩
  constructor
  · exact cosineMoment_tendsto_of_unweighted theta 1
      (split_prime_unweighted_cancellation
        hWI theta 1 c1 hc1 hPrime1 hData1) hAP
  · exact cosineMoment_tendsto_of_unweighted theta 2
      (split_prime_unweighted_cancellation
        hWI theta 2 c2 hc2 hPrime2 hData2) hAP

#check @FirstTwoHeckeLBoundaryData
#check @firstTwoHeckeMoments_of_boundaryData
#print axioms firstTwoHeckeMoments_of_boundaryData

end

end K3Lean.HeckeTwoMomentBoundary
