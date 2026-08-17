import K3Lean.LogWeightRemoval
import K3Lean.WikipediaHeckeTauberian

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# From an audited Tauberian input to unweighted prime moments

This file composes the checked adapters:

1. the PrimeNumberTheorem+ Wiener--Ikehara statement;
2. subtraction of the untwisted logarithmic derivative;
3. removal of higher prime powers;
4. Abel removal of logarithmic weights.

The output is still completely generic in the bounded real local coefficient
`c`; no CM or Fermat-cubic fact is assumed here.
-/

namespace K3Lean.HeckeMomentAdapters

open ArithmeticFunction Complex Filter Set Topology
open K3Lean.AuditedWienerIkehara
open K3Lean.LogWeightRemoval
open K3Lean.PrimePowerRemoval
open K3Lean.WikipediaHeckePositivity
open K3Lean.WikipediaHeckeTauberian
open scoped BigOperators Topology

noncomputable section

/-- The three elementary adapters after a discrete prime-power cancellation limit. -/
theorem unweighted_prime_sum_of_discrete_cancellation
    (c : Nat → Real) (C : Real) (hC : 0 ≤ C)
    (hc : ∀ n, |c n| ≤ C)
    (hDiscrete : Tendsto
      (normalizedPartialSum (fun n => c n * vonMangoldt n))
      atTop (nhds 0)) :
    Tendsto
      (fun x => unweightedPrimeSum c x / (x / Real.log x))
      atTop (nhds 0) := by
  have hRange : Tendsto
      (fun N : Nat =>
        (∑ n ∈ Finset.range N, c n * vonMangoldt n) / (N : Real))
      atTop (nhds 0) := by
    change Tendsto
      (fun N : Nat =>
        (∑ n ∈ Finset.range N, c n * vonMangoldt n) / (N : Real))
      atTop (nhds 0) at hDiscrete
    exact hDiscrete
  have hPsi := twistedPsi_normalized_tendsto_zero_of_sum_range c hRange
  have hTheta := twistedTheta_normalized_tendsto_zero c C hC hc hPsi
  have hWeighted : Tendsto
      (fun x => weightedPrimeSum c x / x) atTop (nhds 0) := by
    simpa only [weightedPrimeSum_eq_twistedTheta] using hTheta
  exact unweightedPrimeSum_normalized_tendsto_zero c C hC hc hWeighted

/--
The full bridge from the audited PNT+ theorem and two analytic Dirichlet-series
continuations to an unweighted prime sum.  The `positive` coefficients have
residue `2`, the `base` coefficients have residue `1`, and their difference is
the twisted von Mangoldt sequence.
-/
theorem unweighted_prime_sum_from_pnt_plus
    (hWI : PNTPlusWienerIkehara)
    (c : Nat → Real) (C : Real) (hC : 0 ≤ C)
    (hc : ∀ n, |c n| ≤ C)
    (base positive : Nat → Real)
    (hCoeff : ∀ n,
      positive n = 2 * base n + 2 * (c n * vonMangoldt n))
    (hPositiveNonneg : 0 ≤ positive)
    (hPositiveSummable : ∀ sigma : Real, 1 < sigma →
      Summable (nterm (fun n => (positive n : Complex)) sigma))
    (GPositive : Complex → Complex)
    (hPositiveContinuous : ContinuousOn GPositive {s | 1 ≤ s.re})
    (hPositiveEq : Set.EqOn GPositive
      (fun s => LSeries (fun n => (positive n : Complex)) s -
        (2 : Complex) / (s - 1))
      {s | 1 < s.re})
    (hBaseNonneg : 0 ≤ base)
    (hBaseSummable : ∀ sigma : Real, 1 < sigma →
      Summable (nterm (fun n => (base n : Complex)) sigma))
    (GBase : Complex → Complex)
    (hBaseContinuous : ContinuousOn GBase {s | 1 ≤ s.re})
    (hBaseEq : Set.EqOn GBase
      (fun s => LSeries (fun n => (base n : Complex)) s -
        (1 : Complex) / (s - 1))
      {s | 1 < s.re}) :
    Tendsto
      (fun x => unweightedPrimeSum c x / (x / Real.log x))
      atTop (nhds 0) := by
  have hDiscrete := real_character_cancellation_from_pnt_plus
    hWI base (fun n => c n * vonMangoldt n) positive hCoeff
      hPositiveNonneg hPositiveSummable GPositive
      hPositiveContinuous hPositiveEq
      hBaseNonneg hBaseSummable GBase hBaseContinuous hBaseEq
  exact unweighted_prime_sum_of_discrete_cancellation c C hC hc hDiscrete

#check @unweighted_prime_sum_of_discrete_cancellation
#print axioms unweighted_prime_sum_of_discrete_cancellation
#check @unweighted_prime_sum_from_pnt_plus
#print axioms unweighted_prime_sum_from_pnt_plus

end

end K3Lean.HeckeMomentAdapters
