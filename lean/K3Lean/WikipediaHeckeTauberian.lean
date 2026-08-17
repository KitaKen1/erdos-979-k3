import K3Lean.AuditedWienerIkehara
import K3Lean.WikipediaHeckePositivity

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Applying the audited Wiener--Ikehara theorem

This file performs the purely formal subtraction needed by the Hecke route.
It takes the exact PrimeNumberTheorem+ Wiener--Ikehara statement, applies it
once with residue `2` and once with residue `1`, and obtains cancellation of
the real character coefficients.  No Tauberian conclusion is assumed in a
problem-specific form.
-/

namespace K3Lean.WikipediaHeckeTauberian

open Complex Filter Set Topology
open K3Lean.AuditedWienerIkehara
open K3Lean.WikipediaHeckePositivity
open scoped BigOperators Topology

/--
The two general Wiener--Ikehara applications imply cancellation after the
coefficient identity `positive = 2 * base + 2 * twist` is checked.
-/
theorem real_character_cancellation_from_pnt_plus
    (hWI : PNTPlusWienerIkehara)
    (base twist positive : Nat → Real)
    (hCoeff : ∀ n, positive n = 2 * base n + 2 * twist n)
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
    Tendsto (normalizedPartialSum twist) atTop (nhds 0) := by
  have hPositive := hWI 2 GPositive positive hPositiveNonneg
    hPositiveSummable hPositiveContinuous hPositiveEq
  have hBase := hWI 1 GBase base hBaseNonneg
    hBaseSummable hBaseContinuous hBaseEq
  apply real_character_cancellation_of_wiener_ikehara
    base twist positive hCoeff
  · change Tendsto
      (fun N => (∑ n ∈ Finset.range N, positive n) / (N : Real))
      atTop (nhds 2)
    simpa [K3Lean.AuditedWienerIkehara.cumsum] using hPositive
  · change Tendsto
      (fun N => (∑ n ∈ Finset.range N, base n) / (N : Real))
      atTop (nhds 1)
    simpa [K3Lean.AuditedWienerIkehara.cumsum] using hBase

#check @real_character_cancellation_from_pnt_plus
#print axioms real_character_cancellation_from_pnt_plus

end K3Lean.WikipediaHeckeTauberian
