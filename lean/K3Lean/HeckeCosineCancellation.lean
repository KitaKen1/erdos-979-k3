import K3Lean.HeckeCharacterCriterion
import K3Lean.HeckeMomentAdapters

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Normalizing unweighted split-prime sums

This file identifies a generic unweighted prime sum with the numerator of the
split-prime cosine moment and divides by the PNT in the progression `1 mod 3`.
-/

namespace K3Lean.HeckeCosineCancellation

open Filter
open K3Lean.HeckeCharacterCriterion
open K3Lean.HeckeDeuringReduction
open K3Lean.LogWeightRemoval
open scoped BigOperators Topology

noncomputable section

/-- Cosine coefficient supported on rational primes that split in `Q(sqrt(-3))`. -/
def splitCosineCoefficient (theta : Nat → Real) (m n : Nat) : Real :=
  if Nat.Prime n ∧ n % 3 = 1 then Real.cos ((m : Real) * theta n) else 0

theorem abs_splitCosineCoefficient_le_one
    (theta : Nat → Real) (m n : Nat) :
    |splitCosineCoefficient theta m n| ≤ 1 := by
  rw [splitCosineCoefficient]
  split_ifs
  · exact Real.abs_cos_le_one _
  · norm_num

/-- The generic prime sum is exactly the numerator of `cosineMoment`. -/
theorem unweightedPrimeSum_splitCosineCoefficient
    (theta : Nat → Real) (m X : Nat) :
    unweightedPrimeSum (splitCosineCoefficient theta m) (X : Real) =
      ∑ p ∈ splitPrimesUpTo X, Real.cos ((m : Real) * theta p) := by
  rw [unweightedPrimeSum, splitPrimesUpTo, Nat.range_succ_eq_Icc_zero,
    Finset.sum_filter]
  simp only [Nat.floor_natCast, splitCosineCoefficient]
  refine Finset.sum_congr rfl fun p hp => ?_
  by_cases hprime : Nat.Prime p <;> by_cases hmod : p % 3 = 1 <;>
    simp [hprime, hmod]

/--
An `o(x / log x)` split-prime cosine numerator, divided by the PNT denominator,
gives the corresponding single cosine moment.
-/
theorem cosineMoment_tendsto_of_unweighted
    (theta : Nat → Real) (m : Nat)
    (hNumerator : Tendsto
      (fun x : Real =>
        unweightedPrimeSum (splitCosineCoefficient theta m) x /
          (x / Real.log x))
      atTop (nhds 0))
    (hAP : PrimeNumberTheoremModThreeOne) :
    Tendsto (fun X : Nat => cosineMoment splitPrimesUpTo theta m X)
      atTop (nhds 0) := by
  have hNumNat := hNumerator.comp
    (tendsto_natCast_atTop_atTop (R := Real))
  have hRatio := hNumNat.div hAP (by norm_num : ((1 : Real) / 2) ≠ 0)
  refine Tendsto.congr' ?_ (by simpa using hRatio)
  filter_upwards [eventually_ge_atTop (7 : Nat)] with X hX
  have hSeven : 7 ∈ splitPrimesUpTo X := by
    simp only [splitPrimesUpTo, Finset.mem_filter, Finset.mem_range]
    norm_num
    omega
  have hCard : ((splitPrimesUpTo X).card : Real) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr ⟨7, hSeven⟩)
  have hXpos : (0 : Real) < X := by exact_mod_cast (by omega : 0 < X)
  have hXne : (X : Real) ≠ 0 := hXpos.ne'
  have hXone : (X : Real) ≠ 1 := by exact_mod_cast (by omega : X ≠ 1)
  have hLog : Real.log (X : Real) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hXpos hXone
  rw [cosineMoment, ← unweightedPrimeSum_splitCosineCoefficient]
  simp only [Function.comp_apply, Pi.div_apply]
  field_simp [hCard, hXne, hLog]

/--
The preceding one-frequency result applied to every positive frequency is
precisely `HeckePrimeCharacterCancellation`.
-/
theorem heckePrimeCharacterCancellation_of_unweighted
    (theta : Nat → Real)
    (hNumerator : ∀ m : Nat, 0 < m →
      Tendsto
        (fun x : Real =>
          unweightedPrimeSum (splitCosineCoefficient theta m) x /
            (x / Real.log x))
        atTop (nhds 0))
    (hAP : PrimeNumberTheoremModThreeOne) :
    HeckePrimeCharacterCancellation theta := by
  intro m hm
  exact cosineMoment_tendsto_of_unweighted theta m (hNumerator m hm) hAP

#check @splitCosineCoefficient
#check @cosineMoment_tendsto_of_unweighted
#check @heckePrimeCharacterCancellation_of_unweighted
#print axioms heckePrimeCharacterCancellation_of_unweighted

end

end K3Lean.HeckeCosineCancellation
