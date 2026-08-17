import K3Lean.AuditedWienerIkehara
import K3Lean.HeckeDeuringReduction
import K3Lean.LogWeightRemoval
import PrimeNumberTheoremAnd.Wiener
import PrimeNumberTheoremAnd.Consequences

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Discharging the two analytic imports from PrimeNumberTheorem+

* `PNTPlusWienerIkehara` is instantiated by the upstream
  `WienerIkeharaTheorem''` (whose statement it copies verbatim).
* `PrimeNumberTheoremModThreeOne` (the unweighted prime-counting form in the
  progression `1 mod 3`) is derived from the upstream log-weighted
  `chebyshev_asymptotic_pnt` at `(q, a) = (3, 1)` and `(1, 0)` through the
  signed weight `c = 1_{n ≡ 1 (3)} - 1/2`: the project's Abel-summation
  machinery (`K3Lean.LogWeightRemoval`) removes the logarithmic weight from
  the difference, and the upstream `pi_alt'` restores the main term.
-/

namespace K3Lean.PNTImports

open Filter Finset Asymptotics
open K3Lean.AuditedWienerIkehara
open K3Lean.LogWeightRemoval
open K3Lean.HeckeDeuringReduction

/-- The Wiener--Ikehara statement used by the project, discharged. -/
theorem pntPlusWienerIkehara : PNTPlusWienerIkehara := by
  intro A G f hpos hsum hG hEq
  exact WienerIkeharaTheorem'' hpos hsum hG hEq

noncomputable section

/-- The signed weight `1_{n ≡ 1 (3)} - 1/2`, bounded by `1/2`. -/
private def cWeight (n : ℕ) : ℝ := (if n % 3 = 1 then (1 : ℝ) else 0) - 1/2

private lemma abs_cWeight_le (n : ℕ) : |cWeight n| ≤ 1/2 := by
  unfold cWeight
  split <;> norm_num

private lemma Icc_zero_eq_Iic (N : ℕ) : Finset.Icc 0 N = Finset.Iic N := by
  ext n; simp

/-- The log-weighted sum of `cWeight` is the split theta sum minus half the
full theta sum, in the exact shapes produced by `chebyshev_asymptotic_pnt`. -/
private lemma weightedPrimeSum_cWeight (x : ℝ) :
    weightedPrimeSum cWeight x =
      (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          if p % 3 = 1 then Real.log p else 0)
        - (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
            if p % 1 = 0 then Real.log p else 0) / 2 := by
  rw [weightedPrimeSum, Icc_zero_eq_Iic, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hp : Nat.Prime n
  · by_cases h3 : n % 3 = 1 <;>
      simp [hp, h3, cWeight, Nat.mod_one] <;> ring
  · simp [hp]

/-- The unweighted sum of `cWeight` is the split prime count minus half the
full prime count. -/
private lemma unweightedPrimeSum_cWeight (x : ℝ) :
    unweightedPrimeSum cWeight x =
      ((splitPrimesUpTo ⌊x⌋₊).card : ℝ)
        - (Nat.primeCounting ⌊x⌋₊ : ℝ) / 2 := by
  have hπ : (Nat.primeCounting ⌊x⌋₊ : ℝ) =
      (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hsplit : ((splitPrimesUpTo ⌊x⌋₊).card : ℝ) =
      (((Finset.range (⌊x⌋₊ + 1)).filter
          (fun p => Nat.Prime p ∧ p % 3 = 1)).card : ℝ) := by
    rw [splitPrimesUpTo]
  rw [hπ, hsplit, unweightedPrimeSum,
    ← Finset.sum_boole, ← Finset.sum_boole, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  have hrange : Finset.Icc 0 ⌊x⌋₊ = Finset.range (⌊x⌋₊ + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hrange]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hp : Nat.Prime n
  · by_cases h3 : n % 3 = 1
    · rw [if_pos hp, if_pos ⟨hp, h3⟩, if_pos hp]
      unfold cWeight
      rw [if_pos h3]
    · rw [if_pos hp, if_neg (fun h => h3 h.2), if_pos hp]
      unfold cWeight
      rw [if_neg h3]
  · rw [if_neg hp, if_neg (fun h => hp h.1), if_neg hp]
    norm_num

/-- Normalized limit of the split theta sum. -/
private lemma theta_split_div_tendsto :
    Tendsto (fun x : ℝ =>
        (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          if p % 3 = 1 then Real.log p else 0) / x)
      atTop (nhds (1/2)) := by
  have h := chebyshev_asymptotic_pnt (q := 3) (a := 1)
    (by norm_num) (by norm_num) (by norm_num)
  have htot : ((3 : ℕ).totient : ℝ) = 2 := by norm_num [Nat.totient_prime]
  have hne : ∀ᶠ x : ℝ in atTop, x / ((3:ℕ).totient : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [htot]; positivity
  have h1 := (Asymptotics.isEquivalent_iff_tendsto_one hne).mp h
  have h2 : Tendsto (fun x : ℝ =>
      ((∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
        if p % 3 = 1 then Real.log p else 0) / (x / ((3:ℕ).totient : ℝ)))
        * (1/2)) atTop (nhds (1 * (1/2))) := h1.mul_const _
  rw [one_mul] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  rw [htot]
  field_simp

/-- Normalized limit of the full theta sum. -/
private lemma theta_full_div_tendsto :
    Tendsto (fun x : ℝ =>
        (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          if p % 1 = 0 then Real.log p else 0) / x)
      atTop (nhds 1) := by
  have h := chebyshev_asymptotic_pnt (q := 1) (a := 0)
    (by norm_num) (by norm_num) (by norm_num)
  have hne : ∀ᶠ x : ℝ in atTop, x / ((1:ℕ).totient : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    simp [Nat.totient_one]
    positivity
  have h1 := (Asymptotics.isEquivalent_iff_tendsto_one hne).mp h
  refine h1.congr' ?_
  filter_upwards with x
  simp [Nat.totient_one]

/-- The weighted signed sum is `o(x)`. -/
private lemma weighted_cWeight_tendsto_zero :
    Tendsto (fun x => weightedPrimeSum cWeight x / x) atTop (nhds 0) := by
  have h := theta_split_div_tendsto.sub (theta_full_div_tendsto.div_const 2)
  norm_num at h
  refine h.congr' ?_
  filter_upwards with x
  rw [weightedPrimeSum_cWeight, sub_div, div_div]
  ring_nf

/-- Normalized limit of the ordinary prime-counting function. -/
private lemma pi_div_tendsto :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x))
      atTop (nhds 1) := by
  have hne : ∀ᶠ x : ℝ in atTop, x / Real.log x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    have hx0 : (0:ℝ) < x := by linarith
    have hlog : (0:ℝ) < Real.log x := Real.log_pos hx
    positivity
  exact (Asymptotics.isEquivalent_iff_tendsto_one hne).mp pi_alt'

/-- The split prime count against `x / log x` tends to `1/2`. -/
private lemma split_count_div_tendsto :
    Tendsto (fun x : ℝ =>
        ((splitPrimesUpTo ⌊x⌋₊).card : ℝ) / (x / Real.log x))
      atTop (nhds (1/2)) := by
  have hU := unweightedPrimeSum_normalized_tendsto_zero cWeight (1/2)
    (by norm_num) abs_cWeight_le weighted_cWeight_tendsto_zero
  have h := hU.add (pi_div_tendsto.div_const 2)
  norm_num at h
  refine h.congr' ?_
  filter_upwards with x
  rw [unweightedPrimeSum_cWeight, sub_div, div_div]
  ring_nf

/-- The prime number theorem in the progression `1 mod 3`, discharged. -/
theorem primeNumberTheoremModThreeOne :
    K3Lean.HeckeDeuringReduction.PrimeNumberTheoremModThreeOne := by
  unfold K3Lean.HeckeDeuringReduction.PrimeNumberTheoremModThreeOne
  have h := split_count_div_tendsto.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  refine h.congr ?_
  intro X
  simp only [Function.comp_apply, Nat.floor_natCast]
  rw [div_div_eq_mul_div]

end

end K3Lean.PNTImports
