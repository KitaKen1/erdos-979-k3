import K3Lean.PrimePowerRemoval
import Mathlib.NumberTheory.AbelSummation

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Removing logarithmic weights from bounded signed prime sums

Abel summation expresses an unweighted bounded prime sum in terms of its
logarithmically weighted version and an integral remainder.  The remainder is
dominated by a constant multiple of Mathlib's ordinary Chebyshev remainder,
which is already proved to be `o(x / log x)`.
-/

namespace K3Lean.LogWeightRemoval

open Asymptotics Filter MeasureTheory Set
open K3Lean.PrimePowerRemoval
open scoped BigOperators Topology

noncomputable section

/-- Logarithmically weighted signed prime sum. -/
def weightedPrimeSum (c : Nat → Real) (x : Real) : Real :=
  ∑ p ∈ Finset.Icc 0 ⌊x⌋₊,
    if Nat.Prime p then c p * Real.log p else 0

/-- The same signed prime sum without logarithmic weights. -/
def unweightedPrimeSum (c : Nat → Real) (x : Real) : Real :=
  ∑ p ∈ Finset.Icc 0 ⌊x⌋₊,
    if Nat.Prime p then c p else 0

/-- The closed-interval convention agrees with `PrimePowerRemoval.twistedTheta`. -/
theorem weightedPrimeSum_eq_twistedTheta (c : Nat → Real) (x : Real) :
    weightedPrimeSum c x = twistedTheta c x := by
  rw [weightedPrimeSum, twistedTheta]
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le ⌊x⌋₊), Finset.sum_cons]
  norm_num

/-- The step function in the Abel remainder is integrable on compact intervals. -/
theorem integrableOn_weightedPrimeSum_div_id_mul_log_sq
    (c : Nat → Real) (x : Real) :
    IntegrableOn
      (fun t => weightedPrimeSum c t / (t * Real.log t ^ 2))
      (Set.Icc 2 x) volume := by
  conv =>
    arg 1
    ext t
    rw [weightedPrimeSum, div_eq_mul_one_div, mul_comm]
  refine integrableOn_mul_sum_Icc _ (by norm_num) <|
    ContinuousOn.integrableOn_Icc fun t ht => ContinuousAt.continuousWithinAt ?_
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hden : t * Real.log t ^ 2 ≠ 0 := mul_ne_zero ht0 <| by
    simp
    grind
  fun_prop

/-- Abel summation for a bounded signed prime sequence. -/
theorem unweightedPrimeSum_eq_weighted_div_log_add_integral
    (c : Nat → Real) {x : Real} (hx : 2 ≤ x) :
    unweightedPrimeSum c x =
      weightedPrimeSum c x / Real.log x +
        ∫ t in 2..x, weightedPrimeSum c t / (t * Real.log t ^ 2) := by
  rw [unweightedPrimeSum]
  let a : Nat → Real :=
    Set.indicator {n | Nat.Prime n} (fun n => c n * Real.log n)
  trans ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (Real.log n)⁻¹ * a n
  · refine Finset.sum_congr rfl fun n hn => ?_
    split_ifs with h
    · have hlog : Real.log n ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (by exact_mod_cast h.pos)
          (by exact_mod_cast h.ne_one)
      simp [a, h, field]
    · simp [a, h]
  rw [sum_mul_eq_sub_integral_mul₁ a
      (f := fun n => (Real.log n)⁻¹) (by simp [a]) (by simp [a]),
    ← intervalIntegral.integral_of_le hx]
  · have int_deriv (f : Real → Real) :
        ∫ u in 2..x, deriv (fun y => (Real.log y)⁻¹) u * f u =
          ∫ u in 2..x, f u * -(u * Real.log u ^ 2)⁻¹ :=
      intervalIntegral.integral_congr fun u _ => by
        simp [Real.deriv_inv_log, field]
    simp [int_deriv, a, Set.indicator_apply, weightedPrimeSum]
    grind
  · intro z hz
    have hz0 : z ≠ 0 := by linarith [hz.1]
    have hlog : Real.log z ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith [hz.1]
    fun_prop
  · refine ContinuousOn.integrableOn_Icc fun z hz => ContinuousWithinAt.congr ?_
      (fun _ _ => Real.deriv_inv_log) Real.deriv_inv_log
    have hz0 : z ≠ 0 := by linarith [hz.1]
    have hlog : Real.log z ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 <| Real.log_ne_zero_of_pos_of_ne_one ?_ ?_ <;>
        linarith [hz.1]
    exact ContinuousAt.continuousWithinAt <| by fun_prop

/-- A bounded signed weighted sum is dominated by `C * theta`. -/
theorem abs_weightedPrimeSum_le
    (c : Nat → Real) (C : Real) (_hC : 0 ≤ C)
    (hc : ∀ n, |c n| ≤ C) (x : Real) :
    |weightedPrimeSum c x| ≤ C * Chebyshev.theta x := by
  rw [weightedPrimeSum, Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  calc
    |∑ p ∈ Finset.Icc 0 ⌊x⌋₊,
        if Nat.Prime p then c p * Real.log p else 0| ≤
      ∑ p ∈ Finset.Icc 0 ⌊x⌋₊,
        |if Nat.Prime p then c p * Real.log p else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Finset.Icc 0 ⌊x⌋₊,
        C * (if Nat.Prime p then Real.log p else 0) := by
      refine Finset.sum_le_sum fun p hp => ?_
      by_cases hprime : Nat.Prime p
      · simp only [hprime, if_pos, abs_mul]
        rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le))]
        exact mul_le_mul_of_nonneg_right (hc p)
          (Real.log_nonneg (by exact_mod_cast hprime.one_le))
      · simp [hprime]
    _ = C * ∑ p ∈ Finset.Icc 0 ⌊x⌋₊,
        if Nat.Prime p then Real.log p else 0 := by
      rw [Finset.mul_sum]

/-- The signed Abel remainder is bounded by the ordinary Chebyshev remainder. -/
theorem integral_weightedPrimeSum_div_log_sq_isBigO
    (c : Nat → Real) (C : Real) (hC : 0 ≤ C)
    (hc : ∀ n, |c n| ≤ C) :
    (fun x => ∫ t in 2..x,
      weightedPrimeSum c t / (t * Real.log t ^ 2)) =O[atTop]
      (fun x => ∫ t in 2..x,
        Chebyshev.theta t / (t * Real.log t ^ 2)) := by
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
  simp_rw [Real.norm_eq_abs]
  calc
    |∫ t in 2..x, weightedPrimeSum c t / (t * Real.log t ^ 2)| ≤
        ∫ t in 2..x, |weightedPrimeSum c t / (t * Real.log t ^ 2)| :=
      intervalIntegral.abs_integral_le_integral_abs (by linarith)
    _ ≤ ∫ t in 2..x,
        C * (Chebyshev.theta t / (t * Real.log t ^ 2)) :=
      intervalIntegral.integral_mono_on (by linarith) ?hf ?hg fun t ht => ?hh
    _ = C * |∫ t in 2..x,
        Chebyshev.theta t / (t * Real.log t ^ 2)| := by
      rw [intervalIntegral.integral_const_mul, abs_of_nonneg]
      exact intervalIntegral.integral_nonneg (by linarith) fun u hu => by
        have hupos : 0 < u := by linarith [hu.1]
        exact div_nonneg (Chebyshev.theta_nonneg u)
          (mul_nonneg hupos.le (sq_nonneg _))
  case hf =>
    refine (intervalIntegrable_iff.mpr ?_).abs
    rw [Set.uIoc_of_le (by linarith), ← integrableOn_Icc_iff_integrableOn_Ioc]
    exact integrableOn_weightedPrimeSum_div_id_mul_log_sq c x
  case hg =>
    refine (intervalIntegrable_iff.mpr ?_).const_mul _
    rw [Set.uIoc_of_le (by linarith), ← integrableOn_Icc_iff_integrableOn_Ioc]
    exact Chebyshev.integrableOn_theta_div_id_mul_log_sq x
  case hh =>
    have htpos : 0 < t := by linarith [ht.1]
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hdenpos : 0 < t * Real.log t ^ 2 :=
      mul_pos htpos (sq_pos_of_pos hlogpos)
    rw [abs_div, abs_of_pos hdenpos]
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right
        (abs_weightedPrimeSum_le c C hC hc t) hdenpos.le

theorem integral_weightedPrimeSum_div_log_sq_isLittleO
    (c : Nat → Real) (C : Real) (hC : 0 ≤ C)
    (hc : ∀ n, |c n| ≤ C) :
    (fun x => ∫ t in 2..x,
      weightedPrimeSum c t / (t * Real.log t ^ 2)) =o[atTop]
      (fun x => x / Real.log x) :=
  (integral_weightedPrimeSum_div_log_sq_isBigO c C hC hc).trans_isLittleO
    Chebyshev.integral_theta_div_log_sq_isLittleO

/-- Log-weighted cancellation implies unweighted cancellation. -/
theorem unweightedPrimeSum_normalized_tendsto_zero
    (c : Nat → Real) (C : Real) (hC : 0 ≤ C)
    (hc : ∀ n, |c n| ≤ C)
    (hWeighted :
      Tendsto (fun x => weightedPrimeSum c x / x) atTop (nhds 0)) :
    Tendsto
      (fun x => unweightedPrimeSum c x / (x / Real.log x))
      atTop (nhds 0) := by
  have hMain : Tendsto
      (fun x => (weightedPrimeSum c x / Real.log x) /
        (x / Real.log x)) atTop (nhds 0) := by
    refine Tendsto.congr' ?_ hWeighted
    filter_upwards [eventually_gt_atTop (1 : Real)] with x hx
    have hx0 : x ≠ 0 := by linarith
    have hlog0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    field_simp
  have hRemainder :=
    (integral_weightedPrimeSum_div_log_sq_isLittleO c C hC hc).tendsto_div_nhds_zero
  have hSum := hMain.add hRemainder
  refine Tendsto.congr' ?_ (by simpa using hSum)
  filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
  rw [unweightedPrimeSum_eq_weighted_div_log_add_integral c hx]
  ring

#check @unweightedPrimeSum_eq_weighted_div_log_add_integral
#check @integral_weightedPrimeSum_div_log_sq_isLittleO
#print axioms integral_weightedPrimeSum_div_log_sq_isLittleO
#check @unweightedPrimeSum_normalized_tendsto_zero
#print axioms unweightedPrimeSum_normalized_tendsto_zero

end

end K3Lean.LogWeightRemoval
