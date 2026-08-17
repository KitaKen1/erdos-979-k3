import Mathlib.NumberTheory.Chebyshev

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Removing higher prime powers from a twisted Chebyshev sum

The logarithmic derivative of an Euler product naturally sums over all prime
powers.  For coefficients bounded in absolute value, the non-prime terms are
bounded by the ordinary difference `psi - theta`, hence by
`2 * sqrt x * log x = o(x)`.  This file proves that reduction independently of
Hecke characters.
-/

namespace K3Lean.PrimePowerRemoval

open ArithmeticFunction Asymptotics Filter
open scoped BigOperators Topology

noncomputable section

/-- A Chebyshev `psi` sum with arbitrary real coefficients. -/
def twistedPsi (c : Nat → Real) (x : Real) : Real :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, c n * vonMangoldt n

/-- The corresponding sum restricted to primes. -/
def twistedTheta (c : Nat → Real) (x : Real) : Real :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
    if Nat.Prime n then c n * Real.log n else 0

/-- The contribution from composite prime powers. -/
def twistedPrimePowerRemainder (c : Nat → Real) (x : Real) : Real :=
  ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬Nat.Prime n),
    c n * vonMangoldt n

/-- `floor x + 1` converts the `n < N` convention to the `n <= x` convention. -/
theorem twistedPsi_eq_sum_range_floor_succ (c : Nat → Real) (x : Real) :
    twistedPsi c x =
      ∑ n ∈ Finset.range (⌊x⌋₊ + 1), c n * vonMangoldt n := by
  rw [twistedPsi, Nat.range_succ_eq_Icc_zero,
    Finset.Icc_eq_cons_Ioc (Nat.zero_le ⌊x⌋₊), Finset.sum_cons]
  simp

/-- A PNT+-style discrete limit gives the corresponding real-step-function limit. -/
theorem twistedPsi_normalized_tendsto_zero_of_sum_range
    (c : Nat → Real)
    (hDiscrete : Tendsto
      (fun N : Nat =>
        (∑ n ∈ Finset.range N, c n * vonMangoldt n) / (N : Real))
      atTop (nhds 0)) :
    Tendsto (fun x : Real => twistedPsi c x / x) atTop (nhds 0) := by
  have hIndex : Tendsto (fun x : Real => ⌊x⌋₊ + 1) atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards
      [tendsto_nat_floor_atTop.eventually (eventually_ge_atTop N)] with x hx
    omega
  have hComposed := hDiscrete.comp hIndex
  have hInv : Tendsto (fun x : Real => 1 / x) atTop (nhds 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero :
      Tendsto (fun x : Real => x⁻¹) atTop (nhds 0))
  have hRatio : Tendsto
      (fun x : Real => ((⌊x⌋₊ + 1 : Nat) : Real) / x)
      atTop (nhds 1) := by
    convert (tendsto_nat_floor_div_atTop (R := Real)).add hInv using 1
    · funext x
      push_cast
      ring
    · norm_num
  have hProduct := hComposed.mul hRatio
  refine Tendsto.congr' ?_ (by simpa using hProduct)
  filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
  rw [twistedPsi_eq_sum_range_floor_succ]
  have hIndexNe : (((⌊x⌋₊ + 1 : Nat) : Real)) ≠ 0 := by positivity
  field_simp [hx.ne', hIndexNe]

theorem twistedPsi_sub_twistedTheta
    (c : Nat → Real) (x : Real) :
    twistedPsi c x - twistedTheta c x =
      twistedPrimePowerRemainder c x := by
  rw [twistedPsi, twistedTheta, twistedPrimePowerRemainder,
    Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  by_cases hp : Nat.Prime n
  · simp [hp, vonMangoldt_apply_prime hp]
  · simp [hp]

/-- A bounded twist cannot enlarge the higher-prime-power remainder. -/
theorem abs_twistedPsi_sub_twistedTheta_le
    (c : Nat → Real) (C : Real) (_hC : 0 ≤ C)
    (hc : ∀ n, |c n| ≤ C) (x : Real) :
    |twistedPsi c x - twistedTheta c x| ≤
      C * (Chebyshev.psi x - Chebyshev.theta x) := by
  rw [twistedPsi_sub_twistedTheta, twistedPrimePowerRemainder]
  calc
    |∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬Nat.Prime n),
        c n * vonMangoldt n| ≤
        ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬Nat.Prime n),
          |c n * vonMangoldt n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬Nat.Prime n),
          C * vonMangoldt n := by
      refine Finset.sum_le_sum fun n hn => ?_
      rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
      exact mul_le_mul_of_nonneg_right (hc n) vonMangoldt_nonneg
    _ = C * (Chebyshev.psi x - Chebyshev.theta x) := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.mul_sum]

/-- The standard square-root prime-power error is little-oh of `x`. -/
theorem sqrt_mul_log_isLittleO :
    (fun x : Real => Real.sqrt x * Real.log x) =o[atTop]
      (fun x : Real => x) := by
  have h := (isBigO_refl Real.sqrt atTop).mul_isLittleO
    (isLittleO_log_rpow_atTop (r := (1 / 2 : Real)) (by norm_num))
  refine h.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
  norm_num

theorem twistedPsi_sub_twistedTheta_isBigO
    (c : Nat → Real) (C : Real) (hC : 0 ≤ C)
    (hc : ∀ n, |c n| ≤ C) :
    (fun x => twistedPsi c x - twistedTheta c x) =O[atTop]
      (fun x : Real => Real.sqrt x * Real.log x) := by
  refine IsBigO.of_bound (2 * C) ?_
  filter_upwards [eventually_ge_atTop (1 : Real)] with x hx
  have hPrimePower := abs_twistedPsi_sub_twistedTheta_le c C hC hc x
  have hChebyshev := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx
  have hDiff : Chebyshev.psi x - Chebyshev.theta x ≤
      2 * Real.sqrt x * Real.log x :=
    (le_abs_self _).trans hChebyshev
  have hSqrtLog : 0 ≤ Real.sqrt x * Real.log x :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hx)
  simp only [Real.norm_eq_abs, abs_of_nonneg hSqrtLog]
  calc
    |twistedPsi c x - twistedTheta c x| ≤
        C * (Chebyshev.psi x - Chebyshev.theta x) := hPrimePower
    _ ≤ C * (2 * Real.sqrt x * Real.log x) :=
      mul_le_mul_of_nonneg_left hDiff hC
    _ = (2 * C) * (Real.sqrt x * Real.log x) := by ring

theorem twistedPsi_sub_twistedTheta_isLittleO
    (c : Nat → Real) (C : Real) (hC : 0 ≤ C)
    (hc : ∀ n, |c n| ≤ C) :
    (fun x => twistedPsi c x - twistedTheta c x) =o[atTop]
      (fun x : Real => x) :=
  (twistedPsi_sub_twistedTheta_isBigO c C hC hc).trans_isLittleO
    sqrt_mul_log_isLittleO

/-- Cancellation for all prime powers therefore implies cancellation for primes. -/
theorem twistedTheta_normalized_tendsto_zero
    (c : Nat → Real) (C : Real) (hC : 0 ≤ C)
    (hc : ∀ n, |c n| ≤ C)
    (hPsi : Tendsto (fun x => twistedPsi c x / x) atTop (nhds 0)) :
    Tendsto (fun x => twistedTheta c x / x) atTop (nhds 0) := by
  have hRemainder :=
    (twistedPsi_sub_twistedTheta_isLittleO c C hC hc).tendsto_div_nhds_zero
  have hDifference := hPsi.sub hRemainder
  convert hDifference using 1
  · funext x
    ring
  · norm_num

#check @twistedPsi_sub_twistedTheta_isLittleO
#print axioms twistedPsi_sub_twistedTheta_isLittleO
#check @twistedTheta_normalized_tendsto_zero
#print axioms twistedTheta_normalized_tendsto_zero
#check @twistedPsi_normalized_tendsto_zero_of_sum_range
#print axioms twistedPsi_normalized_tendsto_zero_of_sum_range

end

end K3Lean.PrimePowerRemoval
