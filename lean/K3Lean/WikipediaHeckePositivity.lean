import K3Lean.PublishedInputs
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.Niven

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Positivity identities for the Wikipedia-only Hecke route

The prime-number-theorem proof on Wikipedia excludes zeros on `re s = 1`
with `3 + 4 cos phi + cos (2 phi) >= 0`.  The same local identity applies to
unitary Hecke-character values.  A second nonnegative identity makes the
ordinary Wiener--Ikehara theorem sufficient: the logarithmic derivative of
`zeta_K^2 L(psi^m) L(conj psi^m)` has local coefficient `normSq (1 + z)`.

This file proves only these elementary algebraic facts.  It does not assume or
state CM Sato--Tate or Hecke prime cancellation.

Reference:

* https://en.wikipedia.org/wiki/Prime_number_theorem#Non-vanishing_on_Re(s)_=_1
-/

namespace K3Lean.WikipediaHeckePositivity

open K3Lean.PublishedInputs
open Complex Filter
open scoped BigOperators Topology

/-- Partial sums in the normalization used by the discrete Wiener--Ikehara theorem. -/
noncomputable def normalizedPartialSum (f : Nat → Real) (N : Nat) : Real :=
  (∑ n ∈ Finset.range N, f n) / (N : Real)

/-- The projective Fermat cubic has exactly nine points over `ZMod 7`. -/
theorem fermatProjectivePointCount_seven :
    fermatProjectivePointCount 7 = 9 := by
  rw [fermatProjectivePointCount]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide

/-- Consequently its Frobenius trace at `7` is `8 - 9 = -1`. -/
theorem fermatFrobeniusTrace_seven :
    fermatFrobeniusTrace 7 = -1 := by
  simp [fermatFrobeniusTrace, fermatProjectivePointCount_seven]

/--
A unit complex number with the normalized trace forced by the Fermat cubic at
`p = 7` cannot have finite multiplicative order.  If it did, `z + z⁻¹` would
be an algebraic integer.  Its square is `1 / 7`, contradicting that a rational
algebraic integer is an integer.
-/
theorem not_isOfFinOrder_of_fermatTrace_seven
    (z : Complex)
    (hzNorm : Complex.normSq z = 1)
    (hzTrace : (2 * Real.sqrt 7) * z.re = -1) :
    ¬ IsOfFinOrder z := by
  intro hfinite
  obtain ⟨n, hn, hpow⟩ := hfinite.exists_pow_eq_one
  have hzIntegral : IsIntegral ℤ z :=
    IsIntegral.of_pow hn (hpow ▸ isIntegral_one)
  have hpowPred : z ^ (n - 1) * z = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
    exact hpow
  have hinv : z ^ (n - 1) = z⁻¹ :=
    eq_inv_of_mul_eq_one_left hpowPred
  have hzInvIntegral : IsIntegral ℤ z⁻¹ := by
    rw [← hinv]
    exact hzIntegral.pow _
  have hsumIntegral : IsIntegral ℤ (z + z⁻¹) :=
    hzIntegral.add hzInvIntegral
  have hsqrt : Real.sqrt 7 ≠ 0 := by positivity
  have hre : 2 * z.re = -1 / Real.sqrt 7 := by
    apply (eq_div_iff hsqrt).2
    nlinarith [hzTrace]
  have hinvConj : z⁻¹ = starRingEnd Complex z := by
    apply Complex.ext
    · rw [Complex.inv_re]
      simp [hzNorm]
    · rw [Complex.inv_im]
      simp [hzNorm]
  have hsum : z + z⁻¹ = ((-1 / Real.sqrt 7 : Real) : Complex) := by
    rw [hinvConj, Complex.add_conj, hre]
  rw [hsum] at hsumIntegral
  have hrealIntegral : IsIntegral ℤ (-1 / Real.sqrt 7 : Real) :=
    (isIntegral_algebraMap_iff (B := Complex) RCLike.ofReal_injective).mp
      hsumIntegral
  have hsqrtSq : (Real.sqrt 7) ^ 2 = 7 := by
    exact Real.sq_sqrt (by norm_num)
  have hrealSq : (-1 / Real.sqrt 7 : Real) ^ 2 = ((1 / 7 : ℚ) : Real) := by
    calc
      (-1 / Real.sqrt 7 : Real) ^ 2 = 1 / (Real.sqrt 7) ^ 2 := by ring
      _ = 1 / 7 := by rw [hsqrtSq]
      _ = ((1 / 7 : ℚ) : Real) := by norm_num
  have hOneSeventhIntegral : IsIntegral ℤ ((1 / 7 : ℚ) : Real) := by
    rw [← hrealSq]
    exact hrealIntegral.pow 2
  obtain ⟨k, hk⟩ : ∃ k : ℤ, ((1 / 7 : ℚ) : Real) = k := by
    rw [← hOneSeventhIntegral.exists_int_iff_exists_rat]
    exact ⟨1 / 7, rfl⟩
  have hkPosReal : (0 : Real) < (k : Real) := by
    rw [← hk]
    norm_num
  have hkLtReal : (k : Real) < 1 := by
    rw [← hk]
    norm_num
  have hkPos : (0 : ℤ) < k := by exact_mod_cast hkPosReal
  have hkLt : k < (1 : ℤ) := by exact_mod_cast hkLtReal
  omega

/-- Every positive power of the normalized `p = 7` Frobenius root is nontrivial. -/
theorem pow_ne_one_of_fermatTrace_seven
    (z : Complex)
    (hzNorm : Complex.normSq z = 1)
    (hzTrace : (2 * Real.sqrt 7) * z.re = -1)
    (m : Nat) (hm : 0 < m) :
    z ^ m ≠ 1 := by
  intro hpow
  exact not_isOfFinOrder_of_fermatTrace_seven z hzNorm hzTrace
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hpow⟩)

/-- The de la Vallee Poussin trigonometric identity used on Wikipedia. -/
theorem de_la_vallee_poussin_identity (phi : Real) :
    3 + 4 * Real.cos phi + Real.cos (2 * phi) =
      2 * (1 + Real.cos phi) ^ 2 := by
  rw [Real.cos_two_mul]
  ring

/-- In particular, every local term in the boundary-zero argument is nonnegative. -/
theorem de_la_vallee_poussin_nonneg (phi : Real) :
    0 <= 3 + 4 * Real.cos phi + Real.cos (2 * phi) := by
  rw [de_la_vallee_poussin_identity]
  positivity

/-- The same identity written without choosing an argument for a unit complex number. -/
theorem de_la_vallee_poussin_complex_identity
    (z : Complex) (hz : Complex.normSq z = 1) :
    3 + 4 * z.re + (z ^ 2).re = 2 * (1 + z.re) ^ 2 := by
  have hz' : z.re ^ 2 + z.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using hz
  have hpow : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    simp [pow_two]
  rw [hpow]
  nlinarith

/-- The disk version also covers the finitely many omitted Euler factors by setting `z = 0`. -/
theorem de_la_vallee_poussin_disk_identity (z : Complex) :
    3 + 4 * z.re + (z ^ 2).re =
      2 * (1 + z.re) ^ 2 + (1 - Complex.normSq z) := by
  have hpow : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    simp [pow_two]
  rw [hpow, Complex.normSq_apply]
  ring

/-- Every local term is nonnegative for values in the closed unit disk. -/
theorem de_la_vallee_poussin_disk_nonneg
    (z : Complex) (hz : Complex.normSq z <= 1) :
    0 <= 3 + 4 * z.re + (z ^ 2).re := by
  rw [de_la_vallee_poussin_disk_identity]
  positivity

/-- Complex local terms in the Hecke boundary-zero argument are nonnegative. -/
theorem de_la_vallee_poussin_complex_nonneg
    (z : Complex) (hz : Complex.normSq z = 1) :
    0 <= 3 + 4 * z.re + (z ^ 2).re := by
  rw [de_la_vallee_poussin_complex_identity z hz]
  positivity

/-- Powers of a closed-unit-disk value remain in the closed unit disk. -/
theorem normSq_pow_le_one
    (z : Complex) (hz : Complex.normSq z <= 1) (n : Nat) :
    Complex.normSq (z ^ n) <= 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Complex.normSq_mul]
      nlinarith [Complex.normSq_nonneg (z ^ n), Complex.normSq_nonneg z]

/--
The de la Vallee Poussin positivity identity lifted from one local coefficient
to the logarithm of an Euler factor.  The disk hypothesis includes omitted
local factors, represented by `z = 0`.
-/
theorem re_neg_log_dvp_nonneg
    {a : Real} (ha0 : 0 <= a) (ha1 : a < 1)
    {z : Complex} (hz : Complex.normSq z <= 1) :
    0 <= 3 * (-Complex.log (1 - a)).re +
      4 * (-Complex.log (1 - a * z)).re +
      (-Complex.log (1 - a * z ^ 2)).re := by
  have hzNorm : ‖z‖ <= 1 := by
    nlinarith [Complex.sq_norm z, norm_nonneg z]
  have hac0 : ‖(a : Complex)‖ < 1 := by
    simpa only [Complex.norm_of_nonneg ha0] using ha1
  have hac1 : ‖(a : Complex) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_of_nonneg ha0]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hzNorm ha0) (by simpa using ha1)
  have hzNormSq : ‖z‖ ^ 2 <= 1 := by
    rwa [Complex.sq_norm]
  have hac2 : ‖(a : Complex) * z ^ 2‖ < 1 := by
    rw [norm_mul, norm_pow, Complex.norm_of_nonneg ha0]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hzNormSq ha0) (by simpa using ha1)
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac0).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac1).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac2) |>.tsum_eq]
  refine tsum_nonneg fun n => ?_
  simp only [← ofReal_pow, Complex.div_natCast_re, ofReal_re, mul_pow,
    mul_re, ofReal_im, zero_mul, sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    have hLocal := de_la_vallee_poussin_disk_nonneg
      (z ^ n) (normSq_pow_le_one z hz n)
    have haPow : 0 <= a ^ n := pow_nonneg ha0 n
    have hScaled := mul_nonneg haPow hLocal
    convert hScaled using 1
    rw [← pow_mul, pow_mul']
    ring

/--
Summing the nonnegative local logarithms gives the Euler-product lower bound
used in the boundary-zero contradiction.  The index type is arbitrary, so it
can later be instantiated by prime ideals rather than rational primes.
-/
theorem norm_exp_tsum_dvp_ge_one
    {P : Type*} (a : P → Real) (z : P → Complex)
    (ha0 : ∀ p, 0 <= a p) (ha1 : ∀ p, a p < 1)
    (hz : ∀ p, Complex.normSq (z p) <= 1)
    (h0 : Summable (fun p => -Complex.log (1 - (a p : Complex))))
    (h1 : Summable (fun p => -Complex.log (1 - (a p : Complex) * z p)))
    (h2 : Summable (fun p => -Complex.log (1 - (a p : Complex) * (z p) ^ 2))) :
    1 <= ‖Complex.exp (∑' p, -Complex.log (1 - (a p : Complex))) ^ 3 *
      Complex.exp (∑' p, -Complex.log (1 - (a p : Complex) * z p)) ^ 4 *
      Complex.exp (∑' p, -Complex.log (1 - (a p : Complex) * (z p) ^ 2))‖ := by
  have hs0 := (hasSum_re h0.hasSum).summable.mul_left 3
  have hs1 := (hasSum_re h1.hasSum).summable.mul_left 4
  have hs2 := (hasSum_re h2.hasSum).summable
  simp only [← exp_nat_mul, Nat.cast_ofNat, ← exp_add, norm_exp, add_re,
    mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, Real.one_le_exp_iff]
  rw [re_tsum h0, re_tsum h1, re_tsum h2, ← tsum_mul_left,
    ← tsum_mul_left, ← hs0.tsum_add hs1, ← (hs0.add hs1).tsum_add hs2]
  exact tsum_nonneg fun p => re_neg_log_dvp_nonneg (ha0 p) (ha1 p) (hz p)

/-- Powers of a unit complex number still have squared norm one. -/
theorem normSq_pow_eq_one
    (z : Complex) (hz : Complex.normSq z = 1) (n : Nat) :
    Complex.normSq (z ^ n) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Complex.normSq_mul, ih, hz, one_mul]

/--
The local coefficient used for Wiener--Ikehara is exactly a squared norm.
For a unitary value `z`, this is the real number `2 + z + conjugate z`.
-/
theorem wiener_ikehara_coefficient_eq_normSq
    (z : Complex) (hz : Complex.normSq z = 1) :
    2 + z.re + (starRingEnd Complex z).re = Complex.normSq (1 + z) := by
  rw [Complex.normSq_add]
  simp [hz]
  ring

/-- Disk form of the nonnegative Wiener--Ikehara coefficient identity. -/
theorem wiener_ikehara_disk_coefficient_identity (z : Complex) :
    2 + z.re + (starRingEnd Complex z).re =
      Complex.normSq (1 + z) + (1 - Complex.normSq z) := by
  rw [Complex.normSq_add]
  simp
  ring

/-- The Wiener--Ikehara coefficient remains nonnegative at omitted factors. -/
theorem wiener_ikehara_disk_coefficient_nonneg
    (z : Complex) (hz : Complex.normSq z <= 1) :
    0 <= 2 + z.re + (starRingEnd Complex z).re := by
  rw [wiener_ikehara_disk_coefficient_identity]
  exact add_nonneg (Complex.normSq_nonneg _) (sub_nonneg.mpr hz)

/-- Hence the Wiener--Ikehara coefficient is nonnegative. -/
theorem wiener_ikehara_coefficient_nonneg
    (z : Complex) (hz : Complex.normSq z = 1) :
    0 <= 2 + z.re + (starRingEnd Complex z).re := by
  rw [wiener_ikehara_coefficient_eq_normSq z hz]
  exact Complex.normSq_nonneg _

/-- The prime-power form needed for the logarithmic derivative. -/
theorem wiener_ikehara_power_coefficient_nonneg
    (z : Complex) (hz : Complex.normSq z = 1) (n : Nat) :
    0 <= 2 + (z ^ n).re + (starRingEnd Complex (z ^ n)).re :=
  wiener_ikehara_coefficient_nonneg (z ^ n) (normSq_pow_eq_one z hz n)

/--
Subtracting twice the untwisted Wiener--Ikehara asymptotic from the positive
twist asymptotic gives cancellation of the real character coefficients.
-/
theorem real_character_cancellation_of_wiener_ikehara
    (base twist positive : Nat → Real)
    (hCoeff : ∀ n, positive n = 2 * base n + 2 * twist n)
    (hPositive :
      Tendsto (normalizedPartialSum positive) atTop (nhds 2))
    (hBase :
      Tendsto (normalizedPartialSum base) atTop (nhds 1)) :
    Tendsto (normalizedPartialSum twist) atTop (nhds 0) := by
  have hDifference :
      Tendsto
        (fun N => normalizedPartialSum positive N -
          2 * normalizedPartialSum base N)
        atTop (nhds 0) := by
    convert hPositive.sub (hBase.const_mul 2) using 1
    all_goals norm_num
  have hIdentity :
      (fun N => (normalizedPartialSum positive N -
          2 * normalizedPartialSum base N) / 2) =
        normalizedPartialSum twist := by
    funext N
    simp only [normalizedPartialSum]
    rw [Finset.sum_congr rfl (fun n hn => hCoeff n)]
    rw [Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [← hIdentity]
  convert hDifference.div_const 2 using 1
  all_goals norm_num

#check @de_la_vallee_poussin_nonneg
#check @de_la_vallee_poussin_disk_nonneg
#check @re_neg_log_dvp_nonneg
#print axioms re_neg_log_dvp_nonneg
#check @norm_exp_tsum_dvp_ge_one
#print axioms norm_exp_tsum_dvp_ge_one
#check @wiener_ikehara_power_coefficient_nonneg
#print axioms wiener_ikehara_power_coefficient_nonneg
#check @real_character_cancellation_of_wiener_ikehara
#check fermatFrobeniusTrace_seven
#print axioms fermatFrobeniusTrace_seven
#check @not_isOfFinOrder_of_fermatTrace_seven
#print axioms not_isOfFinOrder_of_fermatTrace_seven
#check @pow_ne_one_of_fermatTrace_seven

end K3Lean.WikipediaHeckePositivity
