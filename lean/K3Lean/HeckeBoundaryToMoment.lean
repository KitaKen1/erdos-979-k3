import K3Lean.HeckeMomentAdapters
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Linearity

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# From a Hecke L-function boundary theorem to a prime moment

This file isolates the analytic adapter that will sit immediately below
Hecke's general theorem.  Its input is not a prime-distribution conclusion:
it is a holomorphic, nonvanishing L-function whose logarithmic derivative has
the expected Dirichlet series on `re s > 1`.

The Riemann-zeta part is discharged entirely from Mathlib.  The only
Tauberian input is the Blueprint-audited Wiener--Ikehara theorem from
`K3Lean.AuditedWienerIkehara`.
-/

namespace K3Lean.HeckeBoundaryToMoment

open ArithmeticFunction Complex Filter Set Topology
open K3Lean.AuditedWienerIkehara
open K3Lean.HeckeMomentAdapters
open scoped BigOperators Topology

noncomputable section

/-- The open half-plane on which the Hecke continuations are actually used. -/
def heckeContinuationDomain : Set Complex :=
  {s : Complex | (1 / 2 : Real) < s.re}

theorem isOpen_heckeContinuationDomain : IsOpen heckeContinuationDomain := by
  exact isOpen_lt continuous_const continuous_re

theorem closedUnitHalfPlane_subset_heckeContinuationDomain :
    {s : Complex | 1 <= s.re} ⊆ heckeContinuationDomain := by
  intro s hs
  change 1 <= s.re at hs
  change (1 / 2 : Real) < s.re
  exact lt_of_lt_of_le (by norm_num) hs

/-- The Riemann zeta function with its simple pole at `1` removed. -/
def regularizedRiemannZeta (s : Complex) : Complex :=
  Function.update (fun z : Complex => (z - 1) * riemannZeta z) 1 1 s

@[simp]
theorem regularizedRiemannZeta_one : regularizedRiemannZeta 1 = 1 := by
  simp [regularizedRiemannZeta]

theorem regularizedRiemannZeta_of_ne_one
    {s : Complex} (hs : s ≠ 1) :
    regularizedRiemannZeta s = (s - 1) * riemannZeta s := by
  simp [regularizedRiemannZeta, hs]

theorem differentiableAt_regularizedRiemannZeta_of_ne_one
    {s : Complex} (hs : s ≠ 1) :
    DifferentiableAt Complex regularizedRiemannZeta s := by
  apply DifferentiableAt.congr_of_eventuallyEq
    ((differentiableAt_id.sub (differentiableAt_const (c := (1 : Complex)))).mul
      (differentiableAt_riemannZeta hs))
  filter_upwards [eventually_ne_nhds hs] with z hz
  exact regularizedRiemannZeta_of_ne_one hz

/-- The pole removal is an entire function. -/
theorem differentiable_regularizedRiemannZeta :
    Differentiable Complex regularizedRiemannZeta := by
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · refine
      (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z ≠ 1 := by simpa using hz
      exact differentiableAt_regularizedRiemannZeta_of_ne_one hz'
    · change ContinuousAt
        (Function.update
          (fun z : Complex => (z - 1) * riemannZeta z) 1 1) 1
      rw [continuousAt_update_same]
      exact riemannZeta_residue_one
  · exact differentiableAt_regularizedRiemannZeta_of_ne_one hs

/-- The regularized zeta function has no zeros on `re s >= 1`. -/
theorem regularizedRiemannZeta_ne_zero
    {s : Complex} (hs : 1 <= s.re) :
    regularizedRiemannZeta s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hsOne
  · simp
  · rw [regularizedRiemannZeta_of_ne_one hsOne]
    exact mul_ne_zero (sub_ne_zero.mpr hsOne)
      (riemannZeta_ne_zero_of_one_le_re hs)

/-- The continuous boundary correction for the von Mangoldt L-series. -/
def zetaLogDerivativeCorrection (s : Complex) : Complex :=
  -deriv regularizedRiemannZeta s / regularizedRiemannZeta s

theorem continuousOn_zetaLogDerivativeCorrection :
    ContinuousOn zetaLogDerivativeCorrection {s : Complex | 1 <= s.re} := by
  have hDeriv : Differentiable Complex (deriv regularizedRiemannZeta) :=
    differentiableOn_univ.mp
      (differentiable_regularizedRiemannZeta.differentiableOn.deriv isOpen_univ)
  exact hDeriv.continuous.continuousOn.neg.div
    differentiable_regularizedRiemannZeta.continuous.continuousOn
    (fun s hs => regularizedRiemannZeta_ne_zero hs)

/-- On `re s > 1`, the correction is `-zeta'/zeta - 1/(s-1)`. -/
theorem zetaLogDerivativeCorrection_eq
    {s : Complex} (hs : 1 < s.re) :
    zetaLogDerivativeCorrection s =
      LSeries (fun n => (vonMangoldt n : Complex)) s - 1 / (s - 1) := by
  have hsOne : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hDerivEq :
      deriv regularizedRiemannZeta s =
        riemannZeta s + (s - 1) * deriv riemannZeta s := by
    have hLocal : regularizedRiemannZeta =ᶠ[nhds s]
        (fun z : Complex => (z - 1) * riemannZeta z) := by
      filter_upwards [eventually_ne_nhds hsOne] with z hz
      exact regularizedRiemannZeta_of_ne_one hz
    rw [hLocal.deriv_eq]
    have hProduct :=
      ((hasDerivAt_id s).sub_const (1 : Complex)).mul
        (differentiableAt_riemannZeta hsOne).hasDerivAt
    change deriv ((fun z : Complex => z - 1) * riemannZeta) s =
      riemannZeta s + (s - 1) * deriv riemannZeta s
    simpa using hProduct.deriv
  rw [zetaLogDerivativeCorrection, regularizedRiemannZeta_of_ne_one hsOne,
    hDerivEq, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  have hSub : s - 1 ≠ 0 := sub_ne_zero.mpr hsOne
  have hZeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hs
  field_simp [hSub, hZeta]
  <;> ring

/--
Analytic data supplied by a nontrivial unitary Hecke L-function after its
ideal coefficients have been grouped by their rational norm.

The coefficient `c n` is normalized so that the logarithmic derivative is
`2 * c n * Lambda(n)`.  For a split rational prime this makes `c p` the
cosine of the Frobenius angle.
-/
def HeckeLogDerivativeData (c : Nat -> Real) : Prop :=
  exists L : Complex -> Complex,
    DifferentiableOn Complex L heckeContinuationDomain /\
    (forall s : Complex, 1 <= s.re -> L s ≠ 0) /\
    forall s : Complex, 1 < s.re ->
      LSeries (fun n => ((c n * vonMangoldt n : Real) : Complex)) s =
        -deriv L s / (2 * L s)

/-- A Hecke logarithmic derivative is continuous on the closed right half-plane. -/
theorem heckeLogDerivative_continuousOn
    {L : Complex -> Complex}
    (hDiff : DifferentiableOn Complex L heckeContinuationDomain)
    (hNonzero : forall s : Complex, 1 <= s.re -> L s ≠ 0) :
    ContinuousOn (fun s => -deriv L s / (2 * L s))
      {s : Complex | 1 <= s.re} := by
  have hDeriv : ContinuousOn (deriv L) {s : Complex | 1 <= s.re} :=
    (hDiff.deriv isOpen_heckeContinuationDomain).continuousOn.mono
      closedUnitHalfPlane_subset_heckeContinuationDomain
  have hL : ContinuousOn L {s : Complex | 1 <= s.re} :=
    hDiff.continuousOn.mono closedUnitHalfPlane_subset_heckeContinuationDomain
  exact hDeriv.neg.div
    (continuousOn_const.mul hL)
    (fun s hs => mul_ne_zero (by norm_num) (hNonzero s hs))

/-- The positive coefficient used by Wiener--Ikehara. -/
def positiveHeckeCoefficient (c : Nat -> Real) (n : Nat) : Real :=
  2 * vonMangoldt n + 2 * (c n * vonMangoldt n)

theorem positiveHeckeCoefficient_identity (c : Nat -> Real) (n : Nat) :
    positiveHeckeCoefficient c n =
      2 * vonMangoldt n + 2 * (c n * vonMangoldt n) := rfl

theorem positiveHeckeCoefficient_nonneg
    (c : Nat -> Real) (hc : forall n, |c n| <= 1) :
    0 <= positiveHeckeCoefficient c := by
  intro n
  have hcLower : -1 <= c n := (abs_le.mp (hc n)).1
  have hLambda : 0 <= vonMangoldt n := vonMangoldt_nonneg (n := n)
  rw [positiveHeckeCoefficient]
  have hOnePlus : 0 <= 1 + c n := by linarith
  calc
    0 <= 2 * ((1 + c n) * vonMangoldt n) :=
      mul_nonneg (by norm_num) (mul_nonneg hOnePlus hLambda)
    _ = 2 * vonMangoldt n + 2 * (c n * vonMangoldt n) := by ring

theorem LSeriesSummable_real_mul_vonMangoldt
    (c : Nat -> Real) (hc : forall n, |c n| <= 1)
    {s : Complex} (hs : 1 < s.re) :
    LSeriesSummable
      (fun n => ((c n * vonMangoldt n : Real) : Complex)) s := by
  have hBase := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  rw [LSeriesSummable] at hBase ⊢
  apply Summable.of_norm
  refine hBase.norm.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
  apply LSeries.norm_term_le
  calc
    ‖((c n * vonMangoldt n : Real) : Complex)‖ =
        |c n| * |vonMangoldt n| := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    _ <= 1 * |vonMangoldt n| :=
      mul_le_mul_of_nonneg_right (hc n) (abs_nonneg _)
    _ = ‖((vonMangoldt n : Real) : Complex)‖ := by
      rw [one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem nterm_vonMangoldt_summable
    {sigma : Real} (hsigma : 1 < sigma) :
    Summable (nterm (fun n => ((vonMangoldt n : Real) : Complex)) sigma) := by
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (sigma : Complex)) (by simpa using hsigma)
  rw [LSeriesSummable] at h
  convert h.norm using 1
  funext n
  rw [LSeries.norm_term_eq]
  simp only [nterm, ofReal_re, norm_real,
    abs_of_nonneg (vonMangoldt_nonneg (n := n))]

theorem nterm_positiveHeckeCoefficient_summable
    (c : Nat -> Real) (hc : forall n, |c n| <= 1)
    {sigma : Real} (hsigma : 1 < sigma) :
    Summable
      (nterm (fun n => ((positiveHeckeCoefficient c n : Real) : Complex)) sigma) := by
  have hBase := nterm_vonMangoldt_summable hsigma
  refine (hBase.mul_left 4).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · rw [nterm]
    split_ifs <;> positivity
  by_cases hn : n = 0
  · subst n
    simp [nterm]
  have hLambda : 0 <= vonMangoldt n := vonMangoldt_nonneg (n := n)
  have hPos : 0 <= positiveHeckeCoefficient c n :=
    positiveHeckeCoefficient_nonneg c hc n
  have hCoeff : positiveHeckeCoefficient c n <= 4 * vonMangoldt n := by
    rw [positiveHeckeCoefficient]
    have := (abs_le.mp (hc n)).2
    nlinarith [mul_le_mul_of_nonneg_right this hLambda]
  have hnPos : (0 : Real) < n := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  simp only [nterm, if_neg hn]
  simp only [norm_real, Real.norm_eq_abs, abs_of_nonneg hPos,
    abs_of_nonneg hLambda]
  calc
    positiveHeckeCoefficient c n / (n : Real) ^ sigma <=
        (4 * vonMangoldt n) / (n : Real) ^ sigma :=
      (div_le_div_iff_of_pos_right (Real.rpow_pos_of_pos hnPos _)).2 hCoeff
    _ = 4 * (vonMangoldt n / (n : Real) ^ sigma) := by ring

/--
The source-facing Hecke boundary data imply the required unweighted prime
sum cancellation.  All Tauberian and logarithmic-weight removal steps occur
in Lean below this boundary.
-/
theorem unweighted_prime_sum_of_heckeLogDerivativeData
    (hWI : PNTPlusWienerIkehara)
    (c : Nat -> Real)
    (hc : forall n, |c n| <= 1)
    (hHecke : HeckeLogDerivativeData c) :
    Tendsto
      (fun x => K3Lean.LogWeightRemoval.unweightedPrimeSum c x /
        (x / Real.log x))
      atTop (nhds 0) := by
  rcases hHecke with ⟨L, hLDiff, hLNonzero, hLogDerivative⟩
  let GHecke : Complex -> Complex := fun s => -deriv L s / (2 * L s)
  let GPositive : Complex -> Complex := fun s =>
    2 * zetaLogDerivativeCorrection s + 2 * GHecke s
  have hGHecke : ContinuousOn GHecke {s : Complex | 1 <= s.re} := by
    simpa [GHecke] using heckeLogDerivative_continuousOn hLDiff hLNonzero
  have hGPositive : ContinuousOn GPositive {s : Complex | 1 <= s.re} := by
    exact (continuousOn_const.mul continuousOn_zetaLogDerivativeCorrection).add
      (continuousOn_const.mul hGHecke)
  refine unweighted_prime_sum_from_pnt_plus
      (hWI := hWI) (c := c) (C := 1) (hC := by norm_num) (hc := hc)
      (base := vonMangoldt) (positive := positiveHeckeCoefficient c)
      (hCoeff := positiveHeckeCoefficient_identity c)
      (hPositiveNonneg := positiveHeckeCoefficient_nonneg c hc)
      (hPositiveSummable := fun sigma hsigma =>
        nterm_positiveHeckeCoefficient_summable c hc hsigma)
      (GPositive := GPositive) (hPositiveContinuous := hGPositive)
      (hBaseNonneg := fun n => vonMangoldt_nonneg (n := n))
      (hBaseSummable := fun sigma hsigma => nterm_vonMangoldt_summable hsigma)
      (GBase := zetaLogDerivativeCorrection)
      (hBaseContinuous := continuousOn_zetaLogDerivativeCorrection)
      (hBaseEq := fun s hs => zetaLogDerivativeCorrection_eq hs) ?_
  · intro s hs
    change 1 < s.re at hs
    change GPositive s =
      LSeries (fun n => ((positiveHeckeCoefficient c n : Real) : Complex)) s -
        (2 : Complex) / (s - 1)
    rw [show GPositive s =
        2 * zetaLogDerivativeCorrection s + 2 * GHecke s by rfl]
    rw [zetaLogDerivativeCorrection_eq hs, show GHecke s =
        LSeries (fun n => ((c n * vonMangoldt n : Real) : Complex)) s by
          simpa [GHecke] using (hLogDerivative s hs).symm]
    let base : Nat -> Complex := fun n => (vonMangoldt n : Complex)
    let twist : Nat -> Complex := fun n => ((c n * vonMangoldt n : Real) : Complex)
    have hBase : LSeriesSummable base s := by
      simpa [base] using ArithmeticFunction.LSeriesSummable_vonMangoldt hs
    have hTwist : LSeriesSummable twist s := by
      simpa [twist] using LSeriesSummable_real_mul_vonMangoldt c hc hs
    have hCoeff :
        (fun n => ((positiveHeckeCoefficient c n : Real) : Complex)) =
          (2 : Complex) • base + (2 : Complex) • twist := by
      funext n
      simp [base, twist, positiveHeckeCoefficient]
    rw [hCoeff, LSeries_add (hBase.smul 2) (hTwist.smul 2),
      LSeries_smul, LSeries_smul]
    ring

#check @HeckeLogDerivativeData
#check @unweighted_prime_sum_of_heckeLogDerivativeData
#print axioms unweighted_prime_sum_of_heckeLogDerivativeData

end

end K3Lean.HeckeBoundaryToMoment
