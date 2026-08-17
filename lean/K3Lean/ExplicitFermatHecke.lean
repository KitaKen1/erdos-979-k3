import K3Lean.HeckeEulerNonvanishing
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.LSeries.Deriv

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Explicit rational coefficients of the Fermat-cubic Hecke Euler product

For a rational prime `p != 3`, the field `Q(sqrt(-3))` has two possible
unramified local shapes.

* If `p = 1 mod 3`, there are two degree-one prime ideals.  Their unitary
  values are conjugate, so the coefficient at `p^k` is
  `cos (m * k * theta p)` after division by two.
* If `p = 2 mod 3`, there is one degree-two prime ideal.  Its normalized
  Fermat Hecke value is `-1`, so it contributes at `p^(2r)` with phase
  `(-1)^(m*r)` for the `m`th character power.

The definitions below make this elementary grouping explicit.  The only
remaining source-facing equality says that the Hecke Euler product is the
exponential of this grouped Euler logarithm on `re s > 1`.  Lean then proves
the coefficient bound and differentiates the L-series; neither is retained
as an external Hecke hypothesis.
-/

namespace K3Lean.ExplicitFermatHecke

open Complex Filter
open K3Lean.HeckeBoundaryToMoment
open K3Lean.HeckeCosineCancellation
open K3Lean.HeckeEulerNonvanishing
open K3Lean.HeckeTwoMomentBoundary
open scoped Topology

noncomputable section

/-- The exponent in the canonical prime-power presentation of `n`. -/
def primePowerExponent (n : Nat) : Nat :=
  n.factorization n.minFac

/--
The rationally grouped coefficient of the `m`th unitary Fermat Hecke power.
It is zero off prime powers and at the ramified prime `3`.
-/
def fermatHeckeCoefficient
    (theta : Nat -> Real) (m n : Nat) : Real :=
  if h : IsPrimePow n then
    let p := n.minFac
    let k := primePowerExponent n
    if p % 3 = 1 then
      Real.cos (((m * k : Nat) : Real) * theta p)
    else if p % 3 = 2 ∧ Even k then
      (-1 : Real) ^ (m * (k / 2))
    else
      0
  else
    0

/--
Coefficient of the logarithm of the Euler product.  At `n = p^k` it is
`2 * c_m(n) / k`; the factor two accounts for the quadratic field degree.
-/
def fermatHeckeEulerLogCoefficient
    (theta : Nat -> Real) (m n : Nat) : Complex :=
  if h : IsPrimePow n then
    (((2 : Real) / primePowerExponent n) *
      fermatHeckeCoefficient theta m n : Real)
  else
    0

theorem primePowerExponent_pos {n : Nat} (hn : IsPrimePow n) :
    0 < primePowerExponent n := by
  exact Nat.pos_of_ne_zero (Nat.factorization_minFac_ne_zero hn.one_lt)

/-- Every grouped coefficient lies in the closed unit interval. -/
theorem abs_fermatHeckeCoefficient_le_one
    (theta : Nat -> Real) (m n : Nat) :
    |fermatHeckeCoefficient theta m n| <= 1 := by
  by_cases hn : IsPrimePow n
  · rw [fermatHeckeCoefficient, dif_pos hn]
    dsimp only
    by_cases hSplit : n.minFac % 3 = 1
    · rw [if_pos hSplit]
      exact Real.abs_cos_le_one _
    · rw [if_neg hSplit]
      by_cases hInert : n.minFac % 3 = 2 ∧ Even (primePowerExponent n)
      · simp [hInert]
      · simp [hInert]
  · simp [fermatHeckeCoefficient, hn]

/-- At a split rational prime the grouped coefficient is the desired cosine. -/
theorem fermatHeckeCoefficient_prime
    (theta : Nat -> Real) (m p : Nat) (hp : Nat.Prime p) :
    fermatHeckeCoefficient theta m p =
      splitCosineCoefficient theta m p := by
  rw [fermatHeckeCoefficient, splitCosineCoefficient]
  simp only [hp, true_and, hp.prime.isPrimePow, dite_true,
    hp.minFac_eq, primePowerExponent, hp.factorization_self,
    mul_one, Nat.cast_one]
  by_cases hSplit : p % 3 = 1
  · simp [hSplit]
  · have hNotInertContribution :
        ¬(p % 3 = 2 && Even (1 : Nat)) := by simp
    simp [hSplit, hNotInertContribution]

theorem hasSplitPrimeCoefficients_fermat
    (theta : Nat -> Real) (m : Nat) :
    HasSplitPrimeCoefficients theta m
      (fermatHeckeCoefficient theta m) := by
  intro p hp
  exact fermatHeckeCoefficient_prime theta m p hp

/-- The Euler-log coefficient is uniformly bounded by two. -/
theorem norm_fermatHeckeEulerLogCoefficient_le_two
    (theta : Nat -> Real) (m n : Nat) :
    ‖fermatHeckeEulerLogCoefficient theta m n‖ <= 2 := by
  rw [fermatHeckeEulerLogCoefficient]
  split_ifs with hn
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hk : (1 : Real) <= primePowerExponent n := by
      exact_mod_cast (primePowerExponent_pos hn)
    have hdiv : |(2 : Real) / primePowerExponent n| <= 2 := by
      rw [abs_of_nonneg (div_nonneg (by norm_num) (by positivity))]
      exact (div_le_iff₀ (by positivity : (0 : Real) < primePowerExponent n)).2
        (by nlinarith)
    calc
      |(2 : Real) / primePowerExponent n| *
          |fermatHeckeCoefficient theta m n| <=
          2 * 1 :=
        mul_le_mul hdiv (abs_fermatHeckeCoefficient_le_one theta m n)
          (abs_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  · norm_num

theorem fermatHeckeEulerLog_abscissa_le_one
    (theta : Nat -> Real) (m : Nat) :
    LSeries.abscissaOfAbsConv
        (fermatHeckeEulerLogCoefficient theta m) <= 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_le_const
  exact ⟨2, fun n _hn =>
    norm_fermatHeckeEulerLogCoefficient_le_two theta m n⟩

/--
Termwise identity behind the logarithmic derivative.  This is the precise
prime-power bookkeeping which was formerly hidden in the external `c_m`.
-/
theorem logMul_fermatHeckeEulerLogCoefficient
    (theta : Nat -> Real) (m n : Nat) :
    LSeries.logMul (fermatHeckeEulerLogCoefficient theta m) n =
      (2 : Complex) *
        (((fermatHeckeCoefficient theta m n *
          ArithmeticFunction.vonMangoldt n : Real) : Complex)) := by
  by_cases hn : IsPrimePow n
  · let p := n.minFac
    let k := primePowerExponent n
    have hkNat : 0 < k := primePowerExponent_pos hn
    have hkReal : (k : Real) ≠ 0 := by exact_mod_cast hkNat.ne'
    have hkComplex : (k : Complex) ≠ 0 := by exact_mod_cast hkNat.ne'
    have hnPow : p ^ k = n := by
      exact hn.minFac_pow_factorization_eq
    have hLogReal : Real.log n = (k : Real) * Real.log p := by
      rw [← hnPow, Nat.cast_pow, Real.log_pow]
    have hLogComplex : Complex.log n =
        ((k : Real) * Real.log p : Real) := by
      rw [← Complex.natCast_log, hLogReal]
    rw [LSeries.logMul, fermatHeckeEulerLogCoefficient,
      dif_pos hn, ArithmeticFunction.vonMangoldt_apply, if_pos hn]
    change Complex.log n *
        ((((2 : Real) / k) * fermatHeckeCoefficient theta m n : Real) : Complex) =
      (2 : Complex) *
        ((fermatHeckeCoefficient theta m n * Real.log p : Real) : Complex)
    rw [hLogComplex]
    push_cast
    field_simp [hkReal, hkComplex]
  · rw [LSeries.logMul, fermatHeckeEulerLogCoefficient,
      dif_neg hn, fermatHeckeCoefficient, dif_neg hn,
      ArithmeticFunction.vonMangoldt_apply, if_neg hn]
    simp

/-! ## The explicit two-slot Euler product -/

/-- Two possible prime-ideal slots above each rational prime. -/
abbrev FermatEulerSlot := Nat × Fin 2

/-- Norm factor `N(q)^(-(1+x))` for the explicit split/inert local shapes. -/
def fermatEulerRadius (x : Real) (q : FermatEulerSlot) : Real :=
  if hp : Nat.Prime q.1 then
    if hSplit : q.1 % 3 = 1 then
      Real.exp (-(1 + x) * Real.log q.1)
    else if hInert : q.1 % 3 = 2 ∧ q.2 = 0 then
      Real.exp (-2 * (1 + x) * Real.log q.1)
    else
      0
  else
    0

/--
The unitary local value, including the vertical factor `N(q)^(-it)`.
The two split slots have phases `+m theta_p` and `-m theta_p`; the inert
degree-two slot has character value `(-1)^m` and vertical phase `-2t log p`.
-/
def fermatEulerLocalValue
    (theta : Nat -> Real) (m : Nat) (t : Real)
    (q : FermatEulerSlot) : Complex :=
  if hp : Nat.Prime q.1 then
    if hSplit : q.1 % 3 = 1 then
      let characterPhase : Real :=
        if q.2 = 0 then (m : Real) * theta q.1
        else -(m : Real) * theta q.1
      Complex.exp
        ((characterPhase - t * Real.log q.1 : Real) * Complex.I)
    else if hInert : q.1 % 3 = 2 ∧ q.2 = 0 then
      (-1 : Complex) ^ m *
        Complex.exp ((-2 * t * Real.log q.1 : Real) * Complex.I)
    else
      0
  else
    0

theorem fermatEulerRadius_nonneg
    (x : Real) (hx : 0 < x) (q : FermatEulerSlot) :
    0 <= fermatEulerRadius x q := by
  simp only [fermatEulerRadius]
  split_ifs <;> positivity

theorem fermatEulerRadius_lt_one
    (x : Real) (hx : 0 < x) (q : FermatEulerSlot) :
    fermatEulerRadius x q < 1 := by
  rw [fermatEulerRadius]
  split_ifs with hp hSplit hInert
  · rw [Real.exp_lt_one_iff]
    have hlog : 0 < Real.log q.1 :=
      Real.log_pos (by exact_mod_cast hp.one_lt)
    nlinarith
  · rw [Real.exp_lt_one_iff]
    have hlog : 0 < Real.log q.1 :=
      Real.log_pos (by exact_mod_cast hp.one_lt)
    nlinarith
  · norm_num
  · norm_num

theorem fermatEulerLocalValue_normSq_le_one
    (theta : Nat -> Real) (m : Nat) (t : Real)
    (q : FermatEulerSlot) :
    Complex.normSq (fermatEulerLocalValue theta m t q) <= 1 := by
  rw [fermatEulerLocalValue]
  split_ifs with hp hSplit hSlot hInert
  · rw [Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
    norm_num
  · rw [Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
    norm_num
  · have hExp :
        ‖Complex.exp (((-2 * t * Real.log q.1 : Real) : Complex) * Complex.I)‖ = 1 :=
      Complex.norm_exp_ofReal_mul_I _
    rw [Complex.normSq_eq_norm_sq, norm_mul, norm_pow,
      norm_neg, norm_one, one_pow, one_mul, hExp]
    norm_num
  · norm_num
  · norm_num

/-- Powers and vertical shifts obey the square law used by de la Vallee Poussin. -/
theorem fermatEulerLocalValue_sq
    (theta : Nat -> Real) (m : Nat) (t : Real)
    (q : FermatEulerSlot) :
    fermatEulerLocalValue theta (2 * m) (2 * t) q =
      (fermatEulerLocalValue theta m t q) ^ 2 := by
  rw [fermatEulerLocalValue, fermatEulerLocalValue]
  split_ifs with hp hSplit hSlot hInert
  · rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  · rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  · rw [mul_pow, ← pow_mul, ← Complex.exp_nat_mul]
    congr 1
    · rw [Nat.mul_comm]
    · congr 1
      push_cast
      ring
  · norm_num
  · norm_num

/-- The explicit norm factors are summable in every half-plane `re s > 1`. -/
theorem summable_fermatEulerRadius
    (x : Real) (hx : 0 < x) :
    Summable (fermatEulerRadius x) := by
  let majorant : FermatEulerSlot -> Real := fun q =>
    (q.1 : Real) ^ (-(1 + x) : Real)
  have hNat : Summable (fun n : Nat =>
      (n : Real) ^ (-(1 + x) : Real)) := by
    exact Real.summable_nat_rpow.mpr (by linarith)
  have hMajorant : Summable majorant := by
    rw [summable_prod_of_nonneg (f := majorant)
      (by intro q; exact Real.rpow_nonneg (Nat.cast_nonneg q.1) _)]
    constructor
    · intro n
      exact (hasSum_fintype _).summable
    · simpa [majorant, tsum_fintype] using hNat.mul_left 2
  refine hMajorant.of_nonneg_of_le
    (fun q => fermatEulerRadius_nonneg x hx q) (fun q => ?_)
  rw [fermatEulerRadius]
  split_ifs with hp hSplit hInert
  · change Real.exp (-(1 + x) * Real.log q.1) <=
      (q.1 : Real) ^ (-(1 + x) : Real)
    rw [Real.rpow_def_of_pos (by exact_mod_cast hp.pos)]
    ring_nf
    exact le_rfl
  · change Real.exp (-2 * (1 + x) * Real.log q.1) <=
      (q.1 : Real) ^ (-(1 + x) : Real)
    rw [Real.rpow_def_of_pos (by exact_mod_cast hp.pos)]
    apply Real.exp_le_exp.mpr
    have hlog : 0 < Real.log q.1 :=
      Real.log_pos (by exact_mod_cast hp.one_lt)
    nlinarith
  · exact Real.rpow_nonneg (Nat.cast_nonneg q.1) _
  · exact Real.rpow_nonneg (Nat.cast_nonneg q.1) _

theorem fermatEulerLocalValue_norm_le_one
    (theta : Nat -> Real) (m : Nat) (t : Real)
    (q : FermatEulerSlot) :
    ‖fermatEulerLocalValue theta m t q‖ <= 1 := by
  have h := fermatEulerLocalValue_normSq_le_one theta m t q
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (fermatEulerLocalValue theta m t q)]

/-- Absolute convergence of the trivial Euler logarithm. -/
theorem summable_fermatEulerBaseLog
    (x : Real) (hx : 0 < x) :
    Summable
      (fun q : FermatEulerSlot =>
        -Complex.log (1 - (fermatEulerRadius x q : Complex))) := by
  apply Summable.neg
  apply Summable.clog_one_sub
  apply Summable.of_norm
  simpa [Complex.norm_real,
    abs_of_nonneg (fermatEulerRadius_nonneg x hx _)] using
      summable_fermatEulerRadius x hx

/-- Absolute convergence of every powered unitary Euler logarithm. -/
theorem summable_fermatEulerPowerLog
    (theta : Nat -> Real) (m : Nat) (t x : Real) (hx : 0 < x) :
    Summable
      (fun q : FermatEulerSlot =>
        -Complex.log
          (1 - (fermatEulerRadius x q : Complex) *
            fermatEulerLocalValue theta m t q)) := by
  apply Summable.neg
  apply Summable.clog_one_sub
  apply Summable.of_norm
  refine (summable_fermatEulerRadius x hx).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun q => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (fermatEulerRadius_nonneg x hx q)]
  exact mul_le_of_le_one_right
    (fermatEulerRadius_nonneg x hx q)
    (fermatEulerLocalValue_norm_le_one theta m t q)

/-!
This is now the source-facing package.  Its fields are only the standard
analytic assertions attached to the displayed Euler product: absolute
convergence in `re s > 1`, equality with the Euler product, a simple pole for
the trivial factor, and holomorphy for nonzero powers.  The radius, phases,
square law, coefficient sequence, coefficient bound, and logarithmic
derivative are no longer fields supplied by the user.
-/

structure FermatHeckeSourceData (theta : Nat -> Real) where
  baseL : Complex -> Complex
  powerL : Nat -> Complex -> Complex
  base_euler : forall x : Real, 0 < x ->
    baseL (1 + x) =
      Complex.exp
        (∑' q : FermatEulerSlot,
          -Complex.log (1 - (fermatEulerRadius x q : Complex)))
  power_euler : forall m : Nat, forall t x : Real, 0 < x ->
    powerL m (1 + x + Complex.I * t) =
      Complex.exp
        (∑' q : FermatEulerSlot,
          -Complex.log
            (1 - (fermatEulerRadius x q : Complex) *
              fermatEulerLocalValue theta m t q))
  base_simple_pole :
    (fun x : Real => baseL (1 + x)) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun x : Real => (1 : Complex) / x)
  power_holomorphic : forall m : Nat, RequiredHeckePower m ->
    DifferentiableOn Complex (powerL m) heckeContinuationDomain
  power_euler_log : forall m : Nat, forall s : Complex, 1 < s.re ->
    powerL m s =
      Complex.exp
        (LSeries (fermatHeckeEulerLogCoefficient theta m) s)

/--
The source-facing Hecke datum after all elementary rational-prime grouping has
been made explicit.  `power_euler_log` is the logarithmic form of the standard
Euler product on `re s > 1`; `eulerFamily` supplies that Euler product,
holomorphy, and the trivial Dedekind-zeta pole.
-/
structure ExplicitFermatHeckeData (theta : Nat -> Real) where
  eulerFamily : UnitaryHeckeEulerFamily
  power_euler_log : forall m : Nat, forall s : Complex, 1 < s.re ->
    eulerFamily.powerL m s =
      Complex.exp
        (LSeries (fermatHeckeEulerLogCoefficient theta m) s)

/-- Package the explicit two-slot source data into the generic zero-free argument. -/
def FermatHeckeSourceData.toExplicitFermatHeckeData
    {theta : Nat -> Real} (D : FermatHeckeSourceData theta) :
    ExplicitFermatHeckeData theta :=
  { eulerFamily :=
      { PrimeIndex := FermatEulerSlot
        radius := fermatEulerRadius
        localValue := fermatEulerLocalValue theta
        baseL := D.baseL
        powerL := D.powerL
        radius_nonneg := fermatEulerRadius_nonneg
        radius_lt_one := fermatEulerRadius_lt_one
        local_normSq_le_one :=
          fermatEulerLocalValue_normSq_le_one theta
        local_sq := fermatEulerLocalValue_sq theta
        summable_base := summable_fermatEulerBaseLog
        summable_power := summable_fermatEulerPowerLog theta
        base_euler := D.base_euler
        power_euler := D.power_euler
        base_simple_pole := D.base_simple_pole
        power_holomorphic := D.power_holomorphic }
    power_euler_log := D.power_euler_log }

namespace ExplicitFermatHeckeData

/-- Differentiating the explicit Euler logarithm gives its von Mangoldt series. -/
theorem logDerivative
    {theta : Nat -> Real} (D : ExplicitFermatHeckeData theta)
    (m : Nat) (s : Complex) (hs : 1 < s.re) :
    LSeries
        (fun n => (((fermatHeckeCoefficient theta m n *
          ArithmeticFunction.vonMangoldt n : Real) : Complex))) s =
      -deriv (D.eulerFamily.powerL m) s /
        (2 * D.eulerFamily.powerL m s) := by
  let ell : Nat -> Complex := fermatHeckeEulerLogCoefficient theta m
  let coeff : Nat -> Complex := fun n =>
    ((fermatHeckeCoefficient theta m n *
      ArithmeticFunction.vonMangoldt n : Real) : Complex)
  have hAbs : LSeries.abscissaOfAbsConv ell < s.re :=
    (fermatHeckeEulerLog_abscissa_le_one theta m).trans_lt
      (by exact_mod_cast hs)
  have hDerivLog :
      HasDerivAt (LSeries ell)
        (-LSeries (LSeries.logMul ell) s) s :=
    LSeries_hasDerivAt hAbs
  have hDerivExp :
      deriv (fun z => Complex.exp (LSeries ell z)) s =
        Complex.exp (LSeries ell s) *
          (-LSeries (LSeries.logMul ell) s) :=
    hDerivLog.cexp.deriv
  have hOpen : {z : Complex | 1 < z.re} ∈ nhds s :=
    (isOpen_lt continuous_const continuous_re).mem_nhds hs
  have hEventually :
      D.eulerFamily.powerL m =ᶠ[nhds s]
        (fun z => Complex.exp (LSeries ell z)) := by
    filter_upwards [hOpen] with z hz
    exact D.power_euler_log m z hz
  have hDerivL :
      deriv (D.eulerFamily.powerL m) s =
        Complex.exp (LSeries ell s) *
          (-LSeries (LSeries.logMul ell) s) := by
    rw [hEventually.deriv_eq, hDerivExp]
  have hValue : D.eulerFamily.powerL m s =
      Complex.exp (LSeries ell s) := D.power_euler_log m s hs
  have hNonzero : D.eulerFamily.powerL m s ≠ 0 := by
    rw [hValue]
    exact Complex.exp_ne_zero _
  have hLogMul : LSeries (LSeries.logMul ell) s =
      (2 : Complex) * LSeries coeff s := by
    rw [show LSeries.logMul ell = (2 : Complex) • coeff by
      funext n
      simpa [ell, coeff, Pi.smul_apply] using
        logMul_fermatHeckeEulerLogCoefficient theta m n]
    rw [LSeries_smul]
  change LSeries coeff s = _
  rw [hDerivL, hValue, hLogMul]
  field_simp [Complex.exp_ne_zero (LSeries ell s)]

/-- The explicit source datum supplies the former generic first-two-moment package. -/
theorem toFirstTwoHolomorphicHeckeData
    {theta : Nat -> Real} (D : ExplicitFermatHeckeData theta) :
    FirstTwoHolomorphicHeckeData theta := by
  refine ⟨D.eulerFamily,
    fermatHeckeCoefficient theta 1,
    fermatHeckeCoefficient theta 2,
    abs_fermatHeckeCoefficient_le_one theta 1,
    abs_fermatHeckeCoefficient_le_one theta 2,
    hasSplitPrimeCoefficients_fermat theta 1,
    hasSplitPrimeCoefficients_fermat theta 2, ?_, ?_⟩
  · intro s hs
    exact D.logDerivative 1 s hs
  · intro s hs
    exact D.logDerivative 2 s hs

end ExplicitFermatHeckeData

#check @fermatHeckeCoefficient
#check @abs_fermatHeckeCoefficient_le_one
#check @logMul_fermatHeckeEulerLogCoefficient
#check @ExplicitFermatHeckeData
#check @FermatHeckeSourceData
#check @FermatHeckeSourceData.toExplicitFermatHeckeData
#check @ExplicitFermatHeckeData.toFirstTwoHolomorphicHeckeData
#print axioms ExplicitFermatHeckeData.toFirstTwoHolomorphicHeckeData

end

end K3Lean.ExplicitFermatHecke
