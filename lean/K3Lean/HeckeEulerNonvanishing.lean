import K3Lean.HeckeTwoMomentBoundary
import K3Lean.WikipediaHeckeBoundary

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Removing boundary nonvanishing from the Hecke hypothesis

Wikipedia defines a Hecke L-function by an Euler product and states that a
nontrivial Hecke character has analytic continuation.  This file packages
that source-level data for all positive powers of one unitary character and
proves the missing nonvanishing on `re s = 1` by the classical de la Vallee
Poussin argument already checked in `WikipediaHeckeBoundary`.

The index type below is instantiated mathematically by prime ideals away from
the conductor.  It is intentionally arbitrary: the proof uses only the Euler
factors, not a project-specific CM-sector theorem.

Source:

* https://en.wikipedia.org/wiki/Hecke_character#Relationship_between_Gr%C3%B6%C3%9Fencharakter_and_Hecke_character
* https://swc-math.github.io/aws/2016/2016SutherlandNotes.pdf#page=17
-/

namespace K3Lean.HeckeEulerNonvanishing

open Asymptotics Complex Filter Set Topology
open K3Lean.HeckeBoundaryToMoment
open K3Lean.HeckeTwoMomentBoundary
open K3Lean.WikipediaHeckeBoundary
open scoped Topology

noncomputable section

/-- The only character powers used by the two-moment zero-free argument. -/
def RequiredHeckePower (m : Nat) : Prop :=
  m = 1 ∨ m = 2 ∨ m = 4

/-- The two powers whose logarithmic derivatives enter the moment argument. -/
def MomentHeckePower (m : Nat) : Prop :=
  m = 1 ∨ m = 2

theorem requiredHeckePower_of_moment
    {m : Nat} (hm : MomentHeckePower m) : RequiredHeckePower m := by
  rcases hm with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

theorem requiredHeckePower_two_mul_of_moment
    {m : Nat} (hm : MomentHeckePower m) : RequiredHeckePower (2 * m) := by
  rcases hm with rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/--
A source-level family of Euler products for the powers of one unitary Hecke
character.  `baseL` is the trivial-character (Dedekind-zeta) factor and
`powerL m` is the L-function of the `m`th power.

For a horizontal point `1 + x + I*t`, `radius x q` is the positive norm
factor and `localValue m t q` is the unit-disk character/phase factor.  The square
law is exactly the fact that the local value of the `2m`th power at height
`2t` is the square of the `m`th value at height `t`.
-/
structure UnitaryHeckeEulerFamily where
  PrimeIndex : Type
  radius : Real -> PrimeIndex -> Real
  localValue : Nat -> Real -> PrimeIndex -> Complex
  baseL : Complex -> Complex
  powerL : Nat -> Complex -> Complex
  radius_nonneg : forall x : Real, 0 < x -> forall q, 0 <= radius x q
  radius_lt_one : forall x : Real, 0 < x -> forall q, radius x q < 1
  local_normSq_le_one : forall m t q, Complex.normSq (localValue m t q) <= 1
  local_sq : forall m t q,
    localValue (2 * m) (2 * t) q = (localValue m t q) ^ 2
  summable_base : forall x : Real, 0 < x ->
    Summable (fun q => -Complex.log (1 - (radius x q : Complex)))
  summable_power : forall m (t x : Real), 0 < x ->
    Summable
      (fun q => -Complex.log (1 - (radius x q : Complex) * localValue m t q))
  base_euler : forall x : Real, 0 < x ->
    baseL (1 + x) =
      Complex.exp
        (∑' q, -Complex.log (1 - (radius x q : Complex)))
  power_euler : forall m (t x : Real), 0 < x ->
    powerL m (1 + x + Complex.I * t) =
      Complex.exp
        (∑' q,
          -Complex.log (1 - (radius x q : Complex) * localValue m t q))
  base_simple_pole :
    (fun x : Real => baseL (1 + x)) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun x : Real => (1 : Complex) / x)
  power_holomorphic : forall m : Nat, RequiredHeckePower m ->
    DifferentiableOn Complex (powerL m) heckeContinuationDomain

namespace UnitaryHeckeEulerFamily

/-- The de la Vallee Poussin product excludes a boundary zero. -/
theorem powerL_ne_zero_on_boundary
    (F : UnitaryHeckeEulerFamily) (m : Nat) (hm : MomentHeckePower m) (t : Real) :
    F.powerL m (1 + Complex.I * t) ≠ 0 := by
  apply boundary_ne_zero_of_euler_logs
      F.baseL (F.powerL m) (F.powerL (2 * m)) t
      F.radius (F.localValue m t)
  · exact F.base_simple_pole
  · exact ((F.power_holomorphic m (requiredHeckePower_of_moment hm)) _
      (by norm_num [heckeContinuationDomain])).differentiableAt
      (isOpen_heckeContinuationDomain.mem_nhds
        (by norm_num [heckeContinuationDomain]))
  · exact ((F.power_holomorphic (2 * m)
      (requiredHeckePower_two_mul_of_moment hm)) _
      (by norm_num [heckeContinuationDomain])).differentiableAt
      (isOpen_heckeContinuationDomain.mem_nhds
        (by norm_num [heckeContinuationDomain]))
  · exact F.radius_nonneg
  · exact F.radius_lt_one
  · exact F.local_normSq_le_one m t
  · exact F.summable_base
  · exact F.summable_power m t
  · intro x hx
    simpa only [F.local_sq m t] using F.summable_power (2 * m) (2 * t) x hx
  · exact F.base_euler
  · exact F.power_euler m t
  · intro x hx
    have hPoint :
        (1 + (x : Complex) + Complex.I * ((2 * t : Real) : Complex)) =
          1 + (x : Complex) + 2 * Complex.I * (t : Complex) := by
      push_cast
      ring
    rw [← hPoint]
    simpa only [F.local_sq m t] using F.power_euler (2 * m) (2 * t) x hx

/-- Euler products handle `re s > 1`; the preceding theorem handles the boundary. -/
theorem powerL_ne_zero_on_closed_halfPlane
    (F : UnitaryHeckeEulerFamily) (m : Nat) (hm : MomentHeckePower m)
    (s : Complex) (hs : 1 <= s.re) :
    F.powerL m s ≠ 0 := by
  by_cases hInterior : 1 < s.re
  · let x : Real := s.re - 1
    have hx : 0 < x := sub_pos.mpr hInterior
    have hsForm : (1 + x + Complex.I * s.im : Complex) = s := by
      apply Complex.ext
      · simp [x]
      · simp
    rw [← hsForm, F.power_euler m s.im x hx]
    exact Complex.exp_ne_zero _
  · have hRe : s.re = 1 := le_antisymm (le_of_not_gt hInterior) hs
    have hsForm : (1 + Complex.I * s.im : Complex) = s := by
      apply Complex.ext
      · simpa using hRe.symm
      · simp
    rw [← hsForm]
    exact F.powerL_ne_zero_on_boundary m hm s.im

end UnitaryHeckeEulerFamily

/--
The Hecke input before nonvanishing is proved: analytic continuation of the
Euler-product family, its first two logarithmic derivatives, and the local
prime coefficients attached to the two Frobenius-angle powers.
-/
def FirstTwoHolomorphicHeckeData (theta : Nat -> Real) : Prop :=
  exists F : UnitaryHeckeEulerFamily,
  exists c1 c2 : Nat -> Real,
    (forall n, |c1 n| <= 1) /\
    (forall n, |c2 n| <= 1) /\
    HasSplitPrimeCoefficients theta 1 c1 /\
    HasSplitPrimeCoefficients theta 2 c2 /\
    (forall s : Complex, 1 < s.re ->
      LSeries (fun n => ((c1 n * ArithmeticFunction.vonMangoldt n : Real) : Complex)) s =
        -deriv (F.powerL 1) s / (2 * F.powerL 1 s)) /\
    (forall s : Complex, 1 < s.re ->
      LSeries (fun n => ((c2 n * ArithmeticFunction.vonMangoldt n : Real) : Complex)) s =
        -deriv (F.powerL 2) s / (2 * F.powerL 2 s))

/-- The proved zero-free argument converts holomorphy data to the former boundary data. -/
theorem firstTwoBoundaryData_of_holomorphicData
    (theta : Nat -> Real)
    (h : FirstTwoHolomorphicHeckeData theta) :
    FirstTwoHeckeLBoundaryData theta := by
  rcases h with
    ⟨F, c1, c2, hc1, hc2, hPrime1, hPrime2, hLog1, hLog2⟩
  refine ⟨c1, c2, hc1, hc2, hPrime1, hPrime2, ?_, ?_⟩
  · exact ⟨F.powerL 1, F.power_holomorphic 1 (Or.inl rfl),
      F.powerL_ne_zero_on_closed_halfPlane 1 (Or.inl rfl), hLog1⟩
  · exact ⟨F.powerL 2, F.power_holomorphic 2 (Or.inr (Or.inl rfl)),
      F.powerL_ne_zero_on_closed_halfPlane 2 (Or.inr rfl), hLog2⟩

#check @UnitaryHeckeEulerFamily
#check @RequiredHeckePower
#check @UnitaryHeckeEulerFamily.powerL_ne_zero_on_boundary
#print axioms UnitaryHeckeEulerFamily.powerL_ne_zero_on_boundary
#check @FirstTwoHolomorphicHeckeData
#check @firstTwoBoundaryData_of_holomorphicData
#print axioms firstTwoBoundaryData_of_holomorphicData

end

end K3Lean.HeckeEulerNonvanishing
