import K3Lean.LocalMultiplicativity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Interval

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Source-level external inputs for Erdos Problem 979, k = 3

The declarations in this file are the public assumption boundary.  They do not
mention the representation-counting function, a block certificate, or the
conclusion of Problem 979.

## CM Sato--Tate input

The public final theorem uses the standard counting statement displayed in
the introduction of Chen--Park--Swaminathan:

`# {p <= X : theta_p in I} / # {p <= X} -> mu_CM(I)`.

For `I = [2*pi/3, 5*pi/6]`, the interval avoids the inert atom and has mass
`1/12`.  The CM case is the classical theorem of Hecke.

Source: https://arxiv.org/abs/1506.09170

An alternative weighted source interface is retained below for comparison.

For the projective Fermat cubic `X^3 + Y^3 + Z^3 = 0`, let

`a_p = p + 1 - #E(F_p)` and `a_p = 2 sqrt(p) cos(theta_p)`.

Equation (2) in the introduction of Panidapu--Thorner records the classical
fixed-sector theorem of Hecke--Deuring:

`sum log p = (1/2 * 1_{pi/2 in I} + |I|/(2*pi)) h * (1 + o(1))`.

Taking the dyadic interval `(x, 2x]` and `I = [2*pi/3, 5*pi/6]` gives
exactly the limit `1/12` in `PublishedFermatCMSector` below.  The interval
contains no inert atom.  Theorem 1.1 of that paper is a much stronger
short-interval and shrinking-sector refinement; this project does not need
that extra uniformity.

This angular theorem is not a consequence of the rational PNT in arithmetic
progressions below.  The latter controls Dirichlet characters of the rational
prime `p`; the sector theorem additionally controls powers of a Hecke
Grossencharacter, which retain the angle of a prime factor in the CM field.
See equations (5)--(6) and Section 2.2 of the cited paper for this separation.

Source for the weighted formulation: https://arxiv.org/abs/2105.11093

`FermatCubicLocalTraceFormula` is the elementary local formula

`R_p = (p - 1) (p - 8 - a_p)`

at nonzero-trace good primes.  Here `R_p` is the literal finite count already
defined in Lean.  This formula is proved internally from finite-field
cardinalities; it is not part of the external CM assumption.

## Exceptional-modulus PNT

The second structure records the Landau--Page/Gallagher estimate in the form
used in the proof of Lemma 2.8 of Kevin Ford, *The number of solutions of
phi(x)=m*.  Apart from a possible exceptional conductor, it says

`pi(y; n, a) = y/(phi(n) log y) * (1 + O((log Q)^(-b)))`

uniformly for `n <= 8Q` and `y > Q^(log log Q)`.  We use the standard
equivalent device of marking one prime divisor of the possible exceptional
conductor.

Sources:

* https://doi.org/10.1007/BF01403187
* https://www.kurims.kyoto-u.ac.jp/EMIS/journals/Annals/150_1/ford.pdf
-/

namespace K3Lean.SourceTheorems

open Filter Set
open K3Lean.CMProof
open K3Lean.FiniteLifting
open K3Lean.LocalMultiplicativity
open K3Lean.PublishedInputs
open scoped BigOperators Topology

noncomputable section

def panidapuThornerSourceURL : String :=
  "https://arxiv.org/abs/2105.11093"

def chenParkSwaminathanSourceURL : String :=
  "https://arxiv.org/abs/1506.09170"

def gallagherSourceURL : String :=
  "https://doi.org/10.1007/BF01403187"

def fordSourceURL : String :=
  "https://www.kurims.kyoto-u.ac.jp/EMIS/journals/Annals/150_1/ford.pdf"

/--
Primes in `(X, 2X]` whose normalized Frobenius trace lies in the fixed
negative sector corresponding to angles `[2*pi/3, 5*pi/6]`.
-/
def negativeCMTraceSectorPrimes (X : Nat) : Finset Nat :=
  (Finset.Ioc X (2 * X)).filter (fun p =>
    Nat.Prime p ∧ 3 < p ∧
      normalizedFermatTrace p ∈
        Set.Icc (-(Real.sqrt 3) / 2) (-(1 : Real) / 2))

/-- All rational primes at most `X`, for the standard counting form of PNT. -/
def rationalPrimesUpTo (X : Nat) : Finset Nat :=
  (Finset.range (X + 1)).filter Nat.Prime

/--
The same fixed negative Frobenius-trace sector, now counted among all primes
at most `X` as in the standard statement of the CM Sato--Tate theorem.
-/
def negativeCMTraceSectorPrimesUpTo (X : Nat) : Finset Nat :=
  (Finset.range (X + 1)).filter (fun p =>
    Nat.Prime p ∧ 3 < p ∧
      normalizedFermatTrace p ∈
        Set.Icc (-(Real.sqrt 3) / 2) (-(1 : Real) / 2))

/-- The logarithmically weighted prime sum in the fixed CM sector. -/
def negativeCMTraceSectorWeight (X : Nat) : Real :=
  ∑ p ∈ negativeCMTraceSectorPrimes X, Real.log p

/--
The `I = [2*pi/3, 5*pi/6]` specialization of the classical fixed-sector
Hecke--Deuring theorem, recorded as equation (2) by Panidapu--Thorner.
The sector has angular mass `1/12`.
-/
def PublishedFermatCMSector : Prop :=
  Tendsto
    (fun X : Nat => negativeCMTraceSectorWeight X / (X : Real))
    atTop (nhds ((1 : Real) / 12))

/--
The familiar counting statement of CM Sato--Tate, specialized to the Fermat
cubic and the angle interval `[2*pi/3, 5*pi/6]`.  The interval does not contain
the inert atom at `pi/2`, and its CM Sato--Tate mass is `1/12`.

This is the direct specialization of the theorem displayed in the
introduction of Chen--Park--Swaminathan, where the CM case is credited to
Hecke.  Unlike `PublishedFermatCMSector`, it has no logarithmic weights and
simply says that the proportion among rational primes tends to `1/12`.

Source: https://arxiv.org/abs/1506.09170
-/
def FermatCMSatoTate : Prop :=
  Tendsto
    (fun X : Nat =>
      ((negativeCMTraceSectorPrimesUpTo X).card : Real) /
        ((rationalPrimesUpTo X).card : Real))
    atTop (nhds ((1 : Real) / 12))

/--
The ordinary prime number theorem in its standard `pi(X) log(X) / X -> 1`
form.  It is separated from CM Sato--Tate so the two familiar inputs are
visible independently.
-/
def OrdinaryPrimeNumberTheorem : Prop :=
  Tendsto
    (fun X : Nat =>
      ((rationalPrimesUpTo X).card : Real) * Real.log X / (X : Real))
    atTop (nhds (1 : Real))

/--
The much weaker consequence actually consumed by the block construction.

For all sufficiently large `T`, the dyadic interval `(T^8, 2*T^8]`
contains at least `T^6` primes in the fixed negative trace sector.  Unlike the
published weighted limit, this statement contains no asymptotic constant,
real division, logarithmic weight, or `Tendsto` target value.  The implication
`PublishedFermatCMSector -> FermatSectorAbundance` is proved in
`SourceToCM`; it is not an additional external input.
-/
def FermatSectorAbundance : Prop :=
  ∀ᶠ T : Nat in atTop,
    T ^ 6 ≤ (negativeCMTraceSectorPrimes (T ^ 8)).card

/--
The elementary local point-count identity connecting the cited CM curve with
the literal Fermat-cubic local count.  A nonzero trace excludes inert primes.
-/
def FermatCubicLocalTraceFormula : Prop :=
  ∀ p : Nat, Nat.Prime p → 3 < p → fermatFrobeniusTrace p ≠ 0 →
    ((localCubeSolutions p).card : Int) =
      ((p : Int) - 1) * ((p : Int) - 8 - fermatFrobeniusTrace p)

/-- Package for the alternative logarithmically weighted source route. -/
structure FermatCMSource where
  sector : PublishedFermatCMSector

/-- The real prime-counting function `pi(y; q, r)` used in the PNT statement. -/
def progressionCount (y : Real) (q r : Nat) : Nat :=
  (primesInProgressionUpTo y q r).card

/--
Ford's displayed Gallagher PNT away from the possible exceptional conductor
`d_Q`.  Ford proves `d_Q ≫_A (log Q)^A`; after enlarging the fixed threshold,
the only consequence needed here is `2 < d_Q`.  (Ford also records
`16 ∤ d_Q`, not `16 ∣ d_Q`.)

The constants `b` and `C` make the uniform `O((log Q)^(-b))` literal.
`Real.rpow Q (log (log Q))` is `Q^(log log Q)`.
-/
structure GallagherFordConductorPNT where
  exponent : Real
  errorConstant : Real
  exponent_pos : 0 < exponent
  errorConstant_pos : 0 < errorConstant
  threshold : Nat
  threshold_ge_two : 2 ≤ threshold
  estimate : ∀ Q : Nat, threshold ≤ Q →
    ∃ exceptionalConductor : Nat, 2 < exceptionalConductor ∧
      ∀ q r : Nat, 1 < q → q ≤ 8 * Q → r.Coprime q →
        ¬exceptionalConductor ∣ q →
        ∀ y : Real,
          Real.rpow (Q : Real) (Real.log (Real.log Q)) < y →
          |(progressionCount y q r : Real) -
              y / ((q.totient : Real) * Real.log y)| ≤
            errorConstant * (Real.log Q) ^ (-exponent) *
              (y / ((q.totient : Real) * Real.log y))

/--
Internal prime-divisor form derived from `GallagherFordConductorPNT`.

Requiring one chosen prime divisor not to divide `q` is stronger than merely
requiring the full exceptional conductor not to divide `q`, so Ford's estimate
applies.  This structure is convenient for selecting a coprime CM block but is
not the public source statement.
-/
structure GallagherFordPNT where
  exponent : Real
  errorConstant : Real
  exponent_pos : 0 < exponent
  errorConstant_pos : 0 < errorConstant
  threshold : Nat
  threshold_ge_two : 2 ≤ threshold
  estimate : ∀ Q : Nat, threshold ≤ Q →
    ∃ exceptionalPrime : Nat, Nat.Prime exceptionalPrime ∧
      ∀ q r : Nat, 1 < q → q ≤ 8 * Q → r.Coprime q →
        ¬exceptionalPrime ∣ q →
        ∀ y : Real,
          Real.rpow (Q : Real) (Real.log (Real.log Q)) < y →
          |(progressionCount y q r : Real) -
              y / ((q.totient : Real) * Real.log y)| ≤
            errorConstant * (Real.log Q) ^ (-exponent) *
              (y / ((q.totient : Real) * Real.log y))

#check @negativeCMTraceSectorWeight
#check @PublishedFermatCMSector
#check @FermatCMSatoTate
#check @OrdinaryPrimeNumberTheorem
#check @FermatSectorAbundance
#check @FermatCubicLocalTraceFormula
#check @FermatCMSource
#check @GallagherFordConductorPNT
#check @GallagherFordPNT

end

end K3Lean.SourceTheorems
