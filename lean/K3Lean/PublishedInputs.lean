import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Chebyshev

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Published external theorems used in the proposed proof of Erdos #979, k = 3

This file states the two published theorems in their standard analytic form.
It deliberately does not mention block certificates, local cube-solution
amplification, or the target conclusion of Problem #979.

## External theorem 1: CM Sato--Tate (Hecke--Deuring)

Source: Theorem 1.1 in

https://www.math.clemson.edu/~kevja/PAPERS/FrobShortIntervalCM-JNT-2017.pdf

For a CM elliptic curve `E / Q`, write
`a_p = p + 1 - #E(F_p)`.  Half of the primes asymptotically have `a_p = 0`,
and the nonzero normalized traces `a_p / (2 * sqrt p)` have the arcsine
distribution on `[-1, 1]`, with total mass `1 / 2`.

Below this is specialized, without changing its analytic content, to the CM
curve `E : y^2 = x^3 - 432`, a Weierstrass model of the Fermat cubic.  Its
point count is defined literally by counting affine solutions modulo `p` and
adding the point at infinity.

## External theorem 2: Brun--Titchmarsh

Source: the proposition labelled "Brun--Titchmarsh Theorem" in Section 1 of

https://arxiv.org/abs/1201.1777

For positive coprime integers `a, q` and `x > q`,

`pi(x; q, a) <= 2x / (phi(q) * log(x / q))`.

The conversion of these published statements into the finite block
corollaries required by the #979 argument is intentionally not assumed here.
-/

namespace K3Lean.PublishedInputs

open Filter Set
open scoped BigOperators Topology Interval

noncomputable section

def cmSatoTateSourceURL : String :=
  "https://www.math.clemson.edu/~kevja/PAPERS/FrobShortIntervalCM-JNT-2017.pdf"

def brunTitchmarshSourceURL : String :=
  "https://arxiv.org/abs/1201.1777"

/-- The literal finite set of rational primes at most the real number `x`. -/
def primesUpTo (x : Real) : Finset Nat :=
  (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime

/-- The prime-counting function `pi(x)`. -/
def primeCounting (x : Real) : Nat :=
  (primesUpTo x).card

/--
Affine points modulo `p` on `E : y^2 = x^3 - 432`, represented by residues
`0, ..., p - 1`.  The congruence is written as `y^2 + 432 = x^3 (mod p)`.
-/
def cmCurveAffinePoints (p : Nat) : Finset (Nat × Nat) :=
  ((Finset.range p) ×ˢ (Finset.range p)).filter
    (fun xy => (xy.2 ^ 2 + 432) % p = xy.1 ^ 3 % p)

/-- The affine points plus the unique point at infinity. -/
def cmCurvePointCount (p : Nat) : Nat :=
  (cmCurveAffinePoints p).card + 1

/-- The Frobenius trace `a_p = p + 1 - #E(F_p)`. -/
def cmFrobeniusTrace (p : Nat) : Int :=
  (p : Int) + 1 - (cmCurvePointCount p : Int)

/-- The normalized trace `a_p / (2 * sqrt p)`. -/
def normalizedCMTrace (p : Nat) : Real :=
  (cmFrobeniusTrace p : Real) / (2 * Real.sqrt p)

/-!
The Fermat cubic is counted directly in two standard projective charts.  A
projective point has either first coordinate nonzero, in which case it has a
unique representative `[1 : u : v]`, or first coordinate zero and second
coordinate nonzero, in which case it has a unique representative `[0 : 1 : v]`.
The impossible point `[0 : 0 : 1]` contributes no third chart.
-/

/-- Points `[1 : u : v]` on `X^3 + Y^3 + Z^3 = 0` over `ZMod p`. -/
abbrev fermatAffineChartPoint (p : Nat) :=
  {uv : ZMod p × ZMod p // 1 + uv.1 ^ 3 + uv.2 ^ 3 = 0}

/-- Points `[0 : 1 : v]` on `X^3 + Y^3 + Z^3 = 0` over `ZMod p`. -/
abbrev fermatInfinityChartPoint (p : Nat) :=
  {v : ZMod p // 1 + v ^ 3 = 0}

/-- The literal projective point count of the Fermat cubic over `ZMod p`. -/
def fermatProjectivePointCount (p : Nat) : Nat :=
  Nat.card (fermatAffineChartPoint p) +
    Nat.card (fermatInfinityChartPoint p)

/-- The Frobenius trace of the projective Fermat cubic. -/
def fermatFrobeniusTrace (p : Nat) : Int :=
  (p : Int) + 1 - (fermatProjectivePointCount p : Int)

/-- The normalized Frobenius trace of the projective Fermat cubic. -/
def normalizedFermatTrace (p : Nat) : Real :=
  (fermatFrobeniusTrace p : Real) / (2 * Real.sqrt p)

/-- Good-reduction primes with zero Frobenius trace, up to `x`. -/
def zeroCMTracePrimesUpTo (x : Real) : Finset Nat :=
  (primesUpTo x).filter (fun p => 3 < p ∧ cmFrobeniusTrace p = 0)

/--
Good-reduction primes up to `x` whose nonzero normalized trace lies in
the closed interval `[alpha, beta]`.
-/
def nonzeroCMTracePrimesInIntervalUpTo
    (alpha beta x : Real) : Finset Nat :=
  (primesUpTo x).filter (fun p =>
    3 < p ∧ cmFrobeniusTrace p ≠ 0 ∧
      normalizedCMTrace p ∈ Set.Icc alpha beta)

/--
The Hecke--Deuring CM Sato--Tate theorem, specialized to
`E : y^2 = x^3 - 432`, in the exact limiting-distribution form of the source.
-/
def PublishedCMSatoTate : Prop :=
  Tendsto
      (fun x : Real =>
        (zeroCMTracePrimesUpTo x).card / (primeCounting x : Real))
      atTop (nhds ((1 : Real) / 2)) ∧
    ∀ alpha beta : Real,
      -1 ≤ alpha → alpha ≤ beta → beta ≤ 1 →
      Tendsto
        (fun x : Real =>
          (nonzeroCMTracePrimesInIntervalUpTo alpha beta x).card /
            (primeCounting x : Real))
        atTop
        (nhds
          ((1 / (2 * Real.pi)) *
            ∫ t in alpha..beta, 1 / Real.sqrt (1 - t ^ 2)))

/-- The standard counting function `pi(x; q, a)` for real `x`. -/
def primesInProgressionUpTo (x : Real) (q a : Nat) : Finset Nat :=
  (primesUpTo x).filter (fun p => p % q = a % q)

/--
The Montgomery--Vaughan form of the Brun--Titchmarsh theorem exactly as stated
in the cited source.
-/
def PublishedBrunTitchmarsh : Prop :=
  ∀ (x : Real) (q a : Nat),
    0 < q → 0 < a → (q : Real) < x → a.Coprime q →
    ((primesInProgressionUpTo x q a).card : Real) ≤
      (2 * x) /
        ((q.totient : Real) * Real.log (x / (q : Real)))

#check @cmFrobeniusTrace
#check @PublishedCMSatoTate
#check @PublishedBrunTitchmarsh

end

end K3Lean.PublishedInputs
