import K3Lean.FiniteLifting
import Mathlib.Algebra.Order.BigOperators.Group.Finset

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Two standard analytic corollaries used for Erdos #979, k = 3

The final Lean theorem takes exactly the two propositions in this file as
arguments.  Neither proposition mentions `f₃`, a represented integer, a
pigeonhole principle, or the conclusion of Problem #979.

They are deliberately called **corollaries**, not verbatim published theorem
statements.  Their sources state the usual real-asymptotic theorems; the forms
below are weaker, discrete consequences with all constants absorbed into a
single base-two logarithmic loss.

## CM source

Hecke's equidistribution theorem for CM elliptic curves, in Theorem 1.1 of

https://www.math.clemson.edu/~kevja/PAPERS/FrobShortIntervalCM-JNT-2017.pdf

For the Fermat cubic, the elementary local identity

`R_p = (p - 1) * (p - 8 - a_p)` for `p = 1 (mod 3)`

turns a fixed negative-trace interval into local factors
`p * R_p / (p - 1)^3 >= 1 + c / sqrt(p)`.  Positive density of such primes,
partitioned into two blocks, makes each block product dominate every fixed
power of the logarithm of the combined modulus.  `CMProductGrowthCorollary`
is the exact coarse integer consequence used below.

## PNT-in-AP source

P. X. Gallagher, *A large sieve density estimate near sigma = 1*,
Invent. Math. 11 (1970), Theorem 7:

https://doi.org/10.1007/BF01403187

The Landau--Page exceptional-modulus consequence is written explicitly in
the proof of Lemma 2.8 of Kevin Ford, *The number of solutions of phi(x)=m*:

https://www.kurims.kyoto-u.ac.jp/EMIS/journals/Annals/150_1/ford.pdf

For `q <= 8Q` not divisible by the possible exceptional conductor and
`x > Q^(log log Q)`, Ford records

`pi(x; q, a) = (1 + O((log Q)^(-b))) * x / (phi(q) * log x)`.

Choosing one prime divisor of the exceptional conductor, enlarging `Q`, and
absorbing constants and `log x` into `(Nat.log Q + 1)^2` gives the discrete
`ExceptionalPNTCorollary` below.
-/

namespace K3Lean.StandardCorollaries

open K3Lean.CMProof
open K3Lean.FiniteLifting
open scoped BigOperators

def cmSatoTateSourceURL : String :=
  "https://www.math.clemson.edu/~kevja/PAPERS/FrobShortIntervalCM-JNT-2017.pdf"

def gallagherSourceURL : String :=
  "https://doi.org/10.1007/BF01403187"

def fordExceptionalModulusSourceURL : String :=
  "https://www.kurims.kyoto-u.ac.jp/EMIS/journals/Annals/150_1/ford.pdf"

/--
A coarse upper bound for the logarithmic loss in the PNT-in-AP cutoff.
The fourth power leaves enough room both for Ford's cutoff and for the larger
classical cutoff obtained from Page's theorem and the traditional zero-free
region.  The CM amplification is exponential, so this fixed polynomial
enlargement does not change the final argument.
-/
def logLoss (Q : Nat) : Nat := 4 * (Nat.log 2 Q + 1) ^ 4

/--
Two or more pairwise-coprime moduli whose Fermat-cubic local density has been
amplified beyond the sixth power of the combined logarithm.

The numerical constant `24` is only bookkeeping: `3` for the value range,
`6` for ordered-to-unordered triples, and a harmless factor for `+1`.
-/
structure CMGrowthFamily (B minimumProduct : Nat) where
  blocks : Finset Nat
  enough_blocks : 2 ≤ blocks.card
  modulus_gt_one : ∀ a ∈ blocks, 1 < a
  pairwise_coprime :
    ∀ a ∈ blocks, ∀ b ∈ blocks, a ≠ b → a.Coprime b
  product_large : minimumProduct ≤ blocks.prod id
  local_density : ∀ a ∈ blocks,
    24 * B * (logLoss (blocks.prod id)) ^ 3 * a.totient ^ 3 ≤
      a * (localCubeSolutions a).card

/--
The finite Euler-product consequence of CM Sato--Tate used by the proof.
It concerns only local solution densities and pairwise-coprime moduli.
-/
def CMProductGrowthCorollary : Prop :=
  ∀ B minimumProduct : Nat, Nonempty (CMGrowthFamily B minimumProduct)

/--
The finite lower-bound consequence of Gallagher's exceptional-modulus PNT.

For every sufficiently large master modulus `Q`, at most one prime is marked
exceptional.  Every smaller modulus not divisible by that prime has a common
cutoff `X` and at least `g` primes in every reduced class, where
`X <= logLoss(Q) * phi(q) * g`.
-/
def ExceptionalPNTCorollary : Prop :=
  ∃ Q₀ : Nat, 2 ≤ Q₀ ∧
    ∀ Q : Nat, Q₀ ≤ Q →
      ∃ exceptionalPrime X : Nat,
        Nat.Prime exceptionalPrime ∧ Q ≤ X ∧
          ∀ q : Nat, 1 < q → q ≤ Q → ¬exceptionalPrime ∣ q →
            ∃ g : Nat,
              X ≤ logLoss Q * q.totient * g ∧
                UniformPrimeClasses q X g

#check @CMGrowthFamily
#check @CMProductGrowthCorollary
#check @ExceptionalPNTCorollary

end K3Lean.StandardCorollaries
