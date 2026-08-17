import K3Lean.LocalTraceFormula
import K3Lean.SourceSatoTate

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# From Hecke and Deuring to the CM sector used for Erdos 979

This file formalizes the classical proof route in Sections 2.3--2.4 of
Andrew Sutherland's *Sato--Tate distributions* notes:

* Hecke's theorem gives equidistribution of the unitarized values of an
  infinite-order Hecke character in `U(1)` (Lemma 2.15).
* Deuring attaches such a character to a CM elliptic curve and identifies its
  values with Frobenius traces (the input to Proposition 2.16).
* over `Q`, split primes contribute the continuous part and inert primes have
  trace zero; the prime number theorem modulo `3` gives density `1 / 2`.

Source:
https://swc-math.github.io/aws/2016/2016SutherlandNotes.pdf#page=18

The external boundary below is strictly below CM Sato--Tate.  It exposes the
Deuring trace identity, Hecke equidistribution on the split primes, and the
prime number theorem in the progression `1 mod 3` separately.  The fixed
CM-sector density `1 / 12` is proved in this file.
-/

namespace K3Lean.HeckeDeuringReduction

open Filter Set
open K3Lean.LocalTraceFormula
open K3Lean.PublishedInputs
open K3Lean.SourceSatoTate
open K3Lean.SourceTheorems
open scoped Topology

noncomputable section

/-- Rational primes at most `X` that split in `Q(sqrt(-3))`. -/
def splitPrimesUpTo (X : Nat) : Finset Nat :=
  (Finset.range (X + 1)).filter (fun p => Nat.Prime p /\ p % 3 = 1)

/--
The prime number theorem in the single reduced progression `1 mod 3`, in the
same normalization as `OrdinaryPrimeNumberTheorem`.
-/
def PrimeNumberTheoremModThreeOne : Prop :=
  Tendsto
    (fun X : Nat =>
      ((splitPrimesUpTo X).card : Real) * Real.log X / (X : Real))
    atTop (nhds ((1 : Real) / 2))

/-- The density-`1/2` consequence of PNT in the progression `1 mod 3`. -/
def SplitPrimeDensity : Prop :=
  Tendsto
    (fun X : Nat =>
      ((splitPrimesUpTo X).card : Real) /
        ((rationalPrimesUpTo X).card : Real))
    atTop (nhds ((1 : Real) / 2))

/--
Extend the Frobenius angle supplied by Deuring at split primes by putting all
inert primes at the CM atom `pi / 2`.
-/
def extendDeuringAngle (theta : Nat -> Real) (p : Nat) : Real :=
  if p % 3 = 1 then theta p else Real.pi / 2

/-- Primes in an angle interval, excluding the bad prime `3`. -/
def splitAnglePrimesUpTo
    (theta : Nat -> Real) (alpha beta : Real) (X : Nat) : Finset Nat :=
  (Finset.range (X + 1)).filter (fun p =>
    Nat.Prime p /\ p % 3 = 1 /\ theta p ∈ Set.Icc alpha beta)

/--
The interval-counting form of Hecke's equidistribution theorem after passing
from the two conjugate prime ideals above each split rational prime to the
angle in `[0, pi]`.  This is the `U(1)` conclusion of Sutherland, Lemma 2.15,
pushed forward by conjugation.
-/
def HeckeSplitAngleEquidistribution (theta : Nat -> Real) : Prop :=
  forall alpha beta : Real,
    0 <= alpha -> alpha <= beta -> beta <= Real.pi ->
    Tendsto
      (fun X : Nat =>
        ((splitAnglePrimesUpTo theta alpha beta X).card : Real) /
          ((splitPrimesUpTo X).card : Real))
      atTop (nhds ((beta - alpha) / Real.pi))

/--
Finite-field algebra supplies the inert part of the CM proof internally:
at every prime `p = 2 mod 3`, the Fermat-cubic trace is zero.
-/
theorem fermat_angle_data_of_deuring
    (theta : Nat -> Real)
    (hDeuring : forall p : Nat, Nat.Prime p -> p % 3 = 1 ->
      theta p ∈ Set.Icc 0 Real.pi /\
        (fermatFrobeniusTrace p : Real) =
          2 * Real.sqrt p * Real.cos (theta p)) :
    forall p : Nat, Nat.Prime p -> p ≠ 3 ->
      extendDeuringAngle theta p ∈ Set.Icc 0 Real.pi /\
        (fermatFrobeniusTrace p : Real) =
          2 * Real.sqrt p * Real.cos (extendDeuringAngle theta p) := by
  intro p hp hp3
  have hmod_lt : p % 3 < 3 := Nat.mod_lt p (by norm_num)
  have hmod_ne_zero : p % 3 ≠ 0 := by
    intro hzero
    have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hzero
    have heq : 3 = p :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdvd
    exact hp3 heq.symm
  have hmod : p % 3 = 1 \/ p % 3 = 2 := by omega
  rcases hmod with hsplit | hinert
  · simpa [extendDeuringAngle, hsplit] using hDeuring p hp hsplit
  · have hnotSplit : p % 3 ≠ 1 := by omega
    have htrace :=
      fermatFrobeniusTrace_eq_zero_of_mod_three_eq_two p hp hinert
    constructor
    · simp only [extendDeuringAngle, if_neg hnotSplit, Set.mem_Icc]
      constructor <;> nlinarith [Real.pi_pos]
    · simp [extendDeuringAngle, hnotSplit, htrace, Real.cos_pi_div_two]

/-- The ordinary PNT and PNT in `1 mod 3` imply split-prime density `1/2`. -/
theorem splitPrimeDensity_of_pnt
    (hAP : PrimeNumberTheoremModThreeOne)
    (hPNT : OrdinaryPrimeNumberTheorem) : SplitPrimeDensity := by
  have hquot :
      Tendsto
        (fun X : Nat =>
          (((splitPrimesUpTo X).card : Real) * Real.log X / (X : Real)) /
            (((rationalPrimesUpTo X).card : Real) * Real.log X / (X : Real)))
        atTop (nhds ((((1 : Real) / 2) / 1))) :=
    hAP.div hPNT (by norm_num)
  have heq :
      (fun X : Nat =>
        (((splitPrimesUpTo X).card : Real) * Real.log X / (X : Real)) /
          (((rationalPrimesUpTo X).card : Real) * Real.log X / (X : Real))) =ᶠ[atTop]
      (fun X : Nat =>
        ((splitPrimesUpTo X).card : Real) /
          ((rationalPrimesUpTo X).card : Real)) := by
    filter_upwards [eventually_ge_atTop (7 : Nat)] with X hX
    have hXpos : (0 : Real) < X := by exact_mod_cast (by omega : 0 < X)
    have hXne : (X : Real) ≠ 0 := hXpos.ne'
    have hXone : (X : Real) ≠ 1 := by exact_mod_cast (by omega : X ≠ 1)
    have hlog : Real.log (X : Real) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one hXpos hXone
    have hseven : 7 ∈ splitPrimesUpTo X := by
      simp only [splitPrimesUpTo, Finset.mem_filter, Finset.mem_range]
      norm_num
      omega
    have htwo : 2 ∈ rationalPrimesUpTo X := by
      simp only [rationalPrimesUpTo, Finset.mem_filter, Finset.mem_range]
      norm_num
      omega
    have hsplitNat : (splitPrimesUpTo X).card ≠ 0 :=
      (Finset.card_pos.mpr ⟨7, hseven⟩).ne'
    have hprimeNat : (rationalPrimesUpTo X).card ≠ 0 :=
      (Finset.card_pos.mpr ⟨2, htwo⟩).ne'
    have hsplitReal : ((splitPrimesUpTo X).card : Real) ≠ 0 := by
      exact_mod_cast hsplitNat
    have hprimeReal : ((rationalPrimesUpTo X).card : Real) ≠ 0 := by
      exact_mod_cast hprimeNat
    field_simp [hXne, hlog, hsplitReal, hprimeReal]
  change
    Tendsto
      (fun X : Nat =>
        ((splitPrimesUpTo X).card : Real) /
          ((rationalPrimesUpTo X).card : Real))
      atTop (nhds ((1 : Real) / 2))
  convert hquot.congr' heq using 1 <;> norm_num

/--
The fixed interval `[2*pi/3, 5*pi/6]` has uniform split-prime mass `1/6`.
-/
theorem hecke_fixed_sector
    (theta : Nat -> Real)
    (hHecke : HeckeSplitAngleEquidistribution theta) :
    Tendsto
      (fun X : Nat =>
        ((splitAnglePrimesUpTo theta
            (2 * Real.pi / 3) (5 * Real.pi / 6) X).card : Real) /
          ((splitPrimesUpTo X).card : Real))
      atTop (nhds ((1 : Real) / 6)) := by
  have h := hHecke
    (2 * Real.pi / 3) (5 * Real.pi / 6)
    (by positivity)
    (by nlinarith [Real.pi_pos])
    (by nlinarith [Real.pi_pos])
  convert h using 1
  field_simp [ne_of_gt Real.pi_pos]
  ring_nf

/--
At the fixed interval used by the block proof, the split-angle count is
literally the negative Frobenius-trace count.
-/
theorem split_angle_fixed_sector_card_eq_trace_sector_card
    (theta : Nat -> Real)
    (hDeuring : forall p : Nat, Nat.Prime p -> p % 3 = 1 ->
      theta p ∈ Set.Icc 0 Real.pi /\
        (fermatFrobeniusTrace p : Real) =
          2 * Real.sqrt p * Real.cos (theta p))
    (X : Nat) :
    (splitAnglePrimesUpTo theta
        (2 * Real.pi / 3) (5 * Real.pi / 6) X).card =
      (negativeCMTraceSectorPrimesUpTo X).card := by
  have hAngle := fermat_angle_data_of_deuring theta hDeuring
  have hsource := angle_sector_nat_card_eq_trace_sector_card hAngle X
  rw [← hsource]
  apply congrArg Finset.card
  ext p
  simp only [splitAnglePrimesUpTo, primesUpTo, Nat.floor_natCast,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hpX, hp, hsplit, htheta⟩
    have hp3 : p ≠ 3 := by
      intro hpEq
      subst p
      norm_num at hsplit
    exact ⟨⟨hpX, hp⟩, hp3,
      by simpa [extendDeuringAngle, hsplit] using htheta⟩
  · rintro ⟨⟨hpX, hp⟩, hp3, htheta⟩
    have hmod_lt : p % 3 < 3 := Nat.mod_lt p (by norm_num)
    have hmod_ne_zero : p % 3 ≠ 0 := by
      intro hzero
      have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hzero
      have heq : 3 = p :=
        (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdvd
      exact hp3 heq.symm
    have hsplit : p % 3 = 1 := by
      by_contra hnot
      have hinert : p % 3 = 2 := by omega
      have hpi : extendDeuringAngle theta p = Real.pi / 2 := by
        simp [extendDeuringAngle, hnot]
      rw [hpi] at htheta
      have hlow := htheta.1
      nlinarith [Real.pi_pos]
    exact ⟨hpX, hp, hsplit,
      by simpa [extendDeuringAngle, hsplit] using htheta⟩

/--
Sutherland's Hecke--Deuring proof, specialized only after the source inputs
have been stated: split-angle mass `1/6` times split-prime density `1/2`
gives the CM mass `1/12` among all rational primes.
-/
theorem fermatCMSatoTate_of_hecke_deuring_and_split_density
    (theta : Nat -> Real)
    (hDeuring : forall p : Nat, Nat.Prime p -> p % 3 = 1 ->
      theta p ∈ Set.Icc 0 Real.pi /\
        (fermatFrobeniusTrace p : Real) =
          2 * Real.sqrt p * Real.cos (theta p))
    (hHecke : HeckeSplitAngleEquidistribution theta)
    (hSplit : SplitPrimeDensity) : FermatCMSatoTate := by
  have hsector := hecke_fixed_sector theta hHecke
  have hproduct := hsector.mul hSplit
  have hpositive :
      ∀ᶠ X : Nat in atTop, (0 : Real) <
        ((splitPrimesUpTo X).card : Real) /
          ((rationalPrimesUpTo X).card : Real) := by
    have hmem : Set.Ioi ((1 : Real) / 4) ∈ nhds ((1 : Real) / 2) :=
      Ioi_mem_nhds (by norm_num)
    filter_upwards [hSplit.eventually hmem] with X hX
    exact lt_trans (by norm_num) hX
  have heq :
      (fun X : Nat =>
        ((splitAnglePrimesUpTo theta
            (2 * Real.pi / 3) (5 * Real.pi / 6) X).card : Real) /
            ((splitPrimesUpTo X).card : Real) *
          (((splitPrimesUpTo X).card : Real) /
            ((rationalPrimesUpTo X).card : Real))) =ᶠ[atTop]
      (fun X : Nat =>
        ((negativeCMTraceSectorPrimesUpTo X).card : Real) /
          ((rationalPrimesUpTo X).card : Real)) := by
    filter_upwards [hpositive] with X hpos
    have hsplitReal : ((splitPrimesUpTo X).card : Real) ≠ 0 := by
      intro hzero
      rw [hzero, zero_div] at hpos
      exact (lt_irrefl 0) hpos
    have hcard :=
      split_angle_fixed_sector_card_eq_trace_sector_card theta hDeuring X
    rw [hcard]
    field_simp [hsplitReal]
  rw [FermatCMSatoTate]
  convert hproduct.congr' heq using 1 <;> norm_num

/--
CM Sato--Tate is no longer an assumption: it is derived from Hecke's split
angle theorem, Deuring's trace identity, PNT in `1 mod 3`, and ordinary PNT.
-/
theorem fermatCMSatoTate_of_hecke_deuring
    (theta : Nat -> Real)
    (hDeuring : forall p : Nat, Nat.Prime p -> p % 3 = 1 ->
      theta p ∈ Set.Icc 0 Real.pi /\
        (fermatFrobeniusTrace p : Real) =
          2 * Real.sqrt p * Real.cos (theta p))
    (hHecke : HeckeSplitAngleEquidistribution theta)
    (hAP : PrimeNumberTheoremModThreeOne)
    (hPNT : OrdinaryPrimeNumberTheorem) : FermatCMSatoTate := by
  exact fermatCMSatoTate_of_hecke_deuring_and_split_density
    theta hDeuring hHecke (splitPrimeDensity_of_pnt hAP hPNT)

#check @PrimeNumberTheoremModThreeOne
#check @HeckeSplitAngleEquidistribution
#check @fermat_angle_data_of_deuring
#check @splitPrimeDensity_of_pnt
#check @fermatCMSatoTate_of_hecke_deuring
#print axioms fermatCMSatoTate_of_hecke_deuring

end

end K3Lean.HeckeDeuringReduction
