import K3Lean.HeckeDeuringReduction

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Opening Sutherland's Hecke equidistribution lemma

Sutherland's proof of Lemma 2.15 applies the compact-group/L-function
criterion of Theorem 2.12 to every nontrivial character of `U(1)`.  For a
conjugate pair of prime ideals above a split rational prime, the two character
values add to `2 * cos(m * theta_p)`.  Thus the analytic input can be exposed
as cancellation of every nonconstant cosine moment.

This file separates the two ingredients:

* `CosineWeylCriterion` is the standard Weyl/Serre equidistribution criterion
  on `[0, pi]`.
* `HeckePrimeCharacterCancellation` is the prime-number-theorem consequence
  of Hecke's holomorphy and nonvanishing theorem for every nontrivial power of
  the unitarized CM character.

Their combination proves `HeckeSplitAngleEquidistribution`; that conclusion is
not an assumption in the final theorem of this route.

References:

* A. Sutherland, *Sato--Tate distributions*, Theorem 2.12 and Lemma 2.15,
  https://swc-math.github.io/aws/2016/2016SutherlandNotes.pdf#page=17
* E. Hecke, *Eine neue Art von Zetafunktionen ... Zweite Mitteilung*,
  Math. Z. 6 (1920), 11--51,
  https://eudml.org/doc/168357
-/

namespace K3Lean.HeckeCharacterCriterion

open Filter Set
open K3Lean.HeckeDeuringReduction
open K3Lean.PublishedInputs
open scoped BigOperators Topology

noncomputable section

/-- The normalized `m`th cosine moment of a finite family of angles. -/
def cosineMoment
    (A : Nat -> Finset Nat) (theta : Nat -> Real) (m X : Nat) : Real :=
  (∑ p ∈ A X, Real.cos ((m : Real) * theta p)) / ((A X).card : Real)

/-- The normalized frequency of angles in a closed interval. -/
def angleIntervalFrequency
    (A : Nat -> Finset Nat) (theta : Nat -> Real)
    (alpha beta : Real) (X : Nat) : Real :=
  (((A X).filter (fun p => theta p ∈ Set.Icc alpha beta)).card : Real) /
    ((A X).card : Real)

/--
The cosine form of Weyl's criterion on `[0, pi]`.  It is stated for an
arbitrary net of finite index sets, not for primes or elliptic curves.
-/
def CosineWeylCriterion : Prop :=
  forall (A : Nat -> Finset Nat) (theta : Nat -> Real),
    (∀ᶠ X : Nat in atTop, (A X).Nonempty) ->
    (forall X p, p ∈ A X -> theta p ∈ Set.Icc 0 Real.pi) ->
    (forall m : Nat, 0 < m ->
      Tendsto (fun X : Nat => cosineMoment A theta m X)
        atTop (nhds 0)) ->
    forall alpha beta : Real,
      0 <= alpha -> alpha <= beta -> beta <= Real.pi ->
      Tendsto
        (fun X : Nat => angleIntervalFrequency A theta alpha beta X)
        atTop (nhds ((beta - alpha) / Real.pi))

/--
Prime-character cancellation supplied by Hecke's theorem for the powers of
the unitarized CM character, after pairing conjugate prime ideals.
-/
def HeckePrimeCharacterCancellation (theta : Nat -> Real) : Prop :=
  forall m : Nat, 0 < m ->
    Tendsto
      (fun X : Nat => cosineMoment splitPrimesUpTo theta m X)
      atTop (nhds 0)

/-- Every sufficiently large split-prime set contains the prime `7`. -/
theorem splitPrimesUpTo_eventually_nonempty :
    ∀ᶠ X : Nat in atTop, (splitPrimesUpTo X).Nonempty := by
  filter_upwards [eventually_ge_atTop (7 : Nat)] with X hX
  refine ⟨7, ?_⟩
  simp only [splitPrimesUpTo, Finset.mem_filter, Finset.mem_range]
  norm_num
  omega

/--
This is Sutherland's Lemma 2.15 in the concrete quotient-angle form needed
for the Fermat cubic: Hecke cancellation plus Weyl gives interval counts.
-/
theorem heckeSplitAngleEquidistribution_of_character_cancellation
    (theta : Nat -> Real)
    (hRange : forall p : Nat, Nat.Prime p -> p % 3 = 1 ->
      theta p ∈ Set.Icc 0 Real.pi)
    (hWeyl : CosineWeylCriterion)
    (hHecke : HeckePrimeCharacterCancellation theta) :
    HeckeSplitAngleEquidistribution theta := by
  intro alpha beta hAlpha hAlphaBeta hBeta
  have hRange' : forall X p, p ∈ splitPrimesUpTo X ->
      theta p ∈ Set.Icc 0 Real.pi := by
    intro X p hp
    have hpParts := Finset.mem_filter.mp hp
    exact hRange p hpParts.2.1 hpParts.2.2
  have h := hWeyl splitPrimesUpTo theta
    splitPrimesUpTo_eventually_nonempty hRange' hHecke
    alpha beta hAlpha hAlphaBeta hBeta
  simpa [angleIntervalFrequency, splitAnglePrimesUpTo, splitPrimesUpTo,
    Finset.filter_filter, and_assoc] using h

/--
The fixed Fermat-cubic CM sector follows from inputs strictly below
CM Sato--Tate: Deuring, Hecke character cancellation, Weyl, and the two PNTs.
-/
theorem fermatCMSatoTate_of_hecke_character_theorem
    (theta : Nat -> Real)
    (hDeuring : forall p : Nat, Nat.Prime p -> p % 3 = 1 ->
      theta p ∈ Set.Icc 0 Real.pi /\
        (fermatFrobeniusTrace p : Real) =
          2 * Real.sqrt p * Real.cos (theta p))
    (hWeyl : CosineWeylCriterion)
    (hHecke : HeckePrimeCharacterCancellation theta)
    (hAP : PrimeNumberTheoremModThreeOne)
    (hPNT : K3Lean.SourceTheorems.OrdinaryPrimeNumberTheorem) :
    K3Lean.SourceTheorems.FermatCMSatoTate := by
  have hAngles : HeckeSplitAngleEquidistribution theta :=
    heckeSplitAngleEquidistribution_of_character_cancellation
      theta (fun p hp hsplit => (hDeuring p hp hsplit).1) hWeyl hHecke
  exact fermatCMSatoTate_of_hecke_deuring
    theta hDeuring hAngles hAP hPNT

#check @CosineWeylCriterion
#check @HeckePrimeCharacterCancellation
#check @heckeSplitAngleEquidistribution_of_character_cancellation
#check @fermatCMSatoTate_of_hecke_character_theorem
#print axioms fermatCMSatoTate_of_hecke_character_theorem

end

end K3Lean.HeckeCharacterCriterion
