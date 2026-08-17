import K3Lean.HeckeCharacterCriterion

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Full CM Sato--Tate from the Hecke--Deuring source chain

The fixed negative sector is enough for Erdos 979, but the classical proof
gives the full CM measure.  This file completes that argument:

* split primes have uniformly distributed angles in `[0, pi]`;
* inert primes have Frobenius trace zero and angle `pi / 2`;
* the two residue classes `1, 2 mod 3` each have rational-prime density `1/2`.

The resulting measure of `[alpha, beta]` is

`(1/2) * 1_{pi/2 in [alpha,beta]} + (beta-alpha)/(2*pi)`.

This is exactly the CM branch stated in Sutherland, Section 2.4, and in the
displayed Sato--Tate theorem used by the project.
-/

namespace K3Lean.FullCMSatoTateFromHecke

open Filter Set
open K3Lean.HeckeCharacterCriterion
open K3Lean.HeckeDeuringReduction
open K3Lean.LocalTraceFormula
open K3Lean.PublishedInputs
open K3Lean.SourceSatoTate
open K3Lean.SourceTheorems
open scoped Topology

noncomputable section

/-- Rational primes at most `X` that are inert in `Q(sqrt(-3))`. -/
def inertPrimesUpTo (X : Nat) : Finset Nat :=
  (Finset.range (X + 1)).filter (fun p => Nat.Prime p /\ p % 3 = 2)

/-- PNT in the second reduced residue class modulo `3`. -/
def PrimeNumberTheoremModThreeTwo : Prop :=
  Tendsto
    (fun X : Nat =>
      ((inertPrimesUpTo X).card : Real) * Real.log X / (X : Real))
    atTop (nhds ((1 : Real) / 2))

/-- Every rational prime is split, inert, or the unique ramified prime `3`. -/
private theorem rationalPrimesUpTo_eq_split_union_inert_union_three
    (X : Nat) (hX : 3 <= X) :
    rationalPrimesUpTo X =
      (splitPrimesUpTo X ∪ inertPrimesUpTo X) ∪ {3} := by
  ext p
  simp only [rationalPrimesUpTo, splitPrimesUpTo, inertPrimesUpTo,
    Finset.mem_filter, Finset.mem_range, Finset.mem_union,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hpX, hp⟩
    by_cases hp3 : p = 3
    · exact Or.inr hp3
    · have hmod_lt : p % 3 < 3 := Nat.mod_lt p (by norm_num)
      have hmod_ne_zero : p % 3 ≠ 0 := by
        intro hzero
        have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hzero
        have heq : 3 = p :=
          (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdvd
        exact hp3 heq.symm
      have hmod : p % 3 = 1 \/ p % 3 = 2 := by omega
      exact Or.inl (hmod.elim
        (fun hsplit => Or.inl ⟨hpX, hp, hsplit⟩)
        (fun hinert => Or.inr ⟨hpX, hp, hinert⟩))
  · rintro (⟨⟨hpX, hp, _⟩ | ⟨hpX, hp, _⟩⟩ | rfl)
    · exact ⟨hpX, hp⟩
    · exact ⟨hpX, hp⟩
    · exact ⟨by omega, Nat.prime_three⟩

/-- Cardinal version of the split/inert/ramified partition. -/
private theorem card_rationalPrimesUpTo_eq_split_add_inert_add_one
    (X : Nat) (hX : 3 <= X) :
    (rationalPrimesUpTo X).card =
      (splitPrimesUpTo X).card + (inertPrimesUpTo X).card + 1 := by
  have hDisjoint : Disjoint (splitPrimesUpTo X) (inertPrimesUpTo X) := by
    rw [Finset.disjoint_left]
    intro p hpSplit hpInert
    have hs := (Finset.mem_filter.mp hpSplit).2.2
    have hi := (Finset.mem_filter.mp hpInert).2.2
    omega
  have hThree : Disjoint (splitPrimesUpTo X ∪ inertPrimesUpTo X) {3} := by
    rw [Finset.disjoint_left]
    intro p hp hthree
    simp only [Finset.mem_singleton] at hthree
    subst p
    rcases Finset.mem_union.mp hp with hpSplit | hpInert
    · have hs := (Finset.mem_filter.mp hpSplit).2.2
      norm_num at hs
    · have hi := (Finset.mem_filter.mp hpInert).2.2
      norm_num at hi
  rw [rationalPrimesUpTo_eq_split_union_inert_union_three X hX,
    Finset.card_union_of_disjoint hThree,
    Finset.card_union_of_disjoint hDisjoint]
  simp

/--
For modulus `3`, the second reduced residue class needs no additional PNT:
ordinary PNT minus the `1 mod 3` class leaves the `2 mod 3` class, up to the
single ramified prime `3`.
-/
theorem pntModThreeTwo_of_one_and_ordinary
    (hAPOne : PrimeNumberTheoremModThreeOne)
    (hPNT : OrdinaryPrimeNumberTheorem) : PrimeNumberTheoremModThreeTwo := by
  have hDifference := hPNT.sub hAPOne
  have hPartition :
      (fun X : Nat =>
        ((rationalPrimesUpTo X).card : Real) * Real.log X / (X : Real) -
          ((splitPrimesUpTo X).card : Real) * Real.log X / (X : Real)) =ᶠ[atTop]
      (fun X : Nat =>
        ((inertPrimesUpTo X).card : Real) * Real.log X / (X : Real) +
          Real.log X / (X : Real)) := by
    filter_upwards [eventually_ge_atTop (3 : Nat)] with X hX
    rw [card_rationalPrimesUpTo_eq_split_add_inert_add_one X hX]
    push_cast
    ring
  have hLogReal :
      Tendsto (fun x : Real => Real.log x / x) atTop (nhds 0) := by
    simpa using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero)
  have hLog :
      Tendsto (fun X : Nat => Real.log X / (X : Real)) atTop (nhds 0) := by
    have hComp := hLogReal.comp (tendsto_natCast_atTop_atTop (R := Real))
    convert hComp using 1
    funext X
    rfl
  have h := (hDifference.congr' hPartition).sub hLog
  change
    Tendsto
      (fun X : Nat =>
        ((inertPrimesUpTo X).card : Real) * Real.log X / (X : Real))
      atTop (nhds ((1 : Real) / 2))
  convert h using 1
  · funext X
    ring
  · norm_num

/-- Density `1/2` of inert rational primes. -/
def InertPrimeDensity : Prop :=
  Tendsto
    (fun X : Nat =>
      ((inertPrimesUpTo X).card : Real) /
        ((rationalPrimesUpTo X).card : Real))
    atTop (nhds ((1 : Real) / 2))

/-- PNT in `2 mod 3`, divided by ordinary PNT. -/
theorem inertPrimeDensity_of_pnt
    (hAP : PrimeNumberTheoremModThreeTwo)
    (hPNT : OrdinaryPrimeNumberTheorem) : InertPrimeDensity := by
  have hquot :
      Tendsto
        (fun X : Nat =>
          (((inertPrimesUpTo X).card : Real) * Real.log X / (X : Real)) /
            (((rationalPrimesUpTo X).card : Real) * Real.log X / (X : Real)))
        atTop (nhds ((((1 : Real) / 2) / 1))) :=
    hAP.div hPNT (by norm_num)
  have heq :
      (fun X : Nat =>
        (((inertPrimesUpTo X).card : Real) * Real.log X / (X : Real)) /
          (((rationalPrimesUpTo X).card : Real) * Real.log X / (X : Real))) =ᶠ[atTop]
      (fun X : Nat =>
        ((inertPrimesUpTo X).card : Real) /
          ((rationalPrimesUpTo X).card : Real)) := by
    filter_upwards [eventually_ge_atTop (2 : Nat)] with X hX
    have hXpos : (0 : Real) < X := by exact_mod_cast (by omega : 0 < X)
    have hXne : (X : Real) ≠ 0 := hXpos.ne'
    have hXone : (X : Real) ≠ 1 := by exact_mod_cast (by omega : X ≠ 1)
    have hlog : Real.log (X : Real) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one hXpos hXone
    have htwoInert : 2 ∈ inertPrimesUpTo X := by
      simp only [inertPrimesUpTo, Finset.mem_filter, Finset.mem_range]
      norm_num
      omega
    have htwoPrime : 2 ∈ rationalPrimesUpTo X := by
      simp only [rationalPrimesUpTo, Finset.mem_filter, Finset.mem_range]
      norm_num
      omega
    have hinertNat : (inertPrimesUpTo X).card ≠ 0 :=
      (Finset.card_pos.mpr ⟨2, htwoInert⟩).ne'
    have hprimeNat : (rationalPrimesUpTo X).card ≠ 0 :=
      (Finset.card_pos.mpr ⟨2, htwoPrime⟩).ne'
    have hinertReal : ((inertPrimesUpTo X).card : Real) ≠ 0 := by
      exact_mod_cast hinertNat
    have hprimeReal : ((rationalPrimesUpTo X).card : Real) ≠ 0 := by
      exact_mod_cast hprimeNat
    field_simp [hXne, hlog, hinertReal, hprimeReal]
  change
    Tendsto
      (fun X : Nat =>
        ((inertPrimesUpTo X).card : Real) /
          ((rationalPrimesUpTo X).card : Real))
      atTop (nhds ((1 : Real) / 2))
  convert hquot.congr' heq using 1 <;> norm_num

/-- Good rational primes whose extended CM angle lies in an interval. -/
def goodAnglePrimesUpTo
    (theta : Nat -> Real) (alpha beta : Real) (X : Nat) : Finset Nat :=
  (Finset.range (X + 1)).filter (fun p =>
    Nat.Prime p /\ p ≠ 3 /\ theta p ∈ Set.Icc alpha beta)

/-- Split and inert primes partition the good-angle count. -/
theorem goodAnglePrimesUpTo_eq
    (theta : Nat -> Real) (alpha beta : Real) (X : Nat) :
    goodAnglePrimesUpTo (extendDeuringAngle theta) alpha beta X =
      splitAnglePrimesUpTo theta alpha beta X ∪
        (if Real.pi / 2 ∈ Set.Icc alpha beta then inertPrimesUpTo X else ∅) := by
  ext p
  by_cases hAtom : Real.pi / 2 ∈ Set.Icc alpha beta
  · simp only [goodAnglePrimesUpTo, splitAnglePrimesUpTo, inertPrimesUpTo,
      hAtom, if_pos, Finset.mem_filter, Finset.mem_range, Finset.mem_union]
    constructor
    · rintro ⟨hpX, hp, hp3, htheta⟩
      have hmod_lt : p % 3 < 3 := Nat.mod_lt p (by norm_num)
      have hmod_ne_zero : p % 3 ≠ 0 := by
        intro hzero
        have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hzero
        have heq : 3 = p :=
          (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdvd
        exact hp3 heq.symm
      have hmod : p % 3 = 1 \/ p % 3 = 2 := by omega
      rcases hmod with hsplit | hinert
      · exact Or.inl ⟨hpX, hp, hsplit,
          by simpa [extendDeuringAngle, hsplit] using htheta⟩
      · exact Or.inr ⟨hpX, hp, hinert⟩
    · rintro (⟨hpX, hp, hsplit, htheta⟩ | ⟨hpX, hp, hinert⟩)
      · have hp3 : p ≠ 3 := by
          intro hpEq
          subst p
          norm_num at hsplit
        exact ⟨hpX, hp, hp3,
          by simpa [extendDeuringAngle, hsplit] using htheta⟩
      · have hnotSplit : p % 3 ≠ 1 := by omega
        have hp3 : p ≠ 3 := by
          intro hpEq
          subst p
          norm_num at hinert
        exact ⟨hpX, hp, hp3,
          by simpa [extendDeuringAngle, hnotSplit] using hAtom⟩
  · rw [if_neg hAtom, Finset.union_empty]
    simp only [goodAnglePrimesUpTo, splitAnglePrimesUpTo,
      Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hpX, hp, hp3, htheta⟩
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
        exact hAtom (by simpa [hpi] using htheta)
      exact ⟨hpX, hp, hsplit,
        by simpa [extendDeuringAngle, hsplit] using htheta⟩
    · rintro ⟨hpX, hp, hsplit, htheta⟩
      have hp3 : p ≠ 3 := by
        intro hpEq
        subst p
        norm_num at hsplit
      exact ⟨hpX, hp, hp3,
        by simpa [extendDeuringAngle, hsplit] using htheta⟩

/-- Split-angle and inert-prime sets are disjoint. -/
theorem splitAnglePrimesUpTo_disjoint_inert
    (theta : Nat -> Real) (alpha beta : Real) (X : Nat) :
    Disjoint (splitAnglePrimesUpTo theta alpha beta X) (inertPrimesUpTo X) := by
  rw [Finset.disjoint_left]
  intro p hpSplit hpInert
  have hs := (Finset.mem_filter.mp hpSplit).2.2.1
  have hi := (Finset.mem_filter.mp hpInert).2.2
  omega

/-- Cardinal form of the split/inert partition. -/
theorem card_goodAnglePrimesUpTo
    (theta : Nat -> Real) (alpha beta : Real) (X : Nat) :
    (goodAnglePrimesUpTo (extendDeuringAngle theta) alpha beta X).card =
      (splitAnglePrimesUpTo theta alpha beta X).card +
        if Real.pi / 2 ∈ Set.Icc alpha beta then (inertPrimesUpTo X).card else 0 := by
  rw [goodAnglePrimesUpTo_eq]
  by_cases hAtom : Real.pi / 2 ∈ Set.Icc alpha beta
  · rw [if_pos hAtom, Finset.card_union_of_disjoint
      (splitAnglePrimesUpTo_disjoint_inert theta alpha beta X), if_pos hAtom]
  · simp [hAtom]

/-- Uniform split-angle mass, now normalized by all rational primes. -/
theorem splitAngle_density_among_all_primes
    (theta : Nat -> Real)
    (hAngles : HeckeSplitAngleEquidistribution theta)
    (hSplit : SplitPrimeDensity)
    (alpha beta : Real)
    (hAlpha : 0 <= alpha) (hAlphaBeta : alpha <= beta)
    (hBeta : beta <= Real.pi) :
    Tendsto
      (fun X : Nat =>
        ((splitAnglePrimesUpTo theta alpha beta X).card : Real) /
          ((rationalPrimesUpTo X).card : Real))
      atTop (nhds ((beta - alpha) / (2 * Real.pi))) := by
  have hrelative := hAngles alpha beta hAlpha hAlphaBeta hBeta
  have hproduct := hrelative.mul hSplit
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
        ((splitAnglePrimesUpTo theta alpha beta X).card : Real) /
            ((splitPrimesUpTo X).card : Real) *
          (((splitPrimesUpTo X).card : Real) /
            ((rationalPrimesUpTo X).card : Real))) =ᶠ[atTop]
      (fun X : Nat =>
        ((splitAnglePrimesUpTo theta alpha beta X).card : Real) /
          ((rationalPrimesUpTo X).card : Real)) := by
    filter_upwards [hpositive] with X hpos
    have hsplitReal : ((splitPrimesUpTo X).card : Real) ≠ 0 := by
      intro hzero
      rw [hzero, zero_div] at hpos
      exact (lt_irrefl 0) hpos
    field_simp [hsplitReal]
  have h := hproduct.congr' heq
  convert h using 1
  field_simp [ne_of_gt Real.pi_pos]

/-- The full CM interval law with a continuous split part and inert atom. -/
theorem fermat_cm_angle_distribution_nat
    (theta : Nat -> Real)
    (hAngles : HeckeSplitAngleEquidistribution theta)
    (hSplit : SplitPrimeDensity)
    (hInert : InertPrimeDensity)
    (alpha beta : Real)
    (hAlpha : 0 <= alpha) (hAlphaBeta : alpha <= beta)
    (hBeta : beta <= Real.pi) :
    Tendsto
      (fun X : Nat =>
        ((goodAnglePrimesUpTo (extendDeuringAngle theta)
            alpha beta X).card : Real) /
          ((rationalPrimesUpTo X).card : Real))
      atTop
      (nhds
        ((if Real.pi / 2 ∈ Set.Icc alpha beta then (1 : Real) else 0) / 2 +
          (beta - alpha) / (2 * Real.pi))) := by
  have hSplitPart := splitAngle_density_among_all_primes
    theta hAngles hSplit alpha beta hAlpha hAlphaBeta hBeta
  by_cases hAtom : Real.pi / 2 ∈ Set.Icc alpha beta
  · have hsum := hSplitPart.add hInert
    have heq :
        (fun X : Nat =>
          ((splitAnglePrimesUpTo theta alpha beta X).card : Real) /
              ((rationalPrimesUpTo X).card : Real) +
            ((inertPrimesUpTo X).card : Real) /
              ((rationalPrimesUpTo X).card : Real)) =ᶠ[atTop]
        (fun X : Nat =>
          ((goodAnglePrimesUpTo (extendDeuringAngle theta)
              alpha beta X).card : Real) /
            ((rationalPrimesUpTo X).card : Real)) := by
      filter_upwards [] with X
      rw [card_goodAnglePrimesUpTo, if_pos hAtom]
      push_cast
      ring
    have h := hsum.congr' heq
    convert h using 1
    · simp [hAtom]
      ring
  · have heq :
        (fun X : Nat =>
          ((splitAnglePrimesUpTo theta alpha beta X).card : Real) /
            ((rationalPrimesUpTo X).card : Real)) =ᶠ[atTop]
        (fun X : Nat =>
          ((goodAnglePrimesUpTo (extendDeuringAngle theta)
              alpha beta X).card : Real) /
            ((rationalPrimesUpTo X).card : Real)) := by
      filter_upwards [] with X
      rw [card_goodAnglePrimesUpTo, if_neg hAtom]
      norm_num
    have h := hSplitPart.congr' heq
    simpa [hAtom] using h

/--
The complete source-shaped CM Sato--Tate statement is a theorem of the lower
Hecke--Deuring chain; it is not a hypothesis here.
-/
theorem fermatCMAngleSatoTate_of_hecke_character_theorem
    (theta : Nat -> Real)
    (hDeuring : forall p : Nat, Nat.Prime p -> p % 3 = 1 ->
      theta p ∈ Set.Icc 0 Real.pi /\
        (fermatFrobeniusTrace p : Real) =
          2 * Real.sqrt p * Real.cos (theta p))
    (hWeyl : CosineWeylCriterion)
    (hHecke : HeckePrimeCharacterCancellation theta)
    (hAPOne : PrimeNumberTheoremModThreeOne)
    (hPNT : OrdinaryPrimeNumberTheorem) : FermatCMAngleSatoTate := by
  let thetaAll := extendDeuringAngle theta
  have hAngles : HeckeSplitAngleEquidistribution theta :=
    heckeSplitAngleEquidistribution_of_character_cancellation
      theta (fun p hp hsplit => (hDeuring p hp hsplit).1) hWeyl hHecke
  have hSplit : SplitPrimeDensity := splitPrimeDensity_of_pnt hAPOne hPNT
  have hInert : InertPrimeDensity := inertPrimeDensity_of_pnt
    (pntModThreeTwo_of_one_and_ordinary hAPOne hPNT) hPNT
  rw [FermatCMAngleSatoTate]
  refine ⟨thetaAll, ?_, ?_⟩
  · simpa [thetaAll] using fermat_angle_data_of_deuring theta hDeuring
  · intro alpha beta hAlpha hAlphaBeta hBeta
    have hNat := fermat_cm_angle_distribution_nat
      theta hAngles hSplit hInert alpha beta hAlpha hAlphaBeta hBeta
    have hReal := hNat.comp (tendsto_nat_floor_atTop (α := Real))
    convert hReal using 1
    funext x
    simp [Function.comp_apply, goodAnglePrimesUpTo, primesUpTo,
      primeCounting, rationalPrimesUpTo, thetaAll,
      Finset.filter_filter, and_assoc]

#check @PrimeNumberTheoremModThreeTwo
#check @pntModThreeTwo_of_one_and_ordinary
#check @inertPrimeDensity_of_pnt
#check @goodAnglePrimesUpTo_eq
#check @card_goodAnglePrimesUpTo
#check @splitAngle_density_among_all_primes
#check @fermat_cm_angle_distribution_nat
#check @fermatCMAngleSatoTate_of_hecke_character_theorem
#print axioms fermatCMAngleSatoTate_of_hecke_character_theorem

end

end K3Lean.FullCMSatoTateFromHecke
