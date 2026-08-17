import K3Lean.FermatHasseAngle
import K3Lean.HeckeCosineCancellation

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Only two Hecke moments are needed for Erdos 979

The full CM Sato--Tate distribution uses every nonconstant cosine moment.
The block construction for Erdos 979 needs much less.  The quadratic
polynomial

`q(x) = (x + 1/4) * (x - 1)`

is nonpositive for `x > -1/4`, while its uniform cosine average is `1/4`.
Consequently cancellation of only the first two cosine moments supplies many
split primes whose Fermat angle has cosine at most `-1/4`.
-/

namespace K3Lean.TwoMomentHecke

open Filter Set
open K3Lean.FermatHasseAngle
open K3Lean.HeckeCharacterCriterion
open K3Lean.HeckeDeuringReduction
open K3Lean.PublishedInputs
open scoped BigOperators Topology

noncomputable section

/-- The two cosine moments actually used by the weakened negative-sector argument. -/
def FirstTwoHeckeMoments (theta : Nat -> Real) : Prop :=
  Tendsto
      (fun X : Nat => cosineMoment splitPrimesUpTo theta 1 X)
      atTop (nhds 0) /\
    Tendsto
      (fun X : Nat => cosineMoment splitPrimesUpTo theta 2 X)
      atTop (nhds 0)

/-- The quadratic test polynomial that detects a weakly negative angle. -/
def negativeTestPolynomial (x : Real) : Real :=
  (x + (1 : Real) / 4) * (x - 1)

/-- Its cumulative sum over split rational primes. -/
def negativeTestSum (theta : Nat -> Real) (X : Nat) : Real :=
  ∑ p ∈ splitPrimesUpTo X, negativeTestPolynomial (Real.cos (theta p))

/-- Split primes in a dyadic interval on which the test polynomial may be positive. -/
def splitPrimesInDyadic (X : Nat) : Finset Nat :=
  (Finset.Ioc X (2 * X)).filter (fun p => Nat.Prime p /\ p % 3 = 1)

/-- Split primes in a dyadic interval on which the test polynomial may be positive. -/
def weakNegativeAnglePrimes
    (theta : Nat -> Real) (X : Nat) : Finset Nat :=
  (splitPrimesInDyadic X).filter (fun p =>
    Real.cos (theta p) <= -(1 : Real) / 4)

/-- The test-polynomial sum restricted to a dyadic interval. -/
def dyadicNegativeTestSum (theta : Nat -> Real) (X : Nat) : Real :=
  ∑ p ∈ splitPrimesInDyadic X,
    negativeTestPolynomial (Real.cos (theta p))

theorem negativeTestPolynomial_nonpos_of_neg_quarter_lt
    {x : Real} (hx : -(1 : Real) / 4 < x) (hxOne : x <= 1) :
    negativeTestPolynomial x <= 0 := by
  rw [negativeTestPolynomial]
  exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

theorem negativeTestPolynomial_le_three_halves
    {x : Real} (hx : -1 <= x) (hxOne : x <= 1) :
    negativeTestPolynomial x <= (3 : Real) / 2 := by
  rw [negativeTestPolynomial]
  nlinarith

/-- Cumulative split primes decompose into the previous cutoff and its dyadic shell. -/
theorem splitPrimesUpTo_two_mul (X : Nat) :
    splitPrimesUpTo (2 * X) =
      splitPrimesUpTo X ∪ splitPrimesInDyadic X := by
  ext p
  simp only [splitPrimesUpTo, splitPrimesInDyadic,
    Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]
  constructor
  · rintro ⟨hpBound, hpPrime, hpMod⟩
    by_cases hpX : p <= X
    · exact Or.inl ⟨by omega, hpPrime, hpMod⟩
    · exact Or.inr ⟨⟨by omega, by omega⟩, hpPrime, hpMod⟩
  · rintro (⟨hpBound, hpPrime, hpMod⟩ | ⟨⟨hpLower, hpUpper⟩, hpPrime, hpMod⟩)
    · exact ⟨by omega, hpPrime, hpMod⟩
    · exact ⟨by omega, hpPrime, hpMod⟩

/-- The cumulative and dyadic split-prime sets are disjoint. -/
theorem splitPrimesUpTo_disjoint_dyadic (X : Nat) :
    Disjoint (splitPrimesUpTo X) (splitPrimesInDyadic X) := by
  rw [Finset.disjoint_left]
  intro p hpUp hpDyadic
  have hpUpper : p <= X := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hpUp).1
    omega
  have hpLower : X < p :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpDyadic).1).1
  omega

/-- The dyadic test sum is the difference of two cumulative test sums. -/
theorem dyadicNegativeTestSum_eq_sub (theta : Nat -> Real) (X : Nat) :
    dyadicNegativeTestSum theta X =
      negativeTestSum theta (2 * X) - negativeTestSum theta X := by
  rw [negativeTestSum, negativeTestSum, dyadicNegativeTestSum,
    splitPrimesUpTo_two_mul,
    Finset.sum_union (splitPrimesUpTo_disjoint_dyadic X)]
  ring

/-- Only weakly negative angles can contribute positively to the dyadic test sum. -/
theorem dyadicNegativeTestSum_le_card (theta : Nat -> Real) (X : Nat) :
    dyadicNegativeTestSum theta X <=
      (3 : Real) / 2 * (weakNegativeAnglePrimes theta X).card := by
  rw [dyadicNegativeTestSum]
  calc
    (∑ p ∈ splitPrimesInDyadic X,
        negativeTestPolynomial (Real.cos (theta p))) <=
        ∑ p ∈ splitPrimesInDyadic X,
          if Real.cos (theta p) <= -(1 : Real) / 4
          then (3 : Real) / 2 else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      split_ifs with hNegative
      · exact negativeTestPolynomial_le_three_halves
          (Real.neg_one_le_cos _) (Real.cos_le_one _)
      · exact negativeTestPolynomial_nonpos_of_neg_quarter_lt
          (lt_of_not_ge hNegative) (Real.cos_le_one _)
    _ = (3 : Real) / 2 * (weakNegativeAnglePrimes theta X).card := by
      rw [weakNegativeAnglePrimes]
      calc
        (∑ p ∈ splitPrimesInDyadic X,
            if Real.cos (theta p) <= -(1 : Real) / 4
            then (3 : Real) / 2 else 0) =
            (3 : Real) / 2 *
              ∑ p ∈ splitPrimesInDyadic X,
                if Real.cos (theta p) <= -(1 : Real) / 4
                then (1 : Real) else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          split_ifs <;> norm_num
        _ = (3 : Real) / 2 *
            (((splitPrimesInDyadic X).filter (fun p =>
              Real.cos (theta p) <= -(1 : Real) / 4)).card : Real) := by
          rw [Finset.sum_boole]

/-- Exact finite-sum identity behind the two-moment reduction. -/
theorem negativeTestSum_identity (theta : Nat -> Real) (X : Nat) :
    negativeTestSum theta X =
      ((splitPrimesUpTo X).card : Real) / 4 +
        (1 : Real) / 2 *
          (∑ p ∈ splitPrimesUpTo X, Real.cos ((2 : Real) * theta p)) -
        (3 : Real) / 4 *
          (∑ p ∈ splitPrimesUpTo X, Real.cos (theta p)) := by
  rw [negativeTestSum]
  calc
    (∑ p ∈ splitPrimesUpTo X,
        negativeTestPolynomial (Real.cos (theta p))) =
        ∑ p ∈ splitPrimesUpTo X,
          ((1 : Real) / 4 +
            (1 : Real) / 2 * Real.cos ((2 : Real) * theta p) -
            (3 : Real) / 4 * Real.cos (theta p)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [negativeTestPolynomial, Real.cos_two_mul]
      ring
    _ = ((splitPrimesUpTo X).card : Real) / 4 +
          (1 : Real) / 2 *
            (∑ p ∈ splitPrimesUpTo X, Real.cos ((2 : Real) * theta p)) -
          (3 : Real) / 4 *
            (∑ p ∈ splitPrimesUpTo X, Real.cos (theta p)) := by
      simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring

/-- After division by the split-prime count, the test sum has limit `1/4`. -/
theorem normalized_negativeTestSum_tendsto
    (theta : Nat -> Real)
    (hMoments : FirstTwoHeckeMoments theta) :
    Tendsto
      (fun X : Nat =>
        negativeTestSum theta X / ((splitPrimesUpTo X).card : Real))
      atTop (nhds ((1 : Real) / 4)) := by
  have hFormula :
      (fun X : Nat =>
        negativeTestSum theta X / ((splitPrimesUpTo X).card : Real)) =ᶠ[atTop]
      (fun X : Nat =>
        (1 : Real) / 4 +
          (1 : Real) / 2 * cosineMoment splitPrimesUpTo theta 2 X -
          (3 : Real) / 4 * cosineMoment splitPrimesUpTo theta 1 X) := by
    filter_upwards [splitPrimesUpTo_eventually_nonempty] with X hX
    have hCard : ((splitPrimesUpTo X).card : Real) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr hX)
    rw [negativeTestSum_identity]
    simp only [cosineMoment, Nat.cast_ofNat, one_mul]
    field_simp [hCard]
    ring
  have hLimit :
      Tendsto
        (fun X : Nat =>
          (1 : Real) / 4 +
            (1 : Real) / 2 * cosineMoment splitPrimesUpTo theta 2 X -
            (3 : Real) / 4 * cosineMoment splitPrimesUpTo theta 1 X)
        atTop (nhds ((1 : Real) / 4)) := by
    convert
      (tendsto_const_nhds.add
        ((hMoments.2.const_mul ((1 : Real) / 2)))).sub
          (hMoments.1.const_mul ((3 : Real) / 4)) using 1 <;> norm_num
  exact hLimit.congr' hFormula.symm

/-- PNT normalization of the cumulative test sum. -/
theorem negativeTestSum_pnt
    (theta : Nat -> Real)
    (hMoments : FirstTwoHeckeMoments theta)
    (hAP : PrimeNumberTheoremModThreeOne) :
    Tendsto
      (fun X : Nat => negativeTestSum theta X * Real.log X / (X : Real))
      atTop (nhds ((1 : Real) / 8)) := by
  have hProduct := (normalized_negativeTestSum_tendsto theta hMoments).mul hAP
  have hFormula :
      (fun X : Nat =>
        (negativeTestSum theta X / ((splitPrimesUpTo X).card : Real)) *
          (((splitPrimesUpTo X).card : Real) * Real.log X / (X : Real))) =ᶠ[atTop]
      (fun X : Nat => negativeTestSum theta X * Real.log X / (X : Real)) := by
    filter_upwards [splitPrimesUpTo_eventually_nonempty,
      eventually_ge_atTop (1 : Nat)] with X hSplit hX
    have hCard : ((splitPrimesUpTo X).card : Real) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr hSplit)
    have hXne : (X : Real) ≠ 0 := by positivity
    field_simp [hCard, hXne]
  convert hProduct.congr' hFormula using 1 <;> norm_num

/-- For `X >= 256`, eight copies of `log 2` fit below `log X`. -/
theorem eight_log_two_le_log_nat {X : Nat} (hX : 256 <= X) :
    8 * Real.log 2 <= Real.log X := by
  have hcast : (256 : Real) <= (X : Real) := by exact_mod_cast hX
  have hmono : Real.log (256 : Real) <= Real.log (X : Real) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < X))) hcast
  calc
    8 * Real.log 2 = Real.log ((2 : Real) ^ 8) := by
      simpa using (Real.log_pow (2 : Real) 8).symm
    _ = Real.log (256 : Real) := by norm_num
    _ <= Real.log (X : Real) := hmono

/-- A fixed logarithm comparison for the dyadic subtraction. -/
theorem eight_log_two_mul_le_nine_log {X : Nat} (hX : 256 <= X) :
    8 * Real.log (2 * X : Nat) <= 9 * Real.log X := by
  have hXpos : (0 : Real) < X := by exact_mod_cast (by omega : 0 < X)
  have hlogMul : Real.log ((2 * X : Nat) : Real) =
      Real.log 2 + Real.log (X : Real) := by
    push_cast
    rw [Real.log_mul (by norm_num) hXpos.ne']
  rw [hlogMul]
  nlinarith [eight_log_two_le_log_nat hX]

/-- The dyadic test sum has a concrete positive main term. -/
theorem dyadicNegativeTestSum_eventually_lower
    (theta : Nat -> Real)
    (hMoments : FirstTwoHeckeMoments theta)
    (hAP : PrimeNumberTheoremModThreeOne) :
    ∀ᶠ X : Nat in atTop,
      (X : Real) / (12 * Real.log X) < dyadicNegativeTestSum theta X := by
  have hNeighborhood :
      Set.Ioo ((3 : Real) / 25) ((13 : Real) / 100) ∈
        nhds ((1 : Real) / 8) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  obtain ⟨X0, hAfter⟩ := eventually_atTop.1
    ((negativeTestSum_pnt theta hMoments hAP).eventually hNeighborhood)
  refine eventually_atTop.2 ⟨max X0 256, ?_⟩
  intro X hX
  have hX0 : X0 <= X := (le_max_left X0 256).trans hX
  have h256 : 256 <= X := (le_max_right X0 256).trans hX
  have hTwoX0 : X0 <= 2 * X :=
    hX0.trans (Nat.le_mul_of_pos_left X (by norm_num))
  have hAtX := hAfter X hX0
  have hAtTwoX := hAfter (2 * X) hTwoX0
  let S1 := negativeTestSum theta X
  let S2 := negativeTestSum theta (2 * X)
  let x : Real := X
  let l1 := Real.log (X : Real)
  let l2 := Real.log ((2 * X : Nat) : Real)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hl1 : 0 < l1 := by
    dsimp [l1]
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hl2 : 0 < l2 := by
    dsimp [l2]
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * X))
  have hLowerTwo : (6 : Real) / 25 * x < S2 * l2 := by
    have hDen : (0 : Real) < (2 * X : Nat) := by positivity
    have h := (lt_div_iff₀ hDen).mp hAtTwoX.1
    dsimp [S2, l2, x]
    norm_num [Nat.cast_mul] at h ⊢
    nlinarith
  have hUpperOne : S1 * l1 < (13 : Real) / 100 * x := by
    have hDen : (0 : Real) < X := by positivity
    have h := (div_lt_iff₀ hDen).mp hAtX.2
    simpa [S1, l1, x] using h
  have hLogCompare : 8 * l2 <= 9 * l1 := by
    simpa [l1, l2] using eight_log_two_mul_le_nine_log h256
  have hS2pos : 0 < S2 := by
    by_contra hNot
    have hNonpos : S2 <= 0 := le_of_not_gt hNot
    have hProductNonpos : S2 * l2 <= 0 :=
      mul_nonpos_of_nonpos_of_nonneg hNonpos hl2.le
    have hLeftPos : 0 < (6 : Real) / 25 * x := by positivity
    linarith
  have hScaledLog : S2 * (8 * l2) <= S2 * (9 * l1) :=
    mul_le_mul_of_nonneg_left hLogCompare hS2pos.le
  have hLowerTwo' : (16 : Real) / 75 * x < S2 * l1 := by
    nlinarith [hLowerTwo, hScaledLog]
  rw [dyadicNegativeTestSum_eq_sub]
  have hDen : 0 < 12 * Real.log (X : Real) := by
    simpa [l1] using mul_pos (by norm_num : (0 : Real) < 12) hl1
  apply (div_lt_iff₀ hDen).2
  dsimp [S1, S2, x, l1] at hLowerTwo' hUpperOne ⊢
  nlinarith

/-- The positive dyadic test mass forces many weakly negative split primes. -/
theorem weakNegativeAnglePrimes_eventually_lower
    (theta : Nat -> Real)
    (hMoments : FirstTwoHeckeMoments theta)
    (hAP : PrimeNumberTheoremModThreeOne) :
    ∀ᶠ X : Nat in atTop,
      (X : Real) / (18 * Real.log X) <
        ((weakNegativeAnglePrimes theta X).card : Real) := by
  filter_upwards [dyadicNegativeTestSum_eventually_lower theta hMoments hAP,
    eventually_ge_atTop (256 : Nat)] with X hTest hX
  have hLog : Real.log (X : Real) ≠ 0 := by
    exact (Real.log_pos (by exact_mod_cast (by omega : 1 < X))).ne'
  have hScale :
      (X : Real) / (18 * Real.log X) =
        (2 : Real) / 3 * ((X : Real) / (12 * Real.log X)) := by
    field_simp [hLog]
    ring
  rw [hScale]
  have hCard := dyadicNegativeTestSum_le_card theta X
  nlinarith

/-- The weak integer-valued prime supply needed by the finite block argument. -/
def WeakNegativeAngleAbundance (theta : Nat -> Real) : Prop :=
  ∀ᶠ T : Nat in atTop,
    T ^ 6 <= (weakNegativeAnglePrimes theta (T ^ 8)).card

/-- Two Hecke moments and the PNT in `1 mod 3` imply polynomially many usable primes. -/
theorem weakNegativeAngleAbundance_of_two_moments
    (theta : Nat -> Real)
    (hMoments : FirstTwoHeckeMoments theta)
    (hAP : PrimeNumberTheoremModThreeOne) :
    WeakNegativeAngleAbundance theta := by
  obtain ⟨X0, hAfter⟩ := eventually_atTop.1
    (weakNegativeAnglePrimes_eventually_lower theta hMoments hAP)
  refine eventually_atTop.2 ⟨max X0 144, ?_⟩
  intro T hT
  have hX0T : X0 <= T := (le_max_left X0 144).trans hT
  have h144T : 144 <= T := (le_max_right X0 144).trans hT
  have hTone : 1 <= T := by omega
  have hX0Pow : X0 <= T ^ 8 :=
    hX0T.trans (le_self_pow hTone (by norm_num))
  have hCount := hAfter (T ^ 8) hX0Pow
  have hTpos : (0 : Real) < T := by positivity
  have hLogT : Real.log (T : Real) <= (T : Real) :=
    Real.log_le_self hTpos.le
  have hLogPow : Real.log ((T ^ 8 : Nat) : Real) =
      8 * Real.log (T : Real) := by
    simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  have hLogPowPos : 0 < Real.log ((T ^ 8 : Nat) : Real) := by
    exact Real.log_pos (by exact_mod_cast (by
      have hTwo : 2 <= T := by omega
      have := Nat.pow_le_pow_left hTwo 8
      norm_num at this ⊢
      omega : 1 < T ^ 8))
  have hDenCompare :
      18 * Real.log ((T ^ 8 : Nat) : Real) <= 144 * (T : Real) := by
    rw [hLogPow]
    nlinarith
  have hNumeratorNonneg : (0 : Real) <= (T ^ 8 : Nat) := by positivity
  have hFractionCompare :
      ((T ^ 8 : Nat) : Real) / (144 * (T : Real)) <=
        ((T ^ 8 : Nat) : Real) /
          (18 * Real.log ((T ^ 8 : Nat) : Real)) := by
    exact div_le_div_of_nonneg_left hNumeratorNonneg
      (mul_pos (by norm_num) hLogPowPos) hDenCompare
  have hPowerNat : 144 * T ^ 7 <= T ^ 8 := by
    calc
      144 * T ^ 7 <= T * T ^ 7 := Nat.mul_le_mul_right (T ^ 7) h144T
      _ = T ^ 8 := by ring
  have hBase : ((T ^ 6 : Nat) : Real) <=
      ((T ^ 8 : Nat) : Real) / (144 * (T : Real)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hTpos)).2
    have hPowerReal : ((144 * T ^ 7 : Nat) : Real) <=
        ((T ^ 8 : Nat) : Real) := by exact_mod_cast hPowerNat
    push_cast at hPowerReal ⊢
    nlinarith
  have hReal : ((T ^ 6 : Nat) : Real) <
      ((weakNegativeAnglePrimes theta (T ^ 8)).card : Real) :=
    hBase.trans_lt (hFractionCompare.trans_lt hCount)
  exact (by exact_mod_cast hReal : T ^ 6 <
    (weakNegativeAnglePrimes theta (T ^ 8)).card).le

#check @FirstTwoHeckeMoments
#check @normalized_negativeTestSum_tendsto
#print axioms normalized_negativeTestSum_tendsto
#check @negativeTestSum_pnt
#print axioms negativeTestSum_pnt
#check @dyadicNegativeTestSum_eventually_lower
#print axioms dyadicNegativeTestSum_eventually_lower
#check @weakNegativeAngleAbundance_of_two_moments
#print axioms weakNegativeAngleAbundance_of_two_moments

end

end K3Lean.TwoMomentHecke
