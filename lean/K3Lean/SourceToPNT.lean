import K3Lean.SourceTheorems
import K3Lean.StandardCorollaries
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# From Gallagher--Ford to the finite uniform prime-class input

This file contains the conversion from the source-level real asymptotic to the
integer statement consumed by the finite lifting argument.  In particular,
the logarithmic loss and the ceiling division defining the common class count
are proved here rather than hidden in an external hypothesis.
-/

namespace K3Lean.SourceToPNT

open Filter Set
open K3Lean.CMProof
open K3Lean.FiniteLifting
open K3Lean.PublishedInputs
open K3Lean.SourceTheorems
open K3Lean.StandardCorollaries
open scoped BigOperators Topology

noncomputable section

/--
Choose one prime divisor of Ford's exceptional conductor.  Excluding every
modulus divisible by that prime is a stronger restriction than excluding only
moduli divisible by the full conductor.
-/
def gallagherFordPNT_of_conductor
    (H : GallagherFordConductorPNT) : GallagherFordPNT where
  exponent := H.exponent
  errorConstant := H.errorConstant
  exponent_pos := H.exponent_pos
  errorConstant_pos := H.errorConstant_pos
  threshold := H.threshold
  threshold_ge_two := H.threshold_ge_two
  estimate := by
    intro Q hQ
    obtain ⟨d, hdTwo, hestimate⟩ := H.estimate Q hQ
    have hd_ne_one : d ≠ 1 := by
      omega
    let exceptionalPrime := d.minFac
    have hp : Nat.Prime exceptionalPrime := by
      simpa [exceptionalPrime] using Nat.minFac_prime hd_ne_one
    refine ⟨exceptionalPrime, hp, ?_⟩
    intro q r hq hq8Q hcoprime hprime y hy
    apply hestimate q r hq hq8Q hcoprime
    · intro hdq
      exact hprime ((Nat.minFac_dvd d).trans hdq)
    · exact hy

/-- Real logarithms of positive natural numbers are bounded by base-two logs. -/
theorem real_log_nat_le_succ_log_two (n : Nat) :
    Real.log n ≤ (Nat.log 2 n + 1 : Nat) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : (0 : Real) < n := by positivity
  have hpowNat : n < 2 ^ (Nat.log 2 n + 1) :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two n
  have hpowReal : (n : Real) ≤ ((2 ^ (Nat.log 2 n + 1) : Nat) : Real) := by
    exact_mod_cast hpowNat.le
  have hlog := Real.log_le_log hnpos hpowReal
  rw [Nat.cast_pow, Real.log_pow] at hlog
  have hlogtwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h ⊢
    exact h
  calc
    Real.log n ≤ (Nat.log 2 n + 1 : Real) * Real.log 2 := by
      simpa using hlog
    _ ≤ (((Nat.log 2 n + 1 : Nat) : Real)) := by
      have hnonneg : (0 : Real) ≤ Nat.log 2 n + 1 := by positivity
      have hmul := mul_le_mul_of_nonneg_left hlogtwo hnonneg
      simpa only [Nat.cast_add, Nat.cast_one, mul_one] using hmul

/-- At natural arguments, the two progression-counting definitions agree. -/
theorem progressionCount_nat_eq (X q r : Nat) (hr : r < q) :
    progressionCount (X : Real) q r = (primesInClass q X r).card := by
  unfold progressionCount
  apply congrArg Finset.card
  ext p
  simp [progressionCount, primesInProgressionUpTo, primesUpTo,
    primesInClass, Nat.mod_eq_of_lt hr, and_assoc]

/-- Every prime at most `X` is either `2` or belongs to the odd residue class. -/
theorem rationalPrimesUpTo_eq_insert_two_odd (X : Nat) (hX : 2 ≤ X) :
    rationalPrimesUpTo X = insert 2 (primesInClass 2 X 1) := by
  ext p
  simp only [rationalPrimesUpTo, primesInClass, Finset.mem_filter,
    Finset.mem_range, Finset.mem_insert]
  constructor
  · rintro ⟨hpBound, hpPrime⟩
    rcases hpPrime.eq_two_or_odd with rfl | hpOdd
    · exact Or.inl rfl
    · exact Or.inr ⟨hpBound, hpPrime, hpOdd⟩
  · rintro (rfl | ⟨hpBound, hpPrime, _hpOdd⟩)
    · exact ⟨by omega, Nat.prime_two⟩
    · exact ⟨hpBound, hpPrime⟩

/-- At natural cutoffs, total prime count is odd-prime count plus the prime `2`. -/
theorem rationalPrimesUpTo_card_eq_progressionCount (X : Nat) (hX : 2 ≤ X) :
    (rationalPrimesUpTo X).card = progressionCount (X : Real) 2 1 + 1 := by
  rw [rationalPrimesUpTo_eq_insert_two_odd X hX,
    Finset.card_insert_of_notMem]
  · rw [progressionCount_nat_eq X 2 1 (by norm_num)]
  · simp [primesInClass]

/-- The relative error in `GallagherFordPNT` is eventually at most `1/2`. -/
theorem gallagherFord_error_eventually_half (H : GallagherFordPNT) :
    ∀ᶠ Q : Nat in atTop,
      H.errorConstant * (Real.log Q) ^ (-H.exponent) ≤ (1 : Real) / 2 := by
  have hlog : Tendsto (fun Q : Nat => Real.log (Q : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrpow : Tendsto
      (fun Q : Nat => (Real.log Q) ^ (-H.exponent))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop H.exponent_pos).comp hlog
  have hzero : Tendsto
      (fun Q : Nat => H.errorConstant * (Real.log Q) ^ (-H.exponent))
      atTop (nhds 0) := by
    simpa using
      (show Tendsto (fun _Q : Nat => H.errorConstant) atTop
          (nhds H.errorConstant) from tendsto_const_nhds).mul hrpow
  have hhalf : Set.Iio ((1 : Real) / 2) ∈ nhds 0 :=
    Iio_mem_nhds (by norm_num)
  filter_upwards [hzero.eventually hhalf] with Q hQ
  exact hQ.le

/-- The relative error coefficient in Ford's conductor formulation tends to zero. -/
theorem gallagherFordConductor_error_tendsto_zero
    (H : GallagherFordConductorPNT) :
    Tendsto
      (fun Q : Nat =>
        H.errorConstant * (Real.log Q) ^ (-H.exponent))
      atTop (nhds 0) := by
  have hlog : Tendsto (fun Q : Nat => Real.log (Q : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrpow : Tendsto
      (fun Q : Nat => (Real.log Q) ^ (-H.exponent))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop H.exponent_pos).comp hlog
  simpa using
    (show Tendsto (fun _Q : Nat => H.errorConstant) atTop
        (nhds H.errorConstant) from tendsto_const_nhds).mul hrpow

/--
Ford's conductor-level PNT contains the ordinary PNT as the special residue
class `1 mod 2`.  The source lower bound has already been absorbed into the
condition `2 < exceptionalConductor`, so the exceptional conductor cannot
divide the modulus `2`.
-/
theorem ordinaryPNT_of_gallagherFordConductor
    (H : GallagherFordConductorPNT) : OrdinaryPrimeNumberTheorem := by
  rw [OrdinaryPrimeNumberTheorem, Metric.tendsto_atTop]
  intro ε hε
  have herror := gallagherFordConductor_error_tendsto_zero H
  obtain ⟨Qerror, hQerror⟩ :=
    Metric.tendsto_atTop.1 herror (ε / 4) (by linarith)
  let Q := max H.threshold (max Qerror 2)
  have hQthreshold : H.threshold ≤ Q := le_max_left _ _
  have hQerrorBound : Qerror ≤ Q :=
    (le_max_left Qerror 2).trans (le_max_right H.threshold _)
  have hQtwo : 2 ≤ Q :=
    (le_max_right Qerror 2).trans (le_max_right H.threshold _)
  have hdeltaDist := hQerror Q hQerrorBound
  have hdeltaNonneg :
      (0 : Real) ≤ H.errorConstant * (Real.log Q) ^ (-H.exponent) := by
    exact mul_nonneg H.errorConstant_pos.le
      (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q))) _)
  have hdelta :
      H.errorConstant * (Real.log Q) ^ (-H.exponent) < ε / 4 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hdeltaNonneg] at hdeltaDist
    exact hdeltaDist
  obtain ⟨exceptionalConductor, hConductorTwo, hestimate⟩ :=
    H.estimate Q hQthreshold
  have hnotdivtwo : ¬exceptionalConductor ∣ 2 := by
    intro hd
    have hle : exceptionalConductor ≤ 2 :=
      Nat.le_of_dvd (by norm_num) hd
    omega
  have hlogDiv :
      Tendsto (fun X : Nat => Real.log X / (X : Real)) atTop (nhds 0) := by
    have hcomp := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
    exact hcomp.congr' (Filter.Eventually.of_forall fun X => rfl)
  obtain ⟨Nlog, hNlog⟩ :=
    Metric.tendsto_atTop.1 hlogDiv (ε / 4) (by linarith)
  obtain ⟨Ncutoff, hNcutoff⟩ := exists_nat_gt
    (Real.rpow (Q : Real) (Real.log (Real.log Q)))
  refine ⟨max 2 (max Nlog Ncutoff), ?_⟩
  intro X hX
  have hXtwo : 2 ≤ X := (le_max_left 2 (max Nlog Ncutoff)).trans hX
  have hNlogX : Nlog ≤ X :=
    (le_max_left Nlog Ncutoff).trans
      ((le_max_right 2 (max Nlog Ncutoff)).trans hX)
  have hNcutoffX : Ncutoff ≤ X :=
    (le_max_right Nlog Ncutoff).trans
      ((le_max_right 2 (max Nlog Ncutoff)).trans hX)
  have hcutoff :
      Real.rpow (Q : Real) (Real.log (Real.log Q)) < (X : Real) :=
    hNcutoff.trans_le (by exact_mod_cast hNcutoffX)
  have hest := hestimate 2 1 (by norm_num)
    (by omega : 2 ≤ 8 * Q) (by norm_num) hnotdivtwo (X : Real) hcutoff
  let C : Real := progressionCount (X : Real) 2 1
  let P : Real := (rationalPrimesUpTo X).card
  let L : Real := Real.log X
  let M : Real := (X : Real) / L
  let δ : Real := H.errorConstant * (Real.log Q) ^ (-H.exponent)
  have hXpos : (0 : Real) < X := by exact_mod_cast (by omega : 0 < X)
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hscaleNonneg : 0 ≤ L / (X : Real) := by positivity
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hest' : |C - M| ≤ δ * M := by
    simpa [C, M, δ] using hest
  have hcountNat := rationalPrimesUpTo_card_eq_progressionCount X hXtwo
  have hcount : P = C + 1 := by
    dsimp [P, C]
    exact_mod_cast hcountNat
  have hmainCancel : M * (L / (X : Real)) = 1 := by
    dsimp [M]
    field_simp
  have hscaledError :
      |(C - M) * (L / (X : Real))| ≤ δ := by
    calc
      |(C - M) * (L / (X : Real))| =
          |C - M| * (L / (X : Real)) := by
            rw [abs_mul, abs_of_nonneg hscaleNonneg]
      _ ≤ (δ * M) * (L / (X : Real)) :=
        mul_le_mul_of_nonneg_right hest' hscaleNonneg
      _ = δ := by rw [mul_assoc, hmainCancel, mul_one]
  have htargetIdentity :
      P * L / (X : Real) - 1 =
        (C - M) * (L / (X : Real)) + L / (X : Real) := by
    rw [hcount]
    dsimp [M]
    field_simp
    ring
  have hlogSmallDist := hNlog X hNlogX
  have hlogSmall : L / (X : Real) < ε / 4 := by
    dsimp [L]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hscaleNonneg] at hlogSmallDist
    exact hlogSmallDist
  have hdeltaDef : δ < ε / 4 := by simpa [δ] using hdelta
  change dist (P * L / (X : Real)) 1 < ε
  rw [Real.dist_eq, htargetIdentity]
  calc
    |(C - M) * (L / (X : Real)) + L / (X : Real)|
        ≤ |(C - M) * (L / (X : Real))| + |L / (X : Real)| := abs_add_le _ _
    _ = |(C - M) * (L / (X : Real))| + L / (X : Real) := by
      rw [abs_of_nonneg hscaleNonneg]
    _ < ε := by nlinarith [hscaledError, hdeltaDef, hlogSmall]

/-- The natural cutoff used below lies beyond Ford's `Q^(log log Q)` cutoff. -/
theorem ford_cutoff_lt_nat_power {Q : Nat} (hQ : 2 ≤ Q) :
    Real.rpow (Q : Real) (Real.log (Real.log Q)) <
      (Q ^ (Nat.log 2 Q + 1) : Nat) := by
  have hQreal : (1 : Real) < Q := by exact_mod_cast hQ
  have hlogQpos : 0 < Real.log (Q : Real) := Real.log_pos hQreal
  have hloglog_le : Real.log (Real.log Q) ≤ Real.log Q - 1 :=
    Real.log_le_sub_one_of_pos hlogQpos
  have hQlt : Q < 2 ^ (Nat.log 2 Q + 1) :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two Q
  have hlogQlt : Real.log (Q : Real) < (Nat.log 2 Q + 1 : Real) := by
    have hcast : (Q : Real) < ((2 ^ (Nat.log 2 Q + 1) : Nat) : Real) := by
      exact_mod_cast hQlt
    have hlogs := Real.log_lt_log (by positivity : (0 : Real) < Q) hcast
    rw [Nat.cast_pow, Real.log_pow] at hlogs
    have hlogtwo : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
      norm_num at h ⊢
      exact h
    push_cast at hlogs ⊢
    nlinarith [Nat.cast_nonneg (α := Real) (Nat.log 2 Q)]
  have hexponent : Real.log (Real.log Q) < (Nat.log 2 Q + 1 : Real) :=
    lt_of_le_of_lt hloglog_le (by linarith)
  have hrpow := Real.rpow_lt_rpow_of_exponent_lt hQreal hexponent
  have hexpCast :
      (Nat.log 2 Q + 1 : Real) = ((Nat.log 2 Q + 1 : Nat) : Real) := by
    norm_num
  rw [hexpCast, Real.rpow_natCast] at hrpow
  norm_cast at hrpow ⊢

/-- Coarse, entirely discrete lower bound extracted from Gallagher--Ford. -/
def CoarseExceptionalPNT : Prop :=
  ∃ Q₀ : Nat, 2 ≤ Q₀ ∧
    ∀ Q : Nat, Q₀ ≤ Q →
      ∃ exceptionalPrime : Nat, Nat.Prime exceptionalPrime ∧
        ∀ q : Nat, 1 < q → q ≤ Q → ¬exceptionalPrime ∣ q →
          ∀ X : Nat, Q ^ (Nat.log 2 Q + 1) ≤ X →
            ∀ r ∈ unitResidues q,
              X ≤ 4 * (Nat.log 2 X + 1) * q.totient *
                (primesInClass q X r).card

/-- Ford--Gallagher's real estimate implies the coarse discrete lower bound. -/
theorem coarseExceptionalPNT_of_gallagherFord
    (H : GallagherFordPNT) : CoarseExceptionalPNT := by
  obtain ⟨Qerr, hQerr⟩ :=
    (eventually_atTop.1 (gallagherFord_error_eventually_half H))
  refine ⟨max H.threshold (max Qerr 2), by omega, ?_⟩
  intro Q hQ
  have hsourceQ : H.threshold ≤ Q :=
    (le_max_left _ _).trans hQ
  have herrQ :
      H.errorConstant * (Real.log Q) ^ (-H.exponent) ≤ (1 : Real) / 2 :=
    hQerr Q ((le_max_left Qerr 2).trans ((le_max_right H.threshold _).trans hQ))
  have hQtwo : 2 ≤ Q :=
    (le_max_right Qerr 2).trans ((le_max_right H.threshold _).trans hQ)
  obtain ⟨exceptionalPrime, hp, hestimate⟩ := H.estimate Q hsourceQ
  refine ⟨exceptionalPrime, hp, ?_⟩
  intro q hq hqQ hexceptional X hX r hr
  have hrParts := Finset.mem_filter.mp hr
  have hrlt : r < q := Finset.mem_range.mp hrParts.1
  have hrcoprime : r.Coprime q := hrParts.2.symm
  have hq8Q : q ≤ 8 * Q := hqQ.trans (by omega)
  have hQpowXreal :
      ((Q ^ (Nat.log 2 Q + 1) : Nat) : Real) ≤ (X : Real) := by
    exact_mod_cast hX
  have hcutoff :
      Real.rpow (Q : Real) (Real.log (Real.log Q)) < (X : Real) :=
    (ford_cutoff_lt_nat_power hQtwo).trans_le hQpowXreal
  have hest := hestimate q r hq hq8Q hrcoprime hexceptional
    (X : Real) hcutoff
  have hXtwo : 2 ≤ X := by
    have hQlePow : Q ≤ Q ^ (Nat.log 2 Q + 1) := by
      apply Nat.le_pow
      omega
    exact hQtwo.trans (hQlePow.trans hX)
  have hlogXpos : 0 < Real.log (X : Real) := by
    exact Real.log_pos (by exact_mod_cast hXtwo)
  have htotientPos : 0 < q.totient := Nat.totient_pos.mpr (by omega)
  have hdenomPos :
      0 < (q.totient : Real) * Real.log (X : Real) := by positivity
  let M : Real :=
    (X : Real) / ((q.totient : Real) * Real.log (X : Real))
  let C : Real := progressionCount (X : Real) q r
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have herrorM :
      H.errorConstant * (Real.log Q) ^ (-H.exponent) * M ≤ M / 2 := by
    have := mul_le_mul_of_nonneg_right herrQ hMnonneg
    nlinarith
  have habsLower : M - C ≤ |C - M| := by
    simpa only [neg_sub] using neg_le_abs (C - M)
  have hCM : M / 2 ≤ C := by
    dsimp [M, C] at hest ⊢
    dsimp [M, C] at habsLower herrorM
    nlinarith
  have hfrac :
      (X : Real) / ((q.totient : Real) * Real.log (X : Real)) ≤ 2 * C := by
    dsimp [M] at hCM
    nlinarith
  have hXscale :
      (X : Real) ≤
        ((q.totient : Real) * Real.log (X : Real)) * (2 * C) :=
    by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        (div_le_iff₀ hdenomPos).mp hfrac
  have hlogBound := real_log_nat_le_succ_log_two X
  have hfactorNonneg : 0 ≤ (q.totient : Real) * C := by
    dsimp [C]
    positivity
  have hlogScaled :
      Real.log (X : Real) * ((q.totient : Real) * C) ≤
        (((Nat.log 2 X + 1 : Nat) : Real)) *
          ((q.totient : Real) * C) :=
    mul_le_mul_of_nonneg_right hlogBound hfactorNonneg
  have hcoarseReal :
      (X : Real) ≤
        (4 * (Nat.log 2 X + 1) * q.totient *
          (primesInClass q X r).card : Nat) := by
    have hcount : C = (primesInClass q X r).card := by
      dsimp [C]
      exact_mod_cast progressionCount_nat_eq X q r hrlt
    rw [hcount] at hXscale hlogScaled
    push_cast at hXscale hlogScaled ⊢
    ring_nf at hXscale hlogScaled ⊢
    nlinarith [Nat.cast_nonneg (α := Real) q.totient,
      Nat.cast_nonneg (α := Real) (primesInClass q X r).card,
      Nat.cast_nonneg (α := Real) (Nat.log 2 X + 1)]
  exact_mod_cast hcoarseReal

/-- The base-two logarithm of the chosen cutoff fits inside `logLoss Q`. -/
theorem cutoff_log_loss_le {Q : Nat} (hQ : 2 ≤ Q) :
    4 * (Nat.log 2 (Q ^ (Nat.log 2 Q + 1)) + 1) ≤ logLoss Q := by
  let e := Nat.log 2 Q + 1
  have he : 0 < e := by simp [e]
  have hQlt : Q < 2 ^ e := by
    simpa [e] using Nat.lt_pow_succ_log_self Nat.one_lt_two Q
  have hpowlt : Q ^ e < 2 ^ (e ^ 2) := by
    calc
      Q ^ e < (2 ^ e) ^ e := Nat.pow_lt_pow_left hQlt he.ne'
      _ = 2 ^ (e ^ 2) := by rw [← Nat.pow_mul]; ring
  have hloglt : Nat.log 2 (Q ^ e) < e ^ 2 :=
    Nat.log_lt_of_lt_pow (by positivity) hpowlt
  have heOne : 1 ≤ e := by omega
  have hePow : e ^ 2 ≤ e ^ 4 :=
    pow_le_pow_right' heOne (by norm_num)
  change 4 * (Nat.log 2 (Q ^ e) + 1) ≤ 4 * e ^ 4
  exact Nat.mul_le_mul_left 4 ((Nat.succ_le_iff.mpr hloglt).trans hePow)

/-- The coarse PNT is exactly strong enough to produce the shared class count. -/
theorem exceptionalPNTCorollary_of_coarse
    (H : CoarseExceptionalPNT) : ExceptionalPNTCorollary := by
  obtain ⟨Q₀, hQ₀, hafter⟩ := H
  refine ⟨Q₀, hQ₀, ?_⟩
  intro Q hQ
  obtain ⟨exceptionalPrime, hp, hclasses⟩ := hafter Q hQ
  let X := Q ^ (Nat.log 2 Q + 1)
  refine ⟨exceptionalPrime, X, hp, ?_, ?_⟩
  · dsimp [X]
    apply Nat.le_pow
    omega
  intro q hq hqQ hexceptional
  let d := logLoss Q * q.totient
  let g := X ⌈/⌉ d
  have hQtwo : 2 ≤ Q := hQ₀.trans hQ
  have htotient : 0 < q.totient := Nat.totient_pos.mpr (by omega)
  have hloss : 0 < logLoss Q := by
    simp [logLoss]
  have hd : 0 < d := Nat.mul_pos hloss htotient
  have hscale : X ≤ d * g := by
    exact (ceilDiv_le_iff_le_mul hd).mp le_rfl
  refine ⟨g, ?_, ?_⟩
  · simpa [d, Nat.mul_assoc] using hscale
  intro r hr
  have hsmall := hclasses q hq hqQ hexceptional X (by rfl) r hr
  have hlossBound :
      4 * (Nat.log 2 X + 1) ≤ logLoss Q := by
    simpa [X] using cutoff_log_loss_le hQtwo
  have hlarge :
      X ≤ d * (primesInClass q X r).card := by
    calc
      X ≤ 4 * (Nat.log 2 X + 1) * q.totient *
          (primesInClass q X r).card := hsmall
      _ ≤ logLoss Q * q.totient * (primesInClass q X r).card := by
        simpa only [Nat.mul_assoc] using
          Nat.mul_le_mul_right (q.totient * (primesInClass q X r).card)
            hlossBound
      _ = d * (primesInClass q X r).card := by simp [d, Nat.mul_assoc]
  exact (ceilDiv_le_iff_le_mul hd).mpr hlarge

/-- The source-level Gallagher--Ford theorem discharges the old PNT corollary. -/
theorem exceptionalPNTCorollary_of_gallagherFord
    (H : GallagherFordPNT) : ExceptionalPNTCorollary :=
  exceptionalPNTCorollary_of_coarse
    (coarseExceptionalPNT_of_gallagherFord H)

/-- Ford's conductor-level source statement implies the finite corollary. -/
theorem exceptionalPNTCorollary_of_gallagherFordConductor
    (H : GallagherFordConductorPNT) : ExceptionalPNTCorollary :=
  exceptionalPNTCorollary_of_gallagherFord
    (gallagherFordPNT_of_conductor H)

#check @gallagherFordPNT_of_conductor
#check @real_log_nat_le_succ_log_two
#check @progressionCount_nat_eq
#check @rationalPrimesUpTo_card_eq_progressionCount
#check @gallagherFord_error_eventually_half
#check @gallagherFordConductor_error_tendsto_zero
#check @ordinaryPNT_of_gallagherFordConductor
#check @ford_cutoff_lt_nat_power
#check @CoarseExceptionalPNT
#check @coarseExceptionalPNT_of_gallagherFord
#check @cutoff_log_loss_le
#check @exceptionalPNTCorollary_of_coarse
#check @exceptionalPNTCorollary_of_gallagherFord
#check @exceptionalPNTCorollary_of_gallagherFordConductor
#print axioms gallagherFordPNT_of_conductor
#print axioms ordinaryPNT_of_gallagherFordConductor
#print axioms exceptionalPNTCorollary_of_gallagherFord
#print axioms exceptionalPNTCorollary_of_gallagherFordConductor

end

end K3Lean.SourceToPNT
