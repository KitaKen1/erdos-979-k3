import K3Lean.SourceTheorems
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Source-shaped CM Sato--Tate specialization for the Fermat cubic

This file keeps the interval in the published Sato--Tate statement arbitrary.
The only specialization made at the external boundary is the choice of the
elliptic curve: the projective Fermat cubic.  The choice of interval, the
conversion from Frobenius angles to normalized traces, the removal of `p = 2`,
and the computation of the mass `1 / 12` are all carried out below in Lean.

Source statement:
https://arxiv.org/pdf/1506.09170#page=1
-/

namespace K3Lean.SourceSatoTate

open Filter Set
open K3Lean.PublishedInputs
open K3Lean.SourceTheorems
open scoped Topology

noncomputable section

/--
The CM branch of the displayed Sato--Tate theorem after fixing only the curve
to be the projective Fermat cubic.  The angle interval and its mass remain
fully general.

The source ranges over primes of good reduction.  For the Fermat cubic the
only bad prime is `3`, so that condition is written literally as `p ≠ 3`.
-/
def FermatCMAngleSatoTate : Prop :=
  ∃ theta : Nat → Real,
    (∀ p : Nat, Nat.Prime p → p ≠ 3 →
      theta p ∈ Set.Icc 0 Real.pi ∧
        (fermatFrobeniusTrace p : Real) =
          2 * Real.sqrt p * Real.cos (theta p)) ∧
    ∀ alpha beta : Real,
      0 ≤ alpha → alpha ≤ beta → beta ≤ Real.pi →
      Tendsto
        (fun x : Real =>
          (((primesUpTo x).filter (fun p =>
              p ≠ 3 ∧ theta p ∈ Set.Icc alpha beta)).card : Real) /
            (primeCounting x : Real))
        atTop
        (nhds
          ((if Real.pi / 2 ∈ Set.Icc alpha beta then (1 : Real) else 0) / 2 +
            (beta - alpha) / (2 * Real.pi)))

lemma fermatProjectivePointCount_two : fermatProjectivePointCount 2 = 3 := by
  rw [fermatProjectivePointCount]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide

lemma normalizedFermatTrace_two : normalizedFermatTrace 2 = 0 := by
  simp [normalizedFermatTrace, fermatFrobeniusTrace,
    fermatProjectivePointCount_two]

lemma cos_two_pi_div_three :
    Real.cos (2 * Real.pi / 3) = -(1 : Real) / 2 := by
  calc
    Real.cos (2 * Real.pi / 3) = Real.cos (Real.pi - Real.pi / 3) := by
      congr 1
      ring
    _ = -Real.cos (Real.pi / 3) := Real.cos_pi_sub _
    _ = -(1 : Real) / 2 := by rw [Real.cos_pi_div_three]; ring

lemma cos_five_pi_div_six :
    Real.cos (5 * Real.pi / 6) = -Real.sqrt 3 / 2 := by
  calc
    Real.cos (5 * Real.pi / 6) = Real.cos (Real.pi - Real.pi / 6) := by
      congr 1
      ring
    _ = -Real.cos (Real.pi / 6) := Real.cos_pi_sub _
    _ = -Real.sqrt 3 / 2 := by rw [Real.cos_pi_div_six]; ring

lemma normalizedFermatTrace_eq_cos
    {theta : Nat → Real}
    (hAngle : ∀ p : Nat, Nat.Prime p → p ≠ 3 →
      theta p ∈ Set.Icc 0 Real.pi ∧
        (fermatFrobeniusTrace p : Real) =
          2 * Real.sqrt p * Real.cos (theta p))
    {p : Nat} (hp : Nat.Prime p) (hp3 : p ≠ 3) :
    normalizedFermatTrace p = Real.cos (theta p) := by
  rw [normalizedFermatTrace, (hAngle p hp hp3).2]
  have hpReal : (0 : Real) < p := by exact_mod_cast hp.pos
  have hsqrt : Real.sqrt (p : Real) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpReal)
  field_simp

lemma fermat_angle_sector_iff_trace_sector
    {theta : Nat → Real}
    (hAngle : ∀ p : Nat, Nat.Prime p → p ≠ 3 →
      theta p ∈ Set.Icc 0 Real.pi ∧
        (fermatFrobeniusTrace p : Real) =
          2 * Real.sqrt p * Real.cos (theta p))
    {p : Nat} (hp : Nat.Prime p) (hp3 : p ≠ 3) :
    theta p ∈ Set.Icc (2 * Real.pi / 3) (5 * Real.pi / 6) ↔
      normalizedFermatTrace p ∈
        Set.Icc (-(Real.sqrt 3) / 2) (-(1 : Real) / 2) := by
  have htheta := (hAngle p hp hp3).1
  have hnorm := normalizedFermatTrace_eq_cos hAngle hp hp3
  have hLowNonneg : 0 ≤ 2 * Real.pi / 3 := by positivity
  have hLowPi : 2 * Real.pi / 3 ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have hHighNonneg : 0 ≤ 5 * Real.pi / 6 := by positivity
  have hHighPi : 5 * Real.pi / 6 ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  rw [hnorm]
  constructor
  · intro hsector
    constructor
    · rw [← cos_five_pi_div_six]
      exact Real.cos_le_cos_of_nonneg_of_le_pi htheta.1 hHighPi hsector.2
    · rw [← cos_two_pi_div_three]
      exact Real.cos_le_cos_of_nonneg_of_le_pi hLowNonneg htheta.2 hsector.1
  · intro htrace
    constructor
    · by_contra hnot
      have hlt : theta p < 2 * Real.pi / 3 := lt_of_not_ge hnot
      have hcos : Real.cos (2 * Real.pi / 3) < Real.cos (theta p) :=
        Real.cos_lt_cos_of_nonneg_of_le_pi htheta.1 hLowPi hlt
      rw [cos_two_pi_div_three] at hcos
      exact (not_lt_of_ge htrace.2) hcos
    · by_contra hnot
      have hlt : 5 * Real.pi / 6 < theta p := lt_of_not_ge hnot
      have hcos : Real.cos (theta p) < Real.cos (5 * Real.pi / 6) :=
        Real.cos_lt_cos_of_nonneg_of_le_pi hHighNonneg htheta.2 hlt
      rw [cos_five_pi_div_six] at hcos
      exact (not_lt_of_ge htrace.1) hcos

lemma source_angle_predicate_iff_trace_predicate
    {theta : Nat → Real}
    (hAngle : ∀ p : Nat, Nat.Prime p → p ≠ 3 →
      theta p ∈ Set.Icc 0 Real.pi ∧
        (fermatFrobeniusTrace p : Real) =
          2 * Real.sqrt p * Real.cos (theta p))
    (p : Nat) :
    (Nat.Prime p ∧ p ≠ 3 ∧
        theta p ∈ Set.Icc (2 * Real.pi / 3) (5 * Real.pi / 6)) ↔
      (Nat.Prime p ∧ 3 < p ∧
        normalizedFermatTrace p ∈
          Set.Icc (-(Real.sqrt 3) / 2) (-(1 : Real) / 2)) := by
  constructor
  · rintro ⟨hp, hp3, htheta⟩
    have htrace := (fermat_angle_sector_iff_trace_sector hAngle hp hp3).mp htheta
    have hpgt : 3 < p := by
      by_contra hnot
      have hpge : 2 ≤ p := hp.two_le
      have hp2 : p = 2 := by omega
      subst p
      rw [normalizedFermatTrace_two] at htrace
      norm_num at htrace
    exact ⟨hp, hpgt, htrace⟩
  · rintro ⟨hp, hpgt, htrace⟩
    have hp3 : p ≠ 3 := by omega
    exact ⟨hp, hp3,
      (fermat_angle_sector_iff_trace_sector hAngle hp hp3).mpr htrace⟩

lemma angle_sector_nat_card_eq_trace_sector_card
    {theta : Nat → Real}
    (hAngle : ∀ p : Nat, Nat.Prime p → p ≠ 3 →
      theta p ∈ Set.Icc 0 Real.pi ∧
        (fermatFrobeniusTrace p : Real) =
          2 * Real.sqrt p * Real.cos (theta p))
    (X : Nat) :
    ((primesUpTo (X : Real)).filter (fun p =>
        p ≠ 3 ∧
          theta p ∈ Set.Icc (2 * Real.pi / 3) (5 * Real.pi / 6))).card =
      (negativeCMTraceSectorPrimesUpTo X).card := by
  apply congrArg Finset.card
  ext p
  simp only [primesUpTo, Nat.floor_natCast, negativeCMTraceSectorPrimesUpTo,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨hpX, hp⟩, hp3, htheta⟩
    have hpred :=
      (source_angle_predicate_iff_trace_predicate hAngle p).mp
        ⟨hp, hp3, htheta⟩
    exact ⟨hpX, hpred⟩
  · rintro ⟨hpX, hp, hpgt, htrace⟩
    have hpred :=
      (source_angle_predicate_iff_trace_predicate hAngle p).mpr
        ⟨hp, hpgt, htrace⟩
    exact ⟨⟨hpX, hpred.1⟩, hpred.2⟩

lemma fermat_cm_mass_fixed_interval :
    ((if Real.pi / 2 ∈
          Set.Icc (2 * Real.pi / 3) (5 * Real.pi / 6)
        then (1 : Real) else 0) / 2 +
      ((5 * Real.pi / 6) - (2 * Real.pi / 3)) /
        (2 * Real.pi)) =
      (1 : Real) / 12 := by
  have hnot : Real.pi / 2 ∉
      Set.Icc (2 * Real.pi / 3) (5 * Real.pi / 6) := by
    rw [Set.mem_Icc]
    rintro ⟨hlow, _⟩
    nlinarith [Real.pi_pos]
  rw [if_neg hnot]
  field_simp [ne_of_gt Real.pi_pos]
  ring

/--
All substitutions needed by the block proof are internal consequences of the
source-shaped angle theorem.
-/
theorem fermatCMSatoTate_of_angle_satoTate
    (hST : FermatCMAngleSatoTate) : FermatCMSatoTate := by
  rw [FermatCMSatoTate]
  rcases hST with ⟨theta, hAngle, hDistribution⟩
  have hAlpha : (0 : Real) ≤ 2 * Real.pi / 3 := by positivity
  have hAlphaBeta : 2 * Real.pi / 3 ≤ 5 * Real.pi / 6 := by
    nlinarith [Real.pi_pos]
  have hBeta : 5 * Real.pi / 6 ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have hReal := hDistribution
    (2 * Real.pi / 3) (5 * Real.pi / 6)
    hAlpha hAlphaBeta hBeta
  rw [fermat_cm_mass_fixed_interval] at hReal
  have hNat := hReal.comp (tendsto_natCast_atTop_atTop (R := Real))
  convert hNat using 1
  funext X
  simp only [Function.comp_apply]
  rw [angle_sector_nat_card_eq_trace_sector_card hAngle X]
  simp [primeCounting, primesUpTo, rationalPrimesUpTo]

#check @FermatCMAngleSatoTate
#check @fermatCMSatoTate_of_angle_satoTate

end

end K3Lean.SourceSatoTate
