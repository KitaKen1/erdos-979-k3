import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.SumCoeff

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Conditional Dirichlet continuation from a square-root partial-sum bound

This file isolates the analytic part of the remaining Fermat-Hecke argument.
If the coefficient partial sums are `O(X^r)`, their step function has a
Mellin transform that is holomorphic after the substitution `s -> -s` in the
half-plane `r < re s`.  The application uses `r = 1 / 2`.
-/

namespace K3Lean.AbelMellinContinuation

open Asymptotics Complex Filter Finset MeasureTheory Set Topology
open scoped Topology

noncomputable section

/-- Partial sums, viewed as a step function and cut off below `1`. -/
def partialSumStep (f : Nat -> Complex) (x : Real) : Complex :=
  Set.indicator (Set.Ioi (1 : Real))
    (fun t : Real => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n) x

/-- The coefficient cancellation estimate used by Abel summation. -/
def PartialSumBigO (f : Nat -> Complex) (r : Real) : Prop :=
  (fun N : Nat => ∑ n ∈ Finset.Icc 1 N, f n) =O[atTop]
    (fun N : Nat => (N : Real) ^ r)

private theorem uncutPartialSumStep_locallyIntegrableOn
    (f : Nat -> Complex) :
    LocallyIntegrableOn
      (fun t : Real => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n)
      (Set.Ioi (0 : Real)) := by
  have h : LocallyIntegrableOn
      (fun t : Real => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n)
      (Set.Ici (0 : Real)) := by
    simpa only [one_mul] using
      (locallyIntegrableOn_mul_sum_Icc f (a := (0 : Real)) (m := 1)
        le_rfl (locallyIntegrableOn_const (1 : Complex)))
  exact h.mono_set Set.Ioi_subset_Ici_self

theorem partialSumStep_locallyIntegrableOn
    (f : Nat -> Complex) :
    LocallyIntegrableOn (partialSumStep f) (Set.Ioi (0 : Real)) := by
  intro x hx
  rcases uncutPartialSumStep_locallyIntegrableOn f x hx with
    ⟨u, hu, hInt⟩
  exact ⟨u, hu, hInt.indicator measurableSet_Ioi⟩

theorem partialSumStep_isBigO_atTop
    {f : Nat -> Complex} {r : Real}
    (h : PartialSumBigO f r) (hr : 0 <= r) :
    partialSumStep f =O[atTop] (fun x : Real => x ^ r) := by
  have hFloor :
      (fun x : Real => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n) =O[atTop]
        (fun x : Real => x ^ r) :=
    (h.comp_tendsto tendsto_nat_floor_atTop).trans
      (isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0))
  have hEq : partialSumStep f =ᶠ[atTop]
      (fun x : Real => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n) := by
    filter_upwards [eventually_gt_atTop (1 : Real)] with x hx
    simp [partialSumStep, hx]
  exact hEq.trans_isBigO hFloor

theorem partialSumStep_isBigO_nhdsGT_zero
    (f : Nat -> Complex) (b : Real) :
    partialSumStep f =O[nhdsWithin (0 : Real) (Set.Ioi 0)]
      (fun x : Real => x ^ (-b)) := by
  have hEq : partialSumStep f =ᶠ[nhdsWithin (0 : Real) (Set.Ioi 0)] 0 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : Real) < 1 by norm_num)] with x hx
    have hxNot : x ∉ Set.Ioi (1 : Real) := not_lt.mpr hx.2.le
    simp [partialSumStep, hxNot]
  exact hEq.trans_isBigO
    (isBigO_zero (fun x : Real => x ^ (-b))
      (nhdsWithin (0 : Real) (Set.Ioi 0)))

/-- The Mellin transform of the partial-sum step function, in Dirichlet coordinates. -/
def abelMellinCore (f : Nat -> Complex) (s : Complex) : Complex :=
  mellin (partialSumStep f) (-s)

theorem abelMellinCore_eq_integral
    (f : Nat -> Complex) (s : Complex) :
    abelMellinCore f s =
      ∫ t : Real in Set.Ioi (1 : Real),
        (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n) *
          (t : Complex) ^ (-(s + 1)) := by
  rw [abelMellinCore, mellin]
  have hIntegrand :
      ∀ t ∈ Set.Ioi (0 : Real),
        (t : Complex) ^ (-s - 1) • partialSumStep f t =
          Set.indicator (Set.Ioi (1 : Real))
            (fun u : Real =>
              (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, f n) *
                (u : Complex) ^ (-(s + 1))) t := by
    intro t _ht
    by_cases ht : t ∈ Set.Ioi (1 : Real)
    · simp only [partialSumStep, Set.indicator_of_mem ht, smul_eq_mul]
      rw [mul_comm]
      congr 1
      ring
    · simp [partialSumStep, ht]
  rw [setIntegral_congr_fun measurableSet_Ioi hIntegrand,
    setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Set.Ioi_subset_Ioi (by norm_num : (0 : Real) <= 1))]

theorem differentiableAt_abelMellinCore
    {f : Nat -> Complex} {r : Real} (h : PartialSumBigO f r)
    (hr0 : 0 <= r) {s : Complex} (hs : r < s.re) :
    DifferentiableAt Complex (abelMellinCore f) s := by
  let b : Real := (-s).re - 1
  have hMellin : DifferentiableAt Complex (mellin (partialSumStep f)) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow
      (partialSumStep_locallyIntegrableOn f)
      (a := -r) (b := b)
      (by simpa using partialSumStep_isBigO_atTop h hr0)
      (by simp; linarith)
      (partialSumStep_isBigO_nhdsGT_zero f b)
      (by simp [b])
  exact hMellin.comp s (hasDerivAt_neg s).differentiableAt

/-- Abel's candidate continuation for a Dirichlet series. -/
def abelMellinContinuation (f : Nat -> Complex) (s : Complex) : Complex :=
  s * abelMellinCore f s

theorem differentiableOn_abelMellinContinuation
    {f : Nat -> Complex} {r : Real} (h : PartialSumBigO f r)
    (hr0 : 0 <= r) :
    DifferentiableOn Complex (abelMellinContinuation f)
      {s : Complex | r < s.re} := by
  intro s hs
  exact (differentiableAt_id.mul
    (differentiableAt_abelMellinCore h hr0 hs)).differentiableWithinAt

theorem abelMellinContinuation_eq_LSeries
    {f : Nat -> Complex} {r : Real} (h : PartialSumBigO f r)
    (hr0 : 0 <= r) {s : Complex} (hs : r < s.re)
    (hSummable : LSeriesSummable f s) :
    abelMellinContinuation f s = LSeries f s := by
  rw [abelMellinContinuation, abelMellinCore_eq_integral]
  exact (LSeries_eq_mul_integral f hr0 hs hSummable h).symm

#check @PartialSumBigO
#check @differentiableOn_abelMellinContinuation
#check @abelMellinContinuation_eq_LSeries
#print axioms differentiableOn_abelMellinContinuation
#print axioms abelMellinContinuation_eq_LSeries

end

end K3Lean.AbelMellinContinuation
