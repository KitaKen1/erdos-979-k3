import K3Lean.AbelMellinContinuation
import K3Lean.CanonicalFermatEuler

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# A concrete criterion for the remaining Fermat-Hecke continuation

The former continuation hypothesis is a consequence of three statements
about an ordinary Dirichlet coefficient sequence: square-root cancellation
of its partial sums, absolute convergence in `re s > 1`, and equality there
with the displayed Fermat Euler product.  The passage from these statements
to a holomorphic function on `re s > 1/2` is proved by the Mellin argument in
`AbelMellinContinuation`.
-/

namespace K3Lean.FermatDirichletCriterion

open Complex Filter Finset
open K3Lean.AbelMellinContinuation
open K3Lean.CanonicalFermatEuler
open K3Lean.HeckeBoundaryToMoment
open K3Lean.HeckeEulerNonvanishing

noncomputable section

/-- Dirichlet-series data for one required power of the Fermat Hecke character. -/
structure FermatPowerDirichletModel (theta : Nat -> Real) (m : Nat) where
  coeff : Nat -> Complex
  partial_sum_sqrt : PartialSumBigO coeff (1 / 2 : Real)
  summable_gt_one : forall s : Complex, 1 < s.re -> LSeriesSummable coeff s
  euler_eq : forall s : Complex, 1 < s.re ->
    LSeries coeff s = explicitFermatPowerL theta m s

/-- The three concrete Dirichlet models needed by the two-moment argument. -/
def FermatRequiredDirichletModels (theta : Nat -> Real) : Prop :=
  forall m : Nat, RequiredHeckePower m ->
    Nonempty (FermatPowerDirichletModel theta m)

theorem fermatPowerEulerContinuation_of_dirichletModels
    {theta : Nat -> Real} (h : FermatRequiredDirichletModels theta) :
    FermatPowerEulerContinuation theta := by
  intro m hm
  let D := Classical.choice (h m hm)
  refine ⟨abelMellinContinuation D.coeff, ?_, ?_⟩
  · simpa [heckeContinuationDomain] using
      differentiableOn_abelMellinContinuation D.partial_sum_sqrt
        (by norm_num : (0 : Real) <= 1 / 2)
  · intro s hs
    calc
      abelMellinContinuation D.coeff s = LSeries D.coeff s :=
        abelMellinContinuation_eq_LSeries D.partial_sum_sqrt
          (by norm_num) (by linarith) (D.summable_gt_one s hs)
      _ = explicitFermatPowerL theta m s := D.euler_eq s hs

#check @FermatPowerDirichletModel
#check @FermatRequiredDirichletModels
#check @fermatPowerEulerContinuation_of_dirichletModels
#print axioms fermatPowerEulerContinuation_of_dirichletModels

end

end K3Lean.FermatDirichletCriterion
