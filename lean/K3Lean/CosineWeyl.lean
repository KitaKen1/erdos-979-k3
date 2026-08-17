import K3Lean.HeckeCharacterCriterion
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# The cosine Weyl criterion from Mathlib

This file proves the topological/measure-theoretic input that was previously
exposed as `CosineWeylCriterion`.  The proof symmetrizes each angle on the
circle of circumference `2 * pi`.  Its integer Fourier coefficients are the
given cosine moments.  Density of the Fourier algebra gives weak convergence
to Haar measure, and folding the circle by distance from zero gives uniform
measure on `[0, pi]`.
-/

namespace K3Lean.CosineWeyl

open Filter Set
open MeasureTheory MeasureTheory.Measure Algebra Submodule
open K3Lean.HeckeCharacterCriterion
open scoped BigOperators ComplexConjugate ENNReal NNReal Topology

noncomputable section

private local instance twoPiPositive : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

abbrev AngleCircle := AddCircle (2 * Real.pi)

/-- A Fourier monomial, regarded as a bounded continuous function. -/
def fourierBCF (n : Int) : BoundedContinuousFunction AngleCircle Complex :=
  BoundedContinuousFunction.mkOfCompact (fourier n)

@[simp]
theorem fourierBCF_apply (n : Int) (x : AngleCircle) :
    fourierBCF n x = fourier n x :=
  rfl

/-- The bounded Fourier star-subalgebra on the angle circle. -/
def fourierBCFSubalgebra :
    StarSubalgebra Complex (BoundedContinuousFunction AngleCircle Complex) where
  toSubalgebra := Algebra.adjoin Complex (Set.range fourierBCF)
  star_mem' := by
    change Algebra.adjoin Complex (Set.range fourierBCF) ≤
      star (Algebra.adjoin Complex (Set.range fourierBCF))
    refine Algebra.adjoin_le ?_
    rintro _ ⟨n, rfl⟩
    exact Algebra.subset_adjoin ⟨-n, by
      ext x
      simp [fourierBCF]⟩

/-- The Fourier algebra is exactly the linear span of its monomials. -/
theorem fourierBCFSubalgebra_coe :
    Subalgebra.toSubmodule fourierBCFSubalgebra.toSubalgebra =
      Submodule.span Complex (Set.range fourierBCF) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Set.Subset.trans ?_ Submodule.subset_span
  intro x hx
  refine Submonoid.closure_induction (fun _ => id) ⟨0, ?_⟩ ?_ hx
  · ext z
    simp [fourierBCF]
  · rintro _ _ _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    refine ⟨m + n, ?_⟩
    ext z
    simp [fourierBCF]

/-- The bounded Fourier algebra separates points of the circle. -/
theorem fourierBCFSubalgebra_separatesPoints :
    (fourierBCFSubalgebra.map
      (BoundedContinuousFunction.toContinuousMapStarₐ Complex)).SeparatesPoints := by
  intro x y hxy
  refine ⟨_, ⟨fourier 1, ?_, rfl⟩, ?_⟩
  · change ∃ f ∈ fourierBCFSubalgebra,
      BoundedContinuousFunction.toContinuousMapStarₐ Complex f = fourier 1
    refine ⟨fourierBCF 1, ?_, ?_⟩
    · exact Algebra.subset_adjoin ⟨1, rfl⟩
    · ext z
      rfl
  · dsimp only
    rw [fourier_one, fourier_one]
    contrapose hxy
    rw [Subtype.coe_inj] at hxy
    exact AddCircle.injective_toCircle twoPiPositive.elim.ne' hxy

/-- A Dirac measure bundled as a finite measure. -/
def finiteDirac (x : AngleCircle) : FiniteMeasure AngleCircle :=
  ⟨Measure.dirac x, inferInstance⟩

@[simp]
theorem finiteDirac_mass (x : AngleCircle) : (finiteDirac x).mass = 1 := by
  change (Measure.dirac x Set.univ).toNNReal = 1
  simp

@[simp]
theorem finiteMeasure_mass_add (mu nu : FiniteMeasure AngleCircle) :
    (mu + nu).mass = mu.mass + nu.mass := by
  change (mu + nu) Set.univ = mu Set.univ + nu Set.univ
  exact congrFun (FiniteMeasure.coeFn_add mu nu) Set.univ

/-- A finite measure placing one atom at each `theta p` and `-theta p`. -/
def symmetrizedFiniteMeasure
    (A : Nat → Finset Nat) (theta : Nat → Real) (X : Nat) :
    FiniteMeasure AngleCircle :=
  ∑ p ∈ A X, (finiteDirac (theta p : AngleCircle) +
    finiteDirac ((-theta p : Real) : AngleCircle))

/-- The probability-normalized symmetrized empirical measure. -/
def symmetrizedEmpiricalMeasure
    (A : Nat → Finset Nat) (theta : Nat → Real) (X : Nat) :
    ProbabilityMeasure AngleCircle :=
  (symmetrizedFiniteMeasure A theta X).normalize

@[simp]
theorem symmetrizedFiniteMeasure_mass
    (A : Nat → Finset Nat) (theta : Nat → Real) (X : Nat) :
    (symmetrizedFiniteMeasure A theta X).mass = 2 * (A X).card := by
  classical
  have aux : ∀ s : Finset Nat,
      (∑ p ∈ s, (finiteDirac (theta p : AngleCircle) +
        finiteDirac ((-theta p : Real) : AngleCircle))).mass = 2 * s.card := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih =>
        rw [Finset.sum_insert hp, finiteMeasure_mass_add,
          finiteMeasure_mass_add, finiteDirac_mass, finiteDirac_mass, ih]
        simp [Finset.card_insert_of_notMem hp]
        ring_nf
  exact aux (A X)

theorem symmetrizedFiniteMeasure_ne_zero
    {A : Nat → Finset Nat} {theta : Nat → Real} {X : Nat}
    (hX : (A X).Nonempty) :
    symmetrizedFiniteMeasure A theta X ≠ 0 := by
  intro hzero
  have hmass := congrArg FiniteMeasure.mass hzero
  simp [symmetrizedFiniteMeasure_mass, hX.ne_empty] at hmass

/-- Pairing the two signs turns a Fourier monomial into a cosine. -/
theorem fourierBCF_add_neg_nat (n : Nat) (x : Real) :
    fourierBCF (n : Int) (x : AngleCircle) +
        fourierBCF (n : Int) ((-x : Real) : AngleCircle) =
      2 * (Real.cos ((n : Real) * x) : Complex) := by
  rw [fourierBCF_apply, fourierBCF_apply, fourier_coe_apply,
    fourier_coe_apply]
  have hpi : (Real.pi : Complex) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hpos :
      2 * (Real.pi : Complex) * Complex.I * (n : Int) * (x : Complex) /
          (2 * Real.pi : Real) =
        (((n : Real) * x : Real) : Complex) * Complex.I := by
    push_cast
    field_simp
  have hneg :
      2 * (Real.pi : Complex) * Complex.I * (n : Int) * ((-x : Real) : Complex) /
          (2 * Real.pi : Real) =
        (-((n : Real) * x : Real) : Complex) * Complex.I := by
    push_cast
    field_simp
  rw [hpos, hneg, Complex.exp_ofReal_mul_I]
  rw [← Complex.ofReal_neg, Complex.exp_ofReal_mul_I]
  simp [Real.cos_neg, Real.sin_neg]
  ring

/-- The Fourier integral of the empirical measure is the original cosine moment. -/
theorem integral_fourierBCF_symmetrized_nat
    {A : Nat → Finset Nat} {theta : Nat → Real} {X n : Nat}
    (hX : (A X).Nonempty) :
    (∫ z, fourierBCF (n : Int) z ∂
      (symmetrizedEmpiricalMeasure A theta X : Measure AngleCircle)) =
        (cosineMoment A theta n X : Complex) := by
  let mu := symmetrizedFiniteMeasure A theta X
  have hmu : mu ≠ 0 := symmetrizedFiniteMeasure_ne_zero hX
  rw [show symmetrizedEmpiricalMeasure A theta X = mu.normalize by rfl]
  rw [← FiniteMeasure.average_eq_integral_normalize mu hmu]
  rw [MeasureTheory.average_eq]
  have hmassReal : (mu : Measure AngleCircle).real Set.univ =
      2 * ((A X).card : Real) := by
    rw [measureReal_def, ← FiniteMeasure.ennreal_mass]
    simp [mu, symmetrizedFiniteMeasure_mass]
  rw [hmassReal]
  have hint :
      (∫ z, fourierBCF (n : Int) z ∂(mu : Measure AngleCircle)) =
        ∑ p ∈ A X,
          (fourierBCF (n : Int) (theta p : AngleCircle) +
            fourierBCF (n : Int) ((-theta p : Real) : AngleCircle)) := by
    have hmeasure : (mu : Measure AngleCircle) =
        ∑ p ∈ A X,
          (Measure.dirac (theta p : AngleCircle) +
            Measure.dirac ((-theta p : Real) : AngleCircle)) := by
      simp [mu, symmetrizedFiniteMeasure, finiteDirac]
    rw [hmeasure]
    rw [integral_finsetSum_measure]
    · apply Finset.sum_congr rfl
      intro p hp
      rw [integral_add_measure]
      · simp
      · exact (fourierBCF (n : Int)).integrable _
      · exact (fourierBCF (n : Int)).integrable _
    · intro p hp
      exact (fourierBCF (n : Int)).integrable _
  rw [hint]
  simp_rw [fourierBCF_add_neg_nat]
  simp only [cosineMoment]
  push_cast
  rw [Complex.real_smul, ← Finset.mul_sum]
  have hcard : (((A X).card : Nat) : Complex) ≠ 0 := by
    exact_mod_cast hX.card_pos.ne'
  push_cast
  field_simp [hcard]

/-- Negative Fourier modes have the same integral after symmetrization. -/
theorem integral_fourierBCF_symmetrized_negSucc
    {A : Nat → Finset Nat} {theta : Nat → Real} {X : Nat}
    (k : Nat) (hX : (A X).Nonempty) :
    (∫ z, fourierBCF (Int.negSucc k) z ∂
      (symmetrizedEmpiricalMeasure A theta X : Measure AngleCircle)) =
        (cosineMoment A theta (k + 1) X : Complex) := by
  have hpos := integral_fourierBCF_symmetrized_nat
    (A := A) (theta := theta) (X := X) (n := k + 1) hX
  calc
    (∫ z, fourierBCF (Int.negSucc k) z ∂
        (symmetrizedEmpiricalMeasure A theta X : Measure AngleCircle)) =
        ∫ z, conj (fourierBCF ((k + 1 : Nat) : Int) z) ∂
          (symmetrizedEmpiricalMeasure A theta X : Measure AngleCircle) := by
            apply integral_congr_ae
            filter_upwards [] with z
            change fourier (Int.negSucc k) z =
              conj (fourier ((k + 1 : Nat) : Int) z)
            have hindex : Int.negSucc k = -((k + 1 : Nat) : Int) := by omega
            rw [hindex]
            exact fourier_neg
    _ = conj (∫ z, fourierBCF ((k + 1 : Nat) : Int) z ∂
          (symmetrizedEmpiricalMeasure A theta X : Measure AngleCircle)) := by
            exact integral_conj
    _ = conj (cosineMoment A theta (k + 1) X : Complex) := by rw [hpos]
    _ = (cosineMoment A theta (k + 1) X : Complex) := by simp

/-- Haar integrals of nonconstant Fourier monomials vanish. -/
theorem integral_fourierBCF_haar (n : Int) :
    (∫ z, fourierBCF n z ∂AddCircle.haarAddCircle) =
      if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [fourierBCF]
  · rw [if_neg hn]
    simpa [fourierBCF] using
      (integral_eq_zero_of_add_right_eq_neg
        (μ := AddCircle.haarAddCircle)
        (fourier_add_half_inv_index hn twoPiPositive.elim))

/-- The zeroth cosine moment of a nonempty finite family is one. -/
theorem cosineMoment_zero
    {A : Nat → Finset Nat} {theta : Nat → Real} {X : Nat}
    (hX : (A X).Nonempty) : cosineMoment A theta 0 X = 1 := by
  simp [cosineMoment, hX.ne_empty]

/-- Every Fourier generator has the required limiting integral. -/
theorem tendsto_integral_fourierBCF
    {A : Nat → Finset Nat} {theta : Nat → Real}
    (hne : ∀ᶠ X : Nat in atTop, (A X).Nonempty)
    (hmom : ∀ m : Nat, 0 < m →
      Tendsto (fun X : Nat => cosineMoment A theta m X)
        atTop (nhds 0))
    (n : Int) :
    Tendsto
      (fun X : Nat =>
        ∫ z, fourierBCF n z ∂
          (symmetrizedEmpiricalMeasure A theta X : Measure AngleCircle))
      atTop
      (nhds (∫ z, fourierBCF n z ∂AddCircle.haarAddCircle)) := by
  cases n with
  | ofNat m =>
      cases m with
      | zero =>
          simpa [fourierBCF] using
            (tendsto_const_nhds :
              Tendsto (fun _ : Nat => (1 : Complex)) atTop (nhds 1))
      | succ m =>
          have hreal := hmom (m + 1) (by omega)
          have hcomplex :
              Tendsto
                (fun X : Nat => (cosineMoment A theta (m + 1) X : Complex))
                atTop (nhds 0) :=
            (Complex.continuous_ofReal.tendsto 0).comp hreal
          have heq :
              (fun X : Nat =>
                ∫ z, fourierBCF ((m + 1 : Nat) : Int) z ∂
                  (symmetrizedEmpiricalMeasure A theta X : Measure AngleCircle)) =ᶠ[atTop]
                (fun X : Nat => (cosineMoment A theta (m + 1) X : Complex)) := by
            filter_upwards [hne] with X hX
            exact integral_fourierBCF_symmetrized_nat hX
          rw [integral_fourierBCF_haar, if_neg (by
            exact ne_of_gt (by positivity : (0 : Int) < (m : Int) + 1))]
          exact hcomplex.congr' heq.symm
  | negSucc k =>
      have hreal := hmom (k + 1) (by omega)
      have hcomplex :
          Tendsto
            (fun X : Nat => (cosineMoment A theta (k + 1) X : Complex))
            atTop (nhds 0) :=
        (Complex.continuous_ofReal.tendsto 0).comp hreal
      have heq :
          (fun X : Nat =>
            ∫ z, fourierBCF (Int.negSucc k) z ∂
              (symmetrizedEmpiricalMeasure A theta X : Measure AngleCircle)) =ᶠ[atTop]
            (fun X : Nat => (cosineMoment A theta (k + 1) X : Complex)) := by
        filter_upwards [hne] with X hX
        exact integral_fourierBCF_symmetrized_negSucc k hX
      rw [integral_fourierBCF_haar]
      simp only [Int.negSucc_ne_zero, if_false]
      exact hcomplex.congr' heq.symm

/-- Normalized Haar measure on the angle circle. -/
def haarProbability : ProbabilityMeasure AngleCircle :=
  ⟨AddCircle.haarAddCircle, inferInstance⟩

/-- Vanishing cosine moments imply weak convergence to Haar measure. -/
theorem symmetrizedEmpiricalMeasure_tendsto_haar
    {A : Nat → Finset Nat} {theta : Nat → Real}
    (hne : ∀ᶠ X : Nat in atTop, (A X).Nonempty)
    (hmom : ∀ m : Nat, 0 < m →
      Tendsto (fun X : Nat => cosineMoment A theta m X)
        atTop (nhds 0)) :
    Tendsto (symmetrizedEmpiricalMeasure A theta) atTop
      (nhds haarProbability) := by
  refine ProbabilityMeasure.tendsto_of_tight_of_separatesPoints Complex
    (μ := symmetrizedEmpiricalMeasure A theta)
    (μ₀ := haarProbability)
    IsTightMeasureSet.of_compactSpace
    fourierBCFSubalgebra_separatesPoints ?_
  intro g hg
  have hgspan : g ∈ Submodule.span Complex (Set.range fourierBCF) := by
    rw [← fourierBCFSubalgebra_coe]
    exact hg
  clear hg
  induction hgspan using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨n, rfl⟩ := hg
      exact tendsto_integral_fourierBCF hne hmom n
  | zero => simp
  | add f g hf hg hflim hglim =>
      simpa only [BoundedContinuousFunction.coe_add, Pi.add_apply,
        integral_add (f.integrable _) (g.integrable _)] using hflim.add hglim
  | smul c f hf hflim =>
      simpa only [BoundedContinuousFunction.coe_smul, Pi.smul_apply,
        integral_smul] using hflim.const_smul c

/-- The circular annulus obtained by folding the interval `[alpha, beta]`. -/
def foldedInterval (alpha beta : Real) : Set AngleCircle :=
  {z | dist z 0 ∈ Set.Icc alpha beta}

theorem foldedInterval_eq_sdiff_ball (alpha beta : Real) :
    foldedInterval alpha beta =
      Metric.closedBall (0 : AngleCircle) beta \ Metric.ball 0 alpha := by
  ext z
  simp only [foldedInterval, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_sdiff,
    Metric.mem_closedBall, Metric.mem_ball]
  rw [dist_comm z 0]
  constructor <;> intro h
  · exact ⟨h.2, not_lt.mpr h.1⟩
  · exact ⟨not_lt.mp h.2, h.1⟩

theorem measurableSet_foldedInterval (alpha beta : Real) :
    MeasurableSet (foldedInterval alpha beta) := by
  rw [foldedInterval_eq_sdiff_ball]
  exact
    (measurableSet_closedBall :
      MeasurableSet (Metric.closedBall (0 : AngleCircle) beta)).diff
      (measurableSet_ball :
        MeasurableSet (Metric.ball (0 : AngleCircle) alpha))

/-- On the half-period, circular distance from zero is ordinary absolute value. -/
theorem dist_coe_zero_eq_abs (x : Real) (hx : |x| ≤ Real.pi) :
    dist (x : AngleCircle) 0 = |x| := by
  rw [dist_eq_norm, sub_zero]
  apply (AddCircle.norm_coe_eq_abs_iff (p := 2 * Real.pi) (by positivity)).2
  simpa [abs_of_pos Real.pi_pos] using hx

theorem dist_coe_zero_of_mem_Icc {x : Real}
    (hx : x ∈ Set.Icc (0 : Real) Real.pi) :
    dist (x : AngleCircle) 0 = x := by
  rw [dist_coe_zero_eq_abs x (by simpa [abs_of_nonneg hx.1] using hx.2),
    abs_of_nonneg hx.1]

theorem dist_neg_coe_zero_of_mem_Icc {x : Real}
    (hx : x ∈ Set.Icc (0 : Real) Real.pi) :
    dist ((-x : Real) : AngleCircle) 0 = x := by
  rw [dist_coe_zero_eq_abs (-x) (by simpa [abs_neg, abs_of_nonneg hx.1] using hx.2),
    abs_neg, abs_of_nonneg hx.1]

/-- A symmetrized atom contributes twice exactly when its angle lies in the interval. -/
theorem finiteDirac_pair_foldedInterval
    {x alpha beta : Real} (hx : x ∈ Set.Icc (0 : Real) Real.pi) :
    (finiteDirac (x : AngleCircle) +
        finiteDirac ((-x : Real) : AngleCircle))
        (foldedInterval alpha beta) =
      if x ∈ Set.Icc alpha beta then 2 else 0 := by
  rw [congrFun (FiniteMeasure.coeFn_add _ _) (foldedInterval alpha beta)]
  change
    (Measure.dirac (x : AngleCircle) (foldedInterval alpha beta)).toNNReal +
        (Measure.dirac ((-x : Real) : AngleCircle)
          (foldedInterval alpha beta)).toNNReal = _
  have hpos : (x : AngleCircle) ∈ foldedInterval alpha beta ↔
      x ∈ Set.Icc alpha beta := by
    simp only [foldedInterval, Set.mem_setOf_eq]
    rw [dist_coe_zero_of_mem_Icc hx]
  have hneg : ((-x : Real) : AngleCircle) ∈ foldedInterval alpha beta ↔
      x ∈ Set.Icc alpha beta := by
    simp only [foldedInterval, Set.mem_setOf_eq]
    rw [dist_neg_coe_zero_of_mem_Icc hx]
  by_cases h : x ∈ Set.Icc alpha beta
  · rw [Measure.dirac_apply_of_mem (hpos.mpr h),
      Measure.dirac_apply_of_mem (hneg.mpr h)]
    norm_num [h]
  · rw [Measure.dirac_apply, Measure.dirac_apply,
      Set.indicator_of_notMem (fun hxMem => h (hpos.mp hxMem)),
      Set.indicator_of_notMem (fun hxMem => h (hneg.mp hxMem))]
    norm_num [h]

/-- Applying the symmetrized finite measure to a folded interval counts
the original angles in that interval, with multiplicity two. -/
theorem symmetrizedFiniteMeasure_foldedInterval
    {A : Nat → Finset Nat} {theta : Nat → Real} {X : Nat}
    {alpha beta : Real}
    (hRange : ∀ p ∈ A X, theta p ∈ Set.Icc (0 : Real) Real.pi) :
    symmetrizedFiniteMeasure A theta X (foldedInterval alpha beta) =
      2 * (((A X).filter
        (fun p => theta p ∈ Set.Icc alpha beta)).card : NNReal) := by
  classical
  have aux : ∀ s : Finset Nat,
      (∀ p ∈ s, theta p ∈ Set.Icc (0 : Real) Real.pi) →
      (∑ p ∈ s, (finiteDirac (theta p : AngleCircle) +
          finiteDirac ((-theta p : Real) : AngleCircle)))
          (foldedInterval alpha beta) =
        2 * ((s.filter
          (fun p => theta p ∈ Set.Icc alpha beta)).card : NNReal) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih =>
        have hpRange : theta p ∈ Set.Icc (0 : Real) Real.pi :=
          hs p (Finset.mem_insert_self p s)
        have hsRange : ∀ q ∈ s,
            theta q ∈ Set.Icc (0 : Real) Real.pi := by
          intro q hq
          exact hs q (Finset.mem_insert_of_mem hq)
        rw [Finset.sum_insert hp]
        rw [congrFun (FiniteMeasure.coeFn_add
          (finiteDirac (theta p : AngleCircle) +
            finiteDirac ((-theta p : Real) : AngleCircle))
          (∑ q ∈ s, (finiteDirac (theta q : AngleCircle) +
            finiteDirac ((-theta q : Real) : AngleCircle))))
          (foldedInterval alpha beta)]
        simp only [Pi.add_apply]
        rw [finiteDirac_pair_foldedInterval hpRange, ih hsRange]
        by_cases hInterval : theta p ∈ Set.Icc alpha beta
        · have hInterval' : alpha ≤ theta p ∧ theta p ≤ beta := hInterval
          have hpFilter : p ∉ s.filter
              (fun q => theta q ∈ Set.Icc alpha beta) := by
            simp [hp]
          simp only [Finset.filter_insert, hInterval, if_true]
          rw [Finset.card_insert_of_notMem (by
            simpa only [Set.mem_Icc] using hpFilter)]
          push_cast
          ring
        · have hInterval' : ¬ (alpha ≤ theta p ∧ theta p ≤ beta) :=
            hInterval
          simp [Finset.filter_insert, hInterval']
  exact aux (A X) hRange

/-- The folded empirical probability is exactly the original interval frequency. -/
theorem symmetrizedEmpiricalMeasure_foldedInterval_real
    {A : Nat → Finset Nat} {theta : Nat → Real} {X : Nat}
    {alpha beta : Real}
    (hX : (A X).Nonempty)
    (hRange : ∀ p ∈ A X, theta p ∈ Set.Icc (0 : Real) Real.pi) :
    ((symmetrizedEmpiricalMeasure A theta X
        (foldedInterval alpha beta) : NNReal) : Real) =
      angleIntervalFrequency A theta alpha beta X := by
  let mu := symmetrizedFiniteMeasure A theta X
  have hmu : mu ≠ 0 := symmetrizedFiniteMeasure_ne_zero hX
  rw [show symmetrizedEmpiricalMeasure A theta X = mu.normalize by rfl]
  rw [mu.normalize_eq_of_nonzero hmu]
  simp only [NNReal.coe_mul, NNReal.coe_inv]
  rw [show mu.mass = 2 * (A X).card by
    exact symmetrizedFiniteMeasure_mass A theta X]
  rw [show mu (foldedInterval alpha beta) =
      2 * (((A X).filter
        (fun p => theta p ∈ Set.Icc alpha beta)).card : NNReal) by
    exact symmetrizedFiniteMeasure_foldedInterval hRange]
  simp only [angleIntervalFrequency]
  push_cast
  have hcard : ((A X).card : Real) ≠ 0 := by
    exact_mod_cast hX.card_pos.ne'
  field_simp [hcard]

/-- Spheres have zero normalized Haar measure on the circle. -/
theorem haar_sphere_zero (x : AngleCircle) (r : Real) :
    AddCircle.haarAddCircle (Metric.sphere x r) = 0 := by
  have hvol : (volume : Measure AngleCircle) (Metric.sphere x r) = 0 := by
    have h := (ae_eq_set.mp
      (AddCircle.closedBall_ae_eq_ball (x := x) (ε := r))).1
    simpa [Metric.closedBall_sdiff_ball] using h
  rw [AddCircle.volume_eq_smul_haarAddCircle] at hvol
  simp only [Measure.coe_smul, Pi.smul_apply, smul_eq_mul] at hvol
  exact (mul_eq_zero.mp hvol).resolve_left
    (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))

/-- A closed ball of radius `r ≤ pi` has normalized Haar mass `r / pi`. -/
theorem haar_closedBall_real (r : Real) (hr0 : 0 ≤ r) (hrpi : r ≤ Real.pi) :
    AddCircle.haarAddCircle.real (Metric.closedBall (0 : AngleCircle) r) =
      r / Real.pi := by
  have hmeasure := congrArg
    (fun mu : Measure AngleCircle => mu (Metric.closedBall (0 : AngleCircle) r))
    (@AddCircle.volume_eq_smul_haarAddCircle (2 * Real.pi) twoPiPositive)
  rw [AddCircle.volume_closedBall, min_eq_right (by linarith)] at hmeasure
  simp only [Measure.coe_smul, Pi.smul_apply, smul_eq_mul] at hmeasure
  have hreal := congrArg ENNReal.toReal hmeasure
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)] at hreal
  rw [measureReal_def]
  apply (eq_div_iff Real.pi_ne_zero).2
  nlinarith [Real.pi_pos]

/-- Open and closed balls have the same normalized Haar mass. -/
theorem haar_ball_real (r : Real) (hr0 : 0 ≤ r) (hrpi : r ≤ Real.pi) :
    AddCircle.haarAddCircle.real (Metric.ball (0 : AngleCircle) r) =
      r / Real.pi := by
  have hae : Metric.closedBall (0 : AngleCircle) r =ᵐ[AddCircle.haarAddCircle]
      Metric.ball 0 r := by
    apply ae_eq_set.2
    constructor
    · simpa [Metric.closedBall_sdiff_ball] using
        haar_sphere_zero (0 : AngleCircle) r
    · rw [show Metric.ball (0 : AngleCircle) r \
          Metric.closedBall 0 r = ∅ by
        exact Set.sdiff_eq_empty.2 Metric.ball_subset_closedBall]
      simp
  rw [← measureReal_congr hae]
  exact haar_closedBall_real r hr0 hrpi

/-- The folded interval has normalized Haar mass equal to its length ratio. -/
theorem haar_foldedInterval_real
    {alpha beta : Real} (hAlpha : 0 ≤ alpha)
    (hAlphaBeta : alpha ≤ beta) (hBeta : beta ≤ Real.pi) :
    AddCircle.haarAddCircle.real (foldedInterval alpha beta) =
      (beta - alpha) / Real.pi := by
  rw [foldedInterval_eq_sdiff_ball]
  rw [measureReal_sdiff]
  · rw [haar_closedBall_real beta (hAlpha.trans hAlphaBeta) hBeta,
      haar_ball_real alpha hAlpha (hAlphaBeta.trans hBeta)]
    ring
  · intro z hz
    exact Metric.mem_closedBall.mpr
      ((Metric.mem_ball.mp hz).le.trans hAlphaBeta)
  · exact measurableSet_ball

/-- The boundary of a folded interval consists only of its two endpoint spheres. -/
theorem frontier_foldedInterval_subset (alpha beta : Real) :
    frontier (foldedInterval alpha beta) ⊆
      Metric.sphere (0 : AngleCircle) beta ∪ Metric.sphere 0 alpha := by
  rw [foldedInterval_eq_sdiff_ball, Set.sdiff_eq]
  refine (frontier_inter_subset _ _).trans (Set.union_subset ?_ ?_)
  · exact (Set.inter_subset_left.trans
      (Metric.frontier_closedBall_subset_sphere :
        frontier (Metric.closedBall (0 : AngleCircle) beta) ⊆
          Metric.sphere 0 beta)).trans Set.subset_union_left
  · exact (Set.inter_subset_right.trans (by
      simpa only [frontier_compl] using
        (Metric.frontier_ball_subset_sphere :
          frontier (Metric.ball (0 : AngleCircle) alpha) ⊆
            Metric.sphere 0 alpha))).trans Set.subset_union_right

/-- Folded intervals are continuity sets for normalized Haar measure. -/
theorem haar_frontier_foldedInterval_zero (alpha beta : Real) :
    AddCircle.haarAddCircle (frontier (foldedInterval alpha beta)) = 0 := by
  exact measure_mono_null (frontier_foldedInterval_subset alpha beta)
    (measure_union_null
      (haar_sphere_zero (0 : AngleCircle) beta)
      (haar_sphere_zero (0 : AngleCircle) alpha))

/-- Mathlib's Fourier-density and Portmanteau theorems prove the cosine form
of Weyl's criterion required by the Hecke-character reduction. -/
theorem cosineWeylCriterion : CosineWeylCriterion := by
  intro A theta hne hRange hMom alpha beta hAlpha hAlphaBeta hBeta
  let E : Set AngleCircle := foldedInterval alpha beta
  have hWeak :
      Tendsto (symmetrizedEmpiricalMeasure A theta) atTop
        (nhds haarProbability) :=
    symmetrizedEmpiricalMeasure_tendsto_haar hne hMom
  have hBoundary : haarProbability (frontier E) = 0 := by
    change (AddCircle.haarAddCircle (frontier E)).toNNReal = 0
    rw [show AddCircle.haarAddCircle (frontier E) = 0 by
      simpa [E] using haar_frontier_foldedInterval_zero alpha beta]
    simp
  have hSet :
      Tendsto
        (fun X : Nat => symmetrizedEmpiricalMeasure A theta X E)
        atTop (nhds (haarProbability E)) :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
      hWeak hBoundary
  have hReal :
      Tendsto
        (fun X : Nat =>
          ((symmetrizedEmpiricalMeasure A theta X E : NNReal) : Real))
        atTop (nhds ((haarProbability E : NNReal) : Real)) :=
    NNReal.tendsto_coe.mpr hSet
  have hLimit : ((haarProbability E : NNReal) : Real) =
      (beta - alpha) / Real.pi := by
    change AddCircle.haarAddCircle.real E =
      (beta - alpha) / Real.pi
    simpa [E] using
      haar_foldedInterval_real hAlpha hAlphaBeta hBeta
  rw [hLimit] at hReal
  have hEventually :
      (fun X : Nat =>
        ((symmetrizedEmpiricalMeasure A theta X E : NNReal) : Real)) =ᶠ[atTop]
      (fun X : Nat => angleIntervalFrequency A theta alpha beta X) := by
    filter_upwards [hne] with X hX
    simpa [E] using
      symmetrizedEmpiricalMeasure_foldedInterval_real hX (hRange X)
  exact hReal.congr' hEventually

#check @fourierBCFSubalgebra_separatesPoints
#check @symmetrizedEmpiricalMeasure
#check @cosineWeylCriterion
#print axioms cosineWeylCriterion

end

end K3Lean.CosineWeyl
