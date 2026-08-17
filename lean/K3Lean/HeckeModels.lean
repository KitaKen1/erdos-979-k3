import K3Lean.CubicJacobi
import K3Lean.PrimaryDiskBound
import K3Lean.FermatDirichletCriterion
import K3Lean.FermatEulerLogGrouping
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.SumCoeff

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# The Dirichlet models for the Fermat Hecke powers

This file constructs, for each `m ∈ {1, 2, 4}`, the concrete Dirichlet
coefficient sequence demanded by
`K3Lean.FermatDirichletCriterion.FermatPowerDirichletModel`:

* `heckeCoeff m n := ∑_{α primary, N(α) = n} (α/|α|)^m` — the angular sum
  over primary Eisenstein integers of norm `n`;
* square-root cancellation of partial sums (`K3Lean.PrimaryDiskBound`);
* absolute convergence on `re s > 1`;
* equality of its L-series with the explicit Fermat Euler product
  `explicitFermatPowerL fermatTraceAngle m` on `re s > 1`.

The Euler identification goes through the pair of completely multiplicative
functions `g`, `h` with

* `g p = exp(i m θ_p)`, `h p = exp(-i m θ_p)` at split primes,
* `g q = i^m`, `h q = -i^m` at inert primes, and `g 3 = h 3 = 0`,

whose Dirichlet convolution agrees with `heckeCoeff m` at all prime powers:
at split primes by Gauss's theorem (`K3Lean.CubicJacobi`), at inert primes and
at `3` by the classification of primary elements of prime-power norm
(`K3Lean.EisensteinRing`).  The final output is
`FermatRequiredDirichletModels fermatTraceAngle`.
-/

namespace K3Lean.HeckeModels

open Complex Finset Asymptotics Filter
open K3Lean.Eisenstein K3Lean.Eisenstein.Eis
open K3Lean.PrimaryDiskBound
open K3Lean.FermatHasseAngle
open K3Lean.FermatDirichletCriterion
open K3Lean.CanonicalFermatEuler
open K3Lean.HeckeEulerNonvanishing
open K3Lean.ExplicitFermatHecke
open K3Lean.PublishedInputs
open scoped LSeries.notation

noncomputable section

/-! ## The lattice coefficients -/

/-- The Hecke coefficient: the angular sum over primary elements of norm `n`. -/
def heckeCoeff (m : ℕ) (n : ℕ) : ℂ :=
  ∑ α ∈ primaryOfNorm n, u (toC α) ^ m

@[simp] lemma heckeCoeff_zero (m : ℕ) : heckeCoeff m 0 = 0 := by
  simp [heckeCoeff]

@[simp] lemma heckeCoeff_one (m : ℕ) : heckeCoeff m 1 = 1 := by
  simp [heckeCoeff, primaryOfNorm_one, u, map_one]

lemma norm_heckeCoeff_le (m n : ℕ) :
    ‖heckeCoeff m n‖ ≤ (primaryOfNorm n).card := by
  calc ‖heckeCoeff m n‖ ≤ ∑ α ∈ primaryOfNorm n, ‖u (toC α) ^ m‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _α ∈ primaryOfNorm n, 1 := by
        refine Finset.sum_le_sum fun α _ => ?_
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (norm_u_le _)
    _ = (primaryOfNorm n).card := by simp

/-! ## The completely multiplicative pair -/

/-- Extend prime values to a completely multiplicative function. -/
def extendCM (v : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else n.factorization.prod fun p k => v p ^ k

@[simp] lemma extendCM_zero (v : ℕ → ℂ) : extendCM v 0 = 0 := rfl

@[simp] lemma extendCM_one (v : ℕ → ℂ) : extendCM v 1 = 1 := by
  simp [extendCM]

lemma extendCM_mul (v : ℕ → ℂ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    extendCM v (a * b) = extendCM v a * extendCM v b := by
  unfold extendCM
  rw [if_neg (Nat.mul_ne_zero ha hb), if_neg ha, if_neg hb,
    Nat.factorization_mul ha hb]
  exact Finsupp.prod_add_index' (fun p => pow_zero (v p)) (fun p k l => pow_add (v p) k l)

lemma extendCM_prime_pow (v : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    extendCM v (p ^ k) = v p ^ k := by
  unfold extendCM
  rw [if_neg (pow_ne_zero k hp.ne_zero), hp.factorization_pow]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact Finsupp.prod_single_index (pow_zero (v p))

lemma extendCM_prime (v : ℕ → ℂ) {p : ℕ} (hp : p.Prime) :
    extendCM v p = v p := by
  simpa using extendCM_prime_pow v hp 1

lemma norm_extendCM_le_one (v : ℕ → ℂ) (hv : ∀ p, p.Prime → ‖v p‖ ≤ 1) (n : ℕ) :
    ‖extendCM v n‖ ≤ 1 := by
  unfold extendCM
  split_ifs with h
  · simp
  · calc ‖n.factorization.prod fun p k => v p ^ k‖
        = ∏ p ∈ n.factorization.support, ‖v p ^ (n.factorization p)‖ := by
          rw [Finsupp.prod, norm_prod]
      _ ≤ ∏ p ∈ n.factorization.support, 1 := by
          refine Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p hp => ?_
          rw [norm_pow]
          exact pow_le_one₀ (norm_nonneg _)
            (hv p (Nat.prime_of_mem_primeFactors
              (by rwa [Nat.support_factorization] at hp)))
      _ = 1 := Finset.prod_const_one

/-- Prime values of `g`. -/
def gPrime (m : ℕ) (p : ℕ) : ℂ :=
  if p % 3 = 1 then Complex.exp ((((m : ℝ) * fermatTraceAngle p : ℝ)) * Complex.I)
  else if p % 3 = 2 then Complex.I ^ m
  else 0

/-- Prime values of `h`. -/
def hPrime (m : ℕ) (p : ℕ) : ℂ :=
  if p % 3 = 1 then Complex.exp ((-((m : ℝ) * fermatTraceAngle p) : ℝ) * Complex.I)
  else if p % 3 = 2 then -(Complex.I ^ m)
  else 0

lemma norm_exp_real_mul_I (r : ℝ) : ‖Complex.exp ((r : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

lemma norm_gPrime_le (m p : ℕ) : ‖gPrime m p‖ ≤ 1 := by
  unfold gPrime
  split_ifs
  · exact le_of_eq (norm_exp_real_mul_I _)
  · rw [norm_pow, Complex.norm_I, one_pow]
  · simp

lemma norm_hPrime_le (m p : ℕ) : ‖hPrime m p‖ ≤ 1 := by
  unfold hPrime
  split_ifs
  · exact le_of_eq (norm_exp_real_mul_I _)
  · rw [_root_.norm_neg, norm_pow, Complex.norm_I, one_pow]
  · simp

/-- `g = extendCM (gPrime m)`. -/
def g (m : ℕ) : ℕ → ℂ := extendCM (gPrime m)

/-- `h = extendCM (hPrime m)`. -/
def h (m : ℕ) : ℕ → ℂ := extendCM (hPrime m)

lemma norm_g_le_one (m n : ℕ) : ‖g m n‖ ≤ 1 :=
  norm_extendCM_le_one _ (fun p _ => norm_gPrime_le m p) n

lemma norm_h_le_one (m n : ℕ) : ‖h m n‖ ≤ 1 :=
  norm_extendCM_le_one _ (fun p _ => norm_hPrime_le m p) n

lemma g_LSeriesSummable (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (g m) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_g_le_one m n) hs

lemma h_LSeriesSummable (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (h m) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_h_le_one m n) hs

/-! ## The bundled completely multiplicative term function -/

/-- The `LSeries.term` of a completely multiplicative extension, as a
monoid-with-zero homomorphism (for the Euler product machinery). -/
def cmTerm (v : ℕ → ℂ) (s : ℂ) : ℕ →*₀ ℂ where
  toFun := LSeries.term (extendCM v) s
  map_zero' := LSeries.term_zero _ _
  map_one' := by
    rw [LSeries.term_of_ne_zero one_ne_zero]
    simp
  map_mul' a b := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp [LSeries.term_zero]
    rcases eq_or_ne b 0 with rfl | hb
    · simp [LSeries.term_zero]
    have hcast : ((a : ℂ) * (b : ℂ)) ^ s = (a : ℂ) ^ s * (b : ℂ) ^ s := by
      rw [(Complex.ofReal_natCast a).symm, (Complex.ofReal_natCast b).symm,
        mul_cpow_ofReal_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
    rw [LSeries.term_of_ne_zero (Nat.mul_ne_zero ha hb),
      LSeries.term_of_ne_zero ha, LSeries.term_of_ne_zero hb,
      extendCM_mul v ha hb, Nat.cast_mul, hcast, div_mul_div_comm]

lemma cmTerm_apply (v : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    cmTerm v s n = LSeries.term (extendCM v) s n := rfl

lemma summable_norm_cmTerm (v : ℕ → ℂ) (hv : ∀ p, p.Prime → ‖v p‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n => ‖cmTerm v s n‖) := by
  have h1 : LSeriesSummable (extendCM v) s :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (fun n _ => norm_extendCM_le_one v hv n) hs
  simpa [cmTerm_apply] using h1.norm

/-- The completely multiplicative Euler product in exp-log form. -/
lemma LSeries_extendCM_eq_exp (v : ℕ → ℂ) (hv : ∀ p, p.Prime → ‖v p‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (extendCM v) s =
      Complex.exp (∑' p : Nat.Primes,
        -Complex.log (1 - LSeries.term (extendCM v) s p)) := by
  have := EulerProduct.exp_tsum_primes_log_eq_tsum
    (f := cmTerm v s) (summable_norm_cmTerm v hv hs)
  rw [LSeries]
  exact this.symm

/-! ## Identification with the convolution -/

lemma u_conj (z : ℂ) : u ((starRingEnd ℂ) z) = (starRingEnd ℂ) (u z) := by
  unfold u
  rw [map_div₀, RCLike.norm_conj]
  congr 1
  exact (Complex.conj_ofReal _).symm

lemma u_toC_pi_pair {p : ℕ} [Fact p.Prime] (hp : p % 3 = 1) {π : Eis}
    (hπnorm : natNorm π = p)
    (htrace : (fermatFrobeniusTrace p : ℂ) = toC π + toC (Eis.conj π)) :
    (u (toC π) = Complex.exp (((fermatTraceAngle p : ℝ)) * Complex.I) ∧
      u (toC (Eis.conj π)) = Complex.exp ((-(fermatTraceAngle p) : ℝ) * Complex.I)) ∨
    (u (toC π) = Complex.exp ((-(fermatTraceAngle p) : ℝ) * Complex.I) ∧
      u (toC (Eis.conj π)) = Complex.exp (((fermatTraceAngle p : ℝ)) * Complex.I)) := by
  have hpp : p.Prime := Fact.out
  have hz_conj : toC (Eis.conj π) = (starRingEnd ℂ) (toC π) := toC_conj π
  set z := toC π with hz_def
  have hnormz : ‖z‖ = Real.sqrt p := by
    rw [hz_def, norm_toC]
    congr 1
    have hc := natNorm_cast π
    rw [← hc, hπnorm]
    push_cast
    rfl
  have hsp : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hpp.pos)
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, _root_.norm_zero] at hnormz
    exact hsp.ne hnormz
  have hretrace : (fermatFrobeniusTrace p : ℝ) = 2 * z.re := by
    have h := congrArg Complex.re htrace
    rw [hz_conj] at h
    simp only [Complex.add_re, Complex.conj_re, Complex.intCast_re] at h
    rw [h]
    ring
  have hcos : Real.cos z.arg = (fermatFrobeniusTrace p : ℝ) / (2 * Real.sqrt p) := by
    rw [Complex.cos_arg hz0, hnormz, hretrace]
    field_simp
  have hangle_def : fermatTraceAngle p = Real.arccos (Real.cos z.arg) := by
    unfold fermatTraceAngle
    rw [hcos]
  have hu : u z = Complex.exp (z.arg * Complex.I) := by
    have hmod := Complex.norm_mul_exp_arg_mul_I z
    have hne : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (norm_pos_iff.mpr hz0).ne'
    unfold u
    rw [div_eq_iff hne, mul_comm]
    exact hmod.symm
  have huc : u ((starRingEnd ℂ) z) = Complex.exp (-(z.arg) * Complex.I) := by
    rw [u_conj, hu, ← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rcases le_total 0 z.arg with h | h
  · left
    have hangle : fermatTraceAngle p = z.arg := by
      rw [hangle_def]
      exact Real.arccos_cos h (Complex.arg_le_pi z)
    constructor
    · rw [hu, hangle]
    · rw [hz_conj, huc, hangle]
      congr 1
      push_cast
      ring
  · right
    have hangle : fermatTraceAngle p = -z.arg := by
      rw [hangle_def, ← Real.cos_neg]
      exact Real.arccos_cos (by linarith) (by linarith [Complex.neg_pi_lt_arg z])
    constructor
    · rw [hu, hangle]
      congr 1
      push_cast
      ring
    · rw [hz_conj, huc, hangle]
      congr 1
      push_cast
      ring

lemma u_pow (z : ℂ) (n : ℕ) : u (z ^ n) = u z ^ n := by
  induction n with
  | zero =>
    simp [u]
  | succ n ih =>
    rw [pow_succ, u_mul, ih, pow_succ]

/-- Split prime powers: the lattice coefficient agrees with the convolution. -/
theorem heckeCoeff_prime_pow_split (m : ℕ) {p : ℕ} [Fact p.Prime]
    (hp : p % 3 = 1) (k : ℕ) :
    heckeCoeff m (p ^ k) =
      ∑ j ∈ Finset.range (k + 1), gPrime m p ^ j * hPrime m p ^ (k - j) := by
  have hpp : p.Prime := Fact.out
  obtain ⟨π, hπP, hπN, hns, htrace⟩ := K3Lean.CubicJacobi.exists_primary_frobenius p hp
  have hg : gPrime m p
      = Complex.exp ((((m : ℝ) * fermatTraceAngle p : ℝ)) * Complex.I) := by
    unfold gPrime
    rw [if_pos hp]
  have hh : hPrime m p
      = Complex.exp ((-((m : ℝ) * fermatTraceAngle p) : ℝ) * Complex.I) := by
    unfold hPrime
    rw [if_pos hp]
  unfold heckeCoeff
  rw [primaryOfNorm_prime_pow_split hpp hπP hπN hns k,
    Finset.sum_image (prime_pow_split_inj hpp hπP hπN hns k)]
  rcases u_toC_pi_pair hp hπN htrace with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    show u (toC (π ^ j * Eis.conj π ^ (k - j))) ^ m = _
    rw [map_mul, map_pow, map_pow, u_mul, u_pow, u_pow, h1, h2, hg, hh]
    simp only [mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · have hreflect := Finset.sum_range_reflect
      (fun j => gPrime m p ^ j * hPrime m p ^ (k - j)) (k + 1)
    simp only [Nat.add_sub_cancel] at hreflect
    rw [← hreflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    show u (toC (π ^ j * Eis.conj π ^ (k - j))) ^ m = _
    rw [show k - (k - j) = j from by omega]
    rw [map_mul, map_pow, map_pow, u_mul, u_pow, u_pow, h1, h2, hg, hh]
    simp only [mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring

theorem heckeCoeff_prime_pow_inert (m : ℕ) {q : ℕ} [Fact q.Prime]
    (hq : q % 3 = 2) (k : ℕ) :
    heckeCoeff m (q ^ k) =
      ∑ j ∈ Finset.range (k + 1), gPrime m q ^ j * hPrime m q ^ (k - j) := by
  have hqp : q.Prime := Fact.out
  have hg : gPrime m q = Complex.I ^ m := by
    unfold gPrime
    rw [if_neg (by omega), if_pos hq]
  have hh : hPrime m q = -(Complex.I ^ m) := by
    unfold hPrime
    rw [if_neg (by omega), if_pos hq]
  have hRHS : ∑ j ∈ Finset.range (k + 1), gPrime m q ^ j * hPrime m q ^ (k - j)
      = (Complex.I ^ m) ^ k * ∑ j ∈ Finset.range (k + 1), (-1 : ℂ) ^ (k - j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [hg, hh, neg_pow]
    calc (Complex.I ^ m) ^ j * ((-1 : ℂ) ^ (k - j) * (Complex.I ^ m) ^ (k - j))
        = ((Complex.I ^ m) ^ j * (Complex.I ^ m) ^ (k - j)) * (-1 : ℂ) ^ (k - j) := by
          ring
      _ = (Complex.I ^ m) ^ k * (-1 : ℂ) ^ (k - j) := by
          rw [← pow_add, show j + (k - j) = k from by omega]
  have hALT : ∑ j ∈ Finset.range (k + 1), (-1 : ℂ) ^ (k - j)
      = if Even (k + 1) then 0 else 1 := by
    have h := Finset.sum_range_reflect (fun j => (-1 : ℂ) ^ j) (k + 1)
    simp only [Nat.add_sub_cancel] at h
    rw [h, neg_one_geom_sum]
  unfold heckeCoeff
  rw [primaryOfNorm_prime_pow_inert hqp hq k, hRHS, hALT]
  rcases Nat.even_or_odd k with hk | hk
  · obtain ⟨j, hj⟩ := hk
    have hk2 : 2 ∣ k := ⟨j, by omega⟩
    have hnot : ¬ Even (k + 1) := by
      rw [Nat.even_add_one]
      exact not_not_intro ⟨j, hj⟩
    have hdiv : k / 2 = j := by omega
    rw [if_pos hk2, if_neg hnot, mul_one, Finset.sum_singleton, hdiv]
    have htoC : toC ((-1) ^ j * (q : Eis) ^ j)
        = (-1 : ℂ) ^ j * (((q : ℝ) ^ j : ℝ) : ℂ) := by
      rw [map_mul, map_pow, map_pow, map_neg, map_one, map_natCast]
      push_cast
      ring
    rw [htoC, u_mul]
    have hu1 : u ((-1 : ℂ) ^ j) = (-1 : ℂ) ^ j := by
      unfold u
      have h1 : ‖(-1 : ℂ) ^ j‖ = 1 := by
        rw [norm_pow]
        simp
      rw [h1]
      push_cast
      rw [div_one]
    have hq0 : (0 : ℝ) < (q : ℝ) ^ j := by
      have := hqp.pos
      positivity
    have hone : u (1 : ℂ) = 1 := by
      unfold u
      simp
    have hu2 : u (((q : ℝ) ^ j : ℝ) : ℂ) = 1 := by
      have h1 : (((q : ℝ) ^ j : ℝ) : ℂ) = ((q : ℝ) ^ j : ℝ) * (1 : ℂ) := by
        ring
      rw [h1, u_smul_pos hq0, hone]
    rw [hu1, hu2, mul_one, ← pow_mul, ← pow_mul,
      show m * k = 2 * (j * m) from by rw [hj]; ring,
      pow_mul Complex.I 2 (j * m), Complex.I_sq]
  · have hk2 : ¬ (2 ∣ k) := by
      obtain ⟨b, hb⟩ := hk
      omega
    have heven : Even (k + 1) := by
      rw [Nat.even_add_one]
      intro hE
      obtain ⟨r, hr⟩ := hE
      obtain ⟨b, hb⟩ := hk
      omega
    rw [if_neg hk2, if_pos heven, Finset.sum_empty, mul_zero]

theorem heckeCoeff_prime_pow_three (m : ℕ) (k : ℕ) (hk : k ≠ 0) :
    heckeCoeff m (3 ^ k) = 0 := by
  have h := primaryOfNorm_three_pow hk
  simp [heckeCoeff, h]

/-- `heckeCoeff m` is multiplicative on coprime arguments. -/
theorem heckeCoeff_mul_coprime (m : ℕ) {a b : ℕ} (hab : Nat.Coprime a b) :
    heckeCoeff m (a * b) = heckeCoeff m a * heckeCoeff m b := by
  unfold heckeCoeff
  rw [primaryOfNorm_mul_coprime hab,
    Finset.sum_image (fun x hx y hy hxy =>
      primaryOfNorm_mul_coprime_inj hab (by exact_mod_cast hx) (by exact_mod_cast hy) hxy),
    Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  refine Finset.sum_congr rfl fun γ _ => ?_
  show u (toC (β * γ)) ^ m = u (toC β) ^ m * u (toC γ) ^ m
  rw [map_mul, u_mul, mul_pow]

lemma toAF_apply (f : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    toArithmeticFunction f n = f n := by
  simp [toArithmeticFunction, hn]

lemma toAF_extendCM_isMultiplicative (v : ℕ → ℂ) :
    (toArithmeticFunction (extendCM v)).IsMultiplicative := by
  constructor
  · rw [toAF_apply _ one_ne_zero]
    exact extendCM_one v
  · intro a b hab
    rcases eq_or_ne a 0 with rfl | ha
    · rw [Nat.coprime_zero_left] at hab
      subst hab
      simp
    rcases eq_or_ne b 0 with rfl | hb
    · rw [Nat.coprime_zero_right] at hab
      subst hab
      simp
    rw [toAF_apply _ (Nat.mul_ne_zero ha hb), toAF_apply _ ha, toAF_apply _ hb]
    exact extendCM_mul v ha hb

/-- `heckeCoeff m` is the Dirichlet convolution of `g m` and `h m`. -/
theorem heckeCoeff_eq_convolution (m : ℕ) (n : ℕ) :
    heckeCoeff m n = ((g m) ⍟ (h m)) n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero =>
    rw [heckeCoeff_zero, LSeries.convolution_map_zero]
  | one =>
    rw [heckeCoeff_one]
    simp only [LSeries.convolution_def, Nat.divisorsAntidiagonal_one,
      Finset.sum_singleton]
    rw [show (g m) 1 = 1 from extendCM_one _,
      show (h m) 1 = 1 from extendCM_one _, mul_one]
  | prime_pow p k hp hk =>
    have hpp : p.Prime := hp
    have hRHS : ((g m) ⍟ (h m)) (p ^ k)
        = ∑ j ∈ Finset.range (k + 1), gPrime m p ^ j * hPrime m p ^ (k - j) := by
      rw [LSeries.convolution_def]
      show ∑ i ∈ (p ^ k).divisorsAntidiagonal, (g m) i.1 * (h m) i.2 = _
      rw [Nat.sum_divisorsAntidiagonal (fun x y => (g m) x * (h m) y),
        Nat.sum_divisors_prime_pow hpp]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      have hdiv : p ^ k / p ^ j = p ^ (k - j) := by
        rw [Nat.pow_div (by omega) hpp.pos]
      rw [hdiv]
      show extendCM (gPrime m) (p ^ j) * extendCM (hPrime m) (p ^ (k - j)) = _
      rw [extendCM_prime_pow _ hpp, extendCM_prime_pow _ hpp]
    rw [hRHS]
    have h3 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases h3 with h3 | h3 | h3
    · have hp3 : p = 3 := by
        have hdvd : (3 : ℕ) ∣ p := by omega
        rcases hpp.eq_one_or_self_of_dvd 3 hdvd with h' | h'
        · norm_num at h'
        · omega
      subst hp3
      rw [heckeCoeff_prime_pow_three m k (by omega)]
      symm
      refine Finset.sum_eq_zero fun j hj => ?_
      have hg3 : gPrime m 3 = 0 := by
        unfold gPrime
        norm_num
      have hh3 : hPrime m 3 = 0 := by
        unfold hPrime
        norm_num
      rw [hg3, hh3]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [pow_zero, one_mul, zero_pow (by omega : k - 0 ≠ 0)]
      · rw [zero_pow (by omega : j ≠ 0), zero_mul]
    · have : Fact p.Prime := ⟨hpp⟩
      exact heckeCoeff_prime_pow_split m h3 k
    · have : Fact p.Prime := ⟨hpp⟩
      exact heckeCoeff_prime_pow_inert m h3 k
  | coprime a b ha hb hab iha ihb =>
    rw [heckeCoeff_mul_coprime m hab, iha, ihb]
    show (g m ⍟ h m) a * (g m ⍟ h m) b
      = (⇑(toArithmeticFunction (extendCM (gPrime m))
          * toArithmeticFunction (extendCM (hPrime m))) : ℕ → ℂ) (a * b)
    rw [((toAF_extendCM_isMultiplicative (gPrime m)).mul
      (toAF_extendCM_isMultiplicative (hPrime m))).map_mul_of_coprime hab]
    rfl

/-! ## L-series facts -/

set_option maxHeartbeats 1000000 in
theorem heckeCoeff_LSeriesSummable (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (heckeCoeff m) s := by
  have hconv := (g_LSeriesSummable m hs).convolution (h_LSeriesSummable m hs)
  unfold LSeriesSummable at hconv ⊢
  refine hconv.congr fun n => ?_
  unfold LSeries.term
  split_ifs with h
  · rfl
  · rw [heckeCoeff_eq_convolution]

theorem heckeCoeff_partial_sum_sqrt (m : ℕ) (hm : ¬ (3 ∣ m)) :
    K3Lean.AbelMellinContinuation.PartialSumBigO (heckeCoeff m) (1 / 2 : ℝ) := by
  unfold K3Lean.AbelMellinContinuation.PartialSumBigO
  have h := primary_sum_isBigO m hm
  refine h.congr_left fun N => ?_
  unfold heckeCoeff
  rfl

lemma cmTerm_prime (v : ℕ → ℂ) (s : ℂ) {p : ℕ} (hp : p.Prime) :
    cmTerm v s p = v p / (p : ℂ) ^ s := by
  show LSeries.term (extendCM v) s p = _
  rw [LSeries.term_of_ne_zero hp.pos.ne', extendCM_prime v hp]

lemma natCast_cpow_eq_exp {p : ℕ} (hp : p.Prime) (s : ℂ) :
    (p : ℂ) ^ s = Complex.exp (s * (Real.log p : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hp.pos.ne'), ← Complex.natCast_log,
    mul_comm]

lemma norm_exp_lt_one_of_re_neg {w : ℂ} (hw : w.re < 0) : ‖Complex.exp w‖ < 1 := by
  rw [Complex.norm_exp]
  exact Real.exp_lt_one_iff.mpr hw

/-- `-log(1-X) - log(1+X) = -log(1-X^2)` for `‖X‖ < 1`. -/
lemma neg_log_one_sub_add_neg_log_one_add {X : ℂ} (hX : ‖X‖ < 1) :
    -Complex.log (1 - X) + -Complex.log (1 + X) = -Complex.log (1 - X ^ 2) := by
  have hre1 : 0 < (1 - X).re := by
    have := Complex.abs_re_le_norm X
    simp only [Complex.sub_re, Complex.one_re]
    have h1 : |X.re| ≤ ‖X‖ := Complex.abs_re_le_norm X
    have h2 : X.re ≤ ‖X‖ := le_trans (le_abs_self _) h1
    linarith
  have hre2 : 0 < (1 + X).re := by
    simp only [Complex.add_re, Complex.one_re]
    have h1 : |X.re| ≤ ‖X‖ := Complex.abs_re_le_norm X
    have h2 : -X.re ≤ ‖X‖ := le_trans (neg_le_abs _) h1
    linarith
  have h10 : (1 - X) ≠ 0 := by
    intro h0
    rw [sub_eq_zero] at h0
    rw [← h0] at hX
    simp at hX
  have h20 : (1 + X) ≠ 0 := by
    intro h0
    have : X = -1 := by linear_combination h0
    rw [this] at hX
    simp at hX
  have harg1 : |Complex.arg (1 - X)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre1)
  have harg2 : |Complex.arg (1 + X)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre2)
  have hmul : Complex.log ((1 - X) * (1 + X))
      = Complex.log (1 - X) + Complex.log (1 + X) := by
    apply Complex.log_mul h10 h20
    constructor
    · have := abs_lt.mp harg1
      have := abs_lt.mp harg2
      linarith
    · have := abs_lt.mp harg1
      have := abs_lt.mp harg2
      have hpi : 0 < Real.pi := Real.pi_pos
      linarith
  have hfactor : (1 - X) * (1 + X) = 1 - X ^ 2 := by ring
  rw [← neg_add, ← hmul, hfactor]

/-- The Euler identification: on `re s > 1` the L-series of `heckeCoeff m`
equals the explicit Fermat Euler product. -/
theorem heckeCoeff_LSeries_eq (m : ℕ) (hm : ¬ (3 ∣ m)) {s : ℂ} (hs : 1 < s.re) :
    LSeries (heckeCoeff m) s = explicitFermatPowerL fermatTraceAngle m s := by
  have hx : 0 < s.re - 1 := by linarith
  have h1 : LSeries (heckeCoeff m) s = LSeries (g m) s * LSeries (h m) s := by
    have he : LSeries (heckeCoeff m) = LSeries ((g m) ⍟ (h m)) :=
      congrArg _ (funext (heckeCoeff_eq_convolution m))
    rw [he, LSeries_convolution' (g_LSeriesSummable m hs) (h_LSeriesSummable m hs)]
  have hgsum := summable_norm_cmTerm (gPrime m) (fun p _ => norm_gPrime_le m p) hs
  have hhsum := summable_norm_cmTerm (hPrime m) (fun p _ => norm_hPrime_le m p) hs
  have hg2 : LSeries (g m) s
      = Complex.exp (∑' p : Nat.Primes,
          -Complex.log (1 - cmTerm (gPrime m) s p)) :=
    (EulerProduct.exp_tsum_primes_log_eq_tsum hgsum).symm
  have hh2 : LSeries (h m) s
      = Complex.exp (∑' p : Nat.Primes,
          -Complex.log (1 - cmTerm (hPrime m) s p)) :=
    (EulerProduct.exp_tsum_primes_log_eq_tsum hhsum).symm
  rw [h1, hg2, hh2, ← Complex.exp_add]
  unfold explicitFermatPowerL
  congr 1
  -- Reindex the slot sum to primes × Fin 2.
  set F : FermatEulerSlot → ℂ := fun q =>
    -Complex.log
      (1 - (fermatEulerRadius (s.re - 1) q : ℂ) *
        fermatEulerLocalValue fermatTraceAngle m s.im q) with hF_def
  have hFsum : Summable F :=
    summable_fermatEulerPowerLog fermatTraceAngle m s.im (s.re - 1) hx
  have hF_nonprime : ∀ q : FermatEulerSlot, ¬ q.1.Prime → F q = 0 := by
    intro q hq
    rw [hF_def]
    simp only [fermatEulerRadius, dif_neg hq, Complex.ofReal_zero, zero_mul,
      sub_zero, Complex.log_one, neg_zero]
  set e : Nat.Primes × Fin 2 → FermatEulerSlot := fun pi => ((pi.1 : ℕ), pi.2)
    with he_def
  have he_inj : Function.Injective e := by
    rintro ⟨⟨p₁, hp₁⟩, i₁⟩ ⟨⟨p₂, hp₂⟩, i₂⟩ hpe
    simp only [he_def, Prod.mk.injEq] at hpe
    obtain ⟨h1', h2'⟩ := hpe
    exact Prod.ext (Subtype.ext h1') h2'
  have he_supp : Function.support F ⊆ Set.range e := by
    intro q hq
    rcases q with ⟨n, i⟩
    by_cases hn : n.Prime
    · exact ⟨(⟨n, hn⟩, i), rfl⟩
    · exact absurd (hF_nonprime (n, i) hn) hq
  have hslot : ∑' q : FermatEulerSlot, F q = ∑' pi : Nat.Primes × Fin 2, F (e pi) :=
    (he_inj.tsum_eq he_supp).symm
  have hFe : Summable (F ∘ e) := hFsum.comp_injective he_inj
  have hprod : ∑' pi : Nat.Primes × Fin 2, F (e pi)
      = ∑' p : Nat.Primes, (F ((p : ℕ), 0) + F ((p : ℕ), 1)) := by
    rw [show (fun pi : Nat.Primes × Fin 2 => F (e pi)) = F ∘ e from rfl]
    rw [hFe.tsum_prod' (fun b => Summable.of_finite)]
    refine tsum_congr fun p => ?_
    rw [tsum_fintype, Fin.sum_univ_two]
    rfl
  rw [hslot, hprod]
  -- Combine the two prime sums on the left.
  have hAsum : Summable (fun p : Nat.Primes =>
      -Complex.log (1 - cmTerm (gPrime m) s p)) :=
    (hgsum.of_norm.clog_one_sub.neg).comp_injective Subtype.coe_injective
  have hBsum : Summable (fun p : Nat.Primes =>
      -Complex.log (1 - cmTerm (hPrime m) s p)) :=
    (hhsum.of_norm.clog_one_sub.neg).comp_injective Subtype.coe_injective
  rw [← hAsum.tsum_add hBsum]
  refine tsum_congr fun p => ?_
  obtain ⟨P, hP⟩ := p
  simp only
  -- Per-prime case analysis.
  have hlogP : 0 < Real.log P := Real.log_pos (by exact_mod_cast hP.one_lt)
  have h3 : P % 3 = 0 ∨ P % 3 = 1 ∨ P % 3 = 2 := by omega
  rcases h3 with h3 | h3 | h3
  · -- P = 3: everything vanishes.
    have hg0 : gPrime m P = 0 := by
      unfold gPrime
      rw [if_neg (by omega), if_neg (by omega)]
    have hh0 : hPrime m P = 0 := by
      unfold hPrime
      rw [if_neg (by omega), if_neg (by omega)]
    have hrad : ∀ i : Fin 2, fermatEulerRadius (s.re - 1) (P, i) = 0 := by
      intro i
      unfold fermatEulerRadius
      rw [dif_pos hP, dif_neg (by omega : ¬ P % 3 = 1),
        dif_neg (fun hcon => by omega : ¬ (P % 3 = 2 ∧ i = 0))]
    have hFP : ∀ i : Fin 2, F (P, i) = 0 := by
      intro i
      rw [hF_def]
      simp only [hrad i, Complex.ofReal_zero, zero_mul, sub_zero,
        Complex.log_one, neg_zero]
    rw [cmTerm_prime _ _ hP, cmTerm_prime _ _ hP, hg0, hh0, zero_div]
    rw [hFP 0, hFP 1]
    simp [Complex.log_one]
  · -- split prime
    have hgP : gPrime m P
        = Complex.exp ((((m : ℝ) * fermatTraceAngle P : ℝ)) * Complex.I) := by
      unfold gPrime
      rw [if_pos h3]
    have hhP : hPrime m P
        = Complex.exp ((-((m : ℝ) * fermatTraceAngle P) : ℝ) * Complex.I) := by
      unfold hPrime
      rw [if_pos h3]
    have hXg : cmTerm (gPrime m) s P
        = (fermatEulerRadius (s.re - 1) (P, 0) : ℂ) *
            fermatEulerLocalValue fermatTraceAngle m s.im (P, 0) := by
      rw [cmTerm_prime _ _ hP, hgP, natCast_cpow_eq_exp hP, ← Complex.exp_sub]
      unfold fermatEulerRadius fermatEulerLocalValue
      rw [dif_pos hP, dif_pos h3, dif_pos hP, dif_pos h3, if_pos rfl,
        Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      apply Complex.ext <;>
        simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im] <;> ring
    have hXh : cmTerm (hPrime m) s P
        = (fermatEulerRadius (s.re - 1) (P, 1) : ℂ) *
            fermatEulerLocalValue fermatTraceAngle m s.im (P, 1) := by
      rw [cmTerm_prime _ _ hP, hhP, natCast_cpow_eq_exp hP, ← Complex.exp_sub]
      unfold fermatEulerRadius fermatEulerLocalValue
      rw [dif_pos hP, dif_pos h3, dif_pos hP, dif_pos h3,
        if_neg (by decide : ¬ ((1 : Fin 2) = 0)),
        Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      apply Complex.ext <;>
        simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im] <;> ring
    rw [hF_def]
    simp only
    rw [← hXg, ← hXh]
  · -- inert prime
    set X : ℂ := Complex.I ^ m * Complex.exp (-(s * (Real.log P : ℂ))) with hX_def
    have hXnorm : ‖X‖ < 1 := by
      rw [hX_def, _root_.norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
      apply norm_exp_lt_one_of_re_neg
      rw [show -(s * (Real.log P : ℂ)) = (-s) * (Real.log P : ℂ) from by ring]
      rw [Complex.mul_re]
      simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
        mul_zero, sub_zero]
      nlinarith
    have hgP : gPrime m P = Complex.I ^ m := by
      unfold gPrime
      rw [if_neg (by omega), if_pos h3]
    have hhP : hPrime m P = -(Complex.I ^ m) := by
      unfold hPrime
      rw [if_neg (by omega), if_pos h3]
    have hXg : cmTerm (gPrime m) s P = X := by
      rw [cmTerm_prime _ _ hP, hgP, natCast_cpow_eq_exp hP, hX_def,
        div_eq_mul_inv, ← Complex.exp_neg]
    have hXh : cmTerm (hPrime m) s P = -X := by
      rw [cmTerm_prime _ _ hP, hhP, natCast_cpow_eq_exp hP, hX_def, neg_div,
        div_eq_mul_inv, ← Complex.exp_neg]
    have hrad0 : fermatEulerRadius (s.re - 1) (P, 0)
        = Real.exp (-2 * (1 + (s.re - 1)) * Real.log P) := by
      unfold fermatEulerRadius
      rw [dif_pos hP, dif_neg (by omega : ¬ P % 3 = 1),
        dif_pos (⟨h3, rfl⟩ : P % 3 = 2 ∧ (0 : Fin 2) = 0)]
    have hloc0 : fermatEulerLocalValue fermatTraceAngle m s.im (P, 0)
        = (-1 : ℂ) ^ m * Complex.exp ((-2 * s.im * Real.log P : ℝ) * Complex.I) := by
      unfold fermatEulerLocalValue
      rw [dif_pos hP, dif_neg (by omega : ¬ P % 3 = 1),
        dif_pos (⟨h3, rfl⟩ : P % 3 = 2 ∧ (0 : Fin 2) = 0)]
    have hval0 : ((fermatEulerRadius (s.re - 1) (P, 0) : ℝ) : ℂ) *
        fermatEulerLocalValue fermatTraceAngle m s.im (P, 0) = X ^ 2 := by
      rw [hrad0, hloc0, hX_def, Complex.ofReal_exp, mul_pow, ← pow_mul,
        show m * 2 = 2 * m from by ring, pow_mul, Complex.I_sq,
        mul_left_comm, pow_two, ← Complex.exp_add, ← Complex.exp_add]
      congr 2
      apply Complex.ext <;>
        simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.neg_re, Complex.neg_im] <;> ring
    have hF0 : F (P, 0) = -Complex.log (1 - X ^ 2) := by
      rw [hF_def]
      simp only
      rw [hval0]
    have hF1 : F (P, 1) = 0 := by
      have hrad1 : fermatEulerRadius (s.re - 1) (P, 1) = 0 := by
        unfold fermatEulerRadius
        rw [dif_pos hP, dif_neg (by omega : ¬ P % 3 = 1),
          dif_neg (fun hcon => absurd hcon.2 (by decide : ¬ ((1 : Fin 2) = 0)))]
      rw [hF_def]
      simp only [hrad1, Complex.ofReal_zero, zero_mul, sub_zero,
        Complex.log_one, neg_zero]
    rw [hXg, hXh, hF0, hF1, add_zero, sub_neg_eq_add]
    exact neg_log_one_sub_add_neg_log_one_add hXnorm

/-! ## The models -/

theorem fermatRequiredDirichletModels :
    FermatRequiredDirichletModels fermatTraceAngle := by
  intro m hm
  have hm3 : ¬ (3 ∣ m) := by
    rcases hm with rfl | rfl | rfl <;> decide
  exact ⟨{ coeff := heckeCoeff m
           partial_sum_sqrt := heckeCoeff_partial_sum_sqrt m hm3
           summable_gt_one := fun s hs => heckeCoeff_LSeriesSummable m hs
           euler_eq := fun s hs => heckeCoeff_LSeries_eq m hm3 hs }⟩

end

end K3Lean.HeckeModels
