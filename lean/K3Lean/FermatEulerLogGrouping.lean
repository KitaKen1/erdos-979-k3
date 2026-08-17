import K3Lean.ExplicitFermatHecke
import Mathlib.NumberTheory.LSeries.PrimesInAP

namespace K3Lean.ExplicitFermatHecke


open Complex Filter
open scoped Topology

noncomputable section

def fermatEulerTaylorTerm
    (theta : Nat -> Real) (m : Nat) (t x : Real)
    (qk : FermatEulerSlot × Nat) : Complex :=
  (((fermatEulerRadius x qk.1 : Real) : Complex) *
      fermatEulerLocalValue theta m t qk.1) ^ (qk.2 + 1) /
    ((qk.2 + 1 : Nat) : Complex)

theorem fermatEulerTaylorTerm_hasSum
    (theta : Nat -> Real) (m : Nat) (t x : Real) (hx : 0 < x)
    (q : FermatEulerSlot) :
    HasSum
      (fun k : Nat => fermatEulerTaylorTerm theta m t x (q, k))
      (-Complex.log
        (1 - (fermatEulerRadius x q : Complex) *
          fermatEulerLocalValue theta m t q)) := by
  let z : Complex :=
    (fermatEulerRadius x q : Complex) *
      fermatEulerLocalValue theta m t q
  have hz : ‖z‖ < 1 := by
    calc
      ‖z‖ <= fermatEulerRadius x q := by
        simp only [z, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (fermatEulerRadius_nonneg x hx q)]
        exact mul_le_of_le_one_right
          (fermatEulerRadius_nonneg x hx q)
          (fermatEulerLocalValue_norm_le_one theta m t q)
      _ < 1 := fermatEulerRadius_lt_one x hx q
  have h := Complex.hasSum_taylorSeries_neg_log hz
  rw [← hasSum_nat_add_iff' 1] at h
  simpa [fermatEulerTaylorTerm, z] using h

def fermatPrimeFactor (p : Nat) (x t : Real) : Complex :=
  (p : Complex) ^ (-(1 + (x : Complex) + Complex.I * (t : Complex)))

theorem fermatPrimeFactor_eq
    (p : Nat) (hp : Nat.Prime p) (x t : Real) :
    fermatPrimeFactor p x t =
      (Real.exp (-(1 + x) * Real.log p) : Complex) *
        Complex.exp ((-t * Real.log p : Real) * Complex.I) := by
  rw [fermatPrimeFactor, Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne_zero)]
  rw [← Complex.natCast_log, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem fermatEuler_split_slot_zero
    (theta : Nat -> Real) (m p : Nat) (t x : Real)
    (hp : Nat.Prime p) (hSplit : p % 3 = 1) :
    (fermatEulerRadius x (p, (0 : Fin 2)) : Complex) *
        fermatEulerLocalValue theta m t (p, (0 : Fin 2)) =
      fermatPrimeFactor p x t *
        Complex.exp (((m : Real) * theta p) * Complex.I) := by
  rw [fermatPrimeFactor_eq p hp]
  simp only [fermatEulerRadius, fermatEulerLocalValue, hp, hSplit,
    dite_true, if_pos, Fin.isValue]
  rw [mul_assoc, ← Complex.exp_add]
  congr 1
  apply congrArg Complex.exp
  push_cast
  ring

theorem fermatEuler_split_slot_one
    (theta : Nat -> Real) (m p : Nat) (t x : Real)
    (hp : Nat.Prime p) (hSplit : p % 3 = 1) :
    (fermatEulerRadius x (p, (1 : Fin 2)) : Complex) *
        fermatEulerLocalValue theta m t (p, (1 : Fin 2)) =
      fermatPrimeFactor p x t *
        Complex.exp ((-(m : Real) * theta p) * Complex.I) := by
  rw [fermatPrimeFactor_eq p hp]
  simp only [fermatEulerRadius, fermatEulerLocalValue, hp, hSplit,
    dite_true, if_pos, Fin.isValue, one_ne_zero, if_false]
  rw [mul_assoc, ← Complex.exp_add]
  congr 1
  apply congrArg Complex.exp
  push_cast
  ring

theorem fermatEuler_inert_slot_zero
    (theta : Nat -> Real) (m p : Nat) (t x : Real)
    (hp : Nat.Prime p) (hNotSplit : p % 3 ≠ 1)
    (hInert : p % 3 = 2) :
    (fermatEulerRadius x (p, (0 : Fin 2)) : Complex) *
        fermatEulerLocalValue theta m t (p, (0 : Fin 2)) =
      (-1 : Complex) ^ m * (fermatPrimeFactor p x t) ^ 2 := by
  rw [fermatPrimeFactor_eq p hp]
  simp [fermatEulerRadius, fermatEulerLocalValue, hp, hInert]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 1
  rw [mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  ring

theorem fermatEuler_inert_slot_one
    (theta : Nat -> Real) (m p : Nat) (t x : Real)
    (hp : Nat.Prime p) (hNotSplit : p % 3 ≠ 1) :
    (fermatEulerRadius x (p, (1 : Fin 2)) : Complex) *
        fermatEulerLocalValue theta m t (p, (1 : Fin 2)) = 0 := by
  simp [fermatEulerRadius, fermatEulerLocalValue, hp, hNotSplit]

theorem primePowerExponent_prime_pow
    (p r : Nat) (hp : Nat.Prime p) (hr : 0 < r) :
    primePowerExponent (p ^ r) = r := by
  simp [primePowerExponent, hp.pow_minFac hr.ne', Nat.factorization_pow, hp]

theorem fermatHeckeCoefficient_prime_pow
    (theta : Nat -> Real) (m p r : Nat)
    (hp : Nat.Prime p) (hr : 0 < r) :
    fermatHeckeCoefficient theta m (p ^ r) =
      if p % 3 = 1 then
        Real.cos (((m * r : Nat) : Real) * theta p)
      else if p % 3 = 2 ∧ Even r then
        (-1 : Real) ^ (m * (r / 2)) else 0 := by
  have hpp : IsPrimePow (p ^ r) :=
    ⟨p, r, Nat.prime_iff.mp hp, hr, rfl⟩
  rw [fermatHeckeCoefficient, dif_pos hpp]
  simp only [hp.pow_minFac hr.ne', primePowerExponent_prime_pow p r hp hr]

theorem fermatHeckeEulerLogCoefficient_prime_pow
    (theta : Nat -> Real) (m p r : Nat)
    (hp : Nat.Prime p) (hr : 0 < r) :
    fermatHeckeEulerLogCoefficient theta m (p ^ r) =
      (((2 : Real) / r) *
        (if p % 3 = 1 then
          Real.cos (((m * r : Nat) : Real) * theta p)
        else if p % 3 = 2 ∧ Even r then
          (-1 : Real) ^ (m * (r / 2)) else 0) : Real) := by
  have hpp : IsPrimePow (p ^ r) :=
    ⟨p, r, Nat.prime_iff.mp hp, hr, rfl⟩
  rw [fermatHeckeEulerLogCoefficient, dif_pos hpp,
    primePowerExponent_prime_pow p r hp hr,
    fermatHeckeCoefficient_prime_pow theta m p r hp hr]

theorem fermatEulerLog_LSeriesTerm_prime_pow
    (theta : Nat -> Real) (m p r : Nat) (x t : Real)
    (hp : Nat.Prime p) (hr : 0 < r) :
    LSeries.term (fermatHeckeEulerLogCoefficient theta m)
        (1 + (x : Complex) + Complex.I * (t : Complex)) (p ^ r) =
      fermatHeckeEulerLogCoefficient theta m (p ^ r) *
        (fermatPrimeFactor p x t) ^ r := by
  rw [LSeries.term_of_ne_zero (pow_ne_zero r hp.ne_zero)]
  rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
  rw [div_eq_mul_inv, ← Complex.cpow_neg, fermatPrimeFactor,
    ← Complex.cpow_mul_nat]
  congr 2
  ring

theorem fermatEuler_split_taylor_sum_eq_LSeriesTerm
    (theta : Nat -> Real) (m p k : Nat) (x t : Real)
    (hp : Nat.Prime p) (hSplit : p % 3 = 1) :
    fermatEulerTaylorTerm theta m t x ((p, (0 : Fin 2)), k) +
        fermatEulerTaylorTerm theta m t x ((p, (1 : Fin 2)), k) =
      LSeries.term (fermatHeckeEulerLogCoefficient theta m)
        (1 + (x : Complex) + Complex.I * (t : Complex)) (p ^ (k + 1)) := by
  let r : Nat := k + 1
  let a : Real := ((m * r : Nat) : Real) * theta p
  let w : Complex := fermatPrimeFactor p x t
  have hr : 0 < r := by simp [r]
  have hrC : (r : Complex) ≠ 0 := by exact_mod_cast hr.ne'
  have hExp0 :
      Complex.exp (((m : Real) * theta p) * Complex.I) ^ r =
        Complex.exp ((a : Complex) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    simp only [a]
    push_cast
    ring
  have hExp1 :
      Complex.exp ((-(m : Real) * theta p) * Complex.I) ^ r =
        Complex.exp (-(a : Complex) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    simp only [a]
    push_cast
    ring
  have hEuler :
      Complex.exp ((a : Complex) * Complex.I) +
          Complex.exp (-(a : Complex) * Complex.I) =
        (2 : Complex) * (Real.cos a : Complex) := by
    rw [Complex.ofReal_cos]
    exact (Complex.two_cos (a : Complex)).symm
  simp only [fermatEulerTaylorTerm]
  rw [fermatEuler_split_slot_zero theta m p t x hp hSplit,
    fermatEuler_split_slot_one theta m p t x hp hSplit,
    fermatEulerLog_LSeriesTerm_prime_pow theta m p r x t hp hr,
    fermatHeckeEulerLogCoefficient_prime_pow theta m p r hp hr,
    if_pos hSplit]
  change (w * Complex.exp (((m : Real) * theta p) * Complex.I)) ^ r / r +
      (w * Complex.exp ((-(m : Real) * theta p) * Complex.I)) ^ r / r =
    ((((2 : Real) / r) * Real.cos a : Real) : Complex) * w ^ r
  rw [mul_pow, mul_pow, hExp0, hExp1]
  rw [← add_div, ← mul_add, hEuler]
  push_cast
  field_simp [hrC]

def fermatLocalEulerLog
    (theta : Nat -> Real) (m : Nat) (t x : Real)
    (q : FermatEulerSlot) : Complex :=
  -Complex.log
    (1 - (fermatEulerRadius x q : Complex) *
      fermatEulerLocalValue theta m t q)

def fermatPrimeEulerLog
    (theta : Nat -> Real) (m : Nat) (t x : Real) (p : Nat) : Complex :=
  fermatLocalEulerLog theta m t x (p, (0 : Fin 2)) +
    fermatLocalEulerLog theta m t x (p, (1 : Fin 2))

theorem fermat_split_primeEulerLog_eq
    (theta : Nat -> Real) (m p : Nat) (t x : Real)
    (hx : 0 < x) (hp : Nat.Prime p) (hSplit : p % 3 = 1) :
    fermatPrimeEulerLog theta m t x p =
      ∑' k : Nat,
        LSeries.term (fermatHeckeEulerLogCoefficient theta m)
          (1 + (x : Complex) + Complex.I * (t : Complex)) (p ^ (k + 1)) := by
  have h0 := fermatEulerTaylorTerm_hasSum theta m t x hx
    (p, (0 : Fin 2))
  have h1 := fermatEulerTaylorTerm_hasSum theta m t x hx
    (p, (1 : Fin 2))
  have hsum :
      HasSum
        (fun k : Nat =>
          fermatEulerTaylorTerm theta m t x ((p, (0 : Fin 2)), k) +
            fermatEulerTaylorTerm theta m t x ((p, (1 : Fin 2)), k))
        (fermatPrimeEulerLog theta m t x p) := by
    simpa [fermatPrimeEulerLog, fermatLocalEulerLog] using h0.add h1
  have hseries :
      HasSum
        (fun k : Nat =>
          LSeries.term (fermatHeckeEulerLogCoefficient theta m)
            (1 + (x : Complex) + Complex.I * (t : Complex)) (p ^ (k + 1)))
        (fermatPrimeEulerLog theta m t x p) :=
    hsum.congr_fun (fun k =>
      (fermatEuler_split_taylor_sum_eq_LSeriesTerm theta m p k x t hp hSplit).symm)
  exact hseries.tsum_eq.symm

theorem fermat_inert_taylor_eq_LSeriesTerm
    (theta : Nat -> Real) (m p l : Nat) (x t : Real)
    (hp : Nat.Prime p) (hNotSplit : p % 3 ≠ 1) (hInert : p % 3 = 2) :
    fermatEulerTaylorTerm theta m t x ((p, (0 : Fin 2)), l) =
      LSeries.term (fermatHeckeEulerLogCoefficient theta m)
        (1 + (x : Complex) + Complex.I * (t : Complex))
        (p ^ ((2 * l + 1) + 1)) := by
  let r0 : Nat := l + 1
  let r : Nat := 2 * r0
  let w : Complex := fermatPrimeFactor p x t
  have hr0 : 0 < r0 := by simp [r0]
  have hr : 0 < r := by simp [r, hr0]
  have hr0C : (r0 : Complex) ≠ 0 := by exact_mod_cast hr0.ne'
  have hr0R : (r0 : Real) ≠ 0 := by exact_mod_cast hr0.ne'
  have hEven : Even r := by simp [r]
  have hRatio : (2 : Real) / r = 1 / r0 := by
    simp only [r]
    push_cast
    field_simp [hr0R]
  simp only [fermatEulerTaylorTerm]
  rw [fermatEuler_inert_slot_zero theta m p t x hp hNotSplit hInert,
    show (2 * l + 1) + 1 = r by simp [r, r0]; omega,
    fermatEulerLog_LSeriesTerm_prime_pow theta m p r x t hp hr,
    fermatHeckeEulerLogCoefficient_prime_pow theta m p r hp hr,
    if_neg hNotSplit, if_pos ⟨hInert, hEven⟩]
  change (((-1 : Complex) ^ m * w ^ 2) ^ r0 / r0) =
    (((((2 : Real) / r) * (-1 : Real) ^ (m * (r / 2)) : Real) : Complex) *
      w ^ r)
  rw [mul_pow, ← pow_mul, show r / 2 = r0 by simp [r], hRatio]
  push_cast
  have hw : (w ^ 2) ^ r0 = w ^ r := by
    rw [← pow_mul]
  rw [hw]
  field_simp [hr0C]

def fermatInertExponentEmbedding (l : Nat) : Nat :=
  2 * l + 1

theorem fermatInertExponentEmbedding_injective :
    Function.Injective fermatInertExponentEmbedding := by
  intro a b h
  simp only [fermatInertExponentEmbedding] at h
  omega

theorem fermat_not_even_succ_of_not_inertExponent_range
    (k : Nat) (hk : k ∉ Set.range fermatInertExponentEmbedding) :
    ¬ Even (k + 1) := by
  intro hEven
  rcases hEven with ⟨d, hd⟩
  have hdPos : 0 < d := by omega
  apply hk
  refine ⟨d - 1, ?_⟩
  simp only [fermatInertExponentEmbedding]
  omega

theorem fermat_inert_LSeriesTerm_zero_off_embedding
    (theta : Nat -> Real) (m p k : Nat) (x t : Real)
    (hp : Nat.Prime p) (hNotSplit : p % 3 ≠ 1) (hInert : p % 3 = 2)
    (hk : k ∉ Set.range fermatInertExponentEmbedding) :
    LSeries.term (fermatHeckeEulerLogCoefficient theta m)
        (1 + (x : Complex) + Complex.I * (t : Complex)) (p ^ (k + 1)) = 0 := by
  have hr : 0 < k + 1 := Nat.zero_lt_succ k
  have hNotEven := fermat_not_even_succ_of_not_inertExponent_range k hk
  rw [fermatEulerLog_LSeriesTerm_prime_pow theta m p (k + 1) x t hp hr,
    fermatHeckeEulerLogCoefficient_prime_pow theta m p (k + 1) hp hr,
    if_neg hNotSplit, if_neg (not_and_or.mpr (Or.inr hNotEven))]
  norm_num

theorem fermat_inert_primeEulerLog_eq
    (theta : Nat -> Real) (m p : Nat) (t x : Real)
    (hx : 0 < x) (hp : Nat.Prime p)
    (hNotSplit : p % 3 ≠ 1) (hInert : p % 3 = 2) :
    fermatPrimeEulerLog theta m t x p =
      ∑' k : Nat,
        LSeries.term (fermatHeckeEulerLogCoefficient theta m)
          (1 + (x : Complex) + Complex.I * (t : Complex)) (p ^ (k + 1)) := by
  let F : Nat -> Complex := fun k =>
    LSeries.term (fermatHeckeEulerLogCoefficient theta m)
      (1 + (x : Complex) + Complex.I * (t : Complex)) (p ^ (k + 1))
  have h0 := fermatEulerTaylorTerm_hasSum theta m t x hx
    (p, (0 : Fin 2))
  have hComp :
      HasSum (F ∘ fermatInertExponentEmbedding)
        (fermatLocalEulerLog theta m t x (p, (0 : Fin 2))) := by
    apply h0.congr_fun
    intro l
    exact (fermat_inert_taylor_eq_LSeriesTerm
      theta m p l x t hp hNotSplit hInert).symm
  have hF :
      HasSum F (fermatLocalEulerLog theta m t x (p, (0 : Fin 2))) :=
    (fermatInertExponentEmbedding_injective.hasSum_iff
      (fun k hk => fermat_inert_LSeriesTerm_zero_off_embedding
        theta m p k x t hp hNotSplit hInert hk)).mp hComp
  have hOne :
      fermatLocalEulerLog theta m t x (p, (1 : Fin 2)) = 0 := by
    rw [fermatLocalEulerLog,
      fermatEuler_inert_slot_one theta m p t x hp hNotSplit]
    simp
  rw [fermatPrimeEulerLog, hOne, add_zero]
  exact hF.tsum_eq.symm

theorem fermat_inactive_primeEulerLog_eq
    (theta : Nat -> Real) (m p : Nat) (t x : Real)
    (hp : Nat.Prime p) (hNotSplit : p % 3 ≠ 1) (hNotInert : p % 3 ≠ 2) :
    fermatPrimeEulerLog theta m t x p =
      ∑' k : Nat,
        LSeries.term (fermatHeckeEulerLogCoefficient theta m)
          (1 + (x : Complex) + Complex.I * (t : Complex)) (p ^ (k + 1)) := by
  have hPrimeLog : fermatPrimeEulerLog theta m t x p = 0 := by
    simp [fermatPrimeEulerLog, fermatLocalEulerLog,
      fermatEulerRadius, fermatEulerLocalValue, hp, hNotSplit, hNotInert]
  have hTerm : ∀ k : Nat,
      LSeries.term (fermatHeckeEulerLogCoefficient theta m)
          (1 + (x : Complex) + Complex.I * (t : Complex))
          (p ^ (k + 1)) = 0 := by
    intro k
    have hr : 0 < k + 1 := Nat.zero_lt_succ k
    rw [fermatEulerLog_LSeriesTerm_prime_pow theta m p (k + 1) x t hp hr,
      fermatHeckeEulerLogCoefficient_prime_pow theta m p (k + 1) hp hr,
      if_neg hNotSplit, if_neg (not_and_or.mpr (Or.inl hNotInert))]
    norm_num
  rw [hPrimeLog]
  simp only [hTerm, tsum_zero]

theorem fermat_primeEulerLog_eq
    (theta : Nat -> Real) (m p : Nat) (t x : Real)
    (hx : 0 < x) (hp : Nat.Prime p) :
    fermatPrimeEulerLog theta m t x p =
      ∑' k : Nat,
        LSeries.term (fermatHeckeEulerLogCoefficient theta m)
          (1 + (x : Complex) + Complex.I * (t : Complex)) (p ^ (k + 1)) := by
  by_cases hSplit : p % 3 = 1
  · exact fermat_split_primeEulerLog_eq theta m p t x hx hp hSplit
  by_cases hInert : p % 3 = 2
  · exact fermat_inert_primeEulerLog_eq theta m p t x hx hp hSplit hInert
  · exact fermat_inactive_primeEulerLog_eq theta m p t x hp hSplit hInert

theorem fermatEulerLog_eq_LSeries
    (theta : Nat -> Real) (m : Nat) (t x : Real) (hx : 0 < x) :
    (∑' q : FermatEulerSlot,
      -Complex.log
        (1 - (fermatEulerRadius x q : Complex) *
          fermatEulerLocalValue theta m t q)) =
      LSeries (fermatHeckeEulerLogCoefficient theta m)
        (1 + (x : Complex) + Complex.I * (t : Complex)) := by
  let s : Complex := 1 + (x : Complex) + Complex.I * (t : Complex)
  let ell : Nat -> Complex := fermatHeckeEulerLogCoefficient theta m
  have hEulerSummable := summable_fermatEulerPowerLog theta m t x hx
  have hProd :
      (∑' q : FermatEulerSlot, fermatLocalEulerLog theta m t x q) =
        ∑' p : Nat, fermatPrimeEulerLog theta m t x p := by
    calc
      (∑' q : FermatEulerSlot, fermatLocalEulerLog theta m t x q) =
          ∑' p : Nat, ∑' j : Fin 2,
            fermatLocalEulerLog theta m t x (p, j) := by
        simpa [fermatLocalEulerLog] using hEulerSummable.tsum_prod
      _ = ∑' p : Nat, fermatPrimeEulerLog theta m t x p := by
        apply tsum_congr
        intro p
        rw [tsum_fintype, Fin.sum_univ_two]
        rfl
  have hPrimeSupport :
      Function.support (fermatPrimeEulerLog theta m t x) ⊆
        {p : Nat | Nat.Prime p} := by
    intro p hpSupport
    change fermatPrimeEulerLog theta m t x p ≠ 0 at hpSupport
    by_contra hp
    have hp' : ¬ Nat.Prime p := by simpa using hp
    apply hpSupport
    simp [fermatPrimeEulerLog, fermatLocalEulerLog,
      fermatEulerRadius, fermatEulerLocalValue, hp']
  have hSubtype :
      (∑' p : Nat.Primes, fermatPrimeEulerLog theta m t x p) =
        ∑' p : Nat, fermatPrimeEulerLog theta m t x p := by
    exact tsum_subtype_eq_of_support_subset hPrimeSupport
  have hPrimeRewrite :
      (∑' p : Nat.Primes, fermatPrimeEulerLog theta m t x p) =
        ∑' p : Nat.Primes, ∑' k : Nat,
          LSeries.term ell s (p ^ (k + 1)) := by
    apply tsum_congr
    intro p
    simpa [ell, s] using
      fermat_primeEulerLog_eq theta m p t x hx p.prop
  have hsRe : 1 < s.re := by simp [s, hx]
  have hLSummable : LSeriesSummable ell s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      ((fermatHeckeEulerLog_abscissa_le_one theta m).trans_lt
        (by exact_mod_cast hsRe))
  have hTermSupport :
      Function.support (LSeries.term ell s) ⊆ {n : Nat | IsPrimePow n} := by
    intro n hn
    change LSeries.term ell s n ≠ 0 at hn
    by_contra hPrimePow
    have hPrimePow' : ¬ IsPrimePow n := by simpa using hPrimePow
    apply hn
    by_cases hn0 : n = 0
    · subst n
      simp
    · simp only [ell]
      rw [LSeries.term_of_ne_zero hn0,
        fermatHeckeEulerLogCoefficient, dif_neg hPrimePow']
      simp
  have hReindex :
      LSeries ell s =
        ∑' p : Nat.Primes, ∑' k : Nat,
          LSeries.term ell s (p ^ (k + 1)) := by
    simpa [LSeries] using
      tsum_eq_tsum_primes_of_support_subset_prime_powers
        hLSummable hTermSupport
  change (∑' q : FermatEulerSlot,
      fermatLocalEulerLog theta m t x q) = LSeries ell s
  calc
    (∑' q : FermatEulerSlot, fermatLocalEulerLog theta m t x q) =
        ∑' p : Nat, fermatPrimeEulerLog theta m t x p := hProd
    _ = ∑' p : Nat.Primes, fermatPrimeEulerLog theta m t x p := hSubtype.symm
    _ = ∑' p : Nat.Primes, ∑' k : Nat,
        LSeries.term ell s (p ^ (k + 1)) := hPrimeRewrite
    _ = LSeries ell s := hReindex.symm

end

end K3Lean.ExplicitFermatHecke
