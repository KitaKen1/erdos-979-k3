import K3Lean.FermatEulerLogGrouping
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# The trivial Fermat-cubic Euler factor

The base Euler product is the product of the principal Dirichlet L-function
modulo three and the quadratic Dirichlet L-function modulo three.  Consequently
its Euler identity and its simple-pole bound are Mathlib consequences, not
fields of the external Hecke hypothesis.
-/

namespace K3Lean.FermatBaseEuler

open Complex Filter
open DirichletCharacter
open K3Lean.ExplicitFermatHecke
open scoped Topology

noncomputable section

def modThreeQuadraticCharacter : DirichletCharacter Complex 3 :=
  (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom Complex)

@[simp] theorem modThreeQuadraticCharacter_zero :
    modThreeQuadraticCharacter (0 : ZMod 3) = 0 := by
  norm_num [modThreeQuadraticCharacter, quadraticChar, quadraticCharFun]

@[simp] theorem modThreeQuadraticCharacter_one :
    modThreeQuadraticCharacter (1 : ZMod 3) = 1 := by
  norm_num [modThreeQuadraticCharacter, quadraticChar, quadraticCharFun]

@[simp] theorem modThreeQuadraticCharacter_two :
    modThreeQuadraticCharacter (2 : ZMod 3) = -1 := by
  have hns : ¬ IsSquare (2 : ZMod 3) := by decide
  have h20 : (2 : ZMod 3) ≠ 0 := by decide
  norm_num [modThreeQuadraticCharacter, quadraticChar, quadraticCharFun, hns, h20]

theorem modThreeQuadraticCharacter_ne_one :
    modThreeQuadraticCharacter ≠ 1 := by
  have hns : ¬ IsSquare (2 : ZMod 3) := by decide
  have h20 : (2 : ZMod 3) ≠ 0 := by decide
  have hu : IsUnit (2 : ZMod 3) := isUnit_iff_ne_zero.mpr h20
  intro h
  have h2 := congrArg
    (fun chi : DirichletCharacter Complex 3 => chi (2 : ZMod 3)) h
  norm_num [modThreeQuadraticCharacter, quadraticChar, quadraticCharFun,
    hns, h20, MulChar.one_apply hu] at h2

theorem modThreeQuadraticCharacter_apply_nat (n : Nat) :
    modThreeQuadraticCharacter n =
      if n % 3 = 0 then 0 else if n % 3 = 1 then 1 else -1 := by
  rw [← ZMod.natCast_mod n 3]
  have hlt : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  interval_cases h : n % 3
  · norm_num [modThreeQuadraticCharacter, quadraticChar, quadraticCharFun]
  · norm_num [modThreeQuadraticCharacter, quadraticChar, quadraticCharFun]
  · have hns : ¬ IsSquare (2 : ZMod 3) := by decide
    have h20 : (2 : ZMod 3) ≠ 0 := by decide
    norm_num [modThreeQuadraticCharacter, quadraticChar, quadraticCharFun, hns, h20]

def fermatBaseL (s : Complex) : Complex :=
  LFunctionTrivChar 3 s * LFunction modThreeQuadraticCharacter s

theorem fermatBaseL_simple_pole :
    (fun x : Real => fermatBaseL (1 + x)) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun x : Real => (1 : Complex) / x) := by
  have hTriv := LFunctionTrivChar_isBigO_near_one_horizontal (N := 3)
  have hChi := modThreeQuadraticCharacter.LFunction_isBigO_horizontal
    (y := 0) (Or.inr modThreeQuadraticCharacter_ne_one)
  simpa [fermatBaseL] using hTriv.mul hChi

theorem trivialModThree_apply_nat (n : Nat) :
    (1 : DirichletCharacter Complex 3) n =
      if n % 3 = 0 then 0 else 1 := by
  rw [← ZMod.natCast_mod n 3]
  have hlt : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  interval_cases h : n % 3
  · exact MulChar.map_zero _
  · norm_num [MulChar.one_apply]
  · have h20 : (2 : ZMod 3) ≠ 0 := by decide
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr h20)

theorem neg_log_one_sub_add_neg_log_one_add
    (a : Real) (ha0 : 0 <= a) (ha1 : a < 1) :
    -Complex.log (1 - (a : Complex)) +
        -Complex.log (1 + (a : Complex)) =
      -Complex.log (1 - ((a ^ 2 : Real) : Complex)) := by
  have hm0 : 0 <= 1 - a := by linarith
  have hp0 : 0 <= 1 + a := by linarith
  have hs0 : 0 <= 1 - a ^ 2 := by nlinarith
  have hmCast : (1 : Complex) - (a : Complex) = ((1 - a : Real) : Complex) := by
    push_cast
    rfl
  have hpCast : (1 : Complex) + (a : Complex) = ((1 + a : Real) : Complex) := by
    push_cast
    rfl
  have hsCast : (1 : Complex) - ((a ^ 2 : Real) : Complex) =
      ((1 - a ^ 2 : Real) : Complex) := by
    push_cast
    rfl
  rw [hmCast, hpCast, hsCast]
  rw [← Complex.ofReal_log hm0, ← Complex.ofReal_log hp0,
    ← Complex.ofReal_log hs0]
  norm_cast
  have hlog := Real.log_mul (by linarith : 1 - a ≠ 0)
    (by linarith : 1 + a ≠ 0)
  have hprod : (1 - a) * (1 + a) = 1 - a ^ 2 := by ring
  rw [hprod] at hlog
  linarith

theorem prime_cpow_eq_fermatRadius
    (p : Nat) (hp : Nat.Prime p) (x : Real) :
    (p : Complex) ^ (-(1 + (x : Complex))) =
      (Real.exp (-(1 + x) * Real.log p) : Complex) := by
  simpa [K3Lean.ExplicitFermatHecke.fermatPrimeFactor] using
    (K3Lean.ExplicitFermatHecke.fermatPrimeFactor_eq p hp x 0)

def dirichletBasePrimeLog (x : Real) (p : Nat) : Complex :=
  -Complex.log
      (1 - (1 : DirichletCharacter Complex 3) p *
        (p : Complex) ^ (-(1 + (x : Complex)))) +
    -Complex.log
      (1 - modThreeQuadraticCharacter p *
        (p : Complex) ^ (-(1 + (x : Complex))))

def explicitBasePrimeLog (x : Real) (p : Nat) : Complex :=
  -Complex.log (1 - (fermatEulerRadius x (p, (0 : Fin 2)) : Complex)) +
    -Complex.log (1 - (fermatEulerRadius x (p, (1 : Fin 2)) : Complex))

theorem dirichletBasePrimeLog_eq_explicit
    (x : Real) (hx : 0 < x) (p : Nat) (hp : Nat.Prime p) :
    dirichletBasePrimeLog x p = explicitBasePrimeLog x p := by
  let a : Real := Real.exp (-(1 + x) * Real.log p)
  have ha0 : 0 <= a := Real.exp_pos _ |>.le
  have ha1 : a < 1 := by
    change Real.exp (-(1 + x) * Real.log p) < 1
    rw [Real.exp_lt_one_iff]
    have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    nlinarith
  have hpow : Real.exp (-2 * (1 + x) * Real.log p) = a ^ 2 := by
    change Real.exp (-2 * (1 + x) * Real.log p) =
      Real.exp (-(1 + x) * Real.log p) ^ 2
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have ha : Real.exp (-(1 + x) * Real.log p) = a := rfl
  have haC :
      Complex.exp ((-(x : Complex) + -1) * Complex.log (p : Complex)) =
        (a : Complex) := by
    change Complex.exp ((-(x : Complex) + -1) * Complex.log (p : Complex)) =
      (Real.exp (-(1 + x) * Real.log p) : Complex)
    rw [Complex.ofReal_exp, ← Complex.natCast_log]
    congr 1
    push_cast
    ring
  have hpowC :
      Complex.exp
          (-(2 * (1 + (x : Complex)) * Complex.log (p : Complex))) =
        ((a ^ 2 : Real) : Complex) := by
    calc
      Complex.exp
          (-(2 * (1 + (x : Complex)) * Complex.log (p : Complex))) =
          (Real.exp (-2 * (1 + x) * Real.log p) : Complex) := by
        rw [Complex.ofReal_exp, ← Complex.natCast_log]
        congr 1
        push_cast
        ring
      _ = ((a ^ 2 : Real) : Complex) := by rw [hpow]
  rw [dirichletBasePrimeLog, explicitBasePrimeLog,
    trivialModThree_apply_nat, modThreeQuadraticCharacter_apply_nat,
    prime_cpow_eq_fermatRadius p hp x]
  have hlt : p % 3 < 3 := Nat.mod_lt p (by norm_num)
  interval_cases h : p % 3
  · simp [fermatEulerRadius, hp, h]
  · simp only [fermatEulerRadius, hp, h, dite_true, if_pos, Fin.isValue,
      one_mul]
    norm_num
  · simp only [fermatEulerRadius, hp, h, dite_true, Fin.isValue]
    norm_num
    rw [haC, hpowC]
    exact neg_log_one_sub_add_neg_log_one_add a ha0 ha1

theorem dirichletBaseEulerLog_eq_explicit
    (x : Real) (hx : 0 < x) :
    (∑' p : Nat.Primes, dirichletBasePrimeLog x p) =
      ∑' q : FermatEulerSlot,
        -Complex.log (1 - (fermatEulerRadius x q : Complex)) := by
  have hBaseSummable := summable_fermatEulerBaseLog x hx
  have hProd :
      (∑' q : FermatEulerSlot,
        -Complex.log (1 - (fermatEulerRadius x q : Complex))) =
        ∑' p : Nat, explicitBasePrimeLog x p := by
    calc
      (∑' q : FermatEulerSlot,
          -Complex.log (1 - (fermatEulerRadius x q : Complex))) =
          ∑' p : Nat, ∑' j : Fin 2,
            -Complex.log
              (1 - (fermatEulerRadius x (p, j) : Complex)) := by
        simpa using hBaseSummable.tsum_prod
      _ = ∑' p : Nat, explicitBasePrimeLog x p := by
        apply tsum_congr
        intro p
        rw [tsum_fintype, Fin.sum_univ_two]
        rfl
  have hSupport :
      Function.support (explicitBasePrimeLog x) ⊆
        {p : Nat | Nat.Prime p} := by
    intro p hpSupport
    change explicitBasePrimeLog x p ≠ 0 at hpSupport
    by_contra hp
    have hp' : ¬ Nat.Prime p := by simpa using hp
    apply hpSupport
    simp [explicitBasePrimeLog, fermatEulerRadius, hp']
  have hSubtype :
      (∑' p : Nat.Primes, explicitBasePrimeLog x p) =
        ∑' p : Nat, explicitBasePrimeLog x p :=
    tsum_subtype_eq_of_support_subset hSupport
  calc
    (∑' p : Nat.Primes, dirichletBasePrimeLog x p) =
        ∑' p : Nat.Primes, explicitBasePrimeLog x p := by
      apply tsum_congr
      intro p
      exact dirichletBasePrimeLog_eq_explicit x hx p p.prop
    _ = ∑' p : Nat, explicitBasePrimeLog x p := hSubtype
    _ = ∑' q : FermatEulerSlot,
        -Complex.log (1 - (fermatEulerRadius x q : Complex)) := hProd.symm

theorem fermatBaseL_euler
    (x : Real) (hx : 0 < x) :
    fermatBaseL (1 + x) =
      Complex.exp
        (∑' q : FermatEulerSlot,
          -Complex.log (1 - (fermatEulerRadius x q : Complex))) := by
  let s : Complex := 1 + (x : Complex)
  have hs : 1 < s.re := by simp [s, hx]
  have hTrivSum :=
    DirichletCharacter.summable_neg_log_one_sub_mul_prime_cpow
      (1 : DirichletCharacter Complex 3) hs
  have hChiSum :=
    DirichletCharacter.summable_neg_log_one_sub_mul_prime_cpow
      modThreeQuadraticCharacter hs
  have hTrivEuler :=
    DirichletCharacter.LSeries_eulerProduct_exp_log
      (1 : DirichletCharacter Complex 3) hs
  have hChiEuler :=
    DirichletCharacter.LSeries_eulerProduct_exp_log
      modThreeQuadraticCharacter hs
  change LFunction (1 : DirichletCharacter Complex 3) s *
      LFunction modThreeQuadraticCharacter s = _
  rw [DirichletCharacter.LFunction_eq_LSeries
      (1 : DirichletCharacter Complex 3) hs,
    DirichletCharacter.LFunction_eq_LSeries modThreeQuadraticCharacter hs,
    ← hTrivEuler, ← hChiEuler, ← Complex.exp_add,
    ← hTrivSum.tsum_add hChiSum]
  congr 1
  calc
    (∑' p : Nat.Primes, (
        -Complex.log
            (1 - (1 : DirichletCharacter Complex 3) p * p ^ (-s)) +
          -Complex.log
            (1 - modThreeQuadraticCharacter p * p ^ (-s)))) =
        ∑' p : Nat.Primes, dirichletBasePrimeLog x p := by
      apply tsum_congr
      intro p
      simp [dirichletBasePrimeLog, s]
    _ = ∑' q : FermatEulerSlot,
        -Complex.log (1 - (fermatEulerRadius x q : Complex)) :=
      dirichletBaseEulerLog_eq_explicit x hx

end

end K3Lean.FermatBaseEuler
