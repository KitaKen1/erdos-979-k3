import K3Lean.WikipediaHeckePositivity
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.NumberField.DedekindZeta

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# The analytic order comparison in the Wikipedia Hecke route

This file abstracts the last contradiction in Mathlib's proof of
`DirichletCharacter.LFunction_ne_zero_of_re_eq_one`.  It applies to arbitrary
complex functions, so a future Hecke L-function layer only has to provide:

* a simple-pole `O(1/x)` bound for the trivial factor;
* differentiability of the two nontrivial factors at the boundary points;
* the de la Vallee Poussin Euler-product lower bound.

No CM Sato--Tate or prime-character cancellation statement is assumed here.
-/

namespace K3Lean.WikipediaHeckeBoundary

open Complex Asymptotics Topology Filter
open scoped ComplexOrder Topology

/--
The right-hand simple-pole bound for the Dedekind zeta function at `s = 1`.
This is a direct asymptotic consequence of Mathlib's formalized Dirichlet
class number formula; it introduces no project-specific analytic hypothesis.
-/
theorem dedekindZeta_isBigO_near_one_horizontal
    (K : Type*) [Field K] [NumberField K] :
    (fun x : Real => NumberField.dedekindZeta K (1 + x)) =O[𝓝[>] 0]
      (fun x : Real => (1 : Complex) / x) := by
  have hShift :
      Tendsto (fun x : Real => 1 + x) (𝓝[>] 0) (𝓝[>] 1) := by
    have hContinuous :
        Tendsto (fun x : Real => 1 + x) (𝓝 0) (𝓝 1) := by
      have h : ContinuousAt (fun x : Real => 1 + x) 0 :=
        (continuousAt_id (x := (0 : Real))).const_add 1
      simpa only [add_zero] using h.tendsto
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact hContinuous.mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_mem_nhdsWithin] with x hx
      change 0 < x at hx
      change 1 < 1 + x
      linarith
  have hResidue :
      Tendsto
        (fun x : Real =>
          (x : Complex) * NumberField.dedekindZeta K (1 + x))
        (𝓝[>] 0) (𝓝 (NumberField.dedekindZeta_residue K)) := by
    convert
      (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K).comp hShift using 1
    · funext x
      simp
  have hx : ∀ᶠ x : Real in 𝓝[>] 0, (x : Complex) ≠ 0 := by
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    exact ofReal_ne_zero.mpr hx.ne'
  exact (isBigO_mul_iff_isBigO_div hx).mp (hResidue.isBigO_one Complex)

/-- A differentiable function vanishing at the boundary is `O(x)` horizontally. -/
theorem differentiableAt_zero_horizontal_isBigO
    {F : Complex → Complex} {s : Complex}
    (hF : DifferentiableAt Complex F s) (hzero : F s = 0) :
    (fun x : Real => F (x + s)) =O[𝓝[>] 0]
      (fun x : Real => (x : Complex)) := by
  have hDeriv := hF.hasDerivAt
  rw [← zero_add s] at hDeriv
  simpa only [zero_add, hzero, sub_zero] using
    (Complex.isBigO_comp_ofReal_nhds
      (hDeriv.comp_add_const 0 s).differentiableAt.isBigO_sub).mono
        nhdsWithin_le_nhds

/-- A function continuous at the boundary is horizontally `O(1)`. -/
theorem differentiableAt_horizontal_isBigO_one
    {F : Complex → Complex} {s : Complex}
    (hF : DifferentiableAt Complex F s) :
    (fun x : Real => F (x + s)) =O[𝓝[>] 0]
      (fun _ : Real => (1 : Complex)) := by
  have hContinuous := hF.continuousAt
  rw [← zero_add s] at hContinuous
  exact (hContinuous.comp (f := fun x : Real => x + s) (x := 0) (by fun_prop))
    |>.tendsto.isBigO_one Complex |>.mono nhdsWithin_le_nhds

/--
Abstract de la Vallee Poussin contradiction.  A simple-pole factor contributes
at most `x⁻³`, a hypothetical zero contributes `x⁴`, and the last factor is
bounded.  Their product would tend to zero, contradicting the Euler-product
lower bound `>= 1`.
-/
theorem boundary_ne_zero_of_dvp_product
    (Z L M : Complex → Complex) (t : Real)
    (hPole :
      (fun x : Real => Z (1 + x)) =O[𝓝[>] 0]
        (fun x : Real => (1 : Complex) / x))
    (hL : DifferentiableAt Complex L (1 + Complex.I * t))
    (hM : DifferentiableAt Complex M (1 + 2 * Complex.I * t))
    (hProduct : ∀ x : Real, 0 < x →
      1 <= ‖Z (1 + x) ^ 3 * L (1 + x + Complex.I * t) ^ 4 *
        M (1 + x + 2 * Complex.I * t)‖) :
    L (1 + Complex.I * t) ≠ 0 := by
  intro hzero
  have hLZero :
      (fun x : Real => L (1 + x + Complex.I * t)) =O[𝓝[>] 0]
        (fun x : Real => (x : Complex)) := by
    simpa only [ofReal_add, ofReal_one, add_assoc, add_left_comm, add_comm] using
      differentiableAt_zero_horizontal_isBigO hL hzero
  have hMBounded :
      (fun x : Real => M (1 + x + 2 * Complex.I * t)) =O[𝓝[>] 0]
        (fun _ : Real => (1 : Complex)) := by
    simpa only [ofReal_add, ofReal_one, add_assoc, add_left_comm, add_comm] using
      differentiableAt_horizontal_isBigO_one hM
  have hOne :
      (fun _ : Real => (1 : Real)) =O[𝓝[>] 0]
        (fun x : Real =>
          Z (1 + x) ^ 3 * L (1 + x + Complex.I * t) ^ 4 *
            M (1 + x + 2 * Complex.I * t)) :=
    IsBigO.of_bound' <| eventually_nhdsWithin_of_forall fun x hx => by
      simpa using hProduct x hx
  have hOrder := hPole.pow 3 |>.mul <| hLZero.pow 4 |>.mul hMBounded
  have hPower (x : Real) :
      (((1 : Complex) / x) ^ 3 * (x : Complex) ^ 4 * 1) = x := by
    rcases eq_or_ne x 0 with rfl | hx
    · rw [ofReal_zero, zero_pow (by omega), mul_zero, mul_one]
    · rw [one_div, inv_pow, pow_succ _ 3, ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero 3 (ofReal_ne_zero.mpr hx)), one_mul, mul_one]
  have hOrder' :
      (fun x : Real =>
        Z (1 + x) ^ 3 * L (1 + x + Complex.I * t) ^ 4 *
          M (1 + x + 2 * Complex.I * t)) =O[𝓝[>] 0]
        (fun x : Real => (x : Complex)) := by
    exact hOrder.congr
      (fun _ => by ring)
      (fun x => by
        calc
          ((1 : Complex) / x) ^ 3 * ((x : Complex) ^ 4 * 1) =
              ((1 : Complex) / x) ^ 3 * (x : Complex) ^ 4 * (1 : Complex) := by ring
          _ = (x : Complex) := hPower x)
  replace hOrder' := (hOne.trans hOrder').norm_right
  simp only [norm_real] at hOrder'
  exact isLittleO_irrefl (.of_forall (fun _ => one_ne_zero)) <|
    hOrder'.of_norm_right.trans_isLittleO <|
      isLittleO_id_one.mono nhdsWithin_le_nhds

/--
Boundary nonvanishing directly from convergent Euler-log expansions.  This is
the reusable interface for a Hecke L-series: the future ideal-theoretic layer
must prove the three displayed Euler expansions, but need not assume their
nonvanishing consequence.
-/
theorem boundary_ne_zero_of_euler_logs
    {P : Type*}
    (Z L M : Complex → Complex) (t : Real)
    (a : Real → P → Real) (z : P → Complex)
    (hPole :
      (fun x : Real => Z (1 + x)) =O[𝓝[>] 0]
        (fun x : Real => (1 : Complex) / x))
    (hL : DifferentiableAt Complex L (1 + Complex.I * t))
    (hM : DifferentiableAt Complex M (1 + 2 * Complex.I * t))
    (ha0 : ∀ x : Real, 0 < x → ∀ p, 0 <= a x p)
    (ha1 : ∀ x : Real, 0 < x → ∀ p, a x p < 1)
    (hz : ∀ p, Complex.normSq (z p) <= 1)
    (hSum0 : ∀ x : Real, 0 < x →
      Summable (fun p => -Complex.log (1 - (a x p : Complex))))
    (hSum1 : ∀ x : Real, 0 < x →
      Summable (fun p => -Complex.log (1 - (a x p : Complex) * z p)))
    (hSum2 : ∀ x : Real, 0 < x →
      Summable (fun p => -Complex.log (1 - (a x p : Complex) * (z p) ^ 2)))
    (hZ : ∀ x : Real, 0 < x →
      Z (1 + x) =
        Complex.exp (∑' p, -Complex.log (1 - (a x p : Complex))))
    (hLSeries : ∀ x : Real, 0 < x →
      L (1 + x + Complex.I * t) =
        Complex.exp
          (∑' p, -Complex.log (1 - (a x p : Complex) * z p)))
    (hMSeries : ∀ x : Real, 0 < x →
      M (1 + x + 2 * Complex.I * t) =
        Complex.exp
          (∑' p, -Complex.log (1 - (a x p : Complex) * (z p) ^ 2))) :
    L (1 + Complex.I * t) ≠ 0 := by
  apply boundary_ne_zero_of_dvp_product Z L M t hPole hL hM
  intro x hx
  rw [hZ x hx, hLSeries x hx, hMSeries x hx]
  exact K3Lean.WikipediaHeckePositivity.norm_exp_tsum_dvp_ge_one
    (a x) z (ha0 x hx) (ha1 x hx) hz
      (hSum0 x hx) (hSum1 x hx) (hSum2 x hx)

#check @differentiableAt_zero_horizontal_isBigO
#check @dedekindZeta_isBigO_near_one_horizontal
#print axioms dedekindZeta_isBigO_near_one_horizontal
#check @boundary_ne_zero_of_dvp_product
#print axioms boundary_ne_zero_of_dvp_product
#check @boundary_ne_zero_of_euler_logs
#print axioms boundary_ne_zero_of_euler_logs

end K3Lean.WikipediaHeckeBoundary
