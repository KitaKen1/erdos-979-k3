import K3Lean.EisensteinRing
import K3Lean.PublishedInputs
import K3Lean.FermatHasseAngle
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.GaussSum

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Gauss's cubic point count via Jacobi sums

For a prime `p ≡ 1 mod 3` and a cubic character `χ` on `ZMod p` with values
in `ℂ`, write `J = jacobiSum χ χ`.  This file proves:

* the two-chart projective point count of the Fermat cubic used by the
  project satisfies `count = p + 1 + (J + conj J)`;
* `J * conj J = p`;
* `J ≡ -1 mod 3` in `ℤ[ω]`, so `π := -J` is a *primary* Eisenstein integer
  of norm `p` with `fermatFrobeniusTrace p = π + conj π`;
* for `p ≡ 2 mod 3` the count is exactly `p + 1`, so the trace vanishes;
* consequently the Hasse bound `|a_p| ≤ 2√p` holds unconditionally
  (`K3Lean.FermatHasseAngle.FermatCubicHasseBound`).

The trace and point count are literally those of `K3Lean.PublishedInputs`.
-/

namespace K3Lean.CubicJacobi

open Complex Finset
open K3Lean.Eisenstein K3Lean.Eisenstein.Eis
open K3Lean.PublishedInputs

noncomputable section

/-! ## Cubic characters -/

/-- A cubic character on `ZMod p` for `p ≡ 1 mod 3`: nontrivial with `χ³ = 1`. -/
theorem exists_cubic_char (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    ∃ χ : MulChar (ZMod p) ℂ, χ ^ 3 = 1 ∧ χ ≠ 1 := by
  have hpp : p.Prime := Fact.out
  have hdvd : (3 : ℕ) ∣ Fintype.card (ZMod p) - 1 := by
    have hc : Fintype.card (ZMod p) = p := ZMod.card p
    rw [hc]
    omega
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 3)) 3 :=
    Complex.isPrimitiveRoot_exp 3 (by norm_num)
  obtain ⟨χ, hχ⟩ := MulChar.exists_mulChar_orderOf (ZMod p) hdvd hζ
  refine ⟨χ, ?_, ?_⟩
  · rw [← hχ]
    exact pow_orderOf_eq_one χ
  · intro hcon
    rw [hcon, orderOf_one] at hχ
    norm_num at hχ

/-- A choice of cubic character. -/
def cubicChar (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) : MulChar (ZMod p) ℂ :=
  Classical.choose (exists_cubic_char p hp)

lemma cubicChar_pow_three (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    cubicChar p hp ^ 3 = 1 :=
  (Classical.choose_spec (exists_cubic_char p hp)).1

lemma cubicChar_ne_one (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    cubicChar p hp ≠ 1 :=
  (Classical.choose_spec (exists_cubic_char p hp)).2

/-- The Jacobi sum `J(χ,χ)` for the chosen cubic character. -/
def jacobiJ (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) : ℂ :=
  jacobiSum (cubicChar p hp) (cubicChar p hp)

/-! ## The three basic facts about `J` -/

/-- Complex conjugation turns the cubic character into its inverse. -/
lemma cubicChar_conj (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    (cubicChar p hp).ringHomComp (starRingEnd ℂ) = (cubicChar p hp)⁻¹ := by
  have hχ3 := cubicChar_pow_three p hp
  apply MulChar.ext
  intro a
  have hu : IsUnit ((a : ZMod p)) := a.isUnit
  have h3 : (cubicChar p hp (a : ZMod p)) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' _ (by norm_num : (3 : ℕ) ≠ 0), hχ3,
      MulChar.one_apply hu]
  have hmc : cubicChar p hp (a : ZMod p) *
      (starRingEnd ℂ) (cubicChar p hp (a : ZMod p)) = 1 := by
    rw [Complex.mul_conj]
    have hnorm : ‖cubicChar p hp (a : ZMod p)‖ = 1 := by
      have hcube := congrArg (fun z : ℂ => ‖z‖) h3
      rw [norm_pow, show ‖(1 : ℂ)‖ = 1 from by simp] at hcube
      have hfact : (‖cubicChar p hp (a : ZMod p)‖ - 1) *
          (‖cubicChar p hp (a : ZMod p)‖ ^ 2 + ‖cubicChar p hp (a : ZMod p)‖ + 1)
          = 0 := by
        linear_combination hcube
      rcases mul_eq_zero.mp hfact with h | h
      · linarith
      · have hpos : (0 : ℝ) < ‖cubicChar p hp (a : ZMod p)‖ ^ 2
            + ‖cubicChar p hp (a : ZMod p)‖ + 1 := by positivity
        linarith
    have h2 : Complex.normSq (cubicChar p hp (a : ZMod p)) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    rw [h2]
    norm_num
  have hinv : (starRingEnd ℂ) (cubicChar p hp (a : ZMod p))
      = (cubicChar p hp (a : ZMod p))⁻¹ :=
    eq_inv_of_mul_eq_one_right hmc
  rw [MulChar.ringHomComp_apply, hinv]
  rw [MulChar.inv_apply_eq_inv]
  rw [Ring.inverse_eq_inv]

theorem jacobiJ_mul_conj (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    jacobiJ p hp * (starRingEnd ℂ) (jacobiJ p hp) = p := by
  have hpp : p.Prime := Fact.out
  have hχ3 := cubicChar_pow_three p hp
  have hχ1 := cubicChar_ne_one p hp
  have hχχ : cubicChar p hp * cubicChar p hp ≠ 1 := by
    intro hcon
    have h2 : (cubicChar p hp) ^ 2 = 1 := by
      rw [pow_two]
      exact hcon
    have hd2 : orderOf (cubicChar p hp) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have hd3 : orderOf (cubicChar p hp) ∣ 3 := orderOf_dvd_of_pow_eq_one hχ3
    have h1 : orderOf (cubicChar p hp) = 1 :=
      Nat.dvd_one.mp (by simpa using Nat.dvd_gcd hd2 hd3)
    exact hχ1 (orderOf_eq_one_iff.mp h1)
  have hconj := cubicChar_conj p hp
  have hJconj : (starRingEnd ℂ) (jacobiJ p hp)
      = jacobiSum (cubicChar p hp)⁻¹ (cubicChar p hp)⁻¹ := by
    rw [jacobiJ, ← jacobiSum_ringHomComp, hconj]
  rw [hJconj, jacobiJ]
  have hrc : ringChar ℂ ≠ ringChar (ZMod p) := by
    rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]
    exact fun hc => hpp.ne_zero hc.symm
  have h := jacobiSum_mul_jacobiSum_inv hrc hχ1 hχ1 hχχ
  rw [h, ZMod.card]

theorem abs_jacobiJ (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    ‖jacobiJ p hp‖ = Real.sqrt p := by
  have h := jacobiJ_mul_conj p hp
  rw [Complex.mul_conj] at h
  have h2 : Complex.normSq (jacobiJ p hp) = p := by exact_mod_cast h
  rw [Complex.norm_def, h2]

/-- `J = -1 + 3·(ω·z)` with `z ∈ ℤ[ω]`: there is a primary Eisenstein integer
`π` with `toC π = -J`. -/
lemma isPrimitiveRoot_omegaC : IsPrimitiveRoot omegaC 3 := by
  have hcube : omegaC ^ 3 = 1 := by
    have h := omegaC_sq
    calc omegaC ^ 3 = omegaC * (omegaC * omegaC) := by ring
      _ = omegaC * (-1 - omegaC) := by rw [h]
      _ = -(omegaC * omegaC) - omegaC := by ring
      _ = -(-1 - omegaC) - omegaC := by rw [h]
      _ = 1 := by ring
  have him : omegaC.im ≠ 0 := by
    rw [omegaC_im]
    have h3 := sqrt_three_pos
    positivity
  constructor
  · exact hcube
  · intro l hl
    obtain ⟨q, r, hr, hlqr⟩ : ∃ q r, r < 3 ∧ l = 3 * q + r :=
      ⟨l / 3, l % 3, Nat.mod_lt _ (by norm_num), by omega⟩
    subst hlqr
    rw [pow_add, pow_mul, hcube, one_pow, one_mul] at hl
    interval_cases r
    · omega
    · exfalso
      rw [pow_one] at hl
      have h := congrArg Complex.im hl
      rw [omegaC_im, Complex.one_im] at h
      have h3 := sqrt_three_pos
      linarith
    · exfalso
      rw [sq, omegaC_sq] at hl
      have h := congrArg Complex.im hl
      simp only [Complex.sub_im, Complex.neg_im, Complex.one_im, omegaC_im,
        Complex.one_im] at h
      have h3 := sqrt_three_pos
      linarith

lemma exists_eis_of_mem_adjoin {w : ℂ} (hw : w ∈ Algebra.adjoin ℤ {omegaC}) :
    ∃ β : Eis, toC β = w := by
  induction hw using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨omega, by rw [toC_omega, hx]⟩
  | algebraMap r =>
    refine ⟨(r : Eis), ?_⟩
    rw [map_intCast]
    simp
  | add x y hx hy ihx ihy =>
    obtain ⟨βx, hβx⟩ := ihx
    obtain ⟨βy, hβy⟩ := ihy
    exact ⟨βx + βy, by rw [map_add, hβx, hβy]⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨βx, hβx⟩ := ihx
    obtain ⟨βy, hβy⟩ := ihy
    exact ⟨βx * βy, by rw [map_mul, hβx, hβy]⟩

theorem exists_primary_neg_jacobiJ (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    ∃ π : Eis, Primary π ∧ toC π = -(jacobiJ p hp) := by
  have hpp : p.Prime := Fact.out
  have hdvd : (3 : ℕ) ∣ Fintype.card (ZMod p) - 1 := by
    have hc : Fintype.card (ZMod p) = p := ZMod.card p
    rw [hc]
    omega
  have hχ3 := cubicChar_pow_three p hp
  obtain ⟨z, hz, hJ⟩ := exists_jacobiSum_eq_neg_one_add (by norm_num : 2 < 3)
    hχ3 hχ3 hdvd isPrimitiveRoot_omegaC
  obtain ⟨βz, hβz⟩ := exists_eis_of_mem_adjoin hz
  have hsq : (omegaC - 1) ^ 2 = -3 * omegaC := by
    have h := omegaC_sq
    calc (omegaC - 1) ^ 2 = omegaC * omegaC - 2 * omegaC + 1 := by ring
      _ = (-1 - omegaC) - 2 * omegaC + 1 := by rw [h]
      _ = -3 * omegaC := by ring
  refine ⟨1 + 3 * (omega * βz), ?_, ?_⟩
  · rw [primary_iff]
    exact ⟨omega * βz, rfl⟩
  · rw [map_add, map_one, map_mul, map_mul, toC_omega, hβz]
    have h3 : toC (3 : Eis) = 3 := by
      have : ((3 : ℕ) : Eis) = (3 : Eis) := by norm_cast
      rw [← this, map_natCast]
      norm_num
    have hJ' : jacobiJ p hp = -1 + z * (omegaC - 1) ^ 2 := hJ
    rw [h3, hJ', hsq]
    ring

/-! ## Point counts -/

/-- The cubic character takes the value `1` at `-1`. -/
lemma cubicChar_neg_one (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    cubicChar p hp (-1) = 1 := by
  have h2 : cubicChar p hp (-1) * cubicChar p hp (-1) = 1 := by
    rw [← map_mul, neg_mul_neg, one_mul, map_one]
  have h3 : cubicChar p hp (-1) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' _ (by norm_num : (3 : ℕ) ≠ 0), cubicChar_pow_three p hp,
      MulChar.one_apply (IsUnit.neg isUnit_one)]
  calc cubicChar p hp (-1)
      = cubicChar p hp (-1) * (cubicChar p hp (-1) * cubicChar p hp (-1)) := by
        rw [h2, mul_one]
    _ = cubicChar p hp (-1) ^ 3 := by ring
    _ = 1 := h3

lemma cubicChar_sq_ne_one (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    cubicChar p hp ^ 2 ≠ 1 := by
  intro hcon
  have hd2 : orderOf (cubicChar p hp) ∣ 2 := orderOf_dvd_of_pow_eq_one hcon
  have hd3 : orderOf (cubicChar p hp) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (cubicChar_pow_three p hp)
  have h1 : orderOf (cubicChar p hp) = 1 :=
    Nat.dvd_one.mp (by simpa using Nat.dvd_gcd hd2 hd3)
  exact cubicChar_ne_one p hp (orderOf_eq_one_iff.mp h1)

lemma cubicChar_sq_eq_inv (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    cubicChar p hp ^ 2 = (cubicChar p hp)⁻¹ := by
  have h3 : cubicChar p hp ^ (2 + 1) = 1 := by
    rw [show (2 + 1 : ℕ) = 3 by norm_num]
    exact cubicChar_pow_three p hp
  rw [pow_succ] at h3
  exact eq_inv_of_mul_eq_one_left h3

/-- `(χ^j)(-1) = 1` for every power of the cubic character. -/
lemma cubicChar_pow_neg_one (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) (j : ℕ) :
    (cubicChar p hp ^ j) (-1) = 1 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, MulChar.one_apply (IsUnit.neg isUnit_one)]
  · rw [MulChar.pow_apply' _ hj.ne', cubicChar_neg_one p hp, one_pow]

/-- `ZMod p` contains a primitive cube root of unity when `p ≡ 1 mod 3`. -/
lemma exists_cube_data (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    ∃ ζ : ZMod p, IsPrimitiveRoot ζ 3 := by
  have hpp : p.Prime := Fact.out
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hpp]
  have horderg : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, p - 1 = 3 * m := by
    refine ⟨(p - 1) / 3, ?_⟩
    have h2 := hpp.two_le
    omega
  have hm0 : 0 < m := by
    have h2 := hpp.two_le
    omega
  have horder : orderOf (g ^ m) = 3 := by
    rw [orderOf_pow, horderg, hm]
    have hgcd : Nat.gcd (3 * m) m = m := by
      rw [Nat.gcd_comm]
      exact Nat.gcd_eq_left ⟨3, by ring⟩
    rw [hgcd]
    rw [Nat.mul_div_assoc 3 dvd_rfl, Nat.div_self hm0, mul_one]
  refine ⟨((g ^ m : (ZMod p)ˣ) : ZMod p), ?_⟩
  rw [IsPrimitiveRoot.coe_units_iff]
  constructor
  · rw [← horder]
    exact pow_orderOf_eq_one _
  · intro l hl
    rw [← horder]
    exact orderOf_dvd_of_pow_eq_one hl

/-- The cubic character detects nonzero cubes. -/
lemma cubicChar_eq_one_iff (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) {a : ZMod p}
    (ha : a ≠ 0) :
    cubicChar p hp a = 1 ↔ ∃ b : ZMod p, b ^ 3 = a := by
  constructor
  · intro h1
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    have hau : IsUnit a := isUnit_iff_ne_zero.mpr ha
    obtain ⟨au, hau'⟩ := hau
    obtain ⟨t, ht⟩ := (Submonoid.mem_powers_iff au g).mp
      ((isOfFinOrder_of_finite g).mem_powers_iff_mem_zpowers.mpr (hg au))
    have hχg1 : cubicChar p hp (g : ZMod p) ≠ 1 := by
      intro hcon
      apply cubicChar_ne_one p hp
      apply MulChar.ext
      intro u
      obtain ⟨s, hs⟩ := (Submonoid.mem_powers_iff u g).mp
        ((isOfFinOrder_of_finite g).mem_powers_iff_mem_zpowers.mpr (hg u))
      rw [MulChar.one_apply u.isUnit, ← hs, Units.val_pow_eq_pow_val, map_pow,
        hcon, one_pow]
    have hχg3 : cubicChar p hp (g : ZMod p) ^ 3 = 1 := by
      rw [← MulChar.pow_apply' _ (by norm_num : (3 : ℕ) ≠ 0), cubicChar_pow_three p hp,
        MulChar.one_apply g.isUnit]
    have hordχg : orderOf (cubicChar p hp (g : ZMod p)) = 3 := by
      have hdvd : orderOf (cubicChar p hp (g : ZMod p)) ∣ 3 :=
        orderOf_dvd_of_pow_eq_one hχg3
      rcases Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hχg1
      · exact h
    have hχa : cubicChar p hp a = cubicChar p hp (g : ZMod p) ^ t := by
      rw [← hau', ← ht, Units.val_pow_eq_pow_val, map_pow]
    rw [hχa] at h1
    obtain ⟨s, hs⟩ : (3 : ℕ) ∣ t := by
      rw [← hordχg]
      exact orderOf_dvd_of_pow_eq_one h1
    refine ⟨(g : ZMod p) ^ s, ?_⟩
    rw [← pow_mul, mul_comm s 3, ← hs, ← Units.val_pow_eq_pow_val, ht, hau']
  · rintro ⟨b, rfl⟩
    have hb : b ≠ 0 := by
      rintro rfl
      exact ha (by norm_num)
    have hbu : IsUnit b := isUnit_iff_ne_zero.mpr hb
    rw [map_pow, ← MulChar.pow_apply' _ (by norm_num : (3 : ℕ) ≠ 0),
      cubicChar_pow_three p hp, MulChar.one_apply hbu]

open scoped Classical in
/-- The number of cube roots of a nonzero element: `3` on cubes, `0` otherwise. -/
lemma cube_fiber_card_nat (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) {a : ZMod p}
    (ha : a ≠ 0) :
    (Finset.univ.filter fun x : ZMod p => x ^ 3 = a).card
      = if ∃ b : ZMod p, b ^ 3 = a then 3 else 0 := by
  obtain ⟨ζ, hζ⟩ := exists_cube_data p hp
  have hfilter : (Finset.univ.filter fun x : ZMod p => x ^ 3 = a)
      = (Polynomial.nthRoots 3 a).toFinset := by
    ext x
    rw [Finset.mem_filter, Multiset.mem_toFinset,
      Polynomial.mem_nthRoots (by norm_num : (0 : ℕ) < 3)]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩
  rw [hfilter, Multiset.toFinset_card_of_nodup (hζ.nthRoots_nodup ha),
    hζ.card_nthRoots]
  split_ifs with h <;> rfl

/-- Character-sum formula for the number of cube roots. -/
lemma cube_fiber_card_char (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) (a : ZMod p) :
    ((Finset.univ.filter fun x : ZMod p => x ^ 3 = a).card : ℂ)
      = (if a = 0 then 1 else 0)
        + ∑ j ∈ Finset.range 3, (cubicChar p hp ^ j) a := by
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl]
    have hfilter : (Finset.univ.filter fun x : ZMod p => x ^ 3 = (0 : ZMod p)) = {0} := by
      ext x
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩
        exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp h
      · rintro rfl
        exact ⟨Finset.mem_univ _, by norm_num⟩
    have hS : ∑ j ∈ Finset.range 3, (cubicChar p hp ^ j) (0 : ZMod p) = 0 :=
      Finset.sum_eq_zero fun j _ => MulChar.map_nonunit _ not_isUnit_zero
    rw [hfilter, hS, Finset.card_singleton]
    norm_num
  · rw [if_neg ha, zero_add, cube_fiber_card_nat p hp ha]
    have hau : IsUnit a := isUnit_iff_ne_zero.mpr ha
    by_cases hcube : ∃ b : ZMod p, b ^ 3 = a
    · have hχ1 : cubicChar p hp a = 1 := (cubicChar_eq_one_iff p hp ha).mpr hcube
      rw [if_pos hcube, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one, pow_zero, MulChar.one_apply hau, pow_one, hχ1,
        MulChar.pow_apply' _ (by norm_num : (2 : ℕ) ≠ 0), hχ1]
      norm_num
    · have hχ1 : cubicChar p hp a ≠ 1 := fun hcon =>
        hcube ((cubicChar_eq_one_iff p hp ha).mp hcon)
      have hw3 : cubicChar p hp a ^ 3 = 1 := by
        rw [← MulChar.pow_apply' _ (by norm_num : (3 : ℕ) ≠ 0),
          cubicChar_pow_three p hp, MulChar.one_apply hau]
      rw [if_neg hcube, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one, pow_zero, MulChar.one_apply hau, pow_one,
        MulChar.pow_apply' _ (by norm_num : (2 : ℕ) ≠ 0)]
      have hfact : (cubicChar p hp a - 1)
          * (1 + cubicChar p hp a + cubicChar p hp a ^ 2) = 0 := by
        linear_combination hw3
      rcases mul_eq_zero.mp hfact with h | h
      · exact absurd (by linear_combination h) hχ1
      · push_cast
        linear_combination -h

/-- Summing `f (x^3)` fiberwise. -/
lemma sum_cube_reindex (p : ℕ) [Fact p.Prime] (f : ZMod p → ℂ) :
    ∑ x : ZMod p, f (x ^ 3)
      = ∑ b : ZMod p,
          ((Finset.univ.filter fun x : ZMod p => x ^ 3 = b).card : ℂ) * f b := by
  rw [← Finset.sum_fiberwise_of_maps_to' (g := fun x : ZMod p => x ^ 3)
      (fun i _ => Finset.mem_univ _) f]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-- Shifted character sums are Jacobi sums when both characters kill `-1`. -/
lemma sum_shift_eq_jacobiSum (p : ℕ) [Fact p.Prime] (χ₁ χ₂ : MulChar (ZMod p) ℂ)
    (h₁ : χ₁ (-1) = 1) (h₂ : χ₂ (-1) = 1) :
    ∑ a : ZMod p, χ₁ a * χ₂ (-1 - a) = jacobiSum χ₁ χ₂ := by
  have hneg : ∀ (χ : MulChar (ZMod p) ℂ), χ (-1) = 1 → ∀ y : ZMod p, χ (-y) = χ y := by
    intro χ hχ y
    calc χ (-y) = χ ((-1) * y) := by rw [neg_one_mul]
      _ = χ (-1) * χ y := map_mul χ _ _
      _ = χ y := by rw [hχ, one_mul]
  have h := Fintype.sum_equiv (Equiv.neg (ZMod p))
    (fun a : ZMod p => χ₁ a * χ₂ (-1 - a)) (fun x : ZMod p => χ₁ x * χ₂ (1 - x)) ?_
  · rw [show jacobiSum χ₁ χ₂ = ∑ x : ZMod p, χ₁ x * χ₂ (1 - x) from rfl]
    exact h
  · intro x
    simp only [Equiv.neg_apply]
    rw [hneg χ₁ h₁ x]
    rw [show (1 - -x : ZMod p) = -(-1 - x) by ring, hneg χ₂ h₂]


set_option maxHeartbeats 1600000 in
/-- Split case: the two-chart count equals `p + 1 + (J + conj J)`. -/
theorem chart_count_split (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    (fermatProjectivePointCount p : ℂ) =
      (p : ℂ) + 1 + (jacobiJ p hp + (starRingEnd ℂ) (jacobiJ p hp)) := by
  have hv00 : jacobiSum (1 : MulChar (ZMod p) ℂ) 1 = (Fintype.card (ZMod p) : ℂ) - 2 :=
    jacobiSum_one_one
  have hv01 : jacobiSum (1 : MulChar (ZMod p) ℂ) (cubicChar p hp) = -1 :=
    jacobiSum_one_nontrivial (cubicChar_ne_one p hp)
  have hv02 : jacobiSum (1 : MulChar (ZMod p) ℂ) (cubicChar p hp ^ 2) = -1 :=
    jacobiSum_one_nontrivial (cubicChar_sq_ne_one p hp)
  have hv10 : jacobiSum (cubicChar p hp) (1 : MulChar (ZMod p) ℂ) = -1 := by
    rw [jacobiSum_comm]; exact hv01
  have hv20 : jacobiSum (cubicChar p hp ^ 2) (1 : MulChar (ZMod p) ℂ) = -1 := by
    rw [jacobiSum_comm]; exact hv02
  have hv11 : jacobiSum (cubicChar p hp) (cubicChar p hp) = jacobiJ p hp := rfl
  have hv12 : jacobiSum (cubicChar p hp) (cubicChar p hp ^ 2) = -1 := by
    rw [cubicChar_sq_eq_inv p hp, jacobiSum_nontrivial_inv (cubicChar_ne_one p hp),
      cubicChar_neg_one p hp]
  have hv21 : jacobiSum (cubicChar p hp ^ 2) (cubicChar p hp) = -1 := by
    rw [jacobiSum_comm]; exact hv12
  have hv22 : jacobiSum (cubicChar p hp ^ 2) (cubicChar p hp ^ 2)
      = (starRingEnd ℂ) (jacobiJ p hp) := by
    rw [cubicChar_sq_eq_inv p hp, ← cubicChar_conj p hp, jacobiSum_ringHomComp]
    rw [hv11]
  have hJK : ∀ j k : ℕ,
      ∑ b : ZMod p, (cubicChar p hp ^ j) b * (cubicChar p hp ^ k) (-1 - b)
        = jacobiSum (cubicChar p hp ^ j) (cubicChar p hp ^ k) := fun j k =>
    sum_shift_eq_jacobiSum p _ _ (cubicChar_pow_neg_one p hp j)
      (cubicChar_pow_neg_one p hp k)
  have hT4 : ∑ b : ZMod p, (∑ j ∈ Finset.range 3, (cubicChar p hp ^ j) b)
      * (∑ k ∈ Finset.range 3, (cubicChar p hp ^ k) (-1 - b))
      = (Fintype.card (ZMod p) : ℂ) - 8
        + (jacobiJ p hp + (starRingEnd ℂ) (jacobiJ p hp)) := by
    rw [Finset.sum_congr rfl fun b _ =>
      Finset.sum_mul_sum (Finset.range 3) (Finset.range 3) _ _]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_comm]
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hJK j k]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [pow_zero, pow_one]
    rw [hv00, hv01, hv02, hv10, hv11, hv12, hv20, hv21, hv22]
    ring
  have hT1 : ∑ b : ZMod p,
      (if b = 0 then (1 : ℂ) else 0) * (if -1 - b = 0 then (1 : ℂ) else 0) = 0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    rcases eq_or_ne b 0 with rfl | hb
    · have hne : ¬(-1 - (0 : ZMod p) = 0) := by
        intro h
        have h1 : (-1 : ZMod p) = 0 := by linear_combination h
        exact one_ne_zero (α := ZMod p) (neg_eq_zero.mp h1)
      rw [if_neg hne, mul_zero]
    · rw [if_neg hb, zero_mul]
  have hSneg1 : ∑ j ∈ Finset.range 3, (cubicChar p hp ^ j) (-1 : ZMod p) = 3 := by
    rw [Finset.sum_congr rfl fun j _ => cubicChar_pow_neg_one p hp j,
      Finset.sum_const, Finset.card_range]
    norm_num
  have hT2 : ∑ b : ZMod p, (if b = 0 then (1 : ℂ) else 0)
      * (∑ k ∈ Finset.range 3, (cubicChar p hp ^ k) (-1 - b)) = 3 := by
    have hpt : ∀ b : ZMod p, (if b = 0 then (1 : ℂ) else 0)
        * (∑ k ∈ Finset.range 3, (cubicChar p hp ^ k) (-1 - b))
        = (if b = 0 then ∑ k ∈ Finset.range 3, (cubicChar p hp ^ k) (-1 - b) else 0) := by
      intro b
      rw [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_congr rfl fun b _ => hpt b]
    rw [Fintype.sum_ite_eq' (0 : ZMod p)
      (fun b => ∑ k ∈ Finset.range 3, (cubicChar p hp ^ k) (-1 - b))]
    rw [show (-1 - (0 : ZMod p)) = -1 by ring]
    exact hSneg1
  have hT3 : ∑ b : ZMod p, (∑ j ∈ Finset.range 3, (cubicChar p hp ^ j) b)
      * (if -1 - b = 0 then (1 : ℂ) else 0) = 3 := by
    have hpt : ∀ b : ZMod p, (∑ j ∈ Finset.range 3, (cubicChar p hp ^ j) b)
        * (if -1 - b = 0 then (1 : ℂ) else 0)
        = (if b = -1 then ∑ j ∈ Finset.range 3, (cubicChar p hp ^ j) b else 0) := by
      intro b
      rw [mul_ite, mul_one, mul_zero]
      refine if_congr ?_ rfl rfl
      constructor
      · intro h
        linear_combination -h
      · intro h
        linear_combination -h
    rw [Finset.sum_congr rfl fun b _ => hpt b]
    rw [Fintype.sum_ite_eq' (-1 : ZMod p)
      (fun b => ∑ j ∈ Finset.range 3, (cubicChar p hp ^ j) b)]
    exact hSneg1
  have haffC : ((Finset.univ.filter
        fun uv : ZMod p × ZMod p => 1 + uv.1 ^ 3 + uv.2 ^ 3 = 0).card : ℂ)
      = (Fintype.card (ZMod p) : ℂ) - 2
        + (jacobiJ p hp + (starRingEnd ℂ) (jacobiJ p hp)) := by
    have h2 : ((Finset.univ.filter
          fun uv : ZMod p × ZMod p => 1 + uv.1 ^ 3 + uv.2 ^ 3 = 0).card : ℂ)
        = ∑ u : ZMod p,
            ((Finset.univ.filter fun x : ZMod p => x ^ 3 = -1 - u ^ 3).card : ℂ) := by
      rw [Finset.card_filter]
      push_cast
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun v _ => ?_
      refine if_congr ?_ rfl rfl
      constructor
      · intro h
        linear_combination h
      · intro h
        linear_combination h
    rw [h2]
    rw [sum_cube_reindex p (fun t : ZMod p =>
      ((Finset.univ.filter fun x : ZMod p => x ^ 3 = -1 - t).card : ℂ))]
    rw [Finset.sum_congr rfl fun b _ => by
      rw [cube_fiber_card_char p hp b, cube_fiber_card_char p hp (-1 - b)]]
    simp only [add_mul, mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [hT1, hT2, hT3, hT4]
    ring
  have hinfC : ((Finset.univ.filter
        fun v : ZMod p => v ^ 3 = (-1 : ZMod p)).card : ℂ) = 3 := by
    have hne : (-1 : ZMod p) ≠ 0 := by
      intro h
      exact one_ne_zero (α := ZMod p) (neg_eq_zero.mp h)
    rw [cube_fiber_card_nat p hp hne, if_pos ⟨-1, by ring⟩]
    norm_num
  have haffN : Nat.card (fermatAffineChartPoint p)
      = (Finset.univ.filter
          fun uv : ZMod p × ZMod p => 1 + uv.1 ^ 3 + uv.2 ^ 3 = 0).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype _
  have hinfN : Nat.card (fermatInfinityChartPoint p)
      = (Finset.univ.filter fun v : ZMod p => v ^ 3 = (-1 : ZMod p)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    apply Finset.filter_congr
    intro v _
    constructor
    · intro h
      linear_combination h
    · intro h
      linear_combination h
  unfold fermatProjectivePointCount
  rw [haffN, hinfN]
  push_cast
  rw [haffC, hinfC, ZMod.card]
  ring

lemma cube_bijective (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2) :
    Function.Bijective (fun x : ZMod p => x ^ 3) := by
  have hpp : p.Prime := Fact.out
  have hcop : (Nat.card (ZMod p)ˣ).Coprime 3 := by
    have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hpp]
    rw [hcard]
    have h3 : ¬ ((3 : ℕ) ∣ (p - 1)) := by
      have h2 := hpp.two_le
      omega
    exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h3).symm
  constructor
  · intro x y hxy
    simp only at hxy
    rcases eq_or_ne x 0 with rfl | hx
    · rcases eq_or_ne y 0 with rfl | hy
      · rfl
      · exfalso
        rw [zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at hxy
        exact hy ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hxy.symm)
    · rcases eq_or_ne y 0 with rfl | hy
      · exfalso
        rw [zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at hxy
        exact hx ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hxy)
      · have hux : (Units.mk0 x hx) ^ 3 = (Units.mk0 y hy) ^ 3 := by
          ext
          push_cast
          exact hxy
        have h := (powCoprime hcop).injective (a₁ := Units.mk0 x hx)
          (a₂ := Units.mk0 y hy) hux
        have := congrArg Units.val h
        simpa using this
  · intro y
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, by simp⟩
    · obtain ⟨ux, hux⟩ := (powCoprime hcop).surjective (Units.mk0 y hy)
      refine ⟨ux.val, ?_⟩
      have := congrArg Units.val hux
      simpa using this

/-- Inert case: cubing is a bijection, and the count is `p + 1`. -/
theorem chart_count_inert (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2) :
    fermatProjectivePointCount p = p + 1 := by
  have hbij := cube_bijective p hp
  set e := Equiv.ofBijective _ hbij with he_def
  have hspec : ∀ z : ZMod p, (e.symm z) ^ 3 = z := by
    intro z
    exact e.apply_symm_apply z
  have haff : Nat.card (fermatAffineChartPoint p) = p := by
    have heq : fermatAffineChartPoint p ≃ ZMod p :=
      { toFun := fun s => s.1.1
        invFun := fun u => ⟨(u, e.symm (-1 - u ^ 3)), by
          show (1 : ZMod p) + u ^ 3 + (e.symm (-1 - u ^ 3)) ^ 3 = 0
          rw [hspec]
          ring⟩
        left_inv := fun s => by
          obtain ⟨⟨u, v⟩, hs⟩ := s
          simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
          apply hbij.1
          beta_reduce
          rw [hspec]
          have hv : v ^ 3 = -1 - u ^ 3 := by linear_combination hs
          exact hv.symm
        right_inv := fun u => rfl }
    rw [Nat.card_congr heq]
    exact Nat.card_zmod p
  have hinf : Nat.card (fermatInfinityChartPoint p) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    constructor
    · constructor
      intro a b
      obtain ⟨va, hva⟩ := a
      obtain ⟨vb, hvb⟩ := b
      have h : va = vb := by
        apply hbij.1
        beta_reduce
        have h1 : va ^ 3 = -1 := by linear_combination hva
        have h2 : vb ^ 3 = -1 := by linear_combination hvb
        rw [h1, h2]
      exact Subtype.ext h
    · exact ⟨⟨e.symm (-1), by
        show (1 : ZMod p) + (e.symm (-1)) ^ 3 = 0
        rw [hspec]
        ring⟩⟩
  unfold fermatProjectivePointCount
  rw [haff, hinf]

theorem trace_eq_zero_inert (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2) :
    fermatFrobeniusTrace p = 0 := by
  have h := chart_count_inert p hp
  unfold fermatFrobeniusTrace
  rw [h]
  push_cast
  ring

/-! ## The primary Frobenius element -/

/--
The heart of the arithmetic: for split `p`, there is a primary `π ∈ ℤ[ω]`
of norm `p`, not associated to its conjugate, with
`fermatFrobeniusTrace p = toC π + toC (conj π)`.
-/
theorem exists_primary_frobenius (p : ℕ) [Fact p.Prime] (hp : p % 3 = 1) :
    ∃ π : Eis, Primary π ∧ natNorm π = p ∧ ¬ Associated π (conj π) ∧
      (fermatFrobeniusTrace p : ℂ) = toC π + toC (conj π) := by
  have hpp : p.Prime := Fact.out
  obtain ⟨π, hπ, hπC⟩ := exists_primary_neg_jacobiJ p hp
  have hnormR : ((natNorm π : ℤ) : ℝ) = (p : ℝ) := by
    have h1 := normSq_toC π
    rw [hπC, Complex.normSq_neg] at h1
    have h2 := jacobiJ_mul_conj p hp
    rw [Complex.mul_conj] at h2
    have h3 : Complex.normSq (jacobiJ p hp) = (p : ℝ) := by exact_mod_cast h2
    rw [h3] at h1
    rw [natNorm_cast]
    exact h1.symm
  have hnorm : natNorm π = p := by exact_mod_cast hnormR
  have hconjP : Primary (conj π) := by
    obtain ⟨h1, h2⟩ := hπ
    refine ⟨?_, ?_⟩
    · rw [Eis.conj_re]
      have h3 : π.re - π.im - 1 = (π.re - 1) - π.im := by ring
      rw [h3]
      exact dvd_sub h1 h2
    · rw [Eis.conj_im]
      exact dvd_neg.mpr h2
  refine ⟨π, hπ, hnorm, ?_, ?_⟩
  · intro hass
    have heq : π = conj π := Primary.eq_of_associated hπ hconjP hass
    have him : π.im = 0 := by
      have h := congrArg Eis.im heq
      rw [Eis.conj_im] at h
      omega
    have hre : (p : ℤ) = π.re * π.re := by
      have h := natNorm_cast π
      rw [hnorm] at h
      have h4 : Eis.norm π = π.re * π.re - π.re * π.im + π.im * π.im := rfl
      rw [h4, him] at h
      linear_combination h
    have hre' : p = π.re.natAbs * π.re.natAbs := by
      have h5 := Int.natAbs_mul_self' π.re
      have h6 : (p : ℤ) = ((π.re.natAbs * π.re.natAbs : ℕ) : ℤ) := by
        rw [Nat.cast_mul, h5]
        exact hre
      exact_mod_cast h6
    rcases hpp.eq_one_or_self_of_dvd π.re.natAbs ⟨π.re.natAbs, hre'⟩ with h | h
    · rw [h] at hre'
      have h2 := hpp.two_le
      omega
    · rw [h] at hre'
      have h2 := hpp.two_le
      nlinarith
  · have hcount := chart_count_split p hp
    unfold fermatFrobeniusTrace
    push_cast
    rw [hcount, hπC, toC_conj, hπC, map_neg]
    ring

/-! ## The Hasse bound -/

theorem fermat_hasse_bound : K3Lean.FermatHasseAngle.FermatCubicHasseBound := by
  intro p hpp hp3
  haveI : Fact p.Prime := ⟨hpp⟩
  have h3 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases h3 with h | h | h
  · exfalso
    have hdvd : (3 : ℕ) ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases Nat.Prime.eq_one_or_self_of_dvd hpp 3 hdvd with h1 | h1
    · omega
    · exact hp3 h1.symm
  · have hC : (fermatFrobeniusTrace p : ℂ)
        = -(jacobiJ p h + (starRingEnd ℂ) (jacobiJ p h)) := by
      have hcount := chart_count_split p h
      unfold fermatFrobeniusTrace
      push_cast
      rw [hcount]
      ring
    have htr : (fermatFrobeniusTrace p : ℝ) = -(2 * (jacobiJ p h).re) := by
      have hC2 : ((fermatFrobeniusTrace p : ℝ) : ℂ)
          = ((-(2 * (jacobiJ p h).re) : ℝ) : ℂ) := by
        push_cast
        rw [hC, Complex.add_conj]
        push_cast
        ring
      exact_mod_cast hC2
    rw [htr, abs_neg, abs_mul, abs_two]
    have hre := Complex.abs_re_le_norm (jacobiJ p h)
    have hJ := abs_jacobiJ p h
    calc 2 * |(jacobiJ p h).re| ≤ 2 * ‖jacobiJ p h‖ := by linarith
      _ = 2 * Real.sqrt p := by rw [hJ]
  · rw [trace_eq_zero_inert p h]
    simp

end

end K3Lean.CubicJacobi
