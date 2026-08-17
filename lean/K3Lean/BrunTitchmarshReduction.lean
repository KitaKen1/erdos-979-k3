import K3Lean.ErdosBrunTitchmarsh
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Brun--Titchmarsh supplies the prime-lifting corollary

This file proves the problem-specific `BrunTitchmarshPrimeLiftingCorollary`
from the ordinary published Brun--Titchmarsh theorem.  The lower bound for the
total number of primes is Mathlib's explicit Chebyshev theorem, so no PNT in
arithmetic progressions is used.

For the product `A` of at least eight candidate blocks and cutoff `X = A^2`,
the proof separates primes into three finite sets:

* primes in a globally heavy CRT class;
* primes in a light class for at least one block;
* primes dividing `A`.

The light classes contain at most half of all primes, and the divisors of `A`
are negligible by the explicit Chebyshev bound.  Brun--Titchmarsh bounds each
global CRT class from above, forcing at least `phi(A) / 16` globally heavy
classes.  The finite lemmas in `ErdosBrunTitchmarsh.lean` then select one block
and lift its local cubic solutions.
-/

namespace K3Lean.BrunTitchmarshReduction

open K3Lean.CMProof
open K3Lean.ErdosBrunTitchmarsh
open K3Lean.FiniteLifting
open K3Lean.PublishedInputs
open scoped BigOperators

noncomputable section

open scoped Nat.Prime

theorem card_primeBasesUpTo_eq_primeCounting (X : Nat) :
    (primeBasesUpTo X).card = Nat.primeCounting X := by
  simpa only [primeBasesUpTo, Nat.primesLE_eq_filter_range] using
    Nat.primesLE_card_eq_primeCounting X

theorem log_nat_le_seven_mul_div_320 {A : Nat} (hA : 256 ≤ A) :
    Real.log (A : Real) ≤ 7 * (A : Real) / 320 := by
  have h256mem : (256 : Real) ∈ Set.Ici (Real.exp 1) := by
    exact Real.exp_one_lt_three.le.trans (by norm_num)
  change Real.exp 1 ≤ 256 at h256mem
  have hAmem : (A : Real) ∈ Set.Ici (Real.exp 1) := by
    exact h256mem.trans (by exact_mod_cast hA)
  change Real.exp 1 ≤ (A : Real) at hAmem
  have hratio := Real.log_div_self_antitoneOn h256mem hAmem
    (by exact_mod_cast hA)
  have hlog256 : Real.log (256 : Real) = 8 * Real.log 2 := by
    rw [show (256 : Real) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
  have hconst : Real.log (256 : Real) / 256 ≤ (7 : Real) / 320 := by
    rw [hlog256]
    nlinarith [Real.log_two_lt_d9]
  have hratio' : Real.log (A : Real) / (A : Real) ≤ (7 : Real) / 320 :=
    hratio.trans hconst
  have hApos : (0 : Real) < A := by positivity
  rw [div_le_iff₀ hApos] at hratio'
  nlinarith

theorem log_square_succ_le_square_div_64 {A : Nat} (hA : 256 ≤ A) :
    Real.log (((A : Real) ^ 2) + 1) ≤ (A : Real) ^ 2 / 64 := by
  have hAreal : (256 : Real) ≤ A := by exact_mod_cast hA
  have hApos : (0 : Real) < A := by positivity
  have hXpos : (0 : Real) < (A : Real) ^ 2 := sq_pos_of_pos hApos
  have harg : (A : Real) ^ 2 + 1 ≤ 2 * (A : Real) ^ 2 := by
    nlinarith
  have hlog := Real.log_le_log (by positivity) harg
  have hlogA : Real.log (A : Real) ≤ (A : Real) :=
    Real.log_le_self hApos.le
  have hlogTwo : Real.log 2 ≤ 1 :=
    (Real.log_le_sub_one_of_pos (by norm_num)).trans_eq (by norm_num)
  rw [Real.log_mul (by norm_num) (ne_of_gt hXpos), Real.log_pow] at hlog
  norm_num at hlog
  nlinarith [sq_nonneg ((A : Real) - 256)]

theorem chebyshev_primeBases_square_lower {A : Nat} (hA : 256 ≤ A) :
    (A : Real) ^ 2 ≤
      3 * Real.log (A : Real) *
        ((primeBasesUpTo (A ^ 2)).card : Real) := by
  have hApos : (0 : Real) < A := by positivity
  have hlogApos : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 256) hA))
  have hlogX : Real.log ((A ^ 2 : Nat) : Real) =
      2 * Real.log (A : Real) := by
    simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  have hlogXpos : 0 < Real.log ((A ^ 2 : Nat) : Real) := by
    rw [hlogX]
    positivity
  have hnumLower :
      (2 : Real) * (A : Real) ^ 2 / 3 ≤
        ((A : Real) ^ 2) * Real.log 2 -
          Real.log (((A : Real) ^ 2) + 1) := by
    have hlogTwo : (11 : Real) / 16 ≤ Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    have hmul := mul_le_mul_of_nonneg_left hlogTwo
      (sq_nonneg (A : Real))
    have hsucc := log_square_succ_le_square_div_64 hA
    nlinarith
  have hcheb := Chebyshev.pi_ge (A ^ 2)
  rw [Nat.cast_pow] at hcheb
  have hlogXpos' : 0 < Real.log ((A : Real) ^ 2) := by
    rw [Real.log_pow]
    positivity
  have hnumUpper :
      ((A : Real) ^ 2) * Real.log 2 -
          Real.log (((A : Real) ^ 2) + 1) ≤
        (Nat.primeCounting (A ^ 2) : Real) *
          Real.log ((A : Real) ^ 2) := by
    exact (div_le_iff₀ hlogXpos').mp hcheb
  have hcard := card_primeBasesUpTo_eq_primeCounting (A ^ 2)
  rw [Real.log_pow, ← hcard] at hnumUpper
  norm_num at hnumUpper
  nlinarith

theorem fifteen_mul_le_primeBases_square {A : Nat} (hA : 256 ≤ A) :
    15 * A ≤ (primeBasesUpTo (A ^ 2)).card := by
  have hpi := chebyshev_primeBases_square_lower hA
  have hlog := log_nat_le_seven_mul_div_320 hA
  have hApos : (0 : Real) < A := by positivity
  have hPnonneg : (0 : Real) ≤ (primeBasesUpTo (A ^ 2)).card := by positivity
  have hscaled : (320 : Real) * A ≤
      21 * (primeBasesUpTo (A ^ 2)).card := by
    nlinarith
  exact_mod_cast (show (15 : Real) * A ≤
    (primeBasesUpTo (A ^ 2)).card by nlinarith)

theorem cmHeckeFamily_product_ge_256 {B : Nat}
    (F : CMHeckeFamily B) : 256 ≤ F.blocks.prod id := by
  calc
    256 = 2 ^ 8 := by norm_num
    _ ≤ 2 ^ F.blocks.card :=
      Nat.pow_le_pow_right (by norm_num) F.enough_blocks
    _ ≤ F.blocks.prod id := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod' fun a ha =>
        Nat.succ_le_iff.mpr (F.modulus_gt_one a ha)

def lightUnits (a X g : Nat) [NeZero a] : Finset (ZMod a)ˣ :=
  (heavyUnits a X g)ᶜ

def lightPrimeLifts (a X g : Nat) [NeZero a] : Finset Nat :=
  (lightUnits a X g).biUnion fun u =>
    primesInClass a X (u : ZMod a).val

theorem light_class_card_le
    {a X g : Nat} [NeZero a] {u : (ZMod a)ˣ}
    (hu : u ∈ lightUnits a X g) :
    (primesInClass a X (u : ZMod a).val).card ≤ 4 * g := by
  have hnot : u ∉ heavyUnits a X g := Finset.mem_compl.mp hu
  have hnot' : ¬4 * g ≤
      (primesInClass a X (u : ZMod a).val).card := by
    simpa [heavyUnits] using hnot
  omega

theorem card_lightPrimeLifts_le (a X g : Nat) [NeZero a] :
    (lightPrimeLifts a X g).card ≤ 4 * g * a.totient := by
  have hunion : (lightPrimeLifts a X g).card ≤
      (lightUnits a X g).card * (4 * g) := by
    exact Finset.card_biUnion_le_card_mul _ _ _ fun u hu =>
      light_class_card_le hu
  have hclasses : (lightUnits a X g).card ≤ a.totient := by
    simpa [ZMod.card_units_eq_totient] using
      Finset.card_le_univ (lightUnits a X g)
  calc
    (lightPrimeLifts a X g).card ≤
        (lightUnits a X g).card * (4 * g) := hunion
    _ ≤ a.totient * (4 * g) := Nat.mul_le_mul_right _ hclasses
    _ = 4 * g * a.totient := by ring

def familyLightPrimeLifts {B : Nat} (F : CMHeckeFamily B) :
    Finset Nat :=
  (Finset.univ : Finset F.blocks).biUnion fun a =>
    lightPrimeLifts (a : Nat) F.cutoff
      (primeClassTarget F.blocks F.cutoff (a : Nat))

theorem block_light_scaled_le {B : Nat} (F : CMHeckeFamily B)
    (a : F.blocks) :
    2 * F.blocks.card *
        (lightPrimeLifts (a : Nat) F.cutoff
          (primeClassTarget F.blocks F.cutoff (a : Nat))).card ≤
      (primeBasesUpTo F.cutoff).card := by
  let P := (primeBasesUpTo F.cutoff).card
  let m := F.blocks.card
  let phi := (a : Nat).totient
  let g := primeClassTarget F.blocks F.cutoff (a : Nat)
  have hlight :
      (lightPrimeLifts (a : Nat) F.cutoff g).card ≤ 4 * g * phi :=
    card_lightPrimeLifts_le (a : Nat) F.cutoff g
  have hdiv : g * (8 * m * phi) ≤ P := by
    dsimp [g, primeClassTarget, P, m, phi]
    exact Nat.div_mul_le_self _ _
  dsimp [P, m, phi, g] at hlight hdiv ⊢
  calc
    2 * F.blocks.card *
        (lightPrimeLifts (a : Nat) F.cutoff
          (primeClassTarget F.blocks F.cutoff (a : Nat))).card ≤
        2 * F.blocks.card *
          (4 * primeClassTarget F.blocks F.cutoff (a : Nat) *
            (a : Nat).totient) :=
      Nat.mul_le_mul_left _ hlight
    _ = primeClassTarget F.blocks F.cutoff (a : Nat) *
          (8 * F.blocks.card * (a : Nat).totient) := by ring
    _ ≤ (primeBasesUpTo F.cutoff).card := hdiv

theorem two_mul_familyLight_card_le {B : Nat}
    (F : CMHeckeFamily B) :
    2 * (familyLightPrimeLifts F).card ≤
      (primeBasesUpTo F.cutoff).card := by
  let P := (primeBasesUpTo F.cutoff).card
  let m := F.blocks.card
  have hm : 0 < m := by
    dsimp [m]
    exact lt_of_lt_of_le (by norm_num) F.enough_blocks
  have hsumScaled :
      2 * m *
          (∑ a : F.blocks,
            (lightPrimeLifts (a : Nat) F.cutoff
              (primeClassTarget F.blocks F.cutoff (a : Nat))).card) ≤
        m * P := by
    calc
      2 * m *
          (∑ a : F.blocks,
            (lightPrimeLifts (a : Nat) F.cutoff
              (primeClassTarget F.blocks F.cutoff (a : Nat))).card) =
          ∑ a : F.blocks,
            2 * m *
              (lightPrimeLifts (a : Nat) F.cutoff
                (primeClassTarget F.blocks F.cutoff (a : Nat))).card := by
        rw [Finset.mul_sum]
      _ ≤ ∑ _a : F.blocks, P := by
        exact Finset.sum_le_sum fun a _ha => by
          simpa [m, P] using block_light_scaled_le F a
      _ = m * P := by simp [m]
  have hsum :
      2 * (∑ a : F.blocks,
        (lightPrimeLifts (a : Nat) F.cutoff
          (primeClassTarget F.blocks F.cutoff (a : Nat))).card) ≤ P := by
    apply Nat.le_of_mul_le_mul_left
    · simpa [mul_assoc, mul_left_comm, mul_comm] using hsumScaled
    · exact hm
  have hunion : (familyLightPrimeLifts F).card ≤
      ∑ a : F.blocks,
        (lightPrimeLifts (a : Nat) F.cutoff
          (primeClassTarget F.blocks F.cutoff (a : Nat))).card := by
    exact Finset.card_biUnion_le
  dsimp [P] at hsum ⊢
  exact (Nat.mul_le_mul_left 2 hunion).trans hsum

def nonunitPrimeBases {B : Nat} (F : CMHeckeFamily B) :
    Finset Nat :=
  (primeBasesUpTo F.cutoff).filter fun p =>
    ¬p.Coprime (F.blocks.prod id)

theorem card_nonunitPrimeBases_le {B : Nat}
    (F : CMHeckeFamily B) :
    (nonunitPrimeBases F).card ≤ F.blocks.prod id := by
  let A := F.blocks.prod id
  have hApos : 0 < A := cmHeckeFamily_product_pos F
  have hsub : nonunitPrimeBases F ⊆ Finset.Icc 1 A := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpPrime : p.Prime := (Finset.mem_filter.mp hp'.1).2
    have hpDiv : p ∣ A := by
      by_contra hnot
      exact hp'.2 ((hpPrime.coprime_iff_not_dvd).mpr hnot)
    exact Finset.mem_Icc.mpr
      ⟨hpPrime.one_le, Nat.le_of_dvd hApos hpDiv⟩
  calc
    (nonunitPrimeBases F).card ≤ (Finset.Icc 1 A).card :=
      Finset.card_le_card hsub
    _ = A := by simp
    _ = F.blocks.prod id := rfl

def globalHeavyPrimeLifts {B : Nat} (F : CMHeckeFamily B)
    [NeZero (F.blocks.prod id)] : Finset Nat :=
  (globalHeavyUnits F).biUnion fun u =>
    primesInClass (F.blocks.prod id) F.cutoff
      (u : ZMod (F.blocks.prod id)).val

theorem blockUnitsCRT_unitOfCoprime_apply
    {B : Nat} (F : CMHeckeFamily B)
    [NeZero (F.blocks.prod id)]
    (p : Nat) (hpA : p.Coprime (F.blocks.prod id))
    (a : F.blocks) :
    (((blockUnitsCRT F (ZMod.unitOfCoprime p hpA)) a :
        (ZMod (a : Nat))ˣ) : ZMod (a : Nat)) = p := by
  change (blockRingCRT F (p : ZMod (F.blocks.prod id))) a =
    (p : ZMod (a : Nat))
  exact congrFun (map_natCast (blockRingCRT F) p) a

theorem primeBases_cover {B : Nat} (F : CMHeckeFamily B)
    [NeZero (F.blocks.prod id)] :
    primeBasesUpTo F.cutoff ⊆
      (globalHeavyPrimeLifts F ∪
        familyLightPrimeLifts F) ∪
          nonunitPrimeBases F := by
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpRange : p ∈ Finset.range F.cutoff.succ := hp'.1
  have hpPrime : p.Prime := hp'.2
  let A := F.blocks.prod id
  by_cases hpA : p.Coprime A
  · let u : (ZMod A)ˣ := ZMod.unitOfCoprime p hpA
    by_cases hu : u ∈ globalHeavyUnits F
    · rw [Finset.mem_union]
      left
      rw [Finset.mem_union]
      left
      rw [globalHeavyPrimeLifts]
      refine Finset.mem_biUnion.mpr ⟨u, hu, ?_⟩
      rw [primesInClass, Finset.mem_filter]
      refine ⟨hpRange, hpPrime, ?_⟩
      simpa [u, A, ZMod.val_natCast]
    · rw [Finset.mem_union]
      left
      rw [Finset.mem_union]
      right
      have hnotAll : ¬∀ a : F.blocks,
          (blockUnitsCRT F u) a ∈ blockHeavyUnits F a := by
        intro hall
        apply hu
        rw [globalHeavyUnits, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hall⟩
      push Not at hnotAll
      obtain ⟨a, ha⟩ := hnotAll
      let v : (ZMod (a : Nat))ˣ := (blockUnitsCRT F u) a
      have hvLight : v ∈ lightUnits (a : Nat) F.cutoff
          (primeClassTarget F.blocks F.cutoff (a : Nat)) := by
        rw [lightUnits, Finset.mem_compl]
        simpa [v, blockHeavyUnits] using ha
      rw [familyLightPrimeLifts]
      refine Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, ?_⟩
      rw [lightPrimeLifts]
      refine Finset.mem_biUnion.mpr ⟨v, hvLight, ?_⟩
      rw [primesInClass, Finset.mem_filter]
      refine ⟨hpRange, hpPrime, ?_⟩
      have hvEq := blockUnitsCRT_unitOfCoprime_apply F p hpA a
      have hval := congrArg ZMod.val hvEq
      simpa [v, u, A, ZMod.val_natCast] using hval.symm
  · rw [Finset.mem_union]
    right
    rw [nonunitPrimeBases, Finset.mem_filter]
    exact ⟨hp, hpA⟩

theorem thirteen_mul_primeBases_le_thirty_mul_globalHeavy
    {B : Nat} (F : CMHeckeFamily B)
    [NeZero (F.blocks.prod id)] :
    13 * (primeBasesUpTo F.cutoff).card ≤
      30 * (globalHeavyPrimeLifts F).card := by
  let G := (globalHeavyPrimeLifts F).card
  let L := (familyLightPrimeLifts F).card
  let D := (nonunitPrimeBases F).card
  let P := (primeBasesUpTo F.cutoff).card
  have hcover := Finset.card_le_card (primeBases_cover F)
  have hfirst := Finset.card_union_le
    (globalHeavyPrimeLifts F) (familyLightPrimeLifts F)
  have hsecond := Finset.card_union_le
    (globalHeavyPrimeLifts F ∪ familyLightPrimeLifts F)
    (nonunitPrimeBases F)
  have hPcover : P ≤ G + L + D := by
    dsimp [P, G, L, D]
    omega
  have hlight : 2 * L ≤ P := by
    simpa [L, P] using two_mul_familyLight_card_le F
  have hdividing : D ≤ F.blocks.prod id := by
    simpa [D] using card_nonunitPrimeBases_le F
  have hA256 := cmHeckeFamily_product_ge_256 F
  have hfifteen : 15 * (F.blocks.prod id) ≤ P := by
    dsimp [P]
    rw [F.cutoff_eq]
    exact fifteen_mul_le_primeBases_square hA256
  have hnonunit : 15 * D ≤ P :=
    (Nat.mul_le_mul_left 15 hdividing).trans hfifteen
  omega

theorem primesInProgression_nat_eq_primesInClass
    (X q r : Nat) (hr : r < q) :
    primesInProgressionUpTo (X : Real) q r = primesInClass q X r := by
  ext p
  simp [primesInProgressionUpTo, primesUpTo, primesInClass,
    Nat.mod_eq_of_lt hr, and_assoc]

theorem global_class_brun_scaled
    (hBT : PublishedBrunTitchmarsh)
    {B : Nat} (F : CMHeckeFamily B)
    [NeZero (F.blocks.prod id)]
    (u : (ZMod (F.blocks.prod id))ˣ) :
    ((F.blocks.prod id).totient : Real) *
        Real.log (F.blocks.prod id : Nat) *
          ((primesInClass (F.blocks.prod id) F.cutoff
            (u : ZMod (F.blocks.prod id)).val).card : Real) ≤
      2 * (F.cutoff : Real) := by
  let A := F.blocks.prod id
  have hA256 := cmHeckeFamily_product_ge_256 F
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA256
  have hAone : 1 < A := lt_of_lt_of_le (by norm_num) hA256
  have hvalLt : (u : ZMod A).val < A := ZMod.val_lt _
  have hcop : (u : ZMod A).val.Coprime A :=
    ZMod.val_coe_unit_coprime u
  have hvalPos : 0 < (u : ZMod A).val := by
    apply Nat.pos_of_ne_zero
    intro hv
    have hAeq : A = 1 := by simpa [hv] using hcop
    omega
  have hcutoff : F.cutoff = A ^ 2 := F.cutoff_eq
  have hAltxNat : A < F.cutoff := by
    rw [hcutoff]
    calc
      A = A * 1 := by simp
      _ < A * A := Nat.mul_lt_mul_of_pos_left hAone hApos
      _ = A ^ 2 := by ring
  have hAltx : (A : Real) < F.cutoff := by exact_mod_cast hAltxNat
  have hratio : (F.cutoff : Real) / (A : Real) = (A : Real) := by
    rw [hcutoff, Nat.cast_pow]
    field_simp
  have htotientPos : (0 : Real) < A.totient := by
    exact_mod_cast Nat.totient_pos.mpr hApos
  have hlogPos : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast hAone)
  unfold PublishedBrunTitchmarsh at hBT
  have h := hBT (F.cutoff : Real) A (u : ZMod A).val
    hApos hvalPos hAltx hcop
  rw [primesInProgression_nat_eq_primesInClass
    F.cutoff A (u : ZMod A).val hvalLt, hratio] at h
  have hdenPos : 0 < (A.totient : Real) * Real.log (A : Real) :=
    mul_pos htotientPos hlogPos
  have hscaled := (le_div_iff₀ hdenPos).mp h
  dsimp [A] at hscaled ⊢
  nlinarith

theorem globalHeavyPrimeLifts_brun_scaled
    (hBT : PublishedBrunTitchmarsh)
    {B : Nat} (F : CMHeckeFamily B)
    [NeZero (F.blocks.prod id)] :
    ((F.blocks.prod id).totient : Real) *
        Real.log (F.blocks.prod id : Nat) *
          ((globalHeavyPrimeLifts F).card : Real) ≤
      2 * (F.cutoff : Real) * ((globalHeavyUnits F).card : Real) := by
  have hunion : (globalHeavyPrimeLifts F).card ≤
      ∑ u ∈ globalHeavyUnits F,
        (primesInClass (F.blocks.prod id) F.cutoff
          (u : ZMod (F.blocks.prod id)).val).card := by
    exact Finset.card_biUnion_le
  have hunionReal : ((globalHeavyPrimeLifts F).card : Real) ≤
      ∑ u ∈ globalHeavyUnits F,
        ((primesInClass (F.blocks.prod id) F.cutoff
          (u : ZMod (F.blocks.prod id)).val).card : Real) := by
    exact_mod_cast hunion
  have hfactorNonneg : 0 ≤ ((F.blocks.prod id).totient : Real) *
      Real.log (F.blocks.prod id : Nat) := by positivity
  calc
    ((F.blocks.prod id).totient : Real) *
          Real.log (F.blocks.prod id : Nat) *
          ((globalHeavyPrimeLifts F).card : Real) ≤
        ((F.blocks.prod id).totient : Real) *
          Real.log (F.blocks.prod id : Nat) *
          (∑ u ∈ globalHeavyUnits F,
            ((primesInClass (F.blocks.prod id) F.cutoff
              (u : ZMod (F.blocks.prod id)).val).card : Real)) :=
      mul_le_mul_of_nonneg_left hunionReal hfactorNonneg
    _ = ∑ u ∈ globalHeavyUnits F,
        (((F.blocks.prod id).totient : Real) *
          Real.log (F.blocks.prod id : Nat) *
          ((primesInClass (F.blocks.prod id) F.cutoff
            (u : ZMod (F.blocks.prod id)).val).card : Real)) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _u ∈ globalHeavyUnits F, 2 * (F.cutoff : Real) := by
      exact Finset.sum_le_sum fun u _hu =>
        global_class_brun_scaled hBT F u
    _ = 2 * (F.cutoff : Real) * ((globalHeavyUnits F).card : Real) := by
      simp
      ring

theorem globalHeavyUnits_density
    (hBT : PublishedBrunTitchmarsh)
    {B : Nat} (F : CMHeckeFamily B)
    [NeZero (F.blocks.prod id)] :
    (F.blocks.prod id).totient ≤ 16 * (globalHeavyUnits F).card := by
  let A := F.blocks.prod id
  let X := F.cutoff
  let P := (primeBasesUpTo X).card
  let G := (globalHeavyPrimeLifts F).card
  let H := (globalHeavyUnits F).card
  have hA256 := cmHeckeFamily_product_ge_256 F
  have hAposNat : 0 < A := lt_of_lt_of_le (by norm_num) hA256
  have hAone : 1 < A := lt_of_lt_of_le (by norm_num) hA256
  have hApos : (0 : Real) < A := by exact_mod_cast hAposNat
  have hlogPos : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast hAone)
  have hXeq : (X : Real) = (A : Real) ^ 2 := by
    dsimp [X, A]
    rw [F.cutoff_eq, Nat.cast_pow]
  have hXpos : (0 : Real) < X := by
    rw [hXeq]
    positivity
  have hcheb : (X : Real) ≤ 3 * Real.log (A : Real) * (P : Real) := by
    dsimp [X, A, P]
    simpa [F.cutoff_eq, Nat.cast_pow] using
      chebyshev_primeBases_square_lower hA256
  have hthirteenNat : 13 * P ≤ 30 * G := by
    simpa [P, G] using
      thirteen_mul_primeBases_le_thirty_mul_globalHeavy F
  have hthirteen : (13 : Real) * P ≤ 30 * G := by
    exact_mod_cast hthirteenNat
  have hlogNonneg : 0 ≤ Real.log (A : Real) := hlogPos.le
  have hfirst : (13 : Real) * X ≤
      39 * Real.log (A : Real) * P := by
    have := mul_le_mul_of_nonneg_left hcheb (by norm_num : (0 : Real) ≤ 13)
    nlinarith
  have hsecond : 39 * Real.log (A : Real) * P ≤
      90 * Real.log (A : Real) * G := by
    have := mul_le_mul_of_nonneg_left hthirteen
      (mul_nonneg (by norm_num : (0 : Real) ≤ 3) hlogNonneg)
    nlinarith
  have hXle : (X : Real) ≤
      8 * Real.log (A : Real) * G := by
    nlinarith [hfirst.trans hsecond]
  have hbrun : (A.totient : Real) * Real.log (A : Real) * G ≤
      2 * (X : Real) * H := by
    simpa [A, X, G, H] using
      globalHeavyPrimeLifts_brun_scaled hBT F
  have hphiNonneg : (0 : Real) ≤ A.totient := by positivity
  have hleft : (A.totient : Real) * X ≤
      8 * ((A.totient : Real) * Real.log (A : Real) * G) := by
    have := mul_le_mul_of_nonneg_left hXle hphiNonneg
    nlinarith
  have hscaled : (A.totient : Real) * X ≤
      16 * H * X := by
    calc
      (A.totient : Real) * X ≤
          8 * ((A.totient : Real) * Real.log (A : Real) * G) := hleft
      _ ≤ 8 * (2 * (X : Real) * H) :=
        mul_le_mul_of_nonneg_left hbrun (by norm_num)
      _ = 16 * H * X := by ring
  have hreal : (A.totient : Real) ≤ 16 * H := by
    nlinarith
  exact_mod_cast hreal

theorem brunTitchmarshPrimeLifting_of_published
    (hBT : PublishedBrunTitchmarsh) :
    BrunTitchmarshPrimeLiftingCorollary := by
  intro B F
  letI : NeZero (F.blocks.prod id) :=
    ⟨(cmHeckeFamily_product_pos F).ne'⟩
  have hdensity := globalHeavyUnits_density hBT F
  obtain ⟨a, haHeavy⟩ := exists_seventy_percent_heavy_block F hdensity
  refine ⟨(a : Nat), a.2, ?_⟩
  have haPos : 0 < (a : Nat) :=
    Nat.zero_lt_of_lt (F.modulus_gt_one (a : Nat) a.2)
  have hlift := robust_prime_lifting
    (a := (a : Nat)) (X := F.cutoff)
    (g := primeClassTarget F.blocks F.cutoff (a : Nat))
    haPos
    (by simpa [blockHeavyUnits] using haHeavy)
  exact hlift

#check @globalHeavyUnits_density
#check @brunTitchmarshPrimeLifting_of_published
#print axioms brunTitchmarshPrimeLifting_of_published

end

end K3Lean.BrunTitchmarshReduction
