import K3Lean.BrunTitchmarshReduction
import K3Lean.SourceToPNT
import Mathlib.Data.Int.CardIntervalMod

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Toward prime lifting without Brun--Titchmarsh

This file develops the alternative many-block route.  Instead of bounding a
prime progression by Brun--Titchmarsh, we first use the elementary fact that a
residue class modulo `a` contains at most `(X + 1) / a + 1` integers up to `X`.
The remaining logarithmic density loss can in principle be absorbed by a
growing number of independent CM blocks.
-/

namespace K3Lean.ElementaryPrimeLifting

open K3Lean.BrunTitchmarshReduction
open K3Lean.CMProof
open K3Lean.ErdosBrunTitchmarsh
open K3Lean.FiniteLifting
open K3Lean.SourceToPNT
open scoped BigOperators

noncomputable section

theorem card_primesInClass_le_div_add_one
    {a X r : Nat} (ha : 0 < a) (hr : r < a) :
    (primesInClass a X r).card ≤ (X + 1) / a + 1 := by
  let residueNumbers :=
    (Finset.range (X + 1)).filter (fun n => n ≡ r [MOD a])
  have hsub : primesInClass a X r ⊆ residueNumbers := by
    intro p hp
    have hpParts := Finset.mem_filter.mp hp
    change p ∈ (Finset.range (X + 1)).filter (fun n => n ≡ r [MOD a])
    rw [Finset.mem_filter]
    refine ⟨by simpa using hpParts.1, ?_⟩
    change p % a = r % a
    rw [hpParts.2.2, Nat.mod_eq_of_lt hr]
  calc
    (primesInClass a X r).card ≤ residueNumbers.card :=
      Finset.card_le_card hsub
    _ = (X + 1).count (fun n => n ≡ r [MOD a]) := by
      simp [residueNumbers, Nat.count_eq_card_filter_range]
    _ = (X + 1) / a + if r % a < (X + 1) % a then 1 else 0 :=
      Nat.count_modEq_card (X + 1) ha r
    _ ≤ (X + 1) / a + 1 := by split_ifs <;> omega

theorem card_primesInClass_square_le
    {A r : Nat} (hA : 1 < A) (hr : r < A) :
    (primesInClass A (A ^ 2) r).card ≤ A + 1 := by
  have h := card_primesInClass_le_div_add_one (X := A ^ 2) hA.pos hr
  have hdiv : (A ^ 2 + 1) / A = A := by
    rw [show A ^ 2 + 1 = A * A + 1 by ring,
      Nat.mul_add_div hA.pos, Nat.div_eq_of_lt hA]
    simp
  simpa [hdiv] using h

theorem globalHeavyPrimeLifts_card_le_elementary
    {B : Nat} (F : CMHeckeFamily B)
    [NeZero (F.blocks.prod id)] :
    (globalHeavyPrimeLifts F).card ≤
      (F.blocks.prod id + 1) * (globalHeavyUnits F).card := by
  let A := F.blocks.prod id
  have hA256 := cmHeckeFamily_product_ge_256 F
  have hAone : 1 < A := lt_of_lt_of_le (by norm_num) hA256
  have hunion : (globalHeavyPrimeLifts F).card ≤
      ∑ u ∈ globalHeavyUnits F,
        (primesInClass A F.cutoff (u : ZMod A).val).card :=
    Finset.card_biUnion_le
  calc
    (globalHeavyPrimeLifts F).card ≤
        ∑ u ∈ globalHeavyUnits F,
          (primesInClass A F.cutoff (u : ZMod A).val).card := hunion
    _ = ∑ u ∈ globalHeavyUnits F,
          (primesInClass A (A ^ 2) (u : ZMod A).val).card := by
      rw [F.cutoff_eq]
    _ ≤ ∑ _u ∈ globalHeavyUnits F, (A + 1) := by
      refine Finset.sum_le_sum fun u _hu => ?_
      exact card_primesInClass_square_le hAone (ZMod.val_lt _)
    _ = (A + 1) * (globalHeavyUnits F).card := by
      simp [Nat.mul_comm]
    _ = (F.blocks.prod id + 1) * (globalHeavyUnits F).card := rfl

theorem square_le_three_binaryLog_mul_primeBases
    {A : Nat} (hA : 256 ≤ A) :
    A ^ 2 ≤
      3 * (Nat.log 2 A + 1) * (primeBasesUpTo (A ^ 2)).card := by
  have hcheb := chebyshev_primeBases_square_lower hA
  have hlog := real_log_nat_le_succ_log_two A
  have hPnonneg : (0 : Real) ≤ (primeBasesUpTo (A ^ 2)).card := by
    positivity
  have hreal : (A : Real) ^ 2 ≤
      3 * ((Nat.log 2 A + 1 : Nat) : Real) *
        ((primeBasesUpTo (A ^ 2)).card : Real) := by
    calc
      (A : Real) ^ 2 ≤
          3 * Real.log (A : Real) *
            ((primeBasesUpTo (A ^ 2)).card : Real) := hcheb
      _ ≤ 3 * ((Nat.log 2 A + 1 : Nat) : Real) *
            ((primeBasesUpTo (A ^ 2)).card : Real) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog (by norm_num)) hPnonneg
  exact_mod_cast hreal

/--
Without Brun--Titchmarsh, every global residue class has the elementary bound
`A + 1`.  Chebyshev's theorem then still forces global heavy tuples, with only
the explicit logarithmic loss `14 * (log₂ A + 1)`.
-/
theorem globalHeavyUnits_density_elementary
    {B : Nat} (F : CMHeckeFamily B)
    [NeZero (F.blocks.prod id)] :
    (F.blocks.prod id).totient ≤
      (14 * (Nat.log 2 (F.blocks.prod id) + 1)) *
        (globalHeavyUnits F).card := by
  let A := F.blocks.prod id
  let P := (primeBasesUpTo F.cutoff).card
  let G := (globalHeavyPrimeLifts F).card
  let H := (globalHeavyUnits F).card
  let L := Nat.log 2 A + 1
  have hA256 := cmHeckeFamily_product_ge_256 F
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA256
  have hcheb : A ^ 2 ≤ 3 * L * P := by
    dsimp [P, L, A]
    rw [F.cutoff_eq]
    exact square_le_three_binaryLog_mul_primeBases hA256
  have hprimeHeavy : 13 * P ≤ 30 * G := by
    simpa [P, G] using
      thirteen_mul_primeBases_le_thirty_mul_globalHeavy F
  have hclass : G ≤ (A + 1) * H := by
    simpa [A, G, H] using globalHeavyPrimeLifts_card_le_elementary F
  have hAp1 : A + 1 ≤ 2 * A := by omega
  have hfirst : 13 * A ^ 2 ≤ 39 * L * P := by
    calc
      13 * A ^ 2 ≤ 13 * (3 * L * P) := Nat.mul_le_mul_left 13 hcheb
      _ = 39 * L * P := by ring
  have hsecond : 39 * L * P ≤ 90 * L * G := by
    calc
      39 * L * P = 3 * L * (13 * P) := by ring
      _ ≤ 3 * L * (30 * G) := Nat.mul_le_mul_left _ hprimeHeavy
      _ = 90 * L * G := by ring
  have hthird : 90 * L * G ≤ 180 * L * A * H := by
    calc
      90 * L * G ≤ 90 * L * ((A + 1) * H) :=
        Nat.mul_le_mul_left _ hclass
      _ ≤ 90 * L * ((2 * A) * H) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right H hAp1)
      _ = 180 * L * A * H := by ring
  have hbig : 13 * A ^ 2 ≤ 180 * L * A * H :=
    hfirst.trans (hsecond.trans hthird)
  have hcancelForm : A * (13 * A) ≤ A * (180 * L * H) := by
    calc
      A * (13 * A) = 13 * A ^ 2 := by ring
      _ ≤ 180 * L * A * H := hbig
      _ = A * (180 * L * H) := by ring
  have hthirteen : 13 * A ≤ 180 * L * H :=
    Nat.le_of_mul_le_mul_left hcancelForm hApos
  have hscaled : 13 * A ≤ 13 * (14 * L * H) := by
    calc
      13 * A ≤ 180 * L * H := hthirteen
      _ ≤ 182 * L * H := by
        simpa only [Nat.mul_assoc] using
          (Nat.mul_le_mul_right (L * H) (show 180 ≤ 182 by norm_num))
      _ = 13 * (14 * L * H) := by ring
  have hA : A ≤ 14 * L * H :=
    Nat.le_of_mul_le_mul_left hscaled (by norm_num)
  exact (Nat.totient_le A).trans (by simpa [A, L, H] using hA)

/--
Once a family has enough blocks to absorb the explicit logarithmic factor,
prime lifting is completely elementary: no theorem about primes in arithmetic
progressions is used.
-/
theorem elementaryPrimeLifting_of_selector_power
    {B : Nat} (F : CMHeckeFamily B)
    (hpower :
      (14 * (Nat.log 2 (F.blocks.prod id) + 1)) *
          7 ^ F.blocks.card ≤ 10 ^ F.blocks.card) :
    ∃ a ∈ F.blocks,
      (localCubeSolutions a).card *
          (primeClassTarget F.blocks F.cutoff a) ^ 3 ≤
        (blockPrimeTriples a F.cutoff).card := by
  letI : NeZero (F.blocks.prod id) :=
    ⟨(cmHeckeFamily_product_pos F).ne'⟩
  have hdensity := globalHeavyUnits_density_elementary F
  obtain ⟨a, haHeavy⟩ :=
    exists_seventy_percent_heavy_block_of_factor F
      (14 * (Nat.log 2 (F.blocks.prod id) + 1)) hdensity hpower
  refine ⟨(a : Nat), a.2, ?_⟩
  have haPos : 0 < (a : Nat) :=
    Nat.zero_lt_of_lt (F.modulus_gt_one (a : Nat) a.2)
  exact robust_prime_lifting
    (a := (a : Nat)) (X := F.cutoff)
    (g := primeClassTarget F.blocks F.cutoff (a : Nat))
    haPos (by simpa [blockHeavyUnits] using haHeavy)

#check @card_primesInClass_le_div_add_one
#check @card_primesInClass_square_le
#check @globalHeavyPrimeLifts_card_le_elementary
#check @square_le_three_binaryLog_mul_primeBases
#check @globalHeavyUnits_density_elementary
#check @elementaryPrimeLifting_of_selector_power
#print axioms elementaryPrimeLifting_of_selector_power

end

end K3Lean.ElementaryPrimeLifting
