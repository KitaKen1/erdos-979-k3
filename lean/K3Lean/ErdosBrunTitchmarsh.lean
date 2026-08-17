import K3Lean.LocalMultiplicativity
import K3Lean.PublishedInputs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Data.ZMod.QuotientRing

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# The Erdos--Brun--Titchmarsh route for k = 3

This file develops the finite block-selection argument used by Erdos for
squares in 1937, with the local square congruence replaced by the Fermat
cubic congruence.  Its intended external prime-distribution input is only the
ordinary Brun--Titchmarsh theorem; Mathlib's explicit Chebyshev lower bound
supplies the total number of primes.
-/

namespace K3Lean.ErdosBrunTitchmarsh

open Filter Set
open K3Lean.CMProof
open K3Lean.Expanded
open K3Lean.FiniteLifting
open K3Lean.LocalMultiplicativity
open K3Lean.PublishedInputs
open scoped BigOperators Nat.Prime Topology

noncomputable section

abbrev UTriple (a : Nat) := (ZMod a)ˣ × (ZMod a)ˣ × (ZMod a)ˣ

def IsUnitLocalCubeSolution (a : Nat) (t : UTriple a) : Prop :=
  ((t.1 : ZMod a) ^ 3 + (t.2.1 : ZMod a) ^ 3 +
    (t.2.2 : ZMod a) ^ 3) = 0

abbrev UnitLocalCubeSolution (a : Nat) :=
  {t : UTriple a // IsUnitLocalCubeSolution a t}

abbrev UnitLocalFirstFiber (a : Nat) (r : (ZMod a)ˣ) :=
  {yz : (ZMod a)ˣ × (ZMod a)ˣ //
    ((r : ZMod a) ^ 3 + (yz.1 : ZMod a) ^ 3 +
      (yz.2 : ZMod a) ^ 3) = 0}

noncomputable instance (a : Nat) [NeZero a] :
    Fintype (UnitLocalCubeSolution a) := Fintype.ofFinite _

noncomputable instance (a : Nat) [NeZero a] (r : (ZMod a)ˣ) :
    Fintype (UnitLocalFirstFiber a r) := Fintype.ofFinite _

def zLocalUnitEquiv (a : Nat) :
    ZLocalCubeSolution a ≃ UnitLocalCubeSolution a where
  toFun t :=
    ⟨(t.2.1.unit, t.2.2.1.unit, t.2.2.2.1.unit), by
      simpa [IsUnitLocalCubeSolution, IsUnit.unit_spec] using t.2.2.2.2⟩
  invFun t :=
    ⟨((t.1.1 : ZMod a), (t.1.2.1 : ZMod a), (t.1.2.2 : ZMod a)),
      ⟨t.1.1.isUnit, t.1.2.1.isUnit, t.1.2.2.isUnit,
        by simpa [IsUnitLocalCubeSolution] using t.2⟩⟩
  left_inv t := by
    apply Subtype.ext
    ext <;> simp
  right_inv t := by
    apply Subtype.ext
    ext <;> simp

def unitLocalSigmaEquiv (a : Nat) :
    UnitLocalCubeSolution a ≃
      Σ r : (ZMod a)ˣ, UnitLocalFirstFiber a r where
  toFun t := ⟨t.1.1, ⟨(t.1.2.1, t.1.2.2), t.2⟩⟩
  invFun t := ⟨(t.1, t.2.1.1, t.2.1.2), t.2.2⟩
  left_inv t := by cases t; rfl
  right_inv t := by cases t with | mk r yz => cases yz; rfl

/-- Divide all coordinates by the first unit. -/
def unitLocalFirstFiberEquivOne (a : Nat) [NeZero a]
    (r : (ZMod a)ˣ) :
    UnitLocalFirstFiber a r ≃ UnitLocalFirstFiber a 1 where
  toFun yz :=
    ⟨(r⁻¹ * yz.1.1, r⁻¹ * yz.1.2), by
      have h := yz.2
      change (1 : ZMod a) ^ 3 +
          ((↑(r⁻¹ * yz.1.1) : ZMod a) ^ 3) +
          ((↑(r⁻¹ * yz.1.2) : ZMod a) ^ 3) = 0
      have hrpow :
          ((r⁻¹ : (ZMod a)ˣ) : ZMod a) ^ 3 * (r : ZMod a) ^ 3 = 1 := by
        rw [← mul_pow]
        simp
      have hscaled :
          (1 : ZMod a) ^ 3 + ((↑(r⁻¹ * yz.1.1) : ZMod a) ^ 3) +
              ((↑(r⁻¹ * yz.1.2) : ZMod a) ^ 3) =
              ((r⁻¹ : (ZMod a)ˣ) : ZMod a) ^ 3 *
                ((r : ZMod a) ^ 3 + (yz.1.1 : ZMod a) ^ 3 +
                  (yz.1.2 : ZMod a) ^ 3) := by
        rw [mul_add, mul_add, hrpow]
        simp [mul_pow]
      rw [hscaled, h, mul_zero]
    ⟩
  invFun yz :=
    ⟨(r * yz.1.1, r * yz.1.2), by
      have h := yz.2
      have h' : (1 : ZMod a) ^ 3 + (yz.1.1 : ZMod a) ^ 3 +
          (yz.1.2 : ZMod a) ^ 3 = 0 := by
        simpa using h
      change (r : ZMod a) ^ 3 +
          ((↑(r * yz.1.1) : ZMod a) ^ 3) +
          ((↑(r * yz.1.2) : ZMod a) ^ 3) = 0
      have hscaled :
          (r : ZMod a) ^ 3 + ((↑(r * yz.1.1) : ZMod a) ^ 3) +
              ((↑(r * yz.1.2) : ZMod a) ^ 3) =
              (r : ZMod a) ^ 3 *
                ((1 : ZMod a) ^ 3 + (yz.1.1 : ZMod a) ^ 3 +
                  (yz.1.2 : ZMod a) ^ 3) := by
        simp [mul_add, mul_pow]
      rw [hscaled, h', mul_zero]
    ⟩
  left_inv yz := by
    apply Subtype.ext
    ext <;> simp
  right_inv yz := by
    apply Subtype.ext
    ext <;> simp

theorem card_unitLocalFirstFiber_eq (a : Nat) [NeZero a]
    (r s : (ZMod a)ˣ) :
    Fintype.card (UnitLocalFirstFiber a r) =
      Fintype.card (UnitLocalFirstFiber a s) := by
  exact Fintype.card_congr
    ((unitLocalFirstFiberEquivOne a r).trans
      (unitLocalFirstFiberEquivOne a s).symm)

theorem card_unitLocalCubeSolution_eq_sum_fibers (a : Nat) [NeZero a] :
    Fintype.card (UnitLocalCubeSolution a) =
      ∑ r : (ZMod a)ˣ, Fintype.card (UnitLocalFirstFiber a r) := by
  rw [Fintype.card_congr (unitLocalSigmaEquiv a), Fintype.card_sigma]

abbrev UnitLocalFirstRestricted (a : Nat) (H : Finset (ZMod a)ˣ) :=
  {t : UnitLocalCubeSolution a // t.1.1 ∈ H}

noncomputable instance (a : Nat) [NeZero a] (H : Finset (ZMod a)ˣ) :
    Fintype (UnitLocalFirstRestricted a H) := Fintype.ofFinite _

def unitLocalFirstRestrictedSigmaEquiv
    (a : Nat) (H : Finset (ZMod a)ˣ) :
    UnitLocalFirstRestricted a H ≃
      Σ r : {u : (ZMod a)ˣ // u ∈ H}, UnitLocalFirstFiber a r.1 where
  toFun t := ⟨⟨t.1.1.1, t.2⟩, ⟨(t.1.1.2.1, t.1.1.2.2), t.1.2⟩⟩
  invFun t := ⟨⟨(t.1.1, t.2.1.1, t.2.1.2), t.2.2⟩, t.1.2⟩
  left_inv t := by cases t with | mk t ht => cases t; rfl
  right_inv t := by cases t with | mk r yz => cases r; cases yz; rfl

theorem card_unitLocalFirstRestricted
    (a : Nat) [NeZero a] (H : Finset (ZMod a)ˣ) :
    Fintype.card (UnitLocalFirstRestricted a H) =
      H.card * Fintype.card (UnitLocalFirstFiber a 1) := by
  rw [Fintype.card_congr (unitLocalFirstRestrictedSigmaEquiv a H),
    Fintype.card_sigma]
  simp_rw [card_unitLocalFirstFiber_eq a _ 1]
  simp

theorem card_unitLocalCubeSolution
    (a : Nat) [NeZero a] :
    Fintype.card (UnitLocalCubeSolution a) =
      Fintype.card ((ZMod a)ˣ) *
        Fintype.card (UnitLocalFirstFiber a 1) := by
  rw [card_unitLocalCubeSolution_eq_sum_fibers]
  simp_rw [card_unitLocalFirstFiber_eq a _ 1]
  simp

theorem card_unitLocalFirstRestricted_balance
    (a : Nat) [NeZero a] (H : Finset (ZMod a)ˣ) :
    Fintype.card ((ZMod a)ˣ) *
        Fintype.card (UnitLocalFirstRestricted a H) =
      H.card * Fintype.card (UnitLocalCubeSolution a) := by
  rw [card_unitLocalFirstRestricted, card_unitLocalCubeSolution]
  ring

def unitLocalGood (a : Nat) [NeZero a] (H : Finset (ZMod a)ˣ) :
    Finset (UnitLocalCubeSolution a) :=
  Finset.univ.filter fun t =>
    t.1.1 ∈ H ∧ t.1.2.1 ∈ H ∧ t.1.2.2 ∈ H

def unitLocalBadFirst (a : Nat) [NeZero a] (H : Finset (ZMod a)ˣ) :
    Finset (UnitLocalCubeSolution a) :=
  Finset.univ.filter fun t => t.1.1 ∉ H

def unitLocalBadSecond (a : Nat) [NeZero a] (H : Finset (ZMod a)ˣ) :
    Finset (UnitLocalCubeSolution a) :=
  Finset.univ.filter fun t => t.1.2.1 ∉ H

def unitLocalBadThird (a : Nat) [NeZero a] (H : Finset (ZMod a)ˣ) :
    Finset (UnitLocalCubeSolution a) :=
  Finset.univ.filter fun t => t.1.2.2 ∉ H

theorem card_unitLocalBadFirst_balance
    (a : Nat) [NeZero a] (H : Finset (ZMod a)ˣ) :
    a.totient * (unitLocalBadFirst a H).card =
      (a.totient - H.card) * Fintype.card (UnitLocalCubeSolution a) := by
  have hbalance := card_unitLocalFirstRestricted_balance a Hᶜ
  rw [ZMod.card_units_eq_totient] at hbalance
  have hrestricted :
      Fintype.card (UnitLocalFirstRestricted a Hᶜ) =
        (unitLocalBadFirst a H).card := by
    rw [Fintype.card_subtype]
    simp [unitLocalBadFirst]
  rw [hrestricted, Finset.card_compl, ZMod.card_units_eq_totient] at hbalance
  exact hbalance

def unitLocalSwap12 (a : Nat) :
    UnitLocalCubeSolution a ≃ UnitLocalCubeSolution a where
  toFun t := ⟨(t.1.2.1, t.1.1, t.1.2.2), by
    simpa [IsUnitLocalCubeSolution, add_comm, add_left_comm, add_assoc] using t.2⟩
  invFun t := ⟨(t.1.2.1, t.1.1, t.1.2.2), by
    simpa [IsUnitLocalCubeSolution, add_comm, add_left_comm, add_assoc] using t.2⟩
  left_inv t := by cases t; rfl
  right_inv t := by cases t; rfl

def unitLocalSwap13 (a : Nat) :
    UnitLocalCubeSolution a ≃ UnitLocalCubeSolution a where
  toFun t := ⟨(t.1.2.2, t.1.2.1, t.1.1), by
    simpa [IsUnitLocalCubeSolution, add_comm, add_left_comm, add_assoc] using t.2⟩
  invFun t := ⟨(t.1.2.2, t.1.2.1, t.1.1), by
    simpa [IsUnitLocalCubeSolution, add_comm, add_left_comm, add_assoc] using t.2⟩
  left_inv t := by cases t; rfl
  right_inv t := by cases t; rfl

def unitLocalBadSecondEquivBadFirst
    (a : Nat) [NeZero a] (H : Finset (ZMod a)ˣ) :
    {t // t ∈ unitLocalBadSecond a H} ≃
      {t // t ∈ unitLocalBadFirst a H} where
  toFun t := ⟨unitLocalSwap12 a t.1, by
    have ht : t.1.1.2.1 ∉ H := (Finset.mem_filter.mp t.2).2
    rw [unitLocalBadFirst, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa [unitLocalSwap12] using ht⟩⟩
  invFun t := ⟨unitLocalSwap12 a t.1, by
    have ht : t.1.1.1 ∉ H := (Finset.mem_filter.mp t.2).2
    rw [unitLocalBadSecond, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa [unitLocalSwap12] using ht⟩⟩
  left_inv t := by cases t; rfl
  right_inv t := by cases t; rfl

def unitLocalBadThirdEquivBadFirst
    (a : Nat) [NeZero a] (H : Finset (ZMod a)ˣ) :
    {t // t ∈ unitLocalBadThird a H} ≃
      {t // t ∈ unitLocalBadFirst a H} where
  toFun t := ⟨unitLocalSwap13 a t.1, by
    have ht : t.1.1.2.2 ∉ H := (Finset.mem_filter.mp t.2).2
    rw [unitLocalBadFirst, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa [unitLocalSwap13] using ht⟩⟩
  invFun t := ⟨unitLocalSwap13 a t.1, by
    have ht : t.1.1.1 ∉ H := (Finset.mem_filter.mp t.2).2
    rw [unitLocalBadThird, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa [unitLocalSwap13] using ht⟩⟩
  left_inv t := by cases t; rfl
  right_inv t := by cases t; rfl

theorem card_unitLocalBadSecond_eq_first
    (a : Nat) [NeZero a] (H : Finset (ZMod a)ˣ) :
    (unitLocalBadSecond a H).card = (unitLocalBadFirst a H).card := by
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (unitLocalBadSecondEquivBadFirst a H)

theorem card_unitLocalBadThird_eq_first
    (a : Nat) [NeZero a] (H : Finset (ZMod a)ˣ) :
    (unitLocalBadThird a H).card = (unitLocalBadFirst a H).card := by
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (unitLocalBadThirdEquivBadFirst a H)

theorem ten_mul_card_unitLocalBadFirst_le
    {a : Nat} [NeZero a] (H : Finset (ZMod a)ˣ)
    (hH : 7 * a.totient ≤ 10 * H.card) :
    10 * (unitLocalBadFirst a H).card ≤
      3 * Fintype.card (UnitLocalCubeSolution a) := by
  have hHle : H.card ≤ a.totient := by
    simpa [ZMod.card_units_eq_totient] using Finset.card_le_univ H
  have hcomplement : 10 * (a.totient - H.card) ≤ 3 * a.totient := by
    omega
  have hscaled := Nat.mul_le_mul_right
    (Fintype.card (UnitLocalCubeSolution a)) hcomplement
  have hbalance := card_unitLocalBadFirst_balance a H
  have htotientPos : 0 < a.totient := Nat.totient_pos.mpr (NeZero.pos a)
  apply Nat.le_of_mul_le_mul_left
    (by
      calc
        a.totient * (10 * (unitLocalBadFirst a H).card) =
            10 * ((a.totient - H.card) *
              Fintype.card (UnitLocalCubeSolution a)) := by
          rw [← hbalance]
          ring
        _ ≤ 3 * (a.totient *
              Fintype.card (UnitLocalCubeSolution a)) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
        _ = a.totient *
              (3 * Fintype.card (UnitLocalCubeSolution a)) := by ring)
    htotientPos

/-- Deleting at most 30 percent of the unit classes in each coordinate
removes at most 90 percent of the diagonally homogeneous local solutions. -/
theorem local_good_tenth
    {a : Nat} [NeZero a] (H : Finset (ZMod a)ˣ)
    (hH : 7 * a.totient ≤ 10 * H.card) :
    Fintype.card (UnitLocalCubeSolution a) ≤
      10 * (unitLocalGood a H).card := by
  let R := Fintype.card (UnitLocalCubeSolution a)
  let G := (unitLocalGood a H).card
  let B₁ := (unitLocalBadFirst a H).card
  let B₂ := (unitLocalBadSecond a H).card
  let B₃ := (unitLocalBadThird a H).card
  have hcover : (Finset.univ : Finset (UnitLocalCubeSolution a)) ⊆
      unitLocalGood a H ∪ unitLocalBadFirst a H ∪
        unitLocalBadSecond a H ∪ unitLocalBadThird a H := by
    intro t _ht
    by_cases h1 : t.1.1 ∈ H <;>
      by_cases h2 : t.1.2.1 ∈ H <;>
        by_cases h3 : t.1.2.2 ∈ H <;>
          simp [unitLocalGood, unitLocalBadFirst, unitLocalBadSecond,
            unitLocalBadThird, h1, h2, h3]
  have hcount : R ≤ G + B₁ + B₂ + B₃ := by
    dsimp [R, G, B₁, B₂, B₃]
    calc
      Fintype.card (UnitLocalCubeSolution a) =
          (Finset.univ : Finset (UnitLocalCubeSolution a)).card := by simp
      _ ≤ (unitLocalGood a H ∪ unitLocalBadFirst a H ∪
          unitLocalBadSecond a H ∪ unitLocalBadThird a H).card :=
        Finset.card_le_card hcover
      _ ≤ (unitLocalGood a H).card + (unitLocalBadFirst a H).card +
          (unitLocalBadSecond a H).card + (unitLocalBadThird a H).card := by
        have h₁ := Finset.card_union_le
          (unitLocalGood a H) (unitLocalBadFirst a H)
        have h₂ := Finset.card_union_le
          (unitLocalGood a H ∪ unitLocalBadFirst a H)
          (unitLocalBadSecond a H)
        have h₃ := Finset.card_union_le
          (unitLocalGood a H ∪ unitLocalBadFirst a H ∪
            unitLocalBadSecond a H) (unitLocalBadThird a H)
        omega
  have hB₁ : 10 * B₁ ≤ 3 * R := by
    simpa [B₁, R] using ten_mul_card_unitLocalBadFirst_le H hH
  have hB₂ : 10 * B₂ ≤ 3 * R := by
    simpa [B₂, B₁, R, card_unitLocalBadSecond_eq_first] using hB₁
  have hB₃ : 10 * B₃ ≤ 3 * R := by
    simpa [B₃, B₁, R, card_unitLocalBadThird_eq_first] using hB₁
  omega

def heavyUnits (a X g : Nat) [NeZero a] : Finset (ZMod a)ˣ :=
  Finset.univ.filter fun u =>
    4 * g ≤ (primesInClass a X (u : ZMod a).val).card

def unitResidueLifts {a : Nat} [NeZero a] (X : Nat)
    (t : UnitLocalCubeSolution a) : Finset Triple :=
  (primesInClass a X (t.1.1 : ZMod a).val) ×ˢ
    (primesInClass a X (t.1.2.1 : ZMod a).val) ×ˢ
      (primesInClass a X (t.1.2.2 : ZMod a).val)

theorem pairwiseDisjoint_unitResidueLifts
    {a X : Nat} [NeZero a]
    (S : Finset (UnitLocalCubeSolution a)) :
    ((S : Set (UnitLocalCubeSolution a))).PairwiseDisjoint
      (unitResidueLifts X) := by
  intro r _hr s _hs hrs
  change Disjoint (unitResidueLifts X r) (unitResidueLifts X s)
  rw [Finset.disjoint_left]
  intro p hpr hps
  simp only [unitResidueLifts, Finset.mem_product] at hpr hps
  have h1val : (r.1.1 : ZMod a).val = (s.1.1 : ZMod a).val := by
    exact (Finset.mem_filter.mp hpr.1).2.2.symm.trans
      (Finset.mem_filter.mp hps.1).2.2
  have h2val : (r.1.2.1 : ZMod a).val = (s.1.2.1 : ZMod a).val := by
    exact (Finset.mem_filter.mp hpr.2.1).2.2.symm.trans
      (Finset.mem_filter.mp hps.2.1).2.2
  have h3val : (r.1.2.2 : ZMod a).val = (s.1.2.2 : ZMod a).val := by
    exact (Finset.mem_filter.mp hpr.2.2).2.2.symm.trans
      (Finset.mem_filter.mp hps.2.2).2.2
  have h1 : r.1.1 = s.1.1 := by
    apply Units.ext
    exact ZMod.val_injective a h1val
  have h2 : r.1.2.1 = s.1.2.1 := by
    apply Units.ext
    exact ZMod.val_injective a h2val
  have h3 : r.1.2.2 = s.1.2.2 := by
    apply Units.ext
    exact ZMod.val_injective a h3val
  apply hrs
  apply Subtype.ext
  exact Prod.ext h1 (Prod.ext h2 h3)

def allHeavyUnitLifts (a X g : Nat) [NeZero a] : Finset Triple :=
  (unitLocalGood a (heavyUnits a X g)).biUnion (unitResidueLifts X)

theorem card_allHeavyUnitLifts (a X g : Nat) [NeZero a] :
    (allHeavyUnitLifts a X g).card =
      ∑ t ∈ unitLocalGood a (heavyUnits a X g),
        (unitResidueLifts X t).card := by
  rw [allHeavyUnitLifts,
    Finset.card_biUnion (pairwiseDisjoint_unitResidueLifts _)]

theorem heavy_four_mul_le_card_class
    {a X g : Nat} [NeZero a] {u : (ZMod a)ˣ}
    (hu : u ∈ heavyUnits a X g) :
    4 * g ≤ (primesInClass a X (u : ZMod a).val).card := by
  exact (Finset.mem_filter.mp hu).2

theorem heavy_lift_card_lower
    {a X g : Nat} [NeZero a]
    {t : UnitLocalCubeSolution a}
    (ht : t ∈ unitLocalGood a (heavyUnits a X g)) :
    (4 * g) ^ 3 ≤ (unitResidueLifts X t).card := by
  have ht' := (Finset.mem_filter.mp ht).2
  have h1 := heavy_four_mul_le_card_class ht'.1
  have h2 := heavy_four_mul_le_card_class ht'.2.1
  have h3 := heavy_four_mul_le_card_class ht'.2.2
  simpa [unitResidueLifts, Finset.card_product, pow_succ,
    Nat.mul_assoc] using Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

theorem good_mul_cube_le_allHeavyUnitLifts
    (a X g : Nat) [NeZero a] :
    (unitLocalGood a (heavyUnits a X g)).card * (4 * g) ^ 3 ≤
      (allHeavyUnitLifts a X g).card := by
  rw [card_allHeavyUnitLifts]
  calc
    (unitLocalGood a (heavyUnits a X g)).card * (4 * g) ^ 3 =
        ∑ _t ∈ unitLocalGood a (heavyUnits a X g), (4 * g) ^ 3 := by
      simp
    _ ≤ ∑ t ∈ unitLocalGood a (heavyUnits a X g),
        (unitResidueLifts X t).card :=
      Finset.sum_le_sum fun t ht => heavy_lift_card_lower ht

theorem allHeavyUnitLifts_subset_orderedBlockPrimeTriples
    (a X g : Nat) [NeZero a] :
    allHeavyUnitLifts a X g ⊆ orderedBlockPrimeTriples a X := by
  intro p hp
  obtain ⟨t, ht, hpt⟩ := Finset.mem_biUnion.mp hp
  simp only [unitResidueLifts, Finset.mem_product] at hpt
  have hp1 := Finset.mem_filter.mp hpt.1
  have hp2 := Finset.mem_filter.mp hpt.2.1
  have hp3 := Finset.mem_filter.mp hpt.2.2
  have hcast1 : ((p.1 : Nat) : ZMod a) = (t.1.1 : ZMod a) := by
    rw [← ZMod.natCast_mod p.1 a, hp1.2.2, ZMod.natCast_zmod_val]
  have hcast2 : ((p.2.1 : Nat) : ZMod a) = (t.1.2.1 : ZMod a) := by
    rw [← ZMod.natCast_mod p.2.1 a, hp2.2.2, ZMod.natCast_zmod_val]
  have hcast3 : ((p.2.2 : Nat) : ZMod a) = (t.1.2.2 : ZMod a) := by
    rw [← ZMod.natCast_mod p.2.2 a, hp3.2.2, ZMod.natCast_zmod_val]
  have hzero : ((cubeSum p : Nat) : ZMod a) = 0 := by
    simpa [cubeSum, hcast1, hcast2, hcast3,
      IsUnitLocalCubeSolution] using t.2
  have hdiv : a ∣ cubeSum p :=
    (ZMod.natCast_eq_zero_iff _ _).mp hzero
  rw [orderedBlockPrimeTriples, Finset.mem_filter]
  constructor
  · simp only [box, Finset.mem_product, Finset.mem_range]
    exact ⟨Finset.mem_range.mp hp1.1,
      Finset.mem_range.mp hp2.1, Finset.mem_range.mp hp3.1⟩
  · exact ⟨hp1.2.1, hp2.2.1, hp3.2.1, hdiv⟩

theorem card_unitLocalCubeSolution_eq_localCubeSolutions
    {a : Nat} [NeZero a] (ha : 0 < a) :
    Fintype.card (UnitLocalCubeSolution a) =
      (localCubeSolutions a).card := by
  calc
    Fintype.card (UnitLocalCubeSolution a) =
        Fintype.card (ZLocalCubeSolution a) :=
      Fintype.card_congr (zLocalUnitEquiv a).symm
    _ = (localCubeSolutions a).card :=
      (card_localCubeSolutions_eq_fintype ha).symm

/-- A 70 percent set of classes, each containing at least `4g` primes,
already gives the full lifting lower bound after the permutation loss. -/
theorem robust_prime_lifting
    {a X g : Nat} [NeZero a]
    (ha : 0 < a)
    (hheavy : 7 * a.totient ≤ 10 * (heavyUnits a X g).card) :
    (localCubeSolutions a).card * g ^ 3 ≤
      (blockPrimeTriples a X).card := by
  let R := (localCubeSolutions a).card
  let G := (unitLocalGood a (heavyUnits a X g)).card
  let L := (allHeavyUnitLifts a X g).card
  let P := (blockPrimeTriples a X).card
  have hRG : R ≤ 10 * G := by
    dsimp [R]
    rw [← card_unitLocalCubeSolution_eq_localCubeSolutions ha]
    simpa [G] using local_good_tenth (heavyUnits a X g) hheavy
  have hGL : G * (4 * g) ^ 3 ≤ L := by
    simpa [G, L] using good_mul_cube_le_allHeavyUnitLifts a X g
  have hLP : L ≤ 6 * P := by
    dsimp [L, P]
    exact (Finset.card_le_card
      (allHeavyUnitLifts_subset_orderedBlockPrimeTriples a X g)).trans
        (card_ordered_le_six_mul_sorted a X)
  have hscaled : 6 * (R * g ^ 3) ≤ G * (4 * g) ^ 3 := by
    calc
      6 * (R * g ^ 3) ≤ 6 * ((10 * G) * g ^ 3) := by
        exact Nat.mul_le_mul_left 6 (Nat.mul_le_mul_right (g ^ 3) hRG)
      _ ≤ G * (4 * g) ^ 3 := by ring_nf; omega
  have : 6 * (R * g ^ 3) ≤ 6 * P := hscaled.trans (hGL.trans hLP)
  exact Nat.le_of_mul_le_mul_left this (by norm_num)

theorem cmHeckeFamily_product_pos {B : Nat} (F : CMHeckeFamily B) :
    0 < F.blocks.prod id := by
  exact Finset.prod_pos fun a ha =>
    Nat.zero_lt_of_lt (F.modulus_gt_one a ha)

noncomputable instance cmHeckeBlockNeZero
    {B : Nat} (F : CMHeckeFamily B) (a : F.blocks) :
    NeZero (a : Nat) :=
  ⟨(Nat.zero_lt_of_lt (F.modulus_gt_one a a.2)).ne'⟩

def blockRingCRT {B : Nat} (F : CMHeckeFamily B) :
    ZMod (F.blocks.prod id) ≃+*
      ((a : F.blocks) → ZMod (a : Nat)) := by
  let e := ZMod.prodEquivPi (fun a : F.blocks => (a : Nat)) (by
    intro a b hab
    exact F.pairwise_coprime a a.2 b b.2 (fun h => hab (Subtype.ext h)))
  have hprod : (∏ a : F.blocks, (a : Nat)) = F.blocks.prod id := by
    simpa using (Finset.prod_coe_sort (s := F.blocks) (f := id))
  exact (ZMod.ringEquivCongr hprod.symm).trans e

def blockUnitsCRT {B : Nat} (F : CMHeckeFamily B) :
    (ZMod (F.blocks.prod id))ˣ ≃*
      ((a : F.blocks) → (ZMod (a : Nat))ˣ) :=
  (Units.mapEquiv (blockRingCRT F).toMulEquiv).trans MulEquiv.piUnits

def blockHeavyUnits {B : Nat} (F : CMHeckeFamily B) (a : F.blocks) :
    Finset (ZMod (a : Nat))ˣ := by
  letI : NeZero (a : Nat) :=
    ⟨(Nat.zero_lt_of_lt (F.modulus_gt_one a a.2)).ne'⟩
  exact heavyUnits (a : Nat) F.cutoff
    (primeClassTarget F.blocks F.cutoff (a : Nat))

def globalHeavyUnits {B : Nat} (F : CMHeckeFamily B)
    [NeZero (F.blocks.prod id)] :
    Finset (ZMod (F.blocks.prod id))ˣ :=
  Finset.univ.filter fun u =>
    ∀ a : F.blocks,
      (blockUnitsCRT F u) a ∈ blockHeavyUnits F a

def globalHeavyUnitsEquivPi {B : Nat} (F : CMHeckeFamily B)
    [NeZero (F.blocks.prod id)] :
    {u // u ∈ globalHeavyUnits F} ≃
      ((a : F.blocks) →
        {v : (ZMod (a : Nat))ˣ //
          v ∈ blockHeavyUnits F a}) where
  toFun u a := ⟨blockUnitsCRT F u.1 a,
    (Finset.mem_filter.mp u.2).2 a⟩
  invFun u := ⟨(blockUnitsCRT F).symm (fun a => (u a).1), by
    rw [globalHeavyUnits, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro a
    simpa using (u a).2⟩
  left_inv u := by
    apply Subtype.ext
    exact (blockUnitsCRT F).symm_apply_apply u.1
  right_inv u := by
    funext a
    apply Subtype.ext
    exact congrFun ((blockUnitsCRT F).apply_symm_apply fun a => (u a).1) a

theorem card_globalHeavyUnits {B : Nat} (F : CMHeckeFamily B)
    [NeZero (F.blocks.prod id)] :
    (globalHeavyUnits F).card =
      ∏ a : F.blocks, (blockHeavyUnits F a).card := by
  calc
    (globalHeavyUnits F).card =
        Fintype.card {u // u ∈ globalHeavyUnits F} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card ((a : F.blocks) →
        {v : (ZMod (a : Nat))ˣ //
          v ∈ blockHeavyUnits F a}) :=
      Fintype.card_congr (globalHeavyUnitsEquivPi F)
    _ = ∏ a : F.blocks,
        Fintype.card {v : (ZMod (a : Nat))ˣ //
          v ∈ blockHeavyUnits F a} := by
      rw [Fintype.card_pi]
    _ = ∏ a : F.blocks, (blockHeavyUnits F a).card := by
      simp only [Fintype.card_coe]

theorem totient_block_product {B : Nat} (F : CMHeckeFamily B)
    [NeZero (F.blocks.prod id)] :
    (F.blocks.prod id).totient =
      ∏ a : F.blocks, (a : Nat).totient := by
  have hcard := Fintype.card_congr (blockUnitsCRT F).toEquiv
  rw [ZMod.card_units_eq_totient, Fintype.card_pi] at hcard
  simpa only [ZMod.card_units_eq_totient] using hcard

theorem sixteen_mul_seven_pow_le_ten_pow {m : Nat} (hm : 8 ≤ m) :
    16 * 7 ^ m ≤ 10 ^ m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  calc
    16 * 7 ^ (8 + d) = (16 * 7 ^ 8) * 7 ^ d := by
      rw [pow_add]
      ring
    _ ≤ 10 ^ 8 * 10 ^ d :=
      Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left (by norm_num) d)
    _ = 10 ^ (8 + d) := by rw [pow_add]

/--
If the global heavy tuples lose a factor `C`, sufficiently many blocks absorb
that loss whenever `C * 7^m ≤ 10^m`.  Then one block has at least 70 percent
heavy units.  This parameterized form also supports routes that use a growing
number of blocks instead of a constant-density prime-distribution theorem.
-/
theorem exists_seventy_percent_heavy_block_of_factor
    {B : Nat} (F : CMHeckeFamily B)
    [NeZero (F.blocks.prod id)]
    (C : Nat)
    (hglobal :
      (F.blocks.prod id).totient ≤ C * (globalHeavyUnits F).card)
    (hpower : C * 7 ^ F.blocks.card ≤ 10 ^ F.blocks.card) :
    ∃ a : F.blocks,
      7 * (a : Nat).totient ≤ 10 * (blockHeavyUnits F a).card := by
  by_contra hnone
  push Not at hnone
  have hstrict : ∀ a : F.blocks,
      10 * (blockHeavyUnits F a).card < 7 * (a : Nat).totient := by
    intro a
    exact hnone a
  have htotientPos : 0 < (F.blocks.prod id).totient :=
    Nat.totient_pos.mpr (NeZero.pos (F.blocks.prod id))
  have hglobalHeavyPos : 0 < (globalHeavyUnits F).card := by
    have hproductPos : 0 < C * (globalHeavyUnits F).card :=
      htotientPos.trans_le hglobal
    exact Nat.pos_of_mul_pos_left hproductPos
  have hheavyProductNe :
      (∏ a : F.blocks, (blockHeavyUnits F a).card) ≠ 0 := by
    rw [← card_globalHeavyUnits F]
    omega
  have hfactorPos : ∀ a : F.blocks,
      0 < 10 * (blockHeavyUnits F a).card := by
    intro a
    have haNe : (blockHeavyUnits F a).card ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hheavyProductNe) a (Finset.mem_univ a)
    exact Nat.mul_pos (by norm_num) (Nat.pos_of_ne_zero haNe)
  have huniv : (Finset.univ : Finset F.blocks).Nonempty := by
    obtain ⟨a, ha⟩ := F.blocks_nonempty
    exact ⟨⟨a, ha⟩, Finset.mem_univ _⟩
  have hprodStrict :
      (∏ a : F.blocks, 10 * (blockHeavyUnits F a).card) <
        ∏ a : F.blocks, 7 * (a : Nat).totient := by
    exact Finset.prod_lt_prod_of_nonempty
      (fun a _ha => hfactorPos a) (fun a _ha => hstrict a) huniv
  have hprodStrict' :
      10 ^ F.blocks.card *
          (∏ a : F.blocks, (blockHeavyUnits F a).card) <
        7 ^ F.blocks.card *
          (∏ a : F.blocks, (a : Nat).totient) := by
    simpa [Finset.prod_mul_distrib, Fintype.card_coe] using hprodStrict
  have hglobal' :
      (∏ a : F.blocks, (a : Nat).totient) ≤
        C * (∏ a : F.blocks, (blockHeavyUnits F a).card) := by
    rw [totient_block_product F, card_globalHeavyUnits F] at hglobal
    exact hglobal
  have hreverse :
      7 ^ F.blocks.card *
          (∏ a : F.blocks, (a : Nat).totient) ≤
        10 ^ F.blocks.card *
          (∏ a : F.blocks, (blockHeavyUnits F a).card) := by
    calc
      7 ^ F.blocks.card *
          (∏ a : F.blocks, (a : Nat).totient) ≤
          7 ^ F.blocks.card *
            (C * ∏ a : F.blocks, (blockHeavyUnits F a).card) :=
        Nat.mul_le_mul_left _ hglobal'
      _ = (C * 7 ^ F.blocks.card) *
            (∏ a : F.blocks, (blockHeavyUnits F a).card) := by ring
      _ ≤ 10 ^ F.blocks.card *
            (∏ a : F.blocks, (blockHeavyUnits F a).card) :=
        Nat.mul_le_mul_right _ hpower
  omega

/-- A global set occupying at least one sixteenth of all CRT unit tuples
forces one of at least eight blocks to have at least 70 percent heavy units. -/
theorem exists_seventy_percent_heavy_block
    {B : Nat} (F : CMHeckeFamily B)
    [NeZero (F.blocks.prod id)]
    (hglobal :
      (F.blocks.prod id).totient ≤ 16 * (globalHeavyUnits F).card) :
    ∃ a : F.blocks,
      7 * (a : Nat).totient ≤ 10 * (blockHeavyUnits F a).card :=
  exists_seventy_percent_heavy_block_of_factor F 16 hglobal
    (sixteen_mul_seven_pow_le_ten_pow F.enough_blocks)

#check @unitLocalFirstFiberEquivOne
#check @card_unitLocalFirstFiber_eq
#check @card_unitLocalCubeSolution_eq_sum_fibers
#check @card_unitLocalFirstRestricted_balance
#check @local_good_tenth
#check @robust_prime_lifting
#check @card_globalHeavyUnits
#check @totient_block_product
#check @exists_seventy_percent_heavy_block_of_factor
#check @exists_seventy_percent_heavy_block

end

end K3Lean.ErdosBrunTitchmarsh
