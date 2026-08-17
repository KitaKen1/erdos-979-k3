import K3Lean.LocalTraceFormula
import K3Lean.SourceToPNT
import Mathlib.Data.Finset.Card

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# From CM Sato--Tate to local-density amplification

This file performs the counting-to-dyadic bridge and Euler-product argument
inside Lean.  The public route starts from standard counting CM Sato--Tate and
ordinary PNT; an alternative weighted-sector route is retained.  The
Fermat-cubic local trace formula is proved internally in `LocalTraceFormula`.
-/

namespace K3Lean.SourceToCM

open Filter Set
open K3Lean.CMProof
open K3Lean.FiniteLifting
open K3Lean.LocalMultiplicativity
open K3Lean.LocalTraceFormula
open K3Lean.PublishedInputs
open K3Lean.SourceTheorems
open K3Lean.SourceToPNT
open K3Lean.StandardCorollaries
open scoped BigOperators Topology

noncomputable section

/-- Denominator in the pointwise local-factor gain. -/
def cmGainDenominator (T : Nat) : Nat := 32 * T ^ 4

/-- Number of Bernoulli-amplification groups used for target `B`. -/
def cmGainExponent (B T : Nat) : Nat := 128 * T + B + 128

/-- Number of CM primes in each of the two candidate blocks. -/
def cmBlockSize (B T : Nat) : Nat :=
  cmGainDenominator T * cmGainExponent B T

/-- Every sector prime at scale `T^8` is below a simple power of two. -/
theorem sector_prime_lt_two_pow {T p : Nat} (hT : 1 ≤ T)
    (hp : p ∈ negativeCMTraceSectorPrimes (T ^ 8)) :
    p < 2 ^ (16 * T) := by
  have hpParts := Finset.mem_filter.mp hp
  have hpUpper : p ≤ 2 * T ^ 8 := (Finset.mem_Ioc.mp hpParts.1).2
  have hTlt : T < 2 ^ T := Nat.lt_two_pow_self
  have hTpow : T ^ 8 < (2 ^ T) ^ 8 :=
    Nat.pow_lt_pow_left hTlt (by norm_num)
  calc
    p ≤ 2 * T ^ 8 := hpUpper
    _ < 2 * (2 ^ T) ^ 8 := by omega
    _ = 2 ^ 1 * 2 ^ (T * 8) := by rw [Nat.pow_mul]; norm_num
    _ = 2 ^ (1 + T * 8) := (Nat.pow_add 2 1 (T * 8)).symm
    _ ≤ 2 ^ (16 * T) := by
      apply pow_le_pow_right'
      · norm_num
      · omega

/-- A sector prime has logarithm at most `16T`. -/
theorem sector_prime_log_le {T p : Nat} (hT : 1 ≤ T)
    (hp : p ∈ negativeCMTraceSectorPrimes (T ^ 8)) :
    Real.log p ≤ (16 * T : Nat) := by
  have hpParts := Finset.mem_filter.mp hp
  have hpPrime : Nat.Prime p := hpParts.2.1
  have hloglt : Nat.log 2 p < 16 * T :=
    Nat.log_lt_of_lt_pow hpPrime.ne_zero (sector_prime_lt_two_pow hT hp)
  exact (real_log_nat_le_succ_log_two p).trans (by exact_mod_cast hloglt)

/-- The whole weighted sector sum is bounded by cardinality times `16T`. -/
theorem sector_weight_le_card_mul (T : Nat) (hT : 1 ≤ T) :
    negativeCMTraceSectorWeight (T ^ 8) ≤
      (negativeCMTraceSectorPrimes (T ^ 8)).card * (16 * T : Nat) := by
  rw [negativeCMTraceSectorWeight]
  calc
    (∑ p ∈ negativeCMTraceSectorPrimes (T ^ 8), Real.log p)
        ≤ ∑ _p ∈ negativeCMTraceSectorPrimes (T ^ 8),
            (((16 * T : Nat) : Real)) :=
      Finset.sum_le_sum fun p hp => sector_prime_log_le hT hp
    _ = (negativeCMTraceSectorPrimes (T ^ 8)).card * (16 * T : Nat) := by
      simp

/-- The CM limit gives the concrete lower bound `weight(X) > X/24`. -/
theorem sector_weight_eventually_lower (H : PublishedFermatCMSector) :
    ∀ᶠ X : Nat in atTop,
      (X : Real) / 24 < negativeCMTraceSectorWeight X := by
  have hneighborhood : Set.Ioi ((1 : Real) / 24) ∈ nhds ((1 : Real) / 12) :=
    Ioi_mem_nhds (by norm_num)
  have hratio := H.eventually hneighborhood
  filter_upwards [hratio, eventually_ge_atTop (1 : Nat)] with X hratio hX
  have hXpos : (0 : Real) < X := by exact_mod_cast hX
  have := (lt_div_iff₀ hXpos).mp hratio
  nlinarith

/-- The cumulative sector count at `2X` splits into the count at `X` and the dyadic shell. -/
theorem negative_sector_upTo_two_mul (X : Nat) :
    negativeCMTraceSectorPrimesUpTo (2 * X) =
      negativeCMTraceSectorPrimesUpTo X ∪ negativeCMTraceSectorPrimes X := by
  ext p
  simp only [negativeCMTraceSectorPrimesUpTo, negativeCMTraceSectorPrimes,
    Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]
  constructor
  · rintro ⟨hpBound, hp⟩
    by_cases hpX : p ≤ X
    · exact Or.inl ⟨by omega, hp⟩
    · exact Or.inr ⟨⟨by omega, by omega⟩, hp⟩
  · rintro (⟨hpBound, hp⟩ | ⟨⟨hpLower, hpUpper⟩, hp⟩)
    · exact ⟨by omega, hp⟩
    · exact ⟨by omega, hp⟩

/-- The cumulative sector and its following dyadic shell are disjoint. -/
theorem negative_sector_upTo_disjoint_dyadic (X : Nat) :
    Disjoint (negativeCMTraceSectorPrimesUpTo X)
      (negativeCMTraceSectorPrimes X) := by
  rw [Finset.disjoint_left]
  intro p hpUp hpDyadic
  have hpUpper : p ≤ X := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hpUp).1
    omega
  have hpLower : X < p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpDyadic).1).1
  omega

/-- Exact cardinality decomposition used to pass from global Sato--Tate to a dyadic block. -/
theorem card_negative_sector_upTo_two_mul (X : Nat) :
    (negativeCMTraceSectorPrimesUpTo (2 * X)).card =
      (negativeCMTraceSectorPrimesUpTo X).card +
        (negativeCMTraceSectorPrimes X).card := by
  rw [negative_sector_upTo_two_mul,
    Finset.card_union_of_disjoint (negative_sector_upTo_disjoint_dyadic X)]

/-- A concrete logarithm comparison used in the Sato--Tate plus PNT bridge. -/
theorem four_log_two_le_log_nat {X : Nat} (hX : 16 ≤ X) :
    4 * Real.log 2 ≤ Real.log X := by
  have hcast : (16 : Real) ≤ (X : Real) := by exact_mod_cast hX
  have hmono : Real.log (16 : Real) ≤ Real.log (X : Real) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < X))) hcast
  calc
    4 * Real.log 2 = Real.log ((2 : Real) ^ 4) := by
      simpa using (Real.log_pow (2 : Real) 4).symm
    _ = Real.log (16 : Real) := by norm_num
    _ ≤ Real.log (X : Real) := hmono

/-- For `X ≥ 16`, replacing `X` by `2X` enlarges its logarithm by at most `5/4`. -/
theorem four_log_two_mul_le_five_log {X : Nat} (hX : 16 ≤ X) :
    4 * Real.log (2 * X : Nat) ≤ 5 * Real.log X := by
  have hXpos : (0 : Real) < X := by exact_mod_cast (by omega : 0 < X)
  have hlogMul : Real.log ((2 * X : Nat) : Real) =
      Real.log 2 + Real.log (X : Real) := by
    push_cast
    rw [Real.log_mul (by norm_num) hXpos.ne']
  rw [hlogMul]
  have hbase := four_log_two_le_log_nat hX
  nlinarith

/--
The standard counting form of CM Sato--Tate, together with the ordinary PNT,
implies the weak polynomial sector abundance used by the block proof.

This theorem is the audit bridge from two familiar statements to the
problem-specific integer bound.  No Hecke-character formalism occurs below.
-/
theorem fermatSectorAbundance_of_satoTate_pnt
    (hST : FermatCMSatoTate)
    (hPNT : OrdinaryPrimeNumberTheorem) : FermatSectorAbundance := by
  have hSTNeighborhood :
      Set.Ioo ((1 : Real) / 13) ((1 : Real) / 11) ∈
        nhds ((1 : Real) / 12) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  have hPNTNeighborhood :
      Set.Ioo ((9 : Real) / 10) ((11 : Real) / 10) ∈ nhds (1 : Real) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  obtain ⟨ST₀, hSTafter⟩ := eventually_atTop.1 (hST.eventually hSTNeighborhood)
  obtain ⟨PNT₀, hPNTafter⟩ := eventually_atTop.1 (hPNT.eventually hPNTNeighborhood)
  refine eventually_atTop.2 ⟨max ST₀ (max PNT₀ 2000), ?_⟩
  intro T hT
  have hST₀T : ST₀ ≤ T := (le_max_left ST₀ (max PNT₀ 2000)).trans hT
  have hPNT₀T : PNT₀ ≤ T :=
    (le_max_left PNT₀ 2000).trans
      ((le_max_right ST₀ (max PNT₀ 2000)).trans hT)
  have h2000T : 2000 ≤ T :=
    (le_max_right PNT₀ 2000).trans
      ((le_max_right ST₀ (max PNT₀ 2000)).trans hT)
  have hTone : 1 ≤ T := by omega
  have hTlePow : T ≤ T ^ 8 := le_self_pow hTone (by norm_num)
  let X := T ^ 8
  let S₁ := (negativeCMTraceSectorPrimesUpTo X).card
  let S₂ := (negativeCMTraceSectorPrimesUpTo (2 * X)).card
  let P₁ := (rationalPrimesUpTo X).card
  let P₂ := (rationalPrimesUpTo (2 * X)).card
  let D := (negativeCMTraceSectorPrimes X).card
  have hST₁ :
      (1 : Real) / 13 < (S₁ : Real) / (P₁ : Real) ∧
        (S₁ : Real) / (P₁ : Real) < (1 : Real) / 11 := by
    simpa [X, S₁, P₁] using hSTafter (T ^ 8) (hST₀T.trans hTlePow)
  have hST₂ :
      (1 : Real) / 13 < (S₂ : Real) / (P₂ : Real) ∧
        (S₂ : Real) / (P₂ : Real) < (1 : Real) / 11 := by
    have hbound : ST₀ ≤ 2 * T ^ 8 :=
      (hST₀T.trans hTlePow).trans (Nat.le_mul_of_pos_left _ (by norm_num))
    simpa [X, S₂, P₂] using hSTafter (2 * T ^ 8) hbound
  have hPNT₁ :
      (9 : Real) / 10 <
          (P₁ : Real) * Real.log (X : Real) / (X : Real) ∧
        (P₁ : Real) * Real.log (X : Real) / (X : Real) <
          (11 : Real) / 10 := by
    simpa [X, P₁] using hPNTafter (T ^ 8) (hPNT₀T.trans hTlePow)
  have hPNT₂ :
      (9 : Real) / 10 <
          (P₂ : Real) * Real.log ((2 * X : Nat) : Real) /
            ((2 * X : Nat) : Real) ∧
        (P₂ : Real) * Real.log ((2 * X : Nat) : Real) /
            ((2 * X : Nat) : Real) < (11 : Real) / 10 := by
    have hbound : PNT₀ ≤ 2 * T ^ 8 :=
      (hPNT₀T.trans hTlePow).trans (Nat.le_mul_of_pos_left _ (by norm_num))
    simpa [X, P₂] using hPNTafter (2 * T ^ 8) hbound
  have hP₁posNat : 0 < P₁ := by
    apply Finset.card_pos.mpr
    refine ⟨2, ?_⟩
    change 2 ∈ rationalPrimesUpTo X
    rw [rationalPrimesUpTo, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (by dsimp [X]; omega), Nat.prime_two⟩
  have hP₂posNat : 0 < P₂ := by
    apply Finset.card_pos.mpr
    refine ⟨2, ?_⟩
    change 2 ∈ rationalPrimesUpTo (2 * X)
    rw [rationalPrimesUpTo, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (by dsimp [X]; omega), Nat.prime_two⟩
  have hP₁pos : (0 : Real) < P₁ := by exact_mod_cast hP₁posNat
  have hP₂pos : (0 : Real) < P₂ := by exact_mod_cast hP₂posNat
  have hXposNat : 0 < X := by simp [X]; positivity
  have hXpos : (0 : Real) < X := by exact_mod_cast hXposNat
  have hTwoXpos : (0 : Real) < (2 * X : Nat) := by positivity
  have hXsixteen : 16 ≤ X := by
    dsimp [X]
    have := Nat.pow_le_pow_left h2000T 8
    norm_num at this ⊢
    omega
  have hlogXpos : (0 : Real) < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hlogTwoXpos : (0 : Real) < Real.log (2 * X : Nat) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * X))
  have hSector₂ : (P₂ : Real) < 13 * (S₂ : Real) := by
    have h := (lt_div_iff₀ hP₂pos).mp hST₂.1
    nlinarith
  have hSector₁ : 11 * (S₁ : Real) < (P₁ : Real) := by
    have h := (div_lt_iff₀ hP₁pos).mp hST₁.2
    nlinarith
  have hPNT₂lower :
      18 * (X : Real) <
        10 * (P₂ : Real) * Real.log (2 * X : Nat) := by
    have h := (lt_div_iff₀ hTwoXpos).mp hPNT₂.1
    norm_num [Nat.cast_mul] at h ⊢
    nlinarith
  have hPNT₁upper :
      10 * (P₁ : Real) * Real.log X < 11 * (X : Real) := by
    have h := (div_lt_iff₀ hXpos).mp hPNT₁.2
    nlinarith
  have hSector₂Log :
      (P₂ : Real) * Real.log (2 * X : Nat) <
        13 * (S₂ : Real) * Real.log (2 * X : Nat) :=
    mul_lt_mul_of_pos_right hSector₂ hlogTwoXpos
  have hLogCompare := four_log_two_mul_le_five_log hXsixteen
  have hLogScaled :
      520 * (S₂ : Real) * Real.log (2 * X : Nat) ≤
        650 * (S₂ : Real) * Real.log X := by
    have hmul := mul_le_mul_of_nonneg_left hLogCompare
      (show (0 : Real) ≤ 130 * S₂ by positivity)
    nlinarith
  have hS₂Main :
      72 * (X : Real) < 650 * (S₂ : Real) * Real.log X := by
    nlinarith [hPNT₂lower, hSector₂Log, hLogScaled]
  have hSector₁Log :
      11 * (S₁ : Real) * Real.log X <
        (P₁ : Real) * Real.log X :=
    mul_lt_mul_of_pos_right hSector₁ hlogXpos
  have hS₁Main :
      10 * (S₁ : Real) * Real.log X < (X : Real) := by
    nlinarith [hSector₁Log, hPNT₁upper]
  have hcard : S₂ = S₁ + D := by
    simpa [S₁, S₂, D] using card_negative_sector_upTo_two_mul X
  have hcardReal : (S₂ : Real) = (S₁ : Real) + (D : Real) := by
    exact_mod_cast hcard
  have hDyadicReal :
      (X : Real) < 100 * (D : Real) * Real.log X := by
    rw [hcardReal] at hS₂Main
    nlinarith [hS₁Main]
  have hlogPow : Real.log (X : Real) = 8 * Real.log (T : Real) := by
    simp only [X, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  have hlogTle : Real.log (T : Real) ≤ (T : Real) :=
    Real.log_le_self (by positivity)
  have hlogXle : Real.log (X : Real) ≤ 8 * (T : Real) := by
    rw [hlogPow]
    nlinarith
  have hlogMulUpper :
      100 * (D : Real) * Real.log X ≤
        800 * (D : Real) * (T : Real) := by
    have hDnonneg : (0 : Real) ≤ (D : Real) := Nat.cast_nonneg D
    have hfactor : (0 : Real) ≤ 100 * (D : Real) :=
      mul_nonneg (by norm_num) hDnonneg
    have hmul := mul_le_mul_of_nonneg_left hlogXle hfactor
    calc
      100 * (D : Real) * Real.log X =
          (100 * (D : Real)) * Real.log X := by rfl
      _ ≤ (100 * (D : Real)) * (8 * (T : Real)) := hmul
      _ = 800 * (D : Real) * (T : Real) := by ring
  have hreal : (X : Real) < 800 * (D : Real) * (T : Real) :=
    hDyadicReal.trans_le hlogMulUpper
  have hnat : X < 800 * D * T := by
    exact_mod_cast hreal
  have hbase : T ^ 7 ≤ 800 * D := by
    have hmul : T * T ^ 7 ≤ T * (800 * D) := by
      calc
        T * T ^ 7 = X := by simp [X]; ring
        _ ≤ 800 * D * T := hnat.le
        _ = T * (800 * D) := by ring
    exact Nat.le_of_mul_le_mul_left hmul (by omega)
  have hscaled : 800 * T ^ 6 ≤ 800 * D := by
    calc
      800 * T ^ 6 ≤ T * T ^ 6 := Nat.mul_le_mul_right (T ^ 6) (by omega)
      _ = T ^ 7 := by ring
      _ ≤ 800 * D := hbase
  have hfinal : T ^ 6 ≤ D :=
    Nat.le_of_mul_le_mul_left hscaled (by norm_num)
  simpa [D, X] using hfinal

/-- The published weighted sector limit implies the simpler integer abundance statement. -/
theorem fermatSectorAbundance_of_published
    (H : PublishedFermatCMSector) : FermatSectorAbundance := by
  obtain ⟨X₀, hafter⟩ := eventually_atTop.1 (sector_weight_eventually_lower H)
  filter_upwards [eventually_ge_atTop (max X₀ 384)] with T hT
  have hX₀T : X₀ ≤ T := (le_max_left X₀ 384).trans hT
  have h384T : 384 ≤ T := (le_max_right X₀ 384).trans hT
  have hTone : 1 ≤ T := by omega
  have hTlePow : T ≤ T ^ 8 := le_self_pow hTone (by norm_num)
  have hlower := hafter (T ^ 8) (hX₀T.trans hTlePow)
  have hupper := sector_weight_le_card_mul T hTone
  let card := (negativeCMTraceSectorPrimes (T ^ 8)).card
  have hreal : (T ^ 8 : Nat) < 384 * T * card := by
    have hreal' : (T ^ 8 : Real) < 384 * T * card := by
      dsimp [card] at hlower hupper ⊢
      push_cast at hlower hupper ⊢
      norm_num at hlower hupper ⊢
      nlinarith
    exact_mod_cast hreal'
  have hcardBase : T ^ 7 ≤ 384 * card := by
    have hmul : T * T ^ 7 ≤ T * (384 * card) := by
      calc
        T * T ^ 7 = T ^ 8 := by ring
        _ ≤ 384 * T * card := hreal.le
        _ = T * (384 * card) := by ring
    exact Nat.le_of_mul_le_mul_left hmul (by omega)
  have hscaled : 384 * T ^ 6 ≤ 384 * card := by
    calc
      384 * T ^ 6 ≤ T * T ^ 6 := Nat.mul_le_mul_right (T ^ 6) h384T
      _ = T ^ 7 := by ring
      _ ≤ 384 * card := hcardBase
  exact Nat.le_of_mul_le_mul_left hscaled (by norm_num)

/--
The weak integer abundance statement already supplies two disjoint blocks of
the exact cardinality needed below.
-/
theorem exists_scale_with_two_blocks_of_abundance
    (H : FermatSectorAbundance) (B minimumProduct : Nat) :
    ∃ T : Nat,
      2000 ≤ T ∧ B ≤ T ∧ minimumProduct ≤ T ∧
        2 * cmBlockSize B T ≤
          (negativeCMTraceSectorPrimes (T ^ 8)).card := by
  obtain ⟨T₀, hafter⟩ := eventually_atTop.1 H
  let T := max T₀ (max B (max minimumProduct 16448))
  have hT₀T : T₀ ≤ T := le_max_left _ _
  have hBT : B ≤ T :=
    (le_max_left B (max minimumProduct 16448)).trans (le_max_right T₀ _)
  have hminimumT : minimumProduct ≤ T :=
    (le_max_left minimumProduct 16448).trans
      ((le_max_right B _).trans (le_max_right T₀ _))
  have h16448T : 16448 ≤ T :=
    (le_max_right minimumProduct 16448).trans
      ((le_max_right B _).trans (le_max_right T₀ _))
  have hsectorCard := hafter T hT₀T
  have hExp : cmGainExponent B T ≤ 257 * T := by
    simp [cmGainExponent]
    omega
  have hsize : 2 * cmBlockSize B T ≤ T ^ 6 := by
    calc
      2 * cmBlockSize B T = 64 * T ^ 4 * cmGainExponent B T := by
        simp [cmBlockSize, cmGainDenominator]
        ring
      _ ≤ 64 * T ^ 4 * (257 * T) :=
        Nat.mul_le_mul_left (64 * T ^ 4) hExp
      _ = 16448 * T ^ 5 := by ring
      _ ≤ T * T ^ 5 := Nat.mul_le_mul_right (T ^ 5) h16448T
      _ = T ^ 6 := by ring
  exact ⟨T, by omega, hBT, hminimumT, hsize.trans hsectorCard⟩

/-- The published sector theorem is more than enough for the block scale. -/
theorem exists_scale_with_two_blocks
    (H : PublishedFermatCMSector) (B minimumProduct : Nat) :
    ∃ T : Nat,
      2000 ≤ T ∧ B ≤ T ∧ minimumProduct ≤ T ∧
        2 * cmBlockSize B T ≤
          (negativeCMTraceSectorPrimes (T ^ 8)).card :=
  exists_scale_with_two_blocks_of_abundance
    (fermatSectorAbundance_of_published H) B minimumProduct

/-- Sector membership forces a trace at most `-T^4`. -/
theorem sector_trace_le_neg_scale {T p : Nat} (hT : 1 ≤ T)
    (hp : p ∈ negativeCMTraceSectorPrimes (T ^ 8)) :
    (fermatFrobeniusTrace p : Real) ≤ -(T ^ 4 : Nat) := by
  have hpParts := Finset.mem_filter.mp hp
  have hpPrime : Nat.Prime p := hpParts.2.1
  have hpLower : T ^ 8 < p := (Finset.mem_Ioc.mp hpParts.1).1
  have hnormalized : normalizedFermatTrace p ≤ -(1 : Real) / 2 :=
    hpParts.2.2.2.2
  have hpRealPos : (0 : Real) < p := by exact_mod_cast hpPrime.pos
  have hsqrtPos : 0 < Real.sqrt (p : Real) := Real.sqrt_pos.2 hpRealPos
  have hdenom : 0 < 2 * Real.sqrt (p : Real) := by positivity
  have htraceSqrt :
      (fermatFrobeniusTrace p : Real) ≤ -Real.sqrt (p : Real) := by
    rw [normalizedFermatTrace] at hnormalized
    have := (div_le_iff₀ hdenom).mp hnormalized
    nlinarith
  have hscaleSqrt : (T ^ 4 : Nat) < Real.sqrt (p : Real) := by
    apply Real.lt_sqrt_of_sq_lt
    have hcast : ((T ^ 8 : Nat) : Real) < (p : Real) := by exact_mod_cast hpLower
    push_cast at hcast ⊢
    nlinarith
  exact htraceSqrt.trans (by nlinarith)

/-- A sector trace is nonzero, so the local trace formula applies. -/
theorem sector_trace_ne_zero {T p : Nat} (hT : 1 ≤ T)
    (hp : p ∈ negativeCMTraceSectorPrimes (T ^ 8)) :
    fermatFrobeniusTrace p ≠ 0 := by
  have htrace := sector_trace_le_neg_scale hT hp
  have hTpos : (0 : Real) < (T ^ 4 : Nat) := by positivity
  intro hz
  rw [hz] at htrace
  norm_num at htrace
  have hTpos' : (0 : Real) < (T : Real) ^ 4 := by
    simpa only [Nat.cast_pow] using hTpos
  exact (not_le_of_gt hTpos') htrace

/-- The source trace formula gives a concrete lower bound for the local count. -/
theorem sector_local_count_lower (H : FermatCubicLocalTraceFormula)
    {T p : Nat} (hT : 2 ≤ T)
    (hp : p ∈ negativeCMTraceSectorPrimes (T ^ 8)) :
    (p - 1) * (p - 8 + T ^ 4) ≤ (localCubeSolutions p).card := by
  have hpParts := Finset.mem_filter.mp hp
  have hpPrime : Nat.Prime p := hpParts.2.1
  have hpThree : 3 < p := hpParts.2.2.1
  have hpLower : T ^ 8 < p := (Finset.mem_Ioc.mp hpParts.1).1
  have hpEight : 8 ≤ p := by
    have : 2 ^ 8 ≤ T ^ 8 := Nat.pow_le_pow_left hT 8
    omega
  have htraceReal := sector_trace_le_neg_scale (by omega : 1 ≤ T) hp
  have htraceInt : fermatFrobeniusTrace p ≤ -((T ^ 4 : Nat) : Int) := by
    exact_mod_cast htraceReal
  have hformula := H p hpPrime hpThree
    (sector_trace_ne_zero (by omega : 1 ≤ T) hp)
  have hInt :
      (((p - 1) * (p - 8 + T ^ 4) : Nat) : Int) ≤
        ((localCubeSolutions p).card : Int) := by
    have hfactor :
        (p : Int) - 8 + (T ^ 4 : Nat) ≤
          (p : Int) - 8 - fermatFrobeniusTrace p := by
      have hneg : ((T ^ 4 : Nat) : Int) ≤ -fermatFrobeniusTrace p := by
        linarith
      simpa only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        add_le_add_left hneg ((p : Int) - 8)
    have hpOneInt : (1 : Int) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
    have hleftNonneg : (0 : Int) ≤ (p : Int) - 1 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hfactor hleftNonneg
    rw [hformula]
    push_cast [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_sub hpEight] at ⊢
    simpa [Nat.cast_pow] using hmul
  exact_mod_cast hInt

/-- Pure arithmetic behind the pointwise normalized local-factor gain. -/
theorem pointwise_local_gain_arithmetic {T p R : Nat}
    (hT : 2 ≤ T) (hpLower : T ^ 8 < p) (hpUpper : p ≤ 2 * T ^ 8)
    (hpEight : 8 ≤ p)
    (hR : (p - 1) * (p - 8 + T ^ 4) ≤ R) :
    cmGainDenominator T * (p * R) ≥
      (cmGainDenominator T + 1) * (p - 1) ^ 3 := by
  let u := T ^ 4
  have hu16 : 16 ≤ u := by
    dsimp [u]
    have := Nat.pow_le_pow_left hT 4
    norm_num at this ⊢
    exact this
  have hpUpper' : p ≤ 2 * u ^ 2 := by
    dsimp [u]
    convert hpUpper using 1 <;> ring
  have hbase :
      32 * u * (p * ((p - 1) * (p - 8 + u))) ≥
        (32 * u + 1) * (p - 1) ^ 3 := by
    have hnonneg1 : 0 ≤ (u : Int) - 16 := by
      have hu16Int : (16 : Int) ≤ u := by exact_mod_cast hu16
      linarith
    have hnonneg2 : 0 ≤ (p : Int) := by positivity
    have hmul1 : 0 ≤ ((u : Int) - 16) * p := mul_nonneg hnonneg1 hnonneg2
    have hupperInt : (p : Int) ≤ 2 * (u : Int) ^ 2 := by exact_mod_cast hpUpper'
    have hmul2 : 0 ≤ (p : Int) * (2 * (u : Int) ^ 2 - p) :=
      mul_nonneg hnonneg2 (sub_nonneg.mpr hupperInt)
    have hpEightInt : (8 : Int) ≤ p := by exact_mod_cast hpEight
    have hpOneInt : (1 : Int) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
    have hmul3 :
        0 ≤ ((u : Int) - 16) * (u : Int) * p := by positivity
    have hrest :
        (32 : Int) * u + 1 ≤ 18 * (u : Int) ^ 2 * p := by
      have hpOneNonneg : 0 ≤ (p : Int) - 1 := by linarith
      have hmulP : 0 ≤ ((u : Int) ^ 2) * ((p : Int) - 1) := by positivity
      nlinarith [sq_nonneg ((u : Int) - 1)]
    have hreduced :
        ((32 : Int) * u + 1) * ((p : Int) - 1) ^ 2 ≤
          32 * u * p * ((p : Int) - 8 + u) := by
      nlinarith
    have hfull := mul_le_mul_of_nonneg_right hreduced
      (sub_nonneg.mpr hpOneInt)
    have hbaseExplicit :
        ((32 : Int) * u + 1) * ((p : Int) - 1) ^ 3 ≤
          32 * u * (p * (((p : Int) - 1) * ((p : Int) - 8 + u))) := by
      calc
        ((32 : Int) * u + 1) * ((p : Int) - 1) ^ 3 =
            ((32 : Int) * u + 1) * ((p : Int) - 1) ^ 2 *
              ((p : Int) - 1) := by ring
        _ ≤ 32 * u * p * ((p : Int) - 8 + u) * ((p : Int) - 1) := hfull
        _ = 32 * u * (p * (((p : Int) - 1) * ((p : Int) - 8 + u))) := by ring
    have hbaseCast :
        ((32 * u + 1) * (p - 1) ^ 3 : Nat) ≤
          32 * u * (p * ((p - 1) * (p - 8 + u))) := by
      have hpOneNat : 1 ≤ p := by omega
      have hcastP1 : (((p - 1 : Nat) : Int)) = (p : Int) - 1 := by
        exact Nat.cast_sub hpOneNat
      have hcastP8 : (((p - 8 : Nat) : Int)) = (p : Int) - 8 := by
        exact Nat.cast_sub hpEight
      have hbaseCastInt :
          ((((32 * u + 1) * (p - 1) ^ 3 : Nat) : Int)) ≤
            (((32 * u * (p * ((p - 1) * (p - 8 + u))) : Nat) : Int)) := by
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
          Nat.cast_pow]
        rw [hcastP1, hcastP8]
        exact hbaseExplicit
      exact_mod_cast hbaseCastInt
    simpa [Nat.mul_assoc] using hbaseCast
  calc
    (cmGainDenominator T + 1) * (p - 1) ^ 3
        ≤ cmGainDenominator T *
            (p * ((p - 1) * (p - 8 + T ^ 4))) := by
          simpa [cmGainDenominator, u, Nat.mul_assoc] using hbase
    _ ≤ cmGainDenominator T * (p * R) := by
      exact Nat.mul_le_mul_left (cmGainDenominator T)
        (Nat.mul_le_mul_left p hR)

/-- Every selected CM prime has the required pointwise local-factor gain. -/
theorem sector_prime_local_gain (H : FermatCubicLocalTraceFormula)
    {T p : Nat} (hT : 2 ≤ T)
    (hp : p ∈ negativeCMTraceSectorPrimes (T ^ 8)) :
    cmGainDenominator T * (p * (localCubeSolutions p).card) ≥
      (cmGainDenominator T + 1) * p.totient ^ 3 := by
  have hpParts := Finset.mem_filter.mp hp
  have hpPrime : Nat.Prime p := hpParts.2.1
  have hpLower : T ^ 8 < p := (Finset.mem_Ioc.mp hpParts.1).1
  have hpUpper : p ≤ 2 * T ^ 8 := (Finset.mem_Ioc.mp hpParts.1).2
  have hpEight : 8 ≤ p := by
    have : 2 ^ 8 ≤ T ^ 8 := Nat.pow_le_pow_left hT 8
    omega
  rw [Nat.totient_prime hpPrime]
  exact pointwise_local_gain_arithmetic hT hpLower hpUpper hpEight
    (sector_local_count_lower H hT hp)

/-- The elementary Bernoulli estimate `(1 + 1/K)^K >= 2`. -/
theorem two_mul_pow_le_succ_pow {K : Nat} (hK : 0 < K) :
    2 * K ^ K ≤ (K + 1) ^ K := by
  have h := pow_add_mul_le_add_pow (R := Nat) (a := K) (b := 1)
    (by omega) (by omega) K
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
  simpa [pow_succ', Nat.mul_comm, two_mul] using h

/-- Grouping `K*E` factors turns the local gain into a factor `2^E`. -/
theorem grouped_local_gain {K E : Nat} (hK : 0 < K) :
    2 ^ E * K ^ (K * E) ≤ (K + 1) ^ (K * E) := by
  have hpow := Nat.pow_le_pow_left (two_mul_pow_le_succ_pow hK) E
  simpa [mul_pow, pow_mul, Nat.mul_assoc] using hpow

/-- Multiplication of all pointwise local-factor inequalities in a prime set. -/
theorem product_local_gain (H : FermatCubicLocalTraceFormula)
    {T : Nat} (hT : 2 ≤ T) (S : Finset Nat)
    (hS : S ⊆ negativeCMTraceSectorPrimes (T ^ 8)) :
    (cmGainDenominator T + 1) ^ S.card *
        (S.prod id).totient ^ 3 ≤
      cmGainDenominator T ^ S.card *
        ((S.prod id) * (localCubeSolutions (S.prod id)).card) := by
  have hprime : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp (hS hp)).2.1
  have hpointwise :
      ∏ p ∈ S,
          ((cmGainDenominator T + 1) * p.totient ^ 3) ≤
        ∏ p ∈ S,
          (cmGainDenominator T * (p * (localCubeSolutions p).card)) := by
    exact Finset.prod_le_prod' fun p hp => sector_prime_local_gain H hT (hS hp)
  rw [localCubeSolutions_card_prod_primes S hprime,
    totient_prod_primes S hprime]
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow,
    id_eq, mul_assoc] using hpointwise

/-- An exact-size CM block has normalized local density at least `2^E`. -/
theorem exact_block_density (H : FermatCubicLocalTraceFormula)
    {B T : Nat} (hT : 2 ≤ T) (S : Finset Nat)
    (hS : S ⊆ negativeCMTraceSectorPrimes (T ^ 8))
    (hcard : S.card = cmBlockSize B T) :
    2 ^ cmGainExponent B T * (S.prod id).totient ^ 3 ≤
      (S.prod id) * (localCubeSolutions (S.prod id)).card := by
  let K := cmGainDenominator T
  let E := cmGainExponent B T
  have hK : 0 < K := by simp [K, cmGainDenominator]; positivity
  have hcardKE : S.card = K * E := by simpa [K, E, cmBlockSize] using hcard
  have hproduct := product_local_gain H hT S hS
  rw [hcardKE] at hproduct
  have hgroup := grouped_local_gain (K := K) (E := E) hK
  have hscaled :
      (2 ^ E * K ^ (K * E)) * (S.prod id).totient ^ 3 ≤
        K ^ (K * E) *
          ((S.prod id) * (localCubeSolutions (S.prod id)).card) := by
    calc
      (2 ^ E * K ^ (K * E)) * (S.prod id).totient ^ 3
          ≤ (K + 1) ^ (K * E) * (S.prod id).totient ^ 3 :=
        Nat.mul_le_mul_right _ hgroup
      _ ≤ K ^ (K * E) *
          ((S.prod id) * (localCubeSolutions (S.prod id)).card) := by
        simpa [K] using hproduct
  have hcancel :
      K ^ (K * E) * (2 ^ E * (S.prod id).totient ^ 3) ≤
        K ^ (K * E) *
          ((S.prod id) * (localCubeSolutions (S.prod id)).card) := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hscaled
  have hKpow : 0 < K ^ (K * E) := pow_pos hK _
  have := Nat.le_of_mul_le_mul_left hcancel hKpow
  simpa [E] using this

/-- Split a sufficiently large finite set into two disjoint exact-size subsets. -/
theorem exists_two_disjoint_subsets {S : Finset Nat} {m : Nat}
    (hcard : 2 * m ≤ S.card) :
    ∃ S₁ S₂ : Finset Nat,
      S₁ ⊆ S ∧ S₂ ⊆ S ∧ Disjoint S₁ S₂ ∧
        S₁.card = m ∧ S₂.card = m := by
  have hmS : m ≤ S.card := by omega
  obtain ⟨S₁, hS₁, hcard₁⟩ := Finset.exists_subset_card_eq hmS
  have hmDiff : m ≤ (S \ S₁).card := by
    rw [Finset.card_sdiff_of_subset hS₁, hcard₁]
    omega
  obtain ⟨S₂, hS₂diff, hcard₂⟩ := Finset.exists_subset_card_eq hmDiff
  have hS₂ : S₂ ⊆ S := hS₂diff.trans (Finset.sdiff_subset)
  have hdisjoint : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    have := hS₂diff hp₂
    simp only [Finset.mem_sdiff] at this
    exact this.2 hp₁
  exact ⟨S₁, S₂, hS₁, hS₂, hdisjoint, hcard₁, hcard₂⟩

/-- Product bound for a fixed-size subset of the sector. -/
theorem sector_subset_product_le {B T : Nat} (hT : 1 ≤ T)
    (S : Finset Nat) (hS : S ⊆ negativeCMTraceSectorPrimes (T ^ 8))
    (hcard : S.card = cmBlockSize B T) :
    S.prod id ≤ 2 ^ (16 * T * cmBlockSize B T) := by
  calc
    S.prod id ≤ S.prod (fun _p => 2 ^ (16 * T)) := by
      exact Finset.prod_le_prod' fun p hp => (sector_prime_lt_two_pow hT (hS hp)).le
    _ = (2 ^ (16 * T)) ^ S.card := by simp
    _ = 2 ^ (16 * T * cmBlockSize B T) := by
      rw [hcard, ← Nat.pow_mul]

/-- Two exact blocks have a polynomially controlled logarithmic loss. -/
theorem target_le_gain_exponential {B T a₁ a₂ : Nat}
    (hT : 2000 ≤ T) (hBT : B ≤ T)
    (ha₁ : a₁ ≤ 2 ^ (16 * T * cmBlockSize B T))
    (ha₂ : a₂ ≤ 2 ^ (16 * T * cmBlockSize B T)) :
    24 * B * (logLoss (a₁ * a₂)) ^ 3 ≤ 2 ^ cmGainExponent B T := by
  let m := cmBlockSize B T
  let E := cmGainExponent B T
  have hTone : 1 ≤ T := by omega
  have hE : E ≤ 130 * T := by
    dsimp [E, cmGainExponent]
    omega
  have hQpow : a₁ * a₂ ≤ 2 ^ (32 * T * m) := by
    calc
      a₁ * a₂ ≤ 2 ^ (16 * T * m) * 2 ^ (16 * T * m) :=
        Nat.mul_le_mul ha₁ ha₂
      _ = 2 ^ (32 * T * m) := by rw [← Nat.pow_add]; congr 1 <;> ring
  have hlog : Nat.log 2 (a₁ * a₂) ≤ 32 * T * m := by
    calc
      Nat.log 2 (a₁ * a₂) ≤ Nat.log 2 (2 ^ (32 * T * m)) :=
        Nat.log_monotone hQpow
      _ = 32 * T * m := Nat.log_pow Nat.one_lt_two _
  have hm : m = 32 * T ^ 4 * E := by
    simp [m, E, cmBlockSize, cmGainDenominator]
  have hlogCoarse : Nat.log 2 (a₁ * a₂) + 1 ≤ 133121 * T ^ 6 := by
    calc
      Nat.log 2 (a₁ * a₂) + 1 ≤ 32 * T * m + 1 := Nat.add_le_add_right hlog 1
      _ = 1024 * T ^ 5 * E + 1 := by rw [hm]; ring
      _ ≤ 1024 * T ^ 5 * (130 * T) + 1 := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left (1024 * T ^ 5) hE) 1
      _ = 133120 * T ^ 6 + 1 := by ring
      _ ≤ 133121 * T ^ 6 := by
        have hT6pos : 0 < T ^ 6 := pow_pos (by omega) _
        have hT6 : 1 ≤ T ^ 6 := by omega
        nlinarith
  have hloss : logLoss (a₁ * a₂) ≤ 4 * (133121 * T ^ 6) ^ 4 := by
    simp only [logLoss]
    exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hlogCoarse 4)
  have hconstant :
      1536 * 133121 ^ 12 ≤ 2 ^ 128 * 2000 ^ 9 := by
    norm_num
  have hconstantT :
      1536 * 133121 ^ 12 ≤ 2 ^ 128 * T ^ 9 := by
    exact hconstant.trans
      (Nat.mul_le_mul_left (2 ^ 128) (Nat.pow_le_pow_left hT 9))
  have hBpow : B ≤ 2 ^ B := (Nat.lt_two_pow_self).le
  have hTpow : T ^ 81 ≤ 2 ^ (128 * T) := by
    calc
      T ^ 81 ≤ T ^ 128 := pow_le_pow_right' hTone (by norm_num)
      _ ≤ (2 ^ T) ^ 128 := Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) 128
      _ = 2 ^ (128 * T) := by
        rw [← Nat.pow_mul]
        congr 1 <;> ring
  calc
    24 * B * (logLoss (a₁ * a₂)) ^ 3
        ≤ 24 * B * (4 * (133121 * T ^ 6) ^ 4) ^ 3 :=
      Nat.mul_le_mul_left (24 * B) (Nat.pow_le_pow_left hloss 3)
    _ = (1536 * 133121 ^ 12) * B * T ^ 72 := by ring
    _ ≤ (2 ^ 128 * T ^ 9) * B * T ^ 72 :=
      by
        simpa only [Nat.mul_assoc] using
          Nat.mul_le_mul_right (B * T ^ 72) hconstantT
    _ = 2 ^ 128 * B * T ^ 81 := by ring
    _ ≤ 2 ^ 128 * 2 ^ B * 2 ^ (128 * T) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left (2 ^ 128) hBpow) hTpow
    _ = 2 ^ E := by
      dsimp [E, cmGainExponent]
      conv_rhs =>
        rw [show 128 * T + B + 128 = (128 + B) + 128 * T by ring]
      simp only [Nat.pow_add]

/-- A nonempty product of primes is greater than one. -/
theorem prime_finset_product_gt_one {S : Finset Nat}
    (hne : S.Nonempty) (hprime : ∀ p ∈ S, Nat.Prime p) :
    1 < S.prod id := by
  obtain ⟨p, hp⟩ := hne
  have hpProd : p ≤ S.prod id :=
    Finset.single_le_prod' (f := id) (fun q hq => (hprime q hq).one_le) hp
  exact (hprime p hp).one_lt.trans_le hpProd

/-- Disjoint prime sets have coprime products. -/
theorem coprime_prime_finset_products {S₁ S₂ : Finset Nat}
    (hdisjoint : Disjoint S₁ S₂)
    (hprime₁ : ∀ p ∈ S₁, Nat.Prime p)
    (hprime₂ : ∀ p ∈ S₂, Nat.Prime p) :
    (S₁.prod id).Coprime (S₂.prod id) := by
  rw [Nat.coprime_prod_left_iff]
  intro p hp
  rw [Nat.coprime_prod_right_iff]
  intro q hq
  exact (Nat.coprime_primes (hprime₁ p hp) (hprime₂ q hq)).2 fun hpq => by
    subst q
    exact (Finset.disjoint_left.mp hdisjoint hp hq)

/-- Coprime integers greater than one are distinct. -/
theorem ne_of_coprime_of_one_lt {a b : Nat}
    (ha : 1 < a) (hab : a.Coprime b) : a ≠ b := by
  intro h
  subst b
  have haone : a = 1 := by
    have hgcd := hab.gcd_eq_one
    simpa using hgcd
  omega

/-- The weak sector-cardinality statement discharges the Euler-product corollary. -/
theorem cmProductGrowthCorollary_of_abundance
    (H : FermatSectorAbundance) : CMProductGrowthCorollary := by
  intro B minimumProduct
  obtain ⟨T, hT, hBT, hminimumT, hsectorCard⟩ :=
    exists_scale_with_two_blocks_of_abundance H B minimumProduct
  let sector := negativeCMTraceSectorPrimes (T ^ 8)
  let m := cmBlockSize B T
  obtain ⟨S₁, S₂, hS₁, hS₂, hdisjoint, hcard₁, hcard₂⟩ :=
    exists_two_disjoint_subsets (S := sector) (m := m) hsectorCard
  let a₁ := S₁.prod id
  let a₂ := S₂.prod id
  have hTone : 1 ≤ T := by omega
  have hTtwo : 2 ≤ T := by omega
  have hsub₁ : S₁ ⊆ negativeCMTraceSectorPrimes (T ^ 8) := by simpa [sector] using hS₁
  have hsub₂ : S₂ ⊆ negativeCMTraceSectorPrimes (T ^ 8) := by simpa [sector] using hS₂
  have hprime₁ : ∀ p ∈ S₁, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp (hsub₁ hp)).2.1
  have hprime₂ : ∀ p ∈ S₂, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp (hsub₂ hp)).2.1
  have hmpos : 0 < m := by
    simp [m, cmBlockSize, cmGainDenominator, cmGainExponent]
    positivity
  have hnonempty₁ : S₁.Nonempty := Finset.card_pos.mp (by simpa [hcard₁] using hmpos)
  have hnonempty₂ : S₂.Nonempty := Finset.card_pos.mp (by simpa [hcard₂] using hmpos)
  have ha₁one : 1 < a₁ := prime_finset_product_gt_one hnonempty₁ hprime₁
  have ha₂one : 1 < a₂ := prime_finset_product_gt_one hnonempty₂ hprime₂
  have hcoprime : a₁.Coprime a₂ :=
    coprime_prime_finset_products hdisjoint hprime₁ hprime₂
  have hne : a₁ ≠ a₂ := ne_of_coprime_of_one_lt ha₁one hcoprime
  have hcard₁' : S₁.card = cmBlockSize B T := by simpa [m] using hcard₁
  have hcard₂' : S₂.card = cmBlockSize B T := by simpa [m] using hcard₂
  have ha₁Bound := sector_subset_product_le hTone S₁ hsub₁ hcard₁'
  have ha₂Bound := sector_subset_product_le hTone S₂ hsub₂ hcard₂'
  have htarget :
      24 * B * (logLoss (a₁ * a₂)) ^ 3 ≤ 2 ^ cmGainExponent B T :=
    target_le_gain_exponential hT hBT ha₁Bound ha₂Bound
  have hdensity₁ := exact_block_density fermatCubicLocalTraceFormula hTtwo S₁ hsub₁ hcard₁'
  have hdensity₂ := exact_block_density fermatCubicLocalTraceFormula hTtwo S₂ hsub₂ hcard₂'
  have hminimumA₁ : minimumProduct ≤ a₁ := by
    obtain ⟨p, hp⟩ := hnonempty₁
    have hpSector := Finset.mem_filter.mp (hsub₁ hp)
    have hpLower : T ^ 8 < p := (Finset.mem_Ioc.mp hpSector.1).1
    have hpProd : p ≤ a₁ :=
      Finset.single_le_prod' (f := id) (fun q hq => (hprime₁ q hq).one_le) hp
    have hTlePow : T ≤ T ^ 8 := le_self_pow hTone (by norm_num)
    exact hminimumT.trans (hTlePow.trans (hpLower.le.trans hpProd))
  refine ⟨{
    blocks := {a₁, a₂}
    enough_blocks := by simp [hne]
    modulus_gt_one := ?_
    pairwise_coprime := ?_
    product_large := ?_
    local_density := ?_ }⟩
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ha₁one
    · exact ha₂one
  · intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact hcoprime
    · exact hcoprime.symm
    · exact (hab rfl).elim
  · have ha₂pos : 0 < a₂ := Nat.zero_lt_of_lt ha₂one
    simpa [hne] using hminimumA₁.trans (Nat.le_mul_of_pos_right a₁ ha₂pos)
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    have hblockProduct : ({a₁, a₂} : Finset Nat).prod id = a₁ * a₂ := by simp [hne]
    rcases ha with rfl | rfl
    · rw [hblockProduct]
      calc
        24 * B * logLoss (a₁ * a₂) ^ 3 * a₁.totient ^ 3
            ≤ 2 ^ cmGainExponent B T * a₁.totient ^ 3 :=
          Nat.mul_le_mul_right _ htarget
        _ ≤ a₁ * (localCubeSolutions a₁).card := by simpa [a₁] using hdensity₁
    · rw [hblockProduct]
      calc
        24 * B * logLoss (a₁ * a₂) ^ 3 * a₂.totient ^ 3
            ≤ 2 ^ cmGainExponent B T * a₂.totient ^ 3 :=
          Nat.mul_le_mul_right _ htarget
        _ ≤ a₂ * (localCubeSolutions a₂).card := by simpa [a₂] using hdensity₂

/-- The published weighted CM theorem implies the weak abundance input in Lean. -/
theorem cmProductGrowthCorollary_of_source
    (H : FermatCMSource) : CMProductGrowthCorollary :=
  cmProductGrowthCorollary_of_abundance
    (fermatSectorAbundance_of_published H.sector)

#check @sector_prime_lt_two_pow
#check @sector_prime_log_le
#check @sector_weight_le_card_mul
#check @sector_weight_eventually_lower
#check @fermatSectorAbundance_of_published
#check @exists_scale_with_two_blocks_of_abundance
#check @exists_scale_with_two_blocks
#check @sector_trace_le_neg_scale
#check @sector_local_count_lower
#check @pointwise_local_gain_arithmetic
#check @sector_prime_local_gain
#check @two_mul_pow_le_succ_pow
#check @grouped_local_gain
#check @product_local_gain
#check @exact_block_density
#check @exists_two_disjoint_subsets
#check @sector_subset_product_le
#check @target_le_gain_exponential
#check @prime_finset_product_gt_one
#check @coprime_prime_finset_products
#check @cmProductGrowthCorollary_of_abundance
#check @cmProductGrowthCorollary_of_source
#print axioms cmProductGrowthCorollary_of_abundance
#print axioms cmProductGrowthCorollary_of_source

end

end K3Lean.SourceToCM
