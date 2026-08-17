import K3Lean.FormalConjecturesTarget
import K3Lean.WeakNegativeLocalGain

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Erdos 979 from only the first two Hecke moments

This module reruns the already checked many-block construction using the
larger prime supply `cos theta <= -1/4`.  The analytic input is therefore only
the first and second cosine moments, not full CM Sato--Tate and not all powers
of the Hecke character.
-/

namespace K3Lean.TwoMomentFinal

open Filter Set
open K3Lean.CMHeckeReduction
open K3Lean.CMProof
open K3Lean.ElementaryPrimeLifting
open K3Lean.Expanded
open K3Lean.FermatHasseAngle
open K3Lean.FiniteLifting
open K3Lean.FormalConjecturesTarget
open K3Lean.HeckeDeuringReduction
open K3Lean.LocalMultiplicativity
open K3Lean.ManyBlockCM
open K3Lean.SourceToCM
open K3Lean.SourceToPNT
open K3Lean.StandardCorollaries
open K3Lean.TwoMomentHecke
open K3Lean.WeakNegativeLocalGain
open scoped BigOperators Topology

noncomputable section

/-- Select the power-of-two scale and the growing family of exact-size blocks. -/
theorem exists_scale_with_many_blocks_of_weak_abundance
    (H : WeakNegativeAngleAbundance fermatTraceAngle) (B : Nat) :
    ∃ k T n : Nat,
      32 <= k /\ T = 2 ^ k /\ B <= T /\
      n = 24 * (k + 1) /\ n <= T /\
      n * cmBlockSize B T <=
        (weakNegativeAnglePrimes fermatTraceAngle (T ^ 8)).card := by
  obtain ⟨T0, hAfter⟩ := eventually_atTop.1 H
  let k := max T0 (max B 32)
  let T := 2 ^ k
  let n := 24 * (k + 1)
  have hT0k : T0 <= k := le_max_left _ _
  have hBk : B <= k :=
    (le_max_left B 32).trans (le_max_right T0 _)
  have h32k : 32 <= k :=
    (le_max_right B 32).trans (le_max_right T0 _)
  have hkT : k <= T := by
    dsimp [T]
    exact Nat.lt_two_pow_self.le
  have hBT : B <= T := hBk.trans hkT
  have hT0T : T0 <= T := hT0k.trans hkT
  have hLinear : 99840 * (k + 1) <= T := by
    simpa [T] using linear_scale_le_two_pow h32k
  have hnT : n <= T := by
    dsimp [n]
    exact (Nat.mul_le_mul_right (k + 1) (by norm_num : 24 <= 99840)).trans
      hLinear
  have hE : cmGainExponent B T <= 130 * T := by
    simp [cmGainExponent]
    omega
  have hm : cmBlockSize B T <= 4160 * T ^ 5 := by
    calc
      cmBlockSize B T = 32 * T ^ 4 * cmGainExponent B T := by
        simp [cmBlockSize, cmGainDenominator]
      _ <= 32 * T ^ 4 * (130 * T) :=
        Nat.mul_le_mul_left (32 * T ^ 4) hE
      _ = 4160 * T ^ 5 := by ring
  have hSize : n * cmBlockSize B T <= T ^ 6 := by
    calc
      n * cmBlockSize B T <= n * (4160 * T ^ 5) :=
        Nat.mul_le_mul_left n hm
      _ = 99840 * (k + 1) * T ^ 5 := by simp [n]; ring
      _ <= T * T ^ 5 := Nat.mul_le_mul_right (T ^ 5) hLinear
      _ = T ^ 6 := by ring
  have hSector := hAfter T hT0T
  exact ⟨k, T, n, h32k, rfl, hBT, rfl, hnT, hSize.trans hSector⟩

set_option maxHeartbeats 0 in
-- The dependent many-block construction needs more than Lean's default heartbeat budget.
/-- Build the finite CM family from the weak two-moment prime supply. -/
theorem exists_many_block_family_of_weak_abundance
    (hHasse : FermatCubicHasseBound)
    (H : WeakNegativeAngleAbundance fermatTraceAngle) (B : Nat) :
    ∃ F : CMHeckeFamily B,
      (14 * (Nat.log 2 (F.blocks.prod id) + 1)) *
          7 ^ F.blocks.card <= 10 ^ F.blocks.card := by
  obtain ⟨k, T, n, hk, hT, hBT, hn, hnT, hSectorCard⟩ :=
    exists_scale_with_many_blocks_of_weak_abundance H B
  let sector := weakNegativeAnglePrimes fermatTraceAngle (T ^ 8)
  let m := cmBlockSize B T
  obtain ⟨S, hSsub, hScard, hSpair⟩ :=
    exists_disjoint_fixed_card_blocks
      (S := sector) (m := m) (n := n) hSectorCard
  let a : Fin n -> Nat := fun i => (S i).prod id
  let blocks : Finset Nat := Finset.univ.image a
  let A := blocks.prod id
  let X := A ^ 2
  have hLinear : 99840 * (k + 1) <= T := by
    rw [hT]
    exact linear_scale_le_two_pow hk
  have hT2048 : 2048 <= T := by omega
  have hTlarge : 20000 <= T := by omega
  have hTone : 1 <= T := by omega
  have hTtwo : 2 <= T := by omega
  have hnFour : 4 <= n := by rw [hn]; omega
  have hnPos : 0 < n := by omega
  have hmPos : 0 < m := by
    simp [m, cmBlockSize, cmGainDenominator, cmGainExponent]
    positivity
  have hSnonempty : ∀ i, (S i).Nonempty := by
    intro i
    apply Finset.card_pos.mp
    rw [hScard i]
    exact hmPos
  have hSprime : ∀ i p, p ∈ S i -> p.Prime := by
    intro i p hp
    have hpSector := hSsub i hp
    exact (Finset.mem_filter.mp
      (Finset.mem_filter.mp hpSector).1).2.1
  have haOne : ∀ i, 1 < a i := by
    intro i
    exact prime_finset_product_gt_one (hSnonempty i) (hSprime i)
  have haCoprime : ∀ ⦃i j : Fin n⦄, i ≠ j -> (a i).Coprime (a j) := by
    intro i j hij
    exact coprime_prime_finset_products (hSpair hij) (hSprime i) (hSprime j)
  have haInjective : Function.Injective a := by
    intro i j hij
    by_contra hne
    exact (ne_of_coprime_of_one_lt (haOne i) (haCoprime hne)) hij
  have hBlocksCard : blocks.card = n := by
    dsimp [blocks]
    rw [Finset.card_image_of_injective _ haInjective, Finset.card_univ,
      Fintype.card_fin]
  have hBlocksNonempty : blocks.Nonempty := by
    apply Finset.card_pos.mp
    rw [hBlocksCard]
    exact hnPos
  have hBlocksOne : ∀ q ∈ blocks, 1 < q := by
    intro q hq
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hq
    exact haOne i
  have hBlocksCoprime :
      ∀ q ∈ blocks, ∀ r ∈ blocks, q ≠ r -> q.Coprime r := by
    intro q hq r hr hqr
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hr
    exact haCoprime (fun hij => hqr (congrArg a hij))
  have hAproduct : A = ∏ i : Fin n, a i := by
    dsimp [A, blocks]
    rw [Finset.prod_image haInjective.injOn]
    simp
  have haBound : ∀ i, a i <= 2 ^ (16 * T * m) := by
    intro i
    apply weak_sector_subset_product_le hTone (S i)
    · simpa [sector] using hSsub i
    · simpa [m] using hScard i
  have hAbound : A <= 2 ^ (16 * n * T * m) := by
    rw [hAproduct]
    calc
      (∏ i : Fin n, a i) <= ∏ _i : Fin n, 2 ^ (16 * T * m) :=
        Finset.prod_le_prod' fun i _hi => haBound i
      _ = (2 ^ (16 * T * m)) ^ n := by simp
      _ = 2 ^ (16 * T * m * n) :=
        (Nat.pow_mul 2 (16 * T * m) n).symm
      _ = 2 ^ (16 * n * T * m) := by
        congr 1
        ring
  have haLower : ∀ i, T ^ 8 <= a i := by
    intro i
    obtain ⟨p, hp⟩ := hSnonempty i
    have hpSector := Finset.mem_filter.mp (hSsub i hp)
    have hpSplitShell := Finset.mem_filter.mp hpSector.1
    have hpLower : T ^ 8 < p := (Finset.mem_Ioc.mp hpSplitShell.1).1
    have hpProduct : p <= a i :=
      Finset.single_le_prod' (f := id)
        (fun q hq => (hSprime i q hq).one_le) hp
    exact hpLower.le.trans hpProduct
  have hAlower : T ^ (8 * n) <= A := by
    rw [hAproduct, Nat.pow_mul]
    calc
      (T ^ 8) ^ n = ∏ _i : Fin n, T ^ 8 := by simp
      _ <= ∏ i : Fin n, a i :=
        Finset.prod_le_prod' fun i _hi => haLower i
  have hE : cmGainExponent B T <= 130 * T := by
    simp [cmGainExponent]
    omega
  have hmBound : m <= 4160 * T ^ 5 := by
    calc
      m = 32 * T ^ 4 * cmGainExponent B T := by
        simp [m, cmBlockSize, cmGainDenominator]
      _ <= 32 * T ^ 4 * (130 * T) :=
        Nat.mul_le_mul_left (32 * T ^ 4) hE
      _ = 4160 * T ^ 5 := by ring
  have hLog : Nat.log 2 A + 1 <= 17 * T ^ 7 :=
    binaryLog_succ_le_seventeen_scale_pow hT hn hmBound hLinear hAbound
  obtain ⟨hA2048, hSize, hLogCube⟩ :=
    many_block_product_size_conditions hT2048 hnFour hnT hLog hAlower
  have hPrime : 8 * n * A <= (primeBasesUpTo (A ^ 2)).card :=
    eight_mul_blocks_mul_A_le_primeBases_square hA2048 hSize
  have hTarget : 24 * B * (logLoss A) ^ 3 <=
      2 ^ cmGainExponent B T :=
    target_le_gain_exponential_many hTlarge hBT hnT
      (by simpa [m] using hAbound)
  have hFactor : 14 * (Nat.log 2 A + 1) <= 2 ^ (8 * (k + 1)) :=
    selector_factor_le_scale_power hT hLog
  have hSelectorN :
      (14 * (Nat.log 2 A + 1)) * 7 ^ n <= 10 ^ n :=
    selector_power_of_scale hn hFactor
  have hFamilyGrowth : ∀ q ∈ blocks,
      ((3 * X ^ 3) / q + 1) * B <=
        (localCubeSolutions q).card *
          (primeClassTarget blocks X q) ^ 3 := by
    intro q hq
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hq
    have haiA : a i <= A := by
      dsimp [A]
      exact Finset.single_le_prod'
        (fun r hr => (hBlocksOne r hr).le)
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    have haiPos : 0 < a i := Nat.zero_lt_of_lt (haOne i)
    have hScale : X <= logLoss A * (a i).totient *
        primeClassTarget blocks X (a i) := by
      have hSquare := square_le_logLoss_mul_totient_mul_target_many
        hA2048 haiPos haiA hnPos hPrime hLogCube
      dsimp [X, primeClassTarget]
      rw [hBlocksCard]
      simpa [A] using hSquare
    have haiX3 : a i <= X ^ 3 := by
      calc
        a i <= A := haiA
        _ <= A ^ 6 := le_self_pow (by omega) (by norm_num)
        _ = X ^ 3 := by simp [X]; ring
    have hDensity := weak_exact_block_density hHasse
      hTtwo (S i) (by simpa [sector] using hSsub i)
        (by simpa [m] using hScard i)
    have hLocal : 24 * B * (logLoss A) ^ 3 * (a i).totient ^ 3 <=
        a i * (localCubeSolutions (a i)).card := by
      exact (Nat.mul_le_mul_right ((a i).totient ^ 3) hTarget).trans hDensity
    have hCert := certificate_growth_of_scaled_bounds
      (B := B) (a := a i) (X := X)
      (g := primeClassTarget blocks X (a i)) (D := logLoss A)
      haiPos haiX3 hScale hLocal
    exact (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 6)).trans hCert
  let F : CMHeckeFamily B :=
    { blocks := blocks
      cutoff := X
      blocks_nonempty := hBlocksNonempty
      enough_blocks := by rw [hBlocksCard, hn]; omega
      modulus_gt_one := hBlocksOne
      pairwise_coprime := hBlocksCoprime
      cutoff_eq := rfl
      growth := hFamilyGrowth }
  refine ⟨F, ?_⟩
  simpa [F, A, hBlocksCard] using hSelectorN

/-- The weak supply supplies a complete finite block certificate. -/
theorem cmBlockPrimeInput_of_weak_abundance
    (hHasse : FermatCubicHasseBound)
    (H : WeakNegativeAngleAbundance fermatTraceAngle) :
    CMBlockPrimeInput := by
  intro B
  obtain ⟨F, hSelector⟩ :=
    exists_many_block_family_of_weak_abundance hHasse H B
  obtain ⟨a, ha, hLift⟩ := elementaryPrimeLifting_of_selector_power F hSelector
  exact ⟨F.toBlockCertificate a ha hLift⟩

/-- The exact Formal Conjectures target from only two Hecke cosine moments. -/
theorem erdos_979_k3_from_first_two_hecke_moments
    (hHasse : FermatCubicHasseBound)
    (hMoments : FirstTwoHeckeMoments fermatTraceAngle)
    (hAP : PrimeNumberTheoremModThreeOne) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  have hAbundance : WeakNegativeAngleAbundance fermatTraceAngle :=
    weakNegativeAngleAbundance_of_two_moments fermatTraceAngle hMoments hAP
  have hUnbounded : ∀ B : Nat, ∃ n : Nat, B <= f₃ n :=
    f₃_infinite_from_cm_blocks
      (cmBlockPrimeInput_of_weak_abundance hHasse hAbundance)
  exact formal_conjectures_limsup_of_f₃_tail_unbounded
    (nat_limsup_eq_infinity_of_unbounded hUnbounded)

/-- Every-power Hecke cancellation implies the strictly weaker two-moment endpoint. -/
theorem erdos_979_k3_from_full_hecke_cancellation
    (hHasse : FermatCubicHasseBound)
    (hHecke :
      K3Lean.HeckeCharacterCriterion.HeckePrimeCharacterCancellation
        fermatTraceAngle)
    (hAP : PrimeNumberTheoremModThreeOne) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  apply erdos_979_k3_from_first_two_hecke_moments hHasse
  · constructor
    · simpa using hHecke 1 (by norm_num)
    · simpa using hHecke 2 (by norm_num)
  · exact hAP

#check @erdos_979_k3_from_first_two_hecke_moments
#print axioms erdos_979_k3_from_first_two_hecke_moments

end

end K3Lean.TwoMomentFinal
