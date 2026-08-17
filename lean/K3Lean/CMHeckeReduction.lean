import K3Lean.BrunTitchmarshReduction
import K3Lean.SourceToCM

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Eight-block CM amplification for Erdos 979

This file derives the problem-specific `CMHeckeAmplificationCorollary` from
the standard counting CM Sato--Tate theorem for the Fermat cubic together with
the ordinary prime number theorem.

The proof extracts eight disjoint exact-size sets of negative-trace CM primes.
Their products are pairwise coprime candidate moduli.  The local cubic trace
formula and a Bernoulli product estimate amplify each local density, while
Mathlib's explicit Chebyshev lower bound controls the floor in the
prime-per-class target at cutoff `A^2`.
-/

namespace K3Lean.CMHeckeReduction

open Filter Set
open K3Lean.BrunTitchmarshReduction
open K3Lean.CMProof
open K3Lean.ErdosBrunTitchmarsh
open K3Lean.FiniteLifting
open K3Lean.LocalMultiplicativity
open K3Lean.LocalTraceFormula
open K3Lean.SourceTheorems
open K3Lean.SourceToCM
open K3Lean.SourceToPNT
open K3Lean.StandardCorollaries
open scoped BigOperators Topology

noncomputable section

theorem exists_disjoint_fixed_card_blocks
    {S : Finset Nat} {m n : Nat}
    (hcard : n * m ≤ S.card) :
    ∃ F : Fin n → Finset Nat,
      (∀ i, F i ⊆ S) ∧
      (∀ i, (F i).card = m) ∧
      Pairwise fun i j => Disjoint (F i) (F j) := by
  induction n generalizing S with
  | zero =>
      refine ⟨Fin.elim0, ?_, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ n ih =>
      have hmS : m ≤ S.card := by
        calc
          m = 1 * m := by simp
          _ ≤ (n + 1) * m :=
            Nat.mul_le_mul_right m (Nat.succ_le_succ (Nat.zero_le n))
          _ ≤ S.card := hcard
      obtain ⟨S₀, hS₀, hcard₀⟩ := Finset.exists_subset_card_eq hmS
      have hrestCard : n * m ≤ (S \ S₀).card := by
        rw [Finset.card_sdiff_of_subset hS₀, hcard₀]
        apply Nat.le_sub_of_add_le
        calc
          n * m + m = (n + 1) * m := by ring
          _ ≤ S.card := hcard
      obtain ⟨F, hFsub, hFcard, hFpair⟩ := ih hrestCard
      let G : Fin (n + 1) → Finset Nat := Fin.cases S₀ F
      have hS₀disjoint : ∀ i : Fin n, Disjoint S₀ (F i) := by
        intro i
        rw [Finset.disjoint_left]
        intro x hx₀ hxF
        have hxDiff := hFsub i hxF
        exact (Finset.mem_sdiff.mp hxDiff).2 hx₀
      refine ⟨G, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases hS₀ (fun j => ?_) i
        exact (hFsub j).trans Finset.sdiff_subset
      · intro i
        refine Fin.cases hcard₀ (fun j => hFcard j) i
      · intro i j hij
        refine Fin.cases ?_ (fun i' => ?_) i j hij
        · intro j hj
          refine Fin.cases (fun h => (h rfl).elim) (fun j' _ => ?_) j hj
          exact hS₀disjoint j'
        · intro j hj
          refine Fin.cases (fun _ => (hS₀disjoint i').symm)
            (fun j' hne => ?_) j hj
          exact hFpair (fun h => hne (congrArg Fin.succ h))

theorem exists_scale_with_eight_blocks_of_abundance
    (H : FermatSectorAbundance) (B : Nat) :
    ∃ T : Nat,
      70000 ≤ T ∧ B ≤ T ∧
        8 * cmBlockSize B T ≤
          (negativeCMTraceSectorPrimes (T ^ 8)).card := by
  obtain ⟨T₀, hafter⟩ := eventually_atTop.1 H
  let T := max T₀ (max B 70000)
  have hT₀T : T₀ ≤ T := le_max_left _ _
  have hBT : B ≤ T :=
    (le_max_left B 70000).trans (le_max_right T₀ _)
  have h70000T : 70000 ≤ T :=
    (le_max_right B 70000).trans (le_max_right T₀ _)
  have hsectorCard := hafter T hT₀T
  have hExp : cmGainExponent B T ≤ 130 * T := by
    simp [cmGainExponent]
    omega
  have hsize : 8 * cmBlockSize B T ≤ T ^ 6 := by
    calc
      8 * cmBlockSize B T =
          256 * T ^ 4 * cmGainExponent B T := by
        simp [cmBlockSize, cmGainDenominator]
        ring
      _ ≤ 256 * T ^ 4 * (130 * T) :=
        Nat.mul_le_mul_left (256 * T ^ 4) hExp
      _ = 33280 * T ^ 5 := by ring
      _ ≤ T * T ^ 5 :=
        Nat.mul_le_mul_right (T ^ 5) (by omega)
      _ = T ^ 6 := by ring
  exact ⟨T, h70000T, hBT, hsize.trans hsectorCard⟩

theorem target_le_gain_exponential_eight
    {B T A : Nat}
    (hT : 20000 ≤ T) (hBT : B ≤ T)
    (hA : A ≤ 2 ^ (128 * T * cmBlockSize B T)) :
    24 * B * (logLoss A) ^ 3 ≤ 2 ^ cmGainExponent B T := by
  let m := cmBlockSize B T
  let E := cmGainExponent B T
  have hTone : 1 ≤ T := by omega
  have hE : E ≤ 130 * T := by
    dsimp [E, cmGainExponent]
    omega
  have hlog : Nat.log 2 A ≤ 128 * T * m := by
    calc
      Nat.log 2 A ≤ Nat.log 2 (2 ^ (128 * T * m)) :=
        Nat.log_monotone hA
      _ = 128 * T * m := Nat.log_pow Nat.one_lt_two _
  have hm : m = 32 * T ^ 4 * E := by
    simp [m, E, cmBlockSize, cmGainDenominator]
  have hlogCoarse : Nat.log 2 A + 1 ≤ 532481 * T ^ 6 := by
    calc
      Nat.log 2 A + 1 ≤ 128 * T * m + 1 :=
        Nat.add_le_add_right hlog 1
      _ = 4096 * T ^ 5 * E + 1 := by rw [hm]; ring
      _ ≤ 4096 * T ^ 5 * (130 * T) + 1 := by
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_left (4096 * T ^ 5) hE) 1
      _ = 532480 * T ^ 6 + 1 := by ring
      _ ≤ 532481 * T ^ 6 := by
        have hT6pos : 0 < T ^ 6 := pow_pos (by omega) _
        have hT6 : 1 ≤ T ^ 6 := hT6pos
        nlinarith
  have hloss : logLoss A ≤ 4 * (532481 * T ^ 6) ^ 4 := by
    simp only [logLoss]
    exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hlogCoarse 4)
  have hconstant :
      1536 * 532481 ^ 12 ≤ 2 ^ 128 * 20000 ^ 9 := by
    norm_num
  have hconstantT :
      1536 * 532481 ^ 12 ≤ 2 ^ 128 * T ^ 9 := by
    exact hconstant.trans
      (Nat.mul_le_mul_left (2 ^ 128) (Nat.pow_le_pow_left hT 9))
  have hBpow : B ≤ 2 ^ B := (Nat.lt_two_pow_self).le
  have hTpow : T ^ 81 ≤ 2 ^ (128 * T) := by
    calc
      T ^ 81 ≤ T ^ 128 := pow_le_pow_right' hTone (by norm_num)
      _ ≤ (2 ^ T) ^ 128 :=
        Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) 128
      _ = 2 ^ (128 * T) := by
        rw [← Nat.pow_mul]
        congr 1 <;> ring
  calc
    24 * B * (logLoss A) ^ 3
        ≤ 24 * B * (4 * (532481 * T ^ 6) ^ 4) ^ 3 :=
      Nat.mul_le_mul_left (24 * B) (Nat.pow_le_pow_left hloss 3)
    _ = (1536 * 532481 ^ 12) * B * T ^ 72 := by ring
    _ ≤ (2 ^ 128 * T ^ 9) * B * T ^ 72 := by
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

theorem log_nat_le_div_192 {A : Nat} (hA : 2048 ≤ A) :
    Real.log (A : Real) ≤ (A : Real) / 192 := by
  have h2048mem : Real.exp 1 ≤ (2048 : Real) :=
    Real.exp_one_lt_three.le.trans (by norm_num)
  have hAmem : Real.exp 1 ≤ (A : Real) :=
    h2048mem.trans (by exact_mod_cast hA)
  have hratio := Real.log_div_self_antitoneOn h2048mem hAmem
    (by exact_mod_cast hA)
  have hlog2048 : Real.log (2048 : Real) = 11 * Real.log 2 := by
    rw [show (2048 : Real) = 2 ^ 11 by norm_num, Real.log_pow]
    norm_num
  have hconst : Real.log (2048 : Real) / 2048 ≤ (1 : Real) / 192 := by
    rw [hlog2048]
    nlinarith [Real.log_two_lt_d9]
  have hratio' : Real.log (A : Real) / (A : Real) ≤ (1 : Real) / 192 :=
    hratio.trans hconst
  have hApos : (0 : Real) < A := by positivity
  rw [div_le_iff₀ hApos] at hratio'
  nlinarith

theorem sixty_four_mul_le_primeBases_square
    {A : Nat} (hA : 2048 ≤ A) :
    64 * A ≤ (primeBasesUpTo (A ^ 2)).card := by
  have hpi := chebyshev_primeBases_square_lower
    (hA.trans' (by norm_num : 256 ≤ 2048))
  have hlog := log_nat_le_div_192 hA
  have hApos : (0 : Real) < A := by positivity
  have hPnonneg : (0 : Real) ≤ (primeBasesUpTo (A ^ 2)).card := by positivity
  have hreal : (64 : Real) * A ≤ (primeBasesUpTo (A ^ 2)).card := by
    nlinarith
  exact_mod_cast hreal

theorem square_le_logLoss_mul_totient_mul_target
    {A a : Nat} (hA : 2048 ≤ A) (haPos : 0 < a) (haA : a ≤ A) :
    A ^ 2 ≤ logLoss A * a.totient *
      ((primeBasesUpTo (A ^ 2)).card / (64 * a.totient)) := by
  let P := (primeBasesUpTo (A ^ 2)).card
  let phi := a.totient
  let d := 64 * phi
  let g := P / d
  let L := Nat.log 2 A + 1
  have hphiPos : 0 < phi := by
    dsimp [phi]
    exact Nat.totient_pos.mpr haPos
  have hdPos : 0 < d := by simp [d]; positivity
  have h64A := sixty_four_mul_le_primeBases_square hA
  have hdP : d ≤ P := by
    dsimp [d, phi, P]
    exact (Nat.mul_le_mul_left 64 ((Nat.totient_le a).trans haA)).trans h64A
  have hgPos : 0 < g := by
    dsimp [g]
    exact Nat.div_pos hdP hdPos
  have hP_lt : P < d * (g + 1) := by
    have hquot : P / d < P / d + 1 := Nat.lt_succ_self _
    have h := (Nat.div_lt_iff_lt_mul hdPos).mp hquot
    simpa [g, Nat.mul_comm] using h
  have hlogReal := real_log_nat_le_succ_log_two A
  have hchebReal := chebyshev_primeBases_square_lower
    (hA.trans' (by norm_num : 256 ≤ 2048))
  have hLnonneg : (0 : Real) ≤ L := by positivity
  have hPnonneg : (0 : Real) ≤ P := by positivity
  have hchebNat : A ^ 2 ≤ 3 * L * P := by
    have hreal : ((A ^ 2 : Nat) : Real) ≤ 3 * L * P := by
      rw [Nat.cast_pow]
      calc
        (A : Real) ^ 2 ≤ 3 * Real.log (A : Real) * (P : Real) := by
          simpa [P] using hchebReal
        _ ≤ 3 * (L : Real) * (P : Real) := by
          have hmul := mul_le_mul_of_nonneg_right hlogReal hPnonneg
          nlinarith
    exact_mod_cast hreal
  have hLlarge : 12 ≤ L := by
    have hlogMono : Nat.log 2 2048 ≤ Nat.log 2 A :=
      Nat.log_monotone hA
    have hlogBase : Nat.log 2 2048 = 11 := by
      rw [show 2048 = 2 ^ 11 by norm_num, Nat.log_pow Nat.one_lt_two]
    rw [hlogBase] at hlogMono
    dsimp [L]
    omega
  have h96 : 96 ≤ L ^ 3 := by
    calc
      96 ≤ 12 ^ 3 := by norm_num
      _ ≤ L ^ 3 := Nat.pow_le_pow_left hLlarge 3
  have hlossFactor : 384 * L ≤ logLoss A := by
    dsimp [L] at h96 ⊢
    simp only [logLoss]
    nlinarith
  have hpre : A ^ 2 ≤ 384 * L * phi * g := by
    calc
      A ^ 2 ≤ 3 * L * P := hchebNat
      _ ≤ 3 * L * (d * (g + 1)) :=
        Nat.mul_le_mul_left _ hP_lt.le
      _ = 192 * L * phi * (g + 1) := by simp [d]; ring
      _ ≤ 384 * L * phi * g := by
        have hgOne : 1 ≤ g := hgPos
        have hgg : g + 1 ≤ 2 * g := by omega
        calc
          192 * L * phi * (g + 1) ≤ 192 * L * phi * (2 * g) :=
            Nat.mul_le_mul_left _ hgg
          _ = 384 * L * phi * g := by ring
  dsimp [P, phi, d, g, L] at hpre ⊢
  calc
    A ^ 2 ≤ 384 * (Nat.log 2 A + 1) * a.totient *
        ((primeBasesUpTo (A ^ 2)).card / (64 * a.totient)) := hpre
    _ ≤ logLoss A * a.totient *
        ((primeBasesUpTo (A ^ 2)).card / (64 * a.totient)) :=
      by
        have h := Nat.mul_le_mul_right
          (a.totient *
            ((primeBasesUpTo (A ^ 2)).card / (64 * a.totient)))
          hlossFactor
        simpa only [Nat.mul_assoc] using h

set_option maxHeartbeats 0 in
-- The eight dependent blocks make elaboration exceed Lean's default heartbeat budget.
theorem cmHeckeAmplification_of_abundance
    (H : FermatSectorAbundance) : CMHeckeAmplificationCorollary := by
  intro B
  obtain ⟨T, hTlarge, hBT, hsectorCard⟩ :=
    exists_scale_with_eight_blocks_of_abundance H B
  let sector := negativeCMTraceSectorPrimes (T ^ 8)
  let m := cmBlockSize B T
  obtain ⟨S, hSsub, hScard, hSpair⟩ :=
    exists_disjoint_fixed_card_blocks
      (S := sector) (m := m) (n := 8) hsectorCard
  let a : Fin 8 → Nat := fun i => (S i).prod id
  let blocks : Finset Nat := Finset.univ.image a
  let A := blocks.prod id
  let X := A ^ 2
  have hTone : 1 ≤ T := by omega
  have hTtwo : 2 ≤ T := by omega
  have hmPos : 0 < m := by
    simp [m, cmBlockSize, cmGainDenominator, cmGainExponent]
    positivity
  have hSnonempty : ∀ i, (S i).Nonempty := by
    intro i
    apply Finset.card_pos.mp
    rw [hScard i]
    exact hmPos
  have hSprime : ∀ i p, p ∈ S i → p.Prime := by
    intro i p hp
    have hpSector := hSsub i hp
    exact (Finset.mem_filter.mp hpSector).2.1
  have haOne : ∀ i, 1 < a i := by
    intro i
    exact prime_finset_product_gt_one (hSnonempty i) (hSprime i)
  have haCoprime : ∀ ⦃i j : Fin 8⦄, i ≠ j → (a i).Coprime (a j) := by
    intro i j hij
    exact coprime_prime_finset_products (hSpair hij) (hSprime i) (hSprime j)
  have haInjective : Function.Injective a := by
    intro i j hij
    by_contra hne
    exact (ne_of_coprime_of_one_lt (haOne i) (haCoprime hne)) hij
  have hblocksCard : blocks.card = 8 := by
    dsimp [blocks]
    rw [Finset.card_image_of_injective _ haInjective, Finset.card_univ,
      Fintype.card_fin]
  have hblocksNonempty : blocks.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have := congrArg Finset.card hempty
    simp [hblocksCard] at this
  have hblocksOne : ∀ q ∈ blocks, 1 < q := by
    intro q hq
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hq
    exact haOne i
  have hblocksCoprime :
      ∀ q ∈ blocks, ∀ r ∈ blocks, q ≠ r → q.Coprime r := by
    intro q hq r hr hqr
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hr
    exact haCoprime (fun hij => hqr (congrArg a hij))
  have hAproduct : A = ∏ i : Fin 8, a i := by
    dsimp [A, blocks]
    rw [Finset.prod_image haInjective.injOn]
    simp
  have haBound : ∀ i, a i ≤ 2 ^ (16 * T * m) := by
    intro i
    apply sector_subset_product_le hTone (S i)
    · simpa [sector] using hSsub i
    · simpa [m] using hScard i
  have hAbound : A ≤ 2 ^ (128 * T * m) := by
    rw [hAproduct]
    calc
      (∏ i : Fin 8, a i) ≤ ∏ _i : Fin 8, 2 ^ (16 * T * m) :=
        Finset.prod_le_prod' fun i _hi => haBound i
      _ = (2 ^ (16 * T * m)) ^ 8 := by simp
      _ = 2 ^ (16 * T * m * 8) :=
        (Nat.pow_mul 2 (16 * T * m) 8).symm
      _ = 2 ^ (128 * T * m) := by
        congr 1
        ring
  have htarget : 24 * B * (logLoss A) ^ 3 ≤
      2 ^ cmGainExponent B T :=
    target_le_gain_exponential_eight (by omega) hBT
      (by simpa [m] using hAbound)
  have hA2048 : 2048 ≤ A := by
    let i : Fin 8 := ⟨0, by norm_num⟩
    obtain ⟨p, hp⟩ := hSnonempty i
    have hpSector := Finset.mem_filter.mp (hSsub i hp)
    have hpLower : T ^ 8 < p := (Finset.mem_Ioc.mp hpSector.1).1
    have hpMod : p ≤ a i :=
      Finset.single_le_prod' (f := id)
        (fun q hq => (hSprime i q hq).one_le) hp
    have haiA : a i ≤ A := by
      dsimp [A]
      exact Finset.single_le_prod'
        (fun q hq => (hblocksOne q hq).le)
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    have h2048T8 : 2048 ≤ T ^ 8 := by
      have hTpow := Nat.pow_le_pow_left hTlarge 8
      norm_num at hTpow ⊢
      omega
    exact h2048T8.trans (hpLower.le.trans (hpMod.trans haiA))
  refine ⟨{
    blocks := blocks
    cutoff := X
    blocks_nonempty := hblocksNonempty
    enough_blocks := by simpa [hblocksCard]
    modulus_gt_one := hblocksOne
    pairwise_coprime := hblocksCoprime
    cutoff_eq := rfl
    growth := ?_ }⟩
  intro q hq
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hq
  have haiA : a i ≤ A := by
    dsimp [A]
    exact Finset.single_le_prod'
      (fun q hq => (hblocksOne q hq).le)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have haiPos : 0 < a i := Nat.zero_lt_of_lt (haOne i)
  have hscale : X ≤ logLoss A * (a i).totient *
      primeClassTarget blocks X (a i) := by
    have hsquare := square_le_logLoss_mul_totient_mul_target
      hA2048 haiPos haiA
    dsimp [X, primeClassTarget]
    rw [hblocksCard]
    norm_num
    simpa [A] using hsquare
  have haiX3 : a i ≤ X ^ 3 := by
    calc
      a i ≤ A := haiA
      _ ≤ A ^ 6 := le_self_pow (by omega) (by norm_num)
      _ = X ^ 3 := by simp [X]; ring
  have hdensity := exact_block_density fermatCubicLocalTraceFormula
    hTtwo (S i) (by simpa [sector] using hSsub i)
      (by simpa [m] using hScard i)
  have hlocal : 24 * B * (logLoss A) ^ 3 * (a i).totient ^ 3 ≤
      a i * (localCubeSolutions (a i)).card := by
    exact (Nat.mul_le_mul_right ((a i).totient ^ 3) htarget).trans hdensity
  have hcert := certificate_growth_of_scaled_bounds
    (B := B) (a := a i) (X := X)
    (g := primeClassTarget blocks X (a i)) (D := logLoss A)
    haiPos haiX3 hscale hlocal
  exact (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 6)).trans hcert

theorem cmHeckeAmplification_of_satoTate_pnt
    (hST : FermatCMSatoTate)
    (hPNT : OrdinaryPrimeNumberTheorem) :
    CMHeckeAmplificationCorollary :=
  cmHeckeAmplification_of_abundance
    (fermatSectorAbundance_of_satoTate_pnt hST hPNT)

/--
The logarithmically weighted fixed-sector Hecke--Deuring theorem already
contains the prime-density information needed by the block construction, so
this route does not require the ordinary prime number theorem separately.
-/
theorem cmHeckeAmplification_of_weighted_sector
    (hCM : PublishedFermatCMSector) :
    CMHeckeAmplificationCorollary :=
  cmHeckeAmplification_of_abundance
    (fermatSectorAbundance_of_published hCM)

theorem erdos_979_k3_from_famous_inputs
    (hST : FermatCMSatoTate)
    (hPNT : OrdinaryPrimeNumberTheorem)
    (hBT : K3Lean.PublishedInputs.PublishedBrunTitchmarsh) :
    (let f : Nat → Nat := fun n =>
      (((Finset.range (n + 1)) ×ˢ
          (Finset.range (n + 1)) ×ˢ
          (Finset.range (n + 1))).filter (fun t =>
        t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
        Nat.Prime t.1 ∧ Nat.Prime t.2.1 ∧ Nat.Prime t.2.2 ∧
        t.1 ^ 3 + t.2.1 ^ 3 + t.2.2 ^ 3 = n)).card
     ∀ B N : Nat, ∃ n : Nat, N ≤ n ∧ B ≤ f n) := by
  exact erdos_979_k3_from_finite_corollaries
    (cmHeckeAmplification_of_satoTate_pnt hST hPNT)
    (brunTitchmarshPrimeLifting_of_published hBT)

/--
The same `k = 3` conclusion from two published inputs: the classical weighted
fixed-sector theorem for the Fermat CM curve and the standard
Brun--Titchmarsh theorem.  In this interface the ordinary PNT is not an input.
-/
theorem erdos_979_k3_from_two_published_inputs
    (hCM : PublishedFermatCMSector)
    (hBT : K3Lean.PublishedInputs.PublishedBrunTitchmarsh) :
    (let f : Nat → Nat := fun n =>
      (((Finset.range (n + 1)) ×ˢ
          (Finset.range (n + 1)) ×ˢ
          (Finset.range (n + 1))).filter (fun t =>
        t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
        Nat.Prime t.1 ∧ Nat.Prime t.2.1 ∧ Nat.Prime t.2.2 ∧
        t.1 ^ 3 + t.2.1 ^ 3 + t.2.2 ^ 3 = n)).card
     ∀ B N : Nat, ∃ n : Nat, N ≤ n ∧ B ≤ f n) := by
  exact erdos_979_k3_from_finite_corollaries
    (cmHeckeAmplification_of_weighted_sector hCM)
    (brunTitchmarshPrimeLifting_of_published hBT)

#check @cmHeckeAmplification_of_satoTate_pnt
#check @erdos_979_k3_from_famous_inputs
#print axioms erdos_979_k3_from_famous_inputs
#check @erdos_979_k3_from_two_published_inputs
#print axioms erdos_979_k3_from_two_published_inputs

end

end K3Lean.CMHeckeReduction
