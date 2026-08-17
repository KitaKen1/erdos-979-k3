import K3Lean.CMHeckeReduction
import K3Lean.ElementaryPrimeLifting
import K3Lean.SourceSatoTate

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Many CM blocks for an elementary prime-lifting route

The fixed eight-block construction pairs naturally with Brun--Titchmarsh.
The elementary residue-class bound loses a factor of order `log A`, so this
module develops a family with a growing number of pairwise-coprime CM blocks.
-/

namespace K3Lean.ManyBlockCM

open Filter Set
open K3Lean.BrunTitchmarshReduction
open K3Lean.CMHeckeReduction
open K3Lean.CMProof
open K3Lean.ElementaryPrimeLifting
open K3Lean.ErdosBrunTitchmarsh
open K3Lean.Expanded
open K3Lean.FiniteLifting
open K3Lean.LocalMultiplicativity
open K3Lean.LocalTraceFormula
open K3Lean.PublishedInputs
open K3Lean.SourceTheorems
open K3Lean.SourceSatoTate
open K3Lean.SourceToCM
open K3Lean.SourceToPNT
open K3Lean.StandardCorollaries
open scoped BigOperators Topology

noncomputable section

/-- The eight-block exponential estimate with an arbitrary block count `n`.
The coarse hypothesis `n ≤ T` is enough for all later applications. -/
theorem target_le_gain_exponential_many
    {B T n A : Nat}
    (hT : 20000 ≤ T) (hBT : B ≤ T) (hnT : n ≤ T)
    (hA : A ≤ 2 ^ (16 * n * T * cmBlockSize B T)) :
    24 * B * (logLoss A) ^ 3 ≤ 2 ^ cmGainExponent B T := by
  let m := cmBlockSize B T
  let E := cmGainExponent B T
  have hTone : 1 ≤ T := by omega
  have hE : E ≤ 130 * T := by
    dsimp [E, cmGainExponent]
    omega
  have hlog : Nat.log 2 A ≤ 16 * n * T * m := by
    calc
      Nat.log 2 A ≤ Nat.log 2 (2 ^ (16 * n * T * m)) :=
        Nat.log_monotone hA
      _ = 16 * n * T * m := Nat.log_pow Nat.one_lt_two _
  have hm : m = 32 * T ^ 4 * E := by
    simp [m, E, cmBlockSize, cmGainDenominator]
  have hlogCoarse : Nat.log 2 A + 1 ≤ 66561 * T ^ 7 := by
    calc
      Nat.log 2 A + 1 ≤ 16 * n * T * m + 1 :=
        Nat.add_le_add_right hlog 1
      _ ≤ 16 * T * T * m + 1 := by
        simpa only [Nat.mul_assoc] using Nat.add_le_add_right
          (Nat.mul_le_mul_right (T * m) (Nat.mul_le_mul_left 16 hnT)) 1
      _ = 512 * T ^ 6 * E + 1 := by rw [hm]; ring
      _ ≤ 512 * T ^ 6 * (130 * T) + 1 := by
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_left (512 * T ^ 6) hE) 1
      _ = 66560 * T ^ 7 + 1 := by ring
      _ ≤ 66561 * T ^ 7 := by
        have hT7 : 1 ≤ T ^ 7 := Nat.one_le_pow 7 T hTone
        nlinarith
  have hloss : logLoss A ≤ 4 * (66561 * T ^ 7) ^ 4 := by
    simp only [logLoss]
    exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hlogCoarse 4)
  have hconstant :
      1536 * 66561 ^ 12 ≤ 2 ^ 128 * 20000 ^ 6 := by
    norm_num
  have hconstantT :
      1536 * 66561 ^ 12 ≤ 2 ^ 128 * T ^ 6 := by
    exact hconstant.trans
      (Nat.mul_le_mul_left (2 ^ 128) (Nat.pow_le_pow_left hT 6))
  have hBpow : B ≤ 2 ^ B := (Nat.lt_two_pow_self).le
  have hTpow : T ^ 90 ≤ 2 ^ (128 * T) := by
    calc
      T ^ 90 ≤ T ^ 128 := pow_le_pow_right' hTone (by norm_num)
      _ ≤ (2 ^ T) ^ 128 :=
        Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) 128
      _ = 2 ^ (128 * T) := by
        rw [← Nat.pow_mul]
        congr 1 <;> ring
  calc
    24 * B * (logLoss A) ^ 3
        ≤ 24 * B * (4 * (66561 * T ^ 7) ^ 4) ^ 3 :=
      Nat.mul_le_mul_left (24 * B) (Nat.pow_le_pow_left hloss 3)
    _ = (1536 * 66561 ^ 12) * B * T ^ 84 := by ring
    _ ≤ (2 ^ 128 * T ^ 6) * B * T ^ 84 := by
      simpa only [Nat.mul_assoc] using
        Nat.mul_le_mul_right (B * T ^ 84) hconstantT
    _ = 2 ^ 128 * B * T ^ 90 := by ring
    _ ≤ 2 ^ 128 * 2 ^ B * 2 ^ (128 * T) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left (2 ^ 128) hBpow) hTpow
    _ = 2 ^ E := by
      dsimp [E, cmGainExponent]
      conv_rhs =>
        rw [show 128 * T + B + 128 = (128 + B) + 128 * T by ring]
      simp only [Nat.pow_add]

theorem eight_mul_blocks_mul_A_le_primeBases_square
    {A n : Nat} (hA : 2048 ≤ A)
    (hsize : 24 * n * (Nat.log 2 A + 1) ≤ A) :
    8 * n * A ≤ (primeBasesUpTo (A ^ 2)).card := by
  let L := Nat.log 2 A + 1
  let P := (primeBasesUpTo (A ^ 2)).card
  have hcheb := square_le_three_binaryLog_mul_primeBases
    (hA.trans' (by norm_num : 256 ≤ 2048))
  have hLpos : 0 < 3 * L := by simp [L]
  have hscaled : (3 * L) * (8 * n * A) ≤ (3 * L) * P := by
    calc
      (3 * L) * (8 * n * A) = (24 * n * L) * A := by ring
      _ ≤ A * A := Nat.mul_le_mul_right A (by simpa [L] using hsize)
      _ = A ^ 2 := by ring
      _ ≤ 3 * L * P := by simpa [L, P] using hcheb
      _ = (3 * L) * P := by ring
  exact Nat.le_of_mul_le_mul_left hscaled hLpos

/-- Floor-safe prime target for `n` blocks. -/
theorem square_le_logLoss_mul_totient_mul_target_many
    {A a n : Nat}
    (hA : 2048 ≤ A) (haPos : 0 < a) (haA : a ≤ A)
    (hnPos : 0 < n)
    (hprime : 8 * n * A ≤ (primeBasesUpTo (A ^ 2)).card)
    (hlogCube : 12 * n ≤ (Nat.log 2 A + 1) ^ 3) :
    A ^ 2 ≤ logLoss A * a.totient *
      ((primeBasesUpTo (A ^ 2)).card / (8 * n * a.totient)) := by
  let P := (primeBasesUpTo (A ^ 2)).card
  let phi := a.totient
  let d := 8 * n * phi
  let g := P / d
  let L := Nat.log 2 A + 1
  have hphiPos : 0 < phi := Nat.totient_pos.mpr haPos
  have hdPos : 0 < d := by
    dsimp [d]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) hnPos) hphiPos
  have hdP : d ≤ P := by
    dsimp [d, phi, P]
    exact (Nat.mul_le_mul_left (8 * n) ((Nat.totient_le a).trans haA)).trans
      hprime
  have hgPos : 0 < g := Nat.div_pos hdP hdPos
  have hP_lt : P < d * (g + 1) := by
    have hquot : P / d < P / d + 1 := Nat.lt_succ_self _
    have h := (Nat.div_lt_iff_lt_mul hdPos).mp hquot
    simpa [g, Nat.mul_comm] using h
  have hlogReal := real_log_nat_le_succ_log_two A
  have hchebReal := chebyshev_primeBases_square_lower
    (hA.trans' (by norm_num : 256 ≤ 2048))
  have hPnonneg : (0 : Real) ≤ P := by positivity
  have hchebNat : A ^ 2 ≤ 3 * L * P := by
    have hreal : ((A ^ 2 : Nat) : Real) ≤ 3 * L * P := by
      rw [Nat.cast_pow]
      calc
        (A : Real) ^ 2 ≤ 3 * Real.log (A : Real) * (P : Real) := by
          simpa [P] using hchebReal
        _ ≤ 3 * (L : Real) * (P : Real) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlogReal (by norm_num)) hPnonneg
    exact_mod_cast hreal
  have hlossFactor : 48 * n * L ≤ logLoss A := by
    have hmul := Nat.mul_le_mul_left (4 * L) hlogCube
    dsimp [L] at hmul ⊢
    simp only [logLoss]
    nlinarith
  have hpre : A ^ 2 ≤ 48 * n * L * phi * g := by
    calc
      A ^ 2 ≤ 3 * L * P := hchebNat
      _ ≤ 3 * L * (d * (g + 1)) :=
        Nat.mul_le_mul_left _ hP_lt.le
      _ = 24 * n * L * phi * (g + 1) := by simp [d]; ring
      _ ≤ 48 * n * L * phi * g := by
        have hgg : g + 1 ≤ 2 * g := by omega
        calc
          24 * n * L * phi * (g + 1) ≤
              24 * n * L * phi * (2 * g) :=
            Nat.mul_le_mul_left _ hgg
          _ = 48 * n * L * phi * g := by ring
  dsimp [P, phi, d, g, L] at hpre ⊢
  calc
    A ^ 2 ≤ 48 * n * (Nat.log 2 A + 1) * a.totient *
        ((primeBasesUpTo (A ^ 2)).card / (8 * n * a.totient)) := hpre
    _ ≤ logLoss A * a.totient *
        ((primeBasesUpTo (A ^ 2)).card / (8 * n * a.totient)) := by
      have h := Nat.mul_le_mul_right
        (a.totient *
          ((primeBasesUpTo (A ^ 2)).card / (8 * n * a.totient)))
        hlossFactor
      simpa only [Nat.mul_assoc] using h

theorem linear_scale_le_two_pow {k : Nat} (hk : 32 ≤ k) :
    99840 * (k + 1) ≤ 2 ^ k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => norm_num
  | succ d ih =>
      calc
        99840 * (32 + (d + 1) + 1) ≤
            2 * (99840 * (32 + d + 1)) := by omega
        _ ≤ 2 * 2 ^ (32 + d) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (32 + (d + 1)) := by
          rw [show 32 + (d + 1) = (32 + d) + 1 by omega, pow_succ]
          exact Nat.mul_comm _ _

theorem exists_scale_with_many_blocks_of_abundance
    (H : FermatSectorAbundance) (B : Nat) :
    ∃ k T n : Nat,
      32 ≤ k ∧ T = 2 ^ k ∧ B ≤ T ∧
      n = 24 * (k + 1) ∧ n ≤ T ∧
      n * cmBlockSize B T ≤
        (negativeCMTraceSectorPrimes (T ^ 8)).card := by
  obtain ⟨T₀, hafter⟩ := eventually_atTop.1 H
  let k := max T₀ (max B 32)
  let T := 2 ^ k
  let n := 24 * (k + 1)
  have hT₀k : T₀ ≤ k := le_max_left _ _
  have hBk : B ≤ k :=
    (le_max_left B 32).trans (le_max_right T₀ _)
  have h32k : 32 ≤ k :=
    (le_max_right B 32).trans (le_max_right T₀ _)
  have hkT : k ≤ T := by
    dsimp [T]
    exact Nat.lt_two_pow_self.le
  have hBT : B ≤ T := hBk.trans hkT
  have hT₀T : T₀ ≤ T := hT₀k.trans hkT
  have hlinear : 99840 * (k + 1) ≤ T := by
    simpa [T] using linear_scale_le_two_pow h32k
  have hnT : n ≤ T := by
    dsimp [n]
    exact (Nat.mul_le_mul_right (k + 1) (by norm_num : 24 ≤ 99840)).trans
      hlinear
  have hE : cmGainExponent B T ≤ 130 * T := by
    simp [cmGainExponent]
    omega
  have hm : cmBlockSize B T ≤ 4160 * T ^ 5 := by
    calc
      cmBlockSize B T = 32 * T ^ 4 * cmGainExponent B T := by
        simp [cmBlockSize, cmGainDenominator]
      _ ≤ 32 * T ^ 4 * (130 * T) :=
        Nat.mul_le_mul_left (32 * T ^ 4) hE
      _ = 4160 * T ^ 5 := by ring
  have hsize : n * cmBlockSize B T ≤ T ^ 6 := by
    calc
      n * cmBlockSize B T ≤ n * (4160 * T ^ 5) :=
        Nat.mul_le_mul_left n hm
      _ = 99840 * (k + 1) * T ^ 5 := by simp [n]; ring
      _ ≤ T * T ^ 5 := Nat.mul_le_mul_right (T ^ 5) hlinear
      _ = T ^ 6 := by ring
  have hsector := hafter T hT₀T
  exact ⟨k, T, n, h32k, rfl, hBT, rfl, hnT, hsize.trans hsector⟩

/-- The global product has only polynomially many binary digits at the selected
many-block scale. -/
theorem binaryLog_succ_le_seventeen_scale_pow
    {k T n m A : Nat}
    (hT : T = 2 ^ k)
    (hn : n = 24 * (k + 1))
    (hm : m ≤ 4160 * T ^ 5)
    (hlinear : 99840 * (k + 1) ≤ T)
    (hA : A ≤ 2 ^ (16 * n * T * m)) :
    Nat.log 2 A + 1 ≤ 17 * T ^ 7 := by
  have hlog : Nat.log 2 A ≤ 16 * n * T * m := by
    calc
      Nat.log 2 A ≤ Nat.log 2 (2 ^ (16 * n * T * m)) :=
        Nat.log_monotone hA
      _ = 16 * n * T * m := Nat.log_pow Nat.one_lt_two _
  have hTone : 1 ≤ T := by
    simp [hT]
    exact Nat.one_le_pow k 2 (by norm_num)
  calc
    Nat.log 2 A + 1 ≤ 16 * n * T * m + 1 :=
      Nat.add_le_add_right hlog 1
    _ ≤ 16 * n * T * (4160 * T ^ 5) + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left (16 * n * T) hm) 1
    _ = 16 * (99840 * (k + 1)) * T ^ 6 + 1 := by
      rw [hn]
      ring
    _ ≤ 16 * T * T ^ 6 + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right (T ^ 6)
        (Nat.mul_le_mul_left 16 hlinear)) 1
    _ = 16 * T ^ 7 + 1 := by ring
    _ ≤ 17 * T ^ 7 := by
      have hT7 : 1 ≤ T ^ 7 := Nat.one_le_pow 7 T hTone
      omega

/-- At the chosen power-of-two scale, the elementary residue-class loss fits
inside a short explicit power of two. -/
theorem selector_factor_le_scale_power
    {k T A : Nat}
    (hT : T = 2 ^ k)
    (hlog : Nat.log 2 A + 1 ≤ 17 * T ^ 7) :
    14 * (Nat.log 2 A + 1) ≤ 2 ^ (8 * (k + 1)) := by
  have hTone : 1 ≤ T := by
    simp [hT]
    exact Nat.one_le_pow k 2 (by norm_num)
  calc
    14 * (Nat.log 2 A + 1) ≤ 14 * (17 * T ^ 7) :=
      Nat.mul_le_mul_left 14 hlog
    _ = 238 * T ^ 7 := by ring
    _ ≤ 256 * T ^ 8 := by
      calc
        238 * T ^ 7 ≤ 256 * T * T ^ 7 := by
          exact Nat.mul_le_mul_right (T ^ 7) (by omega)
        _ = 256 * T ^ 8 := by ring
    _ = 2 ^ 8 * (2 ^ k) ^ 8 := by rw [hT]; norm_num
    _ = 2 ^ 8 * 2 ^ (k * 8) := by rw [← Nat.pow_mul]
    _ = 2 ^ (8 + k * 8) := (Nat.pow_add 2 8 (k * 8)).symm
    _ = 2 ^ (8 * (k + 1)) := by
      congr 1
      ring

/-- The exponential gain from `n = 24(k+1)` blocks absorbs the elementary
logarithmic residue-class loss. -/
theorem selector_power_of_scale
    {k n C : Nat}
    (hn : n = 24 * (k + 1))
    (hC : C ≤ 2 ^ (8 * (k + 1))) :
    C * 7 ^ n ≤ 10 ^ n := by
  have hbase : 2 ^ 8 * 7 ^ 24 ≤ 10 ^ 24 := by norm_num
  calc
    C * 7 ^ n ≤ 2 ^ (8 * (k + 1)) * 7 ^ n :=
      Nat.mul_le_mul_right (7 ^ n) hC
    _ = 2 ^ (8 * (k + 1)) * 7 ^ (24 * (k + 1)) := by rw [hn]
    _ = (2 ^ 8 * 7 ^ 24) ^ (k + 1) := by
      rw [mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
    _ ≤ (10 ^ 24) ^ (k + 1) := Nat.pow_le_pow_left hbase (k + 1)
    _ = 10 ^ n := by
      rw [hn, ← Nat.pow_mul]

/-- A sufficiently large global product simultaneously controls the prime
floor and the cubic logarithmic loss used in every block certificate. -/
theorem many_block_product_size_conditions
    {T n A : Nat}
    (hT2048 : 2048 ≤ T)
    (hnFour : 4 ≤ n)
    (hnT : n ≤ T)
    (hlog : Nat.log 2 A + 1 ≤ 17 * T ^ 7)
    (hAlower : T ^ (8 * n) ≤ A) :
    2048 ≤ A ∧
      24 * n * (Nat.log 2 A + 1) ≤ A ∧
      12 * n ≤ (Nat.log 2 A + 1) ^ 3 := by
  have hTone : 1 ≤ T := hT2048.trans' (by norm_num)
  have hTtwo : 2 ≤ T := hT2048.trans' (by norm_num)
  have hTA : T ≤ A := by
    exact (le_self_pow hTone (by omega : 8 * n ≠ 0)).trans hAlower
  have hA2048 : 2048 ≤ A := hT2048.trans hTA
  have h408T : 408 ≤ T := hT2048.trans' (by norm_num)
  have hsize : 24 * n * (Nat.log 2 A + 1) ≤ A := by
    calc
      24 * n * (Nat.log 2 A + 1) ≤ 24 * n * (17 * T ^ 7) :=
        Nat.mul_le_mul_left (24 * n) hlog
      _ = 408 * n * T ^ 7 := by ring
      _ ≤ T * T * T ^ 7 := by
        exact Nat.mul_le_mul_right (T ^ 7) (Nat.mul_le_mul h408T hnT)
      _ = T ^ 9 := by ring
      _ ≤ T ^ (8 * n) := pow_le_pow_right' hTone (by omega)
      _ ≤ A := hAlower
  have htwoPowA : 2 ^ n ≤ A := by
    calc
      2 ^ n ≤ T ^ n := Nat.pow_le_pow_left hTtwo n
      _ ≤ T ^ (8 * n) := pow_le_pow_right' hTone (by omega)
      _ ≤ A := hAlower
  have hnLog : n ≤ Nat.log 2 A :=
    Nat.le_log_of_pow_le Nat.one_lt_two htwoPowA
  have hnL : n ≤ Nat.log 2 A + 1 := hnLog.trans (Nat.le_add_right _ _)
  have hnSquare : 16 ≤ n ^ 2 := by
    calc
      16 = 4 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hnFour 2
  have hcube : 12 * n ≤ (Nat.log 2 A + 1) ^ 3 := by
    calc
      12 * n ≤ 16 * n := Nat.mul_le_mul_right n (by norm_num)
      _ ≤ n ^ 2 * n := Nat.mul_le_mul_right n hnSquare
      _ = n ^ 3 := by ring
      _ ≤ (Nat.log 2 A + 1) ^ 3 := Nat.pow_le_pow_left hnL 3
  exact ⟨hA2048, hsize, hcube⟩

set_option maxHeartbeats 0 in
/-- A CM family with enough independent blocks to use the elementary
prime-lifting argument.  No theorem about primes in arithmetic progressions is
used in this construction. -/
theorem exists_many_block_family_of_abundance
    (H : FermatSectorAbundance) (B : Nat) :
    ∃ F : CMHeckeFamily B,
      (14 * (Nat.log 2 (F.blocks.prod id) + 1)) *
          7 ^ F.blocks.card ≤ 10 ^ F.blocks.card := by
  obtain ⟨k, T, n, hk, hT, hBT, hn, hnT, hsectorCard⟩ :=
    exists_scale_with_many_blocks_of_abundance H B
  let sector := negativeCMTraceSectorPrimes (T ^ 8)
  let m := cmBlockSize B T
  obtain ⟨S, hSsub, hScard, hSpair⟩ :=
    exists_disjoint_fixed_card_blocks
      (S := sector) (m := m) (n := n) hsectorCard
  let a : Fin n → Nat := fun i => (S i).prod id
  let blocks : Finset Nat := Finset.univ.image a
  let A := blocks.prod id
  let X := A ^ 2
  have hlinear : 99840 * (k + 1) ≤ T := by
    rw [hT]
    exact linear_scale_le_two_pow hk
  have hT2048 : 2048 ≤ T := by omega
  have hTlarge : 20000 ≤ T := by omega
  have hTone : 1 ≤ T := by omega
  have hTtwo : 2 ≤ T := by omega
  have hnFour : 4 ≤ n := by rw [hn]; omega
  have hnPos : 0 < n := by omega
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
  have haCoprime : ∀ ⦃i j : Fin n⦄, i ≠ j → (a i).Coprime (a j) := by
    intro i j hij
    exact coprime_prime_finset_products (hSpair hij) (hSprime i) (hSprime j)
  have haInjective : Function.Injective a := by
    intro i j hij
    by_contra hne
    exact (ne_of_coprime_of_one_lt (haOne i) (haCoprime hne)) hij
  have hblocksCard : blocks.card = n := by
    dsimp [blocks]
    rw [Finset.card_image_of_injective _ haInjective, Finset.card_univ,
      Fintype.card_fin]
  have hblocksNonempty : blocks.Nonempty := by
    apply Finset.card_pos.mp
    rw [hblocksCard]
    exact hnPos
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
  have hAproduct : A = ∏ i : Fin n, a i := by
    dsimp [A, blocks]
    rw [Finset.prod_image haInjective.injOn]
    simp
  have haBound : ∀ i, a i ≤ 2 ^ (16 * T * m) := by
    intro i
    apply sector_subset_product_le hTone (S i)
    · simpa [sector] using hSsub i
    · simpa [m] using hScard i
  have hAbound : A ≤ 2 ^ (16 * n * T * m) := by
    rw [hAproduct]
    calc
      (∏ i : Fin n, a i) ≤ ∏ _i : Fin n, 2 ^ (16 * T * m) :=
        Finset.prod_le_prod' fun i _hi => haBound i
      _ = (2 ^ (16 * T * m)) ^ n := by simp
      _ = 2 ^ (16 * T * m * n) :=
        (Nat.pow_mul 2 (16 * T * m) n).symm
      _ = 2 ^ (16 * n * T * m) := by
        congr 1
        ring
  have haLower : ∀ i, T ^ 8 ≤ a i := by
    intro i
    obtain ⟨p, hp⟩ := hSnonempty i
    have hpSector := Finset.mem_filter.mp (hSsub i hp)
    have hpLower : T ^ 8 < p := (Finset.mem_Ioc.mp hpSector.1).1
    have hpProduct : p ≤ a i :=
      Finset.single_le_prod' (f := id)
        (fun q hq => (hSprime i q hq).one_le) hp
    exact hpLower.le.trans hpProduct
  have hAlower : T ^ (8 * n) ≤ A := by
    rw [hAproduct, Nat.pow_mul]
    calc
      (T ^ 8) ^ n = ∏ _i : Fin n, T ^ 8 := by simp
      _ ≤ ∏ i : Fin n, a i :=
        Finset.prod_le_prod' fun i _hi => haLower i
  have hE : cmGainExponent B T ≤ 130 * T := by
    simp [cmGainExponent]
    omega
  have hmBound : m ≤ 4160 * T ^ 5 := by
    calc
      m = 32 * T ^ 4 * cmGainExponent B T := by
        simp [m, cmBlockSize, cmGainDenominator]
      _ ≤ 32 * T ^ 4 * (130 * T) :=
        Nat.mul_le_mul_left (32 * T ^ 4) hE
      _ = 4160 * T ^ 5 := by ring
  have hlog : Nat.log 2 A + 1 ≤ 17 * T ^ 7 :=
    binaryLog_succ_le_seventeen_scale_pow hT hn hmBound hlinear hAbound
  obtain ⟨hA2048, hsize, hlogCube⟩ :=
    many_block_product_size_conditions hT2048 hnFour hnT hlog hAlower
  have hprime : 8 * n * A ≤ (primeBasesUpTo (A ^ 2)).card :=
    eight_mul_blocks_mul_A_le_primeBases_square hA2048 hsize
  have htarget : 24 * B * (logLoss A) ^ 3 ≤
      2 ^ cmGainExponent B T :=
    target_le_gain_exponential_many hTlarge hBT hnT
      (by simpa [m] using hAbound)
  have hfactor : 14 * (Nat.log 2 A + 1) ≤ 2 ^ (8 * (k + 1)) :=
    selector_factor_le_scale_power hT hlog
  have hselectorN :
      (14 * (Nat.log 2 A + 1)) * 7 ^ n ≤ 10 ^ n :=
    selector_power_of_scale hn hfactor
  have hfamilyGrowth : ∀ q ∈ blocks,
      ((3 * X ^ 3) / q + 1) * B ≤
        (localCubeSolutions q).card *
          (primeClassTarget blocks X q) ^ 3 := by
    intro q hq
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hq
    have haiA : a i ≤ A := by
      dsimp [A]
      exact Finset.single_le_prod'
        (fun r hr => (hblocksOne r hr).le)
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    have haiPos : 0 < a i := Nat.zero_lt_of_lt (haOne i)
    have hscale : X ≤ logLoss A * (a i).totient *
        primeClassTarget blocks X (a i) := by
      have hsquare := square_le_logLoss_mul_totient_mul_target_many
        hA2048 haiPos haiA hnPos hprime hlogCube
      dsimp [X, primeClassTarget]
      rw [hblocksCard]
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
  let F : CMHeckeFamily B :=
    { blocks := blocks
      cutoff := X
      blocks_nonempty := hblocksNonempty
      enough_blocks := by rw [hblocksCard, hn]; omega
      modulus_gt_one := hblocksOne
      pairwise_coprime := hblocksCoprime
      cutoff_eq := rfl
      growth := hfamilyGrowth }
  refine ⟨F, ?_⟩
  simpa [F, A, hblocksCard] using hselectorN

/-- The weak CM-sector abundance statement alone now supplies a complete
finite block certificate; no PNT in arithmetic progressions or
Brun--Titchmarsh theorem is used. -/
theorem cmBlockPrimeInput_of_abundance_elementary
    (H : FermatSectorAbundance) : CMBlockPrimeInput := by
  intro B
  obtain ⟨F, hselector⟩ := exists_many_block_family_of_abundance H B
  obtain ⟨a, ha, hlift⟩ := elementaryPrimeLifting_of_selector_power F hselector
  exact ⟨F.toBlockCertificate a ha hlift⟩

/-- Tail-unboundedness of the literal unordered representation count from the
weak CM-sector abundance statement. -/
theorem erdos_979_k3_from_sector_abundance_elementary
    (H : FermatSectorAbundance) :
    (let f : Nat → Nat := fun n =>
      (((Finset.range (n + 1)) ×ˢ
          (Finset.range (n + 1)) ×ˢ
          (Finset.range (n + 1))).filter (fun t =>
        t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
        Nat.Prime t.1 ∧ Nat.Prime t.2.1 ∧ Nat.Prime t.2.2 ∧
        t.1 ^ 3 + t.2.1 ^ 3 + t.2.2 ^ 3 = n)).card
     ∀ B N : Nat, ∃ n : Nat, N ≤ n ∧ B ≤ f n) := by
  change ∀ B N : Nat, ∃ n : Nat, N ≤ n ∧ B ≤ f₃ n
  exact nat_limsup_eq_infinity_of_unbounded
    (f₃_infinite_from_cm_blocks (cmBlockPrimeInput_of_abundance_elementary H))

/-- Erdős Problem 979 for `k = 3` from one source-level published input: the
classical logarithmically weighted fixed-sector theorem for the Fermat CM
curve.  The ordinary PNT and Brun--Titchmarsh are not assumptions. -/
theorem erdos_979_k3_from_weighted_cm_sector_only
    (hCM : PublishedFermatCMSector) :
    (let f : Nat → Nat := fun n =>
      (((Finset.range (n + 1)) ×ˢ
          (Finset.range (n + 1)) ×ˢ
          (Finset.range (n + 1))).filter (fun t =>
        t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
        Nat.Prime t.1 ∧ Nat.Prime t.2.1 ∧ Nat.Prime t.2.2 ∧
        t.1 ^ 3 + t.2.1 ^ 3 + t.2.2 ^ 3 = n)).card
     ∀ B N : Nat, ∃ n : Nat, N ≤ n ∧ B ≤ f n) := by
  exact erdos_979_k3_from_sector_abundance_elementary
    (fermatSectorAbundance_of_published hCM)

/-- The same result with two familiar source-level inputs: counting CM
Sato--Tate for the Fermat cubic and the ordinary prime number theorem.  This
interface avoids both logarithmic weights and every theorem about primes in
arithmetic progressions. -/
theorem erdos_979_k3_from_cm_sato_tate_and_pnt
    (hST : FermatCMSatoTate)
    (hPNT : OrdinaryPrimeNumberTheorem) :
    (let f : Nat → Nat := fun n =>
      (((Finset.range (n + 1)) ×ˢ
          (Finset.range (n + 1)) ×ˢ
          (Finset.range (n + 1))).filter (fun t =>
        t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
        Nat.Prime t.1 ∧ Nat.Prime t.2.1 ∧ Nat.Prime t.2.2 ∧
        t.1 ^ 3 + t.2.1 ^ 3 + t.2.2 ^ 3 = n)).card
     ∀ B N : Nat, ∃ n : Nat, N ≤ n ∧ B ≤ f n) := by
  exact erdos_979_k3_from_sector_abundance_elementary
    (fermatSectorAbundance_of_satoTate_pnt hST hPNT)

/-- Public endpoint with the two familiar external source statements expanded
in the hypotheses.  The Sato--Tate input keeps the Frobenius angle and interval
arbitrary, exactly as in the published CM branch after fixing only the curve to
be the Fermat cubic.  The interval specialization, trace-sector conversion,
small-prime removal, and mass computation occur in the proof. -/
theorem erdos_979_k3
    (hST :
      ∃ theta : Nat → Real,
        (∀ p : Nat, Nat.Prime p → p ≠ 3 →
          theta p ∈ Set.Icc 0 Real.pi ∧
            (↑((p : Int) + 1 - Int.ofNat
                (Nat.card
                    {uv : ZMod p × ZMod p //
                      1 + uv.1 ^ 3 + uv.2 ^ 3 = 0} +
                  Nat.card
                    {v : ZMod p // 1 + v ^ 3 = 0})) : Real) =
              2 * Real.sqrt p * Real.cos (theta p)) ∧
        ∀ alpha beta : Real,
          0 ≤ alpha → alpha ≤ beta → beta ≤ Real.pi →
          Tendsto
            (fun x : Real =>
              (((((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).filter
                    (fun p => p ≠ 3 ∧ theta p ∈ Set.Icc alpha beta)).card : Real) /
                (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : Real)))
            atTop
            (nhds
              ((if Real.pi / 2 ∈ Set.Icc alpha beta then (1 : Real) else 0) / 2 +
                (beta - alpha) / (2 * Real.pi))))
    (hPNT :
      Tendsto
        (fun X : Nat =>
          (((Finset.range (X + 1)).filter Nat.Prime).card : Real) *
            Real.log X / (X : Real))
        atTop (nhds (1 : Real))) :
    (let f : Nat → Nat := fun n =>
      (((Finset.range (n + 1)) ×ˢ
          (Finset.range (n + 1)) ×ˢ
          (Finset.range (n + 1))).filter (fun t =>
        t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
        Nat.Prime t.1 ∧ Nat.Prime t.2.1 ∧ Nat.Prime t.2.2 ∧
        t.1 ^ 3 + t.2.1 ^ 3 + t.2.2 ^ 3 = n)).card
     ∀ B N : Nat, ∃ n : Nat, N ≤ n ∧ B ≤ f n) := by
  let sourceST : FermatCMAngleSatoTate := by
    rcases hST with ⟨theta, hAngle, hDistribution⟩
    refine ⟨theta, ?_, ?_⟩
    · intro p hp hp3
      simpa [fermatFrobeniusTrace, fermatProjectivePointCount] using
        hAngle p hp hp3
    · intro alpha beta hAlpha hAlphaBeta hBeta
      simpa [primesUpTo, primeCounting] using
        hDistribution alpha beta hAlpha hAlphaBeta hBeta
  exact erdos_979_k3_from_cm_sato_tate_and_pnt
    (fermatCMSatoTate_of_angle_satoTate sourceST) hPNT

#check @target_le_gain_exponential_many
#check @eight_mul_blocks_mul_A_le_primeBases_square
#check @square_le_logLoss_mul_totient_mul_target_many
#check @linear_scale_le_two_pow
#check @exists_scale_with_many_blocks_of_abundance
#check @binaryLog_succ_le_seventeen_scale_pow
#check @selector_factor_le_scale_power
#check @selector_power_of_scale
#check @many_block_product_size_conditions
#check @exists_many_block_family_of_abundance
#check @cmBlockPrimeInput_of_abundance_elementary
#check @erdos_979_k3_from_sector_abundance_elementary
#check @erdos_979_k3_from_weighted_cm_sector_only
#print axioms erdos_979_k3_from_weighted_cm_sector_only
#check @erdos_979_k3_from_cm_sato_tate_and_pnt
#print axioms erdos_979_k3_from_cm_sato_tate_and_pnt
#check @erdos_979_k3
#print axioms erdos_979_k3

end

end K3Lean.ManyBlockCM
