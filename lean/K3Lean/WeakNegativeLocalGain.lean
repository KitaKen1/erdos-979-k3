import K3Lean.ManyBlockCM
import K3Lean.TwoMomentHecke

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Local cubic gain for the two-moment prime supply

The two-moment argument produces split primes with `cos theta <= -1/4`.
This file checks that this weaker angular inequality still gives the same
`1 + 1 / (32 T^4)` local-density gain used by the existing many-block proof.
-/

namespace K3Lean.WeakNegativeLocalGain

open K3Lean.FermatHasseAngle
open K3Lean.CMProof
open K3Lean.LocalMultiplicativity
open K3Lean.LocalTraceFormula
open K3Lean.PublishedInputs
open K3Lean.SourceTheorems
open K3Lean.SourceToCM
open K3Lean.TwoMomentHecke

noncomputable section

/-- A weakly negative canonical angle forces half of the old trace scale. -/
theorem weak_sector_trace_le_half_scale
    (hHasse : FermatCubicHasseBound)
    {T p : Nat} (hT : 1 <= T)
    (hp : p ∈ weakNegativeAnglePrimes fermatTraceAngle (T ^ 8)) :
    (fermatFrobeniusTrace p : Real) <=
      -(((T ^ 4) / 2 : Nat) : Real) := by
  have hpShell := Finset.mem_filter.mp hp
  have hpParts := Finset.mem_filter.mp hpShell.1
  have hpPrime : Nat.Prime p := hpParts.2.1
  have hpSplit : p % 3 = 1 := hpParts.2.2
  have hpLower : T ^ 8 < p := (Finset.mem_Ioc.mp hpParts.1).1
  have hCos : Real.cos (fermatTraceAngle p) <= -(1 : Real) / 4 := hpShell.2
  have hData := split_fermatTraceAngle_data hHasse p hpPrime hpSplit
  have hpRealPos : (0 : Real) < p := by exact_mod_cast hpPrime.pos
  have hSqrtPos : 0 < Real.sqrt (p : Real) := Real.sqrt_pos.2 hpRealPos
  have hTraceSqrt :
      (fermatFrobeniusTrace p : Real) <= -Real.sqrt (p : Real) / 2 := by
    rw [hData.2]
    nlinarith
  have hScaleSqrt : ((T ^ 4 : Nat) : Real) < Real.sqrt (p : Real) := by
    apply Real.lt_sqrt_of_sq_lt
    have hcast : ((T ^ 8 : Nat) : Real) < (p : Real) := by exact_mod_cast hpLower
    push_cast at hcast ⊢
    nlinarith
  have hCastDiv : (((T ^ 4) / 2 : Nat) : Real) <=
      ((T ^ 4 : Nat) : Real) / 2 := by
    exact Nat.cast_div_le
  exact hTraceSqrt.trans (by nlinarith)

/-- Weak-sector traces are nonzero. -/
theorem weak_sector_trace_ne_zero
    (hHasse : FermatCubicHasseBound)
    {T p : Nat} (hT : 2 <= T)
    (hp : p ∈ weakNegativeAnglePrimes fermatTraceAngle (T ^ 8)) :
    fermatFrobeniusTrace p ≠ 0 := by
  have hTrace := weak_sector_trace_le_half_scale hHasse (by omega : 1 <= T) hp
  have hDivPos : 0 < T ^ 4 / 2 := by
    apply Nat.div_pos
    · have := Nat.pow_le_pow_left hT 4
      norm_num at this ⊢
      omega
    · norm_num
  intro hZero
  rw [hZero] at hTrace
  have hDivPosReal : (0 : Real) < ((T ^ 4 / 2 : Nat) : Real) := by
    exact_mod_cast hDivPos
  nlinarith

/-- The finite-field trace formula gives the weakened explicit local count. -/
theorem weak_sector_local_count_lower
    (hHasse : FermatCubicHasseBound)
    {T p : Nat} (hT : 2 <= T)
    (hp : p ∈ weakNegativeAnglePrimes fermatTraceAngle (T ^ 8)) :
    (p - 1) * (p - 8 + T ^ 4 / 2) <=
      (localCubeSolutions p).card := by
  have hpShell := Finset.mem_filter.mp hp
  have hpParts := Finset.mem_filter.mp hpShell.1
  have hpPrime : Nat.Prime p := hpParts.2.1
  have hpLower : T ^ 8 < p := (Finset.mem_Ioc.mp hpParts.1).1
  have hpThree : 3 < p := by
    have hPow : 2 ^ 8 <= T ^ 8 := Nat.pow_le_pow_left hT 8
    omega
  have hpEight : 8 <= p := by
    have : 2 ^ 8 <= T ^ 8 := Nat.pow_le_pow_left hT 8
    omega
  have hTraceReal := weak_sector_trace_le_half_scale hHasse (by omega : 1 <= T) hp
  have hTraceInt : fermatFrobeniusTrace p <= -((T ^ 4 / 2 : Nat) : Int) := by
    exact_mod_cast hTraceReal
  have hFormula := fermatCubicLocalTraceFormula p hpPrime hpThree
    (weak_sector_trace_ne_zero hHasse hT hp)
  have hInt :
      (((p - 1) * (p - 8 + T ^ 4 / 2) : Nat) : Int) <=
        ((localCubeSolutions p).card : Int) := by
    have hFactor :
        (p : Int) - 8 + (T ^ 4 / 2 : Nat) <=
          (p : Int) - 8 - fermatFrobeniusTrace p := by
      have hNeg : ((T ^ 4 / 2 : Nat) : Int) <=
          -fermatFrobeniusTrace p := by linarith
      linarith
    have hpOneInt : (1 : Int) <= p := by exact_mod_cast hpPrime.one_le
    have hLeftNonneg : (0 : Int) <= (p : Int) - 1 := by linarith
    have hMul := mul_le_mul_of_nonneg_left hFactor hLeftNonneg
    rw [hFormula]
    push_cast [Nat.cast_sub (by omega : 1 <= p), Nat.cast_sub hpEight] at ⊢
    simpa [Nat.cast_pow] using hMul
  exact_mod_cast hInt

/-- The old denominator `32 T^4` still absorbs the weaker half-scale trace gain. -/
theorem weak_pointwise_local_gain_arithmetic
    {T p R : Nat}
    (hT : 2 <= T) (hpLower : T ^ 8 < p) (hpUpper : p <= 2 * T ^ 8)
    (hpEight : 8 <= p)
    (hR : (p - 1) * (p - 8 + T ^ 4 / 2) <= R) :
    cmGainDenominator T * (p * R) >=
      (cmGainDenominator T + 1) * (p - 1) ^ 3 := by
  let u := T ^ 4
  let v := u / 2
  have hu16 : 16 <= u := by
    dsimp [u]
    have := Nat.pow_le_pow_left hT 4
    norm_num at this ⊢
    exact this
  have hpLower' : u ^ 2 < p := by
    dsimp [u]
    convert hpLower using 1 <;> ring
  have hpUpper' : p <= 2 * u ^ 2 := by
    dsimp [u]
    convert hpUpper using 1 <;> ring
  have huv : u <= 2 * v + 1 := by
    have hDivision := Nat.mod_add_div u 2
    have hMod : u % 2 < 2 := Nat.mod_lt u (by norm_num)
    dsimp [v]
    omega
  have hBaseInt :
      ((32 : Int) * u + 1) * ((p : Int) - 1) ^ 3 <=
        32 * u *
          ((p : Int) * (((p : Int) - 1) * ((p : Int) - 8 + v))) := by
    have hu0 : (0 : Int) <= u := by positivity
    have hp0 : (0 : Int) <= p := by positivity
    have hpTwo : (2 : Int) <= p := by exact_mod_cast (by omega : 2 <= p)
    have hUV : (u : Int) <= 2 * (v : Int) + 1 := by exact_mod_cast huv
    have hUpper : (p : Int) <= 2 * (u : Int) ^ 2 := by exact_mod_cast hpUpper'
    have hU16 : (16 : Int) <= u := by exact_mod_cast hu16
    have hA : 0 <=
        (2 * (v : Int) + 1 - u) * (16 * (u : Int) * p) := by positivity
    have hB : 0 <=
        (p : Int) * (2 * (u : Int) ^ 2 - p) := by positivity
    have hC : 0 <=
        ((u : Int) - 16) * (u : Int) * p := by positivity
    have hD : 0 <= 16 * (u : Int) * ((p : Int) - 2) := by positivity
    have hE : 0 <= 2 * (p : Int) - 1 := by linarith
    nlinarith
  have hBase :
      (32 * u + 1) * (p - 1) ^ 3 <=
        32 * u * (p * ((p - 1) * (p - 8 + v))) := by
    have hpOne : 1 <= p := by omega
    have hCastInt :
        ((((32 * u + 1) * (p - 1) ^ 3 : Nat) : Int)) <=
          (((32 * u * (p * ((p - 1) * (p - 8 + v))) : Nat) : Int)) := by
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
        Nat.cast_pow]
      rw [Nat.cast_sub hpOne, Nat.cast_sub hpEight]
      exact hBaseInt
    exact_mod_cast hCastInt
  calc
    (cmGainDenominator T + 1) * (p - 1) ^ 3 <=
        cmGainDenominator T *
          (p * ((p - 1) * (p - 8 + T ^ 4 / 2))) := by
      simpa [cmGainDenominator, u, v, Nat.mul_assoc] using hBase
    _ <= cmGainDenominator T * (p * R) := by
      exact Nat.mul_le_mul_left (cmGainDenominator T)
        (Nat.mul_le_mul_left p hR)

/-- Every prime from the two-moment supply has the old pointwise local gain. -/
theorem weak_sector_prime_local_gain
    (hHasse : FermatCubicHasseBound)
    {T p : Nat} (hT : 2 <= T)
    (hp : p ∈ weakNegativeAnglePrimes fermatTraceAngle (T ^ 8)) :
    cmGainDenominator T * (p * (localCubeSolutions p).card) >=
      (cmGainDenominator T + 1) * p.totient ^ 3 := by
  have hpShell := Finset.mem_filter.mp hp
  have hpParts := Finset.mem_filter.mp hpShell.1
  have hpPrime : Nat.Prime p := hpParts.2.1
  have hpLower : T ^ 8 < p := (Finset.mem_Ioc.mp hpParts.1).1
  have hpUpper : p <= 2 * T ^ 8 := (Finset.mem_Ioc.mp hpParts.1).2
  have hpEight : 8 <= p := by
    have : 2 ^ 8 <= T ^ 8 := Nat.pow_le_pow_left hT 8
    omega
  rw [Nat.totient_prime hpPrime]
  exact weak_pointwise_local_gain_arithmetic hT hpLower hpUpper hpEight
    (weak_sector_local_count_lower hHasse hT hp)

/-- Multiplication of the weak-sector pointwise gains over a finite prime set. -/
theorem weak_product_local_gain
    (hHasse : FermatCubicHasseBound)
    {T : Nat} (hT : 2 <= T) (S : Finset Nat)
    (hS : S ⊆ weakNegativeAnglePrimes fermatTraceAngle (T ^ 8)) :
    (cmGainDenominator T + 1) ^ S.card *
        (S.prod id).totient ^ 3 <=
      cmGainDenominator T ^ S.card *
        ((S.prod id) * (localCubeSolutions (S.prod id)).card) := by
  have hPrime : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp
      (Finset.mem_filter.mp (hS hp)).1).2.1
  have hPointwise :
      ∏ p ∈ S,
          ((cmGainDenominator T + 1) * p.totient ^ 3) <=
        ∏ p ∈ S,
          (cmGainDenominator T * (p * (localCubeSolutions p).card)) := by
    exact Finset.prod_le_prod' fun p hp =>
      weak_sector_prime_local_gain hHasse hT (hS hp)
  rw [localCubeSolutions_card_prod_primes S hPrime,
    totient_prod_primes S hPrime]
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow,
    id_eq, mul_assoc] using hPointwise

/-- An exact-size weak-sector block has the same normalized density gain `2^E`. -/
theorem weak_exact_block_density
    (hHasse : FermatCubicHasseBound)
    {B T : Nat} (hT : 2 <= T) (S : Finset Nat)
    (hS : S ⊆ weakNegativeAnglePrimes fermatTraceAngle (T ^ 8))
    (hCard : S.card = cmBlockSize B T) :
    2 ^ cmGainExponent B T * (S.prod id).totient ^ 3 <=
      (S.prod id) * (localCubeSolutions (S.prod id)).card := by
  let K := cmGainDenominator T
  let E := cmGainExponent B T
  have hK : 0 < K := by simp [K, cmGainDenominator]; positivity
  have hCardKE : S.card = K * E := by
    simpa [K, E, cmBlockSize] using hCard
  have hProduct := weak_product_local_gain hHasse hT S hS
  rw [hCardKE] at hProduct
  have hGroup := grouped_local_gain (K := K) (E := E) hK
  have hScaled :
      (2 ^ E * K ^ (K * E)) * (S.prod id).totient ^ 3 <=
        K ^ (K * E) *
          ((S.prod id) * (localCubeSolutions (S.prod id)).card) := by
    calc
      (2 ^ E * K ^ (K * E)) * (S.prod id).totient ^ 3 <=
          (K + 1) ^ (K * E) * (S.prod id).totient ^ 3 :=
        Nat.mul_le_mul_right _ hGroup
      _ <= K ^ (K * E) *
          ((S.prod id) * (localCubeSolutions (S.prod id)).card) := by
        simpa [K] using hProduct
  have hCancel :
      K ^ (K * E) * (2 ^ E * (S.prod id).totient ^ 3) <=
        K ^ (K * E) *
          ((S.prod id) * (localCubeSolutions (S.prod id)).card) := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hScaled
  have hKPow : 0 < K ^ (K * E) := pow_pos hK _
  have hResult := Nat.le_of_mul_le_mul_left hCancel hKPow
  simpa [E] using hResult

/-- Weak-sector primes satisfy the product-size bound used by the many-block proof. -/
theorem weak_sector_prime_lt_two_pow
    {T p : Nat} (hT : 1 <= T)
    (hp : p ∈ weakNegativeAnglePrimes fermatTraceAngle (T ^ 8)) :
    p < 2 ^ (16 * T) := by
  have hpShell := Finset.mem_filter.mp hp
  have hpParts := Finset.mem_filter.mp hpShell.1
  have hpUpper : p <= 2 * T ^ 8 := (Finset.mem_Ioc.mp hpParts.1).2
  have hTlt : T < 2 ^ T := Nat.lt_two_pow_self
  have hTpow : T ^ 8 < (2 ^ T) ^ 8 :=
    Nat.pow_lt_pow_left hTlt (by norm_num)
  calc
    p <= 2 * T ^ 8 := hpUpper
    _ < 2 * (2 ^ T) ^ 8 := by omega
    _ = 2 ^ 1 * 2 ^ (T * 8) := by rw [Nat.pow_mul]; norm_num
    _ = 2 ^ (1 + T * 8) := (Nat.pow_add 2 1 (T * 8)).symm
    _ <= 2 ^ (16 * T) := by
      apply pow_le_pow_right'
      · norm_num
      · omega

/-- Product bound for an exact-size subset of the weak sector. -/
theorem weak_sector_subset_product_le
    {B T : Nat} (hT : 1 <= T)
    (S : Finset Nat)
    (hS : S ⊆ weakNegativeAnglePrimes fermatTraceAngle (T ^ 8))
    (hCard : S.card = cmBlockSize B T) :
    S.prod id <= 2 ^ (16 * T * cmBlockSize B T) := by
  calc
    S.prod id <= S.prod (fun _p => 2 ^ (16 * T)) := by
      exact Finset.prod_le_prod' fun p hp =>
        (weak_sector_prime_lt_two_pow hT (hS hp)).le
    _ = (2 ^ (16 * T)) ^ S.card := by simp
    _ = 2 ^ (16 * T * cmBlockSize B T) := by
      rw [hCard, ← Nat.pow_mul]

#check @weak_sector_prime_local_gain
#print axioms weak_sector_prime_local_gain
#check @weak_exact_block_density
#print axioms weak_exact_block_density

end

end K3Lean.WeakNegativeLocalGain
