import K3Lean.SourceTheorems
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# The elementary local trace formula for the Fermat cubic

Everything in this file is finite algebra.  The projective Fermat cubic is
covered by the unique representatives `[1 : u : v]` and `[0 : 1 : v]`.
At a split prime its boundary has nine points, and every all-nonzero
projective point has exactly `p - 1` nonzero scalar representatives.
-/

namespace K3Lean.LocalTraceFormula

open K3Lean.CMProof
open K3Lean.LocalMultiplicativity
open K3Lean.PublishedInputs
open K3Lean.SourceTheorems

noncomputable section

/-- Affine-chart Fermat points whose two free coordinates are nonzero. -/
abbrev fermatAffineNonzeroPoint (p : Nat) :=
  {uv : ZMod p × ZMod p //
    IsUnit uv.1 ∧ IsUnit uv.2 ∧ 1 + uv.1 ^ 3 + uv.2 ^ 3 = 0}

/-- Cubic roots of unity in the unit group. -/
abbrev unitCubeRoot (p : Nat) :=
  {u : (ZMod p)ˣ // u ^ 3 = 1}

/-- The points `v^3 = -1` are the negatives of the cubic roots of unity. -/
def infinityPointUnitCubeRootEquiv (p : Nat) [Fact p.Prime] :
    fermatInfinityChartPoint p ≃ unitCubeRoot p where
  toFun v := by
    have hv : v.1 ≠ 0 := by
      intro hv
      have h := v.2
      rw [hv] at h
      simp at h
    refine ⟨Units.mk0 (-v.1) (neg_ne_zero.mpr hv), ?_⟩
    apply Units.ext
    change (-v.1) ^ 3 = (1 : ZMod p)
    have hpow : v.1 ^ 3 = -(1 : ZMod p) := by
      linear_combination v.2
    rw [neg_pow, hpow]
    norm_num
  invFun u := by
    refine ⟨-(u.1 : ZMod p), ?_⟩
    have hpow : ((u.1 : (ZMod p)ˣ) ^ 3 : ZMod p) = 1 := by
      have h := congr_arg ((↑) : (ZMod p)ˣ → ZMod p) u.2
      simpa using h
    rw [neg_pow, hpow]
    norm_num
  left_inv v := by
    apply Subtype.ext
    simp
  right_inv u := by
    apply Subtype.ext
    apply Units.ext
    simp

/-- The root chart has `gcd(p - 1, 3)` points. -/
theorem card_fermatInfinityChartPoint (p : Nat) (hp : p.Prime) :
    Nat.card (fermatInfinityChartPoint p) = (p - 1).gcd 3 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
  calc
    Nat.card (fermatInfinityChartPoint p) =
        Nat.card (unitCubeRoot p) :=
      Nat.card_congr (infinityPointUnitCubeRootEquiv p)
    _ = Nat.card
          (MonoidHom.ker (powMonoidHom 3 : (ZMod p)ˣ →* (ZMod p)ˣ)) := by
      congr 1
    _ = (Nat.card (ZMod p)ˣ).gcd 3 :=
      IsCyclic.card_powMonoidHom_ker ((ZMod p)ˣ) 3
    _ = (p - 1).gcd 3 := by
      congr 1
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ZMod.card]

/-- The affine chart splits into the all-nonzero part and two root charts. -/
def fermatAffinePartitionEquiv (p : Nat) [Fact p.Prime] :
    fermatAffineChartPoint p ≃
      fermatAffineNonzeroPoint p ⊕
        (fermatInfinityChartPoint p ⊕ fermatInfinityChartPoint p) where
  toFun P :=
    if hu : P.1.1 = 0 then
      Sum.inr (Sum.inl ⟨P.1.2, by simpa [hu] using P.2⟩)
    else if hv : P.1.2 = 0 then
      Sum.inr (Sum.inr ⟨P.1.1, by simpa [hv] using P.2⟩)
    else
      Sum.inl ⟨P.1, (isUnit_iff_ne_zero.mpr hu),
        (isUnit_iff_ne_zero.mpr hv), P.2⟩
  invFun P :=
    match P with
    | Sum.inl uv => ⟨uv.1, uv.2.2.2⟩
    | Sum.inr (Sum.inl v) => ⟨(0, v.1), by simpa using v.2⟩
    | Sum.inr (Sum.inr u) => ⟨(u.1, 0), by simpa using u.2⟩
  left_inv P := by
    by_cases hu : P.1.1 = 0
    · apply Subtype.ext
      apply Prod.ext <;> simp [hu]
    · by_cases hv : P.1.2 = 0
      · apply Subtype.ext
        apply Prod.ext <;> simp [hu, hv]
      · apply Subtype.ext
        apply Prod.ext <;> simp [hu, hv]
  right_inv P := by
    rcases P with uv | P
    · have hu : uv.1.1 ≠ 0 := isUnit_iff_ne_zero.mp uv.2.1
      have hv : uv.1.2 ≠ 0 := isUnit_iff_ne_zero.mp uv.2.2.1
      simp [hu, hv]
    · rcases P with v | u
      · simp
      · have hu : u.1 ≠ 0 := by
          intro hu
          have h := u.2
          rw [hu] at h
          simp at h
        simp [hu]

/-- Cardinal form of the three-way affine-chart partition. -/
theorem card_fermatAffineChartPoint (p : Nat) (hp : p.Prime) :
    Nat.card (fermatAffineChartPoint p) =
      Nat.card (fermatAffineNonzeroPoint p) +
        2 * Nat.card (fermatInfinityChartPoint p) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  rw [Nat.card_congr (fermatAffinePartitionEquiv p)]
  simp only [Nat.card_sum]
  omega

/-- If `p = 1 (mod 3)`, the root chart has three points. -/
theorem card_fermatInfinityChartPoint_of_mod_three_eq_one
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    Nat.card (fermatInfinityChartPoint p) = 3 := by
  rw [card_fermatInfinityChartPoint p hp]
  apply Nat.gcd_eq_right
  refine ⟨p / 3, ?_⟩
  have hdivision := Nat.mod_add_div p 3
  omega

/-- If `p = 2 (mod 3)`, cubing is a permutation of `ZMod p`. -/
theorem cube_bijective_of_mod_three_eq_two
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 2) :
    Function.Bijective (fun x : ZMod p => x ^ 3) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hdecomp : p - 1 = 1 + 3 * (p / 3) := by
    have hdivision := Nat.mod_add_div p 3
    omega
  have hcop : (p - 1).Coprime 3 := by
    rw [hdecomp, Nat.coprime_add_mul_left_left]
    simp
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    calc
      Nat.card (ZMod p)ˣ = Fintype.card (ZMod p)ˣ := Nat.card_eq_fintype_card
      _ = Fintype.card (ZMod p) - 1 := Fintype.card_units (ZMod p)
      _ = p - 1 := by rw [ZMod.card]
  have hunit : Function.Bijective (fun u : (ZMod p)ˣ => u ^ 3) := by
    apply Nat.Coprime.pow_left_bijective
    rw [hcard]
    exact hcop
  constructor
  · intro x y hxy
    change x ^ 3 = y ^ 3 at hxy
    by_cases hx : x = 0
    · subst x
      have hy3 : y ^ 3 = 0 := by simpa using hxy.symm
      have hy : y = 0 := (pow_eq_zero_iff (by norm_num : 3 ≠ 0)).mp hy3
      exact hy.symm
    · by_cases hy : y = 0
      · subst y
        have hx3 : x ^ 3 = 0 := by simpa using hxy
        exact (pow_eq_zero_iff (by norm_num : 3 ≠ 0)).mp hx3
      · let ux : (ZMod p)ˣ := Units.mk0 x hx
        let uy : (ZMod p)ˣ := Units.mk0 y hy
        have huxy : ux ^ 3 = uy ^ 3 := by
          apply Units.ext
          exact hxy
        have huv : ux = uy := hunit.1 huxy
        exact congr_arg ((↑) : (ZMod p)ˣ → ZMod p) huv
  · intro y
    by_cases hy : y = 0
    · exact ⟨0, by simp [hy]⟩
    · let uy : (ZMod p)ˣ := Units.mk0 y hy
      obtain ⟨ux, hux⟩ := hunit.2 uy
      refine ⟨(ux : ZMod p), ?_⟩
      have h := congr_arg ((↑) : (ZMod p)ˣ → ZMod p) hux
      exact h

/-- When cubing is bijective, projection to the first chart coordinate is an equivalence. -/
def fermatAffineEquivOfCubeBijective
    (p : Nat) [NeZero p]
    (hcube : Function.Bijective (fun x : ZMod p => x ^ 3)) :
    ZMod p ≃ fermatAffineChartPoint p := by
  let e : ZMod p ≃ ZMod p :=
    Equiv.ofBijective (fun x : ZMod p => x ^ 3) hcube
  refine
    { toFun := fun u =>
        ⟨(u, e.symm (-1 - u ^ 3)), by
          have hroot := e.apply_symm_apply (-1 - u ^ 3)
          change (e.symm (-1 - u ^ 3)) ^ 3 = -1 - u ^ 3 at hroot
          change 1 + u ^ 3 + (e.symm (-1 - u ^ 3)) ^ 3 = 0
          rw [hroot]
          ring⟩
      invFun := fun P => P.1.1
      left_inv := fun _ => rfl
      right_inv := ?_ }
  intro P
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply hcube.1
    have hroot := e.apply_symm_apply (-1 - P.1.1 ^ 3)
    change (e.symm (-1 - P.1.1 ^ 3)) ^ 3 = -1 - P.1.1 ^ 3 at hroot
    change (e.symm (-1 - P.1.1 ^ 3)) ^ 3 = P.1.2 ^ 3
    calc
      (e.symm (-1 - P.1.1 ^ 3)) ^ 3 = -1 - P.1.1 ^ 3 := hroot
      _ = P.1.2 ^ 3 := by
        have hsum : 1 + P.1.1 ^ 3 = -(P.1.2 ^ 3) :=
          eq_neg_of_add_eq_zero_left P.2
        calc
          -1 - P.1.1 ^ 3 = -(1 + P.1.1 ^ 3) := by ring
          _ = -(-(P.1.2 ^ 3)) := congr_arg Neg.neg hsum
          _ = P.1.2 ^ 3 := neg_neg _

/-- Inert primes have trace zero on the Fermat cubic. -/
theorem fermatFrobeniusTrace_eq_zero_of_mod_three_eq_two
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 2) :
    fermatFrobeniusTrace p = 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hcube := cube_bijective_of_mod_three_eq_two p hp hmod
  have haffine : Nat.card (fermatAffineChartPoint p) = p := by
    calc
      Nat.card (fermatAffineChartPoint p) = Nat.card (ZMod p) :=
        Nat.card_congr (fermatAffineEquivOfCubeBijective p hcube).symm
      _ = p := by
        rw [Nat.card_eq_fintype_card, ZMod.card]
  have hdecomp : p - 1 = 1 + 3 * (p / 3) := by
    have hdivision := Nat.mod_add_div p 3
    omega
  have hcop : (p - 1).Coprime 3 := by
    rw [hdecomp, Nat.coprime_add_mul_left_left]
    simp
  have hinfinity : Nat.card (fermatInfinityChartPoint p) = 1 := by
    rw [card_fermatInfinityChartPoint p hp]
    exact Nat.coprime_iff_gcd_eq_one.mp hcop
  have hcount : fermatProjectivePointCount p = p + 1 := by
    rw [fermatProjectivePointCount, haffine, hinfinity]
  rw [fermatFrobeniusTrace, hcount]
  omega

/-- A nonzero trace good prime is necessarily split, hence `p = 1 (mod 3)`. -/
theorem mod_three_eq_one_of_fermatTrace_ne_zero
    (p : Nat) (hp : p.Prime) (hthree : 3 < p)
    (htrace : fermatFrobeniusTrace p ≠ 0) :
    p % 3 = 1 := by
  have hlt : p % 3 < 3 := Nat.mod_lt p (by norm_num)
  have hnezero : p % 3 ≠ 0 := by
    intro hzero
    have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hzero
    have heq : 3 = p :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdvd
    omega
  have hone_or_two : p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hone_or_two with hone | htwo
  · exact hone
  · exact (htrace (fermatFrobeniusTrace_eq_zero_of_mod_three_eq_two p hp htwo)).elim

/--
An all-nonzero affine triple is uniquely a nonzero scalar times a point in
the chart `[1 : u : v]` with `u` and `v` nonzero.
-/
def zLocalFermatScaleEquiv (p : Nat) [Fact p.Prime] :
    ZLocalCubeSolution p ≃ (ZMod p)ˣ × fermatAffineNonzeroPoint p := by
  refine
    { toFun := fun t => by
        let a : (ZMod p)ˣ := Units.mk0 t.1.1 (isUnit_iff_ne_zero.mp t.2.1)
        let ai : ZMod p := t.1.1⁻¹
        refine ⟨a, ⟨(t.1.2.1 * ai, t.1.2.2 * ai), ?_, ?_, ?_⟩⟩
        · exact t.2.2.1.mul t.2.1.inv
        · exact t.2.2.2.1.mul t.2.1.inv
        · have hai : t.1.1 * ai = 1 := by
            exact ZMod.mul_inv_of_unit t.1.1 t.2.1
          calc
            1 + (t.1.2.1 * ai) ^ 3 + (t.1.2.2 * ai) ^ 3 =
                t.1.1 ^ 3 * ai ^ 3 +
                  t.1.2.1 ^ 3 * ai ^ 3 + t.1.2.2 ^ 3 * ai ^ 3 := by
              rw [← mul_pow, hai]
              simp [mul_pow]
            _ = (t.1.1 ^ 3 + t.1.2.1 ^ 3 + t.1.2.2 ^ 3) * ai ^ 3 := by
              ring
            _ = 0 := by rw [t.2.2.2.2, zero_mul]
      invFun := fun P =>
        ⟨((P.1 : ZMod p),
            (P.1 : ZMod p) * P.2.1.1,
            (P.1 : ZMod p) * P.2.1.2), by
          refine ⟨P.1.isUnit, P.1.isUnit.mul P.2.2.1,
            P.1.isUnit.mul P.2.2.2.1, ?_⟩
          calc
            (P.1 : ZMod p) ^ 3 +
                  ((P.1 : ZMod p) * P.2.1.1) ^ 3 +
                  ((P.1 : ZMod p) * P.2.1.2) ^ 3 =
                (P.1 : ZMod p) ^ 3 *
                  (1 + P.2.1.1 ^ 3 + P.2.1.2 ^ 3) := by
              ring
            _ = 0 := by rw [P.2.2.2.2, mul_zero]⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · calc
          t.1.1 * (t.1.2.1 * t.1.1⁻¹) =
              t.1.2.1 * (t.1.1 * t.1.1⁻¹) := by ring
          _ = t.1.2.1 := by rw [ZMod.mul_inv_of_unit t.1.1 t.2.1, mul_one]
      · calc
          t.1.1 * (t.1.2.2 * t.1.1⁻¹) =
              t.1.2.2 * (t.1.1 * t.1.1⁻¹) := by ring
          _ = t.1.2.2 := by rw [ZMod.mul_inv_of_unit t.1.1 t.2.1, mul_one]
  · intro P
    apply Prod.ext
    · apply Units.ext
      rfl
    · apply Subtype.ext
      apply Prod.ext
      · calc
          (P.1 : ZMod p) * P.2.1.1 * (P.1 : ZMod p)⁻¹ =
              P.2.1.1 * ((P.1 : ZMod p) * (P.1 : ZMod p)⁻¹) := by ring
          _ = P.2.1.1 := by
            rw [ZMod.mul_inv_of_unit (P.1 : ZMod p) P.1.isUnit, mul_one]
      · calc
          (P.1 : ZMod p) * P.2.1.2 * (P.1 : ZMod p)⁻¹ =
              P.2.1.2 * ((P.1 : ZMod p) * (P.1 : ZMod p)⁻¹) := by ring
          _ = P.2.1.2 := by
            rw [ZMod.mul_inv_of_unit (P.1 : ZMod p) P.1.isUnit, mul_one]

/-- Cardinal form of the scalar-times-projective-point equivalence. -/
theorem card_zLocalCubeSolution_eq_scale_mul
    (p : Nat) (hp : p.Prime) :
    Nat.card (ZLocalCubeSolution p) =
      (p - 1) * Nat.card (fermatAffineNonzeroPoint p) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  calc
    Nat.card (ZLocalCubeSolution p) =
        Nat.card ((ZMod p)ˣ × fermatAffineNonzeroPoint p) :=
      Nat.card_congr (zLocalFermatScaleEquiv p)
    _ = Nat.card (ZMod p)ˣ * Nat.card (fermatAffineNonzeroPoint p) :=
      Nat.card_prod _ _
    _ = (p - 1) * Nat.card (fermatAffineNonzeroPoint p) := by
      congr 1
      calc
        Nat.card (ZMod p)ˣ = Fintype.card (ZMod p)ˣ := Nat.card_eq_fintype_card
        _ = Fintype.card (ZMod p) - 1 := Fintype.card_units (ZMod p)
        _ = p - 1 := by rw [ZMod.card]

/-- The literal natural-residue local count has the same scalar factorization. -/
theorem card_localCubeSolutions_eq_scale_mul
    (p : Nat) (hp : p.Prime) :
    (localCubeSolutions p).card =
      (p - 1) * Nat.card (fermatAffineNonzeroPoint p) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  calc
    (localCubeSolutions p).card = Fintype.card (ZLocalCubeSolution p) :=
      card_localCubeSolutions_eq_fintype hp.pos
    _ = Nat.card (ZLocalCubeSolution p) := Nat.card_eq_fintype_card.symm
    _ = (p - 1) * Nat.card (fermatAffineNonzeroPoint p) :=
      card_zLocalCubeSolution_eq_scale_mul p hp

/-- At a split prime, the projective curve is the all-nonzero chart plus nine boundary points. -/
theorem fermatProjectivePointCount_eq_nonzero_add_nine
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1) :
    fermatProjectivePointCount p =
      Nat.card (fermatAffineNonzeroPoint p) + 9 := by
  rw [fermatProjectivePointCount,
    card_fermatAffineChartPoint p hp,
    card_fermatInfinityChartPoint_of_mod_three_eq_one p hp hmod]

/--
The local trace identity is a theorem: the external CM hypothesis is not used.
-/
theorem fermatCubicLocalTraceFormula :
    K3Lean.SourceTheorems.FermatCubicLocalTraceFormula := by
  intro p hp hthree htrace
  let A := Nat.card (fermatAffineNonzeroPoint p)
  have hmod : p % 3 = 1 :=
    mod_three_eq_one_of_fermatTrace_ne_zero p hp hthree htrace
  have hlocal : (localCubeSolutions p).card = (p - 1) * A := by
    simpa [A] using card_localCubeSolutions_eq_scale_mul p hp
  have hpoint : fermatProjectivePointCount p = A + 9 := by
    simpa [A] using
      fermatProjectivePointCount_eq_nonzero_add_nine p hp hmod
  have hfactor :
      (p : Int) - 8 - fermatFrobeniusTrace p = (A : Int) := by
    rw [fermatFrobeniusTrace, hpoint]
    push_cast
    ring
  rw [hfactor]
  have hpone : 1 ≤ p := hp.one_le
  calc
    ((localCubeSolutions p).card : Int) = (((p - 1) * A : Nat) : Int) := by
      exact_mod_cast hlocal
    _ = ((p : Int) - 1) * (A : Int) := by
      rw [Nat.cast_mul, Nat.cast_sub hpone, Nat.cast_one]

#check @fermatCubicLocalTraceFormula
#print axioms fermatCubicLocalTraceFormula

end

end K3Lean.LocalTraceFormula
