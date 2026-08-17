import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# The Eisenstein integers as an explicit Euclidean domain

`Eis` is the ring `ℤ[ω]`, `ω = e^{2πi/3}`, realized as pairs `(a, b)`
representing `a + bω`, with multiplication induced by `ω² = -1 - ω`.

Contents:

* commutative-ring structure and the conjugation ring involution;
* the norm `a² - ab + b²`, its multiplicativity and positivity;
* the embedding `toC : Eis →+* ℂ` and `‖toC α‖² = norm α`;
* Euclidean-domain structure (rounding division), hence PID and UFD;
* units: exactly the six elements of norm `1`;
* primary elements (`α ≡ 1 mod 3`): every element whose norm is prime to `3`
  has exactly one primary associate, and primary elements are closed under
  multiplication and conjugation;
* classification of primary elements of prime-power norm, split and inert
  cases, and the coprime-norm factorization of primary elements.

Everything is self-contained over Mathlib.
-/

namespace K3Lean.Eisenstein

open Complex

/-- The Eisenstein integers `ℤ[ω]`: pairs `(re, im)` representing `re + im·ω`
with `ω = e^{2πi/3}`, so that `ω² = -1 - ω`. -/
@[ext]
structure Eis where
  re : ℤ
  im : ℤ
deriving DecidableEq

namespace Eis

instance : Zero Eis := ⟨⟨0, 0⟩⟩
instance : One Eis := ⟨⟨1, 0⟩⟩
instance : Add Eis := ⟨fun α β => ⟨α.re + β.re, α.im + β.im⟩⟩
instance : Neg Eis := ⟨fun α => ⟨-α.re, -α.im⟩⟩
instance : Mul Eis :=
  ⟨fun α β => ⟨α.re * β.re - α.im * β.im,
    α.re * β.im + α.im * β.re - α.im * β.im⟩⟩

@[simp] lemma zero_re : (0 : Eis).re = 0 := rfl
@[simp] lemma zero_im : (0 : Eis).im = 0 := rfl
@[simp] lemma one_re : (1 : Eis).re = 1 := rfl
@[simp] lemma one_im : (1 : Eis).im = 0 := rfl
@[simp] lemma add_re (α β : Eis) : (α + β).re = α.re + β.re := rfl
@[simp] lemma add_im (α β : Eis) : (α + β).im = α.im + β.im := rfl
@[simp] lemma neg_re (α : Eis) : (-α).re = -α.re := rfl
@[simp] lemma neg_im (α : Eis) : (-α).im = -α.im := rfl
@[simp] lemma mul_re (α β : Eis) :
    (α * β).re = α.re * β.re - α.im * β.im := rfl
@[simp] lemma mul_im (α β : Eis) :
    (α * β).im = α.re * β.im + α.im * β.re - α.im * β.im := rfl

instance : CommRing Eis where
  add_assoc := by intros; ext <;> simp <;> ring
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp <;> ring
  neg_add_cancel := by intros; ext <;> simp
  mul_assoc := by intros; ext <;> simp <;> ring
  one_mul := by intros; ext <;> simp
  mul_one := by intros; ext <;> simp
  left_distrib := by intros; ext <;> simp <;> ring
  right_distrib := by intros; ext <;> simp <;> ring
  mul_comm := by intros; ext <;> simp <;> ring
  zero_mul := by intros; ext <;> simp
  mul_zero := by intros; ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec

@[simp] lemma sub_re (α β : Eis) : (α - β).re = α.re - β.re := by
  rw [sub_eq_add_neg, add_re, neg_re]; ring

@[simp] lemma sub_im (α β : Eis) : (α - β).im = α.im - β.im := by
  rw [sub_eq_add_neg, add_im, neg_im]; ring

@[simp] lemma natCast_re (n : ℕ) : (n : Eis).re = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.cast_succ, add_re, ih]; simp
@[simp] lemma natCast_im (n : ℕ) : (n : Eis).im = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.cast_succ, add_im, ih]; simp
@[simp] lemma intCast_re (n : ℤ) : (n : Eis).re = n := by
  cases n with
  | ofNat m =>
      simpa using natCast_re m
  | negSucc m =>
      rw [Int.cast_negSucc, neg_re, natCast_re, Int.negSucc_eq]
      push_cast
      ring
@[simp] lemma intCast_im (n : ℤ) : (n : Eis).im = 0 := by
  cases n with
  | ofNat m =>
      simpa using natCast_im m
  | negSucc m =>
      rw [Int.cast_negSucc, neg_im, natCast_im]
      simp

lemma three_eis : (3 : Eis) = ⟨3, 0⟩ := by
  have h : (3 : Eis) = ((3 : ℕ) : Eis) := by norm_cast
  rw [h]
  ext
  · rw [natCast_re]; rfl
  · rw [natCast_im]

@[simp] lemma three_re : (3 : Eis).re = 3 := by rw [three_eis]
@[simp] lemma three_im : (3 : Eis).im = 0 := by rw [three_eis]

/-- `ω` as an Eisenstein integer. -/
def omega : Eis := ⟨0, 1⟩

@[simp] lemma omega_re : omega.re = 0 := rfl
@[simp] lemma omega_im : omega.im = 1 := rfl

lemma omega_sq : omega * omega = -1 - omega := by
  ext <;> simp [omega]

/-- Conjugation `a + bω ↦ a + b ω̄ = (a - b) - bω` as a ring homomorphism. -/
def conj : Eis →+* Eis where
  toFun α := ⟨α.re - α.im, -α.im⟩
  map_one' := by ext <;> simp
  map_mul' α β := by ext <;> simp <;> ring
  map_zero' := by ext <;> simp
  map_add' α β := by ext <;> simp <;> ring

@[simp] lemma conj_re (α : Eis) : (conj α).re = α.re - α.im := rfl
@[simp] lemma conj_im (α : Eis) : (conj α).im = -α.im := rfl

@[simp] lemma conj_conj (α : Eis) : conj (conj α) = α := by ext <;> simp

/-- The norm `a² - ab + b²` of `a + bω`. -/
def norm (α : Eis) : ℤ := α.re * α.re - α.re * α.im + α.im * α.im

lemma norm_def (α : Eis) : norm α = α.re * α.re - α.re * α.im + α.im * α.im := rfl

@[simp] lemma norm_zero : norm 0 = 0 := by simp [norm]
@[simp] lemma norm_one : norm 1 = 1 := by simp [norm]
@[simp] lemma norm_neg (α : Eis) : norm (-α) = norm α := by
  simp only [norm, neg_re, neg_im]; ring
@[simp] lemma norm_conj (α : Eis) : norm (conj α) = norm α := by
  simp only [norm, conj_re, conj_im]; ring

lemma mul_conj (α : Eis) : α * conj α = (norm α : Eis) := by
  ext
  · simp only [mul_re, conj_re, conj_im, intCast_re, norm]; ring
  · simp only [mul_im, conj_re, conj_im, intCast_im, norm]; ring

lemma norm_mul (α β : Eis) : norm (α * β) = norm α * norm β := by
  simp only [norm, mul_re, mul_im]; ring

lemma four_mul_norm (α : Eis) :
    4 * norm α = (2 * α.re - α.im) ^ 2 + 3 * α.im ^ 2 := by
  simp only [norm]; ring

lemma norm_nonneg (α : Eis) : 0 ≤ norm α := by
  nlinarith [four_mul_norm α, sq_nonneg (2 * α.re - α.im), sq_nonneg α.im]

lemma norm_eq_zero_iff {α : Eis} : norm α = 0 ↔ α = 0 := by
  constructor
  · intro h
    have h4 : (2 * α.re - α.im) ^ 2 + 3 * α.im ^ 2 = 0 := by
      have h' := four_mul_norm α
      omega
    have him : α.im = 0 := by nlinarith [sq_nonneg (2 * α.re - α.im), sq_nonneg α.im]
    have hre : α.re = 0 := by nlinarith [sq_nonneg α.im]
    ext <;> simp [hre, him]
  · rintro rfl; simp

/-- The natural-number norm. -/
def natNorm (α : Eis) : ℕ := (norm α).toNat

lemma natNorm_cast (α : Eis) : (natNorm α : ℤ) = norm α :=
  Int.toNat_of_nonneg (norm_nonneg α)

lemma natNorm_mul (α β : Eis) : natNorm (α * β) = natNorm α * natNorm β := by
  have h : (natNorm (α * β) : ℤ) = ((natNorm α * natNorm β : ℕ) : ℤ) := by
    rw [natNorm_cast, norm_mul]
    push_cast
    rw [natNorm_cast, natNorm_cast]
  exact_mod_cast h

@[simp] lemma natNorm_zero : natNorm 0 = 0 := rfl
@[simp] lemma natNorm_one : natNorm 1 = 1 := rfl
@[simp] lemma natNorm_neg (α : Eis) : natNorm (-α) = natNorm α := by
  unfold natNorm; rw [norm_neg]
@[simp] lemma natNorm_conj (α : Eis) : natNorm (conj α) = natNorm α := by
  unfold natNorm; rw [norm_conj]

lemma natNorm_eq_zero_iff {α : Eis} : natNorm α = 0 ↔ α = 0 := by
  unfold natNorm
  rw [← norm_eq_zero_iff]
  have := norm_nonneg α
  omega

lemma natNorm_pos_of_ne_zero {α : Eis} (h : α ≠ 0) : 0 < natNorm α := by
  rcases Nat.eq_zero_or_pos (natNorm α) with h0 | h1
  · exact absurd (natNorm_eq_zero_iff.mp h0) h
  · exact h1

/-! ## The embedding into `ℂ` -/

/-- The complex cube root of unity `(-1 + √3 i)/2`. -/
noncomputable def omegaC : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

lemma omegaC_re : omegaC.re = -1 / 2 := rfl
lemma omegaC_im : omegaC.im = Real.sqrt 3 / 2 := rfl

lemma sq_sqrt_three : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

lemma omegaC_sq : omegaC * omegaC = -1 - omegaC := by
  have h3 := sq_sqrt_three
  apply Complex.ext
  · simp only [Complex.mul_re, omegaC_re, omegaC_im, Complex.sub_re, Complex.neg_re,
      Complex.one_re]
    nlinarith
  · simp only [Complex.mul_im, omegaC_re, omegaC_im, Complex.sub_im, Complex.neg_im,
      Complex.one_im]
    ring

/-- The multiplication rule for numbers of the shape `x + y·ω`. -/
lemma omegaC_mul_rule (x y u v : ℂ) :
    (x + y * omegaC) * (u + v * omegaC) =
      (x * u - y * v) + (x * v + y * u - y * v) * omegaC := by
  have h := omegaC_sq
  calc (x + y * omegaC) * (u + v * omegaC)
      = x * u + (x * v + y * u) * omegaC + y * v * (omegaC * omegaC) := by ring
    _ = x * u + (x * v + y * u) * omegaC + y * v * (-1 - omegaC) := by rw [h]
    _ = (x * u - y * v) + (x * v + y * u - y * v) * omegaC := by ring

/-- The embedding `ℤ[ω] →+* ℂ`. -/
noncomputable def toC : Eis →+* ℂ where
  toFun α := (α.re : ℂ) + (α.im : ℂ) * omegaC
  map_one' := by simp
  map_mul' α β := by
    simp only [mul_re, mul_im]
    push_cast
    rw [omegaC_mul_rule]
  map_zero' := by simp
  map_add' α β := by
    simp only [add_re, add_im]
    push_cast
    ring

lemma toC_def (α : Eis) : toC α = (α.re : ℂ) + (α.im : ℂ) * omegaC := rfl

@[simp] lemma toC_omega : toC omega = omegaC := by
  simp [toC_def, omega]

lemma toC_re (α : Eis) : (toC α).re = (α.re : ℝ) - (α.im : ℝ) / 2 := by
  simp [toC_def, omegaC_re, omegaC_im]
  ring

lemma toC_im (α : Eis) : (toC α).im = (α.im : ℝ) * (Real.sqrt 3 / 2) := by
  simp [toC_def, omegaC_re, omegaC_im]

lemma sqrt_three_pos : (0 : ℝ) < Real.sqrt 3 := by
  have : (0:ℝ) < 3 := by norm_num
  exact Real.sqrt_pos.mpr this

lemma toC_injective : Function.Injective toC := by
  intro α β h
  have him : (α.im : ℝ) = (β.im : ℝ) := by
    have h1 := congrArg Complex.im h
    rw [toC_im, toC_im] at h1
    have h2 : Real.sqrt 3 / 2 ≠ 0 := by positivity
    exact mul_right_cancel₀ h2 h1
  have hre : (α.re : ℝ) = (β.re : ℝ) := by
    have h1 := congrArg Complex.re h
    rw [toC_re, toC_re, him] at h1
    linarith
  ext
  · exact_mod_cast hre
  · exact_mod_cast him

lemma normSq_toC (α : Eis) : Complex.normSq (toC α) = (norm α : ℝ) := by
  rw [Complex.normSq_apply, toC_re, toC_im]
  have h3 := sq_sqrt_three
  simp only [norm]
  push_cast
  nlinarith [h3]

lemma norm_toC_sq (α : Eis) : ‖toC α‖ ^ 2 = (norm α : ℝ) := by
  rw [← Complex.normSq_eq_norm_sq, normSq_toC]

lemma norm_toC (α : Eis) : ‖toC α‖ = Real.sqrt (norm α : ℝ) := by
  rw [← norm_toC_sq, Real.sqrt_sq (_root_.norm_nonneg (toC α))]

lemma toC_conj (α : Eis) : toC (conj α) = (starRingEnd ℂ) (toC α) := by
  apply Complex.ext
  · rw [Complex.conj_re, toC_re, toC_re]
    simp only [conj_re, conj_im]
    push_cast
    ring
  · rw [Complex.conj_im, toC_im, toC_im]
    simp only [conj_im]
    push_cast
    ring

instance : IsDomain Eis :=
  Function.Injective.isDomain toC toC_injective

/-! ## Euclidean structure -/

/-- Rounding division: the quotient of `α` by nonzero `β`, obtained by rounding
the exact complex quotient to a nearest lattice point. -/
def ediv (α β : Eis) : Eis :=
  let d := norm β
  let x := α * conj β
  ⟨round ((x.re : ℚ) / d), round ((x.im : ℚ) / d)⟩

def emod (α β : Eis) : Eis := α - β * ediv α β

lemma emod_add (α β : Eis) : β * ediv α β + emod α β = α := by
  simp [emod]

/-- The key inequality: the rounding remainder has smaller norm. -/
lemma emod_norm_lt (α β : Eis) (hβ : β ≠ 0) : natNorm (emod α β) < natNorm β := by
  have hd0 : 0 < norm β := by
    have h1 := natNorm_pos_of_ne_zero hβ
    have h2 := natNorm_cast β
    omega
  set d : ℤ := norm β with hd_def
  set x : Eis := α * conj β with hx_def
  set q : Eis := ediv α β with hq_def
  have hq_re : q.re = round ((x.re : ℚ) / (d : ℚ)) := rfl
  have hq_im : q.im = round ((x.im : ℚ) / (d : ℚ)) := rfl
  have hkey : emod α β * conj β = x - q * ((d : ℤ) : Eis) := by
    have hmc : β * conj β = ((d : ℤ) : Eis) := mul_conj β
    calc emod α β * conj β
        = α * conj β - q * (β * conj β) := by rw [emod, hq_def]; ring
      _ = x - q * ((d : ℤ) : Eis) := by rw [hmc, hx_def]
  have hsub_re : (x - q * ((d : ℤ) : Eis)).re = x.re - q.re * d := by
    simp [sub_re, mul_re]
  have hsub_im : (x - q * ((d : ℤ) : Eis)).im = x.im - q.im * d := by
    simp [sub_im, mul_im]
  have hnorm_mul : norm (emod α β) * d = norm (x - q * ((d : ℤ) : Eis)) := by
    have h := norm_mul (emod α β) (conj β)
    rw [hkey, norm_conj] at h
    exact h.symm
  set e1 : ℚ := (x.re : ℚ) / (d : ℚ) - round ((x.re : ℚ) / (d : ℚ)) with he1_def
  set e2 : ℚ := (x.im : ℚ) / (d : ℚ) - round ((x.im : ℚ) / (d : ℚ)) with he2_def
  have habs1 := abs_le.mp (abs_sub_round ((x.re : ℚ) / (d : ℚ)))
  have habs2 := abs_le.mp (abs_sub_round ((x.im : ℚ) / (d : ℚ)))
  have hd0Q : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd0
  have hdne : (d : ℚ) ≠ 0 := hd0Q.ne'
  have hre_q : ((x.re : ℚ) - (q.re : ℚ) * (d : ℚ)) = (d : ℚ) * e1 := by
    rw [he1_def, hq_re]
    field_simp
  have him_q : ((x.im : ℚ) - (q.im : ℚ) * (d : ℚ)) = (d : ℚ) * e2 := by
    rw [he2_def, hq_im]
    field_simp
  have hnorm_sub : ((norm (x - q * ((d : ℤ) : Eis)) : ℤ) : ℚ)
      = (d : ℚ) ^ 2 * (e1 ^ 2 - e1 * e2 + e2 ^ 2) := by
    rw [norm_def, hsub_re, hsub_im]
    push_cast
    rw [hre_q, him_q]
    ring
  have hE : e1 ^ 2 - e1 * e2 + e2 ^ 2 ≤ 3 / 4 := by
    nlinarith [habs1.1, habs1.2, habs2.1, habs2.2]
  have hA : ((norm (x - q * ((d : ℤ) : Eis)) : ℤ) : ℚ) ≤ 3 / 4 * (d : ℚ) ^ 2 := by
    rw [hnorm_sub]
    nlinarith [mul_le_mul_of_nonneg_left hE (sq_nonneg (d : ℚ))]
  have hlt : norm (emod α β) < d := by
    by_contra hge
    rw [not_lt] at hge
    have hgeQ : (d : ℚ) ≤ ((norm (emod α β) : ℤ) : ℚ) := by exact_mod_cast hge
    have hmulQ : ((norm (emod α β) : ℤ) : ℚ) * (d : ℚ)
        = ((norm (x - q * ((d : ℤ) : Eis)) : ℤ) : ℚ) := by exact_mod_cast hnorm_mul
    nlinarith [hgeQ, hd0Q, hmulQ, hA]
  have hc1 := natNorm_cast (emod α β)
  have hc2 := natNorm_cast β
  omega

instance : EuclideanDomain Eis where
  quotient := ediv
  remainder := emod
  quotient_zero := fun a => by
    ext <;> simp [ediv]
  quotient_mul_add_remainder_eq := fun a b => by
    simp [emod]
  r a b := natNorm a < natNorm b
  r_wellFounded := InvImage.wf natNorm Nat.lt_wfRel.wf
  remainder_lt := fun a b hb => emod_norm_lt a b hb
  mul_left_not_lt := by
    intro a b hb
    simp only [not_lt]
    rw [natNorm_mul]
    exact Nat.le_mul_of_pos_right _ (natNorm_pos_of_ne_zero hb)

/-! ## Units -/

lemma isUnit_iff_natNorm_eq_one {α : Eis} : IsUnit α ↔ natNorm α = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h : natNorm (u : Eis) * natNorm ((u⁻¹ : Eisˣ) : Eis) = 1 := by
      rw [← natNorm_mul]
      simp
    exact Nat.dvd_one.mp ⟨natNorm ((u⁻¹ : Eisˣ) : Eis), h.symm⟩
  · intro h
    have hmc : α * conj α = 1 := by
      have hm := mul_conj α
      have hn : norm α = 1 := by
        have hc := natNorm_cast α
        omega
      rw [hn] at hm
      simpa using hm
    exact IsUnit.of_mul_eq_one (conj α) hmc

/-- The list of the six units. -/
lemma eq_of_isUnit {α : Eis} (h : IsUnit α) :
    α = 1 ∨ α = -1 ∨ α = omega ∨ α = -omega ∨
      α = ⟨-1, -1⟩ ∨ α = ⟨1, 1⟩ := by
  have h1 : natNorm α = 1 := isUnit_iff_natNorm_eq_one.mp h
  have hn : norm α = 1 := by
    have hc := natNorm_cast α
    omega
  have h4 : (2 * α.re - α.im) ^ 2 + 3 * α.im ^ 2 = 4 := by
    have h44 := four_mul_norm α
    omega
  obtain ⟨a, b⟩ := α
  simp only at h4 ⊢
  have hb : b = -1 ∨ b = 0 ∨ b = 1 := by
    have hb2 : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg (2 * a - b)]
    have hb3 : -1 ≤ b := by nlinarith
    have hb4 : b ≤ 1 := by nlinarith
    omega
  rcases hb with rfl | rfl | rfl
  · -- b = -1 : (2a+1)^2 = 1
    have hsq : (2 * a - (-1)) ^ 2 = 1 := by linarith
    have hz : (2 * a - (-1) - 1) * (2 * a - (-1) + 1) = 0 := by linear_combination hsq
    have ha : a = 0 ∨ a = -1 := by
      rcases mul_eq_zero.mp hz with h' | h'
      · left; omega
      · right; omega
    rcases ha with rfl | rfl
    · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      decide
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · -- b = 0 : (2a)^2 = 4
    have hsq : (2 * a - 0) ^ 2 = 4 := by linarith
    have hz : (2 * a - 0 - 2) * (2 * a - 0 + 2) = 0 := by linear_combination hsq
    have ha : a = 1 ∨ a = -1 := by
      rcases mul_eq_zero.mp hz with h' | h'
      · left; omega
      · right; omega
    rcases ha with rfl | rfl
    · exact Or.inl (by decide)
    · exact Or.inr (Or.inl (by decide))
  · -- b = 1 : (2a-1)^2 = 1
    have hsq : (2 * a - 1) ^ 2 = 1 := by linarith
    have hz : (2 * a - 1 - 1) * (2 * a - 1 + 1) = 0 := by linear_combination hsq
    have ha : a = 1 ∨ a = 0 := by
      rcases mul_eq_zero.mp hz with h' | h'
      · left; omega
      · right; omega
    rcases ha with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))
    · exact Or.inr (Or.inr (Or.inl (by decide)))

/-! ## Primary elements -/

/-- `α` is primary if `α ≡ 1 mod 3`, i.e. `3 ∣ re α - 1` and `3 ∣ im α`. -/
def Primary (α : Eis) : Prop := (3 : ℤ) ∣ α.re - 1 ∧ (3 : ℤ) ∣ α.im

instance (α : Eis) : Decidable (Primary α) := by unfold Primary; infer_instance

lemma primary_iff (α : Eis) : Primary α ↔ ∃ β : Eis, α = 1 + 3 * β := by
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨⟨x, y⟩, ?_⟩
    ext
    · simp only [add_re, one_re, mul_re, three_re, three_im]
      omega
    · simp only [add_im, one_im, mul_im, three_re, three_im]
      omega
  · rintro ⟨β, rfl⟩
    constructor
    · refine ⟨β.re, ?_⟩
      simp only [add_re, one_re, mul_re, three_re, three_im]
      ring
    · refine ⟨β.im, ?_⟩
      simp only [add_im, one_im, mul_im, three_re, three_im]
      ring

lemma Primary.mul {α β : Eis} (hα : Primary α) (hβ : Primary β) :
    Primary (α * β) := by
  rw [primary_iff] at hα hβ ⊢
  obtain ⟨a, rfl⟩ := hα
  obtain ⟨b, rfl⟩ := hβ
  exact ⟨a + b + 3 * (a * b), by ring⟩

lemma Primary.conj {α : Eis} (hα : Primary α) : Primary (Eis.conj α) := by
  obtain ⟨h1, h2⟩ := hα
  constructor
  · simp only [conj_re]
    omega
  · simp only [conj_im]
    omega

@[simp] lemma primary_one : Primary 1 := ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩

lemma Primary.pow {α : Eis} (hα : Primary α) (k : ℕ) : Primary (α ^ k) := by
  induction k with
  | zero => simpa using primary_one
  | succ k ih => rw [pow_succ]; exact ih.mul hα

lemma Primary.ne_zero {α : Eis} (hα : Primary α) : α ≠ 0 := by
  rintro rfl
  obtain ⟨h1, _⟩ := hα
  rw [zero_re] at h1
  omega

lemma Primary.norm_mod_three {α : Eis} (hα : Primary α) :
    (natNorm α) % 3 = 1 := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hα
  have hre : α.re = 3 * x + 1 := by omega
  have him : α.im = 3 * y := hy
  have : norm α = 3 * (3 * x * x + 2 * x - 3 * x * y - y + 3 * y * y) + 1 := by
    simp only [norm, hre, him]
    ring
  have hc := natNorm_cast α
  omega

/-- Bad residue pairs `(re, im) mod 3` force `3 ∣ norm`. -/
lemma three_dvd_norm_of_bad_residues {α : Eis}
    (h : (α.re % 3 = 0 ∧ α.im % 3 = 0) ∨ (α.re % 3 = 1 ∧ α.im % 3 = 2) ∨
      (α.re % 3 = 2 ∧ α.im % 3 = 1)) : (3 : ℤ) ∣ norm α := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨x, hx⟩ : ∃ x, α.re = 3 * x := ⟨α.re / 3, by omega⟩
    obtain ⟨y, hy⟩ : ∃ y, α.im = 3 * y := ⟨α.im / 3, by omega⟩
    exact ⟨3 * (x * x - x * y + y * y), by rw [norm_def, hx, hy]; ring⟩
  · obtain ⟨x, hx⟩ : ∃ x, α.re = 3 * x + 1 := ⟨α.re / 3, by omega⟩
    obtain ⟨y, hy⟩ : ∃ y, α.im = 3 * y + 2 := ⟨α.im / 3, by omega⟩
    exact ⟨3 * x * x - 3 * x * y + 3 * y * y + 3 * y + 1,
      by rw [norm_def, hx, hy]; ring⟩
  · obtain ⟨x, hx⟩ : ∃ x, α.re = 3 * x + 2 := ⟨α.re / 3, by omega⟩
    obtain ⟨y, hy⟩ : ∃ y, α.im = 3 * y + 1 := ⟨α.im / 3, by omega⟩
    exact ⟨3 * x * x + 3 * x - 3 * x * y + 3 * y * y + 1,
      by rw [norm_def, hx, hy]; ring⟩

lemma isUnit_omega : IsUnit omega :=
  IsUnit.of_mul_eq_one ⟨-1, -1⟩ (by decide)

lemma isUnit_neg_omega : IsUnit (-omega) :=
  IsUnit.of_mul_eq_one ⟨1, 1⟩ (by decide)

lemma isUnit_omega_sq : IsUnit (⟨-1, -1⟩ : Eis) :=
  IsUnit.of_mul_eq_one omega (by decide)

lemma isUnit_neg_omega_sq : IsUnit (⟨1, 1⟩ : Eis) :=
  IsUnit.of_mul_eq_one (-omega) (by decide)

/-- Two associated primary elements are equal. -/
theorem Primary.eq_of_associated {α β : Eis} (hα : Primary α) (hβ : Primary β)
    (h : Associated α β) : α = β := by
  obtain ⟨u, hu⟩ := h
  have hun := eq_of_isUnit u.isUnit
  obtain ⟨ha1, ha2⟩ := hα
  rcases hun with h5 | h5 | h5 | h5 | h5 | h5 <;> rw [h5] at hu <;> subst hu
  · exact (mul_one α).symm
  · exfalso
    obtain ⟨hb1, hb2⟩ := hβ
    simp at hb1 hb2
    omega
  · exfalso
    obtain ⟨hb1, hb2⟩ := hβ
    simp [omega] at hb1 hb2
    omega
  · exfalso
    obtain ⟨hb1, hb2⟩ := hβ
    simp [omega] at hb1 hb2
    omega
  · exfalso
    obtain ⟨hb1, hb2⟩ := hβ
    simp at hb1 hb2
    omega
  · exfalso
    obtain ⟨hb1, hb2⟩ := hβ
    simp at hb1 hb2
    omega

/-- Every element whose norm is prime to `3` has exactly one primary associate. -/
theorem exists_unique_primary_associate {α : Eis} (h : ¬ (3 ∣ natNorm α)) :
    ∃! β : Eis, Associated α β ∧ Primary β := by
  have hZ : ¬ ((3 : ℤ) ∣ norm α) := by
    intro hd
    apply h
    have hc := natNorm_cast α
    have : (3 : ℤ) ∣ (natNorm α : ℤ) := by rw [hc]; exact hd
    exact_mod_cast this
  have build : ∀ u : Eis, IsUnit u → Primary (α * u) →
      ∃! β : Eis, Associated α β ∧ Primary β := by
    intro u hu hp
    refine ⟨α * u, ⟨⟨hu.unit, by rw [IsUnit.unit_spec]⟩, hp⟩, ?_⟩
    rintro γ ⟨hg1, hg2⟩
    exact hg2.eq_of_associated hp
      (hg1.symm.trans ⟨hu.unit, by rw [IsUnit.unit_spec]⟩)
  have hre : α.re % 3 = 0 ∨ α.re % 3 = 1 ∨ α.re % 3 = 2 := by omega
  have him : α.im % 3 = 0 ∨ α.im % 3 = 1 ∨ α.im % 3 = 2 := by omega
  rcases hre with h1 | h1 | h1 <;> rcases him with h2 | h2 | h2
  · exact absurd (three_dvd_norm_of_bad_residues (Or.inl ⟨h1, h2⟩)) hZ
  · -- (0,1): u = ω² = ⟨-1,-1⟩
    refine build ⟨-1, -1⟩ isUnit_omega_sq ⟨?_, ?_⟩ <;> simp <;> omega
  · -- (0,2): u = -ω² = ⟨1,1⟩
    refine build ⟨1, 1⟩ isUnit_neg_omega_sq ⟨?_, ?_⟩ <;> simp <;> omega
  · -- (1,0): u = 1
    refine build 1 isUnit_one ⟨?_, ?_⟩ <;> simp <;> omega
  · -- (1,1): u = -ω
    refine build (-omega) isUnit_neg_omega ⟨?_, ?_⟩ <;> simp [omega] <;> omega
  · exact absurd (three_dvd_norm_of_bad_residues (Or.inr (Or.inl ⟨h1, h2⟩))) hZ
  · -- (2,0): u = -1
    refine build (-1) isUnit_one.neg ⟨?_, ?_⟩ <;> simp <;> omega
  · exact absurd (three_dvd_norm_of_bad_residues (Or.inr (Or.inr ⟨h1, h2⟩))) hZ
  · -- (2,2): u = ω
    refine build omega isUnit_omega ⟨?_, ?_⟩ <;> simp [omega] <;> omega

/-! ## Primes -/

lemma prime_of_natNorm_prime {α : Eis} (h : (natNorm α).Prime) : Prime α := by
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  constructor
  · intro hu
    rw [isUnit_iff_natNorm_eq_one] at hu
    rw [hu] at h
    exact Nat.not_prime_one h
  · intro b c hbc
    have hn : natNorm b * natNorm c = natNorm α := by rw [hbc, natNorm_mul]
    rcases h.eq_one_or_self_of_dvd (natNorm b) ⟨natNorm c, hn.symm⟩ with h1 | h1
    · left
      exact isUnit_iff_natNorm_eq_one.mpr h1
    · right
      apply isUnit_iff_natNorm_eq_one.mpr
      have hb0 : 0 < natNorm b := by
        rcases Nat.eq_zero_or_pos (natNorm b) with h0 | h0
        · rw [h0, zero_mul] at hn
          rw [← hn] at h
          exact absurd h Nat.not_prime_zero
        · exact h0
      have : natNorm b * natNorm c = natNorm b * 1 := by
        rw [hn, h1, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hb0 this

lemma sq_mod_three (n : ℤ) : n ^ 2 % 3 = 0 ∨ n ^ 2 % 3 = 1 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, (r = 0 ∨ r = 1 ∨ r = 2) ∧ n = 3 * q + r :=
    ⟨n / 3, n % 3, by omega, by omega⟩
  rcases hr with rfl | rfl | rfl
  · left
    have h : ((3*q+0:ℤ))^2 = 3 * (3*q*q) + 0 := by ring
    omega
  · right
    have h : ((3*q+1:ℤ))^2 = 3 * (3*q*q+2*q) + 1 := by ring
    omega
  · right
    have h : ((3*q+2:ℤ))^2 = 3 * (3*q*q+4*q+1) + 1 := by ring
    omega

/-- The norm form never takes values `≡ 2 mod 3`. -/
lemma natNorm_mod_three_ne_two (α : Eis) : natNorm α % 3 ≠ 2 := by
  have h4 := four_mul_norm α
  have hc := natNorm_cast α
  have h1 := sq_mod_three (2 * α.re - α.im)
  have h2 := sq_mod_three α.im
  omega

lemma natNorm_natCast (n : ℕ) : natNorm (n : Eis) = n * n := by
  have h : norm (n : Eis) = (n : ℤ) * (n : ℤ) := by
    have hre : ((n : ℕ) : Eis).re = (n : ℤ) := by
      have := intCast_re (n : ℤ)
      exact_mod_cast this
    have him : ((n : ℕ) : Eis).im = 0 := by
      have := intCast_im (n : ℤ)
      exact_mod_cast this
    rw [norm_def, hre, him]
    ring
  unfold natNorm
  rw [h]
  exact_mod_cast Int.toNat_natCast (n * n)

/-- Rational primes `q ≡ 2 mod 3` remain prime in `ℤ[ω]`. -/
lemma prime_intCast_of_two_mod_three {q : ℕ} (hq : q.Prime) (hq2 : q % 3 = 2) :
    Prime (q : Eis) := by
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  constructor
  · rw [isUnit_iff_natNorm_eq_one, natNorm_natCast]
    have := hq.two_le
    nlinarith
  · intro b c hbc
    have hn : natNorm b * natNorm c = q * q := by
      rw [← natNorm_natCast, hbc, natNorm_mul]
    have hdvd : natNorm b ∣ q ^ 2 := by
      rw [pow_two]
      exact ⟨natNorm c, hn.symm⟩
    obtain ⟨i, hi, hbi⟩ := (Nat.dvd_prime_pow hq).mp hdvd
    interval_cases i
    · left
      exact isUnit_iff_natNorm_eq_one.mpr (by simpa using hbi)
    · exfalso
      have hne := natNorm_mod_three_ne_two b
      rw [hbi, pow_one] at hne
      omega
    · right
      apply isUnit_iff_natNorm_eq_one.mpr
      have hq0 : 0 < q * q := by
        have := hq.two_le
        positivity
      have heq : q * q * natNorm c = q * q * 1 := by
        rw [mul_one]
        have h2 : natNorm b * natNorm c = q * q := hn
        rw [hbi] at h2
        calc q * q * natNorm c = q ^ 2 * natNorm c := by ring
          _ = q * q := h2
      exact Nat.eq_of_mul_eq_mul_left hq0 heq

/-! ## Finsets of primary elements of given norm -/

/-- The finite set of primary Eisenstein integers of norm `n`. -/
noncomputable def primaryOfNorm (n : ℕ) : Finset Eis :=
  ((Finset.Icc (-(2 * (n : ℤ))) (2 * n)) ×ˢ (Finset.Icc (-(2 * (n : ℤ))) (2 * n))).image
      (fun ab => (⟨ab.1, ab.2⟩ : Eis))
    |>.filter (fun α => natNorm α = n ∧ Primary α)

lemma coord_bound_of_natNorm_le {α : Eis} {n : ℕ} (h : natNorm α ≤ n) :
    α.re ∈ Finset.Icc (-(2 * (n : ℤ))) (2 * n) ∧
      α.im ∈ Finset.Icc (-(2 * (n : ℤ))) (2 * n) := by
  have h4 := four_mul_norm α
  have hc := natNorm_cast α
  have hre : (2 * α.re - α.im) ^ 2 ≤ 4 * n := by
    nlinarith [sq_nonneg α.im, norm_nonneg α]
  have him : 3 * α.im ^ 2 ≤ 4 * n := by
    nlinarith [sq_nonneg (2 * α.re - α.im), norm_nonneg α]
  constructor <;> simp only [Finset.mem_Icc] <;> constructor <;> nlinarith [sq_nonneg α.re,
    sq_nonneg α.im, sq_nonneg (α.re + α.im), sq_nonneg (α.re - α.im),
    sq_nonneg (2 * α.re - α.im), sq_nonneg (α.re - 2 * n), sq_nonneg (α.re + 2 * n),
    sq_nonneg (α.im - 2 * n), sq_nonneg (α.im + 2 * n)]

lemma mem_primaryOfNorm {n : ℕ} {α : Eis} :
    α ∈ primaryOfNorm n ↔ natNorm α = n ∧ Primary α := by
  unfold primaryOfNorm
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨hn, hp⟩
    refine ⟨?_, hn, hp⟩
    rw [Finset.mem_image]
    obtain ⟨h1, h2⟩ := coord_bound_of_natNorm_le hn.le
    exact ⟨(α.re, α.im), Finset.mem_product.mpr ⟨h1, h2⟩, by ext <;> rfl⟩

@[simp] lemma primaryOfNorm_zero : primaryOfNorm 0 = ∅ := by
  ext α
  simp only [mem_primaryOfNorm, Finset.notMem_empty, iff_false, not_and]
  intro h
  exact fun hp => hp.ne_zero (natNorm_eq_zero_iff.mp h)

@[simp] lemma primaryOfNorm_one : primaryOfNorm 1 = {1} := by
  ext α
  simp only [mem_primaryOfNorm, Finset.mem_singleton]
  constructor
  · rintro ⟨hn, hp⟩
    have hu := eq_of_isUnit (isUnit_iff_natNorm_eq_one.mpr hn)
    obtain ⟨hp1, hp2⟩ := hp
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    all_goals (simp at hp1 hp2 ⊢) <;> omega
  · rintro rfl
    exact ⟨natNorm_one, primary_one⟩

/-- No primary elements of norm `3^k`, `k ≥ 1`. -/
lemma primaryOfNorm_three_pow {k : ℕ} (hk : k ≠ 0) :
    primaryOfNorm (3 ^ k) = ∅ := by
  ext α
  simp only [mem_primaryOfNorm, Finset.notMem_empty, iff_false, not_and]
  intro hn hp
  have h1 := hp.norm_mod_three
  rw [hn] at h1
  have : 3 ^ k % 3 = 0 := by
    have : (3:ℕ) ∣ 3 ^ k := dvd_pow_self 3 hk
    omega
  omega

/-! ### Helper lemmas for the classification -/

/-- Norms are multiplicative along powers. -/
lemma natNorm_pow (α : Eis) (n : ℕ) : natNorm (α ^ n) = natNorm α ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, natNorm_mul, ih, pow_succ]

/-- Associated elements have equal norms. -/
lemma natNorm_eq_of_associated {α β : Eis} (h : Associated α β) :
    natNorm α = natNorm β := by
  obtain ⟨u, hu⟩ := h
  have hu1 : natNorm (u : Eis) = 1 := isUnit_iff_natNorm_eq_one.mp u.isUnit
  rw [← hu, natNorm_mul, hu1, mul_one]

lemma natNorm_dvd {α β : Eis} (h : α ∣ β) : natNorm α ∣ natNorm β := by
  obtain ⟨γ, rfl⟩ := h
  exact ⟨natNorm γ, natNorm_mul α γ⟩

/-- A primary unit is `1`. -/
lemma Primary.eq_one_of_isUnit {α : Eis} (hα : Primary α) (h : IsUnit α) :
    α = 1 := by
  have hu := eq_of_isUnit h
  obtain ⟨hp1, hp2⟩ := hα
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  all_goals (exfalso; simp at hp1 hp2; try omega)

lemma conj_natCast (n : ℕ) : conj (n : Eis) = (n : Eis) := by
  ext <;> simp

/-- `π · conj π = N(π)` as a natural cast. -/
lemma mul_conj_natCast {π : Eis} : π * conj π = ((natNorm π : ℕ) : Eis) := by
  have h := mul_conj π
  have h2 : ((natNorm π : ℤ) : Eis) = ((natNorm π : ℕ) : Eis) := by push_cast; rfl
  rw [← natNorm_cast π] at h
  rw [h, h2]

private lemma primary_split_rep {p : ℕ} (hp : p.Prime) {π : Eis}
    (hπ : Primary π) (hnorm : natNorm π = p) :
    ∀ k α, Primary α → natNorm α = p ^ k →
      ∃ j ≤ k, α = π ^ j * conj π ^ (k - j) := by
  have hp3 : p % 3 = 1 := by
    have h := hπ.norm_mod_three
    rwa [hnorm] at h
  intro k
  induction k with
  | zero =>
    intro α hα hn
    refine ⟨0, le_refl 0, ?_⟩
    have h1 : α = 1 :=
      hα.eq_one_of_isUnit (isUnit_iff_natNorm_eq_one.mpr (by simpa using hn))
    simp [h1]
  | succ k ih =>
    intro α hα hn
    have hπprime : Prime π := prime_of_natNorm_prime (by rw [hnorm]; exact hp)
    have hdvd : π ∣ α ∨ conj π ∣ α := by
      have h1 : π * conj π = ((p : ℕ) : Eis) := by
        rw [mul_conj_natCast, hnorm]
      have h2 : α * conj α = ((p : ℕ) : Eis) ^ (k + 1) := by
        rw [mul_conj_natCast, hn]
        push_cast
        rfl
      have h3 : π ∣ α * conj α := by
        rw [h2, ← h1]
        exact dvd_pow (dvd_mul_right π (conj π)) (Nat.succ_ne_zero k)
      rcases hπprime.dvd_or_dvd h3 with h | h
      · exact Or.inl h
      · right
        obtain ⟨δ, hδ⟩ := h
        exact ⟨conj δ, by rw [← conj_conj α, hδ, map_mul]⟩
    have step : ∀ lam : Eis, Primary lam → natNorm lam = p → lam ∣ α →
        ∃ β, Primary β ∧ natNorm β = p ^ k ∧ α = lam * β := by
      intro lam hlamP hlamN hlamD
      obtain ⟨γ, hγ⟩ := hlamD
      have h1 : natNorm lam * natNorm γ = p ^ (k + 1) := by
        rw [← natNorm_mul, ← hγ, hn]
      rw [hlamN] at h1
      have hγnorm : natNorm γ = p ^ k := by
        have hp0 : 0 < p := hp.pos
        have h2 : p * natNorm γ = p * p ^ k := by
          rw [h1, pow_succ']
        exact Nat.eq_of_mul_eq_mul_left hp0 h2
      have h3γ : ¬ (3 ∣ natNorm γ) := by
        rw [hγnorm]
        have hmod : p ^ k % 3 = 1 := by
          rw [Nat.pow_mod, hp3, one_pow]
          decide
        omega
      obtain ⟨β, ⟨hassoc, hβP⟩, -⟩ := exists_unique_primary_associate h3γ
      refine ⟨β, hβP, by rw [← natNorm_eq_of_associated hassoc, hγnorm], ?_⟩
      have h5 : Associated α (lam * β) := by
        rw [hγ]
        exact Associated.mul_left lam hassoc
      exact hα.eq_of_associated (hlamP.mul hβP) h5
    rcases hdvd with h | h
    · obtain ⟨β, hβP, hβn, rfl⟩ := step π hπ hnorm h
      obtain ⟨j, hj, rfl⟩ := ih β hβP hβn
      refine ⟨j + 1, by omega, ?_⟩
      rw [show k + 1 - (j + 1) = k - j from by omega, pow_succ]
      ring
    · obtain ⟨β, hβP, hβn, rfl⟩ := step (conj π) hπ.conj (by rw [natNorm_conj, hnorm]) h
      obtain ⟨j, hj, rfl⟩ := ih β hβP hβn
      refine ⟨j, by omega, ?_⟩
      rw [show k + 1 - j = (k - j) + 1 from by omega, pow_succ]
      ring

/-- Split case: for a primary prime `π` of prime norm `p` with `π` not associated
to its conjugate, the primary elements of norm `p^k` are exactly
`π^j (conj π)^(k-j)`, `0 ≤ j ≤ k`, all distinct. -/
theorem primaryOfNorm_prime_pow_split {p : ℕ} (hp : p.Prime) {π : Eis}
    (hπ : Primary π) (hnorm : natNorm π = p)
    (hns : ¬ Associated π (conj π)) (k : ℕ) :
    primaryOfNorm (p ^ k) =
      (Finset.range (k + 1)).image (fun j => π ^ j * conj π ^ (k - j)) := by
  ext α
  simp only [mem_primaryOfNorm, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨hn, hα⟩
    obtain ⟨j, hj, rfl⟩ := primary_split_rep hp hπ hnorm k α hα hn
    exact ⟨j, by omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    constructor
    · rw [natNorm_mul, natNorm_pow, natNorm_pow, natNorm_conj, hnorm, ← pow_add]
      congr 1
      omega
    · exact (hπ.pow j).mul (hπ.conj.pow (k - j))

theorem prime_pow_split_inj {p : ℕ} (hp : p.Prime) {π : Eis}
    (hπ : Primary π) (hnorm : natNorm π = p)
    (hns : ¬ Associated π (conj π)) (k : ℕ) :
    ∀ j₁ ∈ Finset.range (k + 1), ∀ j₂ ∈ Finset.range (k + 1),
      π ^ j₁ * conj π ^ (k - j₁) = π ^ j₂ * conj π ^ (k - j₂) → j₁ = j₂ := by
  have hπprime : Prime π := prime_of_natNorm_prime (by rw [hnorm]; exact hp)
  have hcprime : Prime (conj π) :=
    prime_of_natNorm_prime (by rw [natNorm_conj, hnorm]; exact hp)
  have key : ∀ j₁ j₂, j₁ < j₂ → j₂ ≤ k →
      π ^ j₁ * conj π ^ (k - j₁) = π ^ j₂ * conj π ^ (k - j₂) → False := by
    intro j₁ j₂ hlt hle heq
    set m := j₂ - j₁ with hm
    have hπ0 : π ^ j₁ ≠ 0 := pow_ne_zero _ hπ.ne_zero
    have hc0 : conj π ^ (k - j₂) ≠ 0 := pow_ne_zero _ hπ.conj.ne_zero
    have h1 : π ^ j₁ * (conj π ^ m * conj π ^ (k - j₂)) =
        π ^ j₁ * (π ^ m * conj π ^ (k - j₂)) := by
      calc π ^ j₁ * (conj π ^ m * conj π ^ (k - j₂))
          = π ^ j₁ * conj π ^ (k - j₁) := by
            rw [← pow_add, show m + (k - j₂) = k - j₁ from by omega]
        _ = π ^ j₂ * conj π ^ (k - j₂) := heq
        _ = π ^ j₁ * (π ^ m * conj π ^ (k - j₂)) := by
            rw [← mul_assoc, ← pow_add, show j₁ + m = j₂ from by omega]
    have h2 : conj π ^ m * conj π ^ (k - j₂) = π ^ m * conj π ^ (k - j₂) :=
      mul_left_cancel₀ hπ0 h1
    have h3 : conj π ^ m = π ^ m := mul_right_cancel₀ hc0 h2
    have h4 : π ∣ conj π ^ m := by
      rw [h3]
      exact dvd_pow_self π (by omega)
    have h5 : π ∣ conj π := hπprime.dvd_of_dvd_pow h4
    exact hns (hπprime.associated_of_dvd hcprime h5)
  intro j₁ hj₁ j₂ hj₂ heq
  simp only [Finset.mem_range] at hj₁ hj₂
  rcases lt_trichotomy j₁ j₂ with h | h | h
  · exact absurd (key j₁ j₂ h (by omega) heq) not_false
  · exact h
  · exact absurd (key j₂ j₁ h (by omega) heq.symm) not_false

lemma three_dvd_pow_sub_neg_one_pow {q : ℤ} (hq : q % 3 = 2) (j : ℕ) :
    (3 : ℤ) ∣ q ^ j - (-1) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨t, ht⟩ : ∃ t, q = 3 * t + 2 := ⟨q / 3, by omega⟩
    refine ⟨q * c + t * (-1) ^ j + (-1) ^ j, ?_⟩
    rw [pow_succ, pow_succ]
    linear_combination q * hc + (-1 : ℤ) ^ j * ht

private lemma primary_inert_rep {q : ℕ} (hq : q.Prime) (hq2 : q % 3 = 2) :
    ∀ e, ∀ α, Primary α → natNorm α = q ^ e →
      2 ∣ e ∧ α = (-1) ^ (e / 2) * (q : Eis) ^ (e / 2) := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro α hα hn
    match e with
    | 0 =>
      refine ⟨⟨0, rfl⟩, ?_⟩
      have h1 : α = 1 :=
        hα.eq_one_of_isUnit (isUnit_iff_natNorm_eq_one.mpr (by simpa using hn))
      simp [h1]
    | 1 =>
      exfalso
      have hne := natNorm_mod_three_ne_two α
      rw [hn, pow_one] at hne
      omega
    | (e + 2) =>
      have hqprime : Prime ((q : ℕ) : Eis) := prime_intCast_of_two_mod_three hq hq2
      have hqdvd : ((q : ℕ) : Eis) ∣ α := by
        have h2 : α * conj α = ((q : ℕ) : Eis) ^ (e + 2) := by
          rw [mul_conj_natCast, hn]
          push_cast
          rfl
        have h3 : ((q : ℕ) : Eis) ∣ α * conj α := by
          rw [h2]
          exact dvd_pow_self _ (by omega)
        rcases hqprime.dvd_or_dvd h3 with h | h
        · exact h
        · obtain ⟨δ, hδ⟩ := h
          exact ⟨conj δ, by rw [← conj_conj α, hδ, map_mul, conj_natCast]⟩
      obtain ⟨γ, hγ⟩ := hqdvd
      have hγnorm : natNorm γ = q ^ e := by
        have h1 : (q * q) * natNorm γ = q ^ (e + 2) := by
          rw [← natNorm_natCast, ← natNorm_mul, ← hγ, hn]
        have hq0 : 0 < q * q := by
          have := hq.two_le
          positivity
        have h2 : (q * q) * natNorm γ = (q * q) * q ^ e := by
          rw [h1]
          ring
        exact Nat.eq_of_mul_eq_mul_left hq0 h2
      have hq2' : (q : ℤ) % 3 = 2 := by exact_mod_cast hq2
      obtain ⟨t, ht⟩ : ∃ t, (q : ℤ) = 3 * t + 2 := ⟨(q : ℤ) / 3, by omega⟩
      have hre : α.re = (q : ℤ) * γ.re := by
        rw [hγ]
        simp
      have him : α.im = (q : ℤ) * γ.im := by
        rw [hγ]
        simp
      obtain ⟨hα1, hα2⟩ := hα
      have hγP : Primary (-γ) := by
        constructor
        · obtain ⟨c1, hc1⟩ := hα1
          rw [hre, ht] at hc1
          refine ⟨-(t * γ.re + γ.re - c1), ?_⟩
          simp only [neg_re]
          linear_combination hc1
        · obtain ⟨c2, hc2⟩ := hα2
          rw [him, ht] at hc2
          refine ⟨-(t * γ.im + γ.im - c2), ?_⟩
          simp only [neg_im]
          linear_combination hc2
      have hγn : natNorm (-γ) = q ^ e := by rw [natNorm_neg, hγnorm]
      obtain ⟨⟨j, hj⟩, hrep⟩ := ih e (by omega) (-γ) hγP hγn
      refine ⟨⟨j + 1, by omega⟩, ?_⟩
      have hediv : (e + 2) / 2 = j + 1 := by omega
      have hediv' : e / 2 = j := by omega
      rw [hediv]
      rw [hediv'] at hrep
      have hγeq : γ = -((-1) ^ j * (q : Eis) ^ j) := by
        rw [← hrep]
        ring
      rw [hγ, hγeq]
      ring

/-- Inert case: the primary elements of norm `q^e` for a rational prime
`q ≡ 2 mod 3` form `{(-1)^j q^j}` if `e = 2j`, and are empty for odd `e`. -/
theorem primaryOfNorm_prime_pow_inert {q : ℕ} (hq : q.Prime) (hq2 : q % 3 = 2)
    (e : ℕ) :
    primaryOfNorm (q ^ e) =
      if 2 ∣ e then {((-1) ^ (e / 2) * (q : Eis) ^ (e / 2))} else ∅ := by
  have hq2' : (q : ℤ) % 3 = 2 := by exact_mod_cast hq2
  ext α
  split_ifs with h2
  · obtain ⟨j, rfl⟩ := h2
    have hjdiv : 2 * j / 2 = j := by omega
    simp only [mem_primaryOfNorm, Finset.mem_singleton]
    constructor
    · rintro ⟨hn, hα⟩
      have h := (primary_inert_rep hq hq2 (2 * j) α hα hn).2
      rw [hjdiv] at h
      rw [hjdiv]
      exact h
    · rintro rfl
      rw [hjdiv]
      constructor
      · rw [natNorm_mul, natNorm_pow, natNorm_pow, natNorm_natCast]
        have h1 : natNorm (-1 : Eis) = 1 := by
          rw [natNorm_neg, natNorm_one]
        rw [h1, one_pow, one_mul, show q * q = q ^ 2 from by ring, ← pow_mul]
      · have hcast : ((-1 : Eis) ^ j * (q : Eis) ^ j) =
            ((((-1) ^ j * (q : ℤ) ^ j) : ℤ) : Eis) := by
          push_cast
          rfl
        rw [hcast]
        constructor
        · simp only [intCast_re]
          obtain ⟨c, hc⟩ := three_dvd_pow_sub_neg_one_pow hq2' j
          refine ⟨(-1) ^ j * c, ?_⟩
          have hsq : ((-1 : ℤ)) ^ j * (-1 : ℤ) ^ j = 1 := by
            rw [← pow_add]
            exact Even.neg_one_pow ⟨j, by ring⟩
          linear_combination ((-1 : ℤ) ^ j) * hc + hsq
        · simp only [intCast_im]
          exact dvd_zero 3
  · simp only [mem_primaryOfNorm, Finset.notMem_empty, iff_false, not_and]
    intro hn hα
    exact absurd (primary_inert_rep hq hq2 e α hα hn).1 h2

/-- Components of a quotient by a rational prime, shifted to the residue `r`. -/
private lemma primary_div_rational_residues {q : ℕ} {α γ : Eis}
    (hγ : α = (q : Eis) * γ) (hα : Primary α) (r : ℤ) (hr : (q : ℤ) % 3 = r) :
    ((3 : ℤ) ∣ r * γ.re - 1) ∧ ((3 : ℤ) ∣ r * γ.im) := by
  obtain ⟨ha1, ha2⟩ := hα
  have hre : α.re = (q : ℤ) * γ.re := by rw [hγ]; simp
  have him : α.im = (q : ℤ) * γ.im := by rw [hγ]; simp
  obtain ⟨t, ht⟩ : ∃ t, (q : ℤ) = 3 * t + r := ⟨(q : ℤ) / 3, by omega⟩
  constructor
  · obtain ⟨c, hc⟩ := ha1
    rw [hre, ht] at hc
    refine ⟨c - t * γ.re, ?_⟩
    linear_combination hc
  · obtain ⟨c, hc⟩ := ha2
    rw [him, ht] at hc
    refine ⟨c - t * γ.im, ?_⟩
    linear_combination hc

/-- The coprime factorization of a primary element, existence half. -/
private lemma primary_coprime_split :
    ∀ m : ℕ, ∀ {n : ℕ}, Nat.Coprime m n → ∀ α, Primary α → natNorm α = m * n →
      ∃ β γ, Primary β ∧ natNorm β = m ∧ Primary γ ∧ natNorm γ = n ∧ α = β * γ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hmn α hα hN
    rcases eq_or_ne m 1 with rfl | hm1
    · exact ⟨1, α, primary_one, natNorm_one, hα, by simpa using hN, (one_mul α).symm⟩
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hN
      exact hα.ne_zero (natNorm_eq_zero_iff.mp hN)
    obtain ⟨q, hq_def⟩ : ∃ q, m.minFac = q := ⟨m.minFac, rfl⟩
    have hqprime : q.Prime := hq_def ▸ Nat.minFac_prime hm1
    have hqm : q ∣ m := hq_def ▸ Nat.minFac_dvd m
    have hq2 : 2 ≤ q := hqprime.two_le
    have h3N : natNorm α % 3 = 1 := hα.norm_mod_three
    have hq3 : q ≠ 3 := by
      rintro rfl
      obtain ⟨m', hm'⟩ := hqm
      have h3 : (3 : ℕ) ∣ natNorm α := by
        rw [hN, hm']
        exact ⟨m' * n, by ring⟩
      omega
    have hqmod : q % 3 = 1 ∨ q % 3 = 2 := by
      have h0 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
      rcases h0 with h0 | h0 | h0
      · exfalso
        have hdvd : (3 : ℕ) ∣ q := by omega
        rcases hqprime.eq_one_or_self_of_dvd 3 hdvd with h' | h'
        · norm_num at h'
        · exact hq3 h'.symm
      · exact Or.inl h0
      · exact Or.inr h0
    have hcqn : Nat.Coprime q n := Nat.Coprime.coprime_dvd_left hqm hmn
    have main : (∃ lam : Eis, Primary lam ∧ natNorm lam = q ∧ lam ∣ α) ∨
        (((q : ℕ) : Eis) ∣ α) := by
      have hqdvdN : q ∣ natNorm α := by
        rw [hN]
        exact Dvd.dvd.mul_right hqm n
      have hqEdvd : ((q : ℕ) : Eis) ∣ α * conj α := by
        rw [mul_conj_natCast]
        obtain ⟨c, hc⟩ := hqdvdN
        exact ⟨(c : Eis), by rw [hc]; push_cast; ring⟩
      set g := EuclideanDomain.gcd α ((q : ℕ) : Eis) with hg_def
      have hgα : g ∣ α := EuclideanDomain.gcd_dvd_left _ _
      have hgq : g ∣ ((q : ℕ) : Eis) := EuclideanDomain.gcd_dvd_right _ _
      have hgunit : ¬ IsUnit g := by
        intro hu
        have hcop : IsCoprime α ((q : ℕ) : Eis) :=
          EuclideanDomain.gcd_isUnit_iff.mp hu
        have h1 : ((q : ℕ) : Eis) ∣ conj α :=
          hcop.symm.dvd_of_dvd_mul_left hqEdvd
        have h2 : ((q : ℕ) : Eis) ∣ α := by
          obtain ⟨δ, hδ⟩ := h1
          exact ⟨conj δ, by rw [← conj_conj α, hδ, map_mul, conj_natCast]⟩
        have h3 : ((q : ℕ) : Eis) ∣ g := EuclideanDomain.dvd_gcd h2 dvd_rfl
        have h4 : IsUnit ((q : ℕ) : Eis) := isUnit_of_dvd_unit h3 hu
        rw [isUnit_iff_natNorm_eq_one, natNorm_natCast] at h4
        nlinarith
      have hgN : natNorm g ∣ q ^ 2 := by
        have hh := natNorm_dvd hgq
        rwa [natNorm_natCast, ← pow_two] at hh
      obtain ⟨i, hi2, hgNi⟩ := (Nat.dvd_prime_pow hqprime).mp hgN
      interval_cases i
      · exact absurd (isUnit_iff_natNorm_eq_one.mpr (by simpa using hgNi)) hgunit
      · left
        have h3g : ¬ (3 ∣ natNorm g) := by
          rw [hgNi, pow_one]
          omega
        obtain ⟨lam, ⟨hassoc, hlamP⟩, -⟩ := exists_unique_primary_associate h3g
        exact ⟨lam, hlamP, by rw [← natNorm_eq_of_associated hassoc, hgNi, pow_one],
          (hassoc.symm.dvd).trans hgα⟩
      · right
        obtain ⟨h', hh'⟩ := hgq
        have hh'unit : IsUnit h' := by
          rw [isUnit_iff_natNorm_eq_one]
          have h1 : natNorm ((q : ℕ) : Eis) = natNorm g * natNorm h' := by
            rw [hh', natNorm_mul]
          rw [natNorm_natCast, hgNi] at h1
          have hq0 : 0 < q ^ 2 := by positivity
          have h2 : q ^ 2 * natNorm h' = q ^ 2 * 1 := by
            rw [mul_one, ← h1, pow_two]
          exact Nat.eq_of_mul_eq_mul_left hq0 h2
        obtain ⟨δ, hδ⟩ := hgα
        obtain ⟨u, hu⟩ := hh'unit
        refine ⟨(u⁻¹ : Eisˣ) * δ, ?_⟩
        rw [hδ, hh', ← hu, mul_assoc, ← mul_assoc (u : Eis), Units.mul_inv, one_mul]
    rcases main with ⟨lam, hlamP, hlamN, hlamD⟩ | hqα
    · obtain ⟨γ₀, hγ₀⟩ := hlamD
      have hγ₀N : q * natNorm γ₀ = m * n := by
        have h1 : natNorm lam * natNorm γ₀ = m * n := by
          rw [← natNorm_mul, ← hγ₀, hN]
        rwa [hlamN] at h1
      have h3γ₀ : ¬ (3 ∣ natNorm γ₀) := by
        intro h3
        obtain ⟨c, hc⟩ := h3
        have hh : (3 : ℕ) ∣ natNorm α := by
          rw [hN, ← hγ₀N, hc]
          exact ⟨q * c, by ring⟩
        omega
      obtain ⟨γ₁, ⟨hassoc, hγ₁P⟩, -⟩ := exists_unique_primary_associate h3γ₀
      have hαeq : α = lam * γ₁ := by
        have h5 : Associated α (lam * γ₁) := by
          rw [hγ₀]
          exact Associated.mul_left lam hassoc
        exact hα.eq_of_associated (hlamP.mul hγ₁P) h5
      have hγ₁N : natNorm γ₁ = (m / q) * n := by
        have h1 : q * natNorm γ₁ = m * n := by
          rw [← natNorm_eq_of_associated hassoc]
          exact hγ₀N
        have h2 : q * natNorm γ₁ = q * ((m / q) * n) := by
          rw [h1, ← mul_assoc, Nat.mul_div_cancel' hqm]
        exact Nat.eq_of_mul_eq_mul_left (by omega) h2
      have hm'lt : m / q < m := Nat.div_lt_self (by omega) hq2
      have hm'cop : Nat.Coprime (m / q) n :=
        Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hqm) hmn
      obtain ⟨β, γ, hβP, hβN, hγP, hγN, hfac⟩ :=
        ih (m / q) hm'lt hm'cop γ₁ hγ₁P hγ₁N
      refine ⟨lam * β, γ, hlamP.mul hβP, ?_, hγP, hγN, ?_⟩
      · rw [natNorm_mul, hlamN, hβN, Nat.mul_div_cancel' hqm]
      · rw [hαeq, hfac, mul_assoc]
    · obtain ⟨γ₀, hγ₀⟩ := hqα
      have hγ₀N : (q * q) * natNorm γ₀ = m * n := by
        rw [← natNorm_natCast, ← natNorm_mul, ← hγ₀, hN]
      have hq2dvd : q * q ∣ m := by
        have h1 : q * q ∣ m * n := ⟨natNorm γ₀, hγ₀N.symm⟩
        have h2 : Nat.Coprime (q * q) n := by
          rw [← pow_two]
          exact Nat.Coprime.pow_left 2 hcqn
        exact h2.dvd_of_dvd_mul_right h1
      have hγ₀N' : natNorm γ₀ = (m / (q * q)) * n := by
        have h2 : (q * q) * natNorm γ₀ = (q * q) * ((m / (q * q)) * n) := by
          rw [hγ₀N, ← mul_assoc, Nat.mul_div_cancel' hq2dvd]
        exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
      have hm'lt : m / (q * q) < m :=
        Nat.div_lt_self (by omega) (by nlinarith)
      have hm'cop : Nat.Coprime (m / (q * q)) n :=
        Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hq2dvd) hmn
      rcases hqmod with hq1 | hq1
      · have hq1' : (q : ℤ) % 3 = 1 := by exact_mod_cast hq1
        have hres := primary_div_rational_residues hγ₀ hα 1 hq1'
        have hγ₀P : Primary γ₀ := by
          obtain ⟨hr1, hr2⟩ := hres
          exact ⟨by omega, by omega⟩
        obtain ⟨β, γ, hβP, hβN, hγP, hγN, hfac⟩ :=
          ih (m / (q * q)) hm'lt hm'cop γ₀ hγ₀P hγ₀N'
        have hqP : Primary ((q : ℕ) : Eis) := by
          constructor
          · rw [show ((q : ℕ) : Eis).re = (q : ℤ) from by simp]
            omega
          · rw [show ((q : ℕ) : Eis).im = 0 from by simp]
            omega
        refine ⟨((q : ℕ) : Eis) * β, γ, hqP.mul hβP, ?_, hγP, hγN, ?_⟩
        · rw [natNorm_mul, natNorm_natCast, hβN, Nat.mul_div_cancel' hq2dvd]
        · rw [hγ₀, hfac, mul_assoc]
      · have hq1' : (q : ℤ) % 3 = 2 := by exact_mod_cast hq1
        have hres := primary_div_rational_residues hγ₀ hα 2 hq1'
        have hγ₀P : Primary (-γ₀) := by
          obtain ⟨hr1, hr2⟩ := hres
          constructor
          · rw [neg_re]
            omega
          · rw [neg_im]
            omega
        have hγ₀N'' : natNorm (-γ₀) = (m / (q * q)) * n := by
          rw [natNorm_neg, hγ₀N']
        obtain ⟨β, γ, hβP, hβN, hγP, hγN, hfac⟩ :=
          ih (m / (q * q)) hm'lt hm'cop (-γ₀) hγ₀P hγ₀N''
        have hqP : Primary (-((q : ℕ) : Eis)) := by
          constructor
          · rw [neg_re, show ((q : ℕ) : Eis).re = (q : ℤ) from by simp]
            omega
          · rw [neg_im, show ((q : ℕ) : Eis).im = 0 from by simp]
            omega
        refine ⟨(-((q : ℕ) : Eis)) * β, γ, hqP.mul hβP, ?_, hγP, hγN, ?_⟩
        · rw [natNorm_mul, natNorm_neg, natNorm_natCast, hβN, Nat.mul_div_cancel' hq2dvd]
        · have hγ₀eq : γ₀ = -(-γ₀) := by ring
          rw [hγ₀, hγ₀eq, hfac]
          ring

/-- Coprime-norm factorization: multiplication maps pairs of
primary elements of coprime norms `m`, `n` onto primary elements of norm `m*n`. -/
theorem primaryOfNorm_mul_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    primaryOfNorm (m * n) =
      ((primaryOfNorm m) ×ˢ (primaryOfNorm n)).image (fun x => x.1 * x.2) := by
  ext α
  simp only [mem_primaryOfNorm, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨hn', hα⟩
    obtain ⟨β, γ, hβP, hβN, hγP, hγN, rfl⟩ := primary_coprime_split m h α hα hn'
    exact ⟨β, γ, ⟨⟨hβN, hβP⟩, ⟨hγN, hγP⟩⟩, rfl⟩
  · rintro ⟨β, γ, ⟨⟨hβN, hβP⟩, ⟨hγN, hγP⟩⟩, rfl⟩
    exact ⟨by rw [natNorm_mul, hβN, hγN], hβP.mul hγP⟩

theorem primaryOfNorm_mul_coprime_inj {m n : ℕ} (h : Nat.Coprime m n) :
    Set.InjOn (fun x : Eis × Eis => x.1 * x.2)
      ((primaryOfNorm m) ×ˢ (primaryOfNorm n) : Finset (Eis × Eis)) := by
  rintro ⟨β₁, γ₁⟩ h₁ ⟨β₂, γ₂⟩ h₂ heq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe,
    mem_primaryOfNorm] at h₁ h₂
  obtain ⟨⟨hβ₁N, hβ₁P⟩, ⟨hγ₁N, hγ₁P⟩⟩ := h₁
  obtain ⟨⟨hβ₂N, hβ₂P⟩, ⟨hγ₂N, hγ₂P⟩⟩ := h₂
  simp only at heq
  have hcop : ∀ {β γ : Eis}, natNorm β = m → natNorm γ = n → IsCoprime β γ := by
    intro β γ hβ hγ
    rw [← EuclideanDomain.gcd_isUnit_iff, isUnit_iff_natNorm_eq_one]
    have h1 : natNorm (EuclideanDomain.gcd β γ) ∣ m := by
      rw [← hβ]
      exact natNorm_dvd (EuclideanDomain.gcd_dvd_left _ _)
    have h2 : natNorm (EuclideanDomain.gcd β γ) ∣ n := by
      rw [← hγ]
      exact natNorm_dvd (EuclideanDomain.gcd_dvd_right _ _)
    exact Nat.dvd_one.mp (h ▸ Nat.dvd_gcd h1 h2)
  have hβdvd : β₁ ∣ β₂ := by
    have h1 : β₁ ∣ β₂ * γ₂ := ⟨γ₁, heq.symm⟩
    exact (hcop hβ₁N hγ₂N).dvd_of_dvd_mul_right h1
  have hβdvd' : β₂ ∣ β₁ := by
    have h1 : β₂ ∣ β₁ * γ₁ := ⟨γ₂, heq⟩
    exact (hcop hβ₂N hγ₁N).dvd_of_dvd_mul_right h1
  have hβeq : β₁ = β₂ :=
    hβ₁P.eq_of_associated hβ₂P (associated_of_dvd_dvd hβdvd hβdvd')
  subst hβeq
  have hγeq : γ₁ = γ₂ := mul_left_cancel₀ hβ₁P.ne_zero heq
  rw [hγeq]

end Eis

end K3Lean.Eisenstein
