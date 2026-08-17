import K3Lean.EisensteinRing
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Square-root cancellation for angular sums over primary Eisenstein integers

For `3 ∤ m` we prove

  `∑_{α primary, 1 ≤ N(α) ≤ N} (α/|α|)^m  =  O(√N)`.

The proof is completely discrete:

1. the analogous sum over the full lattice `ℤ[ω] ∖ {0}` in the norm-disk
   vanishes exactly, by the six-fold rotation `α ↦ ωα` (here `3 ∤ m` enters);
2. the sum over the sublattice `3ℤ[ω]` in the disk therefore also vanishes,
   by rescaling `α = 3γ` (unitization is scale-invariant);
3. primary elements are exactly `1 + 3ℤ[ω]`, and the translation `β ↦ 1 + β`
   moves the primary sum to the `3ℤ[ω]` sum at cost
   `∑ |u(1+β)^m - u(β)^m| = O(m·∑ 1/|β|) = O(m √N)`
   plus boundary terms controlled by annulus point counts `O(√N)`.

The lattice point counts are proved by one-variable interval counting for the
quadratic `b ↦ Q(a,b)`, with the elementary estimate
`∑_a 1/√(M - (3/4)a²) = O(1)`.
-/

namespace K3Lean.PrimaryDiskBound

open Complex Finset Asymptotics Filter
open K3Lean.Eisenstein K3Lean.Eisenstein.Eis

noncomputable section

/-- Unitization `z / |z|` (zero at `0`). -/
def u (z : ℂ) : ℂ := z / (‖z‖ : ℝ)

@[simp] lemma u_zero : u 0 = 0 := by simp [u]

lemma abs_u {z : ℂ} (hz : z ≠ 0) : ‖u z‖ = 1 := by
  simp [u, norm_ne_zero_iff.mpr hz]

lemma norm_u_le (z : ℂ) : ‖u z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [abs_u hz]

lemma u_mul (z w : ℂ) : u (z * w) = u z * u w := by
  unfold u
  rw [_root_.norm_mul]
  push_cast
  rw [div_mul_div_comm]

lemma u_smul_pos {t : ℝ} (ht : 0 < t) (z : ℂ) : u (t * z) = u z := by
  unfold u
  rw [_root_.norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
  push_cast
  exact mul_div_mul_left z ((‖z‖ : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr ht.ne')

/-- `|a^m - b^m| ≤ m·|a - b|` on the unit circle. -/
lemma pow_sub_pow_norm_le {a b : ℂ} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (m : ℕ) :
    ‖a ^ m - b ^ m‖ ≤ m * ‖a - b‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have key : a ^ (m + 1) - b ^ (m + 1) =
        a * (a ^ m - b ^ m) + (a - b) * b ^ m := by
      ring
    calc ‖a ^ (m + 1) - b ^ (m + 1)‖
        ≤ ‖a * (a ^ m - b ^ m)‖ + ‖(a - b) * b ^ m‖ := by
          rw [key]
          exact norm_add_le _ _
      _ = ‖a ^ m - b ^ m‖ + ‖a - b‖ := by
          rw [_root_.norm_mul, _root_.norm_mul, ha, norm_pow, hb, one_mul,
            one_pow, mul_one]
      _ ≤ m * ‖a - b‖ + ‖a - b‖ := by
          have := norm_nonneg (a - b)
          nlinarith [ih]
      _ = (m + 1 : ℕ) * ‖a - b‖ := by
          push_cast
          ring

/-- The unitization is Lipschitz away from the origin:
`|u z - u w| ≤ 2|z - w| / |z|`. -/
lemma u_sub_u_norm_le {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    ‖u z - u w‖ ≤ 2 * ‖z - w‖ / ‖z‖ := by
  have hz0 : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  have hw0 : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hzC : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hz0.ne'
  have hwC : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hw0.ne'
  have key : u z - u w =
      (z - w) / (‖z‖ : ℂ) + (w / ‖w‖) * (((‖w‖ - ‖z‖ : ℝ) : ℂ) / (‖z‖ : ℂ)) := by
    unfold u
    push_cast
    field_simp
    ring
  rw [key]
  have h1 : ‖(z - w) / (‖z‖ : ℂ)‖ = ‖z - w‖ / ‖z‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hz0.le]
  have h2 : ‖(w / ‖w‖) * (((‖w‖ - ‖z‖ : ℝ) : ℂ) / (‖z‖ : ℂ))‖ =
      |‖w‖ - ‖z‖| / ‖z‖ := by
    rw [_root_.norm_mul, norm_div, norm_div, Complex.norm_real, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg hz0.le, Real.norm_of_nonneg hw0.le,
      Real.norm_eq_abs, div_self hw0.ne', one_mul]
  have h3 : |‖w‖ - ‖z‖| ≤ ‖z - w‖ := by
    rw [abs_sub_comm]
    exact abs_norm_sub_norm_le z w
  calc ‖(z - w) / (‖z‖ : ℂ) + (w / ‖w‖) * (((‖w‖ - ‖z‖ : ℝ) : ℂ) / (‖z‖ : ℂ))‖
      ≤ ‖(z - w) / (‖z‖ : ℂ)‖ + ‖(w / ‖w‖) * (((‖w‖ - ‖z‖ : ℝ) : ℂ) / (‖z‖ : ℂ))‖ :=
        norm_add_le _ _
    _ = ‖z - w‖ / ‖z‖ + |‖w‖ - ‖z‖| / ‖z‖ := by rw [h1, h2]
    _ ≤ ‖z - w‖ / ‖z‖ + ‖z - w‖ / ‖z‖ := by
        gcongr
    _ = 2 * ‖z - w‖ / ‖z‖ := by ring

/-! ## Lattice point Finsets -/

/-- All nonzero Eisenstein integers of norm at most `N`. -/
def normLe (N : ℕ) : Finset Eis :=
  ((Finset.Icc (-(2 * (N : ℤ))) (2 * N)) ×ˢ (Finset.Icc (-(2 * (N : ℤ))) (2 * N))).image
      (fun ab => (⟨ab.1, ab.2⟩ : Eis))
    |>.filter (fun α => α ≠ 0 ∧ natNorm α ≤ N)

lemma mem_normLe {N : ℕ} {α : Eis} :
    α ∈ normLe N ↔ α ≠ 0 ∧ natNorm α ≤ N := by
  unfold normLe
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro ⟨h0, hn⟩
    refine ⟨?_, h0, hn⟩
    rw [Finset.mem_image]
    obtain ⟨h1, h2⟩ := coord_bound_of_natNorm_le hn
    exact ⟨(α.re, α.im), Finset.mem_product.mpr ⟨h1, h2⟩, by ext <;> rfl⟩

/-! ## Point counting -/

lemma abs_le_of_sq_le_sq' {x : ℤ} {t : ℕ} (h : x ^ 2 ≤ 4 * t)
    (ht : 4 * t < (2 * (Nat.sqrt t : ℤ) + 2) ^ 2) :
    -(2 * (Nat.sqrt t : ℤ) + 2) ≤ x ∧ x ≤ 2 * (Nat.sqrt t : ℤ) + 2 := by
  constructor <;> nlinarith [sq_nonneg (x + (2 * (Nat.sqrt t : ℤ) + 2)),
    sq_nonneg (x - (2 * (Nat.sqrt t : ℤ) + 2))]

/-- Disk count: `#{α ≠ 0 : N(α) ≤ N} ≤ 50(N+1)`. -/
theorem card_normLe_le (N : ℕ) : (normLe N).card ≤ 50 * (N + 1) := by
  classical
  set s := Nat.sqrt N with hs_def
  set t : ℤ := 2 * (s : ℤ) + 2 with ht_def
  have hsqN : (N : ℤ) < ((s : ℤ) + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt N
    push_cast
    nlinarith [this]
  have h4N : 4 * (N : ℤ) < t ^ 2 := by
    rw [ht_def]
    nlinarith
  have key : normLe N ⊆
      ((Finset.Icc (-t) t) ×ˢ (Finset.Icc (-t) t)).image
        (fun ab => (⟨ab.1, ab.2⟩ : Eis)) := by
    intro α hα
    rw [mem_normLe] at hα
    obtain ⟨h0, hn⟩ := hα
    rw [Finset.mem_image]
    refine ⟨(α.re, α.im), ?_, by ext <;> rfl⟩
    rw [Finset.mem_product]
    have h4 := four_mul_norm α
    have hc := natNorm_cast α
    have hnZ : norm α ≤ (N : ℤ) := by omega
    have hb2 : α.im ^ 2 ≤ 4 * (N : ℤ) := by
      nlinarith [sq_nonneg (2 * α.re - α.im)]
    have hab2 : (2 * α.re - α.im) ^ 2 ≤ 4 * (N : ℤ) := by
      nlinarith [sq_nonneg α.im]
    have hb : -t ≤ α.im ∧ α.im ≤ t := by
      constructor <;> nlinarith [sq_nonneg (α.im + t), sq_nonneg (α.im - t)]
    have hab : -t ≤ 2 * α.re - α.im ∧ 2 * α.re - α.im ≤ t := by
      constructor <;>
        nlinarith [sq_nonneg (2 * α.re - α.im + t), sq_nonneg (2 * α.re - α.im - t)]
    constructor
    · rw [Finset.mem_Icc]
      constructor <;> omega
    · rw [Finset.mem_Icc]
      exact hb
  calc (normLe N).card
      ≤ (((Finset.Icc (-t) t) ×ˢ (Finset.Icc (-t) t)).image
          (fun ab => (⟨ab.1, ab.2⟩ : Eis))).card := Finset.card_le_card key
    _ ≤ ((Finset.Icc (-t) t) ×ˢ (Finset.Icc (-t) t)).card :=
        Finset.card_image_le
    _ = (Finset.Icc (-t) t).card * (Finset.Icc (-t) t).card :=
        Finset.card_product _ _
    _ ≤ 50 * (N + 1) := by
        rw [Int.card_Icc]
        have hcard : (t + 1 - -t).toNat = 4 * s + 5 := by
          rw [ht_def]
          omega
        rw [hcard]
        have hsN : s * s ≤ N := by
          have h := Nat.sqrt_le' N
          rwa [pow_two] at h
        nlinarith [hsN]

set_option maxHeartbeats 1000000 in
/-- Partial sums of `1/√(i+1)` grow like `2√n`. -/
lemma sum_one_div_sqrt_le (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 : ℝ) / Real.sqrt ((i : ℝ) + 1) ≤ 2 * Real.sqrt n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : Real.sqrt ((n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have h3 : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have h4 : (0 : ℝ) ≤ Real.sqrt ((n : ℝ)) := Real.sqrt_nonneg _
    have hkey : (1 : ℝ) / Real.sqrt ((n : ℝ) + 1)
        ≤ 2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt ((n : ℝ))) := by
      rw [div_le_iff₀ h3]
      nlinarith [h1, h2, h3, h4,
        sq_nonneg (Real.sqrt ((n : ℝ) + 1) - Real.sqrt ((n : ℝ)))]
    have hc1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
      push_cast
      ring
    calc (∑ i ∈ Finset.range n, (1 : ℝ) / Real.sqrt ((i : ℝ) + 1))
          + 1 / Real.sqrt ((n : ℝ) + 1)
        ≤ 2 * Real.sqrt ((n : ℝ))
          + 2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt ((n : ℝ))) :=
          add_le_add ih hkey
      _ = 2 * Real.sqrt ((n : ℝ) + 1) := by ring
      _ = 2 * Real.sqrt ((n + 1 : ℕ) : ℝ) := by rw [hc1]

set_option maxHeartbeats 2000000 in
theorem sum_inv_sqrt_bound (M : ℕ) (hM : 1 ≤ M) :
    ∑ a ∈ Finset.Icc (-(M : ℤ)) M,
      (if 3 * a ^ 2 < 4 * M then (1 : ℝ) / Real.sqrt ((M : ℝ) - 3 / 4 * (a : ℝ) ^ 2) else 0)
      ≤ 50 := by
  obtain ⟨A, hA_def⟩ : ∃ A, A = Nat.sqrt ((4 * M - 1) / 3) :=
    ⟨Nat.sqrt ((4 * M - 1) / 3), rfl⟩
  have hA1 : 3 * (A * A) ≤ 4 * M - 1 := by
    have h : A * A ≤ (4 * M - 1) / 3 := by
      rw [hA_def]
      have hs := Nat.sqrt_le' ((4 * M - 1) / 3)
      rwa [pow_two] at hs
    have h3 := Nat.div_mul_le_self (4 * M - 1) 3
    omega
  have hAmax : ∀ n : ℕ, A < n → ¬ (3 * n ^ 2 < 4 * M) := by
    intro n hn hcon
    have h1 : (4 * M - 1) / 3 < n * n := by
      have hs := Nat.lt_succ_sqrt' ((4 * M - 1) / 3)
      rw [← hA_def] at hs
      have hs' : (4 * M - 1) / 3 < (A + 1) * (A + 1) := by
        simpa [Nat.succ_eq_add_one, pow_two] using hs
      have hnn : (A + 1) * (A + 1) ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
      omega
    rw [pow_two] at hcon
    omega
  set g : ℕ → ℝ := fun k => 2 / Real.sqrt (1 + 3 * A * k) with hg_def
  have hg_nonneg : ∀ k, 0 ≤ g k := by
    intro k
    rw [hg_def]
    positivity
  have hcore : ∀ n : ℕ, n ≤ A → (1 + 3 * A * (A - n)) + 3 * n ^ 2 ≤ 4 * M := by
    intro n hn
    obtain ⟨d, hd⟩ : ∃ d, A = n + d := ⟨A - n, by omega⟩
    have hAn : A - n = d := by omega
    rw [hAn, hd]
    have hA1' : 3 * ((n + d) * (n + d)) ≤ 4 * M - 1 := by
      rw [← hd]
      exact hA1
    have h4 : 1 + 3 * ((n + d) * (n + d)) ≤ 4 * M := by omega
    nlinarith [h4, Nat.zero_le (n * d), Nat.zero_le (n * n)]
  have hterm : ∀ a ∈ Finset.Icc (-(M : ℤ)) M,
      (if 3 * a ^ 2 < 4 * M then (1 : ℝ) / Real.sqrt ((M : ℝ) - 3 / 4 * (a : ℝ) ^ 2) else 0)
        ≤ (if a.natAbs ≤ A then g (A - a.natAbs) else 0) := by
    intro a _
    have hZsq : ((a.natAbs : ℤ)) * ((a.natAbs : ℤ)) = a * a := Int.natAbs_mul_self
    split_ifs with hlt hle
    · set n := a.natAbs with hn_def
      have h3n : 3 * n ^ 2 < 4 * M := by
        have hZ : (3 : ℤ) * ((n : ℤ) * (n : ℤ)) < 4 * M := by
          rw [hn_def, hZsq]
          rw [pow_two] at hlt
          exact_mod_cast hlt
        have : (3 : ℤ) * (n : ℤ) ^ 2 < 4 * M := by
          rw [pow_two]
          exact hZ
        exact_mod_cast this
      have hden : (M : ℝ) - 3 / 4 * (a : ℝ) ^ 2
          = ((4 * M - 3 * n ^ 2 : ℕ) : ℝ) / 4 := by
        have hRsq : ((a : ℝ)) ^ 2 = ((n : ℝ)) ^ 2 := by
          have hc := congrArg (fun z : ℤ => (z : ℝ)) hZsq
          push_cast at hc
          rw [pow_two, pow_two, hn_def]
          linarith [hc]
        rw [hRsq]
        have hle3 : (3 * n ^ 2 : ℕ) ≤ 4 * M := by omega
        rw [Nat.cast_sub hle3]
        push_cast
        ring
      rw [hden, hg_def]
      have hsqrt4 : Real.sqrt (((4 * M - 3 * n ^ 2 : ℕ) : ℝ) / 4)
          = Real.sqrt (((4 * M - 3 * n ^ 2 : ℕ) : ℝ)) / 2 := by
        rw [Real.sqrt_div (by positivity)]
        congr 1
        rw [show (4 : ℝ) = 2 ^ 2 from by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hsqrt4, one_div_div]
      have hmono : Real.sqrt (((1 + 3 * A * (A - n) : ℕ) : ℝ))
          ≤ Real.sqrt (((4 * M - 3 * n ^ 2 : ℕ) : ℝ)) := by
        apply Real.sqrt_le_sqrt
        have hnat : (1 + 3 * A * (A - n) : ℕ) ≤ 4 * M - 3 * n ^ 2 := by
          have := hcore n hle
          omega
        exact_mod_cast hnat
      have hpos1 : (0 : ℝ) < Real.sqrt (((1 + 3 * A * (A - n) : ℕ) : ℝ)) := by
        apply Real.sqrt_pos.mpr
        push_cast
        positivity
      calc (2 : ℝ) / Real.sqrt (((4 * M - 3 * n ^ 2 : ℕ) : ℝ))
          ≤ 2 / Real.sqrt (((1 + 3 * A * (A - n) : ℕ) : ℝ)) := by
            apply div_le_div_of_nonneg_left (by norm_num) hpos1 hmono
        _ = g (A - n) := by
            rw [hg_def]
            norm_cast
    · exfalso
      have h3n : 3 * a.natAbs ^ 2 < 4 * M := by
        have hZ : (3 : ℤ) * ((a.natAbs : ℤ) * (a.natAbs : ℤ)) < 4 * M := by
          rw [hZsq]
          rw [pow_two] at hlt
          exact_mod_cast hlt
        have h2 : (3 : ℤ) * (a.natAbs : ℤ) ^ 2 < 4 * M := by
          rw [pow_two]
          exact hZ
        exact_mod_cast h2
      exact hAmax a.natAbs (by omega) h3n
    · exact hg_nonneg _
    · exact le_refl 0
  calc ∑ a ∈ Finset.Icc (-(M : ℤ)) M,
        (if 3 * a ^ 2 < 4 * M then (1 : ℝ) / Real.sqrt ((M : ℝ) - 3 / 4 * (a : ℝ) ^ 2) else 0)
      ≤ ∑ a ∈ Finset.Icc (-(M : ℤ)) M,
          (if a.natAbs ≤ A then g (A - a.natAbs) else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ a ∈ (Finset.Icc (-(M : ℤ)) M).filter (fun a => a.natAbs ≤ A),
          g (A - a.natAbs) := by
        rw [Finset.sum_filter]
    _ = (∑ a ∈ ((Finset.Icc (-(M : ℤ)) M).filter (fun a => a.natAbs ≤ A)).filter
          (fun a => 0 ≤ a), g (A - a.natAbs))
        + ∑ a ∈ ((Finset.Icc (-(M : ℤ)) M).filter (fun a => a.natAbs ≤ A)).filter
            (fun a => ¬ 0 ≤ a), g (A - a.natAbs) :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ (∑ b ∈ Finset.range (A + 1), g b) + ∑ b ∈ Finset.range (A + 1), g b := by
        have hbound : ∀ s : Finset ℤ,
            (∀ x ∈ s, ∀ y ∈ s, x.natAbs = y.natAbs → x = y) →
            (∀ x ∈ s, x.natAbs ≤ A) →
            ∑ a ∈ s, g (A - a.natAbs) ≤ ∑ b ∈ Finset.range (A + 1), g b := by
          intro s hinj hle
          have hfinj : ∀ x ∈ s, ∀ y ∈ s, A - x.natAbs = A - y.natAbs → x = y := by
            intro x hx y hy hf
            apply hinj x hx y hy
            have h1 := hle x hx
            have h2 := hle y hy
            omega
          rw [← Finset.sum_image hfinj]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro b hb
            simp only [Finset.mem_image] at hb
            obtain ⟨a, ha, rfl⟩ := hb
            rw [Finset.mem_range]
            omega
          · intro b _ _
            exact hg_nonneg b
        apply add_le_add
        · apply hbound
          · intro x hx y hy hxy
            simp only [Finset.mem_filter] at hx hy
            omega
          · intro x hx
            simp only [Finset.mem_filter] at hx
            exact hx.1.2
        · apply hbound
          · intro x hx y hy hxy
            simp only [Finset.mem_filter] at hx hy
            omega
          · intro x hx
            simp only [Finset.mem_filter] at hx
            exact hx.1.2
    _ = ∑ b ∈ Finset.range (A + 1), 2 * g b := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
    _ ≤ 50 := by
        rw [Finset.sum_range_succ' (fun b => 2 * g b) A]
        have hg0 : g 0 = 2 := by
          rw [hg_def]
          norm_num
        have htail : ∑ i ∈ Finset.range A, 2 * g (i + 1) ≤ 8 := by
          rcases Nat.eq_zero_or_pos A with rfl | hA0
          · simp
          have hsA' : (0 : ℝ) < Real.sqrt A := by
            apply Real.sqrt_pos.mpr
            push_cast
            positivity
          have hs3 : (1 : ℝ) ≤ Real.sqrt 3 := by
            rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
            exact Real.sqrt_le_sqrt (by norm_num)
          have hs3' : (0 : ℝ) < Real.sqrt 3 := by linarith
          have hstep : ∀ i ∈ Finset.range A,
              2 * g (i + 1) ≤ (4 / (Real.sqrt 3 * Real.sqrt A)) *
                (1 / Real.sqrt ((i : ℝ) + 1)) := by
            intro i _
            rw [hg_def]
            simp only [Nat.cast_add, Nat.cast_one]
            have hprod : Real.sqrt 3 * Real.sqrt A * Real.sqrt ((i : ℝ) + 1)
                = Real.sqrt (3 * (A : ℝ) * ((i : ℝ) + 1)) := by
              rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3),
                ← Real.sqrt_mul (by positivity)]
            have h1 : Real.sqrt (3 * (A : ℝ) * ((i : ℝ) + 1))
                ≤ Real.sqrt (1 + 3 * A * (i + 1)) := by
              apply Real.sqrt_le_sqrt
              push_cast
              linarith
            have h3 : (0 : ℝ) < Real.sqrt (3 * (A : ℝ) * ((i : ℝ) + 1)) := by
              apply Real.sqrt_pos.mpr
              positivity
            calc 2 * (2 / Real.sqrt (1 + 3 * A * (i + 1)))
                ≤ 2 * (2 / Real.sqrt (3 * (A : ℝ) * ((i : ℝ) + 1))) := by
                  apply mul_le_mul_of_nonneg_left _ (by norm_num)
                  exact div_le_div_of_nonneg_left (by norm_num) h3 h1
              _ = (4 / (Real.sqrt 3 * Real.sqrt A)) * (1 / Real.sqrt ((i : ℝ) + 1)) := by
                  rw [← hprod]
                  have hi1 : (0 : ℝ) < Real.sqrt ((i : ℝ) + 1) := by
                    apply Real.sqrt_pos.mpr
                    positivity
                  field_simp
                  ring
          calc ∑ i ∈ Finset.range A, 2 * g (i + 1)
              ≤ ∑ i ∈ Finset.range A, (4 / (Real.sqrt 3 * Real.sqrt A)) *
                  (1 / Real.sqrt ((i : ℝ) + 1)) :=
                Finset.sum_le_sum hstep
            _ = (4 / (Real.sqrt 3 * Real.sqrt A)) *
                  ∑ i ∈ Finset.range A, (1 : ℝ) / Real.sqrt ((i : ℝ) + 1) := by
                rw [Finset.mul_sum]
            _ ≤ (4 / (Real.sqrt 3 * Real.sqrt A)) * (2 * Real.sqrt A) := by
                apply mul_le_mul_of_nonneg_left (sum_one_div_sqrt_le A) (by positivity)
            _ = 8 / Real.sqrt 3 := by
                field_simp
                ring
            _ ≤ 8 := by
                rw [div_le_iff₀ hs3']
                nlinarith [hs3]
        have hfinal : (∑ i ∈ Finset.range A, 2 * g (i + 1)) + 2 * g 0 ≤ 8 + 4 := by
          rw [hg0]
          linarith [htail]
        linarith [hfinal]

lemma mem_Icc_sqrt_of_sq_le {Q : ℕ} {x : ℤ} (hx : x ^ 2 ≤ (Q : ℤ)) :
    x ∈ Finset.Icc (-(Nat.sqrt Q : ℤ)) (Nat.sqrt Q) := by
  rw [Finset.mem_Icc]
  have h2 : x.natAbs * x.natAbs ≤ Q := by
    have h3 : (x.natAbs : ℤ) * x.natAbs ≤ (Q : ℤ) := by
      rw [Int.natAbs_mul_self', ← pow_two]
      exact hx
    exact_mod_cast h3
  have h4 : x.natAbs ≤ Nat.sqrt Q := Nat.le_sqrt.mpr h2
  omega

lemma sq_le_of_mem_Icc_sqrt {Q : ℕ} {x : ℤ}
    (hx : x ∈ Finset.Icc (-(Nat.sqrt Q : ℤ)) (Nat.sqrt Q)) : x ^ 2 ≤ (Q : ℤ) := by
  rw [Finset.mem_Icc] at hx
  have h1 : x.natAbs ≤ Nat.sqrt Q := by omega
  have h2 : x.natAbs * x.natAbs ≤ Q := by
    calc x.natAbs * x.natAbs ≤ Nat.sqrt Q * Nat.sqrt Q :=
          Nat.mul_le_mul h1 h1
      _ ≤ Q := by
          have hs := Nat.sqrt_le' Q
          rwa [pow_two] at hs
  rw [pow_two, ← Int.natAbs_mul_self']
  exact_mod_cast h2

/-- Points of a square-annulus in `ℤ`: at most `2(√Q − √P)`. -/
lemma card_sq_between_le (s : Finset ℤ) {P Q : ℕ} (hPQ : P ≤ Q)
    (hmem : ∀ x ∈ s, (P : ℤ) < x ^ 2 ∧ x ^ 2 ≤ (Q : ℤ)) :
    s.card ≤ 2 * (Nat.sqrt Q - Nat.sqrt P) := by
  have hsub : s ⊆ Finset.Icc (-(Nat.sqrt Q : ℤ)) (Nat.sqrt Q) \
      Finset.Icc (-(Nat.sqrt P : ℤ)) (Nat.sqrt P) := by
    intro x hx
    obtain ⟨hP, hQ⟩ := hmem x hx
    rw [Finset.mem_sdiff]
    refine ⟨mem_Icc_sqrt_of_sq_le hQ, fun hmem2 => ?_⟩
    have h5 := sq_le_of_mem_Icc_sqrt hmem2
    omega
  have hsq : (Nat.sqrt P : ℤ) ≤ Nat.sqrt Q := by
    exact_mod_cast Nat.sqrt_le_sqrt hPQ
  have hIccSub : Finset.Icc (-(Nat.sqrt P : ℤ)) (Nat.sqrt P) ⊆
      Finset.Icc (-(Nat.sqrt Q : ℤ)) (Nat.sqrt Q) := by
    intro x hx
    rw [Finset.mem_Icc] at *
    omega
  calc s.card
      ≤ (Finset.Icc (-(Nat.sqrt Q : ℤ)) (Nat.sqrt Q) \
          Finset.Icc (-(Nat.sqrt P : ℤ)) (Nat.sqrt P)).card :=
        Finset.card_le_card hsub
    _ ≤ 2 * (Nat.sqrt Q - Nat.sqrt P) := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hIccSub,
          Int.card_Icc, Int.card_Icc]
        omega

/-- Nat-sqrt difference against the gap. -/
lemma nat_sqrt_sub_le {P Q : ℕ} (hPQ : P ≤ Q) (hP : 1 ≤ P) :
    Nat.sqrt Q - Nat.sqrt P ≤ (Q - P) / (2 * Nat.sqrt P) + 1 := by
  obtain ⟨a, ha⟩ : ∃ a, a = Nat.sqrt P := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = Nat.sqrt Q := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have ha1 : 1 ≤ a := by
    rw [ha]
    calc 1 = Nat.sqrt 1 := Nat.sqrt_one.symm
      _ ≤ Nat.sqrt P := Nat.sqrt_le_sqrt hP
  have hab : a ≤ b := by
    rw [ha, hb]
    exact Nat.sqrt_le_sqrt hPQ
  have hbQ : b * b ≤ Q := by
    rw [hb]
    have hs := Nat.sqrt_le' Q
    rwa [pow_two] at hs
  have haP : P ≤ a * a + 2 * a := by
    rw [ha]
    have hs' : P < (Nat.sqrt P + 1) * (Nat.sqrt P + 1) := by
      simpa [Nat.succ_eq_add_one, pow_two] using Nat.lt_succ_sqrt' P
    have hexp : (Nat.sqrt P + 1) * (Nat.sqrt P + 1)
        = Nat.sqrt P * Nat.sqrt P + 2 * Nat.sqrt P + 1 := by
      ring
    omega
  have hkey : (b - a) * (2 * a) ≤ (Q - P) + 2 * a := by
    have h1 : (b - a) * (2 * a) ≤ (b - a) * (b + a) := by
      apply Nat.mul_le_mul_left
      omega
    have h2 : (b - a) * (b + a) = b * b - a * a := by
      obtain ⟨d, hd⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
      subst hd
      have : (a + d) * (a + d) = a * a + (2 * a * d + d * d) := by ring
      rw [this]
      have h3 : (a + d - a) * ((a + d) + a) = 2 * a * d + d * d := by
        have h4 : a + d - a = d := by omega
        rw [h4]
        ring
      omega
    omega
  have hdiv : b - a ≤ ((Q - P) + 2 * a) / (2 * a) :=
    (Nat.le_div_iff_mul_le (by omega : 0 < 2 * a)).mpr hkey
  have heq : ((Q - P) + 2 * a) / (2 * a) = (Q - P) / (2 * a) + 1 :=
    Nat.add_div_right _ (by omega)
  omega

set_option maxHeartbeats 4000000 in
/-- Annulus count (thin version): if `V − U = O(√V)` then the annulus has
`O(√V)` points. -/
theorem card_annulus_le (U V : ℕ) (hUV : U ≤ V) (hU : 1 ≤ U)
    (hthin : V ≤ U + 5 * Nat.sqrt V + 5) :
    ((normLe V).filter (fun α => U < natNorm α)).card ≤
      3000 * (Nat.sqrt V + 1) := by
  classical
  obtain ⟨sV, hsV⟩ : ∃ s, s = Nat.sqrt V := ⟨_, rfl⟩
  set ann := (normLe V).filter (fun α => U < natNorm α) with hann
  -- fiberwise decomposition over the imaginary part
  have hfib : ann.card = ∑ y ∈ Finset.Icc (-(2 * (V : ℤ))) (2 * V),
      (ann.filter (fun α => α.im = y)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro α hα
    rw [Finset.mem_coe, hann, Finset.mem_filter, mem_normLe] at hα
    exact (coord_bound_of_natNorm_le hα.1.2).2
  -- basic per-element facts
  have hmem_ann : ∀ α ∈ ann, (4 * U : ℤ) < (2 * α.re - α.im) ^ 2 + 3 * α.im ^ 2 ∧
      (2 * α.re - α.im) ^ 2 + 3 * α.im ^ 2 ≤ (4 * V : ℤ) := by
    intro α hα
    rw [hann, Finset.mem_filter, mem_normLe] at hα
    obtain ⟨⟨_, hV⟩, hUα⟩ := hα
    have h4 := four_mul_norm α
    have hc := natNorm_cast α
    constructor
    · have : (U : ℤ) < natNorm α := by exact_mod_cast hUα
      omega
    · have : (natNorm α : ℤ) ≤ V := by exact_mod_cast hV
      omega
  -- per-row bound via the x-coordinate
  have hrow : ∀ y : ℤ, (ann.filter (fun α => α.im = y)).card ≤
      ((Finset.Icc (-(8 * (V : ℤ))) (8 * V)).filter
        (fun x => (4 * U : ℤ) - 3 * y ^ 2 < x ^ 2 ∧
          x ^ 2 ≤ (4 * V : ℤ) - 3 * y ^ 2)).card := by
    intro y
    apply Finset.card_le_card_of_injOn (fun α => 2 * α.re - α.im)
    · intro α hα
      simp only [Finset.mem_coe, Finset.mem_filter] at hα
      obtain ⟨hα1, hα2⟩ := hα
      have hf := hmem_ann α hα1
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
      have hbound : α.re ∈ Finset.Icc (-(2 * (V : ℤ))) (2 * V) ∧
          α.im ∈ Finset.Icc (-(2 * (V : ℤ))) (2 * V) := by
        rw [hann, Finset.mem_filter, mem_normLe] at hα1
        exact coord_bound_of_natNorm_le hα1.1.2
      obtain ⟨hre, him⟩ := hbound
      rw [Finset.mem_Icc] at hre him
      refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
      · rw [← hα2]
        linarith [hf.1]
      · rw [← hα2]
        linarith [hf.2]
    · intro α hα β hβ hf
      rw [Finset.mem_coe, Finset.mem_filter] at hα hβ
      have hf' : 2 * α.re - α.im = 2 * β.re - β.im := hf
      ext
      · omega
      · omega
  -- the row-count function
  have hrowc : ∀ y : ℤ, ((Finset.Icc (-(8 * (V : ℤ))) (8 * V)).filter
      (fun x => (4 * U : ℤ) - 3 * y ^ 2 < x ^ 2 ∧
        x ^ 2 ≤ (4 * V : ℤ) - 3 * y ^ 2)).card ≤
      (if 3 * y ^ 2 < (4 * U : ℤ) then
        2 * (Nat.sqrt (4 * V - 3 * y.natAbs ^ 2) - Nat.sqrt (4 * U - 3 * y.natAbs ^ 2))
      else if 3 * y ^ 2 ≤ (4 * V : ℤ) then 4 * sV + 3 else 0) := by
    intro y
    have hysq : (y ^ 2 : ℤ) = ((y.natAbs ^ 2 : ℕ) : ℤ) := by
      have h := Int.natAbs_mul_self' (a := y)
      calc (y ^ 2 : ℤ) = y * y := by ring
        _ = (y.natAbs : ℤ) * y.natAbs := h.symm
        _ = ((y.natAbs ^ 2 : ℕ) : ℤ) := by
            push_cast
            ring
    split_ifs with h1 h2
    · -- interior
      have hyy : y * y = ((y.natAbs * y.natAbs : ℕ) : ℤ) := by
        rw [← Int.natAbs_mul_self']
        push_cast
        ring
      rw [pow_two] at h1
      apply card_sq_between_le _
        (Nat.sub_le_sub_right (by omega : 4 * U ≤ 4 * V) _)
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨-, hxa, hxb⟩ := hx
      have hcastU : ((4 * U - 3 * y.natAbs ^ 2 : ℕ) : ℤ) = 4 * U - 3 * y ^ 2 := by
        rw [pow_two, pow_two]
        omega
      have hcastV : ((4 * V - 3 * y.natAbs ^ 2 : ℕ) : ℤ) = 4 * V - 3 * y ^ 2 := by
        rw [pow_two, pow_two]
        omega
      exact ⟨by rw [hcastU]; exact hxa, by rw [hcastV]; exact hxb⟩
    · -- boundary: crude ball bound
      calc ((Finset.Icc (-(8 * (V : ℤ))) (8 * V)).filter
            (fun x => (4 * U : ℤ) - 3 * y ^ 2 < x ^ 2 ∧
              x ^ 2 ≤ (4 * V : ℤ) - 3 * y ^ 2)).card
          ≤ (Finset.Icc (-(Nat.sqrt (4 * V) : ℤ)) (Nat.sqrt (4 * V))).card := by
            apply Finset.card_le_card
            intro x hx
            rw [Finset.mem_filter] at hx
            apply mem_Icc_sqrt_of_sq_le
            have := hx.2.2
            push_cast
            nlinarith [sq_nonneg y]
        _ ≤ 4 * sV + 3 := by
            rw [Int.card_Icc]
            have hs4 : Nat.sqrt (4 * V) ≤ 2 * sV + 1 := by
              rw [hsV]
              have h1 : 4 * V < (2 * (Nat.sqrt V + 1)) ^ 2 := by
                have := Nat.lt_succ_sqrt' V
                nlinarith [this]
              by_contra hcon
              push_neg at hcon
              have h2 : (2 * (Nat.sqrt V + 1)) ^ 2 ≤ Nat.sqrt (4 * V) ^ 2 := by
                have : 2 * (Nat.sqrt V + 1) ≤ Nat.sqrt (4 * V) := by omega
                exact Nat.pow_le_pow_left this 2
              have h3 := Nat.sqrt_le' (4 * V)
              omega
            omega
    · -- empty
      rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _
      rintro ⟨-, h2⟩
      nlinarith [sq_nonneg x, sq_nonneg y]
  -- shorthand for the row bound
  obtain ⟨Rb, hRb⟩ : ∃ f : ℤ → ℕ, f = fun y =>
      (if 3 * y ^ 2 < (4 * U : ℤ) then
        2 * (Nat.sqrt (4 * V - 3 * y.natAbs ^ 2) - Nat.sqrt (4 * U - 3 * y.natAbs ^ 2))
      else if 3 * y ^ 2 ≤ (4 * V : ℤ) then 4 * sV + 3 else 0) :=
    ⟨_, rfl⟩
  have hcard1 : ann.card ≤ ∑ y ∈ Finset.Icc (-(2 * (V : ℤ))) (2 * V), Rb y := by
    rw [hfib]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [hRb]
    exact (hrow y).trans (hrowc y)
  -- the boundary-row count
  obtain ⟨s₁, hs₁⟩ : ∃ s, s = Nat.sqrt ((4 * V) / 3) := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ s, s = Nat.sqrt ((4 * U - 1) / 3) := ⟨_, rfl⟩
  have hs₁sq : 3 * (s₁ * s₁) ≤ 4 * V := by
    have h := Nat.sqrt_le' ((4 * V) / 3)
    rw [pow_two] at h
    rw [← hs₁] at h
    have h2 := Nat.div_mul_le_self (4 * V) 3
    omega
  have hs₂sq : 4 * U ≤ 3 * ((s₂ + 1) * (s₂ + 1)) + 3 := by
    have h := Nat.lt_succ_sqrt' ((4 * U - 1) / 3)
    have h' : (4 * U - 1) / 3 < (s₂ + 1) * (s₂ + 1) := by
      rw [hs₂]
      simpa [Nat.succ_eq_add_one, pow_two] using h
    have h3 : 3 * ((4 * U - 1) / 3) + 2 ≥ 4 * U - 1 := by omega
    omega
  have hsV2 : sV * sV ≤ V := by
    rw [hsV]
    have h := Nat.sqrt_le' V
    rwa [pow_two] at h
  have hs12 : s₁ ≤ s₂ + 13 := by
    by_contra hcon
    push_neg at hcon
    have h14 : s₂ + 14 ≤ s₁ := by omega
    have hA : (s₂ + 14) * (s₂ + 14) ≤ s₁ * s₁ := Nat.mul_le_mul h14 h14
    -- pass to ℤ
    have hZ1 : (3 : ℤ) * ((s₂ + 14) * (s₂ + 14)) ≤ 4 * V := by
      have := le_trans (Nat.mul_le_mul_left 3 hA) hs₁sq
      exact_mod_cast this
    have hZ2 : (4 : ℤ) * U ≤ 3 * ((s₂ + 1) * (s₂ + 1)) + 3 := by
      exact_mod_cast hs₂sq
    have hZ3 : (V : ℤ) ≤ U + 5 * sV + 5 := by
      have h := hthin
      rw [← hsV] at h
      exact_mod_cast h
    have hZ4 : (sV : ℤ) * sV ≤ V := by exact_mod_cast hsV2
    -- E1 : 20 sV ≥ 78 s₂ + 562
    have hE1 : (78 : ℤ) * s₂ + 562 ≤ 20 * sV := by nlinarith [hZ1, hZ2, hZ3]
    -- E2 : 4 sV² ≤ 3(s₂+1)² + 23 + 20 sV
    have hE2 : (4 : ℤ) * (sV * sV) ≤ 3 * ((s₂ + 1) * (s₂ + 1)) + 23 + 20 * sV := by
      nlinarith [hZ4, hZ3, hZ2]
    -- contradiction via (x−y)(x+y−100) ≥ 0 with x = 20 sV, y = 78 s₂ + 562
    have hxy : (0 : ℤ) ≤ 20 * sV - (78 * s₂ + 562) := by linarith
    have hsum : (0 : ℤ) ≤ 20 * sV + (78 * s₂ + 562) - 100 := by linarith
    have hprod := mul_nonneg hxy hsum
    nlinarith [hprod, hE2, hE1, sq_nonneg ((s₂ : ℤ)), Int.natCast_nonneg s₂]
  have hbdry_count : ((Finset.Icc (-(2 * (V : ℤ))) (2 * V)).filter
      (fun y => ¬ (3 * y ^ 2 < (4 * U : ℤ)) ∧ 3 * y ^ 2 ≤ (4 * V : ℤ))).card
      ≤ 2 * (s₁ - s₂) := by
    have hsub : (Finset.Icc (-(2 * (V : ℤ))) (2 * V)).filter
        (fun y => ¬ (3 * y ^ 2 < (4 * U : ℤ)) ∧ 3 * y ^ 2 ≤ (4 * V : ℤ))
        ⊆ Finset.Icc (-(s₁ : ℤ)) s₁ \ Finset.Icc (-(s₂ : ℤ)) s₂ := by
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨-, hyU, hyV⟩ := hy
      have hyy : y * y = ((y.natAbs * y.natAbs : ℕ) : ℤ) := by
        rw [← Int.natAbs_mul_self']
        push_cast
        ring
      rw [pow_two] at hyU hyV
      have hnV : 3 * (y.natAbs * y.natAbs) ≤ 4 * V := by omega
      have hnU : 4 * U ≤ 3 * (y.natAbs * y.natAbs) := by omega
      rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Icc]
      constructor
      · have h1 : y.natAbs * y.natAbs ≤ (4 * V) / 3 :=
          (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
        have h2 : y.natAbs ≤ s₁ := by
          rw [hs₁]
          exact Nat.le_sqrt.mpr h1
        omega
      · intro hcon
        have h3 : y.natAbs ≤ s₂ := by omega
        have h4 : y.natAbs * y.natAbs ≤ s₂ * s₂ := Nat.mul_le_mul h3 h3
        have h5 : s₂ * s₂ ≤ (4 * U - 1) / 3 := by
          rw [hs₂]
          have h := Nat.sqrt_le' ((4 * U - 1) / 3)
          rwa [pow_two] at h
        have h6 := Nat.div_mul_le_self (4 * U - 1) 3
        omega
    have hIccSub : Finset.Icc (-(s₂ : ℤ)) s₂ ⊆ Finset.Icc (-(s₁ : ℤ)) s₁ := by
      intro x hx
      rw [Finset.mem_Icc] at *
      have : (s₂ : ℤ) ≤ s₁ := by
        have h5 : s₂ * s₂ ≤ (4 * U - 1) / 3 := by
          rw [hs₂]
          have h := Nat.sqrt_le' ((4 * U - 1) / 3)
          rwa [pow_two] at h
        have h7 : s₂ * s₂ ≤ (4 * V) / 3 :=
          le_trans h5 (Nat.div_le_div_right (by omega))
        have h8 : s₂ ≤ s₁ := by
          rw [hs₁]
          exact Nat.le_sqrt.mpr h7
        exact_mod_cast h8
      omega
    calc ((Finset.Icc (-(2 * (V : ℤ))) (2 * V)).filter
          (fun y => ¬ (3 * y ^ 2 < (4 * U : ℤ)) ∧ 3 * y ^ 2 ≤ (4 * V : ℤ))).card
        ≤ (Finset.Icc (-(s₁ : ℤ)) s₁ \ Finset.Icc (-(s₂ : ℤ)) s₂).card :=
          Finset.card_le_card hsub
      _ ≤ 2 * (s₁ - s₂) := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hIccSub,
            Int.card_Icc, Int.card_Icc]
          omega
  -- interior rows: real-valued comparison
  have hint_ptwise : ∀ y : ℤ, 3 * y ^ 2 < (4 * U : ℤ) → (Rb y : ℝ) ≤
      4 * ((V : ℝ) - U) *
        (if 3 * y ^ 2 < 4 * (U : ℤ) then
          (1 : ℝ) / Real.sqrt ((U : ℝ) - 3 / 4 * (y : ℝ) ^ 2) else 0) + 2 := by
    intro y hy
    rw [hRb]
    simp only [if_pos hy]
    have hyy : y * y = ((y.natAbs * y.natAbs : ℕ) : ℤ) := by
      rw [← Int.natAbs_mul_self']
      push_cast
      ring
    have hy' := hy
    rw [pow_two] at hy'
    have hA1 : 1 ≤ 4 * U - 3 * y.natAbs ^ 2 := by
      rw [pow_two]
      omega
    have hPQ : 4 * U - 3 * y.natAbs ^ 2 ≤ 4 * V - 3 * y.natAbs ^ 2 :=
      Nat.sub_le_sub_right (by omega) _
    have hgap : (4 * V - 3 * y.natAbs ^ 2) - (4 * U - 3 * y.natAbs ^ 2)
        = 4 * (V - U) := by
      rw [pow_two]
      omega
    have hnat := nat_sqrt_sub_le hPQ hA1
    rw [hgap] at hnat
    -- cast the nat bound to ℝ
    have hcastb : ((2 * (Nat.sqrt (4 * V - 3 * y.natAbs ^ 2)
        - Nat.sqrt (4 * U - 3 * y.natAbs ^ 2)) : ℕ) : ℝ)
        ≤ 2 * (((4 * (V - U)) / (2 * Nat.sqrt (4 * U - 3 * y.natAbs ^ 2)) : ℕ) : ℝ)
          + 2 := by
      push_cast
      have : ((Nat.sqrt (4 * V - 3 * y.natAbs ^ 2)
          - Nat.sqrt (4 * U - 3 * y.natAbs ^ 2) : ℕ) : ℝ)
          ≤ (((4 * (V - U)) / (2 * Nat.sqrt (4 * U - 3 * y.natAbs ^ 2)) + 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      push_cast at this
      linarith
    have hsA1 : 1 ≤ Nat.sqrt (4 * U - 3 * y.natAbs ^ 2) := by
      calc 1 = Nat.sqrt 1 := Nat.sqrt_one.symm
        _ ≤ Nat.sqrt (4 * U - 3 * y.natAbs ^ 2) := Nat.sqrt_le_sqrt hA1
    have hdivle : (((4 * (V - U)) / (2 * Nat.sqrt (4 * U - 3 * y.natAbs ^ 2)) : ℕ) : ℝ)
        ≤ (4 * ((V : ℝ) - U)) / (2 * (Nat.sqrt (4 * U - 3 * y.natAbs ^ 2) : ℝ)) := by
      have h1 := Nat.cast_div_le (α := ℝ)
        (m := 4 * (V - U)) (n := 2 * Nat.sqrt (4 * U - 3 * y.natAbs ^ 2))
      calc (((4 * (V - U)) / (2 * Nat.sqrt (4 * U - 3 * y.natAbs ^ 2)) : ℕ) : ℝ)
          ≤ ((4 * (V - U) : ℕ) : ℝ) /
              ((2 * Nat.sqrt (4 * U - 3 * y.natAbs ^ 2) : ℕ) : ℝ) := h1
        _ = (4 * ((V : ℝ) - U)) / (2 * (Nat.sqrt (4 * U - 3 * y.natAbs ^ 2) : ℝ)) := by
            have hVU : (U : ℕ) ≤ V := hUV
            rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hVU]
            push_cast
            ring
    -- 1/NatSqrt ≤ 2/√real
    have hAcast : ((4 * U - 3 * y.natAbs ^ 2 : ℕ) : ℝ) = 4 * U - 3 * (y : ℝ) ^ 2 := by
      have h1 : ((4 * U - 3 * y.natAbs ^ 2 : ℕ) : ℤ) = 4 * U - 3 * y ^ 2 := by
        rw [pow_two, pow_two]
        omega
      have h2 := congrArg (fun z : ℤ => (z : ℝ)) h1
      push_cast at h2
      convert h2 using 2 <;> push_cast <;> ring
    have hsqrt_lb : Real.sqrt ((4 * U : ℝ) - 3 * (y : ℝ) ^ 2)
        ≤ 2 * (Nat.sqrt (4 * U - 3 * y.natAbs ^ 2) : ℝ) := by
      have hs := Nat.lt_succ_sqrt' (4 * U - 3 * y.natAbs ^ 2)
      have hs' : (4 * U - 3 * y.natAbs ^ 2 : ℕ)
          < (Nat.sqrt (4 * U - 3 * y.natAbs ^ 2) + 1) *
            (Nat.sqrt (4 * U - 3 * y.natAbs ^ 2) + 1) := by
        simpa [Nat.succ_eq_add_one, pow_two] using hs
      have h4s : (4 * U - 3 * y.natAbs ^ 2 : ℕ)
          ≤ 4 * (Nat.sqrt (4 * U - 3 * y.natAbs ^ 2)
            * Nat.sqrt (4 * U - 3 * y.natAbs ^ 2)) := by
        nlinarith [hsA1]
    -- √x ≤ √(4s²) = 2s
      have h5 : ((4 * U - 3 * y.natAbs ^ 2 : ℕ) : ℝ)
          ≤ (2 * (Nat.sqrt (4 * U - 3 * y.natAbs ^ 2) : ℝ)) ^ 2 := by
        have h6 : ((4 * U - 3 * y.natAbs ^ 2 : ℕ) : ℝ)
            ≤ ((4 * (Nat.sqrt (4 * U - 3 * y.natAbs ^ 2)
              * Nat.sqrt (4 * U - 3 * y.natAbs ^ 2)) : ℕ) : ℝ) := by
          exact_mod_cast h4s
        calc ((4 * U - 3 * y.natAbs ^ 2 : ℕ) : ℝ) ≤ _ := h6
          _ = (2 * (Nat.sqrt (4 * U - 3 * y.natAbs ^ 2) : ℝ)) ^ 2 := by
              push_cast
              ring
      rw [← hAcast]
      calc Real.sqrt ((4 * U - 3 * y.natAbs ^ 2 : ℕ) : ℝ)
          ≤ Real.sqrt ((2 * (Nat.sqrt (4 * U - 3 * y.natAbs ^ 2) : ℝ)) ^ 2) :=
            Real.sqrt_le_sqrt h5
        _ = 2 * (Nat.sqrt (4 * U - 3 * y.natAbs ^ 2) : ℝ) := by
            rw [Real.sqrt_sq (by positivity)]
    -- combine: Rb ≤ 4(V−U)/(2s) · 2 + 2 ≤ 4(V−U) · (2/√A)/2 + 2
    have hUterm : (U : ℝ) - 3 / 4 * (y : ℝ) ^ 2 = ((4 * U : ℝ) - 3 * (y : ℝ) ^ 2) / 4 := by
      ring
    have hApos : (0 : ℝ) < (4 * U : ℝ) - 3 * (y : ℝ) ^ 2 := by
      rw [← hAcast]
      have : (1 : ℝ) ≤ ((4 * U - 3 * y.natAbs ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast hA1
      linarith
    have hterm_eq : (1 : ℝ) / Real.sqrt ((U : ℝ) - 3 / 4 * (y : ℝ) ^ 2)
        = 2 / Real.sqrt ((4 * U : ℝ) - 3 * (y : ℝ) ^ 2) := by
      rw [hUterm, Real.sqrt_div (by positivity),
        show (4 : ℝ) = 2 ^ 2 from by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2), one_div_div]
    rw [hterm_eq]
    have hsqrtApos : (0 : ℝ) < Real.sqrt ((4 * U : ℝ) - 3 * (y : ℝ) ^ 2) :=
      Real.sqrt_pos.mpr hApos
    have hsApos : (0 : ℝ) < (Nat.sqrt (4 * U - 3 * y.natAbs ^ 2) : ℝ) := by
      exact_mod_cast hsA1
    calc ((2 * (Nat.sqrt (4 * V - 3 * y.natAbs ^ 2)
          - Nat.sqrt (4 * U - 3 * y.natAbs ^ 2)) : ℕ) : ℝ)
        ≤ 2 * (((4 * (V - U)) / (2 * Nat.sqrt (4 * U - 3 * y.natAbs ^ 2)) : ℕ) : ℝ)
          + 2 := hcastb
      _ ≤ 2 * ((4 * ((V : ℝ) - U)) /
            (2 * (Nat.sqrt (4 * U - 3 * y.natAbs ^ 2) : ℝ))) + 2 := by
          have := hdivle
          linarith
      _ = 4 * ((V : ℝ) - U) *
            (1 / (Nat.sqrt (4 * U - 3 * y.natAbs ^ 2) : ℝ)) + 2 := by
          field_simp
          try ring
      _ ≤ 4 * ((V : ℝ) - U) *
            (2 / Real.sqrt ((4 * U : ℝ) - 3 * (y : ℝ) ^ 2)) + 2 := by
          have hVU' : (0 : ℝ) ≤ (V : ℝ) - U := by
            have h := (Nat.cast_le (α := ℝ)).mpr hUV
            linarith
          have h1div : (1 : ℝ) / (Nat.sqrt (4 * U - 3 * y.natAbs ^ 2) : ℝ)
              ≤ 2 / Real.sqrt ((4 * U : ℝ) - 3 * (y : ℝ) ^ 2) := by
            rw [div_le_div_iff₀ hsApos hsqrtApos]
            linarith [hsqrt_lb]
          have h2 := mul_le_mul_of_nonneg_left h1div
            (by linarith : (0 : ℝ) ≤ 4 * ((V : ℝ) - U))
          linarith
  -- interior rows lie in `Icc (−U) U`
  have hAsub : ∀ y : ℤ, 3 * y ^ 2 < (4 * U : ℤ) → -(U : ℤ) ≤ y ∧ y ≤ (U : ℤ) := by
    intro y hy
    have hU1 : (1 : ℤ) ≤ (U : ℤ) := by exact_mod_cast hU
    rw [pow_two] at hy
    constructor
    · by_contra hcon
      push_neg at hcon
      have h1 : y ≤ -(U : ℤ) - 1 := by omega
      have h2 : ((U : ℤ) + 1) * ((U : ℤ) + 1) ≤ y * y := by
        nlinarith [h1, hU1]
      nlinarith [h2, hy, hU1]
    · by_contra hcon
      push_neg at hcon
      have h1 : (U : ℤ) + 1 ≤ y := by omega
      have h2 : ((U : ℤ) + 1) * ((U : ℤ) + 1) ≤ y * y :=
        mul_le_mul h1 h1 (by linarith) (by linarith)
      nlinarith [h2, hy, hU1]
  -- `s₁ ≤ 2 sV + 1` and the interior row count
  have hsV1 : 1 ≤ sV := by
    rw [hsV]
    calc 1 = Nat.sqrt 1 := Nat.sqrt_one.symm
      _ ≤ Nat.sqrt V := Nat.sqrt_le_sqrt (le_trans hU hUV)
  have hVlt : V < (sV + 1) * (sV + 1) := by
    rw [hsV]
    simpa [Nat.succ_eq_add_one, pow_two] using Nat.lt_succ_sqrt' V
  -- split the row-sum
  have hsplit := (Finset.sum_filter_add_sum_filter_not
    (Finset.Icc (-(2 * (V : ℤ))) (2 * V)) (fun y => 3 * y ^ 2 < (4 * U : ℤ)) Rb).symm
  set A := (Finset.Icc (-(2 * (V : ℤ))) (2 * V)).filter
    (fun y => 3 * y ^ 2 < (4 * U : ℤ)) with hA_set
  set B := (Finset.Icc (-(2 * (V : ℤ))) (2 * V)).filter
    (fun y => ¬ 3 * y ^ 2 < (4 * U : ℤ)) with hB_set
  -- boundary part (ℕ)
  have hBsum : ∑ y ∈ B, Rb y ≤ 26 * (4 * sV + 3) := by
    have hBval : ∑ y ∈ B, Rb y
        = ∑ y ∈ B.filter (fun y => 3 * y ^ 2 ≤ (4 * V : ℤ)), (4 * sV + 3) := by
      have hstep : ∀ y ∈ B, Rb y = if 3 * y ^ 2 ≤ (4 * V : ℤ) then 4 * sV + 3 else 0 := by
        intro y hy
        rw [hB_set, Finset.mem_filter] at hy
        rw [hRb]
        simp only [if_neg hy.2]
      rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter]
    rw [hBval, Finset.sum_const, smul_eq_mul]
    have hcount : (B.filter (fun y => 3 * y ^ 2 ≤ (4 * V : ℤ))).card ≤ 2 * (s₁ - s₂) := by
      have heq : B.filter (fun y => 3 * y ^ 2 ≤ (4 * V : ℤ))
          = (Finset.Icc (-(2 * (V : ℤ))) (2 * V)).filter
              (fun y => ¬ (3 * y ^ 2 < (4 * U : ℤ)) ∧ 3 * y ^ 2 ≤ (4 * V : ℤ)) := by
        rw [hB_set, Finset.filter_filter]
      rw [heq]
      exact hbdry_count
    calc (B.filter (fun y => 3 * y ^ 2 ≤ (4 * V : ℤ))).card * (4 * sV + 3)
        ≤ (2 * (s₁ - s₂)) * (4 * sV + 3) :=
          Nat.mul_le_mul_right _ hcount
      _ ≤ 26 * (4 * sV + 3) := by
          have := hs12
          have hmul : 2 * (s₁ - s₂) ≤ 26 := by omega
          exact Nat.mul_le_mul_right _ hmul
  -- interior part (ℝ)
  have hAcard : A.card ≤ 4 * sV + 3 := by
    have hs1b : s₁ ≤ 2 * sV + 1 := by
      nlinarith [hs₁sq, hVlt, hsV1]
    have hsubA : A ⊆ Finset.Icc (-(2 * (sV : ℤ) + 1)) (2 * sV + 1) := by
      intro y hy
      rw [hA_set, Finset.mem_filter] at hy
      obtain ⟨-, hy2⟩ := hy
      have hyy : y * y = ((y.natAbs * y.natAbs : ℕ) : ℤ) := by
        rw [← Int.natAbs_mul_self']
        push_cast
        ring
      rw [pow_two] at hy2
      have hnat : 3 * (y.natAbs * y.natAbs) < 4 * U := by omega
      have hdiv : y.natAbs * y.natAbs ≤ (4 * V) / 3 :=
        (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
      have hle1 : y.natAbs ≤ s₁ := by
        rw [hs₁]
        exact Nat.le_sqrt.mpr hdiv
      rw [Finset.mem_Icc]
      omega
    calc A.card ≤ (Finset.Icc (-(2 * (sV : ℤ) + 1)) (2 * sV + 1)).card :=
          Finset.card_le_card hsubA
      _ ≤ 4 * sV + 3 := by
          rw [Int.card_Icc]
          omega
  have hAsum : (∑ y ∈ A, (Rb y : ℝ)) ≤
      4 * ((V : ℝ) - U) * 50 + 2 * (4 * sV + 3) := by
    have hptwise : ∀ y ∈ A, (Rb y : ℝ) ≤
        4 * ((V : ℝ) - U) *
          (if 3 * y ^ 2 < (4 * U : ℤ) then
            (1 : ℝ) / Real.sqrt ((U : ℝ) - 3 / 4 * (y : ℝ) ^ 2) else 0) + 2 := by
      intro y hy
      rw [hA_set, Finset.mem_filter] at hy
      exact hint_ptwise y hy.2
    calc (∑ y ∈ A, (Rb y : ℝ))
        ≤ ∑ y ∈ A, (4 * ((V : ℝ) - U) *
            (if 3 * y ^ 2 < (4 * U : ℤ) then
              (1 : ℝ) / Real.sqrt ((U : ℝ) - 3 / 4 * (y : ℝ) ^ 2) else 0) + 2) :=
          Finset.sum_le_sum hptwise
      _ = 4 * ((V : ℝ) - U) * (∑ y ∈ A,
            (if 3 * y ^ 2 < (4 * U : ℤ) then
              (1 : ℝ) / Real.sqrt ((U : ℝ) - 3 / 4 * (y : ℝ) ^ 2) else 0))
          + 2 * A.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum,
            nsmul_eq_mul, mul_comm ((A.card : ℝ)) 2]
      _ ≤ 4 * ((V : ℝ) - U) * 50 + 2 * (4 * sV + 3) := by
          have hVU0 : (0 : ℝ) ≤ (V : ℝ) - U := by
            have h := (Nat.cast_le (α := ℝ)).mpr hUV
            linarith
          have hsum50 : (∑ y ∈ A,
              (if 3 * y ^ 2 < (4 * U : ℤ) then
                (1 : ℝ) / Real.sqrt ((U : ℝ) - 3 / 4 * (y : ℝ) ^ 2) else 0)) ≤ 50 := by
            calc (∑ y ∈ A,
                (if 3 * y ^ 2 < (4 * U : ℤ) then
                  (1 : ℝ) / Real.sqrt ((U : ℝ) - 3 / 4 * (y : ℝ) ^ 2) else 0))
                ≤ ∑ y ∈ Finset.Icc (-(U : ℤ)) U,
                    (if 3 * y ^ 2 < (4 * U : ℤ) then
                      (1 : ℝ) / Real.sqrt ((U : ℝ) - 3 / 4 * (y : ℝ) ^ 2) else 0) := by
                  apply Finset.sum_le_sum_of_subset_of_nonneg
                  · intro y hy
                    rw [hA_set, Finset.mem_filter] at hy
                    rw [Finset.mem_Icc]
                    exact hAsub y hy.2
                  · intro y _ _
                    split_ifs with h
                    · positivity
                    · exact le_refl 0
              _ ≤ 50 := sum_inv_sqrt_bound U hU
          have h1 := mul_le_mul_of_nonneg_left hsum50
            (by linarith : (0 : ℝ) ≤ 4 * ((V : ℝ) - U))
          have h2 : (A.card : ℝ) ≤ ((4 * sV + 3 : ℕ) : ℝ) := by
            exact_mod_cast hAcard
          push_cast at h2 ⊢
          linarith
  -- final numeric assembly
  have hcast_main : (ann.card : ℝ) ≤
      (4 * ((V : ℝ) - U) * 50 + 2 * (4 * sV + 3)) + 26 * (4 * sV + 3) := by
    have hc1 : (ann.card : ℝ) ≤ ∑ y ∈ Finset.Icc (-(2 * (V : ℤ))) (2 * V), (Rb y : ℝ) := by
      have := hcard1
      calc (ann.card : ℝ)
          ≤ ((∑ y ∈ Finset.Icc (-(2 * (V : ℤ))) (2 * V), Rb y : ℕ) : ℝ) := by
            exact_mod_cast this
        _ = ∑ y ∈ Finset.Icc (-(2 * (V : ℤ))) (2 * V), (Rb y : ℝ) := by
            push_cast
            rfl
    have hsplitR : ∑ y ∈ Finset.Icc (-(2 * (V : ℤ))) (2 * V), (Rb y : ℝ)
        = (∑ y ∈ A, (Rb y : ℝ)) + ∑ y ∈ B, (Rb y : ℝ) := by
      rw [hA_set, hB_set]
      exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hBsumR : (∑ y ∈ B, (Rb y : ℝ)) ≤ 26 * (4 * sV + 3) := by
      calc (∑ y ∈ B, (Rb y : ℝ)) = ((∑ y ∈ B, Rb y : ℕ) : ℝ) := by
            push_cast
            rfl
        _ ≤ ((26 * (4 * sV + 3) : ℕ) : ℝ) := by exact_mod_cast hBsum
        _ = 26 * (4 * sV + 3) := by push_cast; ring
    calc (ann.card : ℝ) ≤ ∑ y ∈ Finset.Icc (-(2 * (V : ℤ))) (2 * V), (Rb y : ℝ) := hc1
      _ = (∑ y ∈ A, (Rb y : ℝ)) + ∑ y ∈ B, (Rb y : ℝ) := hsplitR
      _ ≤ (4 * ((V : ℝ) - U) * 50 + 2 * (4 * sV + 3)) + 26 * (4 * sV + 3) := by
          have := hAsum
          have := hBsumR
          linarith
  have hthinR : (V : ℝ) - U ≤ 5 * (sV : ℝ) + 5 := by
    have h := (Nat.cast_le (α := ℝ)).mpr hthin
    push_cast at h
    rw [← hsV] at h
    linarith
  have hfinal : (ann.card : ℝ) ≤ 3000 * ((sV : ℝ) + 1) := by
    have h1 := hcast_main
    have h2 : (0 : ℝ) ≤ (sV : ℝ) := Nat.cast_nonneg sV
    nlinarith [hthinR, h2]
  rw [hsV] at hfinal
  exact_mod_cast hfinal

/-- Inverse-norm sum over the disk: `∑_{0<N(α)≤N} 1/|α| ≤ C √N`. -/
theorem sum_inv_abs_le (N : ℕ) :
    ∑ α ∈ normLe N, (1 : ℝ) / ‖toC α‖ ≤ 500 * Real.sqrt (N + 1) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · have h0 : normLe 0 = ∅ := by
        ext α
        simp only [mem_normLe, Finset.notMem_empty, iff_false, not_and, Nat.le_zero]
        intro h0 hn
        exact h0 (natNorm_eq_zero_iff.mp hn)
      rw [h0, Finset.sum_empty]
      positivity
    have hsplit : ∑ α ∈ normLe N, (1 : ℝ) / ‖toC α‖
        = (∑ α ∈ (normLe N).filter (fun α => natNorm α ≤ N / 2),
            (1 : ℝ) / ‖toC α‖)
          + ∑ α ∈ (normLe N).filter (fun α => ¬ natNorm α ≤ N / 2),
              (1 : ℝ) / ‖toC α‖ :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hinner : (normLe N).filter (fun α => natNorm α ≤ N / 2) = normLe (N / 2) := by
      ext α
      simp only [Finset.mem_filter, mem_normLe]
      constructor
      · rintro ⟨⟨h0, _⟩, h2⟩
        exact ⟨h0, h2⟩
      · rintro ⟨h0, h2⟩
        exact ⟨⟨h0, le_trans h2 (Nat.div_le_self N 2)⟩, h2⟩
    have hterm : ∀ α ∈ (normLe N).filter (fun α => ¬ natNorm α ≤ N / 2),
        (1 : ℝ) / ‖toC α‖ ≤ 1 / Real.sqrt (((N / 2 : ℕ) : ℝ) + 1) := by
      intro α hα
      simp only [Finset.mem_filter, mem_normLe, not_le] at hα
      obtain ⟨⟨h0, _⟩, h2⟩ := hα
      rw [norm_toC]
      apply one_div_le_one_div_of_le
      · positivity
      · apply Real.sqrt_le_sqrt
        have hc := natNorm_cast α
        have h3 : ((N / 2 + 1 : ℕ) : ℤ) ≤ norm α := by
          rw [← hc]
          exact_mod_cast h2
        calc ((N / 2 : ℕ) : ℝ) + 1 = ((N / 2 + 1 : ℕ) : ℝ) := by
              push_cast
              ring
          _ ≤ ((norm α : ℤ) : ℝ) := by
              have h4 : (((N / 2 + 1 : ℕ) : ℤ) : ℝ) ≤ ((norm α : ℤ) : ℝ) := by
                exact_mod_cast h3
              rw [Int.cast_natCast] at h4
              exact h4
    have hboundary : ∑ α ∈ (normLe N).filter (fun α => ¬ natNorm α ≤ N / 2),
        (1 : ℝ) / ‖toC α‖
        ≤ (50 * ((N : ℝ) + 1)) / Real.sqrt (((N / 2 : ℕ) : ℝ) + 1) := by
      calc ∑ α ∈ (normLe N).filter (fun α => ¬ natNorm α ≤ N / 2),
            (1 : ℝ) / ‖toC α‖
          ≤ ((normLe N).filter (fun α => ¬ natNorm α ≤ N / 2)).card •
              (1 / Real.sqrt (((N / 2 : ℕ) : ℝ) + 1)) :=
            Finset.sum_le_card_nsmul _ _ _ hterm
        _ = (((normLe N).filter (fun α => ¬ natNorm α ≤ N / 2)).card : ℝ) *
              (1 / Real.sqrt (((N / 2 : ℕ) : ℝ) + 1)) := by
            rw [nsmul_eq_mul]
        _ ≤ (50 * ((N : ℝ) + 1)) * (1 / Real.sqrt (((N / 2 : ℕ) : ℝ) + 1)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hfil : ((normLe N).filter (fun α => ¬ natNorm α ≤ N / 2)).card
                ≤ (normLe N).card := Finset.card_filter_le _ _
            calc (((normLe N).filter (fun α => ¬ natNorm α ≤ N / 2)).card : ℝ)
                ≤ ((normLe N).card : ℝ) := by exact_mod_cast hfil
              _ ≤ 50 * ((N : ℝ) + 1) := by exact_mod_cast card_normLe_le N
        _ = (50 * ((N : ℝ) + 1)) / Real.sqrt (((N / 2 : ℕ) : ℝ) + 1) := by
            rw [mul_one_div]
    rw [hsplit, hinner]
    have hih := ih (N / 2) (Nat.div_lt_self hN (by norm_num))
    set a : ℝ := Real.sqrt (((N / 2 : ℕ) : ℝ) + 1) with ha_def
    set b : ℝ := Real.sqrt ((N : ℝ) + 1) with hb_def
    have ha0 : (0 : ℝ) < a := by
      rw [ha_def]
      positivity
    have hb0 : (0 : ℝ) < b := by
      rw [hb_def]
      positivity
    have ha2 : a ^ 2 = (N / 2 : ℕ) + 1 := by
      rw [ha_def, Real.sq_sqrt (by positivity)]
    have hb2 : b ^ 2 = (N : ℝ) + 1 := by
      rw [hb_def, Real.sq_sqrt (by positivity)]
    have hfact1 : (N : ℝ) + 1 ≤ 2 * ((N / 2 : ℕ) : ℝ) + 2 := by
      have : N + 1 ≤ 2 * (N / 2) + 2 := by omega
      exact_mod_cast this
    have hfact2 : 36 * (((N / 2 : ℕ) : ℝ) + 1) ≤ 25 * ((N : ℝ) + 1) := by
      have : 36 * (N / 2 + 1) ≤ 25 * (N + 1) := by omega
      exact_mod_cast this
    calc (∑ α ∈ normLe (N / 2), (1 : ℝ) / ‖toC α‖)
          + ∑ α ∈ (normLe N).filter (fun α => ¬ natNorm α ≤ N / 2),
              (1 : ℝ) / ‖toC α‖
        ≤ 500 * a + (50 * (N + 1) : ℝ) / a := by
          apply add_le_add hih hboundary
      _ ≤ 500 * b := by
          have h2ab : b ^ 2 ≤ 2 * a ^ 2 := by
            rw [ha2, hb2]
            linarith
          have h36 : 36 * a ^ 2 ≤ 25 * b ^ 2 := by
            rw [ha2, hb2]
            linarith
          have hsum : (0 : ℝ) < 5 * b + 6 * a := by linarith
          have h5b6a : 6 * a ≤ 5 * b := by nlinarith [h36, hsum]
          rw [← sub_nonneg]
          have key : 500 * b - (500 * a + 50 * ((N : ℝ) + 1) / a)
              = (500 * a * b - 500 * a ^ 2 - 50 * b ^ 2) / a := by
            rw [← hb2]
            field_simp
            ring
          rw [key]
          apply div_nonneg _ ha0.le
          nlinarith [mul_nonneg ha0.le (sub_nonneg.mpr h5b6a), h2ab]


/-! ## Exact vanishing on the full lattice and on `3ℤ[ω]` -/

lemma norm_omegaC : ‖omegaC‖ = 1 := by
  have h : ‖toC omega‖ = Real.sqrt ((norm omega : ℤ) : ℝ) := norm_toC omega
  rw [toC_omega] at h
  rw [h, show ((norm omega : ℤ) : ℝ) = 1 by norm_num [Eis.norm_def, omega],
    Real.sqrt_one]

lemma u_omegaC : u omegaC = omegaC := by
  unfold u
  rw [norm_omegaC]
  push_cast
  simp

lemma omegaC_pow_three : omegaC ^ 3 = 1 := by
  calc omegaC ^ 3 = omegaC * omegaC * omegaC := by ring
    _ = (-1 - omegaC) * omegaC := by rw [omegaC_sq]
    _ = -omegaC - omegaC * omegaC := by ring
    _ = -omegaC - (-1 - omegaC) := by rw [omegaC_sq]
    _ = 1 := by ring

lemma omegaC_ne_one : omegaC ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  rw [omegaC_im] at him
  simp only [Complex.one_im] at him
  nlinarith [sqrt_three_pos]

lemma omegaC_pow_ne_one {m : ℕ} (hm : ¬ (3 ∣ m)) : omegaC ^ m ≠ 1 := by
  intro h
  have hdecomp : omegaC ^ m = (omegaC ^ 3) ^ (m / 3) * omegaC ^ (m % 3) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  rw [hdecomp, omegaC_pow_three, one_pow, one_mul] at h
  have hr : m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hr with hr | hr
  · rw [hr, pow_one] at h
    exact omegaC_ne_one h
  · rw [hr, sq, omegaC_sq] at h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.neg_im, Complex.one_im, omegaC_im] at him
    nlinarith [sqrt_three_pos]

lemma natNorm_omega : natNorm omega = 1 := rfl

lemma omega_mul_omega_sq : omega * (⟨-1, -1⟩ : Eis) = 1 := by decide

lemma omega_sq_mul_omega : (⟨-1, -1⟩ : Eis) * omega = 1 := by decide

lemma natNorm_omega_sq : natNorm (⟨-1, -1⟩ : Eis) = 1 := rfl

/-- Rotation by `ω` fixes `normLe N` and multiplies `u^m` by `ω^m ≠ 1`;
hence the full-lattice angular sum vanishes. -/
theorem sum_u_pow_normLe (m : ℕ) (hm : ¬ (3 ∣ m)) (N : ℕ) :
    ∑ α ∈ normLe N, u (toC α) ^ m = 0 := by
  have homega0 : (omega : Eis) ≠ 0 := by decide
  have himg : Finset.image (fun α => omega * α) (normLe N) = normLe N := by
    ext β
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨α, hα, rfl⟩
      rw [mem_normLe] at hα ⊢
      obtain ⟨h0, hn⟩ := hα
      refine ⟨mul_ne_zero homega0 h0, ?_⟩
      rw [natNorm_mul, natNorm_omega, one_mul]
      exact hn
    · intro hβ
      rw [mem_normLe] at hβ
      obtain ⟨h0, hn⟩ := hβ
      refine ⟨(⟨-1, -1⟩ : Eis) * β, ?_, ?_⟩
      · rw [mem_normLe]
        refine ⟨mul_ne_zero (by decide) h0, ?_⟩
        rw [natNorm_mul, natNorm_omega_sq, one_mul]
        exact hn
      · rw [← mul_assoc, omega_mul_omega_sq, one_mul]
  have hinj : ∀ x ∈ normLe N, ∀ y ∈ normLe N,
      omega * x = omega * y → x = y := fun x _ y _ h =>
    mul_left_cancel₀ homega0 h
  have hrot : ∑ α ∈ normLe N, u (toC α) ^ m =
      omegaC ^ m * ∑ α ∈ normLe N, u (toC α) ^ m := by
    calc ∑ α ∈ normLe N, u (toC α) ^ m
        = ∑ β ∈ Finset.image (fun α => omega * α) (normLe N), u (toC β) ^ m := by
          rw [himg]
      _ = ∑ α ∈ normLe N, u (toC (omega * α)) ^ m := Finset.sum_image hinj
      _ = ∑ α ∈ normLe N, omegaC ^ m * u (toC α) ^ m := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [map_mul, toC_omega, u_mul, u_omegaC, mul_pow]
      _ = omegaC ^ m * ∑ α ∈ normLe N, u (toC α) ^ m := by
          rw [Finset.mul_sum]
  have hzero : (1 - omegaC ^ m) * (∑ α ∈ normLe N, u (toC α) ^ m) = 0 := by
    rw [sub_mul, one_mul, ← hrot, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (sub_eq_zero.mp h).symm (omegaC_pow_ne_one hm)
  · exact h

lemma natNorm_three : natNorm (3 : Eis) = 9 := by decide

lemma three_ne_zero' : (3 : Eis) ≠ 0 := by decide

lemma toC_three : toC (3 : Eis) = ((3 : ℝ) : ℂ) := by
  rw [show (3 : Eis) = ((3 : ℕ) : Eis) from by norm_cast]
  rw [map_natCast]
  norm_num

/-- The `3ℤ[ω]`-sum in the disk also vanishes (rescale by `3`). -/
theorem sum_u_pow_three_mul (m : ℕ) (hm : ¬ (3 ∣ m)) (N : ℕ) :
    ∑ α ∈ (normLe N).filter (fun α => (3:ℤ) ∣ α.re ∧ (3:ℤ) ∣ α.im),
      u (toC α) ^ m = 0 := by
  have himg : Finset.image (fun γ => (3 : Eis) * γ) (normLe (N / 9)) =
      (normLe N).filter (fun α => (3:ℤ) ∣ α.re ∧ (3:ℤ) ∣ α.im) := by
    ext β
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      rw [mem_normLe] at hγ
      obtain ⟨h0, hn⟩ := hγ
      refine ⟨?_, ?_, ?_⟩
      · rw [mem_normLe]
        refine ⟨mul_ne_zero three_ne_zero' h0, ?_⟩
        rw [natNorm_mul, natNorm_three]
        have hle := Nat.div_mul_le_self N 9
        omega
      · rw [Eis.mul_re, three_re, three_im]
        exact ⟨γ.re, by ring⟩
      · rw [Eis.mul_im, three_re, three_im]
        exact ⟨γ.im, by ring⟩
    · rintro ⟨hβ, h1, h2⟩
      rw [mem_normLe] at hβ
      obtain ⟨h0, hn⟩ := hβ
      obtain ⟨x, hx⟩ := h1
      obtain ⟨y, hy⟩ := h2
      have hβeq : β = (3 : Eis) * (⟨x, y⟩ : Eis) := by
        ext
        · rw [Eis.mul_re, three_re, three_im]
          simpa using hx
        · rw [Eis.mul_im, three_re, three_im]
          simpa using hy
      refine ⟨⟨x, y⟩, ?_, hβeq.symm⟩
      rw [mem_normLe]
      constructor
      · intro hxy0
        apply h0
        rw [hβeq, hxy0, mul_zero]
      · rw [hβeq, natNorm_mul, natNorm_three] at hn
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 9)]
        omega
  have hinj : ∀ x ∈ normLe (N / 9), ∀ y ∈ normLe (N / 9),
      (3 : Eis) * x = (3 : Eis) * y → x = y := fun x _ y _ h =>
    mul_left_cancel₀ three_ne_zero' h
  rw [← himg, Finset.sum_image hinj]
  have hcongr : ∀ γ, u (toC ((3 : Eis) * γ)) = u (toC γ) := by
    intro γ
    rw [map_mul, toC_three]
    exact u_smul_pos (by norm_num) (toC γ)
  calc ∑ γ ∈ normLe (N / 9), u (toC ((3 : Eis) * γ)) ^ m
      = ∑ γ ∈ normLe (N / 9), u (toC γ) ^ m :=
        Finset.sum_congr rfl fun γ _ => by rw [hcongr]
    _ = 0 := sum_u_pow_normLe m hm (N / 9)

/-! ## Main bound -/

set_option maxHeartbeats 4000000 in
/-- Square-root cancellation for the primary angular sums, explicit form. -/
theorem primary_sum_bound (m : ℕ) (hm : ¬ (3 ∣ m)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖∑ n ∈ Finset.Icc 1 N, ∑ α ∈ primaryOfNorm n, u (toC α) ^ m‖
        ≤ C * (m + 1) * Real.sqrt (N + 1) := by
  refine ⟨16000, by norm_num, fun N => ?_⟩
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  have hsq1 : (1 : ℝ) ≤ Real.sqrt (N + 1) := by
    have h0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt ((N : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  -- Step 1: flatten the double sum
  have hflat : ∑ n ∈ Finset.Icc 1 N, ∑ α ∈ primaryOfNorm n, u (toC α) ^ m
      = ∑ α ∈ (normLe N).filter (fun α => Primary α), u (toC α) ^ m := by
    rw [← Finset.sum_biUnion]
    · congr 1
      ext α
      simp only [Finset.mem_biUnion, Finset.mem_filter, mem_normLe, Finset.mem_Icc]
      constructor
      · rintro ⟨n, ⟨hn1, hn2⟩, hα⟩
        rw [mem_primaryOfNorm] at hα
        obtain ⟨hnorm, hprim⟩ := hα
        exact ⟨⟨hprim.ne_zero, hnorm ▸ hn2⟩, hprim⟩
      · rintro ⟨⟨h0, hle⟩, hprim⟩
        refine ⟨natNorm α, ⟨?_, hle⟩, ?_⟩
        · exact Nat.one_le_iff_ne_zero.mpr fun hc => h0 (natNorm_eq_zero_iff.mp hc)
        · rw [mem_primaryOfNorm]
          exact ⟨rfl, hprim⟩
    · intro x hx y hy hxy
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro α hαx hαy
      rw [mem_primaryOfNorm] at hαx hαy
      exact hxy (by rw [← hαx.1, hαy.1])
  rw [hflat]
  -- crude bound for small N
  have hcrude : ‖∑ α ∈ (normLe N).filter (fun α => Primary α), u (toC α) ^ m‖
      ≤ (((normLe N).filter (fun α => Primary α)).card : ℝ) := by
    calc ‖∑ α ∈ (normLe N).filter (fun α => Primary α), u (toC α) ^ m‖
        ≤ ∑ α ∈ (normLe N).filter (fun α => Primary α), ‖u (toC α) ^ m‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _α ∈ (normLe N).filter (fun α => Primary α), 1 := by
          refine Finset.sum_le_sum fun α _ => ?_
          rw [norm_pow]
          exact pow_le_one₀ (norm_nonneg _) (norm_u_le _)
      _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rcases le_total N 20 with hN20 | hN20
  · -- small N: card bound
    have hcard : (((normLe N).filter (fun α => Primary α)).card : ℝ) ≤ 1050 := by
      have h1 : ((normLe N).filter (fun α => Primary α)).card ≤ (normLe N).card :=
        Finset.card_filter_le _ _
      have h2 := card_normLe_le N
      have h3 : ((normLe N).filter (fun α => Primary α)).card ≤ 50 * (N + 1) :=
        le_trans h1 h2
      have h4 : 50 * (N + 1) ≤ 1050 := by omega
      exact_mod_cast le_trans h3 h4
    calc ‖∑ α ∈ (normLe N).filter (fun α => Primary α), u (toC α) ^ m‖
        ≤ 1050 := le_trans hcrude hcard
      _ ≤ 16000 * ((m : ℝ) + 1) * Real.sqrt (N + 1) := by
          nlinarith [hm1, hsq1]
  -- large N
  obtain ⟨sN, hsN⟩ : ∃ s, s = Nat.sqrt N := ⟨_, rfl⟩
  have hsN1 : 1 ≤ sN := by
    rw [hsN]
    calc 1 = Nat.sqrt 1 := Nat.sqrt_one.symm
      _ ≤ Nat.sqrt N := Nat.sqrt_le_sqrt (by omega)
  have hsN4 : 4 ≤ sN := by
    rw [hsN]
    calc 4 = Nat.sqrt 16 := by rw [show (16 : ℕ) = 4 ^ 2 from by norm_num, Nat.sqrt_eq']
      _ ≤ Nat.sqrt N := Nat.sqrt_le_sqrt (by omega)
  have hsNsq : sN * sN ≤ N := by
    rw [hsN]
    have h := Nat.sqrt_le' N
    rwa [pow_two] at h
  have hsNsq' : N < (sN + 1) * (sN + 1) := by
    rw [hsN]
    simpa [Nat.succ_eq_add_one, pow_two] using Nat.lt_succ_sqrt' N
  set N' := N + 2 * sN + 3 with hN'
  set N'' := N - (2 * sN + 3) with hN''
  have hN''1 : 1 ≤ N'' := by
    rw [hN'']
    have h1 : 2 * sN + 4 ≤ N := by nlinarith [hsNsq, hsN4]
    omega
  have hN''N : N'' ≤ N := by
    rw [hN'']
    omega
  -- trace bound: |2 re − im| ≤ 2(sN''+1)-free ; we use the N-level bound
  have htrace : ∀ α : Eis, natNorm α ≤ N → (2 * α.re - α.im) ^ 2 ≤ 4 * (N : ℤ) := by
    intro α hα
    have h4 := four_mul_norm α
    have hc := natNorm_cast α
    have h1 : (natNorm α : ℤ) ≤ N := by exact_mod_cast hα
    nlinarith [sq_nonneg α.im]
  have htrace_abs : ∀ α : Eis, natNorm α ≤ N →
      -(2 * (sN : ℤ) + 2) ≤ 2 * α.re - α.im ∧ 2 * α.re - α.im ≤ 2 * (sN : ℤ) + 2 := by
    intro α hα
    have h1 := htrace α hα
    have h2 : 4 * (N : ℤ) < (2 * (sN : ℤ) + 2) ^ 2 := by
      have := hsNsq'
      push_cast
      nlinarith [this]
    constructor <;> nlinarith [sq_nonneg (2 * α.re - α.im + (2 * (sN : ℤ) + 2)),
      sq_nonneg (2 * α.re - α.im - (2 * (sN : ℤ) + 2))]
  -- norm of a shift
  have hshift : ∀ α : Eis, norm (α - 1) = norm α - (2 * α.re - α.im) + 1 := by
    intro α
    rw [Eis.norm_def, Eis.norm_def]
    simp only [Eis.sub_re, Eis.sub_im, Eis.one_re, Eis.one_im]
    ring
  have hshift' : ∀ β : Eis, norm (1 + β) = norm β + (2 * β.re - β.im) + 1 := by
    intro β
    rw [Eis.norm_def, Eis.norm_def]
    simp only [Eis.add_re, Eis.add_im, Eis.one_re, Eis.one_im]
    ring
  -- the primary set and its translate
  set P := (normLe N).filter (fun α => Primary α) with hP
  set Q := P.image (fun α => α - 1) with hQ
  have hQmem : ∀ β : Eis, β ∈ Q ↔ (1 + β) ∈ P := by
    intro β
    rw [hQ, Finset.mem_image]
    constructor
    · rintro ⟨α, hα, rfl⟩
      have : 1 + (α - 1) = α := by ring
      rw [this]
      exact hα
    · intro h
      exact ⟨1 + β, h, by ring⟩
  have hsum_translate : ∑ α ∈ P, u (toC α) ^ m = ∑ β ∈ Q, u (toC (1 + β)) ^ m := by
    rw [hQ, Finset.sum_image]
    · refine Finset.sum_congr rfl fun α _ => ?_
      congr 2
      ring
    · intro α _ α' _ h
      have h' : α - 1 = α' - 1 := h
      have h2 : α - 1 + 1 = α' - 1 + 1 := by rw [h']
      simpa using h2
  -- 0 ∈ Q and the zero term
  have h0Q : (0 : Eis) ∈ Q := by
    rw [hQmem]
    rw [hP, Finset.mem_filter, mem_normLe]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp
    · simpa using (by omega : 1 ≤ N)
    · simpa using primary_one
  have hu1 : u (toC (1 + 0)) ^ m = 1 := by
    have h1 : toC (1 + 0) = 1 := by
      rw [add_zero, map_one]
    rw [h1]
    have h2 : u 1 = 1 := by
      unfold u
      simp
    rw [h2, one_pow]
  set Q0 := Q.erase 0 with hQ0
  have hQsplit : ∑ β ∈ Q, u (toC (1 + β)) ^ m
      = 1 + ∑ β ∈ Q0, u (toC (1 + β)) ^ m := by
    rw [hQ0, ← Finset.add_sum_erase _ _ h0Q, hu1]
  -- membership facts for Q0
  have hQ0mem : ∀ β ∈ Q0, β ≠ 0 ∧ (3 : ℤ) ∣ β.re ∧ (3 : ℤ) ∣ β.im ∧
      natNorm (1 + β) ≤ N ∧ (1 + β) ≠ 0 := by
    intro β hβ
    rw [hQ0, Finset.mem_erase] at hβ
    obtain ⟨hβ0, hβQ⟩ := hβ
    rw [hQmem, hP, Finset.mem_filter, mem_normLe] at hβQ
    obtain ⟨⟨h1, h2⟩, h3⟩ := hβQ
    obtain ⟨hp1, hp2⟩ := h3
    refine ⟨hβ0, ?_, ?_, h2, h1⟩
    · have : (1 + β).re - 1 = β.re := by
        simp only [Eis.add_re, Eis.one_re]
        ring
      rwa [this] at hp1
    · have : (1 + β).im = β.im := by
        simp only [Eis.add_im, Eis.one_im]
        ring
      rwa [this] at hp2
  -- Q0 sits inside the N'-disk of the 3-sublattice
  have hQ0sub : ∀ β ∈ Q0, β ∈ (normLe N').filter
      (fun β => (3 : ℤ) ∣ β.re ∧ (3 : ℤ) ∣ β.im) := by
    intro β hβ
    obtain ⟨hβ0, hd1, hd2, hle, hne⟩ := hQ0mem β hβ
    rw [Finset.mem_filter, mem_normLe]
    refine ⟨⟨hβ0, ?_⟩, hd1, hd2⟩
    -- natNorm β ≤ N'
    have hα := hshift (1 + β)
    have : (1 + β) - 1 = β := by ring
    rw [this] at hα
    have htr := htrace_abs (1 + β) hle
    have hc1 := natNorm_cast β
    have hc2 := natNorm_cast (1 + β)
    have h1 : (natNorm (1 + β) : ℤ) ≤ N := by exact_mod_cast hle
    have h2 : (natNorm β : ℤ) ≤ N + 2 * sN + 3 := by
      rw [hc1, hα]
      omega
    have h3 : ((N' : ℕ) : ℤ) = (N : ℤ) + 2 * sN + 3 := by
      rw [hN']
      push_cast
      ring
    have h4 : (natNorm β : ℤ) ≤ ((N' : ℕ) : ℤ) := by
      rw [h3]
      exact h2
    exact_mod_cast h4
  -- the inner sublattice disk sits inside Q0
  have hSsub : ∀ β ∈ (normLe N'').filter
      (fun β => (3 : ℤ) ∣ β.re ∧ (3 : ℤ) ∣ β.im), β ∈ Q0 := by
    intro β hβ
    rw [Finset.mem_filter, mem_normLe] at hβ
    obtain ⟨⟨hβ0, hle⟩, hd1, hd2⟩ := hβ
    rw [hQ0, Finset.mem_erase]
    refine ⟨hβ0, ?_⟩
    rw [hQmem, hP, Finset.mem_filter, mem_normLe]
    have hne : (1 : Eis) + β ≠ 0 := by
      intro hc
      have h1 : β.re = -1 := by
        have := congrArg Eis.re hc
        simp only [Eis.add_re, Eis.one_re, Eis.zero_re] at this
        omega
      rw [h1] at hd1
      omega
    refine ⟨⟨hne, ?_⟩, ?_, ?_⟩
    · -- natNorm (1+β) ≤ N
      have hβN : natNorm β ≤ N := le_trans hle hN''N
      have htr := htrace_abs β hβN
      have hα := hshift' β
      have hc1 := natNorm_cast β
      have hc2 := natNorm_cast (1 + β)
      have h1 : (natNorm β : ℤ) ≤ N'' := by exact_mod_cast hle
      have h2 : ((N'' : ℕ) : ℤ) = (N : ℤ) - (2 * sN + 3) := by
        rw [hN'']
        have : 2 * sN + 3 ≤ N := by nlinarith [hsNsq, hsN4]
        push_cast [Nat.cast_sub this]
        ring
      have h3 : (natNorm (1 + β) : ℤ) ≤ N := by
        rw [hc2, hα]
        omega
      exact_mod_cast h3
    · simp only [Eis.add_re, Eis.one_re]
      have : (1 : ℤ) + β.re - 1 = β.re := by ring
      rw [this]
      exact hd1
    · simp only [Eis.add_im, Eis.one_im]
      have : (0 : ℤ) + β.im = β.im := by ring
      rw [this]
      exact hd2
  -- Lipschitz part
  have hLip : ‖∑ β ∈ Q0, (u (toC (1 + β)) ^ m - u (toC β) ^ m)‖
      ≤ 2 * m * (500 * Real.sqrt (N' + 1)) := by
    calc ‖∑ β ∈ Q0, (u (toC (1 + β)) ^ m - u (toC β) ^ m)‖
        ≤ ∑ β ∈ Q0, ‖u (toC (1 + β)) ^ m - u (toC β) ^ m‖ := norm_sum_le _ _
      _ ≤ ∑ β ∈ Q0, 2 * m * (1 / ‖toC β‖) := by
          refine Finset.sum_le_sum fun β hβ => ?_
          obtain ⟨hβ0, -, -, -, hne⟩ := hQ0mem β hβ
          have htβ : toC β ≠ 0 := fun hc => hβ0 (toC_injective (by simpa using hc))
          have htβ1 : toC (1 + β) ≠ 0 := fun hc => hne (toC_injective (by simpa using hc))
          have hu1' : ‖u (toC (1 + β))‖ = 1 := abs_u htβ1
          have hu2' : ‖u (toC β)‖ = 1 := abs_u htβ
          calc ‖u (toC (1 + β)) ^ m - u (toC β) ^ m‖
              ≤ m * ‖u (toC (1 + β)) - u (toC β)‖ :=
                pow_sub_pow_norm_le hu1' hu2' m
            _ ≤ m * (2 * ‖toC β - toC (1 + β)‖ / ‖toC β‖) := by
                apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
                rw [norm_sub_rev]
                exact u_sub_u_norm_le htβ htβ1
            _ = 2 * m * (1 / ‖toC β‖) := by
                have hdiff : toC β - toC (1 + β) = -1 := by
                  rw [map_add, map_one]
                  ring
                have hn1 : ‖(-1 : ℂ)‖ = 1 := by simp
                rw [hdiff, hn1]
                ring
      _ = 2 * m * ∑ β ∈ Q0, (1 / ‖toC β‖) := by
          rw [Finset.mul_sum]
      _ ≤ 2 * m * (500 * Real.sqrt (N' + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc ∑ β ∈ Q0, (1 : ℝ) / ‖toC β‖
              ≤ ∑ β ∈ normLe N', (1 : ℝ) / ‖toC β‖ := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro β hβ
                  have := hQ0sub β hβ
                  rw [Finset.mem_filter] at this
                  exact this.1
                · intro β _ _
                  positivity
            _ ≤ 500 * Real.sqrt (N' + 1) := sum_inv_abs_le N'
  -- main part via the sublattice vanishing and the annulus
  have hmain : ‖∑ β ∈ Q0, u (toC β) ^ m‖ ≤ 3000 * (Nat.sqrt N' + 1) := by
    set S'' := (normLe N'').filter (fun β => (3 : ℤ) ∣ β.re ∧ (3 : ℤ) ∣ β.im) with hS''
    have hsubQ : S'' ⊆ Q0 := fun β hβ => hSsub β hβ
    have hzero := sum_u_pow_three_mul m hm N''
    rw [← hS''] at hzero
    have hsplit2 : ∑ β ∈ Q0, u (toC β) ^ m
        = (∑ β ∈ Q0 \ S'', u (toC β) ^ m) + ∑ β ∈ S'', u (toC β) ^ m :=
      (Finset.sum_sdiff hsubQ).symm
    rw [hsplit2, hzero, add_zero]
    calc ‖∑ β ∈ Q0 \ S'', u (toC β) ^ m‖
        ≤ ∑ β ∈ Q0 \ S'', ‖u (toC β) ^ m‖ := norm_sum_le _ _
      _ ≤ ∑ _β ∈ Q0 \ S'', 1 := by
          refine Finset.sum_le_sum fun β _ => ?_
          rw [norm_pow]
          exact pow_le_one₀ (norm_nonneg _) (norm_u_le _)
      _ = ((Q0 \ S'').card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ 3000 * (Nat.sqrt N' + 1) := by
          have hsubAnn : Q0 \ S'' ⊆ (normLe N').filter (fun α => N'' < natNorm α) := by
            intro β hβ
            rw [Finset.mem_sdiff] at hβ
            obtain ⟨hβQ, hβS⟩ := hβ
            have h1 := hQ0sub β hβQ
            rw [Finset.mem_filter] at h1
            rw [Finset.mem_filter]
            refine ⟨h1.1, ?_⟩
            by_contra hcon
            push_neg at hcon
            apply hβS
            rw [hS'', Finset.mem_filter, mem_normLe]
            rw [mem_normLe] at h1
            exact ⟨⟨h1.1.1, hcon⟩, h1.2⟩
          have hUV' : N'' ≤ N' := le_trans hN''N (by rw [hN']; omega)
          have hthin' : N' ≤ N'' + 5 * Nat.sqrt N' + 5 := by
            have h1 : sN ≤ Nat.sqrt N' := by
              rw [hsN]
              exact Nat.sqrt_le_sqrt (by rw [hN']; omega)
            have h2 : 2 * sN + 3 ≤ N := by nlinarith [hsNsq, hsN4]
            have h3 : N' = N + 2 * sN + 3 := hN'
            have h4 : N'' = N - (2 * sN + 3) := hN''
            omega
          have hann := card_annulus_le N'' N' hUV' hN''1 hthin'
          calc ((Q0 \ S'').card : ℝ)
              ≤ (((normLe N').filter (fun α => N'' < natNorm α)).card : ℝ) := by
                exact_mod_cast Finset.card_le_card hsubAnn
            _ ≤ 3000 * (Nat.sqrt N' + 1) := by
                exact_mod_cast hann
  -- put the pieces together
  have hdecomp : ∑ β ∈ Q0, u (toC (1 + β)) ^ m
      = (∑ β ∈ Q0, (u (toC (1 + β)) ^ m - u (toC β) ^ m))
        + ∑ β ∈ Q0, u (toC β) ^ m := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  -- the √-comparisons
  have hsqrtN' : Real.sqrt ((N' : ℝ) + 1) ≤ 3 * Real.sqrt (N + 1) := by
    have h1 : ((N' : ℝ)) + 1 ≤ 9 * ((N : ℝ) + 1) := by
      rw [hN']
      push_cast
      have h2 : (sN : ℝ) ≤ N := by
        have h3 : sN ≤ N := by
          calc sN = sN * 1 := (mul_one sN).symm
            _ ≤ sN * sN := Nat.mul_le_mul_left sN hsN1
            _ ≤ N := hsNsq
        exact_mod_cast h3
      linarith
    calc Real.sqrt ((N' : ℝ) + 1) ≤ Real.sqrt (9 * ((N : ℝ) + 1)) :=
          Real.sqrt_le_sqrt h1
      _ = 3 * Real.sqrt (N + 1) := by
          rw [show (9 : ℝ) * ((N : ℝ) + 1) = 3 ^ 2 * ((N : ℝ) + 1) from by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
  have hsqrtN'nat : ((Nat.sqrt N' : ℝ)) + 1 ≤ 3 * Real.sqrt (N + 1) + 1 := by
    have h1 : ((Nat.sqrt N' : ℝ)) ≤ Real.sqrt N' := by
      have h := Nat.sqrt_le' N'
      have h2 : ((Nat.sqrt N' : ℝ)) ^ 2 ≤ ((N' : ℕ) : ℝ) := by
        rw [pow_two] at h ⊢
        exact_mod_cast h
      calc ((Nat.sqrt N' : ℝ)) = Real.sqrt (((Nat.sqrt N' : ℝ)) ^ 2) :=
            (Real.sqrt_sq (Nat.cast_nonneg _)).symm
        _ ≤ Real.sqrt N' := Real.sqrt_le_sqrt h2
    have h2 : Real.sqrt ((N' : ℝ)) ≤ Real.sqrt ((N' : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    linarith [hsqrtN']
  -- final triangle inequality
  calc ‖∑ α ∈ P, u (toC α) ^ m‖
      = ‖(1 : ℂ) + ((∑ β ∈ Q0, (u (toC (1 + β)) ^ m - u (toC β) ^ m))
          + ∑ β ∈ Q0, u (toC β) ^ m)‖ := by
        rw [hsum_translate, hQsplit, hdecomp]
    _ ≤ 1 + (‖∑ β ∈ Q0, (u (toC (1 + β)) ^ m - u (toC β) ^ m)‖
          + ‖∑ β ∈ Q0, u (toC β) ^ m‖) := by
        have ht1 := norm_add_le (1 : ℂ)
          ((∑ β ∈ Q0, (u (toC (1 + β)) ^ m - u (toC β) ^ m))
            + ∑ β ∈ Q0, u (toC β) ^ m)
        have ht2 := norm_add_le (∑ β ∈ Q0, (u (toC (1 + β)) ^ m - u (toC β) ^ m))
          (∑ β ∈ Q0, u (toC β) ^ m)
        have hn1 : ‖(1 : ℂ)‖ = 1 := by simp
        linarith [ht1, ht2]
    _ ≤ 1 + (2 * m * (500 * Real.sqrt (N' + 1)) + 3000 * (Nat.sqrt N' + 1)) := by
        have h := add_le_add hLip hmain
        linarith [h]
    _ ≤ 16000 * ((m : ℝ) + 1) * Real.sqrt (N + 1) := by
        have h1 : Real.sqrt ((N' : ℝ) + 1) ≤ 3 * Real.sqrt (N + 1) := hsqrtN'
        have h2 : ((Nat.sqrt N' : ℝ)) + 1 ≤ 3 * Real.sqrt (N + 1) + 1 := hsqrtN'nat
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith [hm1, hsq1, h1, h2, hm0,
          mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * (m : ℝ) * 500)]

/-- Square-root cancellation, `IsBigO` form matching `PartialSumBigO`. -/
theorem primary_sum_isBigO (m : ℕ) (hm : ¬ (3 ∣ m)) :
    (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ∑ α ∈ primaryOfNorm n, u (toC α) ^ m)
      =O[atTop] (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2)) := by
  obtain ⟨C, hC, hbound⟩ := primary_sum_bound m hm
  rw [Asymptotics.isBigO_iff]
  refine ⟨C * (m + 1) * 2, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have h := hbound N
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsqrt : Real.sqrt (N + 1) ≤ 2 * (N : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt ((N : ℝ) + 1) ≤ Real.sqrt (4 * N) := by
          apply Real.sqrt_le_sqrt
          linarith
      _ = 2 * Real.sqrt N := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
          congr 1
          rw [show (4 : ℝ) = 2 ^ 2 from by norm_num,
            Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  calc ‖∑ n ∈ Finset.Icc 1 N, ∑ α ∈ primaryOfNorm n, u (toC α) ^ m‖
      ≤ C * (m + 1) * Real.sqrt (N + 1) := h
    _ ≤ C * (m + 1) * (2 * (N : ℝ) ^ ((1 : ℝ) / 2)) := by
        apply mul_le_mul_of_nonneg_left hsqrt
        positivity
    _ = C * (m + 1) * 2 * (N : ℝ) ^ ((1 : ℝ) / 2) := by ring
    _ ≤ C * (m + 1) * 2 * ‖(N : ℝ) ^ ((1 : ℝ) / 2)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- Linear growth of the primary counting function (for summability). -/
theorem primary_count_isBigO :
    (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ((primaryOfNorm n).card : ℝ))
      =O[atTop] (fun N : ℕ => (N : ℝ)) := by
  have hbound : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, (primaryOfNorm n).card ≤ 50 * (N + 1) := by
    intro N
    have hdisj : ((Finset.Icc 1 N).biUnion (fun n => primaryOfNorm n)).card =
        ∑ n ∈ Finset.Icc 1 N, (primaryOfNorm n).card := by
      apply Finset.card_biUnion
      intro x hx y hy hxy
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro α hαx hαy
      rw [mem_primaryOfNorm] at hαx hαy
      exact hxy (by rw [← hαx.1, hαy.1])
    rw [← hdisj]
    calc ((Finset.Icc 1 N).biUnion (fun n => primaryOfNorm n)).card
        ≤ (normLe N).card := by
          apply Finset.card_le_card
          intro α hα
          rw [Finset.mem_biUnion] at hα
          obtain ⟨n, hn, hαn⟩ := hα
          rw [mem_primaryOfNorm] at hαn
          rw [Finset.mem_Icc] at hn
          rw [mem_normLe]
          exact ⟨hαn.2.ne_zero, hαn.1 ▸ hn.2⟩
      _ ≤ 50 * (N + 1) := card_normLe_le N
  rw [Asymptotics.isBigO_iff]
  refine ⟨100, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have h := hbound N
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsum_nonneg : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, ((primaryOfNorm n).card : ℝ) :=
    Finset.sum_nonneg fun n _ => by positivity
  have hcast : (∑ n ∈ Finset.Icc 1 N, ((primaryOfNorm n).card : ℝ)) =
      ((∑ n ∈ Finset.Icc 1 N, (primaryOfNorm n).card : ℕ) : ℝ) := by
    push_cast
    rfl
  rw [Real.norm_eq_abs, abs_of_nonneg hsum_nonneg, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (N:ℝ)), hcast]
  calc ((∑ n ∈ Finset.Icc 1 N, (primaryOfNorm n).card : ℕ) : ℝ)
      ≤ ((50 * (N + 1) : ℕ) : ℝ) := by exact_mod_cast h
    _ = 50 * (N : ℝ) + 50 := by push_cast; ring
    _ ≤ 100 * (N : ℝ) := by linarith

end

end K3Lean.PrimaryDiskBound
