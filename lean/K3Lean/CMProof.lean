import K3Lean.Expanded
import K3Lean.PublishedInputs
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient

/-!
# Erdős #979, k = 3: the CM/block proof after the analytic input

This file removes the old conclusion-shaped hypothesis `h_glue`.

The published CM Sato--Tate and Brun--Titchmarsh statements live in
`K3Lean.PublishedInputs`.  This file defines the stronger, problem-specific
finite corollaries needed by the block argument; their derivation from the
published statements is still a proof obligation.  Everything after those
finite corollaries is proved here:

* all selected sums lie among the multiples of the block modulus in `[0, 3X^3]`;
* the number of those possible values is exactly `3X^3 / a + 1`;
* the prime-triple lower bound and the CM growth inequality imply that there are
  at least `B` times as many triples as possible values;
* Mathlib's finite pigeonhole theorem produces one value with at least `B`
  distinct sorted prime-cube representations;
* those representations are counted by the explicit function `f₃`.

The finite certificate is not itself a published theorem.  The explicit goal
`PublishedInputReductionGoal` records the remaining analytic and arithmetic
work without hiding it inside the final conclusion.
-/

namespace K3Lean.CMProof

open K3Lean.Expanded
open K3Lean.PublishedInputs
open scoped BigOperators

abbrev Triple := Nat × Nat × Nat

/-- The integer represented by a triple of cubes. -/
def cubeSum (t : Triple) : Nat :=
  t.1 ^ 3 + t.2.1 ^ 3 + t.2.2 ^ 3

/-- The part of `GoodCubeTriple` independent of the represented integer. -/
def SortedPrimeTriple (t : Triple) : Prop :=
  t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
  Nat.Prime t.1 ∧ Nat.Prime t.2.1 ∧ Nat.Prime t.2.2

instance decSortedPrimeTriple : DecidablePred SortedPrimeTriple := by
  intro t
  unfold SortedPrimeTriple
  infer_instance

theorem goodCubeTriple_iff (n : Nat) (t : Triple) :
    GoodCubeTriple n t ↔ SortedPrimeTriple t ∧ cubeSum t = n := by
  simp [GoodCubeTriple, SortedPrimeTriple, cubeSum, and_assoc]

/-- Multiples of `a` in the closed interval `[0, N]`. -/
def multiplesUpTo (a N : Nat) : Finset Nat :=
  (Finset.range N.succ).filter (fun n => a ∣ n)

theorem mem_multiplesUpTo_iff {a N n : Nat} :
    n ∈ multiplesUpTo a N ↔ n ≤ N ∧ a ∣ n := by
  simp [multiplesUpTo]

/-- There are exactly `N / a + 1` multiples of a positive `a` in `[0, N]`. -/
theorem card_multiplesUpTo {a N : Nat} :
    (multiplesUpTo a N).card = N / a + 1 := by
  let positiveMultiples : Finset Nat :=
    (Finset.range N.succ).filter (fun n => n ≠ 0 ∧ a ∣ n)
  have hdecomp : multiplesUpTo a N = insert 0 positiveMultiples := by
    ext n
    by_cases hn : n = 0
    · subst n
      simp [multiplesUpTo, positiveMultiples]
    · simp [multiplesUpTo, positiveMultiples, hn]
  have hzero : 0 ∉ positiveMultiples := by
    simp [positiveMultiples]
  rw [hdecomp, Finset.card_insert_of_notMem hzero]
  simp only [positiveMultiples, Nat.card_multiples']

/-- A sorted prime triple with all bases at most `X` has cube sum at most `3X^3`. -/
theorem cubeSum_le_three_mul_cube {X : Nat} {t : Triple}
    (hbound : t.1 ≤ X ∧ t.2.1 ≤ X ∧ t.2.2 ≤ X) :
    cubeSum t ≤ 3 * X ^ 3 := by
  have h1 : t.1 ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left hbound.1 3
  have h2 : t.2.1 ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left hbound.2.1 3
  have h3 : t.2.2 ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left hbound.2.2 3
  unfold cubeSum
  omega

/-- Reduced residue representatives in `[0, a)`. -/
def unitResidues (a : Nat) : Finset Nat :=
  (Finset.range a).filter (fun r => a.Coprime r)

/-- The literal finite set counted by `R_a` in the paper proof. -/
def localCubeSolutions (a : Nat) : Finset Triple :=
  ((unitResidues a) ×ˢ (unitResidues a) ×ˢ (unitResidues a)).filter
    (fun t => a ∣ cubeSum t)

/-- Sorted prime triples below `X` whose cube sum is `0 mod a`. -/
def blockPrimeTriples (a X : Nat) : Finset Triple :=
  (box X).filter (fun t => SortedPrimeTriple t ∧ a ∣ cubeSum t)

theorem mem_blockPrimeTriples_iff {a X : Nat} {t : Triple} :
    t ∈ blockPrimeTriples a X ↔
      SortedPrimeTriple t ∧ a ∣ cubeSum t ∧
      t.1 ≤ X ∧ t.2.1 ≤ X ∧ t.2.2 ≤ X := by
  rw [blockPrimeTriples, Finset.mem_filter]
  constructor
  · rintro ⟨htbox, hsorted, hmod⟩
    simp only [box, Finset.mem_product, Finset.mem_range] at htbox
    exact ⟨hsorted, hmod,
      Nat.le_of_lt_succ htbox.1,
      Nat.le_of_lt_succ htbox.2.1,
      Nat.le_of_lt_succ htbox.2.2⟩
  · rintro ⟨hsorted, hmod, h1, h2, h3⟩
    refine ⟨?_, hsorted, hmod⟩
    simp only [box, Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le h1, Nat.lt_succ_of_le h2, Nat.lt_succ_of_le h3⟩

/-!
## The finite output required from the analytic CM/block argument

In the paper proof:

* `modulus` is the selected block `a`;
* `primesPerClass` is the lower bound `g` for primes in every good class;
* `localCubeSolutions modulus` is the literal finite set counted by `R_a`;
* `blockPrimeTriples modulus cutoff` is the literal finite set of lifted,
  **sorted** prime triples. Passing from the ordered count in the paper proof
  to this set costs at most a factor `6`; that factor is included in the two
  quantitative inequalities;
* `growth` is the inequality obtained from
  `Λ(a) / (log X)^3 → ∞` after choosing the analytic parameter large enough.
-/

structure CMBlockCertificate (B : Nat) where
  modulus : Nat
  cutoff : Nat
  primesPerClass : Nat
  modulus_pos : 0 < modulus
  lifted_count :
    (localCubeSolutions modulus).card * primesPerClass ^ 3 ≤
      (blockPrimeTriples modulus cutoff).card
  growth :
    ((3 * cutoff ^ 3) / modulus + 1) * B ≤
      (localCubeSolutions modulus).card * primesPerClass ^ 3

namespace CMBlockCertificate

/-- The actual lifted prime triples associated with a certificate. -/
def triples {B : Nat} (C : CMBlockCertificate B) : Finset Triple :=
  blockPrimeTriples C.modulus C.cutoff

/-- The possible represented values left after imposing the block congruence. -/
def values {B : Nat} (C : CMBlockCertificate B) : Finset Nat :=
  multiplesUpTo C.modulus (3 * C.cutoff ^ 3)

theorem values_card {B : Nat} (C : CMBlockCertificate B) :
    C.values.card = (3 * C.cutoff ^ 3) / C.modulus + 1 := by
  exact card_multiplesUpTo

theorem cubeSum_mem_values {B : Nat} (C : CMBlockCertificate B)
    {t : Triple} (ht : t ∈ C.triples) : cubeSum t ∈ C.values := by
  have ht' := mem_blockPrimeTriples_iff.mp ht
  rw [values, mem_multiplesUpTo_iff]
  exact ⟨cubeSum_le_three_mul_cube ⟨ht'.2.2.1, ht'.2.2.2.1, ht'.2.2.2.2⟩,
    ht'.2.1⟩

theorem values_nonempty {B : Nat} (C : CMBlockCertificate B) : C.values.Nonempty := by
  refine ⟨0, ?_⟩
  simp [values, multiplesUpTo]

theorem enough_triples {B : Nat} (C : CMBlockCertificate B) :
    C.values.card * B ≤ C.triples.card := by
  rw [C.values_card]
  exact C.growth.trans C.lifted_count

/-- The fully formal finite pigeonhole step of the CM/block proof. -/
theorem exists_large_cube_sum_fiber {B : Nat} (C : CMBlockCertificate B) :
    ∃ n ∈ C.values,
      B ≤ (C.triples.filter (fun t => cubeSum t = n)).card := by
  exact Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (fun t ht => C.cubeSum_mem_values ht)
    C.values_nonempty
    C.enough_triples

/-- A certificate produces an integer counted at least `B` times by the explicit `f₃`. -/
theorem exists_le_f₃ {B : Nat} (C : CMBlockCertificate B) :
    ∃ n : Nat, B ≤ f₃ n := by
  obtain ⟨n, _hn, hfiber⟩ := C.exists_large_cube_sum_fiber
  let S : Finset Triple := C.triples.filter (fun t => cubeSum t = n)
  have hgood : ∀ t ∈ S, GoodCubeTriple n t := by
    intro t ht
    have ht' : t ∈ C.triples ∧ cubeSum t = n := by
      simpa [S] using ht
    have htblock := mem_blockPrimeTriples_iff.mp ht'.1
    rw [goodCubeTriple_iff]
    exact ⟨htblock.1, ht'.2⟩
  refine ⟨n, hfiber.trans ?_⟩
  exact card_le_f₃ n S hgood

end CMBlockCertificate

/-!
## Problem-specific finite corollaries still to be derived

These are not the published external theorems.  They are the finite,
problem-specific consequences that the current combinatorial proof consumes.
The actual published statements are `PublishedCMSatoTate` and
`PublishedBrunTitchmarsh` in `K3Lean.PublishedInputs`.

* `CMHeckeAmplificationCorollary` supplies a modulus/scale for which the CM local-solution
  count beats the number of possible represented values by the requested factor.
  This is the finite arithmetic corollary of Hecke equidistribution for the
  `j = 0` CM Fermat cubic (including the standard block partition and eventual
  growth comparison).
* `BrunTitchmarshPrimeLiftingCorollary` supplies the prime-lifting lower bound for those same
  parameters.  It is the finite fixed-block corollary of Brun--Titchmarsh; the
  lower bound for the total number of primes may be taken from Mathlib's
  Chebyshev theorem, so PNT is not a third external input.

All subsequent construction is checked by Lean.
-/

/-- The actual finite set of primes at most `X`. -/
def primeBasesUpTo (X : Nat) : Finset Nat :=
  (Finset.range X.succ).filter Nat.Prime

/--
The prime-per-class threshold used by the fixed-block argument.  The constant
`8` leaves room for the light-class union bound and for the ordered/sorted loss.
-/
def primeClassTarget (blocks : Finset Nat) (X a : Nat) : Nat :=
  (primeBasesUpTo X).card / (8 * blocks.card * a.totient)

/--
A finite family of pairwise-coprime CM-amplified candidate blocks.  Every block
already satisfies the growth inequality; Brun--Titchmarsh only has to select one
whose reduced residue classes contain enough primes.
-/
structure CMHeckeFamily (B : Nat) where
  blocks : Finset Nat
  cutoff : Nat
  blocks_nonempty : blocks.Nonempty
  enough_blocks : 8 ≤ blocks.card
  modulus_gt_one : ∀ a ∈ blocks, 1 < a
  pairwise_coprime :
    ∀ a ∈ blocks, ∀ b ∈ blocks, a ≠ b → a.Coprime b
  cutoff_eq : cutoff = (blocks.prod id) ^ 2
  growth : ∀ a ∈ blocks,
    ((3 * cutoff ^ 3) / a + 1) * B ≤
      (localCubeSolutions a).card *
        (primeClassTarget blocks cutoff a) ^ 3

/-- Problem-specific finite corollary expected from CM Sato--Tate. -/
def CMHeckeAmplificationCorollary : Prop :=
  ∀ B : Nat, Nonempty (CMHeckeFamily B)

/-- Problem-specific finite corollary expected from Brun--Titchmarsh. -/
def BrunTitchmarshPrimeLiftingCorollary : Prop :=
  ∀ {B : Nat} (F : CMHeckeFamily B),
    ∃ a ∈ F.blocks,
      (localCubeSolutions a).card *
          (primeClassTarget F.blocks F.cutoff a) ^ 3 ≤
        (blockPrimeTriples a F.cutoff).card

/-- The two analytic inputs assemble into the concrete finite certificate. -/
def CMHeckeFamily.toBlockCertificate {B : Nat}
    (F : CMHeckeFamily B) (a : Nat) (ha : a ∈ F.blocks)
    (h_lift :
      (localCubeSolutions a).card *
          (primeClassTarget F.blocks F.cutoff a) ^ 3 ≤
        (blockPrimeTriples a F.cutoff).card) :
    CMBlockCertificate B where
  modulus := a
  cutoff := F.cutoff
  primesPerClass := primeClassTarget F.blocks F.cutoff a
  modulus_pos := Nat.zero_lt_of_lt (F.modulus_gt_one a ha)
  lifted_count := h_lift
  growth := F.growth a ha

def CMBlockPrimeInput : Prop :=
  ∀ B : Nat, Nonempty (CMBlockCertificate B)

theorem cmBlockPrimeInput_of_finite_corollaries
    (h_cm : CMHeckeAmplificationCorollary)
    (h_brun : BrunTitchmarshPrimeLiftingCorollary) :
    CMBlockPrimeInput := by
  intro B
  obtain ⟨F⟩ := h_cm B
  obtain ⟨a, ha, h_lift⟩ := h_brun F
  exact ⟨F.toBlockCertificate a ha h_lift⟩

theorem f₃_infinite_from_cm_blocks
    (h_cm_blocks : CMBlockPrimeInput) :
    ∀ B : Nat, ∃ n : Nat, B ≤ f₃ n := by
  intro B
  obtain ⟨C⟩ := h_cm_blocks B
  exact C.exists_le_f₃

/-- Unboundedness from the two problem-specific finite corollaries. -/
theorem f₃_infinite_from_finite_corollaries
    (h_cm : CMHeckeAmplificationCorollary)
    (h_brun : BrunTitchmarshPrimeLiftingCorollary) :
    ∀ B : Nat, ∃ n : Nat, B ≤ f₃ n := by
  exact f₃_infinite_from_cm_blocks
    (cmBlockPrimeInput_of_finite_corollaries h_cm h_brun)

/--
The unproved conversion that must replace the old opaque input boundary.
This is a goal, not an axiom and not a theorem asserted by this project.
-/
def PublishedInputReductionGoal : Prop :=
  PublishedCMSatoTate →
    PublishedBrunTitchmarsh →
      CMHeckeAmplificationCorollary ∧
        BrunTitchmarshPrimeLiftingCorollary

/-- The desired final statement with only the two published inputs. -/
def Erdos979K3FromPublishedInputsGoal : Prop :=
  PublishedCMSatoTate →
    PublishedBrunTitchmarsh →
      (let f : Nat → Nat := fun n =>
        (((Finset.range (n + 1)) ×ˢ
            (Finset.range (n + 1)) ×ˢ
            (Finset.range (n + 1))).filter (fun t =>
          t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
          Nat.Prime t.1 ∧ Nat.Prime t.2.1 ∧ Nat.Prime t.2.2 ∧
          t.1 ^ 3 + t.2.1 ^ 3 + t.2.2 ^ 3 = n)).card
       ∀ B N : Nat, ∃ n : Nat, N ≤ n ∧ B ≤ f n)

/--
For a natural-valued sequence, unboundedness implies arbitrarily large values
after every starting index.  This is the elementary quantifier form of
`limsup g n = ∞` used in the final statement.
-/
theorem nat_limsup_eq_infinity_of_unbounded {g : Nat → Nat}
    (h : ∀ B : Nat, ∃ n : Nat, B ≤ g n) :
    ∀ B N : Nat, ∃ n : Nat, N ≤ n ∧ B ≤ g n := by
  intro B N
  obtain ⟨n, hn⟩ := h (B + (∑ i ∈ Finset.range N, g i) + 1)
  refine ⟨n, ?_, by omega⟩
  by_contra hnN
  have hnlt : n < N := Nat.lt_of_not_ge hnN
  have hterm : g n ≤ ∑ i ∈ Finset.range N, g i :=
    Finset.single_le_sum
      (fun i _hi => Nat.zero_le (g i))
      (Finset.mem_range.mpr hnlt)
  omega

/--
Erdős Problem #979 for `k = 3`, in a directly auditable form.

The local function `f` is written out in the theorem statement: it counts
unordered (sorted) triples of primes whose cubes sum to `n`.  The conclusion
`∀ B N, ∃ n ≥ N, B ≤ f n` is the natural-number formulation of
`limsup f(n) = ∞`.
-/
theorem erdos_979_k3_from_finite_corollaries
    (h_cm_amplification : CMHeckeAmplificationCorollary)
    (h_prime_lifting : BrunTitchmarshPrimeLiftingCorollary) :
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
    (f₃_infinite_from_finite_corollaries h_cm_amplification h_prime_lifting)

/-- Proving the displayed reduction goal would close the desired published-input goal. -/
theorem published_reduction_would_close_erdos_979_k3
    (h_reduction : PublishedInputReductionGoal) :
    Erdos979K3FromPublishedInputsGoal := by
  intro h_cm_sato_tate h_brun_titchmarsh
  obtain ⟨h_cm_amplification, h_prime_lifting⟩ :=
    h_reduction h_cm_sato_tate h_brun_titchmarsh
  exact erdos_979_k3_from_finite_corollaries
    h_cm_amplification h_prime_lifting

/-! ## Audit -/

#check @CMBlockCertificate
#check @CMBlockCertificate.exists_large_cube_sum_fiber
#check @CMBlockCertificate.exists_le_f₃
#check @PublishedCMSatoTate
#check @PublishedBrunTitchmarsh
#check @CMHeckeAmplificationCorollary
#check @BrunTitchmarshPrimeLiftingCorollary
#check @PublishedInputReductionGoal
#check @Erdos979K3FromPublishedInputsGoal
#check @cmBlockPrimeInput_of_finite_corollaries
#check @f₃_infinite_from_cm_blocks
#check @f₃_infinite_from_finite_corollaries
#check @nat_limsup_eq_infinity_of_unbounded
#check @erdos_979_k3_from_finite_corollaries
#check @published_reduction_would_close_erdos_979_k3

#print PublishedCMSatoTate
#print PublishedBrunTitchmarsh
#print CMHeckeFamily
#print CMHeckeAmplificationCorollary
#print BrunTitchmarshPrimeLiftingCorollary
#print PublishedInputReductionGoal
#print Erdos979K3FromPublishedInputsGoal

#print axioms card_multiplesUpTo
#print axioms CMBlockCertificate.exists_large_cube_sum_fiber
#print axioms CMBlockCertificate.exists_le_f₃
#print axioms f₃_infinite_from_cm_blocks
#print axioms f₃_infinite_from_finite_corollaries
#print axioms erdos_979_k3_from_finite_corollaries
#print axioms published_reduction_would_close_erdos_979_k3

end K3Lean.CMProof
