import K3Lean.CMProof
import Mathlib.Algebra.Order.BigOperators.Group.Finset

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# The finite prime-lifting step for Erdos #979, k = 3

This file contains no analytic number theory.  It proves the exact finite
statement needed after a prime-distribution theorem has supplied a lower bound
for every reduced residue class.

The local congruence count is ordered.  Sorting a triple can identify at most
the six permutations of its entries, so the honest comparison has a factor
`3! = 6`.  Keeping that factor visible prevents it from being hidden in an
analytic hypothesis.
-/

namespace K3Lean.FiniteLifting

open K3Lean.Expanded
open K3Lean.CMProof
open scoped BigOperators

/-- Primes at most `X` in the residue class `r (mod a)`. -/
def primesInClass (a X r : Nat) : Finset Nat :=
  (Finset.range X.succ).filter (fun p => Nat.Prime p ∧ p % a = r)

/-- A uniform lower bound for every reduced residue class modulo `a`. -/
def UniformPrimeClasses (a X g : Nat) : Prop :=
  ∀ r ∈ unitResidues a, g ≤ (primesInClass a X r).card

/-- Ordered prime lifts of one local residue triple. -/
def residueLifts (a X : Nat) (r : Triple) : Finset Triple :=
  (primesInClass a X r.1) ×ˢ
    (primesInClass a X r.2.1) ×ˢ
      (primesInClass a X r.2.2)

/-- The disjoint union of the lifts of all local cube solutions. -/
def allResidueLifts (a X : Nat) : Finset Triple :=
  (localCubeSolutions a).biUnion (residueLifts a X)

theorem pairwiseDisjoint_residueLifts (a X : Nat) :
    ((localCubeSolutions a : Finset Triple) : Set Triple).PairwiseDisjoint
      (residueLifts a X) := by
  intro r _hr s _hs hrs
  change Disjoint (residueLifts a X r) (residueLifts a X s)
  rw [Finset.disjoint_left]
  intro t htr hts
  simp only [residueLifts, Finset.mem_product] at htr hts
  have h1 : r.1 = s.1 := by
    have hr := (Finset.mem_filter.mp htr.1).2.2
    have hs := (Finset.mem_filter.mp hts.1).2.2
    exact hr.symm.trans hs
  have h2 : r.2.1 = s.2.1 := by
    have hr := (Finset.mem_filter.mp htr.2.1).2.2
    have hs := (Finset.mem_filter.mp hts.2.1).2.2
    exact hr.symm.trans hs
  have h3 : r.2.2 = s.2.2 := by
    have hr := (Finset.mem_filter.mp htr.2.2).2.2
    have hs := (Finset.mem_filter.mp hts.2.2).2.2
    exact hr.symm.trans hs
  exact hrs (Prod.ext h1 (Prod.ext h2 h3))

theorem card_allResidueLifts (a X : Nat) :
    (allResidueLifts a X).card =
      ∑ r ∈ localCubeSolutions a, (residueLifts a X r).card := by
  rw [allResidueLifts, Finset.card_biUnion (pairwiseDisjoint_residueLifts a X)]

theorem local_solution_components_mem {a : Nat} {r : Triple}
    (hr : r ∈ localCubeSolutions a) :
    r.1 ∈ unitResidues a ∧ r.2.1 ∈ unitResidues a ∧
      r.2.2 ∈ unitResidues a := by
  simpa only [Finset.mem_product] using (Finset.mem_filter.mp hr).1

theorem uniform_le_card_residueLifts {a X g : Nat}
    (huniform : UniformPrimeClasses a X g) {r : Triple}
    (hr : r ∈ localCubeSolutions a) :
    g ^ 3 ≤ (residueLifts a X r).card := by
  obtain ⟨hr1, hr2, hr3⟩ := local_solution_components_mem hr
  have h1 := huniform r.1 hr1
  have h2 := huniform r.2.1 hr2
  have h3 := huniform r.2.2 hr3
  simpa [residueLifts, Finset.card_product, pow_succ, Nat.mul_assoc] using
    Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

theorem local_count_mul_cube_le_all_lifts {a X g : Nat}
    (huniform : UniformPrimeClasses a X g) :
    (localCubeSolutions a).card * g ^ 3 ≤ (allResidueLifts a X).card := by
  rw [card_allResidueLifts]
  calc
    (localCubeSolutions a).card * g ^ 3 =
        ∑ _r ∈ localCubeSolutions a, g ^ 3 := by simp
    _ ≤ ∑ r ∈ localCubeSolutions a, (residueLifts a X r).card :=
      Finset.sum_le_sum fun r hr => uniform_le_card_residueLifts huniform hr

theorem mem_allResidueLifts_iff {a X : Nat} {t : Triple} :
    t ∈ allResidueLifts a X ↔
      ∃ r ∈ localCubeSolutions a, t ∈ residueLifts a X r := by
  simp [allResidueLifts]

/-- Ordered prime triples below `X` whose cube sum is zero modulo `a`. -/
def orderedBlockPrimeTriples (a X : Nat) : Finset Triple :=
  (box X).filter (fun t =>
    Nat.Prime t.1 ∧ Nat.Prime t.2.1 ∧ Nat.Prime t.2.2 ∧
      a ∣ cubeSum t)

theorem allResidueLifts_subset_orderedBlockPrimeTriples (a X : Nat) :
    allResidueLifts a X ⊆ orderedBlockPrimeTriples a X := by
  intro t ht
  obtain ⟨r, hr, htr⟩ := mem_allResidueLifts_iff.mp ht
  simp only [residueLifts, Finset.mem_product] at htr
  have hp1 := Finset.mem_filter.mp htr.1
  have hp2 := Finset.mem_filter.mp htr.2.1
  have hp3 := Finset.mem_filter.mp htr.2.2
  obtain ⟨hr1, hr2, hr3⟩ := local_solution_components_mem hr
  have hr1lt : r.1 < a := Finset.mem_range.mp (Finset.mem_filter.mp hr1).1
  have hr2lt : r.2.1 < a := Finset.mem_range.mp (Finset.mem_filter.mp hr2).1
  have hr3lt : r.2.2 < a := Finset.mem_range.mp (Finset.mem_filter.mp hr3).1
  have hrdiv : a ∣ cubeSum r := (Finset.mem_filter.mp hr).2
  have hmod1 : t.1 ≡ r.1 [MOD a] := by
    show t.1 % a = r.1 % a
    rw [hp1.2.2, Nat.mod_eq_of_lt hr1lt]
  have hmod2 : t.2.1 ≡ r.2.1 [MOD a] := by
    show t.2.1 % a = r.2.1 % a
    rw [hp2.2.2, Nat.mod_eq_of_lt hr2lt]
  have hmod3 : t.2.2 ≡ r.2.2 [MOD a] := by
    show t.2.2 % a = r.2.2 % a
    rw [hp3.2.2, Nat.mod_eq_of_lt hr3lt]
  have hsum : cubeSum t ≡ cubeSum r [MOD a] := by
    exact ((hmod1.pow 3).add (hmod2.pow 3)).add (hmod3.pow 3)
  have hdiv : a ∣ cubeSum t := by
    exact Nat.modEq_zero_iff_dvd.mp
      (hsum.trans (Nat.modEq_zero_iff_dvd.mpr hrdiv))
  rw [orderedBlockPrimeTriples, Finset.mem_filter]
  constructor
  · simp only [box, Finset.mem_product, Finset.mem_range]
    exact ⟨Finset.mem_range.mp hp1.1, Finset.mem_range.mp hp2.1,
      Finset.mem_range.mp hp3.1⟩
  · exact ⟨hp1.2.1, hp2.2.1, hp3.2.1, hdiv⟩

/-- Sort three natural numbers into nondecreasing order. -/
def sortTriple (t : Triple) : Triple :=
  if t.1 ≤ t.2.1 then
    if t.2.1 ≤ t.2.2 then t
    else if t.1 ≤ t.2.2 then (t.1, t.2.2, t.2.1)
    else (t.2.2, t.1, t.2.1)
  else
    if t.1 ≤ t.2.2 then (t.2.1, t.1, t.2.2)
    else if t.2.1 ≤ t.2.2 then (t.2.1, t.2.2, t.1)
    else (t.2.2, t.2.1, t.1)

/-- The at most six permutations of a triple. -/
def triplePermutations (t : Triple) : Finset Triple :=
  {t,
   (t.1, t.2.2, t.2.1),
   (t.2.1, t.1, t.2.2),
   (t.2.1, t.2.2, t.1),
   (t.2.2, t.1, t.2.1),
   (t.2.2, t.2.1, t.1)}

theorem card_triplePermutations_le (t : Triple) :
    (triplePermutations t).card ≤ 6 := by
  unfold triplePermutations
  grind

theorem self_mem_permutations_sortTriple (t : Triple) :
    t ∈ triplePermutations (sortTriple t) := by
  unfold sortTriple
  split_ifs <;> simp [triplePermutations]

theorem sortTriple_ordered (t : Triple) :
    (sortTriple t).1 ≤ (sortTriple t).2.1 ∧
      (sortTriple t).2.1 ≤ (sortTriple t).2.2 := by
  by_cases h12 : t.1 ≤ t.2.1
  · by_cases h23 : t.2.1 ≤ t.2.2
    · simp [sortTriple, h12, h23]
    · by_cases h13 : t.1 ≤ t.2.2
      · simp [sortTriple, h12, h23, h13]
        omega
      · simp [sortTriple, h12, h23, h13]
        omega
  · by_cases h13 : t.1 ≤ t.2.2
    · simp [sortTriple, h12, h13]
      omega
    · by_cases h23 : t.2.1 ≤ t.2.2
      · simp [sortTriple, h12, h13, h23]
        omega
      · simp [sortTriple, h12, h13, h23]
        omega

theorem cubeSum_sortTriple (t : Triple) : cubeSum (sortTriple t) = cubeSum t := by
  unfold sortTriple
  split_ifs <;> simp [cubeSum, add_comm, add_left_comm, add_assoc]

theorem sortTriple_preserves_primes {t : Triple}
    (ht : Nat.Prime t.1 ∧ Nat.Prime t.2.1 ∧ Nat.Prime t.2.2) :
    Nat.Prime (sortTriple t).1 ∧ Nat.Prime (sortTriple t).2.1 ∧
      Nat.Prime (sortTriple t).2.2 := by
  unfold sortTriple
  split_ifs <;> rcases ht with ⟨h1, h2, h3⟩ <;> simp_all

theorem sortTriple_preserves_bounds {X : Nat} {t : Triple}
    (ht : t.1 ≤ X ∧ t.2.1 ≤ X ∧ t.2.2 ≤ X) :
    (sortTriple t).1 ≤ X ∧ (sortTriple t).2.1 ≤ X ∧
      (sortTriple t).2.2 ≤ X := by
  unfold sortTriple
  split_ifs <;> rcases ht with ⟨h1, h2, h3⟩ <;> simp_all

theorem sort_mem_blockPrimeTriples {a X : Nat} {t : Triple}
    (ht : t ∈ orderedBlockPrimeTriples a X) :
    sortTriple t ∈ blockPrimeTriples a X := by
  have ht' := Finset.mem_filter.mp ht
  simp only [box, Finset.mem_product, Finset.mem_range] at ht'
  have hbounds : t.1 ≤ X ∧ t.2.1 ≤ X ∧ t.2.2 ≤ X :=
    ⟨Nat.le_of_lt_succ ht'.1.1,
      Nat.le_of_lt_succ ht'.1.2.1,
      Nat.le_of_lt_succ ht'.1.2.2⟩
  apply mem_blockPrimeTriples_iff.mpr
  refine ⟨?_, ?_, sortTriple_preserves_bounds hbounds⟩
  · exact ⟨(sortTriple_ordered t).1, (sortTriple_ordered t).2,
      sortTriple_preserves_primes ⟨ht'.2.1, ht'.2.2.1, ht'.2.2.2.1⟩⟩
  · rw [cubeSum_sortTriple]
    exact ht'.2.2.2.2

/-- Sorted images of all ordered prime triples in the block. -/
def sortedLiftImages (a X : Nat) : Finset Triple :=
  (orderedBlockPrimeTriples a X).image sortTriple

theorem sortedLiftImages_subset_blockPrimeTriples (a X : Nat) :
    sortedLiftImages a X ⊆ blockPrimeTriples a X := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
  exact sort_mem_blockPrimeTriples hu

theorem ordered_subset_permutations_of_sorted_images (a X : Nat) :
    orderedBlockPrimeTriples a X ⊆
      (sortedLiftImages a X).biUnion triplePermutations := by
  intro t ht
  apply Finset.mem_biUnion.mpr
  exact ⟨sortTriple t, Finset.mem_image.mpr ⟨t, ht, rfl⟩,
    self_mem_permutations_sortTriple t⟩

theorem card_ordered_le_six_mul_sorted (a X : Nat) :
    (orderedBlockPrimeTriples a X).card ≤
      6 * (blockPrimeTriples a X).card := by
  calc
    (orderedBlockPrimeTriples a X).card
        ≤ ((sortedLiftImages a X).biUnion triplePermutations).card :=
      Finset.card_le_card (ordered_subset_permutations_of_sorted_images a X)
    _ ≤ (sortedLiftImages a X).card * 6 :=
      Finset.card_biUnion_le_card_mul _ _ _ fun t _ => card_triplePermutations_le t
    _ ≤ (blockPrimeTriples a X).card * 6 :=
      Nat.mul_le_mul_right 6
        (Finset.card_le_card (sortedLiftImages_subset_blockPrimeTriples a X))
    _ = 6 * (blockPrimeTriples a X).card := Nat.mul_comm _ _

/--
The complete finite lifting theorem.  Its only hypothesis is the explicit
uniform lower bound for primes in reduced residue classes.
-/
theorem uniform_prime_classes_lift {a X g : Nat}
    (huniform : UniformPrimeClasses a X g) :
    (localCubeSolutions a).card * g ^ 3 ≤
      6 * (blockPrimeTriples a X).card := by
  exact (local_count_mul_cube_le_all_lifts huniform).trans
    ((Finset.card_le_card (allResidueLifts_subset_orderedBlockPrimeTriples a X)).trans
      (card_ordered_le_six_mul_sorted a X))

/-!
## An honest finite certificate

Unlike the earlier provisional certificate in `CMProof`, this structure keeps
the ordered-to-unordered factor `6` in both inequalities.  Its lifting field is
the concrete statement `UniformPrimeClasses`; the lifting inequality is now a
theorem above, not an assumed problem-specific corollary.
-/

structure AuditedBlockCertificate (B : Nat) where
  modulus : Nat
  cutoff : Nat
  primesPerClass : Nat
  modulus_pos : 0 < modulus
  uniform : UniformPrimeClasses modulus cutoff primesPerClass
  growth :
    6 * (((3 * cutoff ^ 3) / modulus + 1) * B) ≤
      (localCubeSolutions modulus).card * primesPerClass ^ 3

namespace AuditedBlockCertificate

def triples {B : Nat} (C : AuditedBlockCertificate B) : Finset Triple :=
  blockPrimeTriples C.modulus C.cutoff

def values {B : Nat} (C : AuditedBlockCertificate B) : Finset Nat :=
  multiplesUpTo C.modulus (3 * C.cutoff ^ 3)

theorem values_card {B : Nat} (C : AuditedBlockCertificate B) :
    C.values.card = (3 * C.cutoff ^ 3) / C.modulus + 1 := by
  exact card_multiplesUpTo

theorem cubeSum_mem_values {B : Nat} (C : AuditedBlockCertificate B)
    {t : Triple} (ht : t ∈ C.triples) : cubeSum t ∈ C.values := by
  have ht' := mem_blockPrimeTriples_iff.mp ht
  rw [values, mem_multiplesUpTo_iff]
  exact ⟨cubeSum_le_three_mul_cube
      ⟨ht'.2.2.1, ht'.2.2.2.1, ht'.2.2.2.2⟩,
    ht'.2.1⟩

theorem values_nonempty {B : Nat} (C : AuditedBlockCertificate B) :
    C.values.Nonempty := by
  refine ⟨0, ?_⟩
  simp [values, multiplesUpTo]

theorem enough_triples {B : Nat} (C : AuditedBlockCertificate B) :
    C.values.card * B ≤ C.triples.card := by
  have h6 :
      6 * (((3 * C.cutoff ^ 3) / C.modulus + 1) * B) ≤
        6 * (blockPrimeTriples C.modulus C.cutoff).card :=
    C.growth.trans (uniform_prime_classes_lift C.uniform)
  rw [C.values_card]
  exact Nat.le_of_mul_le_mul_left h6 (by norm_num)

theorem exists_large_cube_sum_fiber {B : Nat} (C : AuditedBlockCertificate B) :
    ∃ n ∈ C.values,
      B ≤ (C.triples.filter (fun t => cubeSum t = n)).card := by
  exact Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (fun t ht => C.cubeSum_mem_values ht)
    C.values_nonempty
    C.enough_triples

theorem exists_le_f₃ {B : Nat} (C : AuditedBlockCertificate B) :
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

end AuditedBlockCertificate

/-!
## Arithmetic assembly of the two analytic estimates

`D` is the logarithmic loss in the prime number theorem for progressions.
The first inequality below says that every reduced class contains at least
`g`, up to that loss.  The second says that the normalized local density has
been amplified by at least `24 * B * D^3`.
-/

theorem certificate_growth_of_scaled_bounds
    {B a X g D : Nat}
    (ha : 0 < a)
    (haX3 : a ≤ X ^ 3)
    (hprimeScale : X ≤ D * a.totient * g)
    (hlocalDensity :
      24 * B * D ^ 3 * a.totient ^ 3 ≤
        a * (localCubeSolutions a).card) :
    6 * (((3 * X ^ 3) / a + 1) * B) ≤
      (localCubeSolutions a).card * g ^ 3 := by
  let R := (localCubeSolutions a).card
  let V := (3 * X ^ 3) / a + 1
  have hdiv : a * ((3 * X ^ 3) / a) ≤ 3 * X ^ 3 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (3 * X ^ 3) a
  have hvalue : a * V ≤ 4 * X ^ 3 := by
    dsimp [V]
    calc
      a * ((3 * X ^ 3) / a + 1) =
          a * ((3 * X ^ 3) / a) + a := by ring
      _ ≤ 3 * X ^ 3 + X ^ 3 := Nat.add_le_add hdiv haX3
      _ = 4 * X ^ 3 := by ring
  have hvalueScaled :
      a * (6 * (V * B)) ≤ 24 * B * X ^ 3 := by
    calc
      a * (6 * (V * B)) = 6 * B * (a * V) := by ring
      _ ≤ 6 * B * (4 * X ^ 3) := Nat.mul_le_mul_left (6 * B) hvalue
      _ = 24 * B * X ^ 3 := by ring
  have hscaleCube : X ^ 3 ≤ D ^ 3 * a.totient ^ 3 * g ^ 3 := by
    calc
      X ^ 3 ≤ (D * a.totient * g) ^ 3 := Nat.pow_le_pow_left hprimeScale 3
      _ = D ^ 3 * a.totient ^ 3 * g ^ 3 := by ring
  have hmiddle :
      24 * B * X ^ 3 ≤
        (24 * B * D ^ 3 * a.totient ^ 3) * g ^ 3 := by
    calc
      24 * B * X ^ 3 ≤ 24 * B * (D ^ 3 * a.totient ^ 3 * g ^ 3) :=
        Nat.mul_le_mul_left (24 * B) hscaleCube
      _ = (24 * B * D ^ 3 * a.totient ^ 3) * g ^ 3 := by ring
  have hlocalScaled :
      (24 * B * D ^ 3 * a.totient ^ 3) * g ^ 3 ≤
        a * (R * g ^ 3) := by
    calc
      (24 * B * D ^ 3 * a.totient ^ 3) * g ^ 3
          ≤ (a * R) * g ^ 3 := Nat.mul_le_mul_right (g ^ 3) hlocalDensity
      _ = a * (R * g ^ 3) := by ring
  have hcancel : a * (6 * (V * B)) ≤ a * (R * g ^ 3) :=
    hvalueScaled.trans (hmiddle.trans hlocalScaled)
  exact Nat.le_of_mul_le_mul_left hcancel ha

#check @UniformPrimeClasses
#check @uniform_prime_classes_lift
#check @AuditedBlockCertificate
#check @AuditedBlockCertificate.exists_le_f₃
#check @certificate_growth_of_scaled_bounds
#print axioms uniform_prime_classes_lift
#print axioms AuditedBlockCertificate.exists_le_f₃
#print axioms certificate_growth_of_scaled_bounds

end K3Lean.FiniteLifting
