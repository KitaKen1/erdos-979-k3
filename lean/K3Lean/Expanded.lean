import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Common

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Erdős #979, k = 3: the explicit representation counter

This module contains the elementary finite layer shared by the proof files.

* Define the representation counter explicitly: `f₃ n` is the number of
  sorted prime-cube representations of `n`.
* Prove `card_le_f₃`, which transfers any explicit finite family of
  representations into a lower bound for `f₃`.
* Check the five-representation witness without additional assumptions.

The two analytic inputs and the final theorem live in `K3Lean.CMProof`.
-/

namespace K3Lean.Expanded

/-- A sorted prime-cube representation of `n`. -/
def GoodCubeTriple (n : Nat) (t : Nat × Nat × Nat) : Prop :=
  t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
  Nat.Prime t.1 ∧ Nat.Prime t.2.1 ∧ Nat.Prime t.2.2 ∧
  t.1 ^ 3 + t.2.1 ^ 3 + t.2.2 ^ 3 = n

/-- `GoodCubeTriple n` is decidable, as required by `Finset.filter`. -/
instance decGoodCubeTriple (n : Nat) : DecidablePred (GoodCubeTriple n) := by
  intro t
  unfold GoodCubeTriple
  infer_instance

/-- The finite search box `[0, n]^3`, which contains every representation. -/
def box (n : Nat) : Finset (Nat × Nat × Nat) :=
  (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))

/-- `f₃ n` is the number of sorted prime-cube representations of `n`. -/
def f₃ (n : Nat) : Nat :=
  ((box n).filter (fun t => GoodCubeTriple n t)).card

/-- An ordered prime-cube solution of the equation in Erdős's original statement. -/
def OrderedPrimeCubeTriple (n : Nat) (t : Nat × Nat × Nat) : Prop :=
  Nat.Prime t.1 ∧ Nat.Prime t.2.1 ∧ Nat.Prime t.2.2 ∧
  t.1 ^ 3 + t.2.1 ^ 3 + t.2.2 ^ 3 = n

instance decOrderedPrimeCubeTriple (n : Nat) :
    DecidablePred (OrderedPrimeCubeTriple n) := by
  intro t
  unfold OrderedPrimeCubeTriple
  infer_instance

/-- The ordered solution count, matching the indexed-variable reading of Erdős's `f₃`. -/
def f₃Ordered (n : Nat) : Nat :=
  ((box n).filter (fun t => OrderedPrimeCubeTriple n t)).card

/-- Forgetting the sorting inequalities embeds unordered representations into ordered ones. -/
theorem f₃_le_f₃Ordered (n : Nat) : f₃ n ≤ f₃Ordered n := by
  unfold f₃ f₃Ordered
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_filter] at ht ⊢
  refine ⟨ht.1, ?_⟩
  exact ⟨ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.1,
    ht.2.2.2.2.2.2⟩

/-- Every valid representation belongs to `box n`. -/
theorem mem_box_of_good (n : Nat) (t : Nat × Nat × Nat)
    (ht : GoodCubeTriple n t) : t ∈ box n := by
  -- Extract primality and the sum identity.
  obtain ⟨_h12, _h23, hp1, hp2, hp3, hsum⟩ := ht
  -- For a prime `x`, combine `x ≤ x^3` with `x^3 ≤ n`.
  have key : ∀ x : Nat, Nat.Prime x → x ^ 3 ≤ n → x ≤ n := fun x hx hxn =>
    le_trans (le_self_pow hx.one_lt.le (by norm_num)) hxn
  -- Each cube is at most the full sum `n`.
  have hb1 : t.1 ^ 3 ≤ n := by omega
  have hb2 : t.2.1 ^ 3 ≤ n := by omega
  have hb3 : t.2.2 ^ 3 ≤ n := by omega
  -- Membership in `box n` is the conjunction of three `< n + 1` bounds.
  simp only [box, Finset.mem_product, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le (key _ hp1 hb1),
         Nat.lt_succ_of_le (key _ hp2 hb2),
         Nat.lt_succ_of_le (key _ hp3 hb3)⟩

/-- Any finite family `S` of valid representations has card at most `f₃ n`. -/
theorem card_le_f₃ (n : Nat) (S : Finset (Nat × Nat × Nat))
    (hS : ∀ t ∈ S, GoodCubeTriple n t) : S.card ≤ f₃ n := by
  -- Unfold `f₃ n` as the cardinality of the filtered box.
  unfold f₃
  -- Show that `S` is a subset of that filter.
  apply Finset.card_le_card
  intro t htS
  rw [Finset.mem_filter]
  exact ⟨mem_box_of_good n t (hS t htS), hS t htS⟩

/-! ## Finite witness: five representations for `k = 3` -/

/-- The five representations from the #979 discussion / OEIS A385316. -/
def fiveK3Triples : Finset (Nat × Nat × Nat) :=
  { (59, 1669, 1811),
    (83, 1567, 1889),
    (139, 1427, 1973),
    (349, 1091, 2099),
    (479, 929, 2131) }

/-- All five triples are sorted prime-cube representations of `10588881419`. -/
theorem five_good : ∀ t ∈ fiveK3Triples, GoodCubeTriple 10588881419 t := by
  intro t ht
  simp only [fiveK3Triples, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with h | h | h | h | h <;> (subst h; norm_num [GoodCubeTriple])

/-- Hence `f₃ 10588881419 ≥ 5`, using `decide` and the finite bridge. -/
theorem five_le_f₃ : 5 ≤ f₃ 10588881419 := by
  have hcard : fiveK3Triples.card = 5 := by decide
  calc (5 : Nat) = fiveK3Triples.card := hcard.symm
    _ ≤ f₃ 10588881419 := card_le_f₃ _ _ five_good

/-! ## Audit: `#check` and `#print axioms` -/

#check @f₃
#check @f₃Ordered
#check @f₃_le_f₃Ordered
#check @five_le_f₃
#check @card_le_f₃

#print axioms five_good
#print axioms five_le_f₃

end K3Lean.Expanded
