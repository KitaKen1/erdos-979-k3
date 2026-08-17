import K3Lean.FiniteLifting
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.GCD.BigOperators

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# CRT multiplicativity of the local cube count

This file is finite algebra.  It identifies the literal natural-residue
finset `localCubeSolutions n` with unit solutions in `ZMod n`, then applies
the Chinese remainder ring equivalence.
-/

namespace K3Lean.LocalMultiplicativity

open K3Lean.CMProof
open K3Lean.FiniteLifting

noncomputable section

abbrev ZTriple (n : Nat) := ZMod n × ZMod n × ZMod n

def IsZLocalCubeSolution (n : Nat) (t : ZTriple n) : Prop :=
  IsUnit t.1 ∧ IsUnit t.2.1 ∧ IsUnit t.2.2 ∧
    t.1 ^ 3 + t.2.1 ^ 3 + t.2.2 ^ 3 = 0

noncomputable instance (n : Nat) : DecidablePred (IsZLocalCubeSolution n) :=
  Classical.decPred _

abbrev ZLocalCubeSolution (n : Nat) :=
  {t : ZTriple n // IsZLocalCubeSolution n t}

def natLocalToZMod {n : Nat} (hn : 0 < n)
    (t : {t : Triple // t ∈ localCubeSolutions n}) :
    ZLocalCubeSolution n := by
  letI : NeZero n := ⟨hn.ne'⟩
  refine ⟨((t.1.1 : ZMod n), (t.1.2.1 : ZMod n), (t.1.2.2 : ZMod n)), ?_⟩
  obtain ⟨h1, h2, h3⟩ := local_solution_components_mem t.2
  have hc1 : t.1.1.Coprime n :=
    (Finset.mem_filter.mp h1).2.symm
  have hc2 : t.1.2.1.Coprime n :=
    (Finset.mem_filter.mp h2).2.symm
  have hc3 : t.1.2.2.Coprime n :=
    (Finset.mem_filter.mp h3).2.symm
  have hdiv : n ∣ cubeSum t.1 := (Finset.mem_filter.mp t.2).2
  refine ⟨(ZMod.isUnit_iff_coprime _ _).2 hc1,
    (ZMod.isUnit_iff_coprime _ _).2 hc2,
    (ZMod.isUnit_iff_coprime _ _).2 hc3, ?_⟩
  have hz := (ZMod.natCast_eq_zero_iff (cubeSum t.1) n).2 hdiv
  simpa [cubeSum] using hz

def zmodLocalToNat {n : Nat} (hn : 0 < n)
    (t : ZLocalCubeSolution n) :
    {t : Triple // t ∈ localCubeSolutions n} := by
  letI : NeZero n := ⟨hn.ne'⟩
  let r : Triple := (t.1.1.val, t.1.2.1.val, t.1.2.2.val)
  have hlt1 : r.1 < n := by
    exact t.1.1.val_lt
  have hlt2 : r.2.1 < n := by
    exact t.1.2.1.val_lt
  have hlt3 : r.2.2 < n := by
    exact t.1.2.2.val_lt
  have hu1 : IsUnit ((r.1 : Nat) : ZMod n) := by
    change IsUnit ((t.1.1.val : Nat) : ZMod n)
    rw [ZMod.natCast_zmod_val]
    exact t.2.1
  have hu2 : IsUnit ((r.2.1 : Nat) : ZMod n) := by
    change IsUnit ((t.1.2.1.val : Nat) : ZMod n)
    rw [ZMod.natCast_zmod_val]
    exact t.2.2.1
  have hu3 : IsUnit ((r.2.2 : Nat) : ZMod n) := by
    change IsUnit ((t.1.2.2.val : Nat) : ZMod n)
    rw [ZMod.natCast_zmod_val]
    exact t.2.2.2.1
  have hc1 : n.Coprime r.1 :=
    ((ZMod.isUnit_iff_coprime _ _).1 hu1).symm
  have hc2 : n.Coprime r.2.1 :=
    ((ZMod.isUnit_iff_coprime _ _).1 hu2).symm
  have hc3 : n.Coprime r.2.2 :=
    ((ZMod.isUnit_iff_coprime _ _).1 hu3).symm
  have heq : ((cubeSum r : Nat) : ZMod n) = 0 := by
    simpa [r, cubeSum, ZMod.natCast_zmod_val] using t.2.2.2.2
  have hdiv : n ∣ cubeSum r :=
    (ZMod.natCast_eq_zero_iff _ _).1 heq
  have hr1 : r.1 ∈ unitResidues n := by
    rw [unitResidues, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr hlt1, hc1⟩
  have hr2 : r.2.1 ∈ unitResidues n := by
    rw [unitResidues, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr hlt2, hc2⟩
  have hr3 : r.2.2 ∈ unitResidues n := by
    rw [unitResidues, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr hlt3, hc3⟩
  refine ⟨r, ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_product.mpr
      ⟨hr1, Finset.mem_product.mpr ⟨hr2, hr3⟩⟩,
    hdiv⟩

def natLocalZModEquiv {n : Nat} (hn : 0 < n) :
    {t : Triple // t ∈ localCubeSolutions n} ≃ ZLocalCubeSolution n where
  toFun := natLocalToZMod hn
  invFun := zmodLocalToNat hn
  left_inv := by
    intro t
    letI : NeZero n := ⟨hn.ne'⟩
    obtain ⟨h1, h2, h3⟩ := local_solution_components_mem t.2
    have hlt1 : t.1.1 < n := Finset.mem_range.mp (Finset.mem_filter.mp h1).1
    have hlt2 : t.1.2.1 < n := Finset.mem_range.mp (Finset.mem_filter.mp h2).1
    have hlt3 : t.1.2.2 < n := Finset.mem_range.mp (Finset.mem_filter.mp h3).1
    apply Subtype.ext
    apply Prod.ext
    · exact ZMod.val_natCast_of_lt hlt1
    · apply Prod.ext
      · exact ZMod.val_natCast_of_lt hlt2
      · exact ZMod.val_natCast_of_lt hlt3
  right_inv := by
    intro t
    letI : NeZero n := ⟨hn.ne'⟩
    apply Subtype.ext
    apply Prod.ext
    · exact ZMod.natCast_zmod_val _
    · apply Prod.ext <;> exact ZMod.natCast_zmod_val _

theorem card_localCubeSolutions_eq_fintype {n : Nat} [NeZero n] (hn : 0 < n) :
    (localCubeSolutions n).card = Fintype.card (ZLocalCubeSolution n) := by
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (natLocalZModEquiv hn)

def zLocalCRT {a b : Nat} (h : a.Coprime b) :
    ZLocalCubeSolution (a * b) ≃
      ZLocalCubeSolution a × ZLocalCubeSolution b := by
  let e := ZMod.chineseRemainder h
  let forward : ZLocalCubeSolution (a * b) →
      ZLocalCubeSolution a × ZLocalCubeSolution b := fun t =>
    (⟨((e t.1.1).1, (e t.1.2.1).1, (e t.1.2.2).1), by
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact (Prod.isUnit_iff.mp ((MulEquiv.isUnit_map e).mpr t.2.1)).1
        · exact (Prod.isUnit_iff.mp ((MulEquiv.isUnit_map e).mpr t.2.2.1)).1
        · exact (Prod.isUnit_iff.mp ((MulEquiv.isUnit_map e).mpr t.2.2.2.1)).1
        · have hm := congr_arg Prod.fst (congr_arg e t.2.2.2.2)
          simpa [map_add, map_pow] using hm⟩,
     ⟨((e t.1.1).2, (e t.1.2.1).2, (e t.1.2.2).2), by
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact (Prod.isUnit_iff.mp ((MulEquiv.isUnit_map e).mpr t.2.1)).2
        · exact (Prod.isUnit_iff.mp ((MulEquiv.isUnit_map e).mpr t.2.2.1)).2
        · exact (Prod.isUnit_iff.mp ((MulEquiv.isUnit_map e).mpr t.2.2.2.1)).2
        · have hm := congr_arg Prod.snd (congr_arg e t.2.2.2.2)
          simpa [map_add, map_pow] using hm⟩)
  let backward : ZLocalCubeSolution a × ZLocalCubeSolution b →
      ZLocalCubeSolution (a * b) := fun t =>
    ⟨(e.symm (t.1.1.1, t.2.1.1),
      e.symm (t.1.1.2.1, t.2.1.2.1),
      e.symm (t.1.1.2.2, t.2.1.2.2)), by
        refine ⟨?_, ?_, ?_, ?_⟩
        · apply (MulEquiv.isUnit_map e.symm).mpr
          exact Prod.isUnit_iff.mpr ⟨t.1.2.1, t.2.2.1⟩
        · apply (MulEquiv.isUnit_map e.symm).mpr
          exact Prod.isUnit_iff.mpr ⟨t.1.2.2.1, t.2.2.2.1⟩
        · apply (MulEquiv.isUnit_map e.symm).mpr
          exact Prod.isUnit_iff.mpr ⟨t.1.2.2.2.1, t.2.2.2.2.1⟩
        · apply e.injective
          ext
          · simpa [map_add, map_pow] using t.1.2.2.2.2
          · simpa [map_add, map_pow] using t.2.2.2.2.2⟩
  exact {
    toFun := forward
    invFun := backward
    left_inv := by
      intro t
      apply Subtype.ext
      ext <;> simp [forward, backward, e]
    right_inv := by
      intro t
      apply Prod.ext <;> apply Subtype.ext <;> ext <;>
        simp [forward, backward, e] }

theorem localCubeSolutions_card_mul {a b : Nat}
    (ha : 0 < a) (hb : 0 < b) (h : a.Coprime b) :
    (localCubeSolutions (a * b)).card =
      (localCubeSolutions a).card * (localCubeSolutions b).card := by
  letI : NeZero a := ⟨ha.ne'⟩
  letI : NeZero b := ⟨hb.ne'⟩
  letI : NeZero (a * b) := ⟨(Nat.mul_pos ha hb).ne'⟩
  rw [card_localCubeSolutions_eq_fintype (Nat.mul_pos ha hb),
    card_localCubeSolutions_eq_fintype ha,
    card_localCubeSolutions_eq_fintype hb,
    ← Fintype.card_prod]
  exact Fintype.card_congr (zLocalCRT h)

theorem localCubeSolutions_card_one :
    (localCubeSolutions 1).card = 1 := by
  decide

theorem prime_coprime_prod {S : Finset Nat} {p : Nat}
    (hp : p.Prime) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∉ S) :
    p.Coprime (S.prod id) := by
  rw [Nat.coprime_prod_right_iff]
  intro q hq
  exact (Nat.coprime_primes hp (hS q hq)).2 (fun hpq => hpS (hpq ▸ hq))

theorem localCubeSolutions_card_prod_primes (S : Finset Nat)
    (hS : ∀ p ∈ S, p.Prime) :
    (localCubeSolutions (S.prod id)).card =
      S.prod (fun p => (localCubeSolutions p).card) := by
  induction S using Finset.induction_on with
  | empty => simpa using localCubeSolutions_card_one
  | @insert p S hpS ih =>
      have hp : p.Prime := hS p (Finset.mem_insert_self p S)
      have hS' : ∀ q ∈ S, q.Prime := by
        intro q hq
        exact hS q (Finset.mem_insert_of_mem hq)
      have hprodpos : 0 < S.prod id :=
        Finset.prod_pos fun q hq => (hS' q hq).pos
      have hcop : p.Coprime (S.prod id) := prime_coprime_prod hp hS' hpS
      have hprod : (insert p S).prod id = p * S.prod id := by
        simpa only [id_eq] using
          (Finset.prod_insert (f := id) hpS)
      have hsolutionProd :
          (insert p S).prod (fun q => (localCubeSolutions q).card) =
            (localCubeSolutions p).card *
              S.prod (fun q => (localCubeSolutions q).card) :=
        Finset.prod_insert hpS
      calc
        (localCubeSolutions ((insert p S).prod id)).card =
            (localCubeSolutions (p * S.prod id)).card := by rw [hprod]
        _ = (localCubeSolutions p).card *
            (localCubeSolutions (S.prod id)).card :=
              localCubeSolutions_card_mul hp.pos hprodpos hcop
        _ = (localCubeSolutions p).card *
            S.prod (fun q => (localCubeSolutions q).card) := by
              rw [ih hS']
        _ = (insert p S).prod (fun q => (localCubeSolutions q).card) :=
          hsolutionProd.symm

theorem totient_prod_primes (S : Finset Nat)
    (hS : ∀ p ∈ S, p.Prime) :
    (S.prod id).totient = S.prod Nat.totient := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hpS ih =>
      have hp : p.Prime := hS p (Finset.mem_insert_self p S)
      have hS' : ∀ q ∈ S, q.Prime := by
        intro q hq
        exact hS q (Finset.mem_insert_of_mem hq)
      have hcop : p.Coprime (S.prod id) := prime_coprime_prod hp hS' hpS
      have hprod : (insert p S).prod id = p * S.prod id := by
        simpa only [id_eq] using
          (Finset.prod_insert (f := id) hpS)
      have htotientProd :
          (insert p S).prod Nat.totient =
            p.totient * S.prod Nat.totient :=
        Finset.prod_insert hpS
      calc
        ((insert p S).prod id).totient = (p * S.prod id).totient := by rw [hprod]
        _ = p.totient * (S.prod id).totient := Nat.totient_mul hcop
        _ = p.totient * S.prod Nat.totient := by rw [ih hS']
        _ = (insert p S).prod Nat.totient := htotientProd.symm

#check @ZMod.chineseRemainder
#check @localCubeSolutions_card_mul
#check @localCubeSolutions_card_prod_primes
#check @totient_prod_primes
#print axioms localCubeSolutions_card_mul
#print axioms localCubeSolutions_card_prod_primes

end

end K3Lean.LocalMultiplicativity
