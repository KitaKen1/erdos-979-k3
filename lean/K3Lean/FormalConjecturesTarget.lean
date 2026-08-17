import K3Lean.ManyBlockCM
import K3Lean.HeckeDeuringReduction
import K3Lean.HeckeCharacterCriterion
import K3Lean.CosineWeyl
import K3Lean.FermatHasseAngle
import K3Lean.FullCMSatoTateFromHecke
import K3Lean.AuditedExternalStatements
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Set.Card
import Mathlib.Order.LiminfLimsup

/-!
# Exact Formal Conjectures target for Erdős problem 979, k = 3

The definition `Erdos979.solutionSet` and the displayed target are copied
verbatim from Google DeepMind's Formal Conjectures repository, commit
`b2e608fc52d765510915a244bb69b1a2741acc3c`:

https://github.com/google-deepmind/formal-conjectures/blob/b2e608fc52d765510915a244bb69b1a2741acc3c/FormalConjectures/ErdosProblems/979.lean

Formal Conjectures places the natural-language problem and its Lean statement
side by side.  That reviewed statement correspondence, rather than the state
of its proof body, is why this file adopts the definition and target.  We prove
the target locally so that the reduction remains independently checkable: the
project's sorted-triple count injects into the exact multiset-valued solution
set, and tail-unboundedness transfers to the repository's literal
`Filter.limsup ... = ⊤` statement.
-/

namespace Erdos979

/-- The exact solution-set definition used by Formal Conjectures for #979. -/
def solutionSet (n k : ℕ) : Set (Multiset ℕ) :=
  {P | P.card = k ∧ (∀ p ∈ P, Nat.Prime p) ∧ n = (P.map (. ^ k)).sum}

end Erdos979

namespace K3Lean.FormalConjecturesTarget

open Filter
open K3Lean.Expanded

abbrev Triple := Nat × Nat × Nat

/-- Forget the sorted order and retain only the unordered multiset. -/
def tripleMultiset (t : Triple) : Multiset Nat :=
  {t.1, t.2.1, t.2.2}

private theorem sort_triple {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) :
    Multiset.sort ({a, b, c} : Multiset Nat) (· ≤ ·) = [a, b, c] := by
  change Multiset.sort (a ::ₘ b ::ₘ ({c} : Multiset Nat)) (· ≤ ·) = [a, b, c]
  rw [Multiset.sort_cons]
  · rw [Multiset.sort_cons]
    · simp
    · simp [hbc]
  · simp [hab, hab.trans hbc]

/-- A sorted triple is uniquely determined by its underlying multiset. -/
private theorem tripleMultiset_injOn (n : Nat) :
    Set.InjOn tripleMultiset
      (↑((box n).filter (fun t => GoodCubeTriple n t)) : Set Triple) := by
  rintro ⟨a, b, c⟩ habc ⟨x, y, z⟩ hxyz hmultiset
  simp only [Finset.mem_coe, Finset.mem_filter] at habc hxyz
  have hlist : [a, b, c] = [x, y, z] := by
    rw [← sort_triple habc.2.1 habc.2.2.1,
      ← sort_triple hxyz.2.1 hxyz.2.2.1]
    exact congrArg (fun P : Multiset Nat => Multiset.sort P (· ≤ ·)) hmultiset
  simpa using hlist

/-- Every sorted prime-cube triple maps to the exact Formal Conjectures set. -/
private theorem tripleMultiset_mapsTo (n : Nat) :
    Set.MapsTo tripleMultiset
      (↑((box n).filter (fun t => GoodCubeTriple n t)) : Set Triple)
      (Erdos979.solutionSet n 3) := by
  rintro ⟨a, b, c⟩ habc
  simp only [Finset.mem_coe, Finset.mem_filter] at habc
  rcases habc.2 with ⟨_hab, _hbc, ha, hb, hc, hsum⟩
  simp only [Erdos979.solutionSet, Set.mem_setOf_eq]
  refine ⟨by simp [tripleMultiset], ?_, ?_⟩
  · simpa [tripleMultiset, ha, hb, hc]
  · simpa [tripleMultiset, add_assoc] using hsum.symm

/-- The project's sorted count is bounded by the exact Formal Conjectures count. -/
theorem f₃_le_solutionSet_encard (n : Nat) :
    (f₃ n : ℕ∞) ≤ (Erdos979.solutionSet n 3).encard := by
  rw [f₃]
  calc
    (((box n).filter (fun t => GoodCubeTriple n t)).card : ℕ∞) =
        (↑((box n).filter (fun t => GoodCubeTriple n t)) : Set Triple).encard := by
          exact (Set.encard_coe_eq_coe_finsetCard _).symm
    _ ≤ (Erdos979.solutionSet n 3).encard :=
      Set.encard_le_encard_of_injOn
        (tripleMultiset_mapsTo n) (tripleMultiset_injOn n)

/-- Tail-unboundedness of `f₃` implies the literal Formal Conjectures limsup target. -/
theorem formal_conjectures_limsup_of_f₃_tail_unbounded
    (h : ∀ B N : Nat, ∃ n : Nat, N ≤ n ∧ B ≤ f₃ n) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  apply ENat.eq_top_iff_forall_ge.mpr
  intro B
  apply Filter.le_limsup_of_frequently_le'
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨n, hn, hB⟩ := h B N
  exact ⟨n, hn, (Nat.cast_le.mpr hB).trans (f₃_le_solutionSet_encard n)⟩

/-- The exact Formal Conjectures target from the two named source inputs. -/
theorem erdos_979_k3_from_cm_sato_tate_and_pnt
    (hST : K3Lean.SourceTheorems.FermatCMSatoTate)
    (hPNT : K3Lean.SourceTheorems.OrdinaryPrimeNumberTheorem) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  apply formal_conjectures_limsup_of_f₃_tail_unbounded
  simpa [f₃, box, GoodCubeTriple] using
    K3Lean.ManyBlockCM.erdos_979_k3_from_cm_sato_tate_and_pnt hST hPNT

/--
Source-level CM Sato--Tate corollary.  The first hypothesis is the full interval
form of CM Sato--Tate for the explicit projective Fermat cubic, rather than the
problem-specific fixed sector or the lower-level Hecke-character statement.
This exact CM distribution formula is not stated on Wikipedia; it is therefore
not used as the Wikipedia-auditable public endpoint.  The interval substitution
and the computation of its mass as `1 / 12` occur in the proof body.
-/
theorem erdos_979_k3_cm_sato_tate_expanded
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
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  have hST' : K3Lean.SourceSatoTate.FermatCMAngleSatoTate := by
    simpa [K3Lean.SourceSatoTate.FermatCMAngleSatoTate,
      K3Lean.PublishedInputs.primesUpTo,
      K3Lean.PublishedInputs.primeCounting,
      K3Lean.PublishedInputs.fermatFrobeniusTrace,
      K3Lean.PublishedInputs.fermatProjectivePointCount] using hST
  have hPNT' : K3Lean.SourceTheorems.OrdinaryPrimeNumberTheorem := by
    simpa [K3Lean.SourceTheorems.OrdinaryPrimeNumberTheorem,
      K3Lean.SourceTheorems.rationalPrimesUpTo] using hPNT
  exact erdos_979_k3_from_cm_sato_tate_and_pnt
    (K3Lean.SourceSatoTate.fermatCMSatoTate_of_angle_satoTate hST') hPNT'

/--
The exact Formal Conjectures target from the single weighted fixed-sector
input recorded as equation (2) by Panidapu--Thorner.  No ordinary PNT, PNT in
arithmetic progressions, Deuring interface, or Hecke-character interface is
an additional hypothesis here.
-/
theorem erdos_979_k3_from_weighted_fermat_cm_sector
    (hCM : K3Lean.SourceTheorems.PublishedFermatCMSector) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  apply formal_conjectures_limsup_of_f₃_tail_unbounded
  simpa [f₃, box, GoodCubeTriple] using
    K3Lean.ManyBlockCM.erdos_979_k3_from_weighted_cm_sector_only hCM

/--
One-input public audit surface.  The hypothesis is the literal weighted
dyadic fixed-sector limit for the Fermat cubic, with every project-specific
definition expanded.  Its natural-language source is equation (2) of
Panidapu--Thorner after taking
`I = [2*pi/3, 5*pi/6]`; the source-to-Lean statement pairing still requires
third-party review.
-/
theorem erdos_979_k3_from_single_published_input
    (hCM :
      Tendsto
        (fun X : Nat =>
          (∑ p ∈ (Finset.Ioc X (2 * X)).filter (fun p =>
              Nat.Prime p ∧ 3 < p ∧
                ((↑((p : Int) + 1 - Int.ofNat
                    (Nat.card
                        {uv : ZMod p × ZMod p //
                          1 + uv.1 ^ 3 + uv.2 ^ 3 = 0} +
                      Nat.card
                        {v : ZMod p // 1 + v ^ 3 = 0})) : Real) /
                    (2 * Real.sqrt p)) ∈
                  Set.Icc (-(Real.sqrt 3) / 2) (-(1 : Real) / 2)),
            Real.log p) / (X : Real))
        atTop (nhds ((1 : Real) / 12))) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  apply erdos_979_k3_from_weighted_fermat_cm_sector
  simpa [K3Lean.SourceTheorems.PublishedFermatCMSector,
    K3Lean.SourceTheorems.negativeCMTraceSectorWeight,
    K3Lean.SourceTheorems.negativeCMTraceSectorPrimes,
    K3Lean.PublishedInputs.normalizedFermatTrace,
    K3Lean.PublishedInputs.fermatFrobeniusTrace,
    K3Lean.PublishedInputs.fermatProjectivePointCount] using hCM

/--
The exact Formal Conjectures target with CM Sato--Tate derived, rather than
assumed, along Sutherland's Hecke--Deuring proof.
-/
theorem erdos_979_k3_from_hecke_deuring
    (theta : Nat -> Real)
    (hDeuring : forall p : Nat, Nat.Prime p -> p % 3 = 1 ->
      theta p ∈ Set.Icc 0 Real.pi /\
        (K3Lean.PublishedInputs.fermatFrobeniusTrace p : Real) =
          2 * Real.sqrt p * Real.cos (theta p))
    (hHecke :
      K3Lean.HeckeDeuringReduction.HeckeSplitAngleEquidistribution theta)
    (hAP : K3Lean.HeckeDeuringReduction.PrimeNumberTheoremModThreeOne)
    (hPNT : K3Lean.SourceTheorems.OrdinaryPrimeNumberTheorem) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  exact erdos_979_k3_from_cm_sato_tate_and_pnt
    (K3Lean.HeckeDeuringReduction.fermatCMSatoTate_of_hecke_deuring
      theta hDeuring hHecke hAP hPNT)
    hPNT

/--
The exact target with the topological cosine-Weyl step proved in Lean.
Only Deuring's CM identification, Hecke prime-character cancellation, and
the two prime-number theorems remain as mathematical source inputs.
-/
theorem erdos_979_k3_from_hecke_character_theorem
    (theta : Nat -> Real)
    (hDeuring : forall p : Nat, Nat.Prime p -> p % 3 = 1 ->
      theta p ∈ Set.Icc 0 Real.pi /\
        (K3Lean.PublishedInputs.fermatFrobeniusTrace p : Real) =
          2 * Real.sqrt p * Real.cos (theta p))
    (hHecke :
      K3Lean.HeckeCharacterCriterion.HeckePrimeCharacterCancellation theta)
    (hAP : K3Lean.HeckeDeuringReduction.PrimeNumberTheoremModThreeOne)
    (hPNT : K3Lean.SourceTheorems.OrdinaryPrimeNumberTheorem) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  exact erdos_979_k3_from_cm_sato_tate_and_pnt
    (K3Lean.HeckeCharacterCriterion.fermatCMSatoTate_of_hecke_character_theorem
      theta hDeuring K3Lean.CosineWeyl.cosineWeylCriterion hHecke hAP hPNT)
    hPNT

/--
The same endpoint with the angle parametrization derived from Hasse's theorem.
This removes the separately stated `hDeuring` argument.  All CM-specific
content is now concentrated in prime-character cancellation for the canonical
trace angle.
-/
theorem erdos_979_k3_from_hasse_and_hecke_character
    (hHasse : K3Lean.FermatHasseAngle.FermatCubicHasseBound)
    (hHecke :
      K3Lean.HeckeCharacterCriterion.HeckePrimeCharacterCancellation
        K3Lean.FermatHasseAngle.fermatTraceAngle)
    (hAP : K3Lean.HeckeDeuringReduction.PrimeNumberTheoremModThreeOne)
    (hPNT : K3Lean.SourceTheorems.OrdinaryPrimeNumberTheorem) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  exact erdos_979_k3_from_hecke_character_theorem
    K3Lean.FermatHasseAngle.fermatTraceAngle
    (K3Lean.FermatHasseAngle.split_fermatTraceAngle_data hHasse)
    hHecke hAP hPNT

/--
Public audit endpoint with every remaining mathematical hypothesis expanded.
The trace is the literal two-chart point count of the projective Fermat cubic;
no project-local definition occurs in the assumptions or conclusion.
-/
theorem erdos_979_k3_hasse_hecke_expanded
    (hHasse :
      ∀ p : Nat, Nat.Prime p → p ≠ 3 →
        abs
          (↑((p : Int) + 1 - Int.ofNat
            (Nat.card
                {uv : ZMod p × ZMod p //
                  1 + uv.1 ^ 3 + uv.2 ^ 3 = 0} +
              Nat.card
                {v : ZMod p // 1 + v ^ 3 = 0})) : Real) ≤
          2 * Real.sqrt p)
    (hHecke :
      ∀ m : Nat, 0 < m →
        Tendsto
          (fun X : Nat ↦
            (∑ p ∈ (Finset.range (X + 1)).filter
                (fun p ↦ Nat.Prime p ∧ p % 3 = 1),
              Real.cos
                ((m : Real) *
                  Real.arccos
                    ((↑((p : Int) + 1 - Int.ofNat
                        (Nat.card
                            {uv : ZMod p × ZMod p //
                              1 + uv.1 ^ 3 + uv.2 ^ 3 = 0} +
                          Nat.card
                            {v : ZMod p // 1 + v ^ 3 = 0})) : Real) /
                      (2 * Real.sqrt p)))) /
              (((Finset.range (X + 1)).filter
                (fun p ↦ Nat.Prime p ∧ p % 3 = 1)).card : Real))
          atTop (nhds 0))
    (hAP :
      Tendsto
        (fun X : Nat ↦
          (((Finset.range (X + 1)).filter
              (fun p ↦ Nat.Prime p ∧ p % 3 = 1)).card : Real) *
            Real.log X / (X : Real))
        atTop (nhds ((1 : Real) / 2)))
    (hPNT :
      Tendsto
        (fun X : Nat ↦
          (((Finset.range (X + 1)).filter Nat.Prime).card : Real) *
            Real.log X / (X : Real))
        atTop (nhds (1 : Real))) :
    Filter.limsup (fun n ↦ (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  apply erdos_979_k3_from_hasse_and_hecke_character
  · intro p hp hp3
    simpa [K3Lean.PublishedInputs.fermatFrobeniusTrace,
      K3Lean.PublishedInputs.fermatProjectivePointCount] using
      hHasse p hp hp3
  · intro m hm
    simpa [K3Lean.HeckeCharacterCriterion.cosineMoment,
      K3Lean.HeckeDeuringReduction.splitPrimesUpTo,
      K3Lean.FermatHasseAngle.fermatTraceAngle,
      K3Lean.PublishedInputs.fermatFrobeniusTrace,
      K3Lean.PublishedInputs.fermatProjectivePointCount] using
      hHecke m hm
  · simpa [K3Lean.HeckeDeuringReduction.PrimeNumberTheoremModThreeOne,
      K3Lean.HeckeDeuringReduction.splitPrimesUpTo] using hAP
  · simpa [K3Lean.SourceTheorems.OrdinaryPrimeNumberTheorem,
      K3Lean.SourceTheorems.rationalPrimesUpTo] using hPNT

/--
The exact target through the full CM Sato--Tate theorem proved from
Sutherland's Hecke--Deuring source chain.  Unlike the shorter fixed-sector
route above, this theorem first proves the complete interval distribution,
including the inert atom of mass `1 / 2` at `pi / 2`.
-/
theorem erdos_979_k3_via_full_cm_sato_tate
    (theta : Nat -> Real)
    (hDeuring : forall p : Nat, Nat.Prime p -> p % 3 = 1 ->
      theta p ∈ Set.Icc 0 Real.pi /\
        (K3Lean.PublishedInputs.fermatFrobeniusTrace p : Real) =
          2 * Real.sqrt p * Real.cos (theta p))
    (hHecke :
      K3Lean.HeckeCharacterCriterion.HeckePrimeCharacterCancellation theta)
    (hAPOne : K3Lean.HeckeDeuringReduction.PrimeNumberTheoremModThreeOne)
    (hPNT : K3Lean.SourceTheorems.OrdinaryPrimeNumberTheorem) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  have hFull : K3Lean.SourceSatoTate.FermatCMAngleSatoTate :=
    K3Lean.FullCMSatoTateFromHecke.fermatCMAngleSatoTate_of_hecke_character_theorem
        theta hDeuring K3Lean.CosineWeyl.cosineWeylCriterion
          hHecke hAPOne hPNT
  exact erdos_979_k3_from_cm_sato_tate_and_pnt
    (K3Lean.SourceSatoTate.fermatCMSatoTate_of_angle_satoTate hFull)
    hPNT

/--
Public endpoint.  Every source input is expanded; the conclusion is copied
from Formal Conjectures.  In particular, CM Sato--Tate does not occur as a
hypothesis.  The ordinary PNT hypothesis is the exact `pi_alt` statement type
paired with its natural-language statement in the PNT+ Blueprint; conversion
to this project's natural-cutoff normalization occurs in the proof body.
-/
theorem erdos_979_k3
    (theta : Nat -> Real)
    (hDeuring : forall p : Nat, Nat.Prime p -> p % 3 = 1 ->
      theta p ∈ Set.Icc 0 Real.pi /\
        (↑((p : Int) + 1 - Int.ofNat
            (Nat.card
                {uv : ZMod p × ZMod p //
                  1 + uv.1 ^ 3 + uv.2 ^ 3 = 0} +
              Nat.card
                {v : ZMod p // 1 + v ^ 3 = 0})) : Real) =
          2 * Real.sqrt p * Real.cos (theta p))
    (hHecke : forall alpha beta : Real,
      0 <= alpha -> alpha <= beta -> beta <= Real.pi ->
      Tendsto
        (fun X : Nat =>
          (((Finset.range (X + 1)).filter (fun p =>
              Nat.Prime p /\ p % 3 = 1 /\
                theta p ∈ Set.Icc alpha beta)).card : Real) /
            (((Finset.range (X + 1)).filter (fun p =>
              Nat.Prime p /\ p % 3 = 1)).card : Real))
        atTop (nhds ((beta - alpha) / Real.pi)))
    (hAP :
      Tendsto
        (fun X : Nat =>
          (((Finset.range (X + 1)).filter (fun p =>
              Nat.Prime p /\ p % 3 = 1)).card : Real) *
            Real.log X / (X : Real))
        atTop (nhds ((1 : Real) / 2)))
    (hPNT :
      ∃ c : Real → Real,
        Asymptotics.IsLittleO atTop c (fun _ => (1 : Real)) ∧
          ∀ x : Real,
            (Nat.primeCounting ⌊x⌋₊ : Real) =
              (1 + c x) * x / Real.log x) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  apply erdos_979_k3_from_hecke_deuring theta
  · intro p hp hsplit
    simpa [K3Lean.PublishedInputs.fermatFrobeniusTrace,
      K3Lean.PublishedInputs.fermatProjectivePointCount] using
      hDeuring p hp hsplit
  · intro alpha beta hAlpha hAlphaBeta hBeta
    simpa [K3Lean.HeckeDeuringReduction.splitAnglePrimesUpTo,
      K3Lean.HeckeDeuringReduction.splitPrimesUpTo,
      K3Lean.SourceTheorems.rationalPrimesUpTo, and_assoc] using
      hHecke alpha beta hAlpha hAlphaBeta hBeta
  · simpa [K3Lean.HeckeDeuringReduction.PrimeNumberTheoremModThreeOne,
      K3Lean.HeckeDeuringReduction.splitPrimesUpTo,
      K3Lean.SourceTheorems.rationalPrimesUpTo, and_assoc] using hAP
  · exact
      K3Lean.AuditedExternalStatements.ordinaryPrimeNumberTheorem_of_pntPlusPiAlt
        hPNT

#check @Erdos979.solutionSet
#check @erdos_979_k3_from_weighted_fermat_cm_sector
#print axioms erdos_979_k3_from_weighted_fermat_cm_sector
#check @erdos_979_k3_from_single_published_input
#print axioms erdos_979_k3_from_single_published_input
#check @erdos_979_k3_from_cm_sato_tate_and_pnt
#print axioms erdos_979_k3_from_cm_sato_tate_and_pnt
#check @erdos_979_k3_cm_sato_tate_expanded
#print axioms erdos_979_k3_cm_sato_tate_expanded
#check @erdos_979_k3_from_hecke_deuring
#print axioms erdos_979_k3_from_hecke_deuring
#check @erdos_979_k3_from_hecke_character_theorem
#print axioms erdos_979_k3_from_hecke_character_theorem
#check @erdos_979_k3_from_hasse_and_hecke_character
#print axioms erdos_979_k3_from_hasse_and_hecke_character
#check @erdos_979_k3_hasse_hecke_expanded
#print axioms erdos_979_k3_hasse_hecke_expanded
#check @erdos_979_k3_via_full_cm_sato_tate
#print axioms erdos_979_k3_via_full_cm_sato_tate
#check @erdos_979_k3
#print axioms erdos_979_k3

end K3Lean.FormalConjecturesTarget
