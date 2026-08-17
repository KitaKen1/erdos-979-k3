import K3Lean.FormalConjecturesTarget

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Bridges from the two fixed CM statement files to #979, k = 3

`ProposedFermatCubicCMSatoTate` and `ProposedFermatCubicCMSector` repeat,
byte for byte, the statements of the two theorems recorded, in Formal
Conjectures house style, in the local statement files

* `FormalConjectures/Arxiv/1506.09170/FermatCubicCMSatoTate.lean`
  (Chen--Park--Swaminathan, displayed Sato--Tate law, CM case, at the
  projective Fermat cubic);
* `FormalConjectures/Arxiv/2105.11093/FermatCubicCMSector.lean`
  (Panidapu--Thorner, equation (2), specialized to `I = [2π/3, 5π/6]`).

These files fix the statement text for third-party statement review; no
pull request to the Formal Conjectures repository is planned.

Each endpoint below proves the exact Formal Conjectures target for Erdős
problem 979, `k = 3`, from one fixed statement together with, in the
Sato--Tate case, the exact PNT+ Blueprint statement type `pi_alt`.

Audit surface: the conclusion and the PNT input already carry third-party
natural-language/Lean pairings (Formal Conjectures pinned commit, PNT+
Blueprint); the single CM hypothesis is one short fixed text; and every
derivation in between is checked by the Lean kernel.  No re-audit of any
proof is ever required.
-/

namespace K3Lean.FormalConjecturesProposalBridge

open Filter

noncomputable section

/--
Byte-identical copy of the statement of
`Arxiv.«1506.09170».sato_tate_cm_fermat_cubic` in the proposal file
`FormalConjectures/Arxiv/1506.09170/FermatCubicCMSatoTate.lean`.
-/
def ProposedFermatCubicCMSatoTate : Prop :=
    ∃ theta : ℕ → ℝ,
      (∀ p : ℕ, Nat.Prime p → p ≠ 3 →
        theta p ∈ Set.Icc 0 Real.pi ∧
          (↑((p : ℤ) + 1 - Int.ofNat
              (Nat.card
                  {uv : ZMod p × ZMod p //
                    1 + uv.1 ^ 3 + uv.2 ^ 3 = 0} +
                Nat.card
                  {v : ZMod p // 1 + v ^ 3 = 0})) : ℝ) =
            2 * Real.sqrt p * Real.cos (theta p)) ∧
      ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ Real.pi →
        Filter.Tendsto
          (fun x : ℝ =>
            (((((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).filter
                  (fun p => p ≠ 3 ∧ theta p ∈ Set.Icc α β)).card : ℝ) /
              (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ)))
          Filter.atTop
          (nhds ((if Real.pi / 2 ∈ Set.Icc α β then (1 : ℝ) else 0) / 2 +
            (β - α) / (2 * Real.pi)))

/--
Byte-identical copy of the statement of
`Arxiv.«2105.11093».fermat_cubic_cm_sector` in the proposal file
`FormalConjectures/Arxiv/2105.11093/FermatCubicCMSector.lean`.
-/
def ProposedFermatCubicCMSector : Prop :=
    Filter.Tendsto
      (fun X : ℕ =>
        (∑ p ∈ (Finset.Ioc X (2 * X)).filter (fun p =>
            Nat.Prime p ∧ 3 < p ∧
              ((↑((p : ℤ) + 1 - Int.ofNat
                  (Nat.card
                      {uv : ZMod p × ZMod p //
                        1 + uv.1 ^ 3 + uv.2 ^ 3 = 0} +
                    Nat.card
                      {v : ZMod p // 1 + v ^ 3 = 0})) : ℝ) /
                  (2 * Real.sqrt p)) ∈
                Set.Icc (-(Real.sqrt 3) / 2) (-(1 : ℝ) / 2)),
          Real.log p) / (X : ℝ))
      Filter.atTop (nhds ((1 : ℝ) / 12))

/--
The exact Formal Conjectures target for Erdős 979, `k = 3`, from the
proposed fixed-sector statement alone.  No prime number theorem, Hasse
bound, or Hecke input is an additional hypothesis.
-/
theorem erdos_979_k3_from_proposed_cm_sector
    (hCM : ProposedFermatCubicCMSector) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ :=
  K3Lean.FormalConjecturesTarget.erdos_979_k3_from_single_published_input hCM

/--
The exact Formal Conjectures target for Erdős 979, `k = 3`, from the
proposed CM Sato--Tate law together with the exact PNT+ Blueprint
statement type `pi_alt` (Corollary 6.0.2 there).
-/
theorem erdos_979_k3_from_proposed_cm_sato_tate_and_pnt_plus
    (hST : ProposedFermatCubicCMSatoTate)
    (hPNT : K3Lean.AuditedExternalStatements.PNTPlusPiAlt) :
    Filter.limsup (fun n => (Erdos979.solutionSet n 3).encard)
      Filter.atTop = ⊤ := by
  have hPNT' : K3Lean.SourceTheorems.OrdinaryPrimeNumberTheorem :=
    K3Lean.AuditedExternalStatements.ordinaryPrimeNumberTheorem_of_pntPlusPiAlt
      hPNT
  refine K3Lean.FormalConjecturesTarget.erdos_979_k3_cm_sato_tate_expanded
    ?_ ?_
  · exact hST
  · simpa [K3Lean.SourceTheorems.OrdinaryPrimeNumberTheorem,
      K3Lean.SourceTheorems.rationalPrimesUpTo] using hPNT'

#check @ProposedFermatCubicCMSatoTate
#check @ProposedFermatCubicCMSector
#check @erdos_979_k3_from_proposed_cm_sector
#print axioms erdos_979_k3_from_proposed_cm_sector
#check @erdos_979_k3_from_proposed_cm_sato_tate_and_pnt_plus
#print axioms erdos_979_k3_from_proposed_cm_sato_tate_and_pnt_plus

end

end K3Lean.FormalConjecturesProposalBridge
