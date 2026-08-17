/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Authors: Kenta Kitamura, OpenAI Codex
-/

import K3Lean.SourceTheorems

/-!
# Third-party-audited external statement types

This file copies statement types whose natural-language/Lean correspondence is
displayed by an external Blueprint.  Whether the external declaration has a
completed proof body is deliberately not part of this interface.

Source:
https://alexkontorovich.github.io/PrimeNumberTheoremAnd/blueprint/corollaries-chapter.html

* Corollary 6.0.2, `pi_alt`:
  `pi(x) = (1 + o(1)) x / log x`.
* Theorem 6.1.1, `chebyshev_asymptotic_pnt`:
  `sum_{p <= x, p = a (q)} log p = x / phi(q) + o(x)`.

The definitions below retain the source declaration types.  Project-specific
normalization changes belong in proved adapters after the theorem hypotheses.
-/

namespace K3Lean.AuditedExternalStatements

open Filter Asymptotics
open K3Lean.SourceTheorems
open scoped BigOperators

noncomputable section

/-- Exact statement type of the PNT+ Blueprint declaration `pi_alt`. -/
def PNTPlusPiAlt : Prop :=
  ∃ c : Real → Real,
    c =o[atTop] (fun _ => (1 : Real)) ∧
      ∀ x : Real,
        (Nat.primeCounting ⌊x⌋₊ : Real) =
          (1 + c x) * x / Real.log x

/--
Exact statement type of the PNT+ Blueprint declaration
`chebyshev_asymptotic_pnt`.
-/
def PNTPlusChebyshevPNTInAP : Prop :=
  ∀ {q a : Nat},
    q ≥ 1 → a.Coprime q → a < q →
      (fun x : Real =>
          ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
            if p % q = a then Real.log p else 0) ~[atTop]
        (fun x : Real => x / (q.totient : Real))

/--
The PNT+ real-cutoff `pi_alt` statement implies the natural-cutoff
normalization used by the block proof.
-/
theorem ordinaryPrimeNumberTheorem_of_pntPlusPiAlt
    (h : PNTPlusPiAlt) : OrdinaryPrimeNumberTheorem := by
  rcases h with ⟨c, hc, hpi⟩
  have hc0 : Tendsto c atTop (nhds 0) :=
    (isLittleO_one_iff Real).mp hc
  have hcNat : Tendsto (fun n : Nat => c n) atTop (nhds 0) :=
    hc0.comp tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun n : Nat => 1 + c n) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hcNat
  rw [OrdinaryPrimeNumberTheorem]
  apply hone.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n : Real) ≠ 0 := by positivity
  have hlog : Real.log (n : Real) ≠ 0 := by
    exact Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by norm_num; omega)
  simp only [rationalPrimesUpTo]
  rw [show ((Finset.range (n + 1)).filter Nat.Prime).card =
      Nat.primeCounting n by
    simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]]
  rw [show (Nat.primeCounting n : Real) =
      (1 + c n) * n / Real.log n by
    simpa using hpi (n : Real)]
  field_simp

#check @PNTPlusPiAlt
#check @PNTPlusChebyshevPNTInAP
#check @ordinaryPrimeNumberTheorem_of_pntPlusPiAlt

end

end K3Lean.AuditedExternalStatements
