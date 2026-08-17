import Mathlib.NumberTheory.LSeries.Basic

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Audited Wiener--Ikehara statement from PrimeNumberTheorem+

This file records the type of the fully proved, Blueprint-linked theorem
`WienerIkeharaTheorem''` from PrimeNumberTheorem+.  The upstream project is on
Lean 4.31 while this project currently uses Lean 4.32-rc1, so the theorem is
kept as an explicit proposition that a public endpoint may receive as a
hypothesis.  Its mathematical content is not weakened or specialized to CM.

Natural-language/Lean audit:

* Blueprint: https://alexkontorovich.github.io/PrimeNumberTheoremAnd/blueprint/secondary-chapter.html
* Source theorem at audited commit:
  https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/6739793850d3eaa031e3543ed72d7f026f8080f5/PrimeNumberTheoremAnd/Wiener.lean#L3895-L3904
-/

namespace K3Lean.AuditedWienerIkehara

open Complex Filter Set Topology
open scoped BigOperators Topology

/-- Exact copy of the upstream absolute-convergence majorant. -/
noncomputable def nterm (f : Nat → Complex) (sigma : Real) (n : Nat) : Real :=
  if n = 0 then 0 else ‖f n‖ / n ^ sigma

/-- Exact copy of the upstream partial-sum convention. -/
def cumsum {E : Type*} [AddCommMonoid E] (u : Nat → E) (N : Nat) : E :=
  ∑ n ∈ Finset.range N, u n

/--
The full no-Chebyshev-hypothesis Wiener--Ikehara theorem proved by the
PrimeNumberTheorem+ project.  This proposition is deliberately general: it
mentions no elliptic curve, Hecke character, or Erdos problem.
-/
def PNTPlusWienerIkehara : Prop :=
  ∀ (A : Real) (G : Complex → Complex) (f : Nat → Real),
    (0 ≤ f) →
    (∀ sigma : Real, 1 < sigma →
      Summable (nterm (fun n => (f n : Complex)) sigma)) →
    ContinuousOn G {s | 1 ≤ s.re} →
    Set.EqOn G
      (fun s =>
        LSeries (fun n => (f n : Complex)) s - (A : Complex) / (s - 1))
      {s | 1 < s.re} →
    Tendsto (fun N => cumsum f N / (N : Real)) atTop (nhds A)

#check PNTPlusWienerIkehara

end K3Lean.AuditedWienerIkehara
