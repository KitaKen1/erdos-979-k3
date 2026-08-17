import K3Lean.HeckeBoundaryFinal
import K3Lean.HeckeModels
import K3Lean.PNTImports

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Erdős Problem 979, `k = 3`: the unconditional theorem

*Reference:* [erdosproblems.com/979](https://www.erdosproblems.com/979)

The statement and the definition `Erdos979.solutionSet` follow the Formal
Conjectures repository
(`FormalConjectures/ErdosProblems/979.lean`, theorem `erdos_979.variants.k3`).

All four inputs of the kernel-checked reduction
`K3Lean.HeckeBoundaryFinal.erdos_979_k3_from_fermat_dirichlet_models` are now
theorems:

* the Hasse bound for the Fermat cubic (`K3Lean.CubicJacobi`, via Jacobi
  sums);
* the Wiener--Ikehara theorem (PrimeNumberTheorem+, `WienerIkeharaTheorem''`);
* the three Dirichlet models for the Fermat Hecke powers
  (`K3Lean.HeckeModels`, via primary Eisenstein lattice sums);
* the prime number theorem in the progression `1 mod 3`
  (PrimeNumberTheorem+, `chebyshev_asymptotic_pnt`, converted).
-/

namespace Erdos979

/--
Erdős (unpublished); cf. Panidapu--Thorner, *involve* 16 (2023).

If $f_3(n)$ counts the number of solutions to $n = p_1^3 + p_2^3 + p_3^3$,
where the $p_i$ are prime numbers, then $\limsup f_3(n) = \infty$.
-/
theorem erdos_979.variants.k3 :
    Filter.limsup (fun n => (solutionSet n 3).encard) Filter.atTop = ⊤ := by
  exact K3Lean.HeckeBoundaryFinal.erdos_979_k3_from_fermat_dirichlet_models
    K3Lean.CubicJacobi.fermat_hasse_bound
    K3Lean.PNTImports.pntPlusWienerIkehara
    K3Lean.HeckeModels.fermatRequiredDirichletModels
    K3Lean.PNTImports.primeNumberTheoremModThreeOne

#check @erdos_979.variants.k3
#print axioms erdos_979.variants.k3

end Erdos979
