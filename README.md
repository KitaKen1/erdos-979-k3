# A Lean proof of Erdős Problem 979 for k = 3

This repository formalizes a complete solution to the `k = 3` target registered in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/b2e608fc52d765510915a244bb69b1a2741acc3c/FormalConjectures/ErdosProblems/979.lean).
If `f₃(n)` counts the representations of `n` as a sum of three prime cubes, then

```text
limsup f₃(n) = ∞.
```

Equivalently, there are integers with arbitrarily many representations as a sum of three
prime cubes.

**Try it in Lean4Web:**
[open the latest standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos-979-k3%2Frefs%2Fheads%2Fmain%2Flean4web%2FErdos979Lean4WebLatest.lean).
The file is about 25,700 lines, so checking it locally with `lake build` is usually faster.

This solves the exact `k = 3` statement in Formal Conjectures. It does **not** address the
other `k` variants of [Erdős Problem 979](https://www.erdosproblems.com/979), or give a
quantitative growth rate for `f₃`.

## Formal Conjectures target

The formalized counting function is

```lean
def solutionSet (n k : ℕ) : Set (Multiset ℕ) :=
  {P | P.card = k ∧ (∀ p ∈ P, Nat.Prime p) ∧ n = (P.map (. ^ k)).sum}
```

and the final theorem is

```lean
theorem erdos_979.variants.k3 :
    Filter.limsup (fun n => (solutionSet n 3).encard) Filter.atTop = ⊤
```

These are copied character-for-character from Formal Conjectures at pinned commit
[`b2e608f`](https://github.com/google-deepmind/formal-conjectures/blob/b2e608fc52d765510915a244bb69b1a2741acc3c/FormalConjectures/ErdosProblems/979.lean).
The upstream project is pinned to Lean `v4.27.0`, while this proof uses Lean `v4.31.0`, so
Formal Conjectures is not imported as a build dependency. The comparison in
[`audit.sh`](audit.sh) mechanically checks that the local definition and theorem statement
agree with the pinned source.

## Mathematical explanation (AI generated)

The proof follows the classical complex-multiplication approach for the Fermat cubic.

First, the projective curve

```text
X³ + Y³ + Z³ = 0
```

is counted over `𝔽_p`. When `p ≡ 1 (mod 3)`, its point count is expressed using the cubic
Jacobi sum `J(χ, χ)`, whose absolute value is `√p`. When `p ≡ 2 (mod 3)`, cubing is a
bijection and the point count is exactly `p + 1`. This gives the required Hasse bound
without any external hypotheses.

Next, primary elements of the Eisenstein integers `ℤ[ω]` encode the Hecke angles of the
Fermat cubic. Lattice-point counting, rotation symmetry, and thin-annulus estimates produce
Dirichlet-series models for the relevant powers of the Hecke coefficients.

The analytic step applies the Wiener–Ikehara Tauberian theorem together with the prime number
theorem in the progression `1 mod 3`. These two results come from
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd).

Finally, the analytic estimates give an unbounded number of suitable prime triples along a
subsequence. An injection from sorted prime triples to multisets transfers this result to the
literal Formal Conjectures `solutionSet` statement.

## Files

| Directory or file | Lean version | Purpose |
|---|---:|---|
| [`lean/`](lean/) | `v4.31.0` | Full modular proof: 52 project modules, Mathlib `db12779`, and PrimeNumberTheoremAnd `6739793` |
| [`lean4web/Erdos979Lean4WebLatest.lean`](lean4web/Erdos979Lean4WebLatest.lean) | `v4.34.0-rc1` | Unconditional standalone proof ported to current Mathlib APIs for Lean4Web |

Both versions discharge the analytic inputs and prove the theorem without hypotheses.

## Verification

Full modular proof:

```bash
cd lean
lake exe cache get
lake build
```

Latest-Mathlib standalone proof:

```bash
cd lean4web
lake exe cache get
lake build
```

The unconditional builds end with the kernel axiom audit

```text
'Erdos979.erdos_979.variants.k3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Thus the final theorem depends only on Lean's standard axioms; in particular, it does not
depend on `sorryAx` or any custom axiom.

## Status boundary

What is solved here:

```text
The number of representations of n as a sum of three prime cubes
is unbounded as n varies.
```

What remains open here:

```text
The other k variants of Erdős Problem 979, and quantitative lower bounds
for the growth of the representation count.
```

## Sources

- [Erdős Problem 979](https://www.erdosproblems.com/979)
- [Formal Conjectures: `ErdosProblems/979.lean`](https://github.com/google-deepmind/formal-conjectures/blob/b2e608fc52d765510915a244bb69b1a2741acc3c/FormalConjectures/ErdosProblems/979.lean)
- [Mathlib](https://github.com/leanprover-community/mathlib4)
- [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
- A. Panidapu and J. Thorner, *involve* 16 (2023), the mathematical blueprint for the CM argument

## AI usage disclosure

This formalization was developed with assistance from OpenAI Codex, Fable5, and Claude Code.

## Appendix: Historical background (AI generated)

Erdős Problem 979 is traced to a 1965 source of Paul Erdős. The problem asks, for every
`k ≥ 2`, whether the number of representations of an integer as a sum of `k` prime `k`-th
powers is unbounded. The [Erdős Problems record](https://www.erdosproblems.com/forum/thread/979)
reports that Erdős proved the case `k = 2` and stated that he could also prove `k = 3`, while
describing the latter proof as unpublished and as requiring special properties of primes.

No text of Erdős's `k = 3` proof is presently cited in the public record. Consequently, this
repository does not claim to reconstruct Erdős's argument, and it is not known whether he used
anything resembling the complex-multiplication and Hecke-theoretic route formalized here. The
correctness and precise scope of the unpublished argument also cannot be assessed from the
available published material.

The route used in this repository instead belongs to the modern theory of CM elliptic curves.
It studies the Fermat cubic through cubic characters, Jacobi sums, Eisenstein integers, Hecke
coefficients, and prime-distribution results. A modern reference for the relevant CM sector
distribution is A. Panidapu and J. Thorner,
[“Short-interval sector problems for CM elliptic curves”](https://doi.org/10.2140/involve.2023.16.1),
*Involve* 16 (2023), 1–12. This paper supplies mathematical context for the approach; it is not
itself presented here as a proof of Erdős Problem 979.

The exact multiset-valued `k = 3` statement was later included in Google's
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) benchmark. The
present project proves that literal Lean statement and should therefore be understood as an
independent, kernel-checked solution, not as a formal transcription of Erdős's unpublished
proof.
