# A Lean proof of Erdős Problem 979 for k = 3

This repository formalizes a complete solution to the `k = 3` target registered in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/b2e608fc52d765510915a244bb69b1a2741acc3c/FormalConjectures/ErdosProblems/979.lean).

Try it in Lean4Web: [Open the standalone proof in Lean4Web](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos-979-k3%2Frefs%2Fheads%2Fmain%2Flean4web%2FErdos979Lean4WebLatest.lean)

If `f₃(n)` counts the representations of `n` as a sum of three prime cubes, then

```text
limsup f₃(n) = ∞.
```

Equivalently, there are integers with arbitrarily many representations as a sum of three
prime cubes.

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

## Appendix 1: Historical background (AI generated)

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

## Appendix 2: Major theorem table (AI generated)

`Source URL` points to mathematical literature, while `Lean source` points to the formal
code. A source marked as background gives the surrounding mathematical theory but does not
claim to contain the exact project-specific statement.

| Mathematical statement | Lean statement | Lean source | Source URL |
|---|---|---|---|
| **Theorem (Wiener–Ikehara).**<br>Let $f:\mathbb N\to\mathbb R_{\geq0}$ and $D(s)=\sum_{n\geq1}f(n)n^{-s}$. If $D$ converges absolutely for $\mathrm{Re}s>1$ and $D(s)-A/(s-1)$ extends continuously to $\mathrm{Re}s\geq1$, then $N^{-1}\sum_{n<N}f(n)\to A$. | <pre><code>theorem&#10;pntPlusWienerIkehara :&#10;PNTPlusWienerIkehara</code></pre> | [Upstream theorem](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/6739793850d3eaa031e3543ed72d7f026f8080f5/PrimeNumberTheoremAnd/Wiener.lean#L3895-L3904); [project wrapper](https://github.com/KitaKen1/erdos-979-k3/blob/main/lean/K3Lean/PNTImports.lean#L30-L33) | [Ikehara (1931), *An Extension of Landau's Theorem in the Analytical Theory of Numbers*](https://doi.org/10.1002/sapm19311011); [mathematical blueprint](https://alexkontorovich.github.io/PrimeNumberTheoremAnd/blueprint/wiener-ikehara-chapter.html) |
| **Theorem (Euclideanity of the Eisenstein integers).**<br>For $\alpha,\beta\in\mathbb Z[\omega]$ with $\beta\neq0$, there are $q,r\in\mathbb Z[\omega]$ such that $\alpha=q\beta+r$ and $N(r)<N(\beta)$. Hence $\mathbb Z[\omega]$ is a Euclidean domain. | <pre><code>instance :&#10;EuclideanDomain Eis&#10;where&#10;quotient := ediv&#10;remainder := emod&#10;...</code></pre> | [`EisensteinRing.lean`](https://github.com/KitaKen1/erdos-979-k3/blob/main/lean/K3Lean/EisensteinRing.lean#L393-L407) | [Garrett, *Factorization and zeta functions*, §2.3](https://www-users.cse.umn.edu/~garrett/m/mfms/notes_c/factorization_zetas.pdf) |
| **Theorem (Unique primary associate).**<br>If $\alpha\in\mathbb Z[\omega]$ and $3\nmid N(\alpha)$, then there is a unique associate $\beta$ of $\alpha$ satisfying $\beta\equiv1\pmod 3$. | <pre><code>theorem&#10;exists_&#10;unique_&#10;primary_&#10;associate&#10;{α : Eis} (h : ¬ (3 ∣&#10;natNorm α)) :&#10;∃! β : Eis, Associated&#10;α β ∧ Primary β</code></pre> | [`EisensteinRing.lean`](https://github.com/KitaKen1/erdos-979-k3/blob/main/lean/K3Lean/EisensteinRing.lean#L601-L603) | [Fløystad, *A tour of the Eisenstein integers*](https://rasmusfl.github.io/Documents/EI.pdf) (the opposite primary-sign convention is used there) |
| **Theorem (Hasse bound for the Fermat cubic).**<br>For a prime $p\neq3$, let $E/\mathbb F_p$ be $X^3+Y^3+Z^3=0$ and $a_p=p+1-\lvert E(\mathbb F_p)\rvert$. Then $\lvert a_p\rvert\leq2\sqrt p$. | <pre><code>theorem&#10;fermat_&#10;hasse_&#10;bound :&#10;K3Lean.&#10;FermatHasseAngle.&#10;FermatCubicHasseBound</code></pre> | [`CubicJacobi.lean`](https://github.com/KitaKen1/erdos-979-k3/blob/main/lean/K3Lean/CubicJacobi.lean#L739-L770) | [Sutherland, *Elliptic Curves*, Lecture 1](https://math.mit.edu/classes/18.783/2023/LectureSlides1.pdf); [Doliskani–Schost, *A remark on the computation of cube roots in finite fields*](https://eprint.iacr.org/2009/457.pdf) |
| **Theorem (Square-root cancellation in the primary Eisenstein lattice).**<br>For $3\nmid m$, let $A_m(N)$ be the sum of $(\alpha/\lvert\alpha\rvert)^m$ over primary Eisenstein integers $\alpha$ with $1\leq N(\alpha)\leq N$. Then $A_m(N)=O(N^{1/2})$. | <pre><code>theorem&#10;primary_&#10;sum_&#10;isBigO&#10;(m : ℕ)&#10;(hm : ¬ (3 ∣ m)) :&#10;(fun N ↦ ...)&#10;=O[atTop]&#10;(fun N ↦ (N : ℝ) ^ (1&#10;/ 2 : ℝ))</code></pre> | [`PrimaryDiskBound.lean`](https://github.com/KitaKen1/erdos-979-k3/blob/main/lean/K3Lean/PrimaryDiskBound.lean#L1765-L1785) | [Panidapu–Thorner, *Short-interval sector problems for CM elliptic curves*](https://arxiv.org/abs/2105.11093) (Hecke/CM background; no exact external statement identified) |
| **Theorem (Removal of logarithmic weights).**<br>If $c(n)$ is bounded and $x^{-1}\sum_{p\leq x}c(p)\log p\to0$, then $(\log x/x)\sum_{p\leq x}c(p)\to0$. | <pre><code>theorem&#10;unweightedPrimeSum_&#10;normalized_&#10;tendsto_&#10;zero&#10;(hWeighted : Tendsto&#10;(fun x ↦&#10;weightedPrimeSum c x /&#10;x)&#10;atTop (nhds 0)) :&#10;Tendsto&#10;(fun x ↦&#10;unweightedPrimeSum c x&#10;/ (x / Real.&#10;log x))&#10;atTop (nhds 0)</code></pre> | [`LogWeightRemoval.lean`](https://github.com/KitaKen1/erdos-979-k3/blob/main/lean/K3Lean/LogWeightRemoval.lean#L176-L184) | [Knill, *Basics on Dirichlet Series*](https://abel.math.harvard.edu/~knill/kam/papers/dirichlet/index.html) (Abel summation; the exact normalized lemma is local) |
| **Theorem (Prime number theorem for $1$ modulo $3$).**<br>If $\pi_{1\,(\mathrm{mod}\,3)}(X)$ counts primes $p\leq X$ with $p\equiv1\pmod3$, then $\pi_{1\,(\mathrm{mod}\,3)}(X)\sim X/(2\log X)$. | <pre><code>theorem&#10;primeNumberTheorem&#10;ModThreeOne :&#10;K3Lean.&#10;HeckeDeuringReduction.&#10;PrimeNumberTheorem&#10;ModThreeOne</code></pre> | [`PNTImports.lean`](https://github.com/KitaKen1/erdos-979-k3/blob/main/lean/K3Lean/PNTImports.lean#L171-L180) | [Selberg (1950), *An Elementary Proof of the Prime-Number Theorem for Arithmetic Progressions*](https://doi.org/10.4153/CJM-1950-008-1); [mathematical blueprint](https://alexkontorovich.github.io/PrimeNumberTheoremAnd/blueprint/corollaries-chapter.html) |
| **Theorem (Abel–Mellin continuation).**<br>If $A(N)=\sum_{n\leq N}f(n)=O(N^r)$ with $r\geq0$, then $F(s)=s\int_1^\infty A(x)x^{-s-1}\,dx$ is holomorphic for $\mathrm{Re}s>r$. | <pre><code>theorem&#10;differentiableOn_&#10;abelMellinContinuation&#10;(h : PartialSumBigO f&#10;r)&#10;(hr0 : 0 ≤ r) :&#10;DifferentiableOn ℂ&#10;(abelMellinContinuation&#10;f)&#10;{s : ℂ &#124; r &lt; s.&#10;re}</code></pre> | [`AbelMellinContinuation.lean`](https://github.com/KitaKen1/erdos-979-k3/blob/main/lean/K3Lean/AbelMellinContinuation.lean#L129-L136) | [Knill, *Basics on Dirichlet Series*](https://abel.math.harvard.edu/~knill/kam/papers/dirichlet/index.html) (Abel–Cahen background; the exact formulation is local) |
| **Theorem (Agreement with the Dirichlet series).**<br>Under the preceding hypotheses, if $\mathrm{Re}s>r$ and $\sum_{n\geq1}f(n)n^{-s}$ converges, then $F(s)=\sum_{n\geq1}f(n)n^{-s}$. | <pre><code>theorem&#10;abelMellinContinuation_&#10;eq_&#10;LSeries&#10;(h : PartialSumBigO f&#10;r)&#10;(hr0 : 0 ≤ r)&#10;(hs : r &lt; s.&#10;re)&#10;(hSummable :&#10;LSeriesSummable f s) :&#10;abelMellinContinuation&#10;f s =&#10;LSeries f s</code></pre> | [`AbelMellinContinuation.lean`](https://github.com/KitaKen1/erdos-979-k3/blob/main/lean/K3Lean/AbelMellinContinuation.lean#L138-L144) | [Knill, *Basics on Dirichlet Series*](https://abel.math.harvard.edu/~knill/kam/papers/dirichlet/index.html) (Abel–Cahen background; the exact agreement theorem is local) |
| **Theorem (Euler identity for the Fermat Hecke coefficients).**<br>Let $a_m(n)$ be the sum of $(\alpha/\lvert\alpha\rvert)^m$ over primary $\alpha$ of norm $n$. If $3\nmid m$ and $\mathrm{Re}s>1$, the Dirichlet series of $a_m$ equals the explicit Fermat Hecke Euler product $L_{\mathrm{Fermat},m}(s)$. | <pre><code>theorem&#10;heckeCoeff_&#10;LSeries_&#10;eq&#10;(m : ℕ)&#10;(hm : ¬ (3 ∣ m))&#10;(hs : 1 &lt; s.&#10;re) :&#10;LSeries (heckeCoeff m)&#10;s =&#10;explicitFermatPowerL&#10;fermatTraceAngle m s</code></pre> | [`HeckeModels.lean`](https://github.com/KitaKen1/erdos-979-k3/blob/main/lean/K3Lean/HeckeModels.lean#L597-L600) | [Panidapu–Thorner, *Short-interval sector problems for CM elliptic curves*](https://arxiv.org/abs/2105.11093) (Hecke/CM background; the exact identity is local) |
| **Theorem (Dirichlet models for the required Fermat Hecke powers).**<br>For every $m\in\{1,2,4\}$ there is a sequence $a_m(n)$ with partial sums $O(N^{1/2})$ whose Dirichlet series equals $L_{\mathrm{Fermat},m}(s)$ for $\mathrm{Re}s>1$. | <pre><code>theorem&#10;fermatRequired&#10;DirichletModels :&#10;FermatRequired&#10;DirichletModels&#10;fermatTraceAngle</code></pre> | [`HeckeModels.lean`](https://github.com/KitaKen1/erdos-979-k3/blob/main/lean/K3Lean/HeckeModels.lean#L784-L794) | [Panidapu–Thorner, *Short-interval sector problems for CM elliptic curves*](https://arxiv.org/abs/2105.11093) (Hecke/CM background; the simultaneous models are local) |
| **Theorem (Dirichlet-model criterion for Erdős 979, $k=3$).**<br>The Fermat-cubic Hasse bound, Wiener–Ikehara theorem, required Fermat Hecke Dirichlet models, and the PNT for $1$ modulo $3$ imply $\limsup_{n\to\infty}\lvert S_3(n)\rvert=\infty$. | <pre><code>theorem&#10;erdos_&#10;979_&#10;k3_&#10;from_&#10;fermat_&#10;dirichlet_&#10;models&#10;(hHasse :&#10;FermatCubicHasseBound)&#10;(hWI :&#10;PNTPlusWienerIkehara)&#10;(hModels :&#10;FermatRequired&#10;DirichletModels&#10;fermatTraceAngle)&#10;(hAP :&#10;PrimeNumberTheorem&#10;ModThreeOne)&#10;:&#10;Filter.&#10;limsup&#10;(fun n ↦ (Erdos979.&#10;solutionSet n 3).&#10;encard) Filter.&#10;atTop =&#10;⊤</code></pre> | [`HeckeBoundaryFinal.lean`](https://github.com/KitaKen1/erdos-979-k3/blob/main/lean/K3Lean/HeckeBoundaryFinal.lean#L144-L157) | [Erdős (1965), *Some Recent Advances and Current Problems in Number Theory*](https://www.renyi.hu/~p_erdos/1965-17.pdf); [Panidapu–Thorner, CM/Hecke background](https://arxiv.org/abs/2105.11093) (project-specific reduction; no exact external statement identified) |
| **Theorem (Erdős 979 for $k=3$).**<br>If $S_3(n)$ is the set of three-element prime multisets whose cubes sum to $n$, then $\limsup_{n\to\infty}\lvert S_3(n)\rvert=\infty$. Erdős stated that this case could be proved, but his proof appears to be unpublished. | <pre><code>theorem&#10;erdos_&#10;979.&#10;variants.&#10;k3 :&#10;Filter.&#10;limsup&#10;(fun n ↦ (solutionSet&#10;n 3).&#10;encard) Filter.&#10;atTop =&#10;⊤</code></pre> | [`Erdos979K3Final.lean`](https://github.com/KitaKen1/erdos-979-k3/blob/main/lean/K3Lean/Erdos979K3Final.lean#L38-L44) | [Erdős (1965), *Some Recent Advances and Current Problems in Number Theory*, p. 224](https://www.renyi.hu/~p_erdos/1965-17.pdf); [Erdős Problems, Problem 979](https://www.erdosproblems.com/979) |
