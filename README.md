# Subpolynomial $n^{4/3} \exp(O((\log n / \log \log n)^{2/3}))$ Upper Bound for Erdős Problem #711 in Lean 4

> **Scope note:** **Erdős Problem #711 (Part A: $\max_m f(n, m) \le n^{1+o(1)}$) remains open.** This repository formalizes an incremental improvement to the subpolynomial error factor in the $n^{4/3}$ upper bound of Chen and Korsky (`arXiv:2607.26450`, July 2026), reducing $\exp(O(\log n / \log \log n))$ to $\exp(O((\log n / \log \log n)^{2/3}))$, together with a self-contained Lean 4 proof of $h_P(n) \le C n^{4/3}$ for Erdős Problem #860 (primes; note that Chen and Korsky's paper proves the stronger $h_P(n) \ll n^{4/3} / (\log n)^{1/3}$).

## Overview

For integers $n \ge 1$ and $m \ge 0$, let $f(n, m)$ denote the least $L$ such that $(m, m + L)$ contains pairwise distinct multiples $a_k$ ($k \mid a_k$) for all $1 \le k \le n$, and let $f_{\mathrm{closed}}(n, m)$ denote the corresponding least $h$ for $(m, m + h]$. Let $h_P(n)$ denote the analogous supremum over $m$ restricted to primes $p \le n$.

Chen and Korsky (`arXiv:2607.26450`, July 2026) proved $F(n) := \sup_m f(n, m) \le n^{4/3} \exp(O(\log n / \log \log n))$ and $h_P(n) \ll n^{4/3} / (\log n)^{1/3}$. The formalization in [`RHDirect/PPL173_WorldRecordFourThirds.lean`](RHDirect/PPL173_WorldRecordFourThirds.lean) establishes the improved subpolynomial factor:

$$
\sup_{m \in \mathbb{N}} f(n, m) \le n^{4/3} \exp\!\left(C \left(\frac{\log n}{\log \log n}\right)^{2/3}\right) \qquad (n \ge 16)
$$

for an explicit absolute constant $C > 0$, along with the $n^{4/3 + \varepsilon}$ corollary for all $\varepsilon > 0$ and $n \ge 1$, and a self-contained Lean 4 proof of $h_P(n) \le C n^{4/3}$ for all $n \ge 1$.

## Exported Theorem Statements

All top-level theorems in `namespace PPL173FourThirds` ([`RHDirect/PPL173_WorldRecordFourThirds.lean`](RHDirect/PPL173_WorldRecordFourThirds.lean)) are stated directly in terms of Mathlib `⨆` and `sInf` on `Set ℕ`, with zero custom masking definitions. Both nonemptiness of each `sInf` set and `BddAbove` for every `⨆ m` range are proved unconditionally (internally via trivial $n^2$ / $n^2 + 1$ witnesses inside each proof), so no supremum or infimum is vacuous.

```lean
theorem ppl173_world_record_four_thirds_iSup :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 16 ≤ n →
      (⨆ m : ℕ, ((sInf ({ L : ℕ | ∃ a : ℕ → ℕ,
        (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
        (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k < m + L ∧ k ∣ a k) } : Set ℕ) : ℕ) : ℝ))
        ≤ (n : ℝ) ^ ((4 : ℝ) / 3) *
            Real.exp (C * (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) ^ ((2 : ℝ) / 3))

theorem ppl173_world_record_four_thirds_closed_iSup :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 16 ≤ n →
      (⨆ m : ℕ, ((sInf ({ h : ℕ | ∃ a : ℕ → ℕ,
        (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
        (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k ≤ m + h ∧ k ∣ a k) } : Set ℕ) : ℕ) : ℝ))
        ≤ (n : ℝ) ^ ((4 : ℝ) / 3) *
            Real.exp (C * (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) ^ ((2 : ℝ) / 3))

theorem ppl173_four_thirds_plus_eps (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (⨆ m : ℕ, ((sInf ({ L : ℕ | ∃ a : ℕ → ℕ,
        (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
        (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k < m + L ∧ k ∣ a k) } : Set ℕ) : ℕ) : ℝ))
        ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3 + ε)

theorem ppl173_erdos860_primes_four_thirds :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (⨆ m : ℕ, ((sInf ({ h : ℕ | ∃ a : ℕ → ℕ,
        (∀ p q, p ≤ n → p.Prime → q ≤ n → q.Prime → a p = a q → p = q) ∧
        (∀ p, p ≤ n → p.Prime → m < a p ∧ a p ≤ m + h ∧ p ∣ a p) } : Set ℕ) : ℕ) : ℝ))
        ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3)
```

## Proof Summary

The formalization is self-contained over Mathlib (`0df444a360eaa60ab8c11dca51a86af692955474`) using three elementary ingredients:

1. **Refined superset 3-path modular reflection (`lemma_A_three_path_reflection`):** A modular reflection inequality with explicit constant $1 + \sqrt{2}$, valid for any superset $U \supseteq \bigcup_{d \in D} S_d$, bounding $|S|$ in terms of $|U|$, the bucket upper scale $M$, and the interval length $\ell$.
2. **Uniform $|U|$-elimination Hall partition (`lemma_B_uniform_single`, `lemma_B_uniform_hall_partition`):** Verifies Hall's marriage condition uniformly across all subset sizes $|U| \in [1, n]$ whenever $\sum_\alpha \kappa_\alpha^{2/3} M_\alpha^{1/3} / \ell_\alpha \le 1/10$ and $\sum_\alpha 1 / \ell_\alpha \le 1/10$.
3. **Polynomial divisor bound and constant-1 joint Euler-product Rankin trick:** Combines the exact big-Omega divisor count bound $\#\{d \mid t : \Omega(d) = k\} \le \binom{\Omega(t)}{k}$ (`lemma_C1_divisors_bigOmega_le_choose`) with a finite joint Euler-product Rankin argument splitting primes at $Y_{\mathrm{cut}} = \lfloor 16 \log n / \log \log n \rfloor$ and doubly-exponential buckets $(2^{2^m}, 2^{2^{m+1}}]$, backed by self-contained proofs of Erdős's primorial bound $\prod_{p \le N} p \le 4^N$, Chebyshev's $\pi(N) \le 6 N / \log N$, the dyadic-tower Mertens bound $\sum_{2^{2^m} < p \le 2^{2^{m+1}}} 1/p \le 4$, and a Wigert-type divisor bound $\tau(t) \le \exp(6 \log t / \log \log t)$.

## Verification & Axiom Audit

- **Toolchain:** `leanprover/lean4:v4.33.1`
- **Mathlib4 revision:** `0df444a360eaa60ab8c11dca51a86af692955474`
- **Source file:** `RHDirect/PPL173_WorldRecordFourThirds.lean` (5,982 lines; 361,302 bytes; SHA-256: `8AC847762F461B4C257216FCE6F0615D6168CB1BDCCC11F408CB6FA26AF45C04`)
- **Build & kernel check:** `lake build` (`0` warnings) and `lake env leanchecker RHDirect.PPL173_WorldRecordFourThirds` (`PASS`)
- **Axiom audit (`Lean.collectAxioms`):** `469` constants audited in `RHDirect.PPL173_WorldRecordFourThirds`; axioms used: `[Quot.sound, Classical.choice, propext]`
- **Static check:** No `sorry`, `sorryAx`, `admit`, `axiom`, `opaque`, `native_decide`, `unsafe`, `@[implemented_by]`, `@[extern]`, or `import Mathlib`.

Verbatim `#print axioms` output:

```text
'PPL173FourThirds.lemma_A_three_path_reflection_nodiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173FourThirds.lemma_A_three_path_reflection' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173FourThirds.lemma_B_uniform_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173FourThirds.lemma_B_uniform_hall_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173FourThirds.lemma_C1_divisors_bigOmega_le_choose' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173FourThirds.ppl173_erdos860_primes_four_thirds' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173FourThirds.ppl173_world_record_four_thirds_closed_iSup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PPL173FourThirds.ppl173_world_record_four_thirds_iSup' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173FourThirds.ppl173_four_thirds_plus_eps' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Building

```bash
lake exe cache get   # optional: fetch prebuilt Mathlib oleans
lake build
lake env leanchecker RHDirect.PPL173_WorldRecordFourThirds
```

## License

[Apache-2.0](LICENSE)
