# Hager's Sharper Gauss–Legendre Reverse-Markov Bound in Lean 4

An elementary Lean 4 / Mathlib formalization of the sharper Gauss–Legendre inequality from William W. Hager's September 2, 2015 problem note (*"10,000 Yen Prize Problem"*):

> Let $p$ be a polynomial of degree at most $n$ with $p(-1) = 0$ and $|p'(\tau_i)| \le 1$ at the $n$ Gauss–Legendre nodes $-1 < \tau_1 < \dots < \tau_n < 1$. Then $|p(\tau_i)| \le 1 + \tau_n$ for all $1 \le i \le n$, with equality attained at $i = n$ by $p(t) = 1 + t$.

## Historical Context

The general bound $|p(\tau_i)| \le 2$ (for both Gauss–Legendre and Gauss–Radau nodes) was proved by Xiang-Sheng Wang (*"On a conjecture of Hager regarding bounds on polynomials"*, [arXiv:1607.02798](https://arxiv.org/abs/1607.02798), *SIAM J. Numer. Anal.*, 2017), winning Hager's 2015 prize. Hager's original note also stated the sharper Gauss–Legendre bound $|p(\tau_i)| \le 1 + \tau_n$, which requires ruling out the $2 - (1 + \tau_n)$ slack and showing that the last row of the Gauss–Legendre integration matrix has strictly nonnegative entries.

This repository formalizes an elementary proof of the sharp bound $|p(\tau_i)| \le 1 + \tau_n$ for all $n \ge 1$, the sharpness witness $p(X) = X + 1$, non-vacuity existence of the Gauss–Legendre and right-Radau nodes, and the companion $|p(\tau_i)| \le 2$ bound for Gauss–Radau quadrature nodes.

## Exported Theorem Signatures

All five top-level theorems in [`RHDirect/PPL031_HagerGaussSharp.lean`](RHDirect/PPL031_HagerGaussSharp.lean) are stated in pure Mathlib types with no custom definitions in their signatures:

```lean
theorem hager_gauss_legendre_sharp_challenge
    (n : ℕ) (hn : 1 ≤ n)
    (P : Polynomial ℝ) (hPdeg : P.natDegree = n)
    (hPorth : ∀ q : Polynomial ℝ, q.natDegree < n →
      ∫ t in (-1 : ℝ)..1, P.eval t * q.eval t = 0)
    (τ : Fin n → ℝ) (hτmono : StrictMono τ) (hτroots : ∀ i : Fin n, P.eval (τ i) = 0)
    (p : Polynomial ℝ) (hpdeg : p.natDegree ≤ n) (hp_m1 : p.eval (-1) = 0)
    (hderiv : ∀ i : Fin n, |p.derivative.eval (τ i)| ≤ 1) :
    ∀ i : Fin n, |p.eval (τ i)| ≤ 1 + τ ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩

theorem hager_gauss_legendre_sharp_attained
    (n : ℕ) (hn : 1 ≤ n) (τ : Fin n → ℝ)
    (hτ_ge : -1 ≤ τ ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩) :
    ∃ p : Polynomial ℝ,
      p.natDegree ≤ n ∧
      p.eval (-1) = 0 ∧
      (∀ i : Fin n, |p.derivative.eval (τ i)| ≤ 1) ∧
      |p.eval (τ ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩)| =
        1 + τ ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩

theorem exists_gauss_legendre_nodes (n : ℕ) (_hn : 1 ≤ n) :
    ∃ (P : Polynomial ℝ) (τ : Fin n → ℝ),
      P.natDegree = n ∧
      (∀ q : Polynomial ℝ, q.natDegree < n → ∫ t in (-1 : ℝ)..1, P.eval t * q.eval t = 0) ∧
      StrictMono τ ∧
      (∀ i : Fin n, -1 < τ i ∧ τ i < 1) ∧
      (∀ i : Fin n, P.eval (τ i) = 0)

theorem exists_radau_nodes (n : ℕ) (hn : 1 ≤ n) :
    ∃ (R : Polynomial ℝ) (τ : Fin n → ℝ),
      R.natDegree = n ∧
      R.eval 1 = 0 ∧
      (∀ q : Polynomial ℝ, q.natDegree < n - 1 → ∫ t in (-1 : ℝ)..1, R.eval t * q.eval t = 0) ∧
      StrictMono τ ∧
      (∀ i : Fin n, -1 < τ i ∧ τ i ≤ 1) ∧
      τ ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ = 1 ∧
      (∀ i : Fin n, R.eval (τ i) = 0)

theorem hager_radau_bound_challenge
    (n : ℕ) (hn : 1 ≤ n)
    (R : Polynomial ℝ) (hRdeg : R.natDegree = n) (hR1 : R.eval 1 = 0)
    (hRorth : ∀ q : Polynomial ℝ, q.natDegree < n - 1 →
      ∫ t in (-1 : ℝ)..1, R.eval t * q.eval t = 0)
    (τ : Fin n → ℝ) (hτmono : StrictMono τ) (hτroots : ∀ i : Fin n, R.eval (τ i) = 0)
    (p : Polynomial ℝ) (hpdeg : p.natDegree ≤ n) (hp_m1 : p.eval (-1) = 0)
    (hderiv : ∀ i : Fin n, |p.derivative.eval (τ i)| ≤ 1) :
    ∀ i : Fin n, |p.eval (τ i)| ≤ 2
```

## Proof Overview

Writing $p(\tau_i) = \int_{-1}^{\tau_i} p'(t)\,dt = \sum_{j=1}^n A_{ij} p'(\tau_j)$ via quadrature exactness for degree $\le n - 1 \le 2n - 2$ reduces the bound to $\sum_{j=1}^n |A_{ij}|$.

1. **Energy / Bessel bound (all rows, Gauss and Radau):** Expanding the quadrature kernel in Legendre polynomials gives $A_{ij} = \frac{1}{2} w_j \bigl(1 + \tau_i + \sum_{k=1}^{n-1} P_k(\tau_j)(P_{k+1}(\tau_i) - P_{k-1}(\tau_i))\bigr)$, from which Bessel's inequality yields $\sum_j |A_{ij}| \le \frac{3 + \tau_i}{2}$. This immediately proves $|p(\tau_i)| \le 2$ for Gauss–Radau ($\tau_n = 1$) and for Gauss–Legendre gives $\frac{3 + \tau_i}{2} \le 1 + \tau_n$ whenever $1 - \tau_i \ge 2(1 - \tau_n)$.
2. **Root-gap bound for interior rows ($i < n$):** Using a degree-3/degree-4 shifted-hypergeometric sum-of-squares certificate around $u = n(n+1)(1 - t)/2$ (for $n \ge 3$, plus direct computation for $n = 2$), we prove $1 - \tau_{n-1} > 3(1 - \tau_n) \ge 2(1 - \tau_n)$, which places every interior row $i < n$ under the energy bound.
3. **Last-row positivity ($i = n$):** Using the Legendre differential-equation energy bound $(1 - \tau_j^2) P_n'(\tau_j)^2 \le n(n+1)$ together with the Christoffel–Darboux identity, we prove $A_{nj} \ge 0$ for all $1 \le j \le n$, so $\sum_j |A_{nj}| = \sum_j A_{nj} = 1 + \tau_n$.

## Verification & Axioms

- **Toolchain:** `leanprover/lean4:v4.33.1`
- **Mathlib4 revision:** `0df444a360eaa60ab8c11dca51a86af692955474`
- **File:** `RHDirect/PPL031_HagerGaussSharp.lean` (3,104 lines; SHA-256: `54DF9E22A16AB500221DA954F29DA64A6436AA4D6FD69A4B50E9E41AFF48C377`)
- **Zero-cheat check:** No `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `unsafe`, `@[implemented_by]`, `@[extern]`, or `set_option` in code.
- **External kernel verifier:** `leanchecker RHDirect.PPL031_HagerGaussSharp` → `PASS`

Verbatim `#print axioms` output:

```text
'PPL031_HagerGaussSharp.hager_gauss_legendre_sharp_challenge' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL031_HagerGaussSharp.hager_gauss_legendre_sharp_attained' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL031_HagerGaussSharp.exists_gauss_legendre_nodes' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL031_HagerGaussSharp.exists_radau_nodes' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL031_HagerGaussSharp.hager_radau_bound_challenge' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Building & Scripts

```bash
lake exe cache get   # optional: fetch prebuilt Mathlib oleans
lake build
leanchecker RHDirect.PPL031_HagerGaussSharp
```

Companion Python scripts in [`scripts/`](scripts/):
- [`scripts/check_sos.py`](scripts/check_sos.py): algebraic verification of the degree-3 and degree-4 polynomial certificates used in the root-gap step.
- [`scripts/verify_complete_proof.py`](scripts/verify_complete_proof.py): numerical sanity checks across $1 \le n \le 500$ (energy bound, root gap, last-row positivity, and $\ell_1$ row norms).

## License

[MIT](LICENSE)
