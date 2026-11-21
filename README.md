# ChernoffBounds

Moment-generating functions and multiplicative Chernoff bounds for sums of independent
Bernoulli random variables, formalized in Lean 4 with [Mathlib](https://github.com/leanprover-community/mathlib4).
Course project for CMU 21-321.

## Setting

Let $X_1, \dots, X_n$ be independent random variables with $X_i \sim \mathrm{Bernoulli}(p_i)$
(the success probabilities may differ), and let

$$
S = \sum_i X_i, \qquad \mu = \mathbb{E}[S] = \sum_i p_i .
$$

## Main results

**Upper tail.** For $\delta > 0$,

$$
\mathbb{P}\bigl(S \ge (1+\delta)\mu\bigr) \le \exp\Bigl[-\mu\bigl((1+\delta)\log(1+\delta) - \delta\bigr)\Bigr]
= \left(\frac{e^\delta}{(1+\delta)^{1+\delta}}\right)^{\mu}.
$$

**Lower tail.** For $0 < \delta < 1$,

$$
\mathbb{P}\bigl(S \le (1-\delta)\mu\bigr) \le \exp\Bigl[-\mu\bigl((1-\delta)\log(1-\delta) + \delta\bigr)\Bigr]
= \left(\frac{e^{-\delta}}{(1-\delta)^{1-\delta}}\right)^{\mu}.
$$

In Lean both exponents are written with Mathlib's `InformationTheory.klFun x = x log x + 1 - x`,
evaluated at $1 + \delta$ and $1 - \delta$.

## Proof outline

1. **Bernoulli MGF.** $\mathbb{E}[e^{tX_i}] = 1 - p_i + p_i e^t$.
2. **MGF of the sum.** By independence, for every real $t$,
   $\mathbb{E}[e^{tS}] = \prod_i (1 - p_i + p_i e^t) \le \exp\bigl(\mu(e^t - 1)\bigr)$,
   using $1 + x \le e^x$.
3. **Exponential Markov inequality.** For $t > 0$,
   $\mathbb{P}(S \ge a) \le \exp\bigl(-ta + \mu(e^t - 1)\bigr)$; for $t \le 0$, the same bound holds
   for $\mathbb{P}(S \le a)$.
4. **Choice of parameters.** Take $a = (1+\delta)\mu$, $t = \log(1+\delta)$ for the upper tail, and
   $a = (1-\delta)\mu$, $t = \log(1-\delta)$ for the lower tail.

## Files

| File | Contents |
|---|---|
| `ChernoffBounds/MGF.lean` | Steps 1–2: Bernoulli MGF (`mgf_bernoulli`), product formula (`mgf_sum_bernoulli`), MGF bound (`mgf_sum_bernoulli_le`), integrability of $e^{tS}$ (`integrable_exp_mul_sum_bernoulli`), and the elementary inequalities they use |
| `ChernoffBounds/UpperTail.lean` | Steps 3–4 for the upper tail: exponential Markov for $t > 0$ (`measure_sum_ge_le`) and the main theorem `chernoff_upper` |
| `ChernoffBounds/LowerTail.lean` | Steps 3–4 for the lower tail: exponential Markov for $t \le 0$ (`measure_sum_le_le`) and `chernoff_lower` |
| `ChernoffBounds.lean` | Root file importing the three files above |

Not formalized: the lower tail at $\delta = 1$, and the simplified quadratic forms of the bounds.

## Documents

- [Report (PDF)](REPORT.pdf) · [Markdown source](REPORT.md)
- [AI use statement](AI_STATEMENT.md)

## Status

The upper-tail bound and the lower-tail bound (for $0 < \delta < 1$) are fully proved (no `sorry`).

## Building

Requires Lean via [elan](https://github.com/leanprover/elan); the Lean version is picked up
from `lean-toolchain`.

```bash
lake exe cache get   # download prebuilt Mathlib instead of compiling it
lake build
```

Source files live under `ChernoffBounds/` and are imported from `ChernoffBounds.lean`, so
`lake build` (and CI, on every push and pull request) checks all of them.

To update Mathlib, change `rev` in `lakefile.toml` and `lean-toolchain` to the new tag, then
run `lake update mathlib && lake exe cache get && lake build` (or run the
**Update Dependencies** workflow from the Actions tab).
