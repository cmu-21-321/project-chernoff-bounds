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

## Main result

For $\mu > 0$ and $\delta > 0$,

$$
\mathbb{P}\bigl(S \ge (1+\delta)\mu\bigr) \le \exp\Bigl[-\mu\bigl((1+\delta)\log(1+\delta) - \delta\bigr)\Bigr].
$$

## Proof outline

1. **Bernoulli MGF.** $\mathbb{E}[e^{tX_i}] = 1 - p_i + p_i e^t$.
2. **MGF of the sum.** By independence, for every real $t$,
   $\mathbb{E}[e^{tS}] = \prod_i (1 - p_i + p_i e^t) \le \exp\bigl(\mu(e^t - 1)\bigr)$,
   using $1 + x \le e^x$.
3. **Exponential Markov inequality.** For $t > 0$,
   $\mathbb{P}(S \ge a) \le \exp\bigl(-ta + \mu(e^t - 1)\bigr)$.
4. **Choice of parameters.** Take $a = (1+\delta)\mu$ and $t = \log(1+\delta)$.

Possible extensions: the lower-tail bound, and the simplified quadratic forms of the bounds.

## Status

Work in progress.

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
