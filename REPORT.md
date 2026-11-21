# Moment-Generating Functions and Multiplicative Chernoff Bounds for Bernoulli Sums

---

## 1. Introduction

A central problem in probability is bounding the probability of rare events whose exact distribution is hard to evaluate. Toss $1{,}000$ independent fair coins and let $S$ be the number of heads, so $\mu = \mathbb{E}[S] = 500$. Computing $\Pr(S \ge 600)$ exactly requires summing $401$ binomial terms $\sum_{k=600}^{1000} \binom{1000}{k} 2^{-1000}$; the value is of order $10^{-10}$, but the sum gives little insight as parameters vary. Concentration inequalities trade exactness for closed-form upper bounds. Markov's inequality gives only $\Pr(S \ge 600) \le 500/600 \approx 0.83$, and Chebyshev's inequality, using $\operatorname{Var}(S) = 250$, gives $\Pr(\vert{}S - 500\vert{} \ge 100) \le 0.025$, with only polynomial decay in the deviation. **Chernoff's bound** [1] applies Markov's inequality to $e^{tS}$ for a tunable parameter $t > 0$, using the moment-generating function $\mathbb{E}[e^{tS}]$ and full mutual independence. Optimizing over $t$ yields $\exp(-500\,\varphi(1.2)) \approx 8 \times 10^{-5}$, where $\varphi(x) = x\log x + 1 - x$: exponential decay in $\mu$. Because of this, multiplicative Chernoff bounds are standard tools in randomized algorithms and probabilistic combinatorics [2, Ch. 4].

In the theorem formalized here, the summands $X_i \sim \mathrm{Bernoulli}(p_i)$ may have *distinct* success probabilities $p_i \in [0, 1]$. For example, if a student decides independently for each course whether to take it, with different probabilities (e.g. $0.3$, $0.75$, $0.5$), and each course takes one hour per day, then the daily workload is such a sum, and the Chernoff bound shows that it exceeds the planned $\mu$ hours by a factor $1+\delta$ only with exponentially small probability. The bound depends *only* on the mean $\mu = \sum_i p_i$, not on the individual $p_i$ (Step 2 of the proof).

As declared in the project proposal, our core goal was a complete, self-contained MGF-based proof of the multiplicative Chernoff bound on top of Mathlib's probability API. The principal theorem is the upper-tail bound of Section 2, formalized in Lean as `chernoff_upper` with right-hand side $\exp(-\mu\,\varphi(1+\delta))$, where $\varphi$ is Mathlib's `InformationTheory.klFun`. Beyond the declared core, we also formalized the lower-tail bound `chernoff_lower` for $0 < \delta < 1$. The repository builds via `lake build` (Lean 4, `v4.36.0-rc1`) with no `sorry`s and no project-specific definitions.

---

## 2. The Mathematics

We state and prove the theorem in the same four steps as our formalization; this is the standard MGF proof (see e.g. [2, Ch. 4]).

**Theorem (Multiplicative Chernoff Bounds for Bernoulli Sums).** *Let $X_1, \dots, X_n$ be mutually independent random variables with $X_i \sim \mathrm{Bernoulli}(p_i)$ for $p_i \in [0, 1]$. Let $S = \sum_{i=1}^n X_i$ and $\mu = \mathbb{E}[S] = \sum_{i=1}^n p_i$, and define $\varphi(x) = x \log x + 1 - x$. Then for every $\delta > 0$,*

$$\Pr\bigl(S \ge (1+\delta)\mu\bigr) \le \left(\frac{e^\delta}{(1+\delta)^{1+\delta}}\right)^{\mu}
= \exp\bigl(-\mu\,\varphi(1+\delta)\bigr).$$

*Moreover, for every $0 < \delta < 1$,*

$$\Pr\bigl(S \le (1-\delta)\mu\bigr) \le \left(\frac{e^{-\delta}}{(1-\delta)^{1-\delta}}\right)^{\mu}
= \exp\bigl(-\mu\,\varphi(1-\delta)\bigr).$$

**Proof.**

*Step 1: Single Bernoulli MGF.* Fix $i$ and $t \in \mathbb{R}$. Since $X_i$ is $1$ with probability $p_i$ and $0$ otherwise, its moment-generating function is

$$\mathbb{E}[e^{tX_i}] = (1 - p_i)e^{t \cdot 0} + p_i e^{t \cdot 1} = 1 - p_i + p_i e^t = 1 + p_i(e^t - 1).$$

*Step 2: Independence and exponential upper bound.* By mutual independence, $e^{tX_1}, \dots, e^{tX_n}$ are independent for any $t \in \mathbb{R}$, so the expectation of their product factors:

$$\mathbb{E}[e^{tS}] = \mathbb{E}\!\left[\prod_{i=1}^n e^{tX_i}\right] = \prod_{i=1}^n \mathbb{E}[e^{tX_i}] = \prod_{i=1}^n \bigl(1 + p_i(e^t - 1)\bigr).$$

Each factor $1 - p_i + p_i e^t$ is a convex combination of $1$ and $e^t$, hence positive. Applying $1 + x \le e^x$ with $x = p_i(e^t - 1)$ to each factor gives

$$\prod_{i=1}^n \bigl(1 + p_i(e^t - 1)\bigr)
\le \prod_{i=1}^n \exp\bigl(p_i(e^t - 1)\bigr)
= \exp\!\left(\sum_{i=1}^n p_i(e^t - 1)\right)
= \exp\bigl(\mu(e^t - 1)\bigr).$$

*Step 3: Exponential Markov inequality.* Let $a \in \mathbb{R}$ and $t > 0$. Since $x \mapsto e^{tx}$ is increasing, $\{S \ge a\} = \{e^{tS} \ge e^{ta}\}$, and Markov's inequality with Step 2 gives

$$\Pr(S \ge a) = \Pr\bigl(e^{tS} \ge e^{ta}\bigr) \le \frac{\mathbb{E}[e^{tS}]}{e^{ta}} \le \exp\bigl(\mu(e^t - 1) - ta\bigr).$$

*Step 4: Choice of $t$ for the upper tail.* The exponent $f(t) = \mu(e^t - 1) - ta$ from Step 3 is convex and minimized where $f'(t) = \mu e^t - a = 0$; for $a = (1 + \delta)\mu$ this gives $t = \log(1 + \delta) > 0$. Then $e^t - 1 = \delta$ and $ta = (1+\delta)\log(1+\delta)\,\mu$, so

$$\mu(e^t - 1) - ta = \mu\bigl(\delta - (1+\delta)\log(1+\delta)\bigr) = -\mu\,\varphi(1+\delta).$$

Exponentiating gives the upper-tail bound.

*Lower tail.* Since Steps 1 and 2 hold for all $t \in \mathbb{R}$, only Steps 3 and 4 change. For $t \le 0$, $x \mapsto e^{tx}$ is nonincreasing, so $\{S \le a\} \subseteq \{e^{tS} \ge e^{ta}\}$ and Markov's inequality with Step 2 gives $\Pr(S \le a) \le \exp(\mu(e^t - 1) - ta)$. Taking $a = (1 - \delta)\mu$ with $0 < \delta < 1$ and $t = \log(1 - \delta) < 0$ gives $e^t - 1 = -\delta$ and the exponent $\mu(-\delta - (1-\delta)\log(1-\delta)) = -\mu\,\varphi(1-\delta)$. $\blacksquare$

---

## 3. Formalization and Design Decisions

### 3.1 Setup and Statement

We use Lean 4 and Mathlib [3] (version `v4.36.0-rc1` [4]). The principal theorem, in `ChernoffBounds/UpperTail.lean`, is:

```lean
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ} {p : ι → unitInterval}

theorem chernoff_upper (h_indep : iIndepFun X P)
    (h_law : ∀ i, HasLaw (X i) (bernoulliMeasure (1 : ℝ) 0 (p i)) P)
    {δ : ℝ} (hδ : 0 < δ) :
    P.real {ω | (1 + δ) * (∑ i, (p i : ℝ)) ≤ ∑ i, X i ω} ≤
      exp (-((∑ i, (p i : ℝ)) * klFun (1 + δ)))
```

Instead of `Fin n`, we index the variables by an arbitrary finite type `ι` (`[Fintype ι]`, possibly empty). Mutual independence is the single hypothesis `h_indep : iIndepFun X P` (defined via generated $\sigma$-algebras, not pairwise), used once to factor the sum MGF in Step 2 (`iIndepFun.mgf_sum₀`) and once to show that `P` is a probability measure (Section 3.2).

Three statement-level design decisions:

1. **Bundled `unitInterval` probabilities.** Typing `p : ι → unitInterval` (Mathlib's subtype `{x : ℝ // 0 ≤ x ∧ x ≤ 1}`) matches `bernoulliMeasure`'s parameter type and removes the hypotheses `0 ≤ p i` and `p i ≤ 1`. The price is the coercion `(p i : ℝ)` in real arithmetic; `unitInterval.nonneg` and `unitInterval.one_sub_nonneg` supply the bounds to tactics.
2. **`P.real`, pointwise sums.** Mathlib measures take values in `ℝ≥0∞`, so we write the probability as `P.real` to compare it with `exp (...)`. The event uses the pointwise sum `{ω | a ≤ ∑ i, X i ω}`, as in Mathlib's Hoeffding inequality (`measure_sum_ge_le_of_iIndepFun`), while the MGF lemmas use the function sum `∑ i, X i`; `Finset.sum_apply` converts between them in Step 3.
3. **Eliminating bespoke definitions via `klFun`.** An early draft defined `mean p := ∑ i, (p i : ℝ)` and `chernoffExponent δ := (1 + δ) * log (1 + δ) - δ`. Following course staff feedback to minimize bespoke definitions, we inlined `mean` and replaced `chernoffExponent` with `InformationTheory.klFun`, which has the same value at $1 + \delta$. One definition now serves both tails (`klFun (1 + δ)` and `klFun (1 - δ)`) and points to KL divergence (Section 4), at the cost of one `unfold klFun` and `ring` per tail.

### 3.2 Why `HasLaw`

In a probability course, "$X \sim \mathrm{Bernoulli}(p)$" is shorthand for $\Pr(X = 1) = p$, $\Pr(X = 0) = 1 - p$, and hence $\mathbb{E}[f(X)] = p\,f(1) + (1-p)\,f(0)$; the sample space $\Omega$, its $\sigma$-algebra and measurability stay in the background. Mathlib splits this shorthand into three objects: a random variable is a function `X : Ω → ℝ`; its law is the push-forward measure `P.map X`, $A \mapsto P(X^{-1}(A))$; and the Bernoulli distribution is the measure `bernoulliMeasure 1 0 p` $= p\,\delta_1 + (1 - p)\,\delta_0$ on $\mathbb{R}$.

`HasLaw X μ P` has two fields: `aemeasurable : AEMeasurable X P` and `map_eq : P.map X = μ`.

Compared with simpler-looking alternatives (hypotheses on point probabilities such as `P {ω | X ω = 1} = p`, `Bool`- or `PMF`-valued variables, or a custom `IsBernoulli` predicate), `HasLaw` has two advantages:

* **Expectations via the law.** With point-probability hypotheses, computing $\mathbb{E}[e^{tX}]$ would mean proving $X \in \{0, 1\}$ almost everywhere and splitting the integral over $\{X = 0\}$ and $\{X = 1\}$. With `HasLaw`, the change-of-variables lemma `HasLaw.integral_comp` turns $\int_\Omega f(X)\,dP$ into $\int_{\mathbb{R}} f\,d(\text{law})$ (expectations depend only on the law), and `integral_bernoulliMeasure` evaluates it in one rewrite, so `mgf_bernoulli` takes six lines (Section 3.3).
* **Measurability for Step 2.** Mathlib's product formula `iIndepFun.mgf_sum₀` requires `∀ i, AEMeasurable (X i) P`. `HasLaw` bundles exactly this, so Step 2 passes `fun i ↦ (h_law i).aemeasurable`; with point-probability hypotheses, our theorems would need an extra `AEMeasurable` assumption.

This design has one cost: `HasLaw` provides `AEMeasurable` rather than `Measurable`, whereas Mathlib's integrability theorem `iIndepFun.integrable_exp_mul_sum` requires `Measurable`. Section 3.3 works around this with Lean's junk-value convention.

`HasLaw X (named distribution) P` is the standard Mathlib idiom [4], e.g. `mgf_gaussianReal` (`Distributions/Gaussian/Real.lean`) and `mgf_dirac` (`Moments/Basic.lean`), both of the form `HasLaw X (dist) P → mgf X P t = …`, like our `mgf_bernoulli`. Mathlib has no such formula for Bernoulli distributions yet, so `mgf_bernoulli` fills a gap.

Compared with a probability course, the mathematics is identical, but Mathlib makes every layer explicit: `P` is an arbitrary `ℝ≥0∞`-valued measure (hence `P.real`), independence is a relation between $\sigma$-algebras, and course intuitions become theorems (`HasLaw.integral_comp`). Usually `IsProbabilityMeasure P` must be assumed, but none of our main theorems do: `iIndepFun X P` says the measure of a finite intersection is the product of the measures, so the empty family gives $P(\Omega) = 1$, and `h_indep.isProbabilityMeasure` derives the instance.

### 3.3 The Proof, Step by Step

**Step 1: Single Bernoulli MGF (`MGF.lean`).** After `unfold mgf`, a `change` writes the integrand as a composition `f ∘ Y` so that `HasLaw.integral_comp` applies (side condition by `fun_prop`). Then `integral_bernoulliMeasure` evaluates the integral, and `simp` and `ring` normalize $q e^{t\cdot 1} + (1-q)e^{t\cdot 0}$ to $1 - q + q e^t$:

```lean
theorem mgf_bernoulli {Y : Ω → ℝ} {q : unitInterval}
    (hY : HasLaw Y (bernoulliMeasure (1 : ℝ) (0 : ℝ) q) P) (t : ℝ) :
    mgf Y P t = 1 - q + q * exp t := by
  unfold mgf
  change ∫ x, ((fun y ↦ exp (t * y)) ∘ Y) x ∂P = _
  rw [hY.integral_comp (by fun_prop)]
  rw [@integral_bernoulliMeasure]
  simp
  ring
```

**Step 2: Sum MGF and Exponential Bound (`MGF.lean`).** `mgf_sum_bernoulli` applies `iIndepFun.mgf_sum₀` over `univ : Finset ι`, with measurability from `(h_law i).aemeasurable`; `Fintype.prod_congr` then reduces to one factor at a time, each closed by `mgf_bernoulli`. To reach $\exp(\mu(e^t - 1))$, `mgf_sum_bernoulli_le` applies `Finset.prod_le_prod₀` factor by factor, then `Real.exp_sum` and `Finset.sum_mul`.

**Step 3: Exponential Markov and Integrability (`UpperTail.lean`, `MGF.lean`).** `measure_sum_ge_le` gets `IsProbabilityMeasure P` from `h_indep.isProbabilityMeasure` and applies Mathlib's `measure_ge_le_exp_mul_mgf`, i.e. $\Pr(S \ge a) \le e^{-ta}\,\mathrm{mgf}(S, P, t)$ for $t \ge 0$. After `Finset.sum_apply` converts the event, `mgf_sum_bernoulli_le` and `Real.exp_add` finish Step 3.

`measure_ge_le_exp_mul_mgf` also needs integrability of $e^{tS}$ (`integrable_exp_mul_sum_bernoulli`). Mathlib's `iIndepFun.integrable_exp_mul_sum` needs `Measurable (X i)`, but `HasLaw` gives only `AEMeasurable` (Section 3.2). Rather than strengthening our hypotheses or passing to measurable representatives (`aemeasurable.mk`), we use Lean's **junk-value convention**: `integral_undef` sets $\int f\,dP = 0$ when $f$ is *not* integrable, so by contrapositive (`Integrable.of_integral_ne_zero`) a function with nonzero integral is integrable.

```lean
theorem integrable_exp_mul_sum_bernoulli (h_indep …) (h_law …) (t : ℝ) :
    Integrable (fun ω ↦ exp (t * (∑ i, X i) ω)) P := by
  apply Integrable.of_integral_ne_zero
  change mgf (∑ i, X i) P t ≠ 0
  rw [mgf_sum_bernoulli h_indep h_law]
  ⋯
```

The integral of $e^{tS}$ is by definition `mgf (∑ i, X i) P t`, which by `mgf_sum_bernoulli` equals $\prod_i (1 - p_i + p_i e^t)$, a product of positive factors (`factor_pos`, `Finset.prod_pos`), hence nonzero. This is **not circular**: `iIndepFun.mgf_sum₀` needs no integrability hypothesis, so the product formula holds unconditionally. On paper, "the integral is positive, so it exists" would be circular.

**Step 4: Specialization (`UpperTail.lean`) and Lower Tail (`LowerTail.lean`).** `chernoff_upper` applies Step 3 with $t = \log(1 + \delta)$ (positive by `Real.log_pos`) and $a = (1 + \delta)\mu$, unfolds `klFun`, rewrites $\exp(\log(1+\delta)) = 1 + \delta$ (`Real.exp_log`), and matches exponents by `ring`. `LowerTail.lean` reuses `MGF.lean` unchanged, since Steps 1–2 hold for every $t \in \mathbb{R}$, and differs from `UpperTail.lean` only in signs and inequality directions: $+\delta$ becomes $-\delta$, $\ge$ becomes $\le$, $t > 0$ becomes $t \le 0$, `measure_ge_le_exp_mul_mgf` is replaced by `measure_le_le_exp_mul_mgf`, and `log_pos` is replaced by `log_nonpos`.

---

## 4. Scope Check and What Was Not Formalized

Every core milestone of the project declaration was completed: the single Bernoulli MGF formula (`mgf_bernoulli`), the exponential MGF upper bound for independent sums (`mgf_sum_bernoulli_le`), and the multiplicative upper-tail Chernoff bound via exponential Markov's inequality (`measure_sum_ge_le` and `chernoff_upper`). Beyond the declared scope, we also formalized the lower tail (`chernoff_lower`).

The proposal also mentioned reusable lemmas for Mathlib; two candidates emerged, neither submitted yet: `mgf_bernoulli` (Section 3.2) and an `AEMeasurable` version of `iIndepFun.integrable_exp_mul_sum` (Section 3.3).

Left for future work:

* **Information-theoretic meaning of $\varphi$.** `klFun` is the generator of the Kullback–Leibler (KL) divergence, $\mathrm{KL}(Q \,\|\, R) = \int \varphi(dQ/dR)\, dR$, and the Chernoff exponents are Poisson KL divergences: $\mu\,\varphi(1 \pm \delta) = \mathrm{KL}(\mathrm{Poi}((1 \pm \delta)\mu) \,\|\, \mathrm{Poi}(\mu))$.
* **Formal proof of $t$-optimality.** We use $t = \log(1 \pm \delta)$ without proving in Lean that it minimizes $f(t)$.
* **General $[0, 1]$-valued random variables and applications.** Extending to independent $[0, 1]$-valued variables (via convexity of $x \mapsto e^{tx}$), and applications such as those suggested in Issue #3.

---

## 5. Reflections

When I started this project, the steepest barrier was not constructing proofs, but simply *reading* Lean. Even familiar mathematical statements initially felt opaque behind implicit arguments, coercions such as `(p i : ℝ)`, bundled predicates like `HasLaw`, and measure notation like `P.real`. Goal states with `↑`, `∘`, and `∂P` took effort to parse before they read as mathematics. This is the usual difficulty of reading mathematical language, and Lean both amplifies and eases it. It amplifies it because every coercion, measurability assumption and $\sigma$-algebra is explicit. It eases it because every theorem has a fixed name, and hovering over a symbol in the editor shows its definition and type.

The most time-consuming practical challenge was finding lemmas in Mathlib. Knowing mathematically that a statement holds does not tell you which Mathlib theorem corresponds to it, or what it is called. This was where AI assistance helped most, less as a proof writer than as an upgraded version of `loogle`, `rw?`, and `apply?` that maps a mathematical intent to likely Mathlib names.

The main technical lesson of the project was how much a well-chosen *statement* simplifies a *proof*. Choosing `HasLaw` over point-probability hypotheses turned `mgf_bernoulli` into a six-line calculation and gave Step 2 the `AEMeasurable` proof it needed without an extra hypothesis. Similarly, the staff reminder to minimize custom definitions led to `Mathlib.InformationTheory.KullbackLeibler.KLFun`. That refactoring unified the upper and lower tails under one function, and showed a connection I had not noticed: the Chernoff exponent in probability theory is a Kullback–Leibler divergence from information theory (Section 4).

Mathlib's junk-value convention also showed up in an unexpected place. When `HasLaw`'s `AEMeasurable` did not satisfy `iIndepFun.integrable_exp_mul_sum`'s `Measurable` requirement, I expected to have to work around it with measurable representatives. Instead, because a non-integrable function integrates to $0$ in Mathlib, Step 3's integrability check reduced to a short contrapositive via `Integrable.of_integral_ne_zero` (Section 3.3)—a shortcut with no real paper analogue, made possible purely by how Lean totalizes the integral.

Finally, working in Mathlib makes it very concrete how much a formalization builds on earlier contributions. Almost every step here relies on abstractions written by others—`bernoulliMeasure`, `HasLaw`, `iIndepFun.mgf_sum₀`, and `klFun`—and our statement follows the exact `HasLaw` template already used in `mgf_gaussianReal` and `mgf_dirac`. Seen from that angle, `mgf_bernoulli` is not just an internal helper for this project: it fills a real gap in the existing pattern and could naturally go back upstream as a Mathlib PR (Section 3.2).

---

## 6. Collaboration Statement and Acknowledgements

This is an individual project completed with no group members.

I am grateful to Sidharth Hariharan for detailed, constructive feedback provided through repository issues #1–#4—specifically on golfing helper lemmas (Issue #1) and reflecting on the `HasLaw` formulation relative to standard probability courses (Issue #2)—as well as to the 21-321 course staff for general guidance on minimizing project-specific definitions.

This formalization builds directly upon the work of the Mathlib community [3, 4], and I specifically acknowledge the authors of the key probability and information-theory modules used here: Etienne Marion and David Ledvinka (`bernoulliMeasure`), Etienne Marion (`HasLaw`), Rémy Degenne (moment-generating functions, independence, and sub-Gaussian bounds), and Rémy Degenne and Lorenzo Luccioli (`klFun`).

For full disclosure of AI tool usage during the development of this project, please refer to `AI_STATEMENT.md` in the project repository.

---

## References

1. H. Chernoff. A measure of asymptotic efficiency for tests of a hypothesis based on the sum of observations. *The Annals of Mathematical Statistics*, 23(4):493–507, 1952.
2. M. Mitzenmacher and E. Upfal. *Probability and Computing: Randomization and Probabilistic Techniques in Algorithms and Data Analysis*. 2nd edition. Cambridge University Press, 2017.
3. The mathlib Community. The Lean mathematical library. In *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020)*, pages 367–381, 2020.
4. Mathlib, version `v4.36.0-rc1`. <https://github.com/leanprover-community/mathlib4>. Files used: `Mathlib/Probability/Distributions/Bernoulli.lean`, `Mathlib/Probability/HasLaw.lean`, `Mathlib/Probability/Moments/Basic.lean`, `Mathlib/Probability/Independence/Basic.lean`, `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean`; precedents cited in Sections 3.1–3.2 from `Mathlib/Probability/Distributions/Gaussian/Real.lean` and `Mathlib/Probability/Moments/SubGaussian.lean`.