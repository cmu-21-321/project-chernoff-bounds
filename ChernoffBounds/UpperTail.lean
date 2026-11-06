import ChernoffBounds.MGF
import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Multiplicative Chernoff bound: upper tail

`X i ~ Bernoulli(p i)` independent, `S = ∑ i, X i`, `μ = ∑ i, p i`.
For `μ > 0` and `δ > 0`:
`P(S ≥ (1 + δ) μ) ≤ exp (-μ klFun (1 + δ))`.

Here `klFun` is mathlib's `InformationTheory.klFun x = x * log x + 1 - x`, the function
whose integral against a density ratio gives the Kullback–Leibler divergence. At
`x = 1 + δ` it equals `(1 + δ) log (1 + δ) - δ`, the usual Chernoff exponent, so the bound
reads `P(S ≥ (1 + δ) μ) ≤ exp (-μ ((1 + δ) log (1 + δ) - δ))`.
-/

open MeasureTheory ProbabilityTheory Real Finset InformationTheory

namespace ChernoffBounds

/-! ## Setup -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ} {p : ι → unitInterval}

/-! ## Step 3: exponential Markov -/

/-- Tail bound for a fixed `t > 0`: `P(S ≥ a) ≤ exp (-t a + μ (e^t - 1))`. -/
theorem measure_sum_ge_le (h_indep : iIndepFun X P)
    (h_law : ∀ i, HasLaw (X i) (bernoulliMeasure (1 : ℝ) 0 (p i)) P)
    {t : ℝ} (ht : 0 < t) (a : ℝ) :
    P.real {ω | a ≤ ∑ i, X i ω} ≤ exp (-t * a + (∑ i, (p i : ℝ)) * (exp t - 1)) := by
  sorry

/-! ## Principal theorem -/

theorem chernoff_upper (h_indep : iIndepFun X P)
    (h_law : ∀ i, HasLaw (X i) (bernoulliMeasure (1 : ℝ) 0 (p i)) P)
    {δ : ℝ} (hμ : 0 < ∑ i, (p i : ℝ)) (hδ : 0 < δ) :
    P.real {ω | (1 + δ) * (∑ i, (p i : ℝ)) ≤ ∑ i, X i ω} ≤
      exp (-((∑ i, (p i : ℝ)) * klFun (1 + δ))) := by
  sorry

end ChernoffBounds
