import ChernoffBounds.MGF

/-!
# Multiplicative Chernoff bound: upper tail

`X i ~ Bernoulli(p i)` independent, `S = ∑ i, X i`, `μ = ∑ i, p i`.
For `μ > 0` and `δ > 0`:
`P(S ≥ (1 + δ) μ) ≤ exp (-μ ((1 + δ) log (1 + δ) - δ))`.
-/

open MeasureTheory ProbabilityTheory Real Finset

namespace ChernoffBounds

/-! ## Definitions -/

/-- The exponent in the principal theorem: `(1 + δ) log (1 + δ) - δ`. -/
noncomputable def chernoffExponent (δ : ℝ) : ℝ :=
  (1 + δ) * log (1 + δ) - δ

/-! ## Setup -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ} {p : ι → unitInterval}

/-! ## Step 3: exponential Markov -/

/-- Tail bound for a fixed `t > 0`: `P(S ≥ a) ≤ exp (-t a + μ (e^t - 1))`. -/
theorem measure_sum_ge_le (h_indep : iIndepFun X P)
    (h_law : ∀ i, HasLaw (X i) (bernoulliMeasure (1 : ℝ) 0 (p i)) P)
    {t : ℝ} (ht : 0 < t) (a : ℝ) :
    P.real {ω | a ≤ ∑ i, X i ω} ≤ exp (-t * a + mean p * (exp t - 1)) := by
  sorry

/-! ## Principal theorem -/

theorem chernoff_upper (h_indep : iIndepFun X P)
    (h_law : ∀ i, HasLaw (X i) (bernoulliMeasure (1 : ℝ) 0 (p i)) P)
    {δ : ℝ} (hμ : 0 < mean p) (hδ : 0 < δ) :
    P.real {ω | (1 + δ) * mean p ≤ ∑ i, X i ω} ≤ exp (-(mean p * chernoffExponent δ)) := by
  sorry

end ChernoffBounds
