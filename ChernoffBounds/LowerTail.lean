import ChernoffBounds.MGF
import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Multiplicative Chernoff bound: lower tail

`X i ~ Bernoulli(p i)` independent, `S = ∑ i, X i`, `μ = ∑ i, p i`.
For `0 < δ < 1`:
`P(S ≤ (1 - δ) μ) ≤ exp (-μ klFun (1 - δ))`.

At `x = 1 - δ`, `klFun x = x * log x + 1 - x` equals `(1 - δ) log (1 - δ) + δ`, so the
bound reads `P(S ≤ (1 - δ) μ) ≤ exp (-μ ((1 - δ) log (1 - δ) + δ))`.
-/

open MeasureTheory ProbabilityTheory Real Finset InformationTheory

namespace ChernoffBounds

/-! ## Setup -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ} {p : ι → unitInterval}

/-! ## Step 3: exponential Markov (Lower Tail) -/

/-- Tail bound for a fixed `t ≤ 0`: `P(S ≤ a) ≤ exp (-t a + μ (e^t - 1))`. -/
theorem measure_sum_le_le (h_indep : iIndepFun X P)
    (h_law : ∀ i, HasLaw (X i) (bernoulliMeasure (1 : ℝ) 0 (p i)) P)
    {t : ℝ} (ht : t ≤ 0) (a : ℝ) :
    P.real {ω | ∑ i, X i ω ≤ a} ≤ exp (-t * a + (∑ i, (p i : ℝ)) * (exp t - 1)) := by
  have hIsProb:= h_indep.isProbabilityMeasure
  have h := measure_le_le_exp_mul_mgf a ht
            (integrable_exp_mul_sum_bernoulli h_indep h_law t)
            -- Markov
  simp only [Finset.sum_apply] at h
  calc
    _ ≤ exp (-t * a) * mgf (∑ i, X i) P t := h
    _ ≤ exp (-t * a) * exp ((∑ i, (p i : ℝ)) * (exp t - 1)) :=
        mul_le_mul_of_nonneg_left (mgf_sum_bernoulli_le h_indep h_law t) (exp_pos _).le
    _ = exp (-t * a + (∑ i, (p i : ℝ)) * (exp t - 1)) := (exp_add _ _).symm

/-! ## Principal theorem (Lower Tail) -/

theorem chernoff_lower (h_indep : iIndepFun X P)
    (h_law : ∀ i, HasLaw (X i) (bernoulliMeasure (1 : ℝ) 0 (p i)) P)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    P.real {ω | ∑ i, X i ω ≤ (1 - δ) * (∑ i, (p i : ℝ))} ≤
      exp (-((∑ i, (p i : ℝ)) * klFun (1 - δ))) := by
  have ht : log (1 - δ) ≤ 0 := log_nonpos (by linarith) (by linarith)
  have h := measure_sum_le_le h_indep h_law ht ((1 - δ) * ∑ i, (p i : ℝ))
  unfold klFun
  rw [Real.exp_log (by linarith)] at h
  have e : -((∑ i, (p i : ℝ)) * ((1 - δ) * log (1 - δ) + 1 - (1 - δ))) =
      -log (1 - δ) * ((1 - δ) * ∑ i, (p i : ℝ)) + (∑ i, (p i : ℝ)) * (1 - δ - 1) := by
    ring
  rw [e]
  exact h

end ChernoffBounds
