import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Moment-generating function of a sum of independent Bernoulli variables

`X i ~ Bernoulli(p i)` independent, `S = ∑ i, X i`, `μ = ∑ i, p i`.

* `mgf_bernoulli`: `M_{X}(t) = 1 - q + q e^t` for `X ~ Bernoulli(q)`.
* `mgf_sum_bernoulli`: `M_S(t) = ∏ i, (1 - p i + p i e^t)`.
* `mgf_sum_bernoulli_le`: `M_S(t) ≤ exp (μ (e^t - 1))` for every real `t`.
-/

open MeasureTheory ProbabilityTheory Real Finset

namespace ChernoffBounds

/-! ## Definitions -/

/-- The mean `μ = ∑ i, p i` of the sum. -/
noncomputable def mean {ι : Type*} [Fintype ι] (p : ι → unitInterval) : ℝ :=
  ∑ i, (p i : ℝ) -- sum of all probability, over i, where i is finite.

/-! ## Real-analysis lemmas used in step 2 -/

/-- Each factor of the product formula is nonnegative. -/
theorem factor_nonneg (p : unitInterval) (t : ℝ) :
    0 ≤ 1 - (p : ℝ) + p * exp t := by
  have h1 : 0 ≤ 1 - (p : ℝ) := by exact unitInterval.one_sub_nonneg p
  have h2 : 0 ≤ (p : ℝ) := by exact unitInterval.nonneg p
  have h3 : 0 < exp t := by exact exp_pos t
  nlinarith

/-- Each factor of the product formula is bounded by an exponential. -/
theorem factor_le_exp (p : unitInterval) (t : ℝ) :
    1 - (p : ℝ) + p * exp t ≤ exp (p * (exp t - 1)) := by
  have h : 1 - (p : ℝ) + p * exp t = p * (exp t - 1) + 1 := by ring
  rw [h]
  exact Real.add_one_le_exp _

/-! ## Setup -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
-- Ω is sample space, P assigns every event in sample space a probability.
-- P {ω | Y ω = 1} is essentially	P(Y = 1)
variable {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ} {p : ι → unitInterval}
-- Y : Ω → ℝ is a discrete real-valued r.v.
-- The function Ω → ℝ stands for a random variable
-- q : unitInterval guarantees q ∈ [0, 1], stands for success probability.
-- hY : HasLaw Y (bernoulliMeasure (1 : ℝ) (0 : ℝ) q) P  ≃  Y ~ Bernoulli(q)
-- #check fun q : unitInterval ↦ bernoulliMeasure (1 : ℝ) 0 q
-- #check mgf

/-! ## Step 1: MGF of a single Bernoulli variable -/

theorem mgf_bernoulli {Y : Ω → ℝ} {q : unitInterval}
    (hY : HasLaw Y (bernoulliMeasure (1 : ℝ) (0 : ℝ) q) P) (t : ℝ) :
    mgf Y P t = 1 - q + q * exp t := by
  unfold mgf
  change ∫ x, ((fun y ↦ exp (t * y)) ∘ Y) x ∂P = _
  rw [hY.integral_comp (by fun_prop)]
  rw [@integral_bernoulliMeasure]
  simp
  ring


/-! ## Step 2: MGF of the sum -/

/-- Product formula: `M_S(t) = ∏ i, (1 - p i + p i * e^t)`. -/
theorem mgf_sum_bernoulli (h_indep : iIndepFun X P) -- X₁, …, Xₙ independent
    (h_law : ∀ i, HasLaw (X i) (bernoulliMeasure (1 : ℝ) 0 (p i)) P) (t : ℝ) :
    mgf (fun ω ↦ ∑ i, X i ω) P t = ∏ i, (1 - (p i : ℝ) + p i * exp t) := by
  have h := h_indep.mgf_sum₀ (t := t) (fun i ↦ (h_law i).aemeasurable) univ
  rw [<- Finset.sum_fn]
  rw [h]
  apply Fintype.prod_congr (fun a ↦ mgf (X a) P t) (fun a ↦ 1 - ↑(p a) + ↑(p a) * rexp t)
  intro i
  exact mgf_bernoulli (h_law i) t

/-- MGF bound `M_S(t) ≤ exp (μ (e^t - 1))`, for every real `t`. -/
theorem mgf_sum_bernoulli_le (h_indep : iIndepFun X P)
    (h_law : ∀ i, HasLaw (X i) (bernoulliMeasure (1 : ℝ) 0 (p i)) P) (t : ℝ) :
    mgf (fun ω ↦ ∑ i, X i ω) P t ≤ exp (mean p * (exp t - 1)) := by
  rw [mgf_sum_bernoulli h_indep h_law]
  calc
    ∏ i, (1 - (p i : ℝ) + p i * exp t) ≤ ∏ i, exp (p i * (exp t - 1)) :=
        prod_le_prod₀ (fun i _ ↦ factor_nonneg (p i) t) (fun i _ ↦ factor_le_exp (p i) t)
    _ = exp (mean p * (exp t - 1))
        := by rw [← exp_sum, mean, sum_mul]

end ChernoffBounds
