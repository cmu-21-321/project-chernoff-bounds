import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Statements for the multiplicative Chernoff bound

`X i ~ Bernoulli(p i)` independent, `S = ∑ i, X i`, `μ = ∑ i, p i`.
Proofs are `sorry` for now; this file fixes the definitions and the targets.
-/

open MeasureTheory ProbabilityTheory Real Finset

namespace ChernoffBounds

/-! ## Definitions -/

-- #check unitInterval

/-- The mean `μ = ∑ i, p i` of the sum. -/
noncomputable def mean {ι : Type*} [Fintype ι] (p : ι → unitInterval) : ℝ :=
  ∑ i, (p i : ℝ)

/-- The exponent in the principal theorem: `(1 + δ) log (1 + δ) - δ`. -/
noncomputable def chernoffExponent (δ : ℝ) : ℝ :=
  (1 + δ) * log (1 + δ) - δ

/-! ## A real-analysis lemma used in step 2 -/

/-- Each factor of the product formula is bounded by an exponential. -/
theorem factor_le_exp (p : unitInterval) (t : ℝ) :
    1 - (p : ℝ) + p * exp t ≤ exp (p * (exp t - 1)) := by
  have h : 1 - (p : ℝ) + p * exp t = p * (exp t - 1) + 1 := by ring
  rw [h]
  exact Real.add_one_le_exp _

/-! ## Setup -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ} {p : ι → unitInterval}

/-! ## Step 1: MGF of a single Bernoulli variable -/

theorem mgf_bernoulli {Y : Ω → ℝ} {q : unitInterval}
    (hY : HasLaw Y (bernoulliMeasure (1 : ℝ) 0 q) P) (t : ℝ) :
    mgf Y P t = 1 - q + q * exp t := by
  sorry

/-! ## Step 2: MGF of the sum -/



/-! ## Step 3: exponential Markov -/



/-! ## Principal theorem -/
