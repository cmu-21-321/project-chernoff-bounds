# AI Statement

AI tool used: [Claude Code](https://claude.com/claude-code) (Anthropic), mainly with the Claude Opus 5.5 model.

1. **Topic search.** AI was used to survey Mathlib for candidate gaps; from these, this topic
   (MGFs and multiplicative Chernoff bounds for Bernoulli sums) was chosen as the final project.
2. **Definitions and statements.** I was not familiar with how Mathlib sets up measure-theoretic
   probability (`MeasureTheory`, `ProbabilityTheory`, `InformationTheory`, …), so AI helped
   prototype the definitions and theorem statements and explained the relevant Mathlib
   conventions. The final statements were settled through discussion between me and the AI. AI
   also carried out the refactor that replaced the project's own definitions with Mathlib ones
   (after instructor feedback).
3. **Proofs.** While I authored the majority of the proofs, discussion with AI was used to work
   out proof strategies and locate the relevant Mathlib lemmas. AI directly wrote the following
   proofs in the final project:
   - `ChernoffBounds/MGF.lean`: the `calc` block in `mgf_sum_bernoulli_le`.
   - `ChernoffBounds/UpperTail.lean`: the proof of `measure_sum_ge_le`.
   - `ChernoffBounds/LowerTail.lean`: the proofs of `measure_sum_le_le` and `chernoff_lower`,
     adapted by AI from the upper-tail proofs consideriing their strong resemblance
4. **Formatting.** AI was used for formatting within the files (docstrings, layout).
5. **Report.** AI assisted in putting my ideas into writing, as well as wording and polishing `REPORT.md`. 