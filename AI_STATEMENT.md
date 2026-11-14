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
   out proof strategies and locate the relevant Mathlib lemmas. Some proof steps
   (calc blocks, etc.) were written by AI.
4. **Formatting.** AI was used for formatting within the files (docstrings, layout).
