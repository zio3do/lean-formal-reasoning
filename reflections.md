# Reflections on Formalizing Arithmetic and Number Theory in Lean 4

## 1. Formalization vs. Informal Reasoning

The gap between informal mathematical reasoning and formal proof is wider than surface syntax suggests. Steps considered "obvious" in natural language—such as algebraic rearrangement or implicit use of commutativity—require explicit justification and often specific lemma invocation. This creates a tension: proofs that are conceptually straightforward can require substantial tactical work, obscuring the underlying mathematical idea unless carefully structured.

Induction in Lean demands precise identification of the induction variable and explicit handling of all constructors. What appears in informal writing as "by induction on n" expands into pattern-matched cases with explicit hypothesis threading. The type system occasionally forces generalization beyond what the informal proof requires, as dependent types impose structural constraints that aren't apparent in standard mathematical notation.

## 2. Structural Friction in Lean

Natural number division truncates in Lean, meaning `(n * (n + 1)) / 2` only computes to the expected value when `2 ∣ n * (n + 1)`. This requires explicit divisibility proofs via lemmas like `Nat.mul_div_cancel'`, which impose preconditions not obvious from the mathematical expression. The intuitive strategy "multiply both sides by 2" becomes a multi-step lemma coordination exercise.

Type strictness requires explicit rewrites for expressions like `(n + 1 + 1)` versus `(n + 2)`, even when they're definitionally equal. Nested case analysis increases cognitive load non-linearly—tracking which hypotheses decompose in which branches becomes challenging as cases proliferate. The `apply` tactic often succeeds in the hypothesis space (via `apply ... at h`) where direct goal application fails, suggesting that proof search heuristics favor forward reasoning in certain contexts.

## 3. Proof Engineering Patterns

Extracting helper lemmas early improves proof clarity when subgoals recur or when intermediate results have independent semantic value. Checking Mathlib before reimplementation is efficient, though reconstructing existing results builds understanding of proof patterns and library organization. Import discipline—foundational files importing only `Mathlib.Data.Nat.Basic`, later files importing prior results—maintains clean dependency structure.

Intermediate proof states benefit from semantic naming (`hq` for quotient equality, `h_cancel` for cancellation steps) rather than generic labels. Explicit pattern matching in case analysis clarifies proof structure more effectively than implicit tactic-driven decomposition.

## 4. Automation and Explicit Structure

Heavy automation via `omega`, `simp`, or `ring` can close goals efficiently but obscures underlying reasoning. Manual rewriting exposes algebraic relationships that automated solvers handle opaquely. For instance, manually applying distributivity in `n * (n + 1) + 2 * (n + 1) = (n + 1) * (n + 2)` demonstrates factorization structure lost when `ring` solves it directly.

The tradeoff is context-dependent: automation is appropriate for routine arithmetic verification where the structure is understood, while explicit steps clarify non-obvious manipulations or pedagogically significant transformations. In proof development targeting structural transparency, limiting automation maintains visibility into proof mechanics.

## 5. Human–AI Collaboration in Formal Proof Development

AI assistants demonstrate capability in translating natural language theorem statements to Lean syntax and suggesting lemma types even when specific names are incorrect. Iterative interaction succeeds where one-shot autocomplete fails—the conversational format enables refinement through feedback cycles that single-inference systems cannot leverage.

State tracking remains problematic: assistants lose synchronization with proof context, suggesting tactics mismatched to current goals or proposing lemmas requiring the theorem being proved. Hallucinated lemma names nonetheless indicate the correct *type signature* needed, providing useful search direction despite nominal inaccuracy. The effective division of labor positions humans as strategic directors (proof architecture, mathematical intuition) and AI as tactical executors (lemma hunting, syntax handling, rapid iteration on approaches).

## 6. Broader Observations

Formalization exposes implicit structure in informal proofs—particularly around case exhaustiveness, termination, and definitional dependencies. Proof search (finding any valid derivation) differs fundamentally from proof construction (building a readable, maintainable argument), and the latter requires deliberate engineering beyond satisfying the type checker.

Abstraction through helper lemmas and modular file organization appears essential for scaling beyond small theorem collections. The library ecosystem (Mathlib) demonstrates that reusability depends on careful generalization, consistent naming, and import hygiene—conventions that become apparent only through sustained formalization work.
