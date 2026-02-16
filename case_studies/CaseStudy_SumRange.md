## Case Study: Formalizing the Triangular Number Sum Identity

### Formalization Challenges

1. **Truncating Division**: Natural number division in Lean truncates, meaning `(n * (n + 1)) / 2` only computes correctly when `2 ∣ n * (n + 1)`. This necessitates explicit divisibility proofs rather than direct algebraic manipulation.

2. **Preconditions on Arithmetic**: The intuitive strategy "multiply both sides by 2" translates to coordinating lemmas like `Nat.mul_div_cancel'`, each carrying divisibility preconditions. The informal step becomes a multi-lemma proof obligation.

3. **Type Strictness**: Expressions like `(n + 1 + 1)` versus `(n + 2)` are not definitionally equal, requiring explicit rewrites despite mathematical equivalence.

4. **Library Navigation**: Discovering appropriate Mathlib lemmas (`Nat.even_or_odd`, `Nat.right_distrib`) requires familiarity with naming conventions and module organization not evident from mathematical terminology alone.

### Human-AI Collaboration Dynamics

**AI Limitations:**
- **State Synchronization**: Frequent loss of proof context resulted in tactics mismatched to current goals and hallucinated lemma names (e.g., `Nat.even_mul_succ_self`)
- **Automation Bias**: Initial strategies over-relied on `omega` and `ring`, obscuring algebraic structure and complicating debugging when automation failed
- **Circular Dependencies**: Occasional suggestions required the theorem being proved, indicating incomplete constraint tracking

**AI Contributions:**
- **Type-Directed Search**: Hallucinated lemmas nonetheless indicated correct type signatures, providing useful search direction for library exploration
- **Strategy Iteration**: Conversational format enabled rapid exploration of multiple approaches (direct multiplication, divisibility lemmas, helper lemma extraction) within a single workflow
- **Tactical Explanation**: Clarified Lean mechanics including precondition requirements, proof structuring combinators, and relation hierarchies

### Strategic Insights

1. **Prove Helper Lemmas First**: Rather than proving divisibility inline repeatedly, proving `two_dvd_prod_succ` once and reusing it made the proof much cleaner.

2. **Natural Language → Lean Gap**: The intuition "multiply both sides by 2" is correct mathematically, but Lean requires:
   - Explicit divisibility proofs
   - Proper lemma applications
   - Understanding of truncating division semantics

3. **Simplification vs. Exposition Trade-off**: Using `ring` solves it quickly, but manually showing the distributive property (`n*(n+1) + 2*(n+1) = (n+1)*(n+2)`) exposes the algebra.

4. **Mathlib Already Has It**: The final revelation was that `Nat.sum_range_id` already exists in Mathlib! This highlights:
   - Check the library first before reinventing wheels
   - But implementing it yourself builds understanding
   - Reading Mathlib's proof can teach you patterns

### Comparison: Human vs. AI Approach

- **Human strength**: Understanding the high-level strategy, recognizing when to pivot approaches
- **AI strength**: Quickly suggesting lemmas, handling syntax, iterating rapidly
- **Collaboration win**: Human provides mathematical intuition and constraints ("no omega, show the algebra"), AI provides tactical execution and lemma hunting

This exercise demonstrates that proving even "simple" theorems in Lean requires understanding subtle details about the type system and standard library that aren't obvious from pure mathematics.
Proof Engineering Observations

1. **Helper Lemma Extraction**: Consolidating repeated divisibility reasoning into `two_dvd_prod_succ` with explicit even/odd case analysis improved readability and documented the mathematical principle (consecutive integers have opposite parity).

2. **Informal-to-Formal Gap**: The valid mathematical intuition "multiply both sides by 2" expands into explicit divisibility proofs, lemma coordination, and truncation-aware reasoning not apparent in informal notation.

3. **Selective Automation**: Using `ring` to solve the entire proof obscures structure; using it to simplify `(2k)(2k+1)` after proving divisibility is appropriate. The distinction: expose conceptually significant steps, automate routine algebra.

4. **Pattern Matching Idioms**: The `rcases ... with ⟨k, rfl⟩` pattern immediately substitutes existential witnesses into goals, avoiding manual bookkeeping—a Lean 4 idiom for cleaner existential reasoning.

5. **Library Redundancy**: `Nat.sum_range_id` exists in Mathlib, but reimplementation builds understanding of proof patterns and library organization. Reading canonical proofs after independent attempts maximizes learning.ng `ring` to solve the entire proof hides structure, but using it to clean up `(2k)(2k+1)` after proving divisibility is appropriate. The goal is to expose *conceptually important* steps, not every algebraic expansion.Division of Labor

**Human Role:** High-level strategy, recognizing when approaches fail, imposing constraints that prioritize transparency over automation

**AI Role:** Lemma search, syntax handling, rapid iteration through tactical variations

**Effective Collaboration:** Human provides mathematical intuition and architectural constraints; AI executes tactical search and manages Lean syntax. The conversational format enables refinement cycles unavailable to one-shot inference systems.

---

**Conclusion**: Formalizing elementary results exposes implicit structure absent from informal proofs—particularly around truncation semantics, precondition management, and library navigation. Even "simple" theorems require understanding type system constraints and standard library conventions not derivable from mathematical content alone