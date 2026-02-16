# Lean 4 Formal Reasoning Portfolio

## Overview

This repository contains formally verified theorems in Lean 4 demonstrating structured inductive reasoning on natural numbers. The emphasis is on explicit proof construction through manual tactic application rather than automated decision procedures. Theorems progress from foundational algebraic properties to multi-lemma coordination in number-theoretic results. Each proof is structured to demonstrate lemma decomposition, hypothesis management, and case analysis discipline. The repository prioritizes proof organization and abstraction patterns over breadth of results.

## Design Philosophy

Files are organized by conceptual theme and proof technique complexity. Foundational results establish core reasoning patterns (induction, rewriting, cancellation) which later files extend to inequality preservation, witness construction, and proof by contradiction. Automation is deliberately limited to maintain transparency in proof structure—tactics like `simp`, `omega`, and `linarith` are avoided in favor of explicit lemma invocation. This constraint demonstrates understanding of underlying proof mechanics rather than tactical pattern matching. Complex theorems are decomposed into manageable subgoals using helper lemmas and `have` blocks, mirroring mathematical practice of building layered arguments.

## Repository Structure

### Formalization Files

**Basic.lean** — Foundational arithmetic properties including associativity and distributivity. Establishes induction patterns and rewriting discipline on recursive definitions.

**Arithmetic.lean** — Cancellation for addition and monotonicity of multiplication. Demonstrates converting between inductive and existential representations of ordering using `le_iff_exists_add`.

**NumberTheory.lean** — Divisibility closure under addition and the parity dichotomy. Emphasizes explicit witness construction and case analysis on existential hypotheses.

**OrderAndInequalities.lean** — Order preservation under addition and cancellation for strict inequality. Showcases proof by contradiction combined with order reflection.

**Combinatorics.lean** — Closed-form formula for triangular number sum using finset operations. Demonstrates handling of truncating division in natural number arithmetic, requiring explicit divisibility proofs via even/odd case analysis to justify algebraic manipulations.

**Advanced.lean** — Uniqueness of quotient and remainder in the division algorithm. Capstone result requiring coordinated reasoning across arithmetic, order theory, and propositional logic through structured case analysis and inequality manipulation.

### Documentation

**notes/reflections.md** — Analytical reflection on formalization experience, covering the gap between informal and formal reasoning, structural friction in Lean, proof engineering patterns, automation tradeoffs, and human-AI collaboration dynamics.

**notes/CaseStudy_SumRange.md** — Detailed case study of formalizing the triangular number sum identity, documenting formalization challenges (truncating division, lemma navigation), proof evolution across multiple iterations, and observations on effective human-AI collaboration in formal proof development.

## Proof Engineering Approach

Helper lemmas are extracted when subgoals appear in multiple contexts or when they clarify proof structure. Induction is performed on carefully chosen variables to minimize case complexity. Imports respect conceptual dependencies—foundational files depend only on `Mathlib.Data.Nat.Basic`, while advanced files import earlier results. Intermediate proof states are named with semantic bindings (`hq`, `h_cancel`) rather than generic labels. Case structure is made explicit through pattern matching rather than implicit through tactic application.

## Selected Highlights

**Division algorithm uniqueness** (`div_mod_unique`): Given two representations of a natural number as quotient-remainder pairs with bounded remainders, both representations must be identical. The proof first establishes quotient equality via contradiction and case analysis on ordering, then derives remainder equality through direct cancellation. This demonstrates multi-phase proof organization and inequality manipulation without automated arithmetic solvers.

**Multiplication preserves inequality** (`my_mul_le_mul_left`): Inequality under multiplication is proved by converting the inductive ordering relation to its existential representation, constructing an appropriate witness, and reconstructing the target inequality. This illustrates working across different formulations of the same mathematical concept.

## How to Navigate This Repository

Foundational inductive reasoning patterns appear in **Basic.lean**. Inequality manipulation and order-theoretic arguments are in **Arithmetic.lean** and **OrderAndInequalities.lean**. The most structurally complex proof is the division uniqueness theorem in **Advanced.lean**, which coordinates multiple subproofs and explicit lemma chains.

## Build Instructions

Requires Lean 4 and Mathlib. Build via:

```bash
lake build
```