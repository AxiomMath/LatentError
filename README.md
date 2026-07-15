[![Logo for Axiom Math](logo.svg)](https://axiommath.ai/)

# Artifacts for the Lean formalization of "Estimation Error in Latent High-Dimensional Factor Models"

These files accompany a formalization of the main results of the paper *Estimation Error in Latent High-Dimensional Factor Models* ([estimation-error.pdf](LatentError/estimation-error.pdf)). This is built using Lean 4.28.0 with mathlib 4.28.0. Compilation with earlier or later versions are not guaranteed due to the quick-changing nature of Lean and mathlib.

The formalization establishes Theorem 1 and Corollaries 1–3 of the paper, assuming three classical background facts that are not yet available in Mathlib:

1. The Kolmogorov strong law of large numbers for independent, non-identically distributed summands
2. Weyl's eigenvalue perturbation inequality
3. Eigenvector continuity for a simple eigenvalue (Davis–Kahan).

- Input:
  - [estimation-error.pdf](LatentError/estimation-error.pdf): The source paper, whose Theorem 1 and Corollaries 1–3 are the targets of the formalization.
  - [assumed-facts.tex](LatentError/assumed-facts.tex): The three classical background facts assumed by the formalization (Kolmogorov SLLN, Weyl's inequality, Davis–Kahan eigenvector continuity), each stated exactly as it appears as a hypothesis in Lean.
  - [task.md](LatentError/task.md): The formalization instructions.
- Output:
  - [problem.lean](LatentError/problem.lean): An autonomously generated formal statement of the task.
  - [solution.lean](LatentError/solution.lean): An autonomously generated formal proof of the task, matching `problem.lean`.
