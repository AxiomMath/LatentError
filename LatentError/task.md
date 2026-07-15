Please read the files `estimation-error.pdf` and `assumed-facts.tex`.

Fact~\ref{Fact1}, Fact~\ref{Fact2} and Fact~\ref{Fact3} are standard facts in the field.

You are required to formalize and verify the following statement in Lean:

Assuming (Fact~\ref{Fact1}, Fact~\ref{Fact2}, and Fact~\ref{Fact3}), all of Theorem 1, Corollary 1, Corollary 2, and Corollary 3 in `estimation-error.pdf` are true.

Important requirement: Do not include these three facts as theorems that are sorried out. Explicitly add these as hypotheses in each of Theorem 1, Corollary 1, Corollary 2, and Corollary 3.

---

## Formalization guidance (hypothesis interface)

The four statements are to be formalized **path-wise**: fix a realization of the
factor path `F` and of the noise array, on the almost-sure event described in the
paper (the event on which Proposition 1 and Lemma 5 hold). The probabilistic
Assumptions 1–5 of the paper enter the Lean statements only through their
deterministic consequences on that event. Accordingly, the model may be bundled
into a structure (one instance per realization) whose fields record those
consequences, with the theorems quantified over all instances of the structure.

**Completeness requirement (critical).** The hypothesis bundle must include *all*
deterministic conclusions of Proposition 1 and Lemma 5 of the paper, at full
(matrix-level) strength — not merely the Gram-matrix corollaries. In particular,
the following must appear as fields (notation as in the paper; `Φ̄ := Φ/√p`):

1. **Noise Gram limit** (Proposition 1(a)):
   `Zᵀ Z / (np) → (δ²/n) Iₙ`.
2. **Projected-noise decoherence** (Proposition 1(b) / Lemma 3):
   `(1/√p) · bᵀ(p) Z(p) → 0` in `ℝ^{k×n}`
   (equivalently `‖bᵀZ‖_F = o(√p)`). This is *not* implied by item 1 —
   `ZᵀZ/(np)` is invariant under `Z ↦ QZ` for orthogonal `Q` and therefore
   cannot constrain the orientation of `bᵀZ` — and it must be recorded
   separately.
3. **Signal-coordinate matrix limit** (Lemma 5(ii)):
   `Φ̄ = Φ(p)/√p → Φ̄∞` in `ℝ^{k×n}`. Here `Φ̄∞` may be recorded as an
   abstract fixed matrix characterized by its properties (this limit, the
   generator identity `N^{(n)} = Φ̄∞ Φ̄∞ᵀ/n`, and the duality link of item 6);
   the paper's explicit formula for `Φ̄∞` need not be transcribed. (Per
   Lemma 5, the paper chooses the column signs of `b` exactly so that this
   limit holds; no conclusion depends on the convention, and all conclusions
   below are sign-free.) This field is strictly stronger than, and must be
   recorded in place of (or in addition to), the Gram form
   `ΦᵀΦ/(np) → Fᵀ G_B F / n`; the Gram form alone loses the limit of the
   vectors `Φ̄ w` needed in Steps 3–4 of the paper's proof.
4. **Dual spectrum limits** (Proposition 1(c)–(d)):
   `θⱼ^{(p,n)} → λⱼ^{(n)} + δ²/n` for `j = 1, …, k`, sortedness of the full dual
   spectrum, and the trailing-average limit `ℓ^{(p,n)} → δ²/n`.
5. **Dual eigenvector convergence** (Proposition 1(d)):
   `wⱼ^{(p,n)} → wⱼ^{(n)}`, each `wⱼ^{(p,n)}` a unit eigenvector of `W^{(p,n)}`
   at its `j`-th largest eigenvalue.
6. **Duality link and limiting eigenstructure** (Lemma 5(iii)):
   `Φ̄∞ wⱼ^{(n)} = √(n λⱼ^{(n)}) · νⱼ^{(n)}`, with `(λⱼ^{(n)}, νⱼ^{(n)})` the
   ordered unit eigenpairs of `N^{(n)} = Φ̄∞ Φ̄∞ᵀ / n` and `(λⱼ^{(n)}, wⱼ^{(n)})`
   those of `W^{(n),0} = Fᵀ G_B F / n` (distinct positive `λⱼ^{(n)}`,
   Assumption 5), together with `νⱼ^{(p)} → νⱼ^{(n)}` for the eigenvectors of
   `N^{(p,n)} = ΦΦᵀ/(np)` (used by Corollary 3's limiting remark).
7. **Population structure** (Assumptions 3–4 and Lemma 2): `BᵀB/p → G_B`
   positive definite; distinct positive eigenvalues of `Σ_f^{1/2} G_B Σ_f^{1/2}`;
   the ordered orthonormal principal directions `b(p)` (unit eigenvectors of
   `Σ₀ = B Σ_f Bᵀ` with strictly decreasing positive eigenvalues, spanning
   `col(B)`); the decomposition `B F = b Φ`; and the sample eigenvectors
   `hⱼ = hvec(p, j)` as ordered orthonormal unit eigenvectors of
   `S^{(p,n)} = Y Yᵀ/(np)` at eigenvalues `θⱼ^{(p,n)}`.

Fields may state any proposition that is proved in the paper as a consequence of
Assumptions 1–5 (conditional on the path, almost surely); they must not state
anything stronger. Items 2 and 3 are the two fields whose omission makes the
theorems false as bundled: a deterministic instance satisfying items 1 and 4–7
exactly, but violating the conclusions of Theorem 1 and Corollaries 1–2, exists
when either is dropped.

**Statement-level requirements.**
- The three Facts of `assumed-facts.tex` appear as explicit hypotheses in each
  of the four theorems (e.g. `hFact1 : Fact1_SLLN`, `hFact2 : Fact2_Weyl m`,
  `hFact3 : Fact3_EigCont m`), stated exactly as in `assumed-facts.tex`. Facts
  2 and 3 are dimension-parametrized (`m × m` matrices for arbitrary `m`); each
  theorem takes them at the dimension(s) appropriate to it — `n` (and/or `k`)
  for the asymptotic statements, `p` for the standalone Corollary 3. They are
  not axioms, not sorried lemmas, and not structure fields.
- Angles are the sign-free acute angles between lines:
  `sin²∠(u,v) = 1 − ⟨u,v⟩²` for unit `u, v`. All conclusions must be stated with
  this sign-free quantity, so no eigenvector sign convention is ever needed.
- Theorem 1: `sin²∠(hⱼ, bⱼ) → δ²/(nλⱼ^{(n)} + δ²)
  + (nλⱼ^{(n)}/(nλⱼ^{(n)} + δ²)) · sin²∠(νⱼ^{(n)}, eⱼ)`.
- Corollary 1: `ℓ^{(p,n)} → δ²/n`; `θⱼ^{(p,n)} → λⱼ^{(n)} + δ²/n > 0`;
  `sin²∠(hⱼ, span(b)) → δ²/(nλⱼ^{(n)} + δ²)`;
  `ℓ^{(p,n)}/θⱼ^{(p,n)} → δ²/(nλⱼ^{(n)} + δ²)`; and this limit is ≤ the
  Theorem-1 limit, with equality iff `sin²∠(νⱼ^{(n)}, eⱼ) = 0`.
- Corollary 2: `(1/2)‖P_H − P_b‖_F² = Σⱼ sin²∠(hⱼ, span(b))
  → Σⱼ δ²/(nλⱼ^{(n)} + δ²)`, including the finite-`p` Frobenius identity.
- Corollary 3 (noiseless, exact at finite `p`) — **standalone statement,
  binding design decision**. Corollary 3 is a finite-`p` linear-algebra
  identity and must NOT be stated over the asymptotic bundle, must NOT carry a
  `Z = 0` hypothesis, and must NOT mention `δ²` (the bundle's `δ² > 0` and
  noise-Gram fields would otherwise render it vacuous). State it as its own
  theorem with its own minimal hypotheses, at a single fixed `p` (with
  `1 ≤ k < n`, `k < p`): given orthonormal `b = [b₁ ⋯ b_k] ∈ ℝ^{p×k}`, any
  `Φ ∈ ℝ^{k×n}`, the noiseless covariance `S⁰ := b Φ Φᵀ bᵀ/(np)` constructed
  directly (not obtained by zeroing noise in a noisy model), and unit
  eigenvectors `h⁰ⱼ` of `S⁰` and `νⱼ^{(p,n)}` of `N^{(p,n)} = ΦΦᵀ/(np)` for a
  common eigenvalue `μⱼ` that is simple for both matrices, conclude
  `sin²∠(h⁰ⱼ, bⱼ) = sin²∠(νⱼ^{(p,n)}, eⱼ)`. This matches the paper's
  quantification ("for every p at which these are simple") exactly. The three
  Facts still appear as explicit hypotheses of this theorem, per the
  requirement above, even though the proof is pure linear algebra. The Remark
  following Corollary 3 in the paper (the limit `νⱼ^{(p)} → νⱼ^{(n)}`) is NOT
  part of Corollary 3's statement; it is already covered by field 6 of the
  main bundle and must not be duplicated into, or demanded of, the standalone
  Corollary 3. Reviewers/judges must accept this split: tying `Z = 0` into
  the main bundle is rejected as vacuous, and the standalone form is the
  intended design, not a domain change.
- No `sorry`, no added axioms, no weakening of the stated conclusions.

**Pre-search falsification pass (mandatory).** After the Lean statements are
frozen and before proof search begins, numerically stress-test them: attempt to
construct (e.g., in Python) an instance of the hypothesis bundle — fields
satisfied exactly or to high precision, constant or convergent in `p` — under
which some stated conclusion fails. The same pass must also confirm the bundle
is SATISFIABLE by exhibiting at least one numerical instance meeting every
field (an unsatisfiable bundle would make all four theorems vacuously true — a
hollow success that must be treated as a spec failure). One such witness:
`b = [I_k; 0]`, `Φ/√p ≡ √n·V` constant with `VᵀV` of rank `k`, noise placed
entirely in rows `k+1, …` with `ZᵀZ/(np) = (δ²/n)Iₙ` exactly, so `bᵀZ ≡ 0`. Adversarial constructions that exploit
degrees of freedom the fields do not pin down (e.g., orientation of `bᵀZ`,
cross-term cancellations in the dual Gram) must be attempted explicitly. If a
counterexample is found, stop and repair the statement before any proof search.

**Proof route (informative).** With items 2 and 3 recorded, the two substantive
limits of Theorem 1 close by finite-dimensional algebra plus `Tendsto`
arithmetic: Gram duality identifies `hⱼ = ± Y wⱼ^{(p,n)} / ‖Y wⱼ^{(p,n)}‖` for
large `p` (eventual simplicity of the top-`k` dual eigenvalues follows from
items 4–6 and Fact 2; the sign squares away), `‖Y wⱼ‖² = np·θⱼ` is exact, and
`bᵀ Y wⱼ/√(np·θⱼ) = (Φ̄ wⱼ + (bᵀZ/√p) wⱼ)/√(n θⱼ)
→ √(nλⱼ/(nλⱼ+δ²)) · νⱼ^{(n)}` by items 2–5. Taking the `j`-th coordinate and
squaring gives Theorem 1; taking the squared norm and using `‖νⱼ^{(n)}‖ = 1`
gives the in-subspace mass `nλⱼ/(nλⱼ+δ²)`, hence Corollaries 1–2.
