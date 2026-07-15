import Mathlib

open scoped BigOperators Topology Matrix MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter

noncomputable section

/-! ## Definition 1 (Sign-free acute angle between lines). -/

/-- The squared sine of the acute angle between the lines spanned by nonzero
`u, v ∈ ℝ^m`:  `sin²∠(u, v) := 1 − ⟨u, v⟩² / (‖u‖² ‖v‖²)`.  This is invariant under
`u ↦ ±u`, `v ↦ ±v` and under positive rescaling; for unit vectors it reduces to
`1 − ⟨u, v⟩²`. -/
def sinSq {m : ℕ} (u v : EuclideanSpace ℝ (Fin m)) : ℝ :=
  1 - (inner ℝ u v) ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2)

/-- The `j`-th column of a matrix, viewed as a Euclidean vector. -/
def colVec {p k : ℕ} (M : Matrix (Fin p) (Fin k) ℝ) (j : Fin k) :
    EuclideanSpace ℝ (Fin p) := WithLp.toLp 2 (fun i => M i j)

/-- The operator (spectral, L2) norm of a square matrix. -/
def opNorm {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖

/-- The squared Frobenius norm `‖M‖_F² = Σᵢⱼ Mᵢⱼ²`. -/
def frobSq {m l : ℕ} (M : Matrix (Fin m) (Fin l) ℝ) : ℝ := ∑ i, ∑ j, (M i j) ^ 2

/-- Assemble the `p × k` matrix `H = [h₁ ⋯ h_k]` whose `j`-th column is `hⱼ`. -/
def Hmat {p k : ℕ} (hh : Fin k → EuclideanSpace ℝ (Fin p)) : Matrix (Fin p) (Fin k) ℝ :=
  Matrix.of (fun i j => (hh j) i)

/-! ## Definition 2 (The three assumed background facts).

These are stated exactly as classical propositions and appear as explicit
hypotheses of each theorem below.  They are NOT axioms or sorried lemmas. -/

/-- **Fact 1 (Kolmogorov SLLN for independent, non-identically distributed
summands).** For independent real random variables `{Xᵢ}_{i≥1}` with finite
variances satisfying Kolmogorov's series condition `Σ_{i=1}^∞ Var(Xᵢ)/i² < ∞`, the
centered average `(1/p) Σ_{i=1}^p (Xᵢ − E[Xᵢ])` tends to `0` almost surely as
`p → ∞`.  The sum runs over `i ∈ {1, …, p}` exactly (`Finset.Icc 1 p`), matching
the source `(1/p) Σ_{i=1}^p`. -/
def Fact1_SLLN : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ),
    (∀ i, Measurable (X i)) →
    (∀ i, MemLp (X i) 2 μ) →
    iIndepFun X μ →
    Summable (fun i : ℕ => variance (X i) μ / ((i : ℝ)) ^ 2) →
    ∀ᵐ ω ∂μ, Tendsto
      (fun p : ℕ => (1 / (p : ℝ)) *
        ∑ i ∈ Finset.Icc 1 p, (X i ω - μ[X i]))
      atTop (𝓝 0)

/-- **Fact 2 (Weyl's eigenvalue perturbation inequality), at dimension `m`.** For
real symmetric `A, A'` and every eigenvalue index `i`, `|λᵢ(A') − λᵢ(A)| ≤
‖A' − A‖_op`, where the eigenvalues at each index are taken in *weakly decreasing
order* `λ₁ ≥ ⋯ ≥ λ_m`.  Here `σ` (resp. `σ'`) is *the* weakly decreasing
eigenvalue list of `A` (resp. `A'`): it is `Antitone` and equals Mathlib's
`eigenvalues` up to a reindexing permutation `e` (resp. `e'`), so the statement
pins down the required sorted convention.  (The stated consequence -- `A^{(p)} → A`
implies `λᵢ(A^{(p)}) → λᵢ(A)` for every `i` -- follows from this inequality.) -/
def Fact2_Weyl (m : ℕ) : Prop :=
  ∀ (A A' : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsHermitian) (hA' : A'.IsHermitian)
    (σ σ' : Fin m → ℝ) (e e' : Fin m ≃ Fin m),
    Antitone σ → Antitone σ' →
    (σ = fun i => hA.eigenvalues (e i)) → (σ' = fun i => hA'.eigenvalues (e' i)) →
    ∀ i : Fin m, |σ' i - σ i| ≤ opNorm (A' - A)

/-- **Fact 3 (Eigenvector continuity for a simple eigenvalue), at dimension `m`.**
If real symmetric `A^{(p)} → A` and `μ` is a simple eigenvalue of `A` with unit
eigenvector `v`, then there exist `μ^{(p)} ∈ ℝ` and unit `v^{(p)}` with, for all
large `p`, `A^{(p)} v^{(p)} = μ^{(p)} v^{(p)}`, `‖v^{(p)}‖ = 1`,
`⟨v^{(p)}, v⟩ ≥ 0`, and `μ^{(p)} → μ`, `v^{(p)} → v`. -/
def Fact3_EigCont (m : ℕ) : Prop :=
  ∀ (A : ℕ → Matrix (Fin m) (Fin m) ℝ) (Ainf : Matrix (Fin m) (Fin m) ℝ),
    (∀ p, (A p).IsHermitian) → Ainf.IsHermitian →
    Tendsto A atTop (𝓝 Ainf) →
    ∀ (μ : ℝ) (v : EuclideanSpace ℝ (Fin m)),
      ‖v‖ = 1 → Matrix.toEuclideanLin Ainf v = μ • v →
      (∀ w : EuclideanSpace ℝ (Fin m), ‖w‖ = 1 →
        Matrix.toEuclideanLin Ainf w = μ • w → w = v ∨ w = -v) →
      ∃ (μ' : ℕ → ℝ) (v' : ℕ → EuclideanSpace ℝ (Fin m)),
        (∀ᶠ p in atTop,
          Matrix.toEuclideanLin (A p) (v' p) = μ' p • v' p ∧
          ‖v' p‖ = 1 ∧ 0 ≤ (inner ℝ (v' p) v : ℝ)) ∧
        Tendsto μ' atTop (𝓝 μ) ∧ Tendsto v' atTop (𝓝 v)

/-! ## Definition 3 (Asymptotic model realization — the hypothesis bundle).

An instance records the deterministic consequences (fields 1--7), valid on the
almost-sure event of Proposition 1 and Lemma 5, for one fixed realization of the
factor path `F` and noise array.  Data are indexed by the admissible cross-section
sizes `Adm k = {p : ℕ // k ≤ p}`, with `k, n, δ²` fixed. -/

/-- Admissible cross-section sizes `p ≥ k`.  Admissibility is part of the index:
no `p × k` matrix with `p < k` can have `k` orthonormal columns, so the structural
fields below are stated unconditionally over `Adm k`, and asymptotic limits are
taken along `atTop` on `Adm k`. -/
abbrev Adm (k : ℕ) := {p : ℕ // k ≤ p}

/-- The asymptotic factor-model bundle (Definition 3).

Abbreviations used below (all derived from the fields):
* `Y P = b P * Φ P + Z P`               (the data matrix `Y = bΦ + Z ∈ ℝ^{p×n}`),
* `S P = (1/(np)) • (Y P) (Y P)ᵀ`       (scaled sample covariance `S^{(p,n)} ∈ ℝ^{p×p}`),
* `W P = (1/(np)) • (Y P)ᵀ (Y P)`       (dual `W^{(p,n)} ∈ ℝ^{n×n}`),
* `Npn P = (1/(np)) • (Φ P) (Φ P)ᵀ`     (`N^{(p,n)} ∈ ℝ^{k×k}`),
* `Sig0 P = (B P) Σ_f (B P)ᵀ`           (population `Σ₀ = B Σ_f Bᵀ ∈ ℝ^{p×p}`),
* `Wn0 = (1/n) • Fᵀ G_B F`              (`W^{(n),0} ∈ ℝ^{n×n}`),
* `Nn = (1/n) • Φ̄∞ (Φ̄∞)ᵀ`             (`N^{(n)} ∈ ℝ^{k×k}`). -/
structure AsymptoticModel (k n : ℕ) (δ2 : ℝ) where
  /-- `1 ≤ k`. -/
  hk : 1 ≤ k
  /-- `k < n`. -/
  hkn : k < n
  /-- `δ² > 0`. -/
  hδ2 : 0 < δ2
  -- Data (indexed by the admissible cross-section size `P : Adm k`):
  /-- `B(p) ∈ ℝ^{p×k}`. -/
  B : (P : Adm k) → Matrix (Fin P.1) (Fin k) ℝ
  /-- fixed `Σ_f ∈ ℝ^{k×k}`, symmetric positive definite. -/
  Sf : Matrix (Fin k) (Fin k) ℝ
  /-- `b(p) ∈ ℝ^{p×k}` with orthonormal columns (`bᵀ b = Iₖ`); its columns are the
  estimation targets. -/
  b : (P : Adm k) → Matrix (Fin P.1) (Fin k) ℝ
  /-- the fixed (`p`-free) factor path `F ∈ ℝ^{k×n}`. -/
  F : Matrix (Fin k) (Fin n) ℝ
  /-- `Φ(p) ∈ ℝ^{k×n}` with `B F = b Φ`; `Φ̄(p) := Φ(p)/√p`. -/
  Φ : (P : Adm k) → Matrix (Fin k) (Fin n) ℝ
  /-- `Z(p) ∈ ℝ^{p×n}` (noise). -/
  Z : (P : Adm k) → Matrix (Fin P.1) (Fin n) ℝ
  /-- `hⱼ = h(p,j) ∈ ℝ^p`, the `j`-th unit eigenvector of `S^{(p,n)}` (top-`k`, in
  decreasing eigenvalue order). -/
  h : (P : Adm k) → Fin k → EuclideanSpace ℝ (Fin P.1)
  /-- `wⱼ^{(p,n)} ∈ ℝ^n`, unit eigenvector of `W^{(p,n)}` at `θⱼ^{(p,n)}`. -/
  w : (P : Adm k) → Fin k → EuclideanSpace ℝ (Fin n)
  /-- `νⱼ^{(p)} ∈ ℝ^k`, `j`-th unit eigenvector of `N^{(p,n)}`. -/
  ν : (P : Adm k) → Fin k → EuclideanSpace ℝ (Fin k)
  /-- the full sorted eigenvalue list `θ₁^{(p,n)} ≥ ⋯ ≥ θₙ^{(p,n)}` of `W^{(p,n)}`. -/
  θ : (P : Adm k) → Fin n → ℝ
  /-- the eigenvalues `νval P j` of `N^{(p,n)}` attached to the ordered eigenvectors
  `ν P j` (weakly decreasing). -/
  νval : (P : Adm k) → Fin k → ℝ
  -- Limiting objects (fixed, `p`-free):
  /-- `Φ̄∞ ∈ ℝ^{k×n}`. -/
  Φbarinf : Matrix (Fin k) (Fin n) ℝ
  /-- `G_B ∈ ℝ^{k×k}`, the limit of `Bᵀ B/p`. -/
  GB : Matrix (Fin k) (Fin k) ℝ
  /-- eigenvalues `λⱼ^{(n)}` (`j = 1,…,k`). -/
  lam : Fin k → ℝ
  /-- unit eigenvectors `wⱼ^{(n)} ∈ ℝ^n` of `W^{(n),0} = Fᵀ G_B F/n`. -/
  wn : Fin k → EuclideanSpace ℝ (Fin n)
  /-- unit eigenvectors `νⱼ^{(n)} ∈ ℝ^k` of `N^{(n)} = Φ̄∞ (Φ̄∞)ᵀ/n`. -/
  νn : Fin k → EuclideanSpace ℝ (Fin k)
  -- ===== Standing structural hypotheses on the data (unconditional over `Adm k`) =====
  /-- `bᵀ b = Iₖ` (orthonormal columns). -/
  hb_ortho : ∀ P : Adm k, (b P)ᵀ * (b P) = 1
  /-- `B(p)` has full column rank `k`. -/
  hB_rank : ∀ P : Adm k, (B P).rank = k
  /-- `col(b) = col(B)`: the two matrices have the same column space (equal ranges of
  their transpose-actions on Euclidean space). -/
  hcol_eq : ∀ P : Adm k,
    LinearMap.range (Matrix.toEuclideanLin (B P)) =
      LinearMap.range (Matrix.toEuclideanLin (b P))
  /-- `B F = b Φ`. -/
  hBF : ∀ P : Adm k, (B P) * F = (b P) * (Φ P)
  /-- `Σ_f` symmetric positive definite. -/
  hSf : Sf.PosDef
  /-- `G_B` positive definite. -/
  hGB : GB.PosDef
  /-- `SfSqrt = Σ_f^{1/2}`, the positive-semidefinite square root of `Σ_f`, recorded
  abstractly by its defining properties (positive-semidefinite, square equals `Σ_f`),
  which uniquely characterize the PSD square root of the positive-definite `Σ_f`. -/
  SfSqrt : Matrix (Fin k) (Fin k) ℝ
  hSfSqrt_psd : SfSqrt.PosSemidef
  hSfSqrt_sq : SfSqrt * SfSqrt = Sf
  /-- The population matrix `Σ_f^{1/2} G_B Σ_f^{1/2}` is Hermitian with *distinct*
  positive eigenvalues (Lemma 2 / Assumption 4).  Distinctness is expressed as
  injectivity of the eigenvalue enumeration. -/
  hSfGB_herm : (SfSqrt * GB * SfSqrt).IsHermitian
  hSfGB_posDef : (SfSqrt * GB * SfSqrt).PosDef
  hSfGB_distinct : Function.Injective hSfGB_herm.eigenvalues
  -- ===== Population eigenstructure of `Σ₀(p) = B(p) Σ_f B(p)ᵀ` (field 7) =====
  /-- Population eigenvalues `σ₀ⱼ(p)` of `Σ₀(p) = B(p) Σ_f B(p)ᵀ` (top `k`), strictly
  decreasing and positive; `p`-dependent. -/
  sig0 : (P : Adm k) → Fin k → ℝ
  hsig0_pos : ∀ P : Adm k, ∀ j, 0 < sig0 P j
  hsig0_sorted : ∀ P : Adm k, StrictAnti (sig0 P)
  /-- The columns `b₁, …, b_k` are ordered orthonormal unit eigenvectors of
  `Σ₀(p) = B(p) Σ_f B(p)ᵀ` at the eigenvalues `σ₀ⱼ(p)`. -/
  hb_eig : ∀ P : Adm k, ∀ j : Fin k,
    Matrix.toEuclideanLin ((B P) * Sf * (B P)ᵀ) (colVec (b P) j)
      = sig0 P j • colVec (b P) j
  -- ===== Ordering / eigenvector fields on `θ, h, w, ν` (fields 4,5,7) =====
  /-- The full dual spectrum `θ P` is weakly decreasing. -/
  hθ_sorted : ∀ P : Adm k, Antitone (θ P)
  /-- `θ P` is the *complete* sorted eigenvalue list of `W^{(p,n)} = Yᵀ Y/(np)`:
  it is a permutation `e` of the Hermitian eigenvalues of `W^{(p,n)}`.  Together with
  `hθ_sorted` this pins `θ P` to be exactly the weakly-decreasing list of all `n`
  eigenvalues of `W^{(p,n)}`. -/
  hθ_spectrum : ∀ P : Adm k,
    ∃ (hW : ((1 / ((n : ℝ) * P.1)) •
        (((b P) * (Φ P) + Z P)ᵀ * ((b P) * (Φ P) + Z P))).IsHermitian)
      (e : Fin n ≃ Fin n), θ P = fun i => hW.eigenvalues (e i)
  /-- Each `hⱼ` is a unit vector. -/
  hh_unit : ∀ P : Adm k, ∀ j, ‖h P j‖ = 1
  /-- The columns `h₁, …, h_k` are pairwise orthonormal (so `H` has `k` orthonormal
  columns).  Encoded as `Hᵀ H = Iₖ`. -/
  hH_ortho : ∀ P : Adm k, (Hmat (h P))ᵀ * (Hmat (h P)) = 1
  /-- `hⱼ` is the `j`-th (top-`k`, decreasing order) unit eigenvector of
  `S^{(p,n)} = Y Yᵀ/(np)` at eigenvalue `θⱼ^{(p,n)}` (index `j` cast into `Fin n`). -/
  hh_eig : ∀ P : Adm k, ∀ j : Fin k,
    Matrix.toEuclideanLin
        ((1 / ((n : ℝ) * P.1)) • (((b P) * (Φ P) + Z P) * ((b P) * (Φ P) + Z P)ᵀ))
        (h P j)
      = θ P (Fin.castLE (le_of_lt hkn) j) • (h P j)
  /-- Each `wⱼ^{(p,n)}` is a unit vector. -/
  hw_unit : ∀ P : Adm k, ∀ j, ‖w P j‖ = 1
  /-- `wⱼ^{(p,n)}` is a unit eigenvector of `W^{(p,n)} = Yᵀ Y/(np)` at its `j`-th
  largest eigenvalue `θⱼ^{(p,n)}`. -/
  hw_eig : ∀ P : Adm k, ∀ j : Fin k,
    Matrix.toEuclideanLin
        ((1 / ((n : ℝ) * P.1)) • (((b P) * (Φ P) + Z P)ᵀ * ((b P) * (Φ P) + Z P)))
        (w P j)
      = θ P (Fin.castLE (le_of_lt hkn) j) • (w P j)
  /-- Each `νⱼ^{(p)}` is a unit vector. -/
  hν_unit : ∀ P : Adm k, ∀ j, ‖ν P j‖ = 1
  /-- The finite-`p` eigenvalues `νval P` (of `N^{(p,n)}`) are weakly decreasing, so
  `ν P` is an *ordered* eigenvector family. -/
  hνval_sorted : ∀ P : Adm k, Antitone (νval P)
  /-- `νⱼ^{(p)}` is the `j`-th (decreasing order) unit eigenvector of
  `N^{(p,n)} = ΦΦᵀ/(np)` at eigenvalue `νval P j`. -/
  hν_eig : ∀ P : Adm k, ∀ j : Fin k,
    Matrix.toEuclideanLin ((1 / ((n : ℝ) * P.1)) • ((Φ P) * (Φ P)ᵀ)) (ν P j)
      = νval P j • (ν P j)
  -- ===== Limiting eigenpair structure (fields 5,6,7 limits) =====
  /-- strict ordering `λ₁^{(n)} > ⋯ > λₖ^{(n)} > 0` (Assumption 5). -/
  hlam_pos : ∀ j, 0 < lam j
  hlam_sorted : StrictAnti lam
  /-- each `wⱼ^{(n)}` a unit vector. -/
  hwn_unit : ∀ j, ‖wn j‖ = 1
  /-- each `νⱼ^{(n)}` a unit vector. -/
  hνn_unit : ∀ j, ‖νn j‖ = 1
  /-- `wⱼ^{(n)}` is the `j`-th unit eigenvector of `W^{(n),0} = Fᵀ G_B F/n` at
  eigenvalue `λⱼ^{(n)}`. -/
  hwn_eig : ∀ j : Fin k,
    Matrix.toEuclideanLin ((1 / (n : ℝ)) • (Fᵀ * GB * F)) (wn j) = lam j • (wn j)
  /-- `νⱼ^{(n)}` is the `j`-th unit eigenvector of `N^{(n)} = Φ̄∞ (Φ̄∞)ᵀ/n` at
  eigenvalue `λⱼ^{(n)}`. -/
  hνn_eig : ∀ j : Fin k,
    Matrix.toEuclideanLin ((1 / (n : ℝ)) • (Φbarinf * Φbarinfᵀ)) (νn j)
      = lam j • (νn j)
  -- ===== Fields (deterministic conclusions of Proposition 1 and Lemma 5) =====
  /-- Field 1 — Noise Gram limit (Prop. 1(a)): `Zᵀ Z/(np) → (δ²/n) Iₙ`. -/
  field1_noiseGram :
    Tendsto (fun P : Adm k => (1 / ((n : ℝ) * P.1)) • ((Z P)ᵀ * (Z P))) atTop
      (𝓝 ((δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ)))
  /-- Field 2 — Projected-noise decoherence (Prop. 1(b) / Lemma 3):
  `(1/√p) bᵀ(p) Z(p) → 0` in `ℝ^{k×n}`. -/
  field2_decoherence :
    Tendsto (fun P : Adm k => (1 / Real.sqrt P.1) • ((b P)ᵀ * (Z P))) atTop
      (𝓝 (0 : Matrix (Fin k) (Fin n) ℝ))
  /-- Field 3 — Signal-coordinate matrix limit (Lemma 5(ii)):
  `Φ̄(p) = Φ(p)/√p → Φ̄∞`. -/
  field3_signalLimit :
    Tendsto (fun P : Adm k => (1 / Real.sqrt P.1) • (Φ P)) atTop (𝓝 Φbarinf)
  /-- Field 4a — Dual spectrum limits (Prop. 1(c)): for `j = 1,…,k`,
  `θⱼ^{(p,n)} → λⱼ^{(n)} + δ²/n`. -/
  field4_dualSpectrum :
    ∀ j : Fin k, Tendsto (fun P : Adm k => θ P (Fin.castLE (le_of_lt hkn) j)) atTop
      (𝓝 (lam j + δ2 / n))
  /-- Field 4b — the trailing (bulk) average `ℓ^{(p,n)} := (1/(n−k)) Σ_{i=k+1}^n
  θᵢ^{(p,n)}` tends to `δ²/n`. -/
  field4_trailing :
    Tendsto (fun P : Adm k => (1 / ((n : ℝ) - k)) *
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)), θ P i) atTop
      (𝓝 (δ2 / n))
  /-- Field 5 — Dual eigenvector convergence (Prop. 1(d)): `wⱼ^{(p,n)} → wⱼ^{(n)}`. -/
  field5_dualEigvec : ∀ j : Fin k, Tendsto (fun P : Adm k => w P j) atTop (𝓝 (wn j))
  /-- Field 6a — Duality link (Lemma 5(iii)):
  `Φ̄∞ wⱼ^{(n)} = √(n λⱼ^{(n)}) · νⱼ^{(n)}`. -/
  field6_duality : ∀ j : Fin k,
    Matrix.toEuclideanLin Φbarinf (wn j) = Real.sqrt (n * lam j) • (νn j)
  /-- Field 6b — `νⱼ^{(p)} → νⱼ^{(n)}`. -/
  field6_nuLimit : ∀ j : Fin k, Tendsto (fun P : Adm k => ν P j) atTop (𝓝 (νn j))
  /-- Field 7a — Population structure: `Bᵀ B/p → G_B`. -/
  field7_BtB : Tendsto (fun P : Adm k => (1 / (P.1 : ℝ)) • ((B P)ᵀ * (B P))) atTop (𝓝 GB)

/-! ## Main Statements

Throughout, `hFact1`, `hFact2 m`, `hFact3 m` are the hypotheses that Facts 1, 2, 3
hold (Definition 2), appearing at the indicated dimension(s). -/

/-- **Statement 1 (Theorem 1 — error decomposition).** Given an instance of the
bundle and the Facts at dimensions `n` and `k`: for each `j`, as `p → ∞`,
`sin²∠(hⱼ, bⱼ) → δ²/(n λⱼ^{(n)} + δ²) + (n λⱼ^{(n)}/(n λⱼ^{(n)} + δ²)) ·
sin²∠(νⱼ^{(n)}, eⱼ)`, the out-of-subspace floor plus the in-subspace rotation. -/
theorem theorem1_error_decomposition {k n : ℕ} {δ2 : ℝ}
    (M : AsymptoticModel k n δ2)
    (hFact1 : Fact1_SLLN) (hFact2n : Fact2_Weyl n) (hFact3n : Fact3_EigCont n)
    (hFact2k : Fact2_Weyl k) (hFact3k : Fact3_EigCont k) :
    ∀ j : Fin k,
      Tendsto (fun P : Adm k => sinSq (M.h P j) (colVec (M.b P) j)) atTop
        (𝓝 (δ2 / ((n : ℝ) * M.lam j + δ2)
            + ((n : ℝ) * M.lam j / ((n : ℝ) * M.lam j + δ2))
              * sinSq (M.νn j) (EuclideanSpace.single j (1 : ℝ)))) := by
  sorry

/-- **Statement 2 (Corollary 1 — observable floor).** Under the same hypotheses,
for each `j`, as `p → ∞`:
(1) `ℓ^{(p,n)} → δ²/n`;
(2) `θⱼ^{(p,n)} → λⱼ^{(n)} + δ²/n`, and this limit is positive;
(3) `sin²∠(hⱼ, col(B)) := ‖Π⊥ hⱼ‖² → δ²/(n λⱼ^{(n)} + δ²)` (with `Π⊥ = I − b bᵀ`);
(4) `ℓ^{(p,n)}/θⱼ^{(p,n)} → δ²/(n λⱼ^{(n)} + δ²)`, equal to the floor of (3);
(5) this limiting ratio is `≤` the Theorem 1 limit, with equality iff
    `sin²∠(νⱼ^{(n)}, eⱼ) = 0`. -/
theorem corollary1_observable_floor {k n : ℕ} {δ2 : ℝ}
    (M : AsymptoticModel k n δ2)
    (hFact1 : Fact1_SLLN) (hFact2n : Fact2_Weyl n) (hFact3n : Fact3_EigCont n)
    (hFact2k : Fact2_Weyl k) (hFact3k : Fact3_EigCont k) :
    ∀ j : Fin k,
      -- (1) trailing (bulk) average limit
      (Tendsto (fun P : Adm k => (1 / ((n : ℝ) - k)) *
          ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)), M.θ P i)
          atTop (𝓝 (δ2 / n))) ∧
      -- (2) dual eigenvalue limit, positive
      (Tendsto (fun P : Adm k => M.θ P (Fin.castLE (le_of_lt M.hkn) j)) atTop
          (𝓝 (M.lam j + δ2 / n)) ∧ 0 < M.lam j + δ2 / n) ∧
      -- (3) angle to the column space col(B) = col(b)
      (Tendsto
          (fun P : Adm k =>
            ‖Matrix.toEuclideanLin (1 - (M.b P) * (M.b P)ᵀ) (M.h P j)‖ ^ 2)
          atTop (𝓝 (δ2 / ((n : ℝ) * M.lam j + δ2)))) ∧
      -- (4) observable ratio limit, equal to the floor
      (Tendsto
          (fun P : Adm k => ((1 / ((n : ℝ) - k)) *
              ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)), M.θ P i)
            / M.θ P (Fin.castLE (le_of_lt M.hkn) j)) atTop
          (𝓝 (δ2 / ((n : ℝ) * M.lam j + δ2)))) ∧
      -- (5) the ratio is ≤ the Theorem 1 limit, with equality iff the rotation vanishes
      (δ2 / ((n : ℝ) * M.lam j + δ2)
          ≤ δ2 / ((n : ℝ) * M.lam j + δ2)
            + ((n : ℝ) * M.lam j / ((n : ℝ) * M.lam j + δ2))
              * sinSq (M.νn j) (EuclideanSpace.single j (1 : ℝ))) ∧
      (δ2 / ((n : ℝ) * M.lam j + δ2)
          = δ2 / ((n : ℝ) * M.lam j + δ2)
            + ((n : ℝ) * M.lam j / ((n : ℝ) * M.lam j + δ2))
              * sinSq (M.νn j) (EuclideanSpace.single j (1 : ℝ))
        ↔ sinSq (M.νn j) (EuclideanSpace.single j (1 : ℝ)) = 0) := by
  sorry

/-- **Statement 3 (Corollary 2 — subspace error).** With `H := [h₁ ⋯ h_k]`,
`P_H := H Hᵀ`, `P_B := b bᵀ`: at every admissible `p` the Frobenius identity
`(1/2)‖P_H − P_B‖_F² = Σⱼ sin²∠(hⱼ, col(B))` holds (using that both `H` and `b`
have `k` orthonormal columns), and as `p → ∞`,
`(1/2)‖P_H − P_B‖_F² → Σⱼ δ²/(n λⱼ^{(n)} + δ²)`. -/
theorem corollary2_subspace_error {k n : ℕ} {δ2 : ℝ}
    (M : AsymptoticModel k n δ2)
    (hFact1 : Fact1_SLLN) (hFact2n : Fact2_Weyl n) (hFact3n : Fact3_EigCont n)
    (hFact2k : Fact2_Weyl k) (hFact3k : Fact3_EigCont k) :
    -- finite-`p` Frobenius identity (at every admissible `p`)
    (∀ P : Adm k,
      (1 / 2 : ℝ) * frobSq ((Hmat (M.h P)) * (Hmat (M.h P))ᵀ - (M.b P) * (M.b P)ᵀ)
        = ∑ j : Fin k,
            ‖Matrix.toEuclideanLin (1 - (M.b P) * (M.b P)ᵀ) (M.h P j)‖ ^ 2) ∧
    -- asymptotic limit
    Tendsto
      (fun P : Adm k => (1 / 2 : ℝ) *
        frobSq ((Hmat (M.h P)) * (Hmat (M.h P))ᵀ - (M.b P) * (M.b P)ᵀ)) atTop
      (𝓝 (∑ j : Fin k, δ2 / ((n : ℝ) * M.lam j + δ2))) := by
  sorry

/-- **Statement 4 (Corollary 3 — noiseless case, exact at finite `p`; STANDALONE).**
A finite-`p` linear-algebra identity with its own minimal hypotheses. Fix
`1 ≤ k < n` and `k < p`; orthonormal `b`, arbitrary `Φ`,
`S⁰ := b Φ Φᵀ bᵀ/(np)`, `N := Φ Φᵀ/(np)`; an index `j` and a value `μⱼ` that is a
simple eigenvalue of both `S⁰` and `N`, with unit eigenvectors `h⁰ⱼ` (of `S⁰`) and
`νⱼ` (of `N`) at `μⱼ`. Then `sin²∠(h⁰ⱼ, bⱼ) = sin²∠(νⱼ, eⱼ)`. -/
theorem corollary3_noiseless {p k n : ℕ}
    (hk : 1 ≤ k) (hkn : k < n) (hkp : k < p)
    (b : Matrix (Fin p) (Fin k) ℝ) (hb : bᵀ * b = 1)
    (Φ : Matrix (Fin k) (Fin n) ℝ)
    (S0 : Matrix (Fin p) (Fin p) ℝ)
    (hS0 : S0 = (1 / ((n : ℝ) * p)) • (b * Φ * Φᵀ * bᵀ))
    (Npn : Matrix (Fin k) (Fin k) ℝ)
    (hNpn : Npn = (1 / ((n : ℝ) * p)) • (Φ * Φᵀ))
    (j : Fin k) (μj : ℝ)
    (h0j : EuclideanSpace ℝ (Fin p)) (νj : EuclideanSpace ℝ (Fin k))
    -- `μⱼ` a simple eigenvalue of `S⁰` with unit eigenvector `h⁰ⱼ`
    (hh0j_unit : ‖h0j‖ = 1)
    (hh0j_eig : Matrix.toEuclideanLin S0 h0j = μj • h0j)
    (hh0j_simple : ∀ w : EuclideanSpace ℝ (Fin p), ‖w‖ = 1 →
      Matrix.toEuclideanLin S0 w = μj • w → w = h0j ∨ w = -h0j)
    -- `μⱼ` a simple eigenvalue of `N^{(p,n)}` with unit eigenvector `νⱼ`
    (hνj_unit : ‖νj‖ = 1)
    (hνj_eig : Matrix.toEuclideanLin Npn νj = μj • νj)
    (hνj_simple : ∀ w : EuclideanSpace ℝ (Fin k), ‖w‖ = 1 →
      Matrix.toEuclideanLin Npn w = μj • w → w = νj ∨ w = -νj)
    (hFact1 : Fact1_SLLN) (hFact2p : Fact2_Weyl p) (hFact3p : Fact3_EigCont p) :
    sinSq h0j (colVec b j) = sinSq νj (EuclideanSpace.single j (1 : ℝ)) := by
  sorry

end
