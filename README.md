# GTZ

**A Lean 4 formalization of the Goreinov–Tyrtyshnikov–Zamarashkin submatrix problem.**

> **Conjecture (GTZ, 1997).** Every real n×k matrix with orthonormal columns has
> a k×k row submatrix B with σ_min(B) ≥ 1/√n.

Known before this project: true for k ≤ 2 (Sengupta–Pautov); false over ℂ with
sharp constant α = 2 − 2/√3 (the SIC configuration is extremal). The first open
case is k = 3, and after the reductions formalized here it is exactly the
weighted (6,3) and (7,3) instances.

This repository is the campaign's **final proof artifact**: nothing enters
until it has survived adversarial audit or been re-derived during
mechanization, and the eventual paper will be a LaTeX rendition of exactly the
definitions and theorems in these modules. The repository is **sorry-free**;
every proved theorem's axiom set is printed on every build and must be exactly
`propext, Classical.choice, Quot.sound`.

---

## The working form

A **weighted design** is a family g₁, …, g_m ∈ ℝᵏ with weights t_c > 0,
Σ t_c = 1, and Σ t_c g_c g_cᵀ = I_k. A k-subset C **dominates** when
Σ_{c∈C} g_c g_cᵀ ⪰ I_k. The original statement for all n at rank k is
equivalent to: *every weighted design of every size has a dominating k-subset*
(`GtzWeightedAll k`). All structural work happens in this weighted form; the
bridge back to the 1997 statement is itself a theorem here.

## What is proven, end to end

**The solved boundary, unconditionally.** `GtzOriginal n k` holds for
k ∈ {1, 2, n−2, n−1, n} — every case humanity had ever solved — and for every
matrix with at most five rows. Rank two is the complete Sengupta–Pautov
theorem in its weighted generalization, formalized without spectral theory.

**The master reduction, as an equivalence.** Via sharp crystallization
(M(k) = k(k+1)/2 + 1), weighted Naimark duality, and the descent assembly:

```
GTZ for all (n, k)   ⟺   weighted (m, s) for  s ≥ 2,  2s ≤ m ≤ s(s+1)/2 + 1
GtzWeightedAll 3     ⟺   GtzWeighted 6 3  ∧  GtzWeighted 7 3
```

**The certificate machinery, at every rank.** The trace identity and
excess-balance pigeonhole (branch a), the de-spectralized cap criterion
(branch b), the determinant form that decides both branches by one sign, the
descent ladder, light-atom deflation, the corner fiber theorem B_k, and
Lemma F_k (Bhatia–Davis at mean zero) with its tie classification.

**The planar platform for (6,3).** The audited GAP-S layer: the master
identity R′ and its corollary R″, the Bloch dictionary, dust control, the
pinch quadratic, the per-pair level law, the compression bridge (Lemma G) that
puts this planar layer underneath a rank-3 design unconditionally, Theorem V
with its branch selection made algebraic, the Zero-Atom Pushoff theorem that
dissolved GAP-T, the tight-graph geometry, the corrected first-order law, the
collar floor, and the interface arithmetic — including a kernel-checked
**counterexample** settling a disputed numerical law inside the kernel.

**The consumption pipeline.** A fully rational certificate layer: exact
ℚ-designs, LDL-congruence gate certificates, and cast lemmas so that a future
rational (6,3)/(7,3) certificate closes rank 3 by finite exact arithmetic.

## The formal frontier

Everything else about GTZ-for-all-(n,k) is a kernel-checked theorem. What
remains is precisely the open mathematics:

1. `GtzWeighted 6 3` and `GtzWeighted 7 3` — the binding open cases;
2. the canonical window 2s ≤ m ≤ s(s+1)/2 + 1 for ranks s ≥ 4.

## Module map

| Module | Content |
|---|---|
| `Basic` | designs, domination, `GtzWeighted` / `GtzOriginal`, pivots |
| `Sanity` | definition-pinning instances (must stay sorry-free forever) |
| `BhatiaDavis` | Lemma F_k: min-pair ≤ −1 on the zero-sum sphere, tie classification |
| `SchurRankOne` | rank-one Schur complement by polarization |
| `TraceIdentity` | trace identity, excess balance, the pigeonhole (branch a) |
| `CapCriterion` | the cap criterion, de-spectralized (branch b) |
| `CapSlack` | Theorem D: both branches as one determinant sign |
| `PsdKit` | Cauchy–Schwarz contraction flips, congruence, whitening |
| `Completion` | orthonormal completion |
| `Naimark` | Theorem N: weighted Naimark duality |
| `Crystallization` | sharp bounded support M(k) = k(k+1)/2 + 1 |
| `CornerFiber` | Theorem B_k: the exact (k+1)-cycle fiber closes at every rank |
| `TwoByTwo` | 2×2 PSD criterion; the one-surface identity |
| `Deflation` | light-atom deflation (m+1,k) → (m,k) |
| `RankTwo` | weighted Sengupta–Pautov, Case B, fully scalar |
| `Reductions` | rank ≤ 2, the bridge, Theorem L, duality descent, the all-heavy reduction |
| `DescentLadder` | Theorem Q: the full-base trace identity and its two ladder consequences |
| `Compression` | Lemma G: orthonormal compressions of designs are designs; the planar gate |
| `PlanarPlatform` | Theorem R′, trace form, abstract R″, the pinch quadratic |
| `BlochDictionary` | Bloch squares, the M-form identity, R″ end-to-end |
| `DustControl` | Proposition D: mixed positivity, dust deficit, cross rebate |
| `MomentCovector` | Theorem V: the tight-triangle covector, branch selected algebraically |
| `Pushoff` | the Zero-Atom Pushoff theorem and its corner saturation |
| `TightGraph` | the max-degree theorem: K₁,₃ is dead |
| `CertificateFrame` | stress-leaf, parabola poles, four-cycle collapse, dust exclusions |
| `FirstOrderLaw` | the corrected two-face first-order constant; the fire rate |
| `LocalLaw` | the LP vertex bound; weight-split invariance |
| `CollarFloor` | the R1 rescaled floor; Theorem OW's off-window fire |
| `Interface` | the statement-(2) interface arithmetic, both directions |
| `LawCounterexample` | the kernel-checked cap-10 refutation of the displayed local law |
| `RatCertificate` | the computable ℚ-certificate consumption layer |
| `Audit` | `#print axioms` for every proved theorem, on every build |

## Rigor rules

- Nothing is called proven while it contains `sorry`. `Audit.lean` prints the
  axiom set of every proved theorem on every build; the expected set is
  `propext, Classical.choice, Quot.sound` — nothing else, ever.
- Definitions stay minimal and Mathlib-anchored (`Matrix.PosSemidef`, no
  bespoke orders). Junk-value footguns are fenced at every use: `Matrix.inv`
  of a singular matrix is 0, so every pivot theorem carries `PosDef`.
- `Sanity.lean` is the definition-drift alarm: if a refactor breaks it, the
  definitions have drifted from the mathematics.
- Mechanization is treated as audit: statement-hygiene findings (unnecessary
  hypotheses, hidden dependencies, silently consumed theorems) are recorded in
  the module docstrings where they were found.

## Build

```sh
lake exe cache get   # once — downloads Mathlib oleans
lake build           # builds everything and prints the axiom audit
```

Toolchain: Lean 4 with Mathlib, pinned in `lean-toolchain` / `lakefile`.

## Selected mechanization findings

Discoveries made *by* the formalization, not merely recorded in it:

- **Theorem V's hidden hypothesis.** The informal proof works in an angle
  parameterization that silently assumes the cyclic branch. The elimination
  actually factors as spread × co-spread, and the co-spread factor scaled by
  the leverage product equals ℓ_A + ℓ_B + ℓ_C − 2 > 0 — so the branch is
  *selected* by an inequality, not assumed.
- **The max-degree theorem consumes dust exclusion.** Its polar normal is
  nonzero only when ν|ξ| < ½, which needs ν ≥ 0 — quietly downstream of the
  Gordan covering theorem. The informal one-line proof states neither side
  condition.
- **The interface pair that composed to the empty set** is now a theorem in
  both directions: the recorded pair is vacuous, the repaired √τ₀ pair is
  nonvacuous, and the one-line nonvacuity test that would have caught it is
  kernel-checked.
- **Statement hygiene.** The bridge and crystallization need neither `1 ≤ k`
  nor `k < n`; Naimark duality genuinely needs `1 ≤ k`; the pigeonhole needs
  `1 ≤ k`; dust-ness is unnecessary for the dust-deficit bound.
- **No spectra anywhere.** Every informally-spectral step (Naimark's W^{−1/2},
  B_k's eigenvalue computation, the cap criterion's signature count) was
  replaced by polarization, Gram algebra, or a witness pair — the whole
  development is free of eigenvalue theory except one C*-factorization import.
